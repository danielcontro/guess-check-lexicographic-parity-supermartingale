from itertools import chain
from typing import Optional
from multiprocessing import Pool, Process, Queue

from z3 import (
    And,
    ArithRef,
    BoolRef,
    Implies,
    Int,
    ModelRef,
    Or,
    RealVal,
    Solver,
    simplify,
    unsat,
)

from reactive_module import (
    LinearFunction,
    QLinearFunction,
    ReactiveModule,
    State,
    UpdateDistribution,
)
from template import QLinearTemplate
from utils import VAR_MANAGER, extract_var, satisfiable, substitute_state


ParityObjective = BoolRef


class Verification:
    def __init__(self, product_system: ReactiveModule):
        self._product_system = product_system

    @property
    def system(self):
        return self._product_system

    def inv_init(self, invariant_template: QLinearTemplate):
        return list(map(lambda init: invariant_template(init) >= 0, self.system.init))

    def inv_consec(
        self,
        dataset: list[State],
        invariant_template: QLinearTemplate,
    ):
        return list(
            chain.from_iterable(
                map(
                    lambda state: map(
                        lambda succ: Implies(
                            And(
                                substitute_state(self.system.state_space, state),
                                invariant_template(state) >= 0,
                            ),
                            And(
                                substitute_state(self.system.state_space, succ),
                                invariant_template(succ) >= 0,
                            ),
                        ),
                        self.system.successors(state),
                    ),
                    dataset,
                )
            )
        )

    def lexicographic_non_increase_constraint(
        self,
        j,
        lin_lex_psm: list[QLinearTemplate],
        state: State,
        command: UpdateDistribution,
        epsilon: ArithRef,
    ):
        # NOTE: The function gets invoked with an actual system state rather than a symbolic one
        successors = command(state)
        return Or(
            *[
                And(
                    *[
                        lin_lex_psm[k].post_exp(state[Int("q")], successors)
                        == lin_lex_psm[k](state)
                        for k in range(i)
                    ],
                    lin_lex_psm[i].post_exp(state[Int("q")], successors)
                    <= lin_lex_psm[i](state) - epsilon,
                )
                for i in range(j)
            ],
            And(
                *[
                    lin_lex_psm[k].post_exp(state[Int("q")], successors)
                    == lin_lex_psm[k](state)
                    for k in range(j)
                ],
                lin_lex_psm[j].post_exp(state[Int("q")], successors)
                <= lin_lex_psm[j](state),
            ),
        )

    def lexicographic_decrease_constraint(
        self,
        j,
        lin_lex_psm: list[QLinearTemplate],
        state: State,
        command: UpdateDistribution,
        epsilon: ArithRef,
    ):
        # NOTE: The function gets invoked with an actual system state rather than a symbolic one
        successors = command(state)
        return Or(
            *[
                And(
                    *[
                        lin_lex_psm[k].post_exp(state[Int("q")], successors)
                        == lin_lex_psm[k](state)
                        for k in range(i)
                    ],
                    lin_lex_psm[i].post_exp(state[Int("q")], successors)
                    <= lin_lex_psm[i](state) - epsilon,
                )
                for i in range(j + 1)
            ]
        )

    def drift_demonic(
        self,
        dataset: list[State],
        invariant_template: QLinearTemplate,
        lin_lex_psm_template: list[QLinearTemplate],
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
    ):
        constraints = []
        # epsilons: dict[tuple[int, int], list[ArithRef]] = {}
        # epsilons: dict[int, list[ArithRef]] = {}
        for state in dataset:
            for j, parity_objective in enumerate(parity_objectives):
                for gc in self.system.guarded_commands:
                    premise = substitute_state(
                        And(
                            invariant_template(state) >= 0,
                            parity_objective,
                            gc.guard,
                            self.system.state_space,
                        ),
                        state,
                    )
                    if not satisfiable(premise):
                        """
                        Would produce False => ... thus skip
                        """
                        continue

                    constraints.append(
                        Implies(
                            premise,
                            self.lexicographic_decrease_constraint(
                                j,
                                lin_lex_psm_template,
                                state,
                                gc.command,
                                epsilon,
                            )
                            if j % 2
                            else self.lexicographic_non_increase_constraint(
                                j,
                                lin_lex_psm_template,
                                state,
                                gc.command,
                                epsilon,
                            ),
                        )
                    )

                    # if (j, k) not in epsilons:
                    # if j not in epsilons:
                    #     """
                    #     If not previously ranked guard k for parity j, create new epsilons
                    #     (else reuse)
                    #     """
                    #     epsilons[j] = [
                    #         # VAR_MANAGER.new_symbol(f"epsilon({j},{k})[{i}]")
                    #         VAR_MANAGER.new_symbol(f"epsilon({j})[{i}]")
                    #         for i in range(j + 1)
                    #     ]
                    #
                    # for i in range(j + 1):
                    #     successors = command(state)
                    #     assert successors is not None
                    #     post_expectation = sum(
                    #         succ[0] * lin_lex_psm_template[i](succ[1])
                    #         for succ in successors
                    #     )
                    #     constraints.append(
                    #         Implies(
                    #             premise,
                    #             post_expectation
                    #             # <= lin_lex_psm_template[i](state) - epsilons[(j, k)][i],
                    #             <= lin_lex_psm_template[i](state) - epsilons[j][i],
                    #         )
                    #     )
                    #
        # Add constraints for epsilons
        # for (j, _), eps_i in epsilons.items():
        # for j, eps_i in epsilons.items():
        #     for i, eps in enumerate(eps_i):
        #         if i == 0:
        #             constraints.append(eps >= 0)
        #             continue
        #         constraints.append(
        #             Implies(
        #                 And(
        #                     [eps_i[prec] == 0 for prec in range(i)],
        #                 ),
        #                 eps > 0 if i == j and (j % 2 == 1) else eps >= 0,
        #             )
        #         )
        return constraints

    def guess_non_neg_constraints(
        self,
        invariant_template: QLinearTemplate,
        lin_lex_psm_template: list[QLinearTemplate],
        dataset: list[State],
    ):
        """
        ∀ lin_psm ∈ lin_lex_psm. ∀x ∈ dataset: invariant(x) >= 0 => lin_psm[k](x) >= 0
        """
        return list(
            chain.from_iterable(
                map(
                    lambda lin_psm_template: map(
                        lambda state: Implies(
                            invariant_template(state) >= 0, lin_psm_template(state) >= 0
                        ),
                        dataset,
                    ),
                    lin_lex_psm_template,
                )
            )
        )

    def inv_init_check(self, invariant: QLinearFunction):
        constraints = []
        for init in self.system.init:
            constraints.append(invariant(init) < 0)
        return constraints

    def inv_consec_check(self, invariant: QLinearFunction):
        constraints = []
        for gc in self.system.guarded_commands:
            for update in gc.command.updates:
                for q, q_invariant in invariant.f.items():
                    constraints.append(
                        simplify(
                            And(
                                Int("q") == q,
                                q_invariant.f >= 0,
                                gc.guard,
                                self.system.state_space,
                                invariant(update.symbolic_successor()) < 0,
                            )
                        )
                    )

        return constraints

    def _neg_lexicographic_non_increase_constraint(
        self,
        j,
        lin_lex_psm: list[QLinearFunction],
        q: int,
        command: UpdateDistribution,
        epsilon: ArithRef,
    ):
        # NOTE: The function gets invoked with a symbolic system state, epsilon is a positive value
        successors = command.symbolic_successors()
        return And(
            *[
                Or(
                    *[
                        lin_lex_psm[k].post_exp(q, successors)
                        > lin_lex_psm[k].symbolic[q]
                        for k in range(i)
                    ],
                    lin_lex_psm[i].post_exp(q, successors)
                    > lin_lex_psm[i].symbolic[q] - RealVal(epsilon),
                )
                for i in range(j)
            ],
            *[
                lin_lex_psm[k].post_exp(q, successors) > lin_lex_psm[k].symbolic[q]
                for k in range(j + 1)
            ],
        )

    def _neg_lexicographic_decrease_constraint(
        self,
        j,
        lin_lex_psm: list[QLinearFunction],
        q: int,
        command: UpdateDistribution,
        epsilon: ArithRef,
    ):
        # NOTE: The function gets invoked with a symbolic system state, epsilon is a positive value
        successors = command.symbolic_successors()
        return And(
            *[
                Or(
                    *[
                        lin_lex_psm[k].post_exp(q, successors)
                        > lin_lex_psm[k].symbolic[q]
                        for k in range(i)
                    ],
                    lin_lex_psm[i].post_exp(q, successors)
                    > lin_lex_psm[i].symbolic[q] - epsilon,
                )
                for i in range(j + 1)
            ]
        )

    def drift_check(
        self,
        lin_lex_psm: list[QLinearFunction],
        invariant: QLinearFunction,
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
    ):
        constraints = []

        for j, parity_objective in enumerate(parity_objectives):
            for gc in self.system.guarded_commands:
                for q, q_invariant in invariant.f.items():
                    # print(f"Drift check j={j} k={k} q={q}:")
                    # print("Lex constraint:\n", lex_constraint)
                    constraint = simplify(
                        And(
                            Int("q") == q,
                            q_invariant.f >= 0,
                            self.system.state_space,
                            parity_objective,
                            self._neg_lexicographic_decrease_constraint(
                                j, lin_lex_psm, q, gc.command, epsilon
                            )
                            if j % 2
                            else self._neg_lexicographic_non_increase_constraint(
                                j, lin_lex_psm, q, gc.command, epsilon
                            ),
                        )
                    )
                    # print("constraint:\n", constraint)
                    constraints.append(constraint)

        return constraints

    def check_non_neg_constraints(
        self, invariant: QLinearFunction, lin_lex_psm: list[QLinearFunction]
    ):
        """
        ∃ x ∈ ℝⁿ×ℕᵐ. ∃ lin_psm ∈ lin_lex_psm. invariant(x) >= 0 ∧ TI(x) ∧ lin_psm(x) < 0
        """
        constraints = []
        for q, q_invariant in invariant.f.items():
            for lin_psm in lin_lex_psm:
                constraints.append(
                    And(
                        Int("q") == q,
                        q_invariant.f >= 0,
                        self.system.state_space,
                        lin_psm.symbolic[q] < 0,
                    )
                )
        return constraints

    def _extract_counterexample(self, model: ModelRef):
        return {var: model[var] for var in self.system.vars}

    def constraint_solver(self, constraint: BoolRef):
        solver = Solver()
        solver.add(constraint)
        if solver.check() == unsat:
            # queue.put(None)
            return None
        model = solver.model()
        print("Constraint:", constraint)
        # queue.put({var: extract_var(var, model) for var in self.system.vars})
        print("Check model:")
        for var in model:
            print(var, "=", model[var])
        return {var: extract_var(var, model) for var in self.system.vars}

    def guess(
        self,
        dataset: list[State],
        invariant_template: QLinearTemplate,
        lin_lex_psm_template: list[QLinearTemplate],
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
    ):
        guesser = Solver()
        non_neg = self.guess_non_neg_constraints(
            invariant_template, lin_lex_psm_template, dataset
        )
        inv_init = self.inv_init(invariant_template)
        inv_consec = self.inv_consec(dataset, invariant_template)
        drift = self.drift_demonic(
            dataset,
            invariant_template,
            lin_lex_psm_template,
            parity_objectives,
            epsilon,
        )
        print("Guess Constraints:")
        print("Non-negativity")
        for c in non_neg:
            print(c)
        print("Initial")
        for c in inv_init:
            print(c)
        print("Consecution")
        for c in inv_consec:
            print(c)
        print("Drift")
        for c in drift:
            print(c)

        guesser.add(*non_neg)
        guesser.add(*inv_init)
        guesser.add(*inv_consec)
        guesser.add(
            *drift,
            epsilon > 0,
        )
        if guesser.check() == unsat:
            raise ValueError("No LexPSM candidate found")
        model = guesser.model()
        print("Model")
        print(model)
        lin_lex_psm_candidate = [
            lin_lex_psm_template[i].instantiate(model)
            for i in range(len(lin_lex_psm_template))
        ]
        invariant_candidate = invariant_template.instantiate(model)
        print("Candidate PSM")
        for psm in lin_lex_psm_candidate:
            print(psm.symbolic)
        print("Candidate invariant")
        print(invariant_candidate.symbolic)
        return (
            lin_lex_psm_candidate,
            invariant_candidate,
            model[epsilon] if not isinstance(epsilon, float) else epsilon,
        )

    def check(
        self,
        lin_lex_psm: list[QLinearFunction],
        invariant: QLinearFunction,
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
    ):
        """
        for each constraint create parallel solver, shortcircut if some solver is sat,
        if all unsat then the candidate are correct
        """
        constraints = []
        non_neg = self.check_non_neg_constraints(invariant, lin_lex_psm)
        inv_init = self.inv_init_check(invariant)
        inv_consec = self.inv_consec_check(invariant)
        drift = self.drift_check(lin_lex_psm, invariant, parity_objectives, epsilon)

        print("Check Constraints:")
        print("Non-negativity")
        for c in non_neg:
            print(c)
        print("Initial")
        for c in inv_init:
            print(c)
        print("Consecution")
        for c in inv_consec:
            print(c)
        print("Drift")
        for c in drift:
            print(c)

        constraints.extend(non_neg)
        constraints.extend(inv_init)
        constraints.extend(inv_consec)
        constraints.extend(drift)

        processes: list[Process] = []
        queue: Queue[Optional[State]] = Queue(maxsize=10)
        counterexamples: list[State] = []
        for constraint in constraints:
            counterexample = self.constraint_solver(
                And(
                    constraint,
                    *[var != val for var, val in counterexamples[-1].items()]
                    if len(counterexamples) == 0
                    else True,
                )
            )
            if counterexample is not None:
                counterexamples.append(counterexample)
        #     p = Process(target=self.constraint_solver, args=[constraint, queue])
        #     processes.append(p)
        #     p.start()
        # terminated = 0
        # counterexample: Optional[State] = None
        # while terminated < len(constraints) or counterexample is None:
        #     counterexample = queue.get()
        #     print("Terminated!")
        #     print(counterexample)
        #     terminated += 1
        #
        # for p in processes:
        #     p.terminate()
        # print("Counterexamples:")
        # for c in counterexamples:
        #     print(c)
        return counterexamples

    def guess_check_linlexpsm_invariant_synthesis(
        self,
        spec_automaton_states: list[int],
        s: list[ParityObjective],
        epsilon: ArithRef,
    ):
        dataset = self.system.init.copy()
        lin_lex_psm_template = [
            QLinearTemplate(f"V{i}", spec_automaton_states, self.system.vars)
            for i in range(len(s))
        ]
        invariant_template = QLinearTemplate(
            "invariant", spec_automaton_states, self.system.vars
        )
        print("Invariant")
        print(invariant_template.symbolic)
        print("LinLexPSM")
        for psm in lin_lex_psm_template:
            print(psm.symbolic)
        # FIX Time cutoff rather than iteration
        CUTOFF = 10
        for _ in range(CUTOFF):
            lin_lex_psm_candidate, invariant_candidate, epsilon = self.guess(
                dataset, invariant_template, lin_lex_psm_template, s, epsilon
            )

            counterexample = self.check(
                lin_lex_psm_candidate, invariant_candidate, s, epsilon
            )
            if len(counterexample) == 0:
                print("Done")
                return lin_lex_psm_candidate, invariant_candidate
            print("New counterexamples:", len(counterexample))
            dataset.extend(counterexample)
            print("Dataset size:", len(dataset))
            print("Dataset:")
            for state in dataset:
                print(state)
