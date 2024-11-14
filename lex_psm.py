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
    Solver,
    simplify,
    unsat,
)

from reactive_module import LinearFunction, QLinearFunction, ReactiveModule, State
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

    def drift_demonic(
        self,
        dataset: list[State],
        invariant_template: QLinearTemplate,
        lin_lex_psm_template: list[QLinearTemplate],
        parity_objectives: list[ParityObjective],
    ):
        constraints = []
        epsilons: dict[tuple[int, int], list[ArithRef]] = {}
        for state in dataset:
            for j, parity_objective in enumerate(parity_objectives):
                for k, command in enumerate(self.system.guarded_commands):
                    premise = substitute_state(
                        And(
                            invariant_template(state) >= 0,
                            parity_objective,
                            command.guard,
                            self.system.state_space,
                        ),
                        state,
                    )
                    if not satisfiable(premise):
                        """
                        Would produce False => ... thus skip
                        """
                        continue

                    if (j, k) not in epsilons:
                        """
                        If not previously ranked guard k for parity j, create new epsilons
                        (else reuse)
                        """
                        epsilons[(j, k)] = [
                            VAR_MANAGER.new_symbol(f"epsilon({j},{k})[{i}]")
                            for i in range(j + 1)
                        ]

                    for i in range(j + 1):
                        successors = command(state)
                        assert successors is not None
                        post_expectation = sum(
                            succ[0] * lin_lex_psm_template[i](succ[1])
                            for succ in successors
                        )
                        constraints.append(
                            Implies(
                                premise,
                                post_expectation
                                <= lin_lex_psm_template[i](state) - epsilons[(j, k)][i],
                            )
                        )

        # Add constraints for epsilons
        for (j, _), eps_i in epsilons.items():
            for i, eps in enumerate(eps_i):
                if i == 0:
                    constraints.append(eps >= 0)
                    continue
                constraints.append(
                    Implies(
                        And(
                            [eps_i[prec] == 0 for prec in range(i)],
                        ),
                        eps > 0 if i == j and (j % 2 == 1) else eps >= 0,
                    )
                )
        return constraints

    def guess(
        self,
        dataset: list[State],
        invariant_template: QLinearTemplate,
        lin_lex_psm_template: list[QLinearTemplate],
        parity_objectives: list[ParityObjective],
    ):
        print("Guessing")
        guesser = Solver()
        guesser.add(*self.inv_init(invariant_template))
        guesser.add(*self.inv_consec(dataset, invariant_template))
        guesser.add(
            *self.drift_demonic(
                dataset, invariant_template, lin_lex_psm_template, parity_objectives
            )
        )
        if guesser.check() == unsat:
            raise ValueError("No LexPSM candidate found")
        print("Contraints")
        print(guesser.assertions())
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
        return lin_lex_psm_candidate, invariant_candidate

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

    def drift_check(
        self,
        lin_lex_psm: list[QLinearFunction],
        invariant: QLinearFunction,
        parity_objectives: list[ParityObjective],
    ):
        constraints = []

        for j, parity_objective in enumerate(parity_objectives):
            for k, gc in enumerate(self.system.guarded_commands):
                for q, q_invariant in invariant.f.items():
                    successors = gc.command.symbolic_successors()
                    # print("Successors:", successors)
                    """
                    !(PostV(x) <=lex V(x)) <=> (PostV0(x) > V0(x)
                        || (PostV0(x) != Vo(x) & PostV1(x) > V1(x))
                        || ...
                        || (⋀(PostV_i(x) != V_i(x) & PostV_i+1(x) > V_i+1(x)))
                    !(PostV(x) <lex V(x)) <=> (PostV0(x) => V0(x)
                        || (PostV0(x) != Vo(x) & PostV1(x) => V1(x))
                        || ...
                        || (⋀(PostV_i(x) != V_i(x) & PostV_i+1(x) => V_i+1(x)))
                    """
                    lex_constraint = []
                    for i, psm_i in enumerate(lin_lex_psm):
                        lex_constraint.append(
                            Or(
                                *list(
                                    map(
                                        lambda psm: psm.post_exp(q, successors)
                                        != psm.symbolic[q],
                                        lin_lex_psm[:i],
                                    )
                                ),
                                psm_i.post_exp(q, successors) >= psm_i.symbolic[q]
                                if j % 2 == 1
                                else psm_i.post_exp(q, successors) > psm_i.symbolic[q],
                            )
                        )
                    # print(f"Drift check j={j} k={k} q={q}:")
                    # print("Lex constraint:\n", lex_constraint)
                    constraint = simplify(
                        And(
                            Int("q") == q,
                            q_invariant.f >= 0,
                            self.system.state_space,
                            parity_objective,
                            And(*lex_constraint),
                        )
                    )

                    # print("constraint:\n", constraint)

                    constraints.append(constraint)

        return constraints

    def _extract_counterexample(self, model: ModelRef):
        return {var: model[var] for var in self.system.vars}

    def constraint_solver(self, constraint: BoolRef):
        # , queue: Queue):
        solver = Solver()
        solver.add(constraint)
        if solver.check() == unsat:
            # queue.put(None)
            return None
        model = solver.model()
        print("Contraint:", constraint)
        # queue.put({var: extract_var(var, model) for var in self.system.vars})
        return {var: extract_var(var, model) for var in self.system.vars}

    def check(
        self,
        lin_lex_psm: list[QLinearFunction],
        invariant: QLinearFunction,
        parity_objectives: list[ParityObjective],
    ):
        print("Checking")
        """
        for each constraint create parallel solver, shortcircut if some solver is sat,
        if all unsat then the candidate are correct
        """
        constraints = []
        constraints.extend(self.inv_init_check(invariant))
        constraints.extend(self.inv_consec_check(invariant))
        constraints.extend(self.drift_check(lin_lex_psm, invariant, parity_objectives))

        processes: list[Process] = []
        queue: Queue[Optional[State]] = Queue(maxsize=10)
        counterexample = None
        for constraint in constraints:
            counterexample = self.constraint_solver(constraint)
            if counterexample is not None:
                break
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
        return counterexample

    def guess_check_linlexpsm_invariant_synthesis(
        self,
        spec_automaton_states: list[int],
        s: list[ParityObjective],
    ):
        dataset = self.system.init
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
            lin_lex_psm_candidate, invariant_candidate = self.guess(
                dataset, invariant_template, lin_lex_psm_template, s
            )

            counterexample = self.check(lin_lex_psm_candidate, invariant_candidate, s)
            if counterexample is None:
                return lin_lex_psm_candidate, invariant_candidate
            dataset.append(counterexample)
            print("counterexample:", counterexample)
