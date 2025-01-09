from itertools import chain
import itertools
from typing import Generic, TypeVar

from z3 import (
    And,
    ArithRef,
    BoolRef,
    ForAll,
    Implies,
    IntNumRef,
    IntVal,
    ModelRef,
    Not,
    Or,
    Solver,
    sat,
    unsat,
)

from functions import IndexedPolynomial, Value, Variable
from reactive_module import (
    Q,
    QLinearFunction,
    QPolytopeFunction,
    ReactiveModule,
    Valuation,
    UpdateDistribution,
)
from tree_psm import TreePSM
from utils import (
    evaluate_to_true,
    extract_var,
    is_value,
    satisfiable,
    substitute_state,
)


ParityObjective = BoolRef

T = TypeVar("T")


class LexPSM(Generic[T]):
    pass


class Verification:
    def __init__(self, product_system: ReactiveModule):
        self._product_system = product_system

    @property
    def system(self):
        return self._product_system

    def inv_init(
        self,
        system: ReactiveModule,
        invariant: QPolytopeFunction,
    ):
        return list(
            chain.from_iterable(
                map(
                    lambda init: [f >= 0 for f in invariant(init, init[Q])],
                    system.init,
                )
            )
        )

    def __inv_init_polynomial(
        self,
        system: ReactiveModule,
        invariant: IndexedPolynomial,
    ):
        return list(
            map(
                lambda init: invariant[
                    tuple(init[var] for var in invariant.indexing_ordering)
                ](init)
                >= 0,
                system.init,
            )
        )

    def lexicographic_non_increase_constraint(
        self,
        j,
        lin_lex_psm: list[QLinearFunction],
        q: IntNumRef,
        state: Valuation,
        post_distribution: list[tuple[float, Valuation]],
        epsilon: ArithRef,
    ):
        # NOTE: The function gets invoked with an actual system state rather than a symbolic one
        return Or(
            *[
                And(
                    *[
                        lin_lex_psm[k].post_exp(q, post_distribution)
                        == lin_lex_psm[k](state, q)
                        for k in range(i)
                    ],
                    lin_lex_psm[i].post_exp(q, post_distribution)
                    <= lin_lex_psm[i](state, q) - epsilon,
                )
                for i in range(j)
            ],
            And(
                *[
                    lin_lex_psm[k].post_exp(q, post_distribution)
                    == lin_lex_psm[k](state, q)
                    for k in range(j)
                ],
                lin_lex_psm[j].post_exp(q, post_distribution)
                <= lin_lex_psm[j](state, q),
            ),
        )

    def lexicographic_decrease_constraint(
        self,
        j: int,
        lin_lex_psm: list[QLinearFunction],
        q: IntNumRef,
        state: Valuation,
        post_distribution: list[tuple[float, Valuation]],
        epsilon: ArithRef,
    ):
        # NOTE: The function gets invoked with an actual system state rather than a symbolic one
        next_q = post_distribution[0][1][Q]
        return Or(
            *[
                And(
                    *[
                        lin_lex_psm[k].post_exp(next_q, post_distribution)
                        == lin_lex_psm[k](state, q)
                        for k in range(i)
                    ],
                    lin_lex_psm[i].post_exp(next_q, post_distribution)
                    <= lin_lex_psm[i](state, q) - epsilon,
                )
                for i in range(j + 1)
            ]
        )

    def _neg_lexicographic_non_increase_constraint(
        self,
        j,
        lin_lex_psm: list[QLinearFunction],
        q: IntNumRef,
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
                    > lin_lex_psm[i].symbolic[q] - IntVal(epsilon),
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

    def extract_counterexample(
        self, system: ReactiveModule, model: ModelRef
    ) -> Valuation:
        return {var: extract_var(var, model) for var in system.vars}

    def post_psm_lexicographic_constraint(
        self,
        j: int,
        lin_lex_psm: list[QLinearFunction],
        q: IntNumRef,
        state: Valuation,
        post_distribution: list[tuple[float, Valuation]],
        epsilon: ArithRef,
    ):
        return (
            self.lexicographic_decrease_constraint(
                j, lin_lex_psm, q, state, post_distribution, epsilon
            )
            if j % 2
            else self.lexicographic_non_increase_constraint(
                j, lin_lex_psm, q, state, post_distribution, epsilon
            )
        )

    def psm_constraints(
        self,
        system: ReactiveModule,
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
        lex_psm: list[QLinearFunction],
        invariant: QPolytopeFunction,
        state: Valuation,
    ) -> list[BoolRef]:
        automaton_states = (
            [q]
            if isinstance(q := state.get(Q), IntNumRef)
            else list(map(lambda q: IntVal(q), invariant.symbolic.keys()))
        )
        inv_consec = []
        drift = []
        non_negativity = []
        for q in automaton_states:
            for psm in lex_psm:
                non_negativity.append(
                    substitute_state(
                        Implies(
                            And(Q == q, *[f >= 0 for f in invariant(state, q)]),
                            psm(state, q) >= 0,
                        ),
                        state,
                    )
                )
            for guarded_command in system.guarded_commands:
                for update in guarded_command.command.updates:
                    if not satisfiable(
                        premise := substitute_state(
                            And(
                                Q == q,
                                *[f >= 0 for f in invariant(state, q)],
                                system.state_space,
                                guarded_command.guard,
                            ),
                            state,
                        )
                    ):
                        continue
                    succ = update(state)
                    constraint = substitute_state(
                        Implies(
                            premise,
                            And(*[f >= 0 for f in invariant(succ, succ[Q])]),
                        ),
                        state,
                    )
                    inv_consec.append(constraint)

                for j, parity_objective in enumerate(parity_objectives):
                    if not satisfiable(
                        premise := substitute_state(
                            And(
                                Q == q,
                                *[f >= 0 for f in invariant(state, q)],
                                system.state_space,
                                guarded_command.guard,
                                parity_objective,
                            ),
                            state,
                        )
                    ):
                        continue
                    constraint = substitute_state(
                        Implies(
                            premise,
                            self.post_psm_lexicographic_constraint(
                                j,
                                lex_psm,
                                q,
                                state,
                                guarded_command.command(state),
                                epsilon,
                            ),
                        ),
                        state,
                    )
                    drift.append(constraint)
        return inv_consec + drift + non_negativity

    def guess(
        self,
        system: ReactiveModule,
        parity_states: list[IntNumRef],
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
        dataset: list[Valuation],
        polyhedra_dimensions: int = 1,
    ):
        lin_lex_psm_template = [
            QLinearFunction.template(f"V{i}", system.vars, parity_states)
            for i in range(len(parity_objectives))
        ]
        invariant_template = QPolytopeFunction.template(
            "I",
            system.vars,
            parity_states,
            polyhedra_dimensions,
        )
        constraints = self.inv_init(system, invariant_template)
        for state in dataset:
            constraints.extend(
                self.psm_constraints(
                    system,
                    parity_objectives,
                    epsilon,
                    lin_lex_psm_template,
                    invariant_template,
                    state,
                )
            )
        solver = Solver()
        solver.add(*constraints)
        print("Guess conjunction size:", len(constraints))
        result = solver.check()
        if result == unsat:
            return None, None
        assert result == sat
        model = solver.model()
        # print("Guess Model:")
        # print(model)
        lin_lex_psm_candidate = [
            lin_lex_psm_template[i].instantiate(model)
            for i in range(len(lin_lex_psm_template))
        ]
        invariant_candidate = invariant_template.instantiate(model)

        return lin_lex_psm_candidate, invariant_candidate

    def check(
        self,
        system: ReactiveModule,
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
        spm: list[QLinearFunction],
        inv: QPolytopeFunction,
    ):
        constraints = [
            *self.inv_init(system, inv),
            *self.psm_constraints(
                system, parity_objectives, epsilon, spm, inv, system.symbolic_state
            ),
        ]
        counterexamples: list[Valuation] = []
        print("Check disjunction size:", len(constraints))
        for constraint in constraints:
            solver = Solver()
            solver.add(Not(constraint))
            result = solver.check()
            if result == sat:
                new_counterexample = self.extract_counterexample(system, solver.model())
                # Ensure that the counterexample is not already in the list
                if not any(
                    all(new_counterexample[var] == old[var] for var in system.vars)
                    for old in counterexamples
                ):
                    counterexamples.append(new_counterexample)

        return counterexamples

    def guess_check(
        self,
        system: ReactiveModule,
        parity_states: list[IntNumRef],
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
    ):
        dataset = system.init.copy()
        CUTOFF = 100
        polyhedra_dimensions = 1
        for i in range(CUTOFF):
            print(f"\n\nGuess-check {i+1}-th iteration")
            spm, inv = self.guess(
                system,
                parity_states,
                parity_objectives,
                epsilon,
                dataset,
                polyhedra_dimensions,
            )
            if spm is None or inv is None:
                polyhedra_dimensions += 1
                print("Increasing polyhedra dimensions to:", polyhedra_dimensions)
                continue
            print("Invariant:")
            print(inv)
            print("Lexicographic PSM:")
            for psm in spm:
                print(psm)
            for state in dataset:
                constraints = [
                    *self.inv_init(system, inv),
                    *self.psm_constraints(
                        system, parity_objectives, epsilon, spm, inv, state
                    ),
                ]
                for constraint in constraints:
                    solver = Solver()
                    solver.add(Not(constraint))
                    result = solver.check()
                    if result == sat:
                        print("Substitution Constraint:\n", solver.assertions())
                        print("Model:\n", solver.model())
                        assert False

            for state in dataset:
                constraints = [
                    *self.inv_init(system, inv),
                    *self.psm_constraints(
                        system,
                        parity_objectives,
                        epsilon,
                        spm,
                        inv,
                        system.symbolic_state,
                    ),
                ]
                for constraint in constraints:
                    solver = Solver()
                    solver.add(
                        And(Not(constraint)),
                        *[var == state[var] for var in system.vars],
                    )
                    result = solver.check()
                    if result == sat:
                        print("Assign Constraint:\n", solver.assertions())
                        print("Model:\n", solver.model())
                        assert False

            assert all(
                evaluate_to_true(
                    And(
                        *self.inv_init(system, inv),
                        *self.psm_constraints(
                            system, parity_objectives, epsilon, spm, inv, state
                        ),
                    )
                )
                for state in dataset
            )
            counterexamples = self.check(
                self.system, parity_objectives, epsilon, spm, inv
            )
            print("New counterexamples:")
            for counterexample in counterexamples:
                print(counterexample)
                assert all(var in counterexample for var in system.vars)

            print("Dataset:")
            for counterexample in dataset:
                print(counterexample)

            if len(counterexamples) == 0:
                return spm, inv
            dataset.extend(counterexamples)
        raise ValueError("TIMEOUT: No LexPSM and Invariant found!")

    def monolithic(
        self,
        system: ReactiveModule,
        parity_states: list[IntNumRef],
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
    ) -> tuple[list[QLinearFunction], QPolytopeFunction]:
        psm_template = [
            QLinearTemplate(f"V{i}", parity_states, system.vars)
            for i in range(len(parity_objectives))
        ]

        inv_template = QPolytopeFunction.template(
            "I",
            system.vars,
            parity_states,
            10,
        )
        state = system.symbolic_state
        constraints = self.inv_init(system, inv_template) + self.psm_constraints(
            system, parity_objectives, epsilon, psm_template, inv_template, state
        )
        query = ForAll(system.vars, And(*constraints))
        solver = Solver()
        if solver.check(query) == unsat:
            raise ValueError("No LexPSM and Invariant found!")
        model = solver.model()
        lin_lex_psm = [spm.instantiate(model) for spm in psm_template]
        invariant = inv_template.instantiate(model)
        return lin_lex_psm, invariant

    def tree_psm_constraints(
        self,
        system: ReactiveModule,
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
        tpsm: TreePSM,
        invariant: QPolytopeFunction,
        state: Valuation,
    ) -> list[BoolRef]:
        parity_states = (
            [q]
            if isinstance(q := state.get(Q), IntNumRef)
            else list(map(lambda q: IntVal(q), invariant.states))
        )

        # non_negativity = []
        # for q in parity_states:
        #     for i in range(len(tpsm.lex_psms)):
        #         lex_psm_constraint, lex_psm = tpsm[i, q]
        #         non_negativity.extend(
        #             [
        #                 substitute_state(
        #                     Implies(
        #                         And(
        #                             Q == q,
        #                             *[f >= 0 for f in invariant(state, q)],
        #                             lex_psm_constraint,
        #                         ),
        #                         psm(state) >= 0,
        #                     ),
        #                     state,
        #                 )
        #                 for psm in lex_psm
        #             ]
        #         )
        #

        # Invariant consecution constraints
        inv_consec = []
        for q in parity_states:
            for gc in system.guarded_commands:
                for update in gc.command.updates:
                    if not satisfiable(
                        premise := substitute_state(
                            And(
                                Q == q,
                                *[f >= 0 for f in invariant(state, q)],
                                system.state_space,
                                gc.guard,
                            ),
                            state,
                        )
                    ):
                        continue
                    succ = update(state)
                    constraint = substitute_state(
                        Implies(
                            premise,
                            And(*[f >= 0 for f in invariant(succ, succ[Q])]),
                        ),
                        state,
                    )
                    inv_consec.append(constraint)

        # Drift constraints
        drift = []
        for q in parity_states:
            for p, objective in enumerate(parity_objectives):
                for gc in system.guarded_commands:
                    for i in range(len(tpsm.lex_psms)):
                        lex_psm_constraint, lex_psm = tpsm[i, q]
                        # Drift constraints
                        if not satisfiable(
                            premise := (
                                substitute_state(
                                    And(
                                        system.state_space,
                                        gc.guard,
                                        objective,
                                        Q == q,
                                        *[f >= 0 for f in invariant(state, q)],
                                        lex_psm_constraint,
                                    ),
                                    state,
                                )
                            )
                        ):
                            continue
                        posts = tpsm.post(gc, state, p)
                        assert isinstance(posts, list)
                        constraint = substitute_state(
                            Implies(
                                premise,
                                Or(
                                    *[
                                        self.lexicographic_constraint(
                                            post,
                                            [v(state) for v in lex_psm],
                                            p,
                                            epsilon,
                                        )
                                        for post in posts
                                    ]
                                ),
                            ),
                            state,
                        )
                        drift.append(constraint)

        return inv_consec + drift

    def lexicographic_constraint(
        self,
        post_v: list[ArithRef],
        v: list[ArithRef],
        p: int,
        epsilon: ArithRef,
    ):
        return (
            self.lexicographic_decrease(post_v, v, p, epsilon)
            if p % 2
            else self.lexicographic_non_increase(post_v, v, p, epsilon)
        )

    def lexicographic_decrease(
        self, post_v: list[ArithRef], v: list[ArithRef], p: int, epsilon: ArithRef
    ):
        return Or(
            *[
                And(
                    *[post_v[k] == v[k] for k in range(i)],
                    post_v[i] <= v[i] - epsilon,
                )
                for i in range(p + 1)
            ]
        )

    def lexicographic_non_increase(
        self, post_v: list[ArithRef], v: list[ArithRef], p: int, epsilon: ArithRef
    ):
        return Or(
            self.lexicographic_decrease(post_v, v, p - 1, epsilon),
            And(
                *[post_v[k] == v[k] for k in range(p)],
                post_v[p] <= v[p],
            ),
        )

    def guess_tree_psm(
        self,
        system: ReactiveModule,
        parity_states: list[IntNumRef],
        parity_objectives: list[ParityObjective],
        polytope_dimensions: int,
        tree_psm_height: int,
        epsilon: ArithRef,
        dataset: list[Valuation],
    ):
        tree_lex_psm = TreePSM.template(
            system.vars, parity_states, tree_psm_height, len(parity_objectives)
        )
        invariant_template = QPolytopeFunction.template(
            "I", system.vars, parity_states, polytope_dimensions
        )
        print("Invariant template:")
        print(invariant_template)
        print("TreePSM template:")
        print(tree_lex_psm)
        constraints = self.inv_init(system, invariant_template)
        for state in dataset:
            constraints.extend(
                self.tree_psm_constraints(
                    system,
                    parity_objectives,
                    epsilon,
                    tree_lex_psm,
                    invariant_template,
                    state,
                )
            )
        solver = Solver()
        solver.add(*constraints)
        print("Guess conjunction size:", len(constraints))
        result = solver.check()
        if result == unsat:
            return None, None
        assert result == sat
        model = solver.model()
        print("Guess Model:")
        print(model)
        tree_psm_candidate = tree_lex_psm.instantiate(model)
        invariant_candidate = invariant_template.instantiate(model)

        return tree_psm_candidate, invariant_candidate

    def check_tree_psm(
        self,
        system: ReactiveModule,
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
        lex_psm: TreePSM,
        inv: QPolytopeFunction,
    ):
        constraints = [
            *self.inv_init(system, inv),
            *self.tree_psm_constraints(
                system, parity_objectives, epsilon, lex_psm, inv, system.symbolic_state
            ),
        ]
        counterexamples: list[Valuation] = []
        print("Check disjunction size:", len(constraints))
        solver = Solver()
        solver.add(Or(*[Not(constraint) for constraint in constraints]))
        result = solver.check()
        if result == sat:
            counterexamples.append(self.extract_counterexample(system, solver.model()))

        return counterexamples

    def guess_check_tree_psm(
        self,
        system: ReactiveModule,
        parity_states: list[IntNumRef],
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
    ):
        dataset = system.init.copy()
        CUTOFF = 1000
        polyhedra_dimensions = 1
        tree_height = 1
        for i in range(CUTOFF):
            print(f"\n\nGuess-check {i+1}-th iteration")
            tree_lex_psm, inv = self.guess_tree_psm(
                system,
                parity_states,
                parity_objectives,
                polyhedra_dimensions,
                tree_height,
                epsilon,
                dataset,
            )
            if tree_lex_psm is None or inv is None:
                polyhedra_dimensions += 1
                tree_height += 1
                print("Increasing polyhedra dimensions to:", polyhedra_dimensions)
                print("Increasing psm height to:", tree_height)
                continue
            print("Invariant:")
            print(inv)
            print("TreePSM:")
            print(tree_lex_psm)

            counterexamples = self.check_tree_psm(
                self.system, parity_objectives, epsilon, tree_lex_psm, inv
            )
            print("New counterexamples:")
            for counterexample in counterexamples:
                print(counterexample)
                assert all(var in counterexample for var in system.vars)

            print("Dataset:")
            for counterexample in dataset:
                print(counterexample)

            if len(counterexamples) == 0:
                return tree_lex_psm, inv
            dataset.extend(counterexamples)
        raise ValueError("TIMEOUT: No LexPSM and Invariant found!")

    def constraints_polynomial_psm(
        self,
        system: ReactiveModule,
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
        lex_psm: list[IndexedPolynomial],
        invariant: IndexedPolynomial,
        indexing: dict[Variable, list[Value]],
        state: Valuation,
    ) -> list[BoolRef]:
        automaton_states = (
            [q] if isinstance(q := state.get(Q), IntNumRef) else indexing[Q]
        )

        non_negativity = []
        inv_consec = []
        drift = []
        Q_index = invariant.indexing_ordering.index(Q)
        polynomial_indexes = (
            invariant.indexes
            if len(automaton_states) > 1
            else list(
                filter(
                    lambda index: index[Q_index] == automaton_states[0],
                    invariant.indexes,
                )
            )
        )

        for index in polynomial_indexes:
            index_assignment = And(
                *[
                    state[var] == index[i]
                    for i, var in enumerate(invariant.indexing_ordering)
                ]
            )

            # Non negativity
            for psm in lex_psm:
                non_negativity.append(
                    substitute_state(
                        Implies(
                            And(
                                index_assignment,
                                invariant[index](state) >= 0,
                            ),
                            psm[index](state) >= 0,
                        ),
                        state,
                    )
                )

            # Invariant consecution
            for guarded_command in system.guarded_commands:
                for update in guarded_command.command.updates:
                    if not satisfiable(
                        premise := substitute_state(
                            And(
                                index_assignment,
                                invariant[index](state) >= 0,
                                system.state_space,
                                guarded_command.guard,
                            ),
                            state,
                        )
                    ):
                        continue
                    succ = update(state)
                    index_succ: tuple[Value, ...] = tuple(
                        succ[var] for var in invariant.indexing_ordering
                    )
                    succ_indexes = list(
                        itertools.product(
                            *[
                                [val] if is_value(val) else indexing[val]
                                for val in index_succ
                            ]
                        )
                    )
                    for succ_index in succ_indexes:
                        constraint = substitute_state(
                            Implies(
                                premise,
                                invariant[succ_index](succ) >= 0,
                            ),
                            state,
                        )
                        inv_consec.append(constraint)

            # Drift
            for p, objective in enumerate(parity_objectives):
                for gc in system.guarded_commands:
                    if not satisfiable(
                        premise := substitute_state(
                            And(
                                index_assignment,
                                invariant[index](state) >= 0,
                                system.state_space,
                                gc.guard,
                                objective,
                            ),
                            state,
                        )
                    ):
                        continue
                    tmp = [psm.post(gc(state)) for psm in lex_psm]
                    tmp1 = {p: [] for p in range(len(lex_psm))}
                    posts = [0 for x in tmp]
                    assert isinstance(posts, list)
                    constraint = substitute_state(
                        Implies(
                            premise,
                            Or(
                                *[
                                    self.lexicographic_constraint(
                                        post,
                                        [v[index](state) for v in lex_psm],
                                        p,
                                        epsilon,
                                    )
                                    for post in posts
                                ]
                            ),
                        ),
                        state,
                    )
                    drift.append(constraint)

        return inv_consec + drift + non_negativity

    def polynomial_lexicographic_decrease_constraint(
        self,
        j: int,
        lex_psm: list[IndexedPolynomial],
        index: tuple[Value, ...],
        state: Valuation,
        post_distribution: list[tuple[float, Valuation]],
        epsilon: ArithRef,
    ):
        return Or(
            *[
                And(
                    *[
                        lex_psm[k].post_exp(post_distribution)
                        == lex_psm[k][index](state)
                        for k in range(i)
                    ],
                    lex_psm[i].post_exp(post_distribution)
                    <= lex_psm[i][index](state) - epsilon,
                )
                for i in range(j + 1)
            ]
        )

    def polynomial_lexicographic_non_increase_constraint(
        self,
        j,
        lex_psm: list[IndexedPolynomial],
        index: tuple[Value, ...],
        state: Valuation,
        post_distribution: list[tuple[float, Valuation]],
        epsilon: ArithRef,
    ):
        return Or(
            *[
                And(
                    *[
                        lex_psm[k].post_exp(post_distribution)
                        == lex_psm[k][index](state)
                        for k in range(i)
                    ],
                    lex_psm[i].post_exp(post_distribution)
                    <= lex_psm[i][index](state) - epsilon,
                )
                for i in range(j)
            ],
            And(
                *[
                    lex_psm[k].post_exp(post_distribution) == lex_psm[k][index](state)
                    for k in range(j)
                ],
                lex_psm[j].post_exp(post_distribution) <= lex_psm[j][index](state),
            ),
        )

    def post_polynomial_psm_lexicographic_constraint(
        self,
        j: int,
        lex_psm: list[IndexedPolynomial],
        index: tuple[Value, ...],
        state: Valuation,
        post_distribution: list[tuple[float, Valuation]],
        epsilon: ArithRef,
    ):
        return (
            self.polynomial_lexicographic_decrease_constraint(
                j, lex_psm, index, state, post_distribution, epsilon
            )
            if j % 2
            else self.polynomial_lexicographic_decrease_constraint(
                j, lex_psm, index, state, post_distribution, epsilon
            )
        )

    def guess_polynomial(
        self,
        system: ReactiveModule,
        parity_states: list[IntNumRef],
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
        dataset: list[Valuation],
        indexing: dict[Variable, list[Value]],
        degree: int,
    ):
        indexing[Q] = parity_states
        name = "_".join([f"{var}" for var in indexing.keys()])
        lex_psm_template = [
            IndexedPolynomial.template(f"V{i}_{name}", system.vars, indexing, degree)
            for i in range(len(parity_objectives))
        ]
        invariant_template = IndexedPolynomial.template(
            f"I_{name}",
            system.vars,
            indexing,
            degree,
        )
        print("Lexicographic PSM template:")
        for psm in lex_psm_template:
            print(psm)
        print("Invariant template:")
        print(invariant_template)
        constraints = self.__inv_init_polynomial(system, invariant_template)
        for state in dataset:
            constraints.extend(
                self.constraints_polynomial_psm(
                    system,
                    parity_objectives,
                    epsilon,
                    lex_psm_template,
                    invariant_template,
                    indexing,
                    state,
                )
            )

        solver = Solver()
        solver.add(*constraints)
        print("Guess conjunction size:", len(constraints))
        result = solver.check()
        if result == unsat:
            return None, None
        assert result == sat
        model = solver.model()
        # print("Guess Model:")
        # print(model)
        lex_psm_candidate = [
            lex_psm_template[i].instantiate(model) for i in range(len(lex_psm_template))
        ]
        invariant_candidate = invariant_template.instantiate(model)

        return lex_psm_candidate, invariant_candidate

    def check_polynomial(
        self,
        system: ReactiveModule,
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
        spm: list[IndexedPolynomial],
        inv: IndexedPolynomial,
    ):
        constraints = [
            *self.__inv_init_polynomial(system, inv),
            *self.constraints_polynomial_psm(
                system,
                parity_objectives,
                epsilon,
                spm,
                inv,
                inv.indexing,
                system.symbolic_state,
            ),
        ]
        counterexamples: list[Valuation] = []
        print("Check disjunction size:", len(constraints))
        for constraint in constraints:
            solver = Solver()
            solver.add(And(system.state_space, Not(constraint)))
            result = solver.check()
            if result == sat:
                new_counterexample = self.extract_counterexample(system, solver.model())
                # Ensure that the counterexample is not already in the list
                if not any(
                    all(new_counterexample[var] == old[var] for var in system.vars)
                    for old in counterexamples
                ):
                    counterexamples.append(new_counterexample)

        return counterexamples

    def guess_check_polynomial(
        self,
        system: ReactiveModule,
        parity_states: list[IntNumRef],
        parity_objectives: list[ParityObjective],
        epsilon: ArithRef,
        indexing: dict[Variable, list[Value]],
        degree: int = 1,
    ):
        dataset = system.init.copy()
        CUTOFF = 100
        for i in range(CUTOFF):
            print(f"\n\nGuess-check {i+1}-th iteration")
            spm, inv = self.guess_polynomial(
                system,
                parity_states,
                parity_objectives,
                epsilon,
                dataset,
                indexing,
                degree,
            )

            if spm is None or inv is None:
                raise ValueError("No LexPSM and Invariant found of degree:", degree)

            print("Invariant:")
            print(inv)
            print("Lexicographic PSM:")
            for psm in spm:
                print(psm)

            # for state in dataset:
            #     constraints = [
            #         *self.inv_init(system, inv),
            #         *self.psm_constraints(
            #             system, parity_objectives, epsilon, spm, inv, state
            #         ),
            #     ]
            #     for constraint in constraints:
            #         solver = Solver()
            #         solver.add(Not(constraint))
            #         result = solver.check()
            #         if result == sat:
            #             print("Substitution Constraint:\n", solver.assertions())
            #             print("Model:\n", solver.model())
            #             assert False
            #
            # for state in dataset:
            #     constraints = [
            #         *self.inv_init(system, inv),
            #         *self.psm_constraints(
            #             system,
            #             parity_objectives,
            #             epsilon,
            #             spm,
            #             inv,
            #             system.symbolic_state,
            #         ),
            #     ]
            #     for constraint in constraints:
            #         solver = Solver()
            #         solver.add(
            #             And(Not(constraint)),
            #             *[var == state[var] for var in system.vars],
            #         )
            #         result = solver.check()
            #         if result == sat:
            #             print("Assign Constraint:\n", solver.assertions())
            #             print("Model:\n", solver.model())
            #             assert False
            #
            # assert all(
            #     evaluate_to_true(
            #         And(
            #             *self.inv_init(system, inv),
            #             *self.psm_constraints(
            #                 system, parity_objectives, epsilon, spm, inv, state
            #             ),
            #         )
            #     )
            #     for state in dataset
            # )

            counterexamples = self.check_polynomial(
                self.system, parity_objectives, epsilon, spm, inv
            )

            print("New counterexamples:")
            for counterexample in counterexamples:
                print(counterexample)
                assert all(var in counterexample for var in system.vars)

            print("Dataset:")
            for counterexample in dataset:
                print(counterexample)

            if len(counterexamples) == 0:
                return spm, inv
            dataset.extend(counterexamples)

        raise ValueError("TIMEOUT: No LexPSM and Invariant found!")
