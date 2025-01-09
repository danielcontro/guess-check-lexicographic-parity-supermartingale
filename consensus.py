import itertools
from z3 import (
    And,
    ArithRef,
    BoolRef,
    Implies,
    Int,
    IntVal,
    ModelRef,
    Not,
    Or,
    RealVal,
    Solver,
    sat,
    unsat,
)

from functions import IndexedPolynomial, Polynomial, Valuation, Value
from lex_psm import ParityObjective, Verification
from reactive_module import (
    GuardedCommand,
    LinearFunction,
    ReactiveModule,
    StateUpdate,
    UpdateDistribution,
    Variable,
)
from utils import extract_var, is_value, satisfiable, substitute_state


N = 1
K = 1024
RANGE = 2 * (K + 1) * N
COUNTER_INIT = (K + 1) * N
LEFT = N
RIGHT = 2 * (K + 1) * N - N


coin1 = Int("coin1")
pc1 = Int("pc1")
counter = Int("counter")
q = Int("q")
state_space = And(
    coin1 >= 0,
    pc1 >= 0,
    counter >= 0,
    counter <= 6,
    coin1 <= 1,
    pc1 <= 3,
    q >= 0,
    q <= 1,
)
vars: list[Variable] = [coin1, pc1, counter, q]
f0 = LinearFunction([], IntVal(0))
f1 = LinearFunction([], IntVal(1))
f2 = LinearFunction([], IntVal(2))
f3 = LinearFunction([], IntVal(3))
counter_inc = LinearFunction([counter], counter + 1)
counter_dec = LinearFunction([counter], counter - 1)

su1 = StateUpdate(vars, {coin1: f0, pc1: f1, q: f1})
su2 = StateUpdate(vars, {coin1: f1, pc1: f1, q: f1})
su3 = StateUpdate(vars, {counter: counter_dec, pc1: f2, coin1: f0, q: f1})
su4 = StateUpdate(vars, {counter: counter_inc, pc1: f2, coin1: f0, q: f1})
su5 = StateUpdate(vars, {pc1: f3, coin1: f0, q: f1})
su6 = StateUpdate(vars, {pc1: f3, coin1: f1, q: f1})
su7 = StateUpdate(vars, {pc1: f0, q: f1})
su8 = StateUpdate(vars, {pc1: f3, q: f0})

gc = [
    GuardedCommand(
        And(pc1 == 0, q == 1),
        UpdateDistribution(vars, [(0.5, su1), (0.5, su2)]),
    ),
    GuardedCommand(
        And(pc1 == 1, coin1 == 0, counter > 0, q == 1),
        UpdateDistribution(vars, [(1, su3)]),
    ),
    GuardedCommand(
        And(pc1 == 1, coin1 == 1, counter < RANGE, q == 1),
        UpdateDistribution(vars, [(1, su4)]),
    ),
    GuardedCommand(
        And(pc1 == 2, counter <= LEFT, q == 1), UpdateDistribution(vars, [(1, su5)])
    ),
    GuardedCommand(
        And(pc1 == 2, counter >= RIGHT, q == 1), UpdateDistribution(vars, [(1, su6)])
    ),
    GuardedCommand(
        And(pc1 == 2, counter > LEFT, counter < RIGHT, q == 1),
        UpdateDistribution(vars, [(1, su7)]),
    ),
    GuardedCommand(And(pc1 == 3), UpdateDistribution(vars, [(1, su8)])),
]

system = ReactiveModule(
    [
        {
            coin1: IntVal(0),
            pc1: IntVal(0),
            counter: IntVal(COUNTER_INIT),
            q: IntVal(1),
        }
    ],
    vars,
    gc,
    state_space,
)

psm = Verification(system)
automata_states = [IntVal(0), IntVal(1)]
parity_objectives = [q == IntVal(0), q == IntVal(1)]


def index(state: Valuation, indexing: list[Variable]):
    return tuple(state[var] for var in indexing)


def invariant_initiation(
    system: ReactiveModule, invariant: IndexedPolynomial
) -> list[BoolRef]:
    return [inv_i > 0 for init in system.init for inv_i in invariant.eval(init)]


def non_negativity(
    system: ReactiveModule,
    invariant: IndexedPolynomial,
    lex_psm: list[IndexedPolynomial],
    state: Valuation,
) -> list[BoolRef]:
    # print("Non-negativity")
    constraints = []
    for index in invariant.induced_indexes(invariant.get_index(state)):
        for psm in lex_psm:
            if not satisfiable(
                premise := substitute_state(
                    And(
                        system.state_space,
                        index_constraint(index, invariant),
                        invariant.eval_indexed(state, index) >= 0,
                    ),
                    state,
                )
            ):
                continue
            constraint = substitute_state(
                Implies(premise, psm.eval_indexed(state, index) >= 0),
                state,
            )
            # print("Constraint")
            # print(constraint, "\n")
            constraints.append(constraint)
    # print()

    return constraints


def index_constraint(index: tuple[Value, ...], f: IndexedPolynomial) -> BoolRef:
    return And(*[var == index[i] for i, var in enumerate(f.indexing_ordering)])


def invariant_consecution(
    system: ReactiveModule, invariant: IndexedPolynomial, state: Valuation
) -> list[BoolRef]:
    # print("Invariant consecution")
    constraints = []
    for gc in system.guarded_commands:
        for update in gc.updates:
            # print("guard", gc.guard)
            # print("update", update.symbolic_successor)
            for index in invariant.induced_indexes(invariant.get_index(state)):
                # print("Index", index)
                # print("State", state)
                indexed_state = {
                    var: index[invariant.indexing_ordering.index(var)]
                    if (not is_value(val := state[var]))
                    and (var in invariant.indexing_ordering)
                    else val
                    for var in invariant.vars
                }
                # print("After", tmp)
                succ = update(indexed_state)
                # print("Succ", succ)
                # index_succ = tuple(
                #     simplify(substitute(v, (invariant.indexing_ordering[i], index[i])))
                #     for i, v in enumerate(invariant.get_index(succ))
                # )
                # print("Succ Index", index_succ)
                for succ_index in invariant.induced_indexes(invariant.get_index(succ)):
                    if not satisfiable(
                        premise := substitute_state(
                            And(
                                system.state_space,
                                gc.guard,
                                index_constraint(index, invariant),
                                And(
                                    *[
                                        succ[var] == succ_index[i]
                                        for i, var in enumerate(
                                            invariant.indexing_ordering
                                        )
                                    ]
                                ),
                                invariant.eval_indexed(indexed_state, index) > 0,
                            ),
                            state,
                        )
                    ):
                        continue
                    constraint = substitute_state(
                        Implies(
                            premise,
                            invariant.eval_indexed(succ, succ_index) >= 0,
                        ),
                        state,
                    )
                    # print("Constraint")
                    # print(constraint, "\n")
                    constraints.append(constraint)
    #             print()
    #         print()
    #     print()
    # print()

    return constraints


def drift(
    system: ReactiveModule,
    invariant: IndexedPolynomial,
    lex_psm: list[IndexedPolynomial],
    state: Valuation,
    parity_objectives: list[ParityObjective],
    epsilon: ArithRef,
) -> list[BoolRef]:
    # print("Drift")
    constraints = []
    for gc in system.guarded_commands:
        # print("Guard", gc.guard)
        # print("Updates")
        # for p, update in gc.command.distribution:
        #     print(f"{p}: {update.symbolic_successor}")
        for p, objective in enumerate(parity_objectives):
            # print("P:", p, "Objective", objective)
            for index in invariant.induced_indexes(invariant.get_index(state)):
                # print("Invariant Index", index)
                # print("Before", state)
                tmp = {
                    var: index[invariant.indexing_ordering.index(var)]
                    if (not is_value(val := state[var]))
                    and (var in invariant.indexing_ordering)
                    else val
                    for var in invariant.vars
                }
                # print("After", tmp)
                if not satisfiable(
                    premise := substitute_state(
                        And(
                            system.state_space,
                            gc.guard,
                            objective,
                            index_constraint(index, invariant),
                            invariant.eval_indexed(tmp, index) >= 0,
                        ),
                        state,
                    )
                ):
                    continue
                # TODO: LexPSM[T] type to handle this
                # for index in lex_psm[0].induced_indexes(lex_psm[0].get_index(state)):
                # TODO: Iterate combinations of post
                lex_posts = lex_post(lex_psm, gc.command(tmp), p)
                # print("Lex Index", index)
                # print("Lex Posts")
                # print(lex_posts)
                constraint = substitute_state(
                    Implies(
                        premise,
                        And(
                            *[
                                lexicographic_decrease_constraint(
                                    post,
                                    [
                                        psm.eval_indexed(tmp, index)
                                        for psm in lex_psm[: p + 1]
                                    ],
                                    p,
                                    epsilon,
                                )
                                if p % 2
                                else lexicographic_non_increase_constraint(
                                    post,
                                    [
                                        psm.eval_indexed(tmp, index)
                                        for psm in lex_psm[: p + 1]
                                    ],
                                    p,
                                    epsilon,
                                )
                                for post in lex_posts
                            ]
                        ),
                    ),
                    state,
                )
                # print(constraint, "\n")
                constraints.append(constraint)
    #         print()
    #     print()
    # print()

    return constraints


def lex_post(
    lex_psm: list[IndexedPolynomial], succ_distr: list[tuple[float, Valuation]], d: int
) -> list[list[ArithRef]]:
    """
    Enumerate all the possible lexicographic post of a distribution of successors induced by the
    successors over an indexed function.
    """

    lex_posts_succ_distr = [
        [
            [prob * psm.eval_indexed(succ, index) for psm in lex_psm[: d + 1]]
            for index in lex_psm[0].induced_indexes(lex_psm[0].get_index(succ))
        ]
        for prob, succ in succ_distr
    ]
    combinations = list(itertools.product(*lex_posts_succ_distr))
    return [[sum(i, RealVal(0)) for i in zip(*comb)] for comb in combinations]


def lexicographic_decrease_constraint(
    lhs: list[ArithRef], rhs: list[ArithRef], d: int, epsilon: ArithRef
) -> BoolRef:
    return Or(
        *[
            And(
                *[lhs[k] == rhs[k] for k in range(i)],
                lhs[i] <= rhs[i] - epsilon,
            )
            for i in range(d + 1)
        ]
    )


def lexicographic_non_increase_constraint(
    lhs: list[ArithRef], rhs: list[ArithRef], d: int, epsilon: ArithRef
) -> BoolRef:
    return Or(
        lexicographic_decrease_constraint(lhs, rhs, d - 1, epsilon),
        And(
            *[lhs[k] == rhs[k] for k in range(d)],
            lhs[d] <= rhs[d],
        ),
    )


def psm_constraints(
    system: ReactiveModule,
    invariant: IndexedPolynomial,
    lex_psm: list[IndexedPolynomial],
    parity_objectives: list[ParityObjective],
    state: Valuation,
    epsilon: ArithRef,
):
    return (
        non_negativity(system, invariant, lex_psm, state)
        + invariant_consecution(system, invariant, state)
        + drift(system, invariant, lex_psm, state, parity_objectives, epsilon)
    )


def guess(
    system: ReactiveModule,
    dataset: list[Valuation],
    parity_objectives: list[ParityObjective],
    epsilon: ArithRef,
):
    lex_psm_template = [
        IndexedPolynomial.template(
            f"V{i}",
            system.vars,
            {
                q: [IntVal(0), IntVal(1)],
                pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
                coin1: [IntVal(0), IntVal(1)],
            },
            2,
        )
        for i in range(len(parity_objectives))
    ]
    invariant_template = IndexedPolynomial.template(
        "I",
        system.vars,
        {
            q: [IntVal(0), IntVal(1)],
            pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
            coin1: [IntVal(0), IntVal(1)],
        },
        2,
    )

    # print("Guess constraints")
    constraints = []
    constraints.extend(invariant_initiation(system, invariant_template))
    for state in dataset:
        # print("State")
        # print(state)
        tmp = psm_constraints(
            system,
            invariant_template,
            lex_psm_template,
            parity_objectives,
            state,
            epsilon,
        )
        # for constraint in tmp:
        #     print(constraint)
        constraints.extend(tmp)
    solver = Solver()
    solver.add(*constraints)
    if solver.check() == unsat:
        raise Exception("No PSM candidate found!")
    model = solver.model()
    return [
        psm_template.instantiate(model) for psm_template in lex_psm_template
    ], invariant_template.instantiate(model)


def extract_counterexample(system: ReactiveModule, model: ModelRef) -> Valuation:
    return {var: extract_var(var, model) for var in system.vars}


def check(
    system: ReactiveModule,
    lex_psm: list[IndexedPolynomial],
    invariant: IndexedPolynomial,
    parity_objectives: list[ParityObjective],
    epsilon: ArithRef,
):
    constraints = [
        *invariant_initiation(system, invariant),
        *psm_constraints(
            system,
            invariant,
            lex_psm,
            parity_objectives,
            system.symbolic_state.copy(),
            epsilon,
        ),
    ]
    # print("Check constraints")
    # for constraint in constraints:
    #     print(constraint)
    counterexamples: list[Valuation] = []
    for constraint in constraints:
        solver = Solver()
        solver.add(constr := Not(constraint))
        result = solver.check()
        if result == sat:
            new_counterexample = extract_counterexample(system, solver.model())
            # Ensure that the counterexample is not already in the list
            if not any(
                all(new_counterexample[var] == old[var] for var in system.vars)
                for old in counterexamples
            ):
                counterexamples.append(new_counterexample)
                # print("Counterexample constraint:")
                # print(constr)
                # print("Model")
                # print(solver.model())

    return counterexamples


def guess_check(
    system: ReactiveModule, parity_objectives: list[ParityObjective], epsilon: ArithRef
):
    dataset = system.init.copy()
    print("Dataset")
    for state in dataset:
        print(state)
    for i in range(100):
        print(f"Guessing and checking iteration {i+1}\n")
        # print("Dataset")
        # for state in dataset:
        #     print(state)
        lex_psm, invariant = guess(system, dataset, parity_objectives, epsilon)
        # print("lex_psm")
        # print(lex_psm)
        # print("invariant")
        # print(invariant)
        counterexamples = check(system, lex_psm, invariant, parity_objectives, epsilon)
        if len(counterexamples) == 0:
            return lex_psm, invariant
        if any(
            any(
                all(state[var] == counterexample[var] for var in system.vars)
                for state in dataset
            )
            for counterexample in counterexamples
        ):
            print("Counterexamples already in dataset!")
        # print("New counterexamples")
        # for counterexample in counterexamples:
        #     print(counterexample)
        dataset.extend(counterexamples)

    raise ValueError("TIMEOUT: No PSM found!")


lex_psm_template = [
    IndexedPolynomial.template(
        f"V{i}",
        system.vars,
        {
            q: [IntVal(0), IntVal(1)],
            pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
            coin1: [IntVal(0), IntVal(1)],
        },
        2,
    )
    for i in range(len(parity_objectives))
]
invariant_template = IndexedPolynomial.template(
    "I",
    system.vars,
    {
        q: [IntVal(0), IntVal(1)],
        pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
        coin1: [IntVal(0), IntVal(1)],
    },
    2,
)

lex_psm, inv = guess_check(system, parity_objectives, RealVal(1))
print(lex_psm)
print(inv)

# constraints = psm_constraints(
#     system,
#     invariant_template,
#     lex_psm_template,
#     parity_objectives,
#     system.symbolic_state,
#     Real("epsilon"),
# )
# invariant_consecution(system, invariant_template, system.symbolic_state)
# drift(
#     system,
#     invariant_template,
#     lex_psm_template,
#     system.symbolic_state,
#     parity_objectives,
#     Real("epsilon"),
# )

# v_1_0_coin = Polynomial(
#     [counter],
#     2,
#     RealVal(-3) * counter**2 + RealVal(18) * counter + RealVal(-15),
# )
# v_1_1_0 = Polynomial(
#     [counter],
#     2,
#     RealVal(-3) * counter**2 + RealVal(24) * counter + RealVal(-34),
# )
# v_1_1_1 = Polynomial(
#     [counter],
#     2,
#     RealVal(-3) * counter**2 + RealVal(12) * counter + RealVal(2),
# )
# v_1_2_coin = Polynomial(
#     [counter],
#     2,
#     RealVal(-3) * counter**2 + RealVal(18) * counter + RealVal(-14),
# )
# v0 = Polynomial([counter], 2, RealVal(0))
# v05 = Polynomial([counter], 2, RealVal(0.6))
# v_neg = Polynomial([counter], 2, RealVal(-1))
# v_true = IndexedPolynomial(
#     system.vars,
#     {
#         q: [IntVal(0), IntVal(1)],
#         pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
#         coin1: [IntVal(0), IntVal(1)],
#     },
#     [
#         # 0,0,0
#         v0,
#         # 0,0,1
#         v0,
#         # 0,1,0
#         v0,
#         # 0,1,1
#         v0,
#         # 0,2,0
#         v0,
#         # 0,2,1
#         v0,
#         # 0,3,0
#         v0,
#         # 0,3,1
#         v0,
#         # 1,0,0
#         v0,
#         # 1,0,1
#         v0,
#         # 1,1,0
#         v0,
#         # 1,1,1
#         v0,
#         # 1,2,0
#         v0,
#         # 1,2,1
#         v0,
#         # 1,3,0
#         v05,
#         # 1,3,1
#         v05,
#     ],
# )
# hand_lexpsm = [
#     IndexedPolynomial(
#         system.vars,
#         {
#             q: [IntVal(0), IntVal(1)],
#             pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
#             coin1: [IntVal(0), IntVal(1)],
#         },
#         [
#             # 0,0,0
#             v0,
#             # 0,0,1
#             v0,
#             # 0,1,0
#             v0,
#             # 0,1,1
#             v0,
#             # 0,2,0
#             v0,
#             # 0,2,1
#             v0,
#             # 0,3,0
#             v0,
#             # 0,3,1
#             v0,
#             # 1,0,0
#             v_1_0_coin,
#             # 1,0,1
#             v_1_0_coin,
#             # 1,1,0
#             v_1_1_0,
#             # 1,1,1
#             v_1_1_1,
#             # 1,2,0
#             v_1_2_coin,
#             # 1,2,1
#             v_1_2_coin,
#             # 1,3,0
#             v0,
#             # 1,3,1
#             v0,
#         ],
#     ),
#     v_true,
# ]
# i_1 = Polynomial(
#     [counter],
#     2,
#     RealVal(-1) * counter**2 + RealVal(6) * counter + RealVal(-8),
# )
# i_2 = Polynomial(
#     [counter],
#     2,
#     RealVal(-1) * counter**2 + RealVal(6) * counter + RealVal(-5),
# )
# c_1 = Polynomial(
#     [counter],
#     2,
#     RealVal(-1) * counter**2 + RealVal(2) * counter + RealVal(-1),
# )
# c_5 = Polynomial(
#     [counter],
#     2,
#     RealVal(-1) * counter**2 + RealVal(10) * counter + RealVal(-25),
# )
# invariant = IndexedPolynomial(
#     system.vars,
#     {
#         q: [IntVal(0), IntVal(1)],
#         pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
#         coin1: [IntVal(0), IntVal(1)],
#     },
#     [
#         # 0,0,0
#         v_neg,
#         # 0,0,1
#         v_neg,
#         # 0,1,0
#         v_neg,
#         # 0,1,1
#         v_neg,
#         # 0,2,0
#         v_neg,
#         # 0,2,1
#         v_neg,
#         # 0,3,0
#         v0,
#         # 0,3,1
#         v0,
#         # 1,0,0
#         i_1,
#         # 1,0,1
#         v_neg,
#         # 1,1,0
#         i_1,
#         # 1,1,1
#         i_1,
#         # 1,2,0
#         i_2,
#         # 1,2,1
#         v_neg,
#         # 1,3,0
#         c_1,
#         # 1,3,1
#         c_5,
#     ],
# )
# counterexamples = check(system, hand_lexpsm, invariant, parity_objectives, RealVal(0.5))
# print("Counterexamples")
# print(counterexamples)

# lex_psm, inv = psm.guess_check_polynomial(
#     system,
#     automata_states,
#     [q == IntVal(0), q == IntVal(1)],
#     IntVal(1),
#     {
#         q: [IntVal(0), IntVal(1)],
#         pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
#         coin1: [IntVal(0), IntVal(1)],
#     },
#     2,
# )
# # tree_lex_psm, inv = psm.guess_check_tree_psm(
# #     system, automata_states, [q == IntVal(0), q == IntVal(1)], IntVal(1)
# # )
# # lin_lex_psm, inv = psm.monolithic(
# #     system, [IntVal(0), IntVal(1)], [q == IntVal(0), q == IntVal(1)], IntVal(1.0)
# # )
# # lin_lex_psm, inv = psm.strict_proof_rule([0, 1], [q == 0, q == 1], 1.0)
#
# print("Invariant:")
# print(inv.symbolic)
# print("LexPSM:")
# print(lex_psm)
