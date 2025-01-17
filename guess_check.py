import itertools
from typing import Optional
from utils import extract_var, is_value, satisfiable, substitute_state
from functions import IndexedPolynomial, Valuation, Value, Variable
from reactive_module import ReactiveModule
from lex_psm import ParityObjective
import matplotlib.pyplot as plt

from z3 import (
    And,
    ArithRef,
    BoolRef,
    Implies,
    Int,
    IntNumRef,
    IntVal,
    ModelRef,
    Not,
    Or,
    RealVal,
    Solver,
    simplify,
    unsat,
)


def extract_index(state: Valuation, indexing: list[Variable]):
    return tuple(state[var] for var in indexing)


def index_constraint(index: tuple[Value, ...], f: IndexedPolynomial) -> BoolRef:
    return And(*[var == index[i] for i, var in enumerate(f.indexing_ordering)])


def invariant_initiation(
    system: ReactiveModule, invariant: IndexedPolynomial
) -> list[BoolRef]:
    return [inv_i > 0 for init in system.init.copy() for inv_i in invariant.eval(init)]


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
                        invariant.eval_indexed(state, index) > 0,
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


def invariant_consecution(
    system: ReactiveModule, invariant: IndexedPolynomial, state: Valuation
) -> list[BoolRef]:
    # print("Invariant consecution")
    constraints = []
    for gc in system.guarded_commands:
        for index in invariant.induced_indexes(invariant.get_index(state)):
            # print("Index", index)
            # print("State", state)
            for update in gc.updates:
                # print("guard", gc.guard)
                # print("update", update.symbolic_successor)
                if not satisfiable(
                    premise := substitute_state(
                        And(
                            system.state_space,
                            gc.guard,
                            index_constraint(index, invariant),
                            invariant.eval_indexed(state, index) > 0,
                        ),
                        state,
                    )
                ):
                    continue

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
                succ_indexes = invariant.induced_indexes(invariant.get_index(succ))
                assert len(succ_indexes) == 1
                # for succ_index in succ_indexes:
                constraint = substitute_state(
                    Implies(
                        premise,
                        invariant.eval_indexed(
                            succ, extract_index(succ, invariant.indexing_ordering)
                        )
                        > 0,
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
    for p, objective in enumerate(parity_objectives):
        # print("P:", p, "Objective", objective)
        for gc in system.guarded_commands:
            # print("Guard", gc.guard)
            # print("Updates")
            # for p, update in gc.command.distribution:
            #     print(f"{p}: {update.symbolic_successor}")
            for index in invariant.induced_indexes(invariant.get_index(state)):
                # print("Invariant Index", index)
                # print("Before", state)
                indexed_state = {
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
                            objective,
                            gc.guard,
                            index_constraint(index, invariant),
                            invariant.eval_indexed(state, index) > 0,
                        ),
                        state,
                    )
                ):
                    continue
                # TODO: LexPSM[T] type to handle this
                # for index in lex_psm[0].induced_indexes(lex_psm[0].get_index(state)):
                # print("Lex Index", index)
                # print("Lex Posts")
                # print(lex_posts)
                constraint = substitute_state(
                    Implies(
                        premise,
                        lexicographic_decrease_constraint(
                            lex_post(lex_psm, gc.command(indexed_state), p),
                            [
                                psm.eval_indexed(state, index)
                                for psm in lex_psm[: p + 1]
                            ],
                            p,
                            epsilon,
                        )
                        if p % 2
                        else lexicographic_non_increase_constraint(
                            lex_post(lex_psm, gc.command(indexed_state), p),
                            [
                                psm.eval_indexed(state, index)
                                for psm in lex_psm[: p + 1]
                            ],
                            p,
                            epsilon,
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
) -> list[ArithRef]:
    """
    Enumerate all the possible lexicographic post of a distribution of successors induced by the
    successors over an indexed function.
    """

    return [
        simplify(sum(
            (
                p * psm.eval_indexed(succ, extract_index(succ, psm.indexing_ordering))
                for p, succ in succ_distr
            ),
            RealVal(0),
        ))
        for psm in lex_psm[: d + 1]
    ]


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
    non_neg = non_negativity(system, invariant, lex_psm, state)
    inv_cons = invariant_consecution(system, invariant, state)
    drift_cond = drift(system, invariant, lex_psm, state, parity_objectives, epsilon)
    return non_neg + inv_cons + drift_cond


def guess(
    system: ReactiveModule,
    dataset: list[Valuation],
    parity_objectives: list[ParityObjective],
    epsilon: ArithRef,
    indexing: dict[Variable, list[Value]],
    degree: int = 1,
):
    # print("Guessing")
    lex_psm_template = [
        IndexedPolynomial.template(
            f"V{i}",
            system.vars,
            indexing,
            degree,
        )
        for i in range(len(parity_objectives))
    ]
    invariant_template = IndexedPolynomial.template(
        "I",
        system.vars,
        indexing,
        degree,
    )
    # print("Guess constraints")

    constraints = invariant_initiation(system, invariant_template) + list(
        itertools.chain(
            *[
                psm_constraints(
                    system,
                    invariant_template,
                    lex_psm_template,
                    parity_objectives,
                    state,
                    epsilon,
                )
                for state in dataset
            ]
        )
    )
    # for state in dataset:
    #     # print("State")
    #     # print(state)
    #     tmp =
    #     # for constraint in tmp:
    #     #     print(constraint)
    #     constraints.extend(tmp)
    solver = Solver()
    solver.add(*constraints)
    # print("Constraints created")
    if solver.check() == unsat:
        raise Exception("No PSM candidate found!")
    model = solver.model()
    # print("Guess model parameters", len(model.decls()))

    # print("Guessing Done")
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
    # print("Checking")
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
    # print("Constraints created")
    for constraint in constraints:
        solver = Solver()
        solver.add(constr := And(system.state_space, Not(constraint)))
        # print("New check")
        result = solver.check()
        if not result == unsat:
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

    # print("Check done")
    return counterexamples


def guess_check(
    system: ReactiveModule,
    parity_objectives: list[ParityObjective],
    epsilon: ArithRef,
    indexing: dict[Variable, list[Value]],
    degree: int = 1,
    plot_range: int = 10,
    dataset: Optional[list[Valuation]] = None,):
    if dataset is None:
        dataset = system.init.copy()
    # print("Dataset")
    #
    # iter_counterexample = {}
    # for state in dataset:
    #     print(state)
    for i in range(100):
        print(f"Guessing and checking iteration {i + 1}\n")
        # print("Dataset")
        # for state in dataset:
        #     print(state)
        lex_psm, invariant = guess(
            system, dataset, parity_objectives, epsilon, indexing, degree
        )
        print("lex_psm")
        for psm in lex_psm:
            print(psm)
        print("invariant")
        print(invariant)

        plot_lexpsm(lex_psm, invariant, system, plot_range, i)
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
        print("New counterexamples")
        for counterexample in counterexamples:
            print(counterexample)
        dataset.extend(counterexamples)

    raise ValueError("TIMEOUT: No PSM found!")

def plot_lexpsm(lex_psm, inv, system: ReactiveModule, plot_range, i):
    xs = [i for i in range(plot_range + 1)]
    pc_range = 4
    coin_range = 2
    fig, ax = plt.subplots(pc_range, coin_range, figsize=(20, 15))
    fig.suptitle(f"LexPSM (1,pc,coin1) iter {i}")
    for coin in range(coin_range):
        ax[0, coin].set_title(f"coin1={coin}")
        for pc in range(pc_range):
            index = (IntVal(1), IntVal(pc), IntVal(coin))
            posts = [lex_post(lex_psm, list(itertools.chain(*system({Int("counter"): IntVal(x), Int("pc1"): IntVal(pc), Int("q"): IntVal(1), Int("coin1"): IntVal(coin)}))), len(lex_psm)) for x in xs]
            for p in range(len(lex_psm)):
                ys = [
                    real_to_float(lex_psm[p].eval_indexed({Int("counter"): IntVal(x)}, index))
                    for x in xs
                ]
                post = [
                    real_to_float(posts[x][p])
                    for x in xs
                ]
                eps = [ys[i] - post[i] for i in range(len(ys))]
                if p == 0:
                    ax[pc, coin].plot(xs, ys, color="orange", linestyle="-", label="V0")
                    ax[pc, coin].plot(xs, post, color="orange", linestyle="--", label="PostV0")
                    ax[pc, coin].plot(xs, eps, color="green", linestyle="-", label="eps_V0")
                else:
                    ax[pc, coin].plot(xs, ys, color="red", linestyle="-", label="V1")
                    ax[pc, coin].plot(xs, ys, color="red", linestyle="--", label="PostV1")
                    ax[pc, coin].plot(xs, eps, color="lightgreen", linestyle="-", label="eps_V1")
            ys = [
                real_to_float(inv.eval_indexed({Int("counter"): IntVal(x)}, index)) for x in xs
            ]
            ax[pc, coin].plot(xs, ys, color="blue", label="inv")
            ax[pc, coin].set_ylabel(f"pc={pc}")
            ax[pc, coin].spines["top"].set_color("none")
            ax[pc, coin].spines["bottom"].set_position("zero")
            ax[pc, coin].spines["left"].set_position("zero")
            ax[pc, coin].spines["right"].set_color("none")
            ax[pc, coin].set_ylim(-2, 5)
    ax[0, 1].legend()
    # for ax in fig.get_axes():
    #     ax.label_outer()
    plt.savefig(f"./out/consensus/{i}.png")
    plt.show()

def real_to_float(real: ArithRef) -> float:
    if real is None:
        print("Real is None")
        return 0.0
    assert real.is_real()
    try:
        fract = real.as_fraction()
        return float(fract.numerator) / float(fract.denominator)
    except Exception as e:
        print(type(real), real)
        raise e
