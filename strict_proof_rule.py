from z3 import And, ForAll, Implies, Int, Or, Solver, unsat
from reactive_module import (
    GuardedCommand,
    LinearFunction,
    ReactiveModule,
    StateUpdate,
    UpdateDistribution,
)
from template import LinearTemplate

x = Int("x")
gc1 = GuardedCommand(
    x > 0,
    UpdateDistribution(
        [x],
        [
            (0.9, StateUpdate([x], {x: LinearFunction([x], x - 1)})),
            (0.1, StateUpdate([x], {x: LinearFunction([x], x + 1)})),
        ],
    ),
)
gc2 = GuardedCommand(
    x <= 0,
    UpdateDistribution([x], [(1, StateUpdate([x], {x: LinearFunction([x], x)}))]),
)

system = ReactiveModule([{x: 10}], [x], [gc1, gc2], True)

ranking_template = LinearTemplate("V", [x])
invariant_template = LinearTemplate("I", [x])
epsilon = 1
"""
inv-init: (∀ init).I(init) >= 0
inv-consec: (∀ s). I(s) >= 0 => I(s') >= 0
drift: (∀ s). I(s) >= 0 => 𝔼[V(s')] <= V(s) - epsilon
non_neg: (∀ s). I(s) >= 0 => V(s) >= 0
"""
inv_init = [invariant_template(init) >= 0 for init in system.init]
inv_consec = [
    ForAll(
        [x],
        Implies(
            And(invariant_template({x: x}) >= 0, gc.guard, x > 0),
            invariant_template(u({x: x})) >= 0,
        ),
    )
    for gc in system.guarded_commands
    for u in gc.command.updates
]
drift = [
    ForAll(
        [x],
        Implies(
            And(invariant_template({x: x}) >= 0, x > 0, gc.guard),
            ranking_template.post_exp(gc.command.symbolic_successors())
            <= ranking_template({x: x}) - epsilon,
        ),
    )
    for gc in system.guarded_commands
]
non_neg = [
    ForAll([x], Implies(invariant_template({x: x}) >= 0, ranking_template({x: x}) >= 0))
]
solver = Solver()
guesser_constraints = inv_init + inv_consec + drift + non_neg
solver.add(*guesser_constraints)
if solver.check() == unsat:
    print("No solution guessing!")
else:
    ranking_candidate = ranking_template.instantiate(solver.model())
    invariant_candidate = invariant_template.instantiate(solver.model())
    print("Constraints:")
    for constraint in guesser_constraints:
        print(constraint)
    print("Model")
    print(solver.model())

    print("Invariant and ranking function found!")
    print("Invariant:")
    print(invariant_candidate.f)
    print("Ranking function:")
    print(ranking_candidate.f)
