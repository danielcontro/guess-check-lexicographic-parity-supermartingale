from z3 import And, Implies, Int, IntVal, Or, Solver, unsat
from lex_psm import Verification
from reactive_module import (
    GuardedCommand,
    LinearFunction,
    ReactiveModule,
    StateUpdate,
    UpdateDistribution,
)
from template import LinearTemplate

x = Int("x")
q = Int("q")
f0 = LinearFunction([], IntVal(0))
f1 = LinearFunction([], IntVal(1))
gc1 = GuardedCommand(
    And(x > 0, q == 1),
    UpdateDistribution(
        [x, q],
        [
            (0.6, StateUpdate([x, q], {x: LinearFunction([x], x - 1), q: f1})),
            (0.4, StateUpdate([x, q], {x: LinearFunction([x], x + 1), q: f1})),
        ],
    ),
)
gc2 = GuardedCommand(
    x <= 0,
    UpdateDistribution(
        [x, q], [(1, StateUpdate([x, q], {x: LinearFunction([x], x), q: f0}))]
    ),
)

system = ReactiveModule(
    [{x: 10, q: IntVal(1)}], [x, q], [gc1, gc2], And(x >= 0, q <= 1, q >= 0)
)

verifier = Verification(system)
psm, inv = verifier.guess_check(
    system, [IntVal(0), IntVal(1)], [q == 0, q == 1], IntVal(1)
)
print("Invariant:", inv)
print("PSM:", psm)


# ranking_template = LinearTemplate("V", [x])
# invariant_template = LinearTemplate("I", [x])
# epsilon = 1
# dataset = system.init.copy()
# for i in range(100):
#     """
#     inv-init: (∀ init).I(init) >= 0
#     inv-consec: (∀ s). I(s) >= 0 => I(s') >= 0
#     drift: (∀ s). I(s) >= 0 => 𝔼[V(s')] <= V(s) - epsilon
#     non_neg: (∀ s). I(s) >= 0 => V(s) >= 0
#     """
#     inv_init = [invariant_template(init) >= 0 for init in system.init]
#     inv_consec = [
#         Implies(invariant_template(s) >= 0, invariant_template(s1) >= 0)
#         for s in dataset
#         for l in system(s)
#         for _, s1 in l
#     ]
#     drift = [
#         Implies(
#             invariant_template(s) >= 0,
#             ranking_template.post_exp(post) <= ranking_template(s) - epsilon,
#         )
#         for s in dataset
#         for post in system(s)
#     ]
#     non_neg = [
#         Implies(invariant_template(s) >= 0, ranking_template(s) >= 0) for s in dataset
#     ]
#     guesser = Solver()
#     guesser_constraints = inv_init + inv_consec + drift + non_neg
#     guesser.add(*guesser_constraints)
#     if guesser.check() == unsat:
#         print("No solution guessing!")
#         break
#     ranking_candidate = ranking_template.instantiate(guesser.model())
#     invariant_candidate = invariant_template.instantiate(guesser.model())
#     print("Guess Constraints:")
#     for constraint in guesser_constraints:
#         print(constraint)
#     print("Guess Model")
#     print(guesser.model())
#
#     """
#     inv-init: (∃ x ∈ init).I(x) < 0
#     inv-consec: (∃ x ∈ S). I(x) >= 0 ∧ I(x') < 0
#     drift: (∃ x ∈ S). I(x) >= 0 ∧ 𝔼[V(x')] > V(x) - epsilon
#     non_neg: (∃ x ∈ S). I(x) >= 0 ∧ V(x) < 0
#     """
#     check_inv_init = [invariant_candidate(init) < 0 for init in system.init]
#     check_inv_consec = [
#         And(
#             invariant_candidate.f >= 0,
#             invariant_candidate(update.symbolic_successor()) < 0,
#         )
#         for gc in system.guarded_commands
#         for update in gc.command.updates
#     ]
#     check_drift = [
#         And(
#             invariant_candidate.f >= 0,
#             ranking_candidate.post_exp(gc.command.symbolic_successors())
#             > ranking_candidate.f - epsilon,
#         )
#         for gc in system.guarded_commands
#     ]
#     check_non_neg = [invariant_candidate.f >= 0, ranking_candidate.f < 0]
#     check_constraints = check_inv_init + check_inv_consec + check_drift + check_non_neg
#     counterexamples = []
#     checker = Solver()
#     for constraint in check_constraints:
#         c = And(constraint, *[x != ce[x] for ce in counterexamples])
#         print(c)
#         if checker.check(c) == unsat:
#             print("Unsat constraint:")
#             continue
#         print("Check Model:")
#         print(checker.model())
#         counterexamples.append(
#             {x: val if (val := checker.model()[x]) is not None else 0}
#         )
#         print("Counterexample:", counterexamples[-1])
#
#     if len(counterexamples) == 0:
#         print("Invariant and ranking function found!")
#         print("Invariant:")
#         print(invariant_candidate.f)
#         print("Ranking function:")
#         print(ranking_candidate.f)
#         break
#
#     dataset.extend(counterexamples)
