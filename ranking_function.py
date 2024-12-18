from z3 import And, Implies, Int, IntVal, Solver, unsat
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
        [x, q], [(1, StateUpdate([x, q], {x: LinearFunction([x], x - 1), q: f1}))]
    ),
)

gc2 = GuardedCommand(
    x <= 0,
    UpdateDistribution(
        [x, q], [(1, StateUpdate([x], {x: LinearFunction([x], x), q: f0}))]
    ),
)

system = ReactiveModule(
    [{x: IntVal(10), q: IntVal(1)}], [x, q], [gc1, gc2], And(x <= 10, q <= 1, q >= 0)
)

verifier = Verification(system)

spm, inv = verifier.guess_check(
    system, [IntVal(0), IntVal(1)], [q == 0, q == 1], IntVal(1)
)

print("Invariant:", inv)
print("SPM:", spm)

# ranking_template = LinearTemplate("V", [x])
# invariant_template = LinearTemplate("I", [x])
# epsilon = 1
# dataset = system.init.copy()
# for i in range(10):
#     """
#     inv-init: (∀ init).I(init) >= 0
#     inv-consec: (∀ s).(∀ s' | s -> s'). I(s) >= 0 => I(s') >= 0
#     drift: (∀ s).(∀ s' | s -> s') I(s) >= 0 ∧ not_terminated(s) => V(s') <= V(s) - epsilon
#     non_neg: (∀ s). I(s) >= 0 => V(s) >= 0
#     """
#     inv_init = [invariant_template(init) >= 0 for init in system.init]
#     inv_consec = [
#         Implies(
#             And(
#                 invariant_template(s) >= 0,
#                 # substitute_state(system.state_space, s),
#                 s[x] > 0,  # not terminated
#             ),
#             invariant_template(s1) >= 0,
#         )
#         for s in dataset
#         for successors in system(s)
#         for _, s1 in successors
#     ]
#     drift = [
#         Implies(
#             And(
#                 invariant_template(s) >= 0,
#                 # substitute_state(system.state_space, s),
#                 s[x] > 0,  # not terminated
#             ),
#             ranking_template(s1) <= ranking_template(s) - epsilon,
#         )
#         for s in dataset
#         for l in system(s)
#         for _, s1 in l
#     ]
#     non_neg = [
#         Implies(
#             And(
#                 invariant_template(s) >= 0,
#                 # substitute_state(system.state_space, s),
#             ),
#             ranking_template(s) >= 0,
#         )
#         for s in dataset
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
#     print("Inv-Init")
#     for constraint in inv_init:
#         print(constraint)
#     print("Inv-Consec")
#     for constraint in inv_consec:
#         print(constraint)
#     print("Drift")
#     for constraint in drift:
#         print(constraint)
#     print("Non-neg")
#     for constraint in non_neg:
#         print(constraint)
#     print("Guess Model")
#     print(guesser.model())
#     print("Ranking Candidate:")
#     print(ranking_candidate.symbolic)
#     print("Invariant Candidate:")
#     print(invariant_candidate.symbolic)
#
#     """
#     inv-init: (∃ x ∈ init).I(x) < 0
#     inv-consec: (∃ x ∈ S).(∀ (g, U) ∈ RM).(∀ u ∈ U). I(x) >= 0 ∧ g(x) ∧ I(u(x)) < 0
#     drift: (∃ x ∈ S).(∀ (g, U) ∈ RM).(∀ u ∈ U). I(x) >= 0 ∧ g(x) ∧ not_terminated(x) ∧ V(u(x)) > V(x) - epsilon
#     non_neg: (∃ x ∈ S). I(x) >= 0 ∧ V(x) < 0
#     """
#     check_inv_init = [invariant_candidate(init) < 0 for init in system.init]
#     check_inv_consec = [
#         And(
#             invariant_candidate.symbolic >= 0,
#             # system.state_space,
#             gc.guard,
#             invariant_candidate(update.symbolic_successor()) < 0,
#         )
#         for gc in system.guarded_commands
#         for update in gc.command.updates
#     ]
#     check_drift = [
#         And(
#             invariant_candidate.symbolic >= 0,
#             gc.guard,
#             # system.state_space,
#             x > 0,  # not_terminated
#             ranking_candidate(update.symbolic_successor())
#             > ranking_candidate.symbolic - epsilon,
#         )
#         for gc in system.guarded_commands
#         for update in gc.command.updates
#     ]
#     check_non_neg = [
#         And(
#             invariant_candidate.symbolic >= 0,
#             ranking_candidate.symbolic < 0,
#             # system.state_space,
#         )
#     ]
#     check_constraints = check_inv_init + check_inv_consec + check_drift + check_non_neg
#     counterexamples = []
#     checker = Solver()
#     for constraint in check_constraints:
#         # c = And(constraint, *[x != ce[x] for ce in (dataset + counterexamples)])
#         c = And(constraint, *[x != ce[x] for ce in counterexamples])
#         print("Constraint:", c)
#         if checker.check(c) == unsat:
#             print("Unsat")
#             continue
#         print("Sat")
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
#         print(invariant_candidate.symbolic)
#         print("Ranking function:")
#         print(ranking_candidate.symbolic)
#         break
#
#     dataset = dataset + counterexamples
#     print("Dataset:")
#     for data in dataset:
#         print(data)
#
#     """
#     encoding without quantifiers
#     spm_conditions(module, parity_objective, epsilon, spm_template, inv_template, state) -> list[BoolRef]:
#         inv-init:
#         inv-conses:
#         drift:
#
#     guess(module, parity_objective, epsilon, dataset) -> tuple[LinearFunction, LinearFunction]:
#         spm_template = LinearTemplate("V", module.vars)
#         inv_template = LinearTemplate("I", module.vars)
#         constraints = []
#         for state in dataset:
#             constraints.extend(spm_conditions(module, parity_objective, epsilon, spm_template, inv_template, state))
#
#         guesser = Solver()
#         guesser.add(*constraints)
#         if guesser.check() == unsat:
#             return None
#
#     check(module, parity_objective, epsilon, spm, inv) -> list[State]:
#         state = module.symbolic_state
#         constraints = spm_conditions(module, parity_objective, epsilon, spm, inv, state))
#         checker = Solver()
#         counterexamples = []
#         for constraint in constraints:
#             c = And(Not(constraint), *[x != ce[x] for ce in counterexamples])
#             if checker.check(c) == unsat:
#                 continue
#             counterexamples.append(
#                 {x: val if (val := checker.model()[x]) is not None else 0}
#             )
#         if len(counterexamples) == 0:
#             return spm, inv
#
#     guess_check(module, parity_objective, epsilon) -> tuple[LinearFunction, LinearFunction]:
#         dataset = module.init
#         for i in range(CUTOFF):
#             spm, inv = guess(module, parity_objective, epsilon, dataset)
#             if spm is None:
#                 break
#             counterexamples = check(module, parity_objective, epsilon, spm, inv)
#             assert forall(counterexamples, lambda x: x not in dataset)
#             if len(counterexamples) == 0:
#                 return spm, inv
#             dataset = dataset + counterexamples
#
#     monolithic(module, parity_objective, epsilon) -> tuple[LinearFunction, LinearFunction]:
#         spm_template = QLinearTemplate("V", module.states, module.vars)
#         inv_template = QLinearTemplate("I", module.vars)
#         state = module.symbolic_state
#         constraints = spm_conditions(module, parity_objective, epsilon, spm_template, inv_template, state)
#         query = Exists(spm_template.vars+inv_template.vars, ForAll(state, And(*constraints)))
#
#     """
