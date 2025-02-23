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

# x = Int("x")
# q = Int("q")
#
# fx0 = LinearFunction([x], IntVal(0))
# fx_dec = LinearFunction([x], x - IntVal(1))
# fx_inc = LinearFunction([x], x + IntVal(1))
# fx_id = LinearFunction([x], x)
# fq0 = LinearFunction([q], IntVal(0))
# fq1 = LinearFunction([q], IntVal(1))
#
# K = 100
# T = 10
# p = 0.75
#
# gc = [
#     # GuardedCommand(
#     #     And(x >= IntVal(T + 1), q == 0),
#     #     UpdateDistribution([x], [(1, StateUpdate([x, q], {x: fx_id, q: fq0}))]),
#     # ),
#     GuardedCommand(
#         And(x >= IntVal(T + 1), q == 1),
#         UpdateDistribution(
#             [x],
#             [
#                 (p, StateUpdate([x, q], {x: fx_dec, q: fq1})),
#                 (1 - p, StateUpdate([x, q], {x: fx_id, q: fq1})),
#             ],
#         ),
#     ),
#     # GuardedCommand(
#     #     x < IntVal(T),
#     #     UpdateDistribution([x], [(1, StateUpdate([x, q], {x: fx_id, q: fq1}))]),
#     # ),
#     GuardedCommand(
#         x == IntVal(T),
#         UpdateDistribution([x], [(1, StateUpdate([x, q], {x: fx_id, q: fq0}))]),
#     ),
# ]
# system = ReactiveModule(
#     [{x: IntVal(K), q: IntVal(1)}],
#     [q, x],
#     gc,
#     And(x >= 0, q >= 0, q <= 1),
#     [IntVal(0), IntVal(1)],
# )
#
# dataset = list(
#     map(
#         lambda var: {x: var[1], q: var[0]},
#         itertools.product([IntVal(0), IntVal(1)], [IntVal(i) for i in range(K + 1)]),
#     )
# )
#
# lex_psm, invariant = guess_check(
#     system,
#     [q == 0, q == 1],
#     RealVal(1),
#     {q: [IntVal(0), IntVal(1)]},
#     1,
#     dataset,
# )
# print("Invariant:")
# print(invariant)
# print("LexPSM:")
# for psm in lex_psm:
#     print(psm)
