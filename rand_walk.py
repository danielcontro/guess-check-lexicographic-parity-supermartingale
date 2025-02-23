import itertools
import random
from z3 import (
    And,
    Int,
    IntVal,
    RealVal,
)

from functions import IndexedPolynomial
from reactive_module import (
    GuardedCommand,
    LinearFunction,
    ReactiveModule,
    StateUpdate,
    UpdateDistribution,
    Variable,
)

from guess_check import guess_check

x = Int("x")
q = Int("q")

fx0 = LinearFunction([x], IntVal(0))
fx_dec = LinearFunction([x], x - IntVal(1))
fx_inc = LinearFunction([x], x + IntVal(1))
fx_id = LinearFunction([x], x)
fq0 = LinearFunction([q], IntVal(0))
fq1 = LinearFunction([q], IntVal(1))

K = 100
T = 10
p = 0.75

gc = [
    # GuardedCommand(
    #     And(x >= IntVal(T + 1), q == 0),
    #     UpdateDistribution([x], [(1, StateUpdate([x, q], {x: fx_id, q: fq0}))]),
    # ),
    GuardedCommand(
        And(x >= IntVal(T + 1), q == 1),
        UpdateDistribution(
            [x],
            [
                (p, StateUpdate([x, q], {x: fx_dec, q: fq1})),
                (1 - p, StateUpdate([x, q], {x: fx_id, q: fq1})),
            ],
        ),
    ),
    # GuardedCommand(
    #     x < IntVal(T),
    #     UpdateDistribution([x], [(1, StateUpdate([x, q], {x: fx_id, q: fq1}))]),
    # ),
    GuardedCommand(
        x == IntVal(T),
        UpdateDistribution([x], [(1, StateUpdate([x, q], {x: fx_id, q: fq0}))]),
    ),
]
system = ReactiveModule(
    [{x: IntVal(K), q: IntVal(1)}],
    [q, x],
    gc,
    And(x >= 0, q >= 0, q <= 1),
    [IntVal(0), IntVal(1)],
)

dataset = list(
    map(
        lambda var: {x: var[1], q: var[0]},
        itertools.product([IntVal(0), IntVal(1)], [IntVal(i) for i in range(K + 1)]),
    )
)

lex_psm, invariant = guess_check(
    system,
    [q == 0, q == 1],
    RealVal(1),
    {q: [IntVal(0), IntVal(1)]},
    1,
    dataset,
)
print("Invariant:")
print(invariant)
print("LexPSM:")
for psm in lex_psm:
    print(psm)
