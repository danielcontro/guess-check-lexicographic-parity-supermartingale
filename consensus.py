import itertools
from z3 import (
    And,
    Int,
    IntVal,
    Real,
    RealVal,
)

from functions import IndexedPolynomial, Polynomial
from reactive_module import (
    GuardedCommand,
    LinearFunction,
    ReactiveModule,
    StateUpdate,
    UpdateDistribution,
    Variable,
)

from guess_check import guess_check


N = 1
K = 2**17
RANGE = 2 * (K + 1) * N
COUNTER_INIT = (K + 1) * N
LEFT = N
RIGHT = 2 * (K + 1) * N - N


coin1 = Int("coin1")
pc1 = Int("pc1")
counter = Int("counter")
q = Int("q")
state_space = And(
    counter >= 0,
    counter <= RANGE,
    coin1 >= 0,
    coin1 <= 1,
    pc1 >= 0,
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
    [IntVal(0), IntVal(1)],
)

parity_objectives = [q == IntVal(0), q == IntVal(1)]

indexing = {
    q: [IntVal(0), IntVal(1)],
    pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
    coin1: [IntVal(0), IntVal(1)],
}


# dataset = system.init.copy() + [
#     {var: IntVal(random.sample(type_invariant[var], 1)[0]) for var in system.vars}
#     for sample in range(SAMPLES)
# ]
#
# for state in dataset:
#     print(state)


even_dataset = system.init.copy() + list(
    map(
        lambda val: {q: val[0], pc1: val[1], coin1: val[2], counter: val[3]},
        itertools.product(
            [IntVal(0), IntVal(1)],
            [IntVal(i) for i in range(4)],
            [IntVal(0), IntVal(1)],
            [IntVal(i) for i in range(0, RANGE + 1, 2)],
        ),
    )
)

odd_dataset = system.init.copy() + list(
    map(
        lambda val: {q: val[0], pc1: val[1], coin1: val[2], counter: val[3]},
        itertools.product(
            [IntVal(0), IntVal(1)],
            [IntVal(i) for i in range(4)],
            [IntVal(0), IntVal(1)],
            [IntVal(i) for i in range(1, RANGE + 1, 2)],
        ),
    )
)
invariant_k_2 = IndexedPolynomial(
    system.vars,
    {
        q: [IntVal(0), IntVal(1)],
        pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
        coin1: [IntVal(0), IntVal(1)],
    },
    [
        Polynomial([counter], 2, RealVal(0)),
        Polynomial([counter], 2, RealVal(0)),
        Polynomial([counter], 2, RealVal(0)),
        Polynomial(
            [counter],
            2,
            RealVal(-2) / RealVal(85) * counter
            + RealVal(1) / RealVal(170) * counter**2,
        ),
        Polynomial([counter], 2, RealVal(0)),
        Polynomial([counter], 2, RealVal(0)),
        Polynomial(
            [counter],
            2,
            RealVal(1) / RealVal(17) * counter + RealVal(-1) / RealVal(34) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(-12) / RealVal(17)
            + RealVal(5) / RealVal(17) * counter
            + RealVal(-1) / RealVal(34) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(-5) / RealVal(102)
            + RealVal(1) / RealVal(17) * counter
            + RealVal(-1) / RealVal(102) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(-5) / RealVal(102)
            + RealVal(1) / RealVal(17) * counter
            + RealVal(-1) / RealVal(102) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(-5) / RealVal(102)
            + RealVal(1) / RealVal(17) * counter
            + RealVal(-1) / RealVal(102) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(5) / RealVal(136) * counter
            + RealVal(-1) / RealVal(136) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(3) / RealVal(85) * counter
            + RealVal(-1) / RealVal(170) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(-9) / RealVal(34)
            + RealVal(9) / RealVal(68) * counter
            + RealVal(-1) / RealVal(68) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(1) / RealVal(17) * counter + RealVal(-1) / RealVal(34) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(-12) / RealVal(17)
            + RealVal(5) / RealVal(17) * counter
            + RealVal(-1) / RealVal(34) * counter**2,
        ),
    ],
)

invariant_k_32 = IndexedPolynomial(
    system.vars,
    {
        q: [IntVal(0), IntVal(1)],
        pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
        coin1: [IntVal(0), IntVal(1)],
    },
    [
        Polynomial([counter], 2, RealVal(0)),
        Polynomial([counter], 2, RealVal(0)),
        Polynomial([counter], 2, RealVal(0)),
        Polynomial([counter], 2, RealVal(0)),
        Polynomial([counter], 2, RealVal(0)),
        Polynomial([counter], 2, RealVal(0)),
        Polynomial(
            [counter],
            2,
            RealVal(3) / RealVal(1888) * counter
            + RealVal(-3) / RealVal(3776) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(-198) / RealVal(59)
            + RealVal(195) / RealVal(1888) * counter
            + RealVal(-3) / RealVal(3776) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(-65) / RealVal(79296)
            + RealVal(11) / RealVal(13216) * counter
            + RealVal(-1) / RealVal(79296) * counter**2,
        ),
        Polynomial([counter], 2, RealVal(0)),
        Polynomial(
            [counter],
            2,
            RealVal(-201) / RealVal(245440)
            + RealVal(51) / RealVal(61360) * counter
            + RealVal(-3) / RealVal(245440) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(3) / RealVal(3776)
            + RealVal(3) / RealVal(3835) * counter
            + RealVal(-3) / RealVal(245440) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(99) / RealVal(122720) * counter
            + RealVal(-3) / RealVal(245440) * counter**2,
        ),
        Polynomial([counter], 2, RealVal(0)),
        Polynomial(
            [counter],
            2,
            RealVal(3) / RealVal(1888) * counter
            + RealVal(-3) / RealVal(3776) * counter**2,
        ),
        Polynomial(
            [counter],
            2,
            RealVal(-198) / RealVal(59)
            + RealVal(195) / RealVal(1888) * counter
            + RealVal(-3) / RealVal(3776) * counter**2,
        ),
    ],
)

parametric_invariant = IndexedPolynomial(
    system.vars,
    {
        q: [IntVal(0), IntVal(1)],
        pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
        coin1: [IntVal(0), IntVal(1)],
    },
    [
        # 0,0,0
        Polynomial([counter], 2, RealVal(0)),
        # 0,0,1
        Polynomial([counter], 2, RealVal(0)),
        # 0,1,0
        Polynomial([counter], 2, RealVal(0)),
        # 0,1,1
        Polynomial([counter], 2, RealVal(0)),
        # 0,2,0
        Polynomial([counter], 2, RealVal(0)),
        # 0,2,1
        Polynomial([counter], 2, RealVal(0)),
        # 0,3,0 (x <= L)
        Polynomial([counter], 1, -counter + (RealVal(LEFT) + RealVal(1))),
        # 0,3,1 (x >= R)
        Polynomial([counter], 1, counter - (RealVal(RIGHT) - RealVal(1))),
        # 1,0,0 (L < x < R)
        Polynomial(
            [counter],
            2,
            -(counter**2)
            + (RealVal(RIGHT) + RealVal(LEFT)) * counter
            + (RealVal(LEFT) * RealVal(RIGHT)),
        ),
        # 1,0,1
        Polynomial([counter], 2, RealVal(0)),
        # 1,1,0 (L < x < R)
        Polynomial(
            [counter],
            2,
            -(counter**2)
            + (RealVal(RIGHT) + RealVal(LEFT)) * counter
            + (RealVal(LEFT) * RealVal(RIGHT)),
        ),
        # 1,1,1 (L < x < R)
        Polynomial(
            [counter],
            2,
            -(counter**2)
            + (RealVal(RIGHT) + RealVal(LEFT)) * counter
            + (RealVal(LEFT) * RealVal(RIGHT)),
        ),
        # 1,2,0 (0 < x < RANGE
        Polynomial(
            [counter],
            2,
            -(counter**2) + RealVal(RANGE) * counter + RealVal(RANGE),
        ),
        # 1,2,1
        Polynomial([counter], 2, RealVal(0)),
        # 1,3,0 (x <= L)
        Polynomial([counter], 1, -counter + (RealVal(LEFT) + RealVal(1))),
        # 1,3,1 (x >= R)
        Polynomial([counter], 1, counter - (RealVal(RIGHT) - RealVal(1))),
    ],
)

lex_psm, inv = guess_check(
    system,
    parity_objectives,
    RealVal(1),
    indexing,
    2,
    RANGE,
    dataset=None,
    precomputed_invariant=parametric_invariant,
)
# print(lex_psm)
# print(inv)
