import itertools
import random
from z3 import (
    And,
    ArithRef,
    Int,
    IntNumRef,
    IntVal,
    RatNumRef,
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

import matplotlib.pyplot as plt

from guess_check import guess_check, plot_lexpsm


N = 1
K = 2
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
    counter <= RANGE,
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
    [IntVal(0), IntVal(1)],
)

parity_objectives = [q == IntVal(0), q == IntVal(1)]

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

indexing = {
    q: [IntVal(0), IntVal(1)],
    pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
    coin1: [IntVal(0), IntVal(1)],
}

type_invariant = {
    q: [1],
    pc1: [0, 1, 2, 3],
    coin1: [0, 1],
    counter: [i for i in range(0, RANGE + 1, 2)],
}

SAMPLES = 500

# dataset = system.init.copy() + [
#     {var: IntVal(random.sample(type_invariant[var], 1)[0]) for var in system.vars}
#     for sample in range(SAMPLES)
# ]
#
# for state in dataset:
#     print(state)


dataset = system.init.copy() + list(
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

lex_psm, inv = guess_check(
    system, parity_objectives, RealVal(1), indexing, 2, RANGE, dataset
)
plot_lexpsm(lex_psm, inv, system, RANGE, "done")
# print(lex_psm)
# print(inv)
