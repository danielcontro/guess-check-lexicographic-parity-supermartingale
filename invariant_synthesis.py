import itertools
from z3 import (
    And,
    Int,
    IntVal,
    Real,
    RealVal,
)

from functions import IndexedPolynomial, Polynomial
import interval_abstract_interpreter
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
K = 2**10
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

indexing = {
    q: [IntVal(0), IntVal(1)],
    pc1: [IntVal(0), IntVal(1), IntVal(2), IntVal(3)],
    coin1: [IntVal(0), IntVal(1)],
}

invariant = interval_abstract_interpreter.system_static_analysis(
    system,
    indexing,
)

print(invariant.invariant)
