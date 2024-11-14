from typing import Optional
from itertools import chain

from z3 import And, ArithRef, Bool, BoolRef, Int, Real, d, simplify, substitute

from utils import VAR_MANAGER, fst, satisfiable, snd, substitute_state

Value = int | float | bool

Variable = ArithRef | BoolRef

State = dict[Variable, Value | ArithRef | BoolRef]


class LinearFunction:
    def __init__(self, vars: list[Variable], f: ArithRef):
        self._vars = vars
        self._f = f

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def f(self) -> ArithRef:
        return self._f

    def __call__(self, state: State) -> Value | ArithRef:
        return substitute_state(self.f, state)


class QLinearFunction:
    def __init__(self, vars: list[Variable], f: dict[int, LinearFunction]):
        self._f = f
        self._vars = vars

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def f(self) -> dict[int, LinearFunction]:
        return self._f

    @property
    def symbolic(self) -> dict[int, ArithRef]:
        return {q: self.f[q].f for q in self.f}

    def __call__(self, state: State) -> Value | ArithRef:
        return self.f[state[Int("q")]](state)

    def post_exp(
        self, q: int, succ_distr: list[tuple[float, State]]
    ) -> Value | ArithRef:
        return sum(map(lambda succ: succ[0] * self.f[q](succ[1]), succ_distr))


class StateUpdate:
    def __init__(
        self, vars: list[Variable], var_updates: dict[Variable, LinearFunction]
    ):
        self._vars = vars
        self._var_updates = var_updates

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def var_updates(self) -> dict[Variable, LinearFunction]:
        return self._var_updates

    def __call__(self, state: State) -> State:
        return {
            var: state[var]
            if (var_update := self.var_updates.get(var)) is None
            else var_update(state)
            for var in self.vars
        }

    def symbolic_successor(self) -> State:
        return {
            var: var
            if (var_update := self.var_updates.get(var)) is None
            else var_update.f
            for var in self.vars
        }


class UpdateDistribution:
    def __init__(
        self, vars: list[Variable], distribution: list[tuple[float, StateUpdate]]
    ):
        assert sum(map(fst, distribution)) == 1
        self._vars = vars
        self._distribution = distribution

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def distribution(self) -> list[tuple[float, StateUpdate]]:
        return self._distribution

    @property
    def probabilities(self) -> list[float]:
        return list(map(fst, self.distribution))

    @property
    def updates(self) -> list[StateUpdate]:
        return list(map(snd, self.distribution))

    def successors(self, state: State) -> list[State]:
        return list(map(lambda update: update(state), self.updates))

    def symbolic_successors(self) -> list[tuple[float, State]]:
        return list(
            map(
                lambda prob_update: (
                    prob_update[0],
                    prob_update[1].symbolic_successor(),
                ),
                self.distribution,
            )
        )

    def __call__(self, state: State) -> list[tuple[float, State]]:
        return list(
            map(lambda update: (update[0], update[1](state)), self.distribution)
        )


class GuardedCommand:
    def __init__(self, guard: BoolRef, update_distribution: UpdateDistribution):
        self._guard = guard
        self._update_distribution = update_distribution

    @property
    def guard(self) -> BoolRef:
        return self._guard

    @property
    def command(self) -> UpdateDistribution:
        return self._update_distribution

    def __call__(self, state: State) -> Optional[list[tuple[float, State]]]:
        return (
            self.command(state)
            if satisfiable(substitute_state(self.guard, state))
            else None
        )

    def successors(self, state: State) -> list[State]:
        return (
            self.command.successors(state)
            if satisfiable(substitute_state(self.guard, state))
            else []
        )


class ReactiveModule:
    def __init__(
        self,
        init: list[State],
        vars: list[Variable],
        guarded_commands: list[GuardedCommand],
        state_space: BoolRef,
    ):
        self._init = init
        self._vars = vars
        self._guarded_commands = guarded_commands
        self._state_space = state_space

    @property
    def init(self) -> list[State]:
        return self._init

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def guarded_commands(self) -> list[GuardedCommand]:
        return self._guarded_commands

    @property
    def state_space(self) -> BoolRef:
        return self._state_space

    def successors(self, state: State) -> list[State]:
        return list(
            chain.from_iterable(
                map(lambda command: command.successors(state), self.guarded_commands)
            )
        )

    def __call__(self, state: State) -> list[list[tuple[float, State]]]:
        """
        Computes the set of successor states of the given state and their probabilities.
        """
        return list(
            filter(
                lambda succ: succ is not None,
                map(lambda command: command(state), self.guarded_commands),
            )
        )
