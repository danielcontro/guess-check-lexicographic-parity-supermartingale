from typing import Optional
from itertools import chain

from z3 import (
    ArithRef,
    BoolRef,
    Int,
    IntNumRef,
    IntVal,
    ModelRef,
    RatNumRef,
)

from utils import VAR_MANAGER, fst, satisfiable, snd, substitute_state

Value = IntNumRef | RatNumRef | BoolRef

Variable = ArithRef | BoolRef

State = dict[Variable, Value | ArithRef | BoolRef]

Q = Int("q")


class LinearFunction:
    def __init__(
        self,
        vars: list[Variable],
        f: ArithRef,
        a: Optional[list[ArithRef]] = None,
        b: Optional[ArithRef] = None,
    ):
        self._vars = vars
        self._f = f
        self._a = a
        self._b = b

    @staticmethod
    def template(name: str, vars: list[Variable]):
        a = [VAR_MANAGER.new_int_var(f"{name}_a_{i}") for i in range(len(vars))]
        b = VAR_MANAGER.new_int_var(f"{name}_b")
        return LinearFunction(
            vars,
            sum(a[i] * vars[i] for i in range(len(vars)))
            + VAR_MANAGER.new_int_var(f"{name}_b"),
            a,
            b,
        )

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def symbolic(self) -> ArithRef:
        return self._f

    def __call__(self, state: State) -> ArithRef:
        return substitute_state(self.symbolic, state)

    def post_exp(self, successors: list[tuple[float, State]]) -> Value | ArithRef:
        return sum(map(lambda succ: succ[0] * self(succ[1]), successors))

    def instantiate(self, model: ModelRef):
        if self._a is None or self._b is None:
            # If the linear function is not a template return self
            return self
        return LinearFunction(
            self.vars,
            sum(
                (val if (val := model[a]) is not None else IntVal(0)) * self._vars[i]
                for i, a in enumerate(self._a)
            )
            + (val if (val := model[self._b]) is not None else IntVal(0)),
        )

    def __repr__(self) -> str:
        return f"{self.symbolic}"


class QLinearFunction:
    def __init__(
        self,
        vars: list[Variable],
        f: dict[int, LinearFunction],
    ):
        self._f = f
        self._vars = vars

    @staticmethod
    def template(name: str, vars: list[Variable], states: list[IntNumRef]):
        return QLinearFunction(
            vars,
            {
                state.as_long(): LinearFunction.template(f"{name}_q{state}", vars)
                for state in states
            },
        )

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def symbolic(self) -> dict[int, LinearFunction]:
        return self._f

    def __getitem__(self, q: IntNumRef) -> LinearFunction:
        return self.symbolic[q.as_long()]

    def __call__(self, state: State, q: IntNumRef) -> ArithRef:
        return self.symbolic[q.as_long()](state)

    def __repr__(self) -> str:
        return "{" + ", ".join([f"{q}: {f}" for q, f in self.symbolic.items()]) + "}"

    def post_exp(
        self, q: IntNumRef, succ_distr: list[tuple[float, State]]
    ) -> Value | ArithRef:
        return self.symbolic[q.as_long()].post_exp(succ_distr)

    def instantiate(self, model: ModelRef):
        return QLinearFunction(
            self.vars,
            {q: f.instantiate(model) for q, f in self.symbolic.items()},
        )


class QPolytopeFunction:
    def __init__(self, vars: list[Variable], f: dict[int, list[LinearFunction]]):
        self._f = f
        self._vars = vars

    @staticmethod
    def template(name: str, vars: list[Variable], states: list[IntNumRef], edges: int):
        return QPolytopeFunction(
            vars,
            {
                state.as_long(): [
                    LinearFunction.template(f"{name}_q{state}_{i}", vars)
                    for i in range(edges)
                ]
                for state in states
            },
        )

    @property
    def states(self) -> list[int]:
        return list(self.symbolic.keys())

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def symbolic(self) -> dict[int, list[LinearFunction]]:
        return self._f

    def __call__(self, state: State, q: IntNumRef) -> list[Value | ArithRef]:
        return [f(state) for f in self.symbolic[q.as_long()]]

    def __repr__(self) -> str:
        return "{" + ", ".join([f"{q}: {f}" for q, f in self.symbolic.items()]) + "}"

    def instantiate(self, model: ModelRef):
        return QPolytopeFunction(
            self.vars,
            {q: [f.instantiate(model) for f in fs] for q, fs in self.symbolic.items()},
        )


class TransitionQLinearFunction:
    def __init__(self, vars: list[Variable], f: dict[int, dict[int, LinearFunction]]):
        self._f = f
        self._vars = vars

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def symbolic(self) -> dict[int, dict[int, LinearFunction]]:
        return self._f

    def __call__(self, state: State, q: IntNumRef, n: IntNumRef) -> Value | ArithRef:
        return self.symbolic[q.as_long()][n.as_long()](state)

    def __repr__(self) -> str:
        return (
            "{"
            + ", ".join(
                [f"{q}: {f}" for q, f in self.symbolic.items() if isinstance(f, dict)]
            )
            + "}"
        )


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
            else var_update.symbolic
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

    @property
    def symbolic_state(self) -> State:
        return {var: var for var in self.vars}

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
