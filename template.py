from z3 import And, ArithRef, BoolRef, IntNumRef, IntVal, ModelRef, RealVal
from functions import Value, Variable, Valuation
from reactive_module import (
    LinearFunction,
    QLinearFunction,
    QPolytopeFunction,
)
from utils import VAR_MANAGER


class LinearTemplate:
    def __init__(self, name: str, vars: list[Variable]) -> None:
        self._vars = vars
        self._a = [VAR_MANAGER.new_int_var(f"{name}_a_{i}") for i in range(len(vars))]
        self._b = VAR_MANAGER.new_int_var(f"{name}_b")
        self._template = LinearFunction(
            vars,
            sum(self._a[i] * vars[i] for i in range(len(vars)))
            + VAR_MANAGER.new_int_var(f"{name}_b"),
        )

    @property
    def symbolic(self):
        return self._template.symbolic

    def instantiate(self, model: ModelRef) -> LinearFunction:
        return LinearFunction(
            self._vars,
            sum(
                (val if (val := model[a]) is not None else IntVal(0)) * self._vars[i]
                for i, a in enumerate(self._a)
            )
            + (val if (val := model[self._b]) is not None else IntVal(0)),
        )

    def __call__(self, state: Valuation) -> Value | ArithRef:
        return self._template(state)

    def post_exp(self, succ_distr: list[tuple[float, Valuation]]) -> Value | ArithRef:
        return sum(
            map(
                lambda succ: succ[0] * self._template(succ[1]),
                succ_distr,
            )
        )

    def __repr__(self) -> str:
        return f"{self._template}"


class QLinearTemplate:
    def __init__(
        self, name: str, states: list[IntNumRef], vars: list[Variable]
    ) -> None:
        self._vars = vars
        self._template = {
            state.as_long(): LinearTemplate(f"{name}_q{state}", vars)
            for state in states
        }

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def symbolic(self):
        return {q: template.symbolic for q, template in self._template.items()}

    def __call__(self, state: Valuation, q: IntNumRef) -> bool | BoolRef:
        assert isinstance(q, IntNumRef)
        return self._template[q.as_long()](state)

    def instantiate(self, model: ModelRef) -> QLinearFunction:
        return QLinearFunction(
            self._vars,
            {q: template.instantiate(model) for q, template in self._template.items()},
        )

    def post_exp(
        self, q: IntNumRef, succ_distr: list[tuple[float, Valuation]]
    ) -> Value | ArithRef:
        return self._template[q.as_long()].post_exp(succ_distr)

    def __repr__(self) -> str:
        return (
            "{"
            + ", ".join([f"{q}: {template}" for q, template in self._template.items()])
            + "}"
        )


class QPolytopeTemplate:
    def __init__(
        self, name: str, states: list[IntNumRef], edges: int, vars: list[Variable]
    ) -> None:
        self._vars = vars
        self._template = {
            state.as_long(): [
                LinearTemplate(f"{name}_q{state}_n{i}", vars) for i in range(edges)
            ]
            for state in states
        }

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def symbolic(self):
        return {
            q: And(*[template.symbolic >= 0 for template in templates])
            for q, templates in self._template.items()
        }

    def __call__(self, state: Valuation, q: IntNumRef) -> list[Value | ArithRef]:
        return [template(state) for template in self._template[q.as_long()]]

    def instantiate(self, model: ModelRef) -> QPolytopeFunction:
        return QPolytopeFunction(
            self._vars,
            {
                q: [template.instantiate(model) for template in templates]
                for q, templates in self._template.items()
            },
        )


class TransitionQLinearTemplate:
    def __init__(
        self,
        name: str,
        states: list[IntNumRef],
        vars: list[Variable],
        transitions: int,
    ) -> None:
        self._vars = vars
        self._template = {
            transition: {
                state.as_long(): LinearTemplate(f"{name}_t{transition}_q{state}", vars)
                for state in states
            }
            for transition in range(transitions)
        }

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def symbolic(self):
        return {
            transition: {q: template.symbolic for q, template in templates.items()}
            for transition, templates in self._template.items()
        }

    def __call__(
        self, state: Valuation, q: IntNumRef, transition: int
    ) -> Value | ArithRef:
        return self._template[transition][q.as_long()](state)

    def instantiate(self, model: ModelRef) -> QPolytopeFunction:
        return QPolytopeFunction(
            self._vars,
            {
                q: [template.instantiate(model) for template in templates]
                for q, templates in self._template.items()
            },
        )
