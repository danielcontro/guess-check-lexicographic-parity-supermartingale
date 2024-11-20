from z3 import ArithRef, Int, ModelRef
from reactive_module import LinearFunction, QLinearFunction, State, Value, Variable
from utils import VAR_MANAGER, real_to_float


class LinearTemplate:
    def __init__(self, name: str, vars: list[Variable]) -> None:
        self._vars = vars
        self._a = [VAR_MANAGER.new_real_var(f"{name}_a_{i}") for i in range(len(vars))]
        self._b = VAR_MANAGER.new_real_var(f"{name}_b")
        self._template = LinearFunction(
            vars,
            sum(self._a[i] * vars[i] for i in range(len(vars)))
            + VAR_MANAGER.new_real_var(f"{name}_b"),
        )

    @property
    def symbolic(self):
        return self._template.f

    def instantiate(self, model: ModelRef) -> LinearFunction:
        return LinearFunction(
            self._vars,
            sum(real_to_float(model[a]) * self._vars[i] for i, a in enumerate(self._a))
            + real_to_float(model[self._b]),
        )

    def __call__(self, state: State) -> Value | ArithRef:
        return self._template(state)

    def post_exp(self, succ_distr: list[tuple[float, State]]) -> Value | ArithRef:
        return sum(
            map(
                lambda succ: succ[0] * self._template(succ[1]),
                succ_distr,
            )
        )


class QLinearTemplate:
    def __init__(self, name: str, states: list[int], vars: list[Variable]) -> None:
        self._vars = vars
        self._template = {
            state: LinearTemplate(f"{name}_q{state}", vars) for state in states
        }

    @property
    def vars(self) -> list[Variable]:
        return self._vars

    @property
    def symbolic(self):
        return {q: template.symbolic for q, template in self._template.items()}

    def __call__(self, state: State) -> Value | ArithRef:
        return self._template[state[Int("q")]](state)

    def instantiate(self, model: ModelRef) -> QLinearFunction:
        return QLinearFunction(
            self._vars,
            {q: template.instantiate(model) for q, template in self._template.items()},
        )

    def post_exp(
        self, q: int, succ_distr: list[tuple[float, State]]
    ) -> Value | ArithRef:
        return self._template[q].post_exp(succ_distr)
