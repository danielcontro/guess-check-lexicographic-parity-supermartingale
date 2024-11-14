from typing import Literal, TypeVar

from z3 import (
    ArithRef,
    Bool,
    BoolRef,
    BoolVal,
    ExprRef,
    Int,
    IntNumRef,
    IntVal,
    ModelRef,
    RatNumRef,
    Real,
    RealVal,
    Solver,
    is_bool,
    is_int,
    is_real,
    sat,
    simplify,
    substitute,
)


T = TypeVar("T")
U = TypeVar("U")


def fst(t: tuple[T, U]) -> T:
    return t[0]


def snd(t: tuple[T, U]) -> U:
    return t[1]


class _VarManager:
    def __init__(self) -> None:
        self._COUNTER = 0
        self._VAR_MAP: dict[str, ArithRef | BoolRef] = {}

    def new_symbol(self, prefix: str) -> ArithRef:
        name = f"{prefix}_({self._COUNTER})"
        symbol = Real(name)
        self._VAR_MAP[name] = symbol
        return symbol

    def new_real_var(self, name: str) -> ArithRef:
        symbol = self._VAR_MAP.get(name)
        if symbol is not None:
            return symbol

        symbol = Real(name)
        self._VAR_MAP[name] = symbol
        return symbol

    def new_int_var(self, name: str) -> ArithRef:
        symbol = self._VAR_MAP.get(name)
        if symbol is not None:
            return symbol

        symbol = Int(name)
        self._VAR_MAP[name] = symbol
        return symbol

    def new_bool_var(self, name: str) -> BoolRef:
        symbol = self._VAR_MAP.get(name)
        if symbol is not None:
            return symbol

        symbol = Bool(name)
        self._VAR_MAP[name] = symbol
        return symbol

    def get_symbol(self, name: str) -> ArithRef | BoolRef:
        return self._VAR_MAP[name]


VAR_MANAGER = _VarManager()


def satisfiable(query):
    solver = Solver()
    solver.add(query)
    return solver.check() == sat


def val_from_var(
    var: ArithRef | BoolRef, val
) -> BoolRef | IntNumRef | RatNumRef | ArithRef:
    if isinstance(val, ArithRef | BoolRef):
        return val
    elif is_bool(var):
        return BoolVal(val)
    elif is_int(var):
        return IntVal(val)
    elif is_real(var):
        return RealVal(val)
    else:
        raise ValueError(f"Unknown variable type: {var}")


def substitute_state(expr: ArithRef | BoolRef, state):
    if not isinstance(expr, ExprRef):
        return expr
    return simplify(
        substitute(
            expr,
            *list(
                map(
                    lambda kv: (kv[0], val_from_var(kv[0], kv[1])),
                    state.items(),
                )
            ),
        )
    )


def integer_to_int(integer: IntNumRef) -> int:
    return integer.as_long()


def bool_to_bool(boolean: BoolRef) -> bool:
    return boolean.decl().name() == "true"


def real_to_float(real: ArithRef) -> float:
    if real is None:
        return 0.0
    fract = real.as_fraction()
    return float(fract.numerator) / float(fract.denominator)


def extract_var(var: ArithRef | BoolRef, model: ModelRef):
    if is_bool(var):
        return bool_to_bool(model[var])
    elif is_int(var):
        return integer_to_int(model[var])
    elif is_real(var):
        return real_to_float(model[var])
    else:
        raise ValueError(f"Unknown variable type: {var}")
