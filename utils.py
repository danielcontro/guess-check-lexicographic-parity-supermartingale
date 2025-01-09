from typing import TypeVar

from z3 import (
    ArithRef,
    Bool,
    BoolRef,
    BoolVal,
    Int,
    IntNumRef,
    IntVal,
    ModelRef,
    RatNumRef,
    Real,
    RealVal,
    Solver,
    is_bool,
    is_false,
    is_int,
    is_real,
    is_true,
    simplify,
    substitute,
    unsat,
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
    return solver.check() != unsat


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
    return substitute(
        expr,
        *list(
            map(
                lambda kv: (kv[0], val_from_var(kv[0], kv[1])),
                state.items(),
            )
        ),
    )

    # return simplify(
    #     substitute(
    #         expr,
    #         *list(
    #             map(
    #                 lambda kv: (kv[0], val_from_var(kv[0], kv[1])),
    #                 state.items(),
    #             )
    #         ),
    #     )
    # )


def integer_to_int(integer: IntNumRef) -> IntNumRef:
    if integer is None:
        print("Integer is None")
        return 1
    return integer.as_long()


def bool_to_bool(boolean: BoolRef) -> BoolRef:
    if boolean is None:
        print("Boolean is None")
        return False
    return boolean.decl().name() == "true"


def real_to_float(real: ArithRef) -> RatNumRef:
    if real is None:
        print("Real is None")
        return 0.0
    return real.as_fraction()
    # return float(fract.numerator) / float(fract.denominator)


def extract_var(var: ArithRef | BoolRef, model: ModelRef):
    # if model[var] is not None:
    #     return model[var]
    # elif is_bool(var):
    #     return False
    # elif is_int(var):
    #     return 0
    # elif is_real(var):
    #     return 0.0
    assert (val := model[var]) is None or is_bool(var) or is_int(var) or is_real(var)

    if val is not None:
        return val
    elif is_bool(var):
        print("Bool is None")
        return BoolVal(False)
    elif is_int(var):
        print("Int is None")
        return IntVal(0)
    elif is_real(var):
        print("Real is None")
        return RealVal(0.0)


def evaluate_to_true(expr: BoolRef) -> bool:
    e = simplify(expr)
    assert e.eq(BoolVal(True)) or e.eq(BoolVal(False))
    return e.eq(BoolVal(True))


def is_value(e) -> bool:
    return (
        isinstance(e, IntNumRef)
        or is_true(e)
        or is_false(e)
        or isinstance(e, RatNumRef)
    )
