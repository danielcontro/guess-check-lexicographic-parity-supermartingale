from enum import Enum
import itertools
from typing import Optional
from z3 import (
    And,
    BoolRef,
    BoolVal,
    IntVal,
    RealVal,
    is_true,
    simplify,
)
from functions import Domain, Valuation, Value, Variable, get_domain
from reactive_module import GuardedCommand, ReactiveModule


class BoundType:
    Closed = 1
    Open = 2


class PlusInf:
    def __init__(self):
        return

    def __gt__(self, other) -> bool:
        return not isinstance(other, PlusInf)

    def __lt__(self, _) -> bool:
        return False

    def __ge__(self, _) -> bool:
        return True

    def __le__(self, other) -> bool:
        return isinstance(other, PlusInf)

    def __eq__(self, other) -> bool:
        return isinstance(other, PlusInf)

    def __add__(self, other):
        if isinstance(other, NegInf):
            raise ValueError("Invalid operation")
        return self

    def __mul__(self, other):
        if isinstance(other, NegInf) or other == 0:
            raise ValueError("Invalid operation")
        if other < 0:
            return NegInf()
        return self

    def __sub__(self, other):
        if isinstance(other, PlusInf):
            raise ValueError("Invalid operation")
        return self

    def __div__(self, other):
        if isinstance(other, NegInf) or isinstance(other, PlusInf) or other == 0:
            raise ValueError("Invalid operation")


class NegInf:
    def __init__(self):
        return

    def __gt__(self, _) -> bool:
        return False

    def __lt__(self, other) -> bool:
        return not isinstance(other, NegInf)

    def __ge__(self, other) -> bool:
        return isinstance(other, NegInf)

    def __le__(self, _) -> bool:
        return True

    def __eq__(self, other) -> bool:
        return isinstance(other, NegInf)


class Lattice(Enum):
    BOT = 0
    TOP = 1
    INTERVAL = 2


class Interval:
    def __init__(
        self,
        lattice_elem: Lattice,
        domain: Domain,
        lb: Optional[tuple[Value | NegInf, BoundType]] = None,
        ub: Optional[tuple[Value | PlusInf, BoundType]] = None,
    ):
        self.__lattice = lattice_elem
        self.__domain = domain
        if lattice_elem == Lattice.INTERVAL:
            assert domain is not None
            assert lb is not None
            assert ub is not None
            assert is_true(simplify(lb[0] <= ub[0]))
            self.__lb, self.__lb_type = lb
            self.__ub, self.__ub_type = ub

    @staticmethod
    def top(domain: Domain):
        return Interval(Lattice.TOP, domain)

    @staticmethod
    def bot(domain: Domain):
        return Interval(Lattice.BOT, domain)

    @property
    def lattice(self) -> Lattice:
        return self.__lattice

    @property
    def domain(self) -> Domain:
        return self.__domain

    @property
    def val_constructor(self):
        match self.domain:
            case Domain.Int:
                return IntVal
            case Domain.Real:
                return RealVal
            case Domain.Bool:
                return BoolVal

    @property
    def lb(self) -> Value | NegInf:
        return self.__lb

    @property
    def lb_type(self) -> BoundType:
        return self.__lb_type

    @property
    def ub(self) -> Value | PlusInf:
        return self.__ub

    @property
    def ub_type(self) -> BoundType:
        return self.__ub_type

    def __repr__(self) -> str:
        if self.lattice == Lattice.BOT:
            return "BOT"
        elif self.lattice == Lattice.TOP:
            return "TOP"
        else:
            return f"[{self.lb}, {self.ub}]"

    def join(self, other: "Interval") -> "Interval":
        assert self.domain == other.domain

        if self.lattice == Lattice.BOT:
            return other
        elif other.lattice == Lattice.BOT:
            return self
        elif self.lattice == Lattice.TOP or other.lattice == Lattice.TOP:
            return Interval(Lattice.TOP, self.domain)
        else:
            return Interval(
                Lattice.INTERVAL,
                self.domain,
                (
                    self.lb if is_true(simplify(self.lb <= other.lb)) else other.lb,
                    BoundType.Open
                    if self.lb_type == BoundType.Open or other.lb_type == BoundType.Open
                    else BoundType.Closed,
                ),
                (
                    self.ub if is_true(simplify(self.ub >= other.ub)) else other.ub,
                    BoundType.Open
                    if self.ub_type == BoundType.Open or other.ub_type == BoundType.Open
                    else BoundType.Closed,
                ),
            )

    def __le__(self, other: "Interval") -> bool:
        if self.lattice == Lattice.BOT:
            return True
        elif other.lattice == Lattice.BOT:
            return False
        elif self.lattice == Lattice.TOP and other.lattice == Lattice.TOP:
            return True
        elif self.lattice == Lattice.TOP:
            return False
        elif other.lattice == Lattice.TOP:
            return True
        else:
            return other.lb <= self.lb and self.ub <= other.ub

    def __ge__(self, other: "Interval") -> bool:
        if self.lattice == Lattice.TOP:
            return True
        elif other.lattice == Lattice.TOP:
            return False
        elif self.lattice == Lattice.BOT and other.lattice == Lattice.BOT:
            return True
        elif self.lattice == Lattice.BOT:
            return False
        elif other.lattice == Lattice.BOT:
            return True
        else:
            return self.lb <= other.lb and other.ub <= self.ub

    def __eq__(self, other) -> bool:
        return self.__le__(other) and other.__le__(self)


class SystemInvariant:
    def __init__(
        self,
        vars: list[Variable],
        indexing: dict[Variable, list[Value]],
        invariant: dict[tuple[Value, ...], dict[Variable, Interval]],
    ) -> None:
        self.__vars = vars
        self.__indexing = indexing
        self.__indexes = list(itertools.product(*list(indexing.values())))
        self.__indexing_order = list(indexing.keys())
        self.__invariant_vars = [var for var in vars if var not in indexing.keys()]
        self.__invariant = invariant

    @staticmethod
    def new(vars: list[Variable], indexing: dict[Variable, list[Value]]):
        indexes = list(itertools.product(*list(indexing.values())))
        invariant_vars = [var for var in vars if var not in indexing.keys()]
        return SystemInvariant(
            vars,
            indexing,
            {
                index: {var: Interval.bot(get_domain(var)) for var in invariant_vars}
                for index in indexes
            },
        )

    @property
    def vars(self):
        return self.__vars

    @property
    def invariant_vars(self):
        return self.__invariant_vars

    @property
    def indexing_vars(self):
        return self.__indexing_order

    @property
    def indexing(self):
        return self.__indexing

    @property
    def indexes(self) -> list[tuple[Value, ...]]:
        return self.__indexes

    @property
    def invariant(self) -> dict[tuple[Value, ...], dict[Variable, Interval]]:
        return self.__invariant

    def state_join(self, state: Valuation):
        return SystemInvariant(
            self.vars,
            self.indexing,
            {
                key: {
                    var: interval.join(
                        Interval(
                            Lattice.INTERVAL,
                            get_domain(var),
                            (state[var], BoundType.Closed),
                            (state[var], BoundType.Closed),
                        )
                        if key == get_index(state, self.indexing_vars)
                        else interval
                    )
                    for var, interval in value.items()
                }
                for key, value in self.invariant.items()
            },
        )


"""
From the system synthesize an interval invariant for each guarded command
"""


def get_index(state: Valuation, index_order: list[Variable]) -> tuple[Value, ...]:
    return tuple(state[var] for var in index_order)


def system_static_analysis(
    system: ReactiveModule, indexing: dict[Variable, list[Value]]
):
    analyze = system.init.copy()
    invariant = SystemInvariant.new(system.vars, indexing)

    visited = []
    while len(analyze) > 0:
        state = analyze.pop()
        if state in visited:
            continue
        visited.append(state)
        new_invariant = invariant.state_join(state)
        if not new_invariant == invariant:
            analyze.extend(system.successors(state))
            invariant = new_invariant
    return invariant


def analyze_guarded_command(
    guarded_command: GuardedCommand, state: Valuation, interval: Interval
):
    successors = guarded_command(state)
    if successors is None:
        return

    # Compute the join between interval and the intervals of the successors

    return
