from abc import ABC, abstractmethod
from enum import Enum
import itertools
from typing import Optional
from utils import VAR_MANAGER, is_value, satisfiable, substitute_state

from z3 import (
    And,
    ArithRef,
    BoolRef,
    IntNumRef,
    IntVal,
    RatNumRef,
    RealVal,
    ModelRef,
    simplify,
    substitute,
)

Value = IntNumRef | RatNumRef | BoolRef
Variable = ArithRef | BoolRef
Valuation = dict[Variable, Value | Variable]


class Domain(Enum):
    Int = 1
    Real = 2
    Bool = 3


def get_domain(var: Variable) -> Domain:
    assert isinstance(var, ArithRef) or isinstance(var, BoolRef)
    if isinstance(var, ArithRef):
        if var.is_int():
            return Domain.Int
        elif var.is_real():
            return Domain.Real
    elif isinstance(var, BoolRef) and var.is_bool():
        return Domain.Bool
    else:
        raise ValueError(f"Unknown variable type: {var}")


class Function(ABC):
    def __init__(self, vars: list[Variable]):
        self._vars = vars

    @property
    def vars(self):
        return self._vars

    @property
    @abstractmethod
    def degree(self) -> int:
        pass

    @property
    @abstractmethod
    def symbolic(self) -> ArithRef:
        pass

    @abstractmethod
    def __call__(self, state: Valuation) -> ArithRef:
        pass

    def __repr__(self) -> str:
        return f"{self.symbolic}"

    @abstractmethod
    def post_exp(self, successors: list[tuple[float, Valuation]]) -> Value | ArithRef:
        pass


class Polynomial:
    __memoized_monomials: dict[tuple[int, tuple[Variable]], list[ArithRef]] = {}

    def __init__(
        self,
        vars: list[Variable],
        degree: int,
        f: ArithRef,
        coefficients: Optional[list[ArithRef]] = None,
    ):
        self._vars = vars
        self._f = f
        self._degree = degree
        self._vars = vars
        self._coefficients = coefficients

    @staticmethod
    def __monomials(degree: int, vars: list[Variable]):
        if (
            monomials := Polynomial.__memoized_monomials.get((degree, tuple(vars)))
        ) is not None:
            return monomials

        if degree == 0:
            Polynomial.__memoized_monomials[(degree, tuple(vars))] = [RealVal(1)]
            return [RealVal(1)]
        if len(vars) == 0:
            Polynomial.__memoized_monomials[(degree, tuple(vars))] = []
            return []

        monomials = []
        for i, var in enumerate(vars):
            monomials += [
                var ** IntVal(d + 1) * monomial
                for d in range(degree)
                for monomial in Polynomial.__monomials(degree - (d + 1), vars[i + 1 :])
            ]
        Polynomial.__memoized_monomials[(degree, tuple(vars))] = monomials
        return monomials

    @staticmethod
    def template(name: str, vars: list[Variable], degree: int):
        coefficients: list[ArithRef] = []
        polynomial: ArithRef = RealVal(0)
        for d in range(degree + 1):
            for i, monomial in enumerate(Polynomial.__monomials(d, vars)):
                coefficients.append(
                    VAR_MANAGER.new_real_var(f"{name}_deg{d}_coeff_{i}")
                )
                polynomial += coefficients[-1] * monomial

        return Polynomial(
            vars,
            degree,
            polynomial,
            coefficients,
        )

    @property
    def vars(self):
        return self._vars

    @property
    def degree(self):
        return self._degree

    @property
    def symbolic(self) -> ArithRef:
        return self._f

    def __repr__(self) -> str:
        return f"{self.symbolic}"

    def eval(self, state: Valuation) -> ArithRef:
        return substitute_state(self.symbolic, state)

    def post_exp(self, successors: list[tuple[float, Valuation]]) -> Value | ArithRef:
        assert len(successors) > 0
        return sum((p * self.eval(succ) for p, succ in successors), RealVal(0))

    def instantiate(self, model: ModelRef):
        if self._coefficients is None:
            # If the polynomial is not a template return self
            return self
        return Polynomial(
            self.vars,
            self.degree,
            simplify(
                substitute(
                    self._f,
                    [
                        (coeff, val)
                        if (val := model[coeff]) is not None
                        else (coeff, RealVal(0))
                        for coeff in self._coefficients
                    ],
                )
            ),
        )


Index = tuple[Value, ...]


class IndexedPolynomial:
    def __init__(
        self,
        vars: list[Variable],
        indexing: dict[Variable, list[Value]],
        functions: list[Polynomial],
    ) -> None:
        self._vars = vars
        self._indexing = indexing
        self._indexing_vars_ordering = list(indexing.keys())
        indexes = list(itertools.product(*list(indexing.values())))
        functions_vars = list(
            filter(lambda var: var not in self._indexing_vars_ordering, vars)
        )
        assert all(f.vars == functions_vars for f in functions)
        assert len(indexes) == len(functions)
        self._indexes = indexes

        self._f = {index: f for index, f in zip(indexes, functions)}
        self._degree = max(f.degree for f in functions)

    @staticmethod
    def template(
        name: str,
        vars: list[Variable],
        indexing: dict[Variable, list[Value]],
        degree: int,
    ):
        functions = [
            Polynomial.template(
                f"{name}_f_{''.join(str(index).split())}",
                list(filter(lambda var: var not in indexing.keys(), vars)),
                degree,
            )
            for index in itertools.product(*indexing.values())
        ]
        return IndexedPolynomial(vars, indexing, functions)

    def instantiate(self, model: ModelRef):
        # TODO: Improve interface and performance of instantiation
        return IndexedPolynomial(
            self.vars, self.indexing, [f.instantiate(model) for f in self._f.values()]
        )

    @property
    def vars(self):
        return self._vars

    @property
    def indexes(self):
        return self._indexes

    @property
    def indexing(self):
        return self._indexing

    @property
    def indexing_ordering(self):
        return self._indexing_vars_ordering

    @property
    def symbolic(self) -> dict[tuple[Value, ...], Polynomial]:
        return self._f

    @property
    def degree(self):
        return self._degree

    def __getitem__(self, key: Index):
        return self._f[key]

    def get_index(self, state: Valuation) -> tuple[Value | Variable, ...]:
        return tuple(state[var] for var in self.indexing_ordering)

    def induced_indexes(self, index: tuple[Value | Variable, ...]) -> list[Index]:
        return list(
            itertools.product(
                *[
                    [val] if is_value(val := index[i]) else self.indexing[var]
                    for i, var in enumerate(self.indexing_ordering)
                ]
            )
        )

    def index_constraint(
        self,
        index: tuple[Value, ...],
    ) -> BoolRef:
        return And(*[var == index[i] for i, var in enumerate(self.indexing_ordering)])

    def eval(
        self, state: Valuation, index: Optional[tuple[Value | Variable, ...]] = None
    ) -> list[ArithRef]:
        """
        Returns the evaluation of the function for the given `state` over any possible index
        "respecting" the given one. Namely if it is provided an `index` containing variables then
        the evaluation is performed enumerating over all possible combination of values of the
        variables in `index`.
        If `index` is `None` then it is computed from the state and then the evaluation is performed
        as before.
        """
        if index is None:
            index = self.get_index(state)

        indexes = self.induced_indexes(index)
        return [self[index].eval(state) for index in indexes]

    def eval_indexed(self, state: Valuation, index: tuple[Value, ...]):
        return self[index].eval(state)

    def post(
        self,
        post_distr: list[tuple[float, Valuation]],
    ) -> list[ArithRef]:
        post: list[ArithRef] = [RealVal(0)]
        for prob, succ in post_distr:
            current: list[float | ArithRef] = []
            for index in self.indexes:
                constraint = And(
                    *[
                        succ[var] == index[i]
                        for i, var in enumerate(self.indexing_ordering)
                    ]
                )
                if not satisfiable(constraint := substitute_state(constraint, succ)):
                    continue
                current.append(prob * self[index].eval(succ))
            post_i: list[ArithRef] = []
            for prev, new in itertools.product(post, current):
                post_i.append(prev + new)
            post = post_i

        return post

    def post_exp(self, successors: list[tuple[float, Valuation]]) -> Value | ArithRef:
        post = []
        for p, succ in successors:
            succ_index: Index = tuple(succ[var] for var in self.indexing_ordering)
            post.append(p * self[succ_index].eval(succ))
        return sum(post, RealVal(0))

    def __repr__(self) -> str:
        repr = f"{self.indexing_ordering}:\n"
        for k, v in self.symbolic.items():
            repr += f"{k} -> {v}\n"
        return repr
