import itertools
import math
from typing import Optional

from z3 import And, ArithRef, BoolRef, IntNumRef, IntVal, ModelRef
from reactive_module import (
    Q,
    GuardedCommand,
    LinearFunction,
    QLinearFunction,
    State,
    Variable,
)
from utils import satisfiable, substitute_state


class TreePSM:
    def __init__(
        self,
        vars: list[Variable],
        linear_constraints: list[QLinearFunction],
        lin_lex_psm: list[list[QLinearFunction]],
    ):
        # Ensure height of the tree (including psm leaves) is at least 1
        assert len(linear_constraints) >= 1
        assert len(lin_lex_psm) >= 2

        # Ensure correct number of linear constraints and lex_psm
        assert len(linear_constraints) + 1 == len(lin_lex_psm)

        self._vars = vars
        self._linear_constraints = linear_constraints
        self._lin_lex_psm = lin_lex_psm

    @staticmethod
    def template(
        vars: list[Variable],
        states: list[IntNumRef],
        height: int,
        lex_length: int,
    ):
        assert height >= 1
        return TreePSM(
            vars,
            [
                QLinearFunction.template(f"C_n{i}", vars, states)
                for i in range(2**height - 1)
            ],
            [
                [
                    QLinearFunction.template(f"V_l{i}_d{p}", vars, states)
                    for p in range(lex_length)
                ]
                for i in range(2**height)
            ],
        )

    @property
    def vars(self):
        return self._vars

    @property
    def height(self):
        return int(math.log(len(self._lin_lex_psm), 2))

    @property
    def lex_psms(self):
        return self._lin_lex_psm

    def ith(self, i: int) -> list[QLinearFunction]:
        return self._lin_lex_psm[i]

    def __getitem__(
        self, item: tuple[int, IntNumRef]
    ) -> tuple[BoolRef, list[LinearFunction]]:
        index, q = item
        binary_index = list(map(int, list(f"{index:0{self.height}b}")))
        # print("Height", self.height)
        # print("Index", index)
        # print("Q", q)
        # print("Binary index", binary_index)
        constraint_nodes = [0]
        for i in range(self.height):
            constraint_nodes.append(2 * constraint_nodes[-1] + binary_index[i] + 1)
        # print("Constraint nodes", constraint_nodes)
        return And(
            Q == q,
            *[
                (
                    self._linear_constraints[idx][q].symbolic >= 0
                    if binary_index[i]
                    else self._linear_constraints[idx][q].symbolic < 0
                )
                for i, idx in enumerate(constraint_nodes[:-1])
            ],
        ), list(map(lambda psm: psm.symbolic[q.as_long()], self._lin_lex_psm[index]))

    def __call__(
        self, state: State, p: Optional[int] = None
    ) -> list[tuple[BoolRef, list[ArithRef]]]:
        values: list[tuple[BoolRef, list[ArithRef]]] = []

        for i in range(len(self._lin_lex_psm)):
            constraint, lex_psm = self[i, state[Q]]
            if satisfiable(constraint := substitute_state(constraint, state)):
                values.append(
                    (
                        constraint,
                        list(
                            map(
                                lambda psm: psm(state, state[Q]),
                                lex_psm[: None if p is None else p + 1],
                            )
                        ),
                    )
                )
        return values

    def __repr__(self) -> str:
        rep = ""
        parity_states = list(self._linear_constraints[0].symbolic.keys())
        for q in parity_states:
            rep += f"Q = {q}\n"
            for i in range(len(self._lin_lex_psm)):
                constraint, lex_psm = self[i, IntVal(q)]
                rep += f"{constraint} =>\n {lex_psm}\n\n"
        return rep

    def post(
        self, gc: GuardedCommand, state: State, p: int
    ) -> Optional[list[list[ArithRef]]]:
        post_distr = gc(state)
        if post_distr is None:
            return None
        post: list[list[ArithRef]] = [[0.0] * (p + 1)]
        succ_q: IntNumRef = post_distr[0][1][Q]
        for prob, succ in post_distr:
            current: list[list[float | ArithRef]] = []
            for j in range(2**self.height):
                constraint, lex_psm = self[j, succ_q]
                if not satisfiable(constraint := substitute_state(constraint, succ)):
                    continue
                current.append([prob * psm(succ) for psm in lex_psm[: p + 1]])
            post_i: list[list[ArithRef]] = []
            for prev, new in itertools.product(post, current):
                post_i.append([prev[i] + new[i] for i in range(p + 1)])
            post = post_i

        return post

    def instantiate(self, model: ModelRef):
        return TreePSM(
            self.vars,
            [lin_constr.instantiate(model) for lin_constr in self._linear_constraints],
            [[psm.instantiate(model) for psm in row] for row in self._lin_lex_psm],
        )