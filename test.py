import z3
import sys

# want V(x) = ax + b
# I(x) = c x + d

# x0 = 10;
# while (x > 0) { x -- }

# InvInit = I(10) >= 0
# InvConsec(x) = [I(x) >= 0 & (x >= 0) implies I(x-1) >= 0]
# RankAtInv(x) = [Inv(x) & (x >= 0) => V(x-1) <= V(x) - 1]
# NonNeg(x) = [Inv(x) => V(x) >= 0]


def real_to_float(real: z3.ArithRef) -> float:
    if real is None:
        print("Integer is None")
        return 0.0
    fract = real.as_fraction()
    return float(fract.numerator) / float(fract.denominator)


def int_to_int(integer) -> int:
    return integer.as_long()


aSym = z3.Int("a")
bSym = z3.Int("b")
cSym = z3.Int("c")
dSym = z3.Int("d")


def absVal(x):
    return z3.If(x > 0, x, -x)


def distant_from_dataset(dataset, var, eps):
    constraints = []
    for k in dataset:
        constraints.append(absVal(var - k) >= eps)
    return z3.And(constraints)


def boundOfParams(aSym, bSym, cSym, dSym, bound):
    return z3.And(
        -bound <= aSym,
        aSym <= bound,
        -bound <= bSym,
        bSym <= bound,
        -bound <= cSym,
        cSym <= bound,
        -bound <= dSym,
        dSym <= bound,
    )


def invHolds(c, d, x):
    return c * x + d >= 0


def Vexpr(a, b, x):
    return a * x + b


def VexprNonNeg(a, b, c, d, x):
    return z3.Implies(invHolds(c, d, x), Vexpr(a, b, x) >= 0)


init_state = 10

dataset = [init_state]


def invInit(c, d):
    return invHolds(c, d, init_state)


def invConsecAt(c, d, x):
    return z3.Implies(z3.And(invHolds(c, d, x), x >= 0), invHolds(c, d, x - 1))


def rankAtInv(a, b, c, d, x):
    return z3.Implies(
        z3.And(invHolds(c, d, x), x >= 0), Vexpr(a, b, x - 1) <= Vexpr(a, b, x) - 1
    )


def allConstraintsToSatisfy(a, b, c, d):
    x_var = z3.Int("x")
    return z3.And(
        [
            invInit(c, d),
            invConsecAt(c, d, x_var),
            rankAtInv(a, b, c, d, x_var),
            VexprNonNeg(a, b, c, d, x_var),
        ]
    )


def guess_and_check_idx(i, oldDataset):
    guesser5 = z3.Solver()
    guesser5.add(invInit(cSym, dSym))

    for x in dataset:
        guesser5.add(invConsecAt(cSym, dSym, x))
        guesser5.add(rankAtInv(aSym, bSym, cSym, dSym, x))
        guesser5.add(VexprNonNeg(aSym, bSym, cSym, dSym, x))
        guesser5.add(boundOfParams(aSym, bSym, cSym, dSym, 10))

    if guesser5.check() == z3.unsat:
        print(f"guesser {i}: unsat")
        sys.exit(0)

    print(f"guesser {i}: model")
    modelG5 = guesser5.model()
    print(modelG5)
    # guess 5
    # Summary of guess 5:

    a4 = int_to_int(modelG5[aSym])
    b4 = int_to_int(modelG5[bSym])
    c4 = int_to_int(modelG5[cSym])
    d4 = int_to_int(modelG5[dSym])
    print(f"a4 = {a4}")
    print(f"b4 = {b4}")
    print(f"c4 = {c4}")
    print(f"d4 = {d4}")
    print(f"V(x) = {round(a4, 2)} * x + {round(b4, 2)}")
    print(f"I(x) = {round(c4, 2)} * x + {round(d4, 2)}")

    # CHECK 5
    checker5 = z3.Solver()
    checker5.add(z3.Not(allConstraintsToSatisfy(a4, b4, c4, d4)))

    if checker5.check() == z3.unsat:
        print(f"checker {i}: unsat")
        sys.exit()

    print(f"checker {i}: model")
    modelC5 = checker5.model()
    print(modelC5)

    x_var = modelC5[z3.Int("x")]
    # x_as_float4 = real_to_float(x_var)
    x_as_float4 = int_to_int(x_var)
    print("x_as_float4", x_as_float4, type(x_as_float4))

    datasetnew = dataset + [x_as_float4]
    print(f"dataset after {i}th guess/check: {datasetnew}")
    return datasetnew


for idx in range(13):
    dataset = guess_and_check_idx(idx, dataset)
