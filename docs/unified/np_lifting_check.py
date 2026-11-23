"""Brute-force checks for NP-LIFTING.md (CPU, seconds, standard library only).

Two tiny unsatisfiable formulas F: pigeonhole 3 into 2 (6 variables, clauses of width 2) and the Tseitin formula on K_4
(6 edge variables, 16 clauses of width 3, one vertex with odd charge). Each is composed with the 2-bit XOR gadget (one
bit for Alice, one for Bob, so 12 bits) and, for the hiding check, with the Index gadget on a 1-bit pointer and a
2-bit table (3 bits per variable, 18 bits). The composition is the one of `Proof/Lifting.lean` (`comp`): for every
clause D of F and every choice of one gadget input pair per literal that falsifies the literal, one clause, falsified
exactly by the assignments that agree with all chosen pairs.

Check 1 (`comp_falsified_iff`): over all assignments u of the lifted variables, a clause of F o g is falsified iff the
decoded assignment z_i = g(block i) falsifies a clause of F. Both formulas are unsatisfiable, so every u falsifies one.
Check 2 (`lifted_needs_pair`): the all-1/2 point satisfies every linear clause inequality of F (when its clauses have
width at least 2) and of F o g (width at least 2 always), in exact rational arithmetic. The multilinear extension of
XOR at (1/2, 1/2) is 1/2, so the point of F lifts to the point of F o XOR. A control with a unit clause: the point fails
for F but holds for F o XOR.
Check 3 (hiding, the one-boundary encoder is lossless): under the uniform distribution on all lifted assignments, the
decoded assignment z is exactly uniform given Alice's half alone, and exactly uniform given Bob's half alone, for XOR.
For Index it is uniform given the pointer holder's half only; given the table holder's half it is not.
Check 4: the resolution width w(F) of each tiny formula, by saturation (the quantity the lifting theorem lifts).

Run: python docs/unified/np_lifting_check.py > docs/unified/np_lifting_check.log
"""
from fractions import Fraction
from itertools import product

HALF = Fraction(1, 2)


def php(pigeons, holes):
    var = {}
    for i in range(pigeons):
        for h in range(holes):
            var[(i, h)] = len(var)
    clauses = []
    for i in range(pigeons):
        clauses.append(frozenset((var[(i, h)], True) for h in range(holes)))
    for h in range(holes):
        for i in range(pigeons):
            for j in range(i + 1, pigeons):
                clauses.append(frozenset({(var[(i, h)], False), (var[(j, h)], False)}))
    return len(var), clauses


def tseitin_k4(charges=(1, 0, 0, 0)):
    edges = [(a, b) for a in range(4) for b in range(a + 1, 4)]
    clauses = []
    for v in range(4):
        inc = [k for k, (a, b) in enumerate(edges) if v in (a, b)]
        for bits in product([0, 1], repeat=len(inc)):
            if sum(bits) % 2 != charges[v]:
                clauses.append(frozenset((e, not bool(b)) for e, b in zip(inc, bits)))
    return len(edges), clauses


class Gadget:
    def __init__(self, name, a, b, g):
        self.name, self.a, self.b, self.g = name, a, b, g

    @property
    def width(self):
        return self.a + self.b


XOR = Gadget("XOR(1+1 bits)", 1, 1, lambda x, y: bool(x[0] ^ y[0]))
IND1 = Gadget("Index(1-bit pointer, 2-bit table)", 1, 2, lambda x, y: bool(y[x[0]]))


def lvar(G, i, party, j):
    """Index of a lifted variable: block i, Alice bits first, then Bob bits."""
    return i * G.width + (j if party == "A" else G.a + j)


def compose(n, clauses, G):
    pairs = {c: [(x, y) for x in product([0, 1], repeat=G.a) for y in product([0, 1], repeat=G.b)
                 if G.g(x, y) == c] for c in (False, True)}
    out = set()
    for D in clauses:
        lits = sorted(D)
        for ch in product(*[pairs[not s] for (_, s) in lits]):
            cl = set()
            for (i, _), (x, y) in zip(lits, ch):
                for j, xv in enumerate(x):
                    cl.add((lvar(G, i, "A", j), not bool(xv)))
                for j, yv in enumerate(y):
                    cl.add((lvar(G, i, "B", j), not bool(yv)))
            out.add(frozenset(cl))
    return out


def falsified(cl, u):
    return all(bool(u[v]) != s for (v, s) in cl)


def any_falsified(clauses, u):
    return any(falsified(c, u) for c in clauses)


def decode(G, n, u):
    z = []
    for i in range(n):
        x = tuple(u[lvar(G, i, "A", j)] for j in range(G.a))
        y = tuple(u[lvar(G, i, "B", j)] for j in range(G.b))
        z.append(int(G.g(x, y)))
    return tuple(z)


def lp_value(cl, p):
    return sum(p[v] if s else 1 - p[v] for (v, s) in cl)


def res_width(n, clauses, cap=8):
    for W in range(1, cap + 1):
        have = {c for c in clauses if len(c) <= W}
        changed = True
        while changed:
            changed = False
            for c1 in list(have):
                for (v, s) in c1:
                    for c2 in list(have):
                        if (v, not s) in c2:
                            r = (c1 - {(v, s)}) | (c2 - {(v, not s)})
                            if len(r) <= W and r not in have:
                                have.add(r)
                                changed = True
                                if not r:
                                    return W
            if frozenset() in have:
                return W
    return None


def check_formula(name, n, clauses):
    print(f"\n=== {name}: {n} variables, {len(clauses)} clauses, widths {sorted({len(c) for c in clauses})}")
    ok_all = True
    # F unsatisfiable
    assert all(any_falsified(clauses, z) for z in product([0, 1], repeat=n)), "F should be unsatisfiable"
    print("F unsatisfiable by brute force over all 2^%d assignments: True" % n)
    w = res_width(n, clauses)
    print(f"resolution width w(F) by saturation: {w}")
    pF = [HALF] * n
    minF = min(lp_value(c, pF) for c in clauses)
    print(f"F: all-1/2 point, least clause value {minF} (>= 1 needed): {minF >= 1}")
    ok_all &= minF >= 1
    for G in (XOR, IND1):
        N = n * G.width
        L = compose(n, clauses, G)
        print(f"-- gadget {G.name}: {N} lifted bits, {len(L)} lifted clauses, widths {sorted({len(c) for c in L})}")
        # Check 1
        bad = 0
        for u in product([0, 1], repeat=N):
            lhs = any_falsified(L, u)
            rhs = any_falsified(clauses, decode(G, n, u))
            if lhs != rhs or not lhs:
                bad += 1
        print(f"   check 1, comp_falsified_iff over all 2^{N} assignments (and F o g unsatisfiable): "
              f"mismatches = {bad}")
        ok_all &= bad == 0
        # Check 2
        p = [HALF] * N
        minL = min(lp_value(c, p) for c in L)
        ext = HALF if G is XOR else None
        print(f"   check 2, all-1/2 point of F o g: least clause value {minL} (>= 1 needed): {minL >= 1}")
        ok_all &= minL >= 1
        if G is XOR:
            # multilinear extension of XOR at (1/2, 1/2): x + y - 2xy
            e = HALF + HALF - 2 * HALF * HALF
            print(f"   multilinear XOR at (1/2, 1/2) = {e}  (the lifted point decodes to the point 1/2 of F): {e == HALF}")
            ok_all &= e == HALF
        # Check 3: hiding
        for party in ("Alice", "Bob"):
            own = (lambda i, j: lvar(G, i, "A", j)) if party == "Alice" else (lambda i, j: lvar(G, i, "B", j))
            nown = G.a if party == "Alice" else G.b
            own_idx = [own(i, j) for i in range(n) for j in range(nown)]
            other_idx = [k for k in range(N) if k not in set(own_idx)]
            worst = Fraction(0)
            joint_uniform = True
            for ownval in product([0, 1], repeat=len(own_idx)):
                counts = {}
                tot = 0
                for oth in product([0, 1], repeat=len(other_idx)):
                    u = [0] * N
                    for k, v in zip(own_idx, ownval):
                        u[k] = v
                    for k, v in zip(other_idx, oth):
                        u[k] = v
                    z = decode(G, n, u)
                    counts[z] = counts.get(z, 0) + 1
                    tot += 1
                if len(counts) != 2 ** n or len(set(counts.values())) != 1:
                    joint_uniform = False
                for i in range(n):
                    p1 = Fraction(sum(c for z, c in counts.items() if z[i] == 1), tot)
                    worst = max(worst, abs(p1 - HALF))
            print(f"   check 3, z given {party}'s half alone: jointly uniform on all 2^{n} values = {joint_uniform}; "
                  f"largest |P(z_i = 1 | half) - 1/2| = {worst}")
            if G is XOR:
                ok_all &= joint_uniform and worst == 0
            elif party == "Alice":
                ok_all &= joint_uniform and worst == 0
            else:
                ok_all &= (not joint_uniform) and worst > 0
    return ok_all


def main():
    results = []
    n, cl = php(3, 2)
    results.append(check_formula("pigeonhole 3 into 2", n, cl))
    n, cl = tseitin_k4()
    results.append(check_formula("Tseitin on K_4, charge (1,0,0,0)", n, cl))
    # control: a unit-clause formula; F's all-1/2 point fails, the lifted one holds
    print("\n=== control: F = { (x), (not x) }  (width 1)")
    n, cl = 1, [frozenset({(0, True)}), frozenset({(0, False)})]
    minF = min(lp_value(c, [HALF]) for c in cl)
    L = compose(n, cl, XOR)
    minL = min(lp_value(c, [HALF] * 2) for c in L)
    print(f"F: all-1/2 point, least clause value {minF}: point satisfies F's linear clauses: {minF >= 1}")
    print(f"F o XOR: {len(L)} clauses, widths {sorted({len(c) for c in L})}, least clause value {minL}: "
          f"point satisfies the lifted clauses: {minL >= 1}")
    results.append(minF < 1 and minL >= 1)
    print("\n=== summary")
    print("all checks as expected:", all(results))


if __name__ == "__main__":
    main()
