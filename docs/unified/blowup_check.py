"""Third-layer check for docs/unified/BLOWUP.md (CPU, under a second).

Part 1. The trapping recursion of the Chen-Hou bootstrap, discrete skeleton:
        M_{i+1} = q M_i + C M_i^2 + r.
        Bounded for all i when (1 - q)^2 >= 4 C r and M_0 <= (1 - q)/(2C);
        escapes (grows without bound) when (1 - q)^2 < 4 C r.  Lean: Blowup.lean (trap_of_gap, escape_of_below).
Part 2. Rescaled time against physical time: unit steps of rescaled time, each with physical duration factor
        e^{a_i}, a_i <= -gamma.  The durations sum to a finite T*, the amplitude 1/d_n grows like e^{gamma n},
        and the BKM integral (amplitude x duration per step) gains a fixed quantum per step, so it diverges.
Part 3. Size of the O1 "for all outsides" for SU(2) on a lattice box of side n (vertices {0..n}^4):
        boundary links (the outside, by the Markov property), interior links (the integral), the dimensions after
        gauge fixing, and the number of cells a branch-and-bound enclosure would need at an optimistic
        resolution of 10 cells per direction.
"""
import itertools
import math


def part1():
    print("== Part 1: trapping recursion M' = q M + C M^2 + r")
    q, C = math.exp(-0.5), 1.0
    thr = (1 - q) ** 2 / (4 * C)
    print(f"q = e^-0.5 = {q:.6f}, C = {C}, threshold r* = (1-q)^2/(4C) = {thr:.6e}")
    for factor in (0.5, 0.99, 1.01, 2.0):
        r = factor * thr
        R = (1 - q) / (2 * C)
        M = R
        hit = None
        for i in range(200000):
            M = q * M + C * M * M + r
            if M > 10:
                hit = i + 1
                break
        state = f"escaped after {hit} steps" if hit else f"bounded, M_200000 = {M:.6e} <= R = {R:.6e}"
        print(f"  r = {factor:4.2f} r*: {state}")


def part2():
    print("== Part 2: rescaled steps in finite physical time")
    gamma = 0.7
    d, T, bkm, amp0 = 1.0, 0.0, 0.0, 1.0
    for n in range(60):
        T += d
        bkm += (amp0 / d) * d  # amplitude in physical variables times physical duration = rescaled amplitude
        d *= math.exp(-gamma)
    print(f"gamma = {gamma}: T after 60 steps = {T:.12f}, bound 1/(1-e^-gamma) = {1/(1-math.exp(-gamma)):.12f}")
    print(f"  amplitude after 60 steps = e^(gamma*60) = {math.exp(gamma*60):.3e}; BKM sum = {bkm:.1f} (one quantum per step)")


def links(n):
    V = list(itertools.product(range(n + 1), repeat=4))
    Vs = set(V)
    onb = lambda x: any(c in (0, n) for c in x)
    bl = il = 0
    for x in V:
        for mu in range(4):
            y = list(x)
            y[mu] += 1
            y = tuple(y)
            if y not in Vs:
                continue
            # a link lies in the boundary surface iff some coordinate other than mu is 0 or n
            if any(x[nu] in (0, n) for nu in range(4) if nu != mu):
                bl += 1
            else:
                il += 1
    bv = sum(1 for x in V if onb(x))
    iv = len(V) - bv
    return bl, il, bv, iv


def part3():
    print("== Part 3: the for-all over outsides of O1 (SU(2), box of side n lattice units)")
    print(" n | boundary links | interior links | outside dim (gauge-fixed) | integral dim | log10 cells at 10/dir")
    for n in (2, 3, 4, 6, 8):
        bl, il, bv, iv = links(n)
        out_dim = 3 * (bl - bv + 1)
        int_dim = 3 * (il - iv)
        print(f"{n:2d} | {bl:14d} | {il:14d} | {out_dim:25d} | {int_dim:12d} | {out_dim:d}")


if __name__ == "__main__":
    part1()
    part2()
    part3()
