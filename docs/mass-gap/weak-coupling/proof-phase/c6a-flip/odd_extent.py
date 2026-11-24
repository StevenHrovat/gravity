"""c6a-flip: is p <= 1/2 true for odd extents? Brute force 2D Z2 lattice gauge theory on an Lx x Ly torus
(one twisted plaquette), plus the exact 2D formulas for Z2 and SU(2). CPU, seconds. Output: odd_extent.log."""
import itertools, math

def z2_brute(Lx, Ly, beta, twist):
    links = [(x, y, d) for x in range(Lx) for y in range(Ly) for d in (0, 1)]
    idx = {l: i for i, l in enumerate(links)}
    plaqs = []
    for x in range(Lx):
        for y in range(Ly):
            plaqs.append((idx[(x, y, 0)], idx[((x + 1) % Lx, y, 1)], idx[(x, (y + 1) % Ly, 0)], idx[(x, y, 1)]))
    Z = 0.0
    for cfg in itertools.product((1, -1), repeat=len(links)):
        s = 0.0
        for k, (a, b, c, d) in enumerate(plaqs):
            u = cfg[a] * cfg[b] * cfg[c] * cfg[d]
            if twist and k == 0:
                u = -u
            s += u
        Z += math.exp(beta * s)
    return Z

def z2_exact(A, beta, twist):
    c, s = 2 * math.cosh(beta), 2 * math.sinh(beta)
    return (c ** A - s ** A) / 2 if twist else (c ** A + s ** A) / 2

def su2_exact(A, beta, twist, jmax=12):
    # torus (genus 1): Z = sum_j (c_j/(d_j c_0))^A up to a common factor, c_j = character coefficient of exp(beta tr U)
    # c_j = (2/beta) * I_{2j+1}(2 beta) * ... ; use the ratio a_j = I_{2j+1}(2b)/I_1(2b) with d_j = 2j+1, sign (-1)^(2j) for the twist
    def bessel_I(n, x, terms=40):
        return sum((x / 2) ** (2 * k + n) / (math.factorial(k) * math.gamma(k + n + 1)) for k in range(terms))
    b = beta
    tot = 0.0
    for twoj in range(0, 2 * jmax):
        d = twoj + 1
        cj = d * bessel_I(d, 2 * b) / b if b != 0 else (1.0 if twoj == 0 else 0.0)
        # normalised plaquette coefficient per rep: cj / d
        w = (cj / d) ** A
        sign = (-1) ** twoj if twist else 1
        tot += sign * w
    return tot

lines = []
for (Lx, Ly) in [(3, 3), (2, 3), (3, 1)]:
    for beta in (0.5, -0.5):
        Z0, Zt = z2_brute(Lx, Ly, beta, False), z2_brute(Lx, Ly, beta, True)
        A = Lx * Ly
        e0, et = z2_exact(A, beta, False), z2_exact(A, beta, True)
        p = Zt / (Zt + Z0)
        lines.append(f"Z2 {Lx}x{Ly} beta={beta:+.1f}: Z_tw/Z = {Zt/Z0:.6f}, p = {p:.6f} ({'p > 1/2' if p > 0.5 else 'p <= 1/2'}); "
                     f"exact ratio {et/e0:.6f}")
for A in (9, 6):
    for beta in (1.0, -1.0):
        Z0, Zt = su2_exact(A, beta, False), su2_exact(A, beta, True)
        p = Zt / (Zt + Z0)
        lines.append(f"SU(2) 2D area {A} beta={beta:+.1f} (beta multiplies tr U): Z_tw/Z = {Zt/Z0:.6f}, p = {p:.6f} "
                     f"({'p > 1/2' if p > 0.5 else 'p <= 1/2'})")
open("odd_extent.log", "w").write("\n".join(lines) + "\n")
print("\n".join(lines))
