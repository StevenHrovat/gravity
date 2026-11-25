# Reduced d = 4, L = 13 test of the one blocking step that the full-lattice test could not reach (TWIST.md 4, NO-TRAP.md 2).
# Questions fixed before running:
#  Q1 path fraction: for a fine site z of a block B(Y), the weight f(z) of the paths of Balaban's average [I] (0.4) of
#     the coarse bonds at Y that pass through z (maximum over the 8 coarse bonds). Expected O(1/(2d)) next to the centre
#     and small far from it.
#  Q2 off-centre cores: put a deep core (vortex star, Haar star, or Haar values on 1-3 bonds) at an off-centre site z,
#     everything else trivial, and block once with the exact contour family of (0.4) at L = 13, d = 4. Classify the
#     resulting coarse star at Y: moderate (spread < 0.5), labelable (isolated sign pattern, corrected spread < 0.6), or
#     deep. For the deep ones, iterate the one-site star map (star_dynamics.py, L = 13) and record the capture time
#     (steps until moderate or labelable under the twisted rule). Trapping = no capture within 40 steps.
# Trivial shell (the shell is smooth; its effect is tested in the one-site model). Exact: all 541k paths of G(Y, x),
#   x in B(Y), with the segment to the next block; paths in the next block never meet B(Y).
# Usage: python -I offcentre_L13.py [random_positions] [samples_per_type] [seed]
import sys, os, itertools, time
import numpy as np

NRAND = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
NS = int(sys.argv[2]) if len(sys.argv) > 2 else 3
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 1
L, d = 13, 4
h = (L - 1) // 2
user_argv = sys.argv
sys.argv = sys.argv[:1] + ["1", "0", str(L), str(d)]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "star_dynamics.py"), encoding="utf-8").read()
ns = {}; exec(compile(src.split("for zlift in (False, True):")[0], "star_dynamics.py", "exec"), ns)
qmul, qinv, qlog, qexp, spreads, step04 = ns["qmul"], ns["qinv"], ns["qlog"], ns["qexp"], ns["spreads"], ns["step"]
rng = np.random.default_rng(SEED)


def dcode(axis, sign):
    return 2 * axis + (0 if sign > 0 else 1)


def opp(code):
    return code ^ 1


# ---------- enumerate all paths of the coarse bond (Y, Y + L e_0), Y = 0, inside B(Y) ----------
t0 = time.time()
W = {}            # site -> {tuple of (in, out): weight}
wsite = {}        # site -> total weight of paths through it
for x in itertools.product(range(-h, h + 1), repeat=d):
    nz = [i for i in range(d) if x[i] != 0]
    perms = list(itertools.permutations(nz)) if nz else [()]
    w = 1.0 / (L ** d * len(perms))
    for perm in perms:
        sites = [(0,) * d]; dirs = []
        cur = [0] * d
        for i in perm:
            s = 1 if x[i] > 0 else -1
            for _ in range(abs(x[i])):
                cur[i] += s; sites.append(tuple(cur)); dirs.append(dcode(i, s))
        for _ in range(L):                                  # segment along +e_0 (only the part inside B(Y) matters)
            cur[0] += 1
            sites.append(tuple(cur)); dirs.append(dcode(0, 1))
            if cur[0] > h:
                break
        visits = {}
        for k in range(1, len(sites) - 1):                  # interior sites of the path
            z = sites[k]
            if max(abs(c) for c in z) > h or z == (0,) * d:
                continue
            visits.setdefault(z, []).append((opp(dirs[k - 1]), dirs[k]))
        for z, v in visits.items():
            dz = W.setdefault(z, {}); key = tuple(v)
            dz[key] = dz.get(key, 0.0) + w
            wsite[z] = wsite.get(z, 0.0) + w
print(f"paths enumerated in {time.time() - t0:.0f}s; sites touched: {len(W)}")
REF = {(t,) + (0,) * (d - 1) for t in range(1, h + 1)}       # sites of the straight reference path inside B(Y)


# ---------- symmetry: frame in which the coarse bond (a, s) becomes (0, +) ----------
def frame(a, s):
    """Returns (map of site coordinates, map of direction codes) taking the bond (Y, Y + s L e_a) to (Y, Y + L e_0)."""
    def site(z):
        z = list(z); z[0], z[a] = z[a], z[0]
        if s < 0:
            z[0] = -z[0]
        return tuple(z)
    def dmap(code):
        ax, sg = code // 2, (1 if code % 2 == 0 else -1)
        if ax == 0: ax = a
        elif ax == a: ax = 0
        if s < 0 and ax == 0:
            sg = -sg
        return dcode(ax, sg)
    return site, dmap


FR = [frame(a, s) for a in range(d) for s in (1, -1)]       # coarse direction index = 2a + (0 if s>0 else 1)


def path_fraction(z):
    return max(wsite.get(fs(z), 0.0) for fs, _ in FR)


def coarse_star(z, g):
    """Coarse star at Y (8 quaternions) for a core with star g (8 quaternions, by direction code) at site z."""
    out = np.empty((2 * d, 4))
    for c, (fs, fd) in enumerate(FR):
        zp = fs(z)
        gp = np.empty_like(g)
        for code in range(2 * d):
            gp[fd(code)] = g[code]                          # the core's bond in direction code appears as fd(code)
        tups = W.get(zp, {})
        Pref = None
        if zp in REF:
            Pref = qmul(qinv(gp[dcode(0, -1)]), gp[dcode(0, 1)])
        U = Pref if Pref is not None else np.array([1.0, 0, 0, 0])
        Ui = qinv(U)
        acc = np.zeros(3); wt = 0.0
        for tup, w in tups.items():
            P = np.array([1.0, 0, 0, 0])
            for i_, o_ in tup:
                P = qmul(P, qmul(qinv(gp[i_]), gp[o_]))
            acc += w * qlog(qmul(P, Ui)); wt += w
        acc += (1.0 - wt) * qlog(Ui)
        out[c] = qmul(qexp(acc), U)
    return out


def labelable(g, th=0.6):
    """Non-trivial sign pattern with corrected spread < th (P0.md rule, one-site form)."""
    n = g.shape[0]
    for r in range(n):
        rel = qmul(g, qinv(g[r:r + 1]))
        sig = np.where(rel[:, 0] < 0, -1.0, 1.0)
        if (sig < 0).any():
            sp, _ = spreads((g * sig[:, None])[None])
            if sp[0] < th:
                return True
    return False


def capture_time(g, cap=40):
    g = g[None].copy()
    for k in range(cap + 1):
        sp, _ = spreads(g)
        if sp[0] < 0.5 or labelable(g[0]):
            return k
        g = step04(g, False)
    return None


def core(kind):
    if kind == "vortex":
        axes = rng.permutation(d)[: rng.integers(1, d)]
        s = np.ones(2 * d)
        for a in axes:
            s[2 * a] = s[2 * a + 1] = -1
        g = np.zeros((2 * d, 4)); g[:, 0] = s
        return g
    if kind == "haar":
        g = rng.normal(size=(2 * d, 4)); return g / np.linalg.norm(g, axis=1, keepdims=True)
    g = np.zeros((2 * d, 4)); g[:, 0] = 1
    for b in rng.choice(2 * d, size=rng.integers(1, 4), replace=False):
        v = rng.normal(size=4); g[b] = v / np.linalg.norm(v)
    return g


# ---------- Q1 ----------
fr = {}
for z in W:
    dist = max(abs(c) for c in z)
    fr.setdefault(dist, []).append(path_fraction(z))
print("Q1 path fraction f(z) (max over the 8 coarse bonds) by l_inf distance from the centre:")
for dist in sorted(fr):
    a = np.array(fr[dist]); print(f"  distance {dist}: max {a.max():.4f}  median {np.median(a):.5f}  sites {len(a)}")

# ---------- Q2 ----------
near = [z for z in itertools.product(range(-2, 3), repeat=d) if any(z)]
allsites = list(itertools.product(range(-h, h + 1), repeat=d))
far = [allsites[i] for i in rng.choice(len(allsites), size=NRAND, replace=False) if any(allsites[i])]
for label, sites in (("near (distance <= 2)", near), ("random", far)):
    for kind in ("vortex", "haar", "bonds"):
        res = {"moderate": 0, "labelable": 0, "deep": 0}; caps = []; trapped = 0; maxspread = 0.0
        for z in sites:
            for _ in range(NS):
                t = coarse_star(z, core(kind))
                sp, _ = spreads(t[None]); sp = sp[0]; maxspread = max(maxspread, sp)
                if sp < 0.5:
                    res["moderate"] += 1
                elif labelable(t):
                    res["labelable"] += 1
                else:
                    res["deep"] += 1
                    ct = capture_time(t)
                    if ct is None:
                        trapped += 1
                    else:
                        caps.append(ct)
        tot = sum(res.values())
        print(f"Q2 {label:22s} {kind:7s}: n={tot}  moderate {res['moderate']/tot:.3f}  labelable {res['labelable']/tot:.3f}  "
              f"deep {res['deep']/tot:.3f}  max coarse spread {maxspread:.3f}  "
              f"capture time of deep ones: max {max(caps) if caps else '-'}  trapped {trapped}")
print(f"done [{time.time() - t0:.0f}s]")
