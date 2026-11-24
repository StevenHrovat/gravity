# No-trapping evidence in the one-site star model at L = 13, d = 4 (NO-TRAP.md). Questions fixed before running:
#  NT1 local contraction: for stars of spread <= alpha, the largest ratio spread(after one step)/spread(before) under
#      Balaban's star map (trivial shell), from random samples and from a local search that maximises the ratio.
#  NT2 capture: "captured" = spread < 0.5 or labelable (isolated sign pattern, corrected spread < 0.6, the twisted rule).
#      Capture time of Haar-random stars, then an adversarial search (random restarts + hill climbing on the star) that
#      maximises the capture time, started from Haar stars and from stars near sign patterns. A trap = no capture in 60.
# Usage: python -I notrap_search.py [restarts] [iterations] [seed]
import sys, os
import numpy as np

R = int(sys.argv[1]) if len(sys.argv) > 1 else 200
IT = int(sys.argv[2]) if len(sys.argv) > 2 else 60
SEED = int(sys.argv[3]) if len(sys.argv) > 3 else 5
sys.argv = sys.argv[:1] + ["1", "0", "13", "4"]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "star_dynamics.py"), encoding="utf-8").read()
ns = {}; exec(compile(src.split("for zlift in (False, True):")[0], "star_dynamics.py", "exec"), ns)
qmul, qinv, qexp, spreads, step04, n = ns["qmul"], ns["qinv"], ns["qexp"], ns["spreads"], ns["step"], ns["n"]
rng = np.random.default_rng(SEED)
CAP = 60


def labelable_batch(g, th=0.6):
    out = np.zeros(g.shape[0], bool)
    for r in range(n):
        rel = qmul(g, qinv(g[:, r:r + 1]))
        sig = np.where(rel[..., 0] < 0, -1.0, 1.0)
        nontriv = (sig < 0).any(1)
        sp, _ = spreads(g * sig[..., None])
        out |= nontriv & (sp < th)
    return out


def capture_times(g):
    g = g.copy(); t = np.full(g.shape[0], -1)
    for k in range(CAP + 1):
        sp, _ = spreads(g)
        cap = (t < 0) & ((sp < 0.5) | labelable_batch(g))
        t[cap] = k
        if (t >= 0).all():
            break
        g = step04(g, False)
    t[t < 0] = CAP + 1                                     # not captured within CAP
    return t


def haar(m):
    g = rng.normal(size=(m, n, 4)); return g / np.linalg.norm(g, axis=-1, keepdims=True)


def perturb(g, sig):
    return qmul(qexp(sig * rng.normal(size=g.shape[:-1] + (3,))), g)


# ---------- NT1 ----------
print("NT1 local contraction (ratio of spreads after/before one step, worst found):")
for alpha in (0.3, 0.6, 0.9, 1.2, 1.5):
    g = qexp((alpha / 2) * rng.uniform(-1, 1, size=(40000, n, 3)) / np.sqrt(3))   # points in a ball: spread <= alpha
    s0, _ = spreads(g); keep = s0 > 0.5 * alpha * 0.3
    g = g[keep]; s0 = s0[keep]
    s1, _ = spreads(step04(g, False)); ratio = s1 / s0
    worst = g[np.argsort(ratio)[-200:]]                  # local search from the 200 worst samples
    best = ratio.max()
    for _ in range(30):
        cand = perturb(worst, 0.02)
        c0, _ = spreads(cand); ok = c0 <= alpha
        c1, _ = spreads(step04(cand, False))
        r = np.where(ok, c1 / np.maximum(c0, 1e-12), 0)
        w0, _ = spreads(worst); w1, _ = spreads(step04(worst, False)); rw = w1 / np.maximum(w0, 1e-12)
        better = r > rw
        worst[better] = cand[better]
        best = max(best, r.max())
    print(f"  spread <= {alpha:.1f}: worst ratio {best:.4f}  (L^(1-d) = {13 ** -3:.5f})")

# ---------- NT2 ----------
base = capture_times(haar(20000))
print(f"NT2 Haar stars (20000): capture time max {base.max()}  mean {base.mean():.2f}  "
      f"histogram {np.bincount(base, minlength=12)[:15].tolist()}")
starts = [haar(R // 2)]
s = np.ones(n); s[4:] = -1                                     # near sign patterns (vortex type), off by 0.6-0.9
pat = np.zeros((R - R // 2, n, 4)); pat[..., 0] = s
starts.append(perturb(pat, 0.35))
g = np.concatenate(starts)
t = capture_times(g)
sig = np.full(g.shape[0], 0.3)
for it in range(IT):
    cand = qmul(qexp(sig[:, None, None] * rng.normal(size=g.shape[:-1] + (3,))), g)
    tc = capture_times(cand)
    better = tc >= t
    g[better] = cand[better]; t[better] = tc[better]
    sig = np.where(better, sig * 1.1, sig * 0.8).clip(1e-4, 1.0)
    if it % 10 == 0 or it == IT - 1:
        print(f"  search iteration {it:3d}: max capture time {t.max()}  (trapped = {CAP + 1})  "
              f"top 5 {sorted(t.tolist())[-5:]}")
worst = g[np.argmax(t)]
sp, sz = spreads(worst[None])
print(f"worst star found: capture time {t.max()}, spread {sp[0]:.3f}, distance of relative elements to the centre "
      f"{sz[0]:.3f}")
