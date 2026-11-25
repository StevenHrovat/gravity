# D-pin scoping, third side check: where does the "zlift" average (star_dynamics.py) trap deep stars?
# Prints, after T steps from Haar stars, the histogram of relative angles theta(g_b g_b'^-1) of the stars that stay
# deep (spread > 0.5). Expectation if trapping is at the fold discontinuity: angles cluster at pi/2 (and 0, pi).
import sys, os
import numpy as np
user_args = sys.argv[1:]
sys.argv = sys.argv[:1] + ["1", "0", "13", "4"]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "star_dynamics.py"), encoding="utf-8").read()
ns = {}; exec(compile(src.split("for zlift in (False, True):")[0], "star_dynamics.py", "exec"), ns)
S = int(user_args[0]) if user_args else 20000; T = int(user_args[1]) if len(user_args) > 1 else 12
n = ns["n"]; rng = np.random.default_rng(3)
g = rng.normal(size=(S, n, 4)); g /= np.linalg.norm(g, axis=-1, keepdims=True)
for _ in range(T):
    g = ns["step"](g, True)
sp, sz = ns["spreads"](g)
deep = g[sp > 0.5]
th = []
for b in range(n):
    rel = ns["qmul"](deep, ns["qinv"](deep[:, b:b+1, :]))
    th.append(np.arccos(np.clip(rel[..., 0], -1, 1)))
th = np.stack(th, 1).ravel()
h, edges = np.histogram(th, bins=12, range=(0, np.pi))
print(f"deep after {T} steps: {len(deep)}/{S}")
for c, a, b in zip(h, edges[:-1], edges[1:]):
    print(f"  angle {a:.2f}-{b:.2f}: {c}")
