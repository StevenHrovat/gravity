# D-pin scoping, second side check: stars that start within distance delta of the exact vortex pattern
# (relative elements +-1: -1 on directions +-3, +-4), under Balaban's star map (star_dynamics.py, trivial shell).
# Question: does the vortex trap nearby stars (stable) or expel them (unstable), and how fast?
# Usage: python -I near_vortex.py [samples] [steps]
import sys
import numpy as np
user_args = sys.argv[1:]
sys.argv = sys.argv[:1] + ["1", "0", "13", "4"]              # reuse star_dynamics definitions (L = 13, d = 4)
import importlib.util, os
spec = importlib.util.spec_from_file_location("sd", os.path.join(os.path.dirname(os.path.abspath(__file__)), "star_dynamics.py"))
src = open(spec.origin, encoding="utf-8").read().split("for zlift in (False, True):")[0]
ns = {}; exec(compile(src, spec.origin, "exec"), ns)
S = int(user_args[0]) if len(user_args) > 0 else 20000
T = int(user_args[1]) if len(user_args) > 1 else 10
n = ns["n"]; rng = np.random.default_rng(7)
s = np.array([1, 1, 1, 1, -1, -1, -1, -1], float)           # directions (+1,-1,+2,-2,+3,-3,+4,-4)
for delta in (1e-1, 1e-2, 1e-4, 1e-8):
    v = rng.normal(size=(S, n, 3)); v *= delta / np.linalg.norm(v, axis=-1, keepdims=True) * rng.random((S, n, 1))
    g = ns["qexp"](v) * s[None, :, None]
    out = []
    for k in range(T + 1):
        sp, sz = ns["spreads"](g)
        out.append(f"{k}:{np.mean(sz < 0.05):.3f}/{np.mean(sp > 0.5):.3f}")
        g = ns["step"](g, False)
    print(f"delta={delta:g}  step:(near centre-valued)/(deep)  " + "  ".join(out))
