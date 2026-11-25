# P0 test of the "twisted sector" averaging (P0.md). Questions, fixed before running:
#  Q1 small fields: on stars whose relative elements are all small, is the twisted rule identical to Balaban's (0.4)?
#  Q2 trapping: starting from Haar-random (deep) stars, after T steps is every star either moderate (spread < 0.5) or a
#     labelled core whose label-corrected ("twisted") star is smooth?  Deep stars that are neither = trapped.
#  Q3 shells: the same with random small-field shells (each path carries an independent factor exp(eps * gaussian)).
# Rule (P0.md 1): an unlabelled star gets a Z2 label sigma (sigma_b = +-1, not all equal) when the corrected star
#  h_b = sigma_b g_b has spread < theta_create; a labelled star is averaged as t_c = sigma_c * [(0.4) applied to h]_c, so
#  the loops fed to the logarithm are the corrected loops h_b h_c^-1 (the cut never enters); the label is kept, and
#  dropped only if the corrected spread exceeds pi/2. Unlabelled stars use Balaban's (0.4) unchanged.
# Usage: python -I twist_dynamics.py [samples] [steps] [eps] [theta_create] [paths_per_group]
import sys, os
import numpy as np

args = sys.argv[1:]
S = int(args[0]) if len(args) > 0 else 20000
T = int(args[1]) if len(args) > 1 else 15
EPS = float(args[2]) if len(args) > 2 else 0.0
TH_C = float(args[3]) if len(args) > 3 else 0.6
NP = int(args[4]) if len(args) > 4 else 4
sys.argv = sys.argv[:1] + ["1", "0", "13", "4"]
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "star_dynamics.py"), encoding="utf-8").read()
ns = {}; exec(compile(src.split("for zlift in (False, True):")[0], "star_dynamics.py", "exec"), ns)
qmul, qinv, qlog, qexp, spreads, F, n = ns["qmul"], ns["qinv"], ns["qlog"], ns["qexp"], ns["spreads"], ns["F"], ns["n"]
rng = np.random.default_rng(11)


def noise(shape):
    if EPS == 0.0:
        out = np.zeros(shape + (4,)); out[..., 0] = 1.0; return out
    return qexp(EPS * rng.normal(size=shape + (3,)))


def avg04(g):
    """Balaban (0.4) on the star with paths: NP paths per (c, b) group, each with its own shell factor."""
    Sn = g.shape[0]
    t = np.empty_like(g)
    for c in range(n):
        R = noise((Sn, n, NP))                                     # shell factor of each path
        Rref = R[:, c, 0, :]                                       # the straight path belongs to group b = c
        ref = qmul(g[:, c, :], Rref)                               # U(c)
        P = qmul(g[:, :, None, :], R)                              # path transports g_b R_x
        loops = qmul(P, qinv(ref)[:, None, None, :])
        a = (F[c][None, :, None, None] * qlog(loops) / NP).sum((1, 2))
        t[:, c, :] = qmul(qexp(a), ref)
    return t


def corrected_spread(g, sig):
    h = g * sig[..., None]
    return spreads(h)[0], h


def try_label(g):
    """Best non-trivial Z2 pattern (relative to each reference bond); returns labels (or zeros) and corrected spread."""
    best_sp = np.full(g.shape[0], np.inf); best_sig = np.zeros(g.shape[:2])
    for r in range(n):
        rel = qmul(g, qinv(g[:, r:r+1, :]))
        sig = np.where(rel[..., 0] < 0, -1.0, 1.0)
        nontriv = (sig < 0).any(1)
        sp, _ = corrected_spread(g, sig)
        better = nontriv & (sp < best_sp)
        best_sp = np.where(better, sp, best_sp); best_sig[better] = sig[better]
    return best_sig, best_sp


def run(twist, g, T, report):
    lab = np.zeros(g.shape[:2])                                    # 0 = unlabelled
    for k in range(T + 1):
        labelled = (lab != 0).any(1)
        sp, _ = spreads(g)
        csp = np.where(labelled, corrected_spread(g, np.where(lab == 0, 1.0, lab))[0], np.nan)
        if k in report:
            mod = (~labelled) & (sp < 0.5)
            carried = labelled & (csp < 0.5)
            trapped = (~mod) & (~carried)
            print(f"  step {k:2d}: moderate {mod.mean():.4f}  labelled&smooth {carried.mean():.4f}  "
                  f"trapped {trapped.mean():.4f}  (labelled {labelled.mean():.4f})")
        if k == T:
            return g, lab
        if twist:
            new_sig, bsp = try_label(g)
            create = (~labelled) & (bsp < TH_C) & (sp >= 0.5)
            lab[create] = new_sig[create]
            labelled = (lab != 0).any(1)
            drop = labelled & (corrected_spread(g, np.where(lab == 0, 1.0, lab))[0] > np.pi / 2)
            lab[drop] = 0; labelled = (lab != 0).any(1)
            sig = np.where(labelled[:, None], lab, 1.0)
            h = g * sig[..., None]
            th = avg04(h)
            g = th * sig[..., None]
        else:
            g = avg04(g)


print(f"L=13 d=4 samples={S} steps={T} eps={EPS} theta_create={TH_C} paths/group={NP}")
# Q1: small fields
g0 = qexp(0.1 * rng.normal(size=(2000, n, 3)))
state = rng.bit_generator.state
a = avg04(g0); rng.bit_generator.state = state
sig, bsp = try_label(g0)
print(f"Q1 small fields (spread <= {spreads(g0)[0].max():.3f}): labels created on {np.mean(bsp < TH_C):.4f} of stars "
      f"(0 means the twisted rule is (0.4) there, exactly)")
rep = (0, 1, 2, 3, 6, 10, T)
for twist in (False, True):
    print(f"--- {'twisted rule' if twist else 'Balaban (0.4)'}; Haar-random stars")
    g = rng.normal(size=(S, n, 4)); g /= np.linalg.norm(g, axis=-1, keepdims=True)
    run(twist, g, T, rep)
for twist in (False, True):
    print(f"--- {'twisted rule' if twist else 'Balaban (0.4)'}; stars within 0.05 of the vortex pattern")
    s = np.array([1, 1, 1, 1, -1, -1, -1, -1], float)
    g = qexp(0.05 * rng.normal(size=(S, n, 3)) / np.sqrt(3)) * s[None, :, None]
    run(twist, g, T, rep)
