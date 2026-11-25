"""Predictions of c7a-fluxvac for the joint z0/z_e measurement (c5e-dmp PREREG-JOINT), written before its data were read.

Model (stated in PREREG.md, section 2; no fit to the running measurement):
  x = L * a*sqrt(sigma) with a*sqrt(sigma) = 0.350, 0.258, 0.1825 (beta 2.3, 2.4, 2.5), as in PREREG-JOINT.
  flux act z_e(x): string band for x >= 1.4: Luescher x^2 - pi/3 (low), Nambu-Goto x*sqrt(x^2 - pi/3) (high), centre c6b fit x^2 - 0.88.
                  For x < 1.4 no string prediction (small-volume regime): reported as None.
  glueball branch z_g(x) = r*x, r in [3.4, 3.8] (centre 3.6), no finite-size correction.
  pair threshold z_pp = 2 z_e (one state per tube, no binding).
  vacuum act z0 = min(z_pp, z_g) - b, binding b in [0, 1] if |x - x_s| <= 0.4 (x_s = switch, z_pp = z_g), else 0.
Outputs: per box (z_e, z_pp, z_g, branch, z0 band) and per pair (flux gain G_e = z_e(2L) - 2 z_e(L), vacuum loss c = 2 z0(L) - z0(2L),
g0 = z0(2L)/z0(L), R = vacuum gain / (2 G_e)). Pure arithmetic, no randomness, runs in milliseconds.
"""
import math

ASIG = {2.3: 0.350, 2.4: 0.258, 2.5: 0.1825}
BOXES = {2.3: [4, 6, 8, 12], 2.4: [4, 6, 8, 12, 16], 2.5: [6, 8, 12, 16, 24]}
PAIRS = [(2.3, 4), (2.3, 6), (2.4, 4), (2.4, 6), (2.4, 8), (2.5, 6), (2.5, 8), (2.5, 12)]  # (beta, L) -> 2L; 2.5/12 optional
R_BAND = (3.4, 3.6, 3.8)
FOURPI = 4 * math.pi


def ze_band(x):
    if x < 1.4:
        return None
    lo = x * x - math.pi / 3
    hi = x * math.sqrt(x * x - math.pi / 3)
    mid = x * x - 0.88
    return (lo, mid, hi)


def switch(r, which):
    # 2 z_e(x) = r x with z_e = x^2 - k (k = pi/3 or 0.88) -> 2x^2 - r x - 2k = 0; Nambu-Goto solved numerically
    if which == "NG":
        f = lambda x: 2 * x * math.sqrt(x * x - math.pi / 3) - r * x
        a, b = 1.05, 5.0
        for _ in range(80):
            m = 0.5 * (a + b)
            a, b = (m, b) if f(m) < 0 else (a, m)
        return 0.5 * (a + b)
    k = math.pi / 3 if which == "L" else 0.88
    return (r + math.sqrt(r * r + 16 * k)) / 4


def z0_band(x):
    """Return (z0_lo, z0_mid, z0_hi, branch) under the model; None outside the string regime."""
    zb = ze_band(x)
    if zb is None:
        return None
    vals = []
    for r in R_BAND:
        for i, ze in enumerate(zb):
            zpp, zg = 2 * ze, r * x
            xs = switch(r, ["L", "fit", "NG"][i])
            b_hi = 1.0 if abs(x - xs) <= 0.4 else 0.0
            vals += [min(zpp, zg), min(zpp, zg) - b_hi]
    zpp_mid, zg_mid = 2 * zb[1], R_BAND[1] * x
    branch = "FLUX-PAIR" if zpp_mid < zg_mid - 1 else ("GLUEBALL" if zg_mid < zpp_mid - 1 else "MIXED")
    mid = min(zpp_mid, zg_mid) - (0.5 if abs(x - switch(3.6, "fit")) <= 0.4 else 0.0)
    return (min(vals), mid, max(vals), branch)


def main():
    print("switch x_s (2 z_e = r x):")
    for r in R_BAND:
        print(f"  r = {r}: Luescher {switch(r, 'L'):.2f}, c6b fit {switch(r, 'fit'):.2f}, Nambu-Goto {switch(r, 'NG'):.2f}"
              f";  z0 at the switch (fit) = {r * switch(r, 'fit'):.2f}  (2 pi = {2 * math.pi:.2f}, 4 pi = {FOURPI:.2f})")
    print("x where the glueball branch reaches 4 pi: " + ", ".join(f"r={r}: {FOURPI / r:.2f}" for r in R_BAND))
    print()
    print("boxes:  beta  L   x     z_e (lo/fit/hi)        z_g(3.6)  branch      z0 band (lo/mid/hi)   z0 vs 4pi")
    table = {}
    for beta, Ls in BOXES.items():
        for L in Ls:
            x = L * ASIG[beta]
            zb, z0 = ze_band(x), z0_band(x)
            table[(beta, L)] = (x, zb, z0)
            if zb is None:
                print(f"        {beta}  {L:2d}  {x:4.2f}  small volume: no string prediction; predicted z0 > 2 z_e (no pair state)")
            else:
                print(f"        {beta}  {L:2d}  {x:4.2f}  {zb[0]:5.2f}/{zb[1]:5.2f}/{zb[2]:5.2f}   {3.6 * x:6.2f}   "
                      f"{z0[3]:10s}  {z0[0]:5.2f}/{z0[1]:5.2f}/{z0[2]:5.2f}    {'>' if z0[0] > FOURPI else ('<' if z0[2] < FOURPI else '~')} 4pi")
    print()
    print("pairs:  beta  L->2L   x->2x        G_e(fit)  c = 2z0(L)-z0(2L) (mid; range)   g0 (mid)   R = gain0/(2 G_e)")
    for beta, L in PAIRS:
        x1, zb1, z01 = table[(beta, L)]
        x2, zb2, z02 = table[(beta, 2 * L)]
        tag = " (optional run)" if (beta, L) == (2.5, 12) else ""
        if z02 is None:
            print(f"        {beta}  {L}->{2 * L}  no prediction")
            continue
        if z01 is None:
            print(f"        {beta}  {L:2d}->{2 * L:2d}  {x1:4.2f}->{x2:4.2f}   start in small volume: predicted c < 0 (g0 > 2),"
                  f" z0(2L) = {z02[1]:.1f} [{z02[0]:.1f}, {z02[2]:.1f}]{tag}")
            continue
        Ge = zb2[1] - 2 * zb1[1]
        c_mid = 2 * z01[1] - z02[1]
        c_lo, c_hi = 2 * z01[0] - z02[2], 2 * z01[2] - z02[0]
        g_mid = z02[1] / z01[1]
        R = (-c_mid) / (2 * Ge) if Ge > 0 else float("nan")
        print(f"        {beta}  {L:2d}->{2 * L:2d}  {x1:4.2f}->{x2:4.2f}   {Ge:6.2f}    {c_mid:6.2f} [{c_lo:6.2f}, {c_hi:5.2f}]"
              f"          {g_mid:4.2f}      {R:5.2f}{tag}")


if __name__ == "__main__":
    main()
