"""One event, three leftovers (Steven 2026-11-01 13:53Z-13:57Z: 'Then we have our path to go on').

The v7 switch (a lagging first-order transition at T_V, dark U(1) kinetically mixed with B, slow decay Gamma/H*) leaves:
  1. PBH dark matter from the lagging patches (Ai & Xie 2605.11332 slow-decay estimates, no accretion, valid 8 <~ beta/H <~ 18),
  2. a gravitational-wave hum (envelope template, diluted by the early matter era; our estimate from slow_decay_rescue.py),
  3. the matter surplus from the slow, out-of-equilibrium decay of the switch field (needs a mirror preference eps per decay;
     sphalerons active since T_reh >> 130 GeV; conversion 28/79; m_X taken = T_V within a factor of a few).
Both PBH and any surplus made at the switch are diluted equally, so Omega_DM/Omega_b = 5.4 constrains the event only.
Detector reach (min Omega h^2 near their best frequency) and PBH bounds are rough, from memory; see notes.
"""
import numpy as np

def gmax(x): return 0.004 * 10 ** (0.07 * (12 - x))

ETA = 8.7e-11          # n_B / s today
DETECTORS = [("LISA", 1e-4, 1e-1, 1e-13), ("DECIGO", 1e-2, 10, 1e-15), ("BBO", 1e-2, 10, 1e-16),
             ("ET", 3, 1e3, 1e-12), ("CE", 5, 1e3, 1e-12), ("LVK O5", 10, 500, 1e-10)]
# PBH window for f = 1 (from memory): evaporation (INTEGRAL/COMPTEL/511 keV) below ~1e17 g; microlensing (HSC) above ~1e22 g
WINDOW = (1e17, 1e22)

def envelope(fr, fp, beta):
    r = fr / fp
    return 1.67e-5 * (1 / beta) ** 2 * 0.077 * 3.8 * r ** 2.8 / (1 + 2.8 * r ** 3.8)

def event(M, gfrac):
    TV = 1e6 * np.sqrt(1e20 / M)
    xs = np.linspace(4, 24, 20001)
    f = 2 * 10 ** (0.3 * (12 - xs)) * (TV / 1e6) * np.sqrt(gfrac * gmax(xs))
    x = xs[np.argmin(abs(np.log(f)))]
    g = gfrac * gmax(x)
    Treh = 0.64 * np.sqrt(g) * TV
    fpk = 16.5e-6 * 0.23 * x * (TV / 100) * g ** (1 / 6) / 0.64
    Om = 1.67e-5 * (1 / x) ** 2 * 0.077 * g ** (2 / 3)
    eps = ETA * 4 * TV / (3 * Treh) * 79 / 28
    D = 0.75 * TV / Treh
    det = []
    for name, lo, hi, sens in DETECTORS:
        fr = np.logspace(np.log10(lo), np.log10(hi), 200)
        peak = envelope(fr, fpk, x).max() * g ** (2 / 3)
        if peak > sens:
            det.append(f"{name}({peak/sens:.0e}x)")
    return dict(M=M, TV=TV, x=x, g=g, ok=8 <= x <= 18, Treh=Treh, fpk=fpk, Om=Om, eps=eps, D=D, det=det)

if __name__ == "__main__":
    print(__doc__)
    print(f"{'M [g]':>8} {'Gam/H*':>8} {'T_V GeV':>9} {'beta/H':>7} {'T_reh':>8} {'dilut':>6} {'eps need':>9} {'hum f_pk Hz':>12} {'Om h2 pk':>9}  in window / fit range / detectors")
    for M in (1e17, 3e17, 1e18, 1e19, 1e20, 1e21, 1e22):
        for gf in (1.0, 0.1):
            e = event(M, gf)
            win = WINDOW[0] <= M <= WINDOW[1]
            print(f"{M:8.0e} {e['g']:8.1e} {e['TV']:9.1e} {e['x']:7.2f} {e['Treh']:8.1e} {e['D']:6.0f} {e['eps']:9.1e} {e['fpk']:12.2e} {e['Om']:9.1e}  "
                  f"{'yes' if win else 'NO '} / {'ok' if e['ok'] else 'OUTSIDE'} / {' '.join(e['det']) or 'none'}")
    print("\nCross-check chain: a PBH mass M fixes T_V = 1e6 GeV (1e20 g / M)^0.5; f = 1 fixes beta/H given Gamma/H*;")
    print("together they fix the hum peak (frequency ~ beta/H * T_V) and the eps that makes Omega_DM/Omega_b = 5.4.")
