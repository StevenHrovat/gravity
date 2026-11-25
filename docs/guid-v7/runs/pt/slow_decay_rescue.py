"""Slow-decay rescue (Ai & Xie 2605.11332, analytic estimates, k = 0.9 k_max, valid 8 <~ beta/H <~ 18):
condition Gamma/H* <~ 0.004 * 10^(0.07 (12 - x)); no accretion: M ~ 1e20 g (1e6 GeV/T_V)^2, f ~ 2*10^(0.3(12-x)) (T_V/1e6)(Gamma/H*)^0.5;
max accretion: M ~ 2e20 g (1e6/T_V)^2 (H*/Gamma), f ~ 4*10^(0.3(12-x)) (T_V/1e6)(H*/Gamma)^0.5.
GW from the switch diluted by the early matter era: Omega x (Gamma/H*)^(2/3), frequency x (Gamma/H*)^(1/6)/0.64 (our estimate)."""
import numpy as np
def gmax(x): return 0.004*10**(0.07*(12-x))
print("No accretion, Gamma/H* at its maximum (longest-allowed fast end) and 10x below:")
for M in (1e17, 1e19, 1e22):
    TV = 1e6*np.sqrt(1e20/M)
    for gf in (1.0, 0.1):
        # solve f = 1 for x
        xs = np.linspace(4, 24, 20001)
        f = 2*10**(0.3*(12-xs))*(TV/1e6)*np.sqrt(gf*gmax(xs))
        x = xs[np.argmin(abs(np.log(f)))]
        g = gf*gmax(x); Treh = 0.64*np.sqrt(g)*TV
        print(f"  M {M:.0e} g: T_V {TV:.1e} GeV, Gamma/H* {g:.1e}: beta/H = {x:.2f}{' (outside 8..18 fit range)' if not 8 <= x <= 18 else ''}; T_reh {Treh:.1e} GeV; "
              f"hum diluted x{g**(2/3):.1e}, frequency x{g**(1/6)/0.64:.2f}; f changes x2 per beta/H shift of {np.log10(2)/0.3:.2f}")
print("\nMax accretion (M grows to the horizon mass at the end of the matter era):")
for M in (1e17, 1e19, 1e22):
    for g in (1e-3, 1e-4, 1e-5):
        TV = 1e6*np.sqrt(2e20/(M*g))
        xs = np.linspace(4, 24, 20001)
        f = 4*10**(0.3*(12-xs))*(TV/1e6)/np.sqrt(g)
        x = xs[np.argmin(abs(np.log(f)))]
        ok = g <= gmax(x)
        print(f"  M {M:.0e} g, Gamma/H* {g:.0e}: T_V {TV:.1e} GeV, beta/H = {x:.2f}; allowed (Gamma/H* <= {gmax(x):.1e}): {ok}")
