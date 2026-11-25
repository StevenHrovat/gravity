#!/usr/bin/env python3
# Checks for "GUID v7: From Inflation to the Standard Model, read through the axioms of DMP" (private draft, 2026-11-04).
# Two kinds: [A] analytic numbers recomputed here from standard inputs; [F] numbers quoted from run outputs, re-read from the files.
# Run: python3 docs/guid-v7/checks.py   (needs numpy, scipy). Exit code 0 when all pass.
import math, re, os, sys
import numpy as np
from scipy.optimize import brentq
from scipy.stats import chi2 as chi2dist, norm
BASE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'runs')  # run outputs as recorded
res = []
def check(tag, name, value, target, tol, unit=''):
    ok = abs(value - target) <= tol
    res.append((tag, name, ok))
    print(f"[{tag}] {'PASS' if ok else 'FAIL'}  {name}: {value:.6g}{unit} (paper {target:.6g}{unit}, tol {tol:g})")
def readfile(p):
    with open(os.path.join(BASE, p)) as f: return f.read()

alpha = 1/137.035999; me, mmu, mtau = 0.51099895, 105.6583755, 1776.86  # MeV
# --- A1 lepton balance (Koide)
Q = (me+mmu+mtau)/(math.sqrt(me)+math.sqrt(mmu)+math.sqrt(mtau))**2
check('A', 'lepton Koide Q (PDG 2022 m_tau 1776.86)', Q, 0.666661, 1.5e-6)
mtau24 = 1776.93
Q24 = (me+mmu+mtau24)/(math.sqrt(me)+math.sqrt(mmu)+math.sqrt(mtau24))**2
check('A', 'lepton Koide Q (PDG 2024 m_tau 1776.93)', Q24, 0.6666645, 1e-6)
# --- A2 neutrino balance with one negative root, normal ordering
d21, d31 = 7.42e-5, 2.51e-3  # eV^2
def kq(m1):
    m2, m3 = math.sqrt(m1*m1+d21), math.sqrt(m1*m1+d31)
    return (m1+m2+m3)/(-math.sqrt(m1)+math.sqrt(m2)+math.sqrt(m3))**2 - 2/3
m1 = brentq(kq, 1e-7, 5e-3); m2, m3 = math.sqrt(m1*m1+d21), math.sqrt(m1*m1+d31)
check('A', 'neutrino balance sum (meV)', 1e3*(m1+m2+m3), 59.2, 0.3)
check('A', 'lightest neutrino (meV)', 1e3*m1, 0.36, 0.05)
# --- A3 pi0 -> 2 gamma width
mpi0, fpi = 134.9768, 92.2
G = alpha**2*mpi0**3/(64*math.pi**3*fpi**2)*1e6  # eV
check('A', 'pi0 -> gamma gamma width (eV)', G, 7.76, 0.05)
# --- A4 pi -> e nu / mu nu at tree level
mpic = 139.57039
R = (me/mmu)**2*((mpic**2-me**2)/(mpic**2-mmu**2))**2
check('A', 'pi -> e nu / mu nu (tree)', R, 1.283e-4, 0.002e-4)
# --- A5 Das et al. electromagnetic pion splitting with the measured m_rho 775.26
mrho = 775.26
dm2 = 3*alpha*math.log(2)/(2*math.pi)*mrho**2
check('A', 'pi+ - pi0 (Das, MeV)', dm2/(2*137.27), 5.29, 0.03)
# --- A6 Witten-Veneziano: chi^(1/4) from eta', eta, K masses, f_pi 92.4
metap, meta, mK = 957.78, 547.862, 495.6
chi = 92.4**2/6*(metap**2+meta**2-2*mK**2)
check('A', 'Witten-Veneziano chi^(1/4) (MeV)', chi**0.25, 179.0, 2.0)
# --- A7 eta' from the lattice chi^(1/4) = 179.9 MeV
metap_pred = math.sqrt(6*179.9**4/92.4**2 - meta**2 + 2*mK**2)
check('A', "eta' from lattice chi (MeV)", metap_pred, 963.0, 6.0)
# --- A8 seesaw Yukawa at the switch scale and Davidson-Ibarra bound
v = 174.0; m3GeV = math.sqrt(d31)*1e-9
for M, y, eps in [(1e6, 4.1e-5, 1.0e-10), (1e7, 1.29e-4, 1.0e-9)]:
    check('A', f'seesaw y_nu at M={M:.0e} GeV', math.sqrt(m3GeV*M)/v, y, 0.05*y)
    check('A', f'Davidson-Ibarra eps_max at M={M:.0e} GeV', 3/(16*math.pi)*M*m3GeV/v**2, eps, 0.05*eps)
# --- A9 cogenesis: eps/beta0 for Omega_PBH/Omega_b = 5.36 at m_X 3.2e6 GeV
check('A', 'cogenesis eps/beta0 at m_X 3.2e6 GeV', 79/28*3.2e6/(5.36*0.93827), 1.8e6, 0.05e6)
# --- A10 horizon time for PBH masses (t = G M / c^3)
for Mg, t in [(1e17, 2.5e-22), (1e22, 2.5e-17)]:
    check('A', f'horizon time for {Mg:.0e} g (s)', 6.674e-8*Mg/2.998e10**3, t, 0.05*t)
# --- A11 dark energy per SN neutrino (rho_DE 3.33 keV/cm^3, n_nu 2.99e-9 /cm^3)
rhoDE = 0.69*3*(67.7/3.0857e19)**2/(8*math.pi*6.674e-8)*2.998e10**2/1.602e-12  # eV/cm^3
check('A', 'rho_DE today (eV/cm^3)', rhoDE, 3330, 40)
check('A', 'DE per SN neutrino, all unclumped (TeV)', rhoDE/2.99e-9/1e12, 1.12, 0.03)
check('A', '4 pi v (TeV)', 4*math.pi*246.22/1e3, 3.09, 0.01)
# --- A12 lattice ratios: physical references
check('A', '(Delta - N)/rho physical', (1232-938.9)/775.3, 0.379, 0.003)
check('A', 'Delta/N physical', 1232/938.9, 1.313, 0.003)
check('A', 'N/rho physical', 938.9/775.3, 1.21, 0.005)

# --- A13 Davidson-Ibarra shortfall: eps_max 1e-10..1e-9 against needed 5e-9..1.5e-8
check('A', 'DI shortfall, smallest (5e-9 / 1e-9)', 5e-9/1.0e-9, 5, 0.01)
check('A', 'DI shortfall, largest (1.5e-8 / 1e-10)', 1.5e-8/1.0e-10, 150, 0.1)
# --- A14 trial-adjusted significance of the leftover law (dchi2 7.35..9.09, 1 dof); Sidak over N tries
def sig(d, N=1):
    p = chi2dist.sf(d, 1); return norm.isf((1-(1-p)**N)/2)
check('A', 'local sigma, dchi2 7.35', sig(7.35), 2.7, 0.05)
check('A', 'local sigma, dchi2 9.09', sig(9.09), 3.0, 0.05)
check('A', 'sigma after 10 tries, dchi2 7.35', sig(7.35, 10), 1.8, 0.05)
check('A', 'sigma after 10 tries, dchi2 9.09', sig(9.09, 10), 2.2, 0.05)
check('A', 'sigma after 62 tries, dchi2 7.35', sig(7.35, 62), 1.0, 0.06)
check('A', 'sigma after 62 tries, dchi2 9.09', sig(9.09, 62), 1.5, 0.06)
# --- A15 S8 against DES Y6 3x2pt (LCDM 0.789 +- 0.012; wCDM 0.782 +- 0.021), theory error 0.012; S8 values from de/acts_growth.out (DES fit)
_g = readfile('de/acts_growth.out').split('SN set: des')[1]
def s8(name): return float(re.search(r'^' + re.escape(name) + r'\s+[\d.]+\s+[\d.]+\s+[\d.]+\s+[\d.]+\s+([\d.]+)', _g, re.M).group(1))
S8law, S8cpl, S8lcdm = s8('acts=SFR M_esc=1e10'), s8('CPL'), s8('LCDM')
th = 0.012
check('A', 'law S8 sigma vs DES LCDM, no theory error', (S8law-0.789)/0.012, 5.2, 0.1)
check('A', 'law S8 sigma vs DES LCDM, with theory error', (S8law-0.789)/math.hypot(0.012, th), 3.7, 0.05)
check('A', 'law S8 sigma vs DES wCDM', (S8law-0.782)/0.021, 3.3, 0.05)
def pen(S, c, e): v = e**2 + th**2; return ((S-c)**2 - (S8lcdm-c)**2)/v
check('A', 'law net dchi2 with S8 prior (LCDM value)', -8.48 + pen(S8law, 0.789, 0.012), 2.1, 0.1)
check('A', 'CPL net dchi2 with S8 prior (LCDM value)', -9.69 + pen(S8cpl, 0.789, 0.012), -4.2, 0.1)
check('A', 'law net dchi2 with S8 prior (wCDM value)', -8.48 + pen(S8law, 0.782, 0.021), -2.5, 0.1)
check('A', 'CPL net dchi2 with S8 prior (wCDM value)', -9.69 + pen(S8cpl, 0.782, 0.021), -6.5, 0.1)

# --- F: numbers from run outputs
def grab(text, pattern, group=1):
    m = re.search(pattern, text, re.M)
    if not m: raise SystemExit(f'pattern not found: {pattern}')
    return float(m.group(group))
co = readfile('de/cosmin.out')
check('F', 'CosMIn N_c, instant reheating', grab(co, r'instant reheating.*N_c=\s*([\d.]+)'), 12.884, 1e-3)
check('F', 'CosMIn N_c, Starobinsky T_reh 2.3e9', grab(co, r'T_reh 2\.3e9 GeV, no switch.*N_c=\s*([\d.]+)'), 11.895, 1e-3)
df = readfile('de/acts_datafit.out')
check('F', 'CPL dchi2 (Pantheon+)', grab(df, r'^CPL .*dchi2 ([-+\d.]+)'), -6.72, 0.01)
check('F', 'leftover law 1e10 dchi2 (Pantheon+)', grab(df, r'^acts=SFR M_esc=1e10\s*: .*dchi2 vs LCDM ([-+\d.]+)'), -7.35, 0.01)
dd = readfile('de/acts_datafit_des.out')
check('F', 'CPL dchi2 (DES)', grab(dd, r'^CPL .*dchi2 ([-+\d.]+)'), -9.69, 0.01)
check('F', 'leftover law 1e10 dchi2 (DES)', grab(dd, r'^acts=SFR M_esc=1e10\s*: .*dchi2 vs LCDM ([-+\d.]+)'), -8.48, 0.01)
ct = readfile('de/acts_controls.out')
check('F', 'control: leftovers alone', grab(ct, r'cumulative SFR alone.*dchi2 vs LCDM ([-+\d.]+)'), 56.10, 0.01)
check('F', 'control: unclumped alone', grab(ct, r'unclumped \(1e10\) alone.*dchi2 vs LCDM ([-+\d.]+)'), 70.00, 0.01)
rb = readfile('de/leftover_robust.out')
check('F', 'Madau-Fragos 1e10 dchi2 (Pantheon+)', grab(rb, r'^MF17 1e10\s+dchi2\s+([-+\d.]+)'), -7.95, 0.01)
check('F', 'held-out BAO+CMB -> SN, CPL (Pantheon+)', grab(rb, r'fit BAO\+CMB -> score SN: .*CPL ([-+\d.]+)'), 56.59, 0.01)
check('F', 'held-out BAO+CMB -> SN, law (Pantheon+)', grab(rb, r'fit BAO\+CMB -> score SN: .*acts=SFR M_esc=1e10 ([-+\d.]+)'), -3.03, 0.01)
gr = readfile('de/acts_growth.out')
check('F', 'S8 leftover law 1e10 (Pantheon+)', grab(gr, r'^acts=SFR M_esc=1e10\s+[\d.]+\s+[\d.]+\s+[\d.]+\s+[\d.]+\s+([\d.]+)'), 0.8517, 1e-4)
check('F', 'S8 LCDM (Pantheon+)', grab(gr, r'^LCDM\s+[\d.]+\s+[\d.]+\s+[\d.]+\s+[\d.]+\s+([\d.]+)'), 0.8183, 1e-4)
dr = readfile('de/acts_drain.out')
check('F', 'relic neutrinos as drivers (Pantheon+)', grab(dr, r'E0 \+ CnuB kinetic.*dchi2\s+([-+\d.]+)'), 261.67, 0.01)
wk = readfile('de/acts_weak.out')
check('F', 'fusion acts 1e10 (Pantheon+)', grab(wk, r'fusion x unclumped 1e10.*dchi2\s+([-+\d.]+)'), 72.03, 0.01)
mt = readfile('de/acts_matter.out')
check('F', 'acts uniform in matter, best (U 1e13, Pantheon+)', grab(mt, r'U M_esc=1e13.*dchi2\s+([-+\d.]+)'), 10.58, 0.01)
rp = readfile('bh/REPORT.md')
rows = [l.split('|') for l in rp.splitlines() if re.match(r'^\| 1e(1[7-9]|2[0-2]) ', l) and '†' not in l]
fs = [float(r[6].split('[')[0]) for r in rows]; om = [float(r[7].split('[')[0]) for r in rows]
check('F', 'hum f, allowed window, lowest (Hz)', min(fs), 0.022, 1e-4)
check('F', 'hum f, allowed window, highest (Hz)', max(fs), 0.74, 1e-3)
check('F', 'hum Omega h^2, allowed window, lowest', min(om), 1.6e-11, 1e-13)
check('F', 'hum Omega h^2, allowed window, highest', max(om), 1.8e-10, 1e-12)
check('F', 'S8 leftover law 1e10 (DES)', S8law, 0.8519, 1e-4)
check('F', 'S8 CPL (DES)', S8cpl, 0.8389, 1e-4)
tl = readfile('pt/timeline_check.out')
check('F', 'Starobinsky T_reh (GeV)', grab(tl, r'T_reh ~ ([\d.e+]+) GeV'), 2.3e9, 1e7)

n = len(res); npass = sum(ok for _, _, ok in res)
print(f"\n{npass}/{n} checks pass ({sum(1 for t,_,_ in res if t=='A')} analytic, {sum(1 for t,_,_ in res if t=='F')} from run outputs)")
sys.exit(0 if npass == n else 1)
