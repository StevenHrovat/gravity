#!/usr/bin/env python3
"""Mirror tool checks (cheap): the s = 2 / s = -1 identity and its family, the mirror data at s = 1 / s = 0 that
fix the constants of Weil's form, and the effective-string form of the one-box condition F_e(L) > log mu_4.
Run from anywhere: python3 docs/rh-guide/mirror.py > docs/rh-guide/mirror.log
"""
import mpmath as mp

mp.mp.dps = 40

print("1. The identity and its family: (2 pi)^(2k) = 2 (-1)^k (2k-1)! zeta(2k) / zeta(1-2k)  (functional equation at s = 2k)")
for k in range(1, 5):
    lhs = (2 * mp.pi) ** (2 * k)
    rhs = 2 * (-1) ** k * mp.factorial(2 * k - 1) * mp.zeta(2 * k) / mp.zeta(1 - 2 * k)
    print(f"  k = {k}: (2 pi)^{2*k} = {mp.nstr(lhs, 20)}   rhs = {mp.nstr(rhs, 20)}   zeta(1-2k) = {mp.nstr(mp.zeta(1-2*k), 12)}")
print(f"  k = 1 written as the owner's identity: 8 pi^2 = {mp.nstr(8 * mp.pi**2, 20)},"
      f" -4 zeta(2)/zeta(-1) = {mp.nstr(-4 * mp.zeta(2) / mp.zeta(-1), 20)}")

print("\n2. The mirror pair that Weil's form actually uses: s = 1 (pole, residue 1, constant gamma) and s = 0")
z0 = mp.zeta(0)
dz0 = mp.diff(mp.zeta, 0)
print(f"  zeta(0) = {mp.nstr(z0, 15)};  zeta'(0) = {mp.nstr(dz0, 15)};  -(1/2) log(2 pi) = {mp.nstr(-mp.log(2*mp.pi)/2, 15)}")
print(f"  zeta'(0)/zeta(0) = {mp.nstr(dz0 / z0, 15)} = log(2 pi) = {mp.nstr(mp.log(2*mp.pi), 15)}")
print(f"  Weil's real-place constant log(pi) + gamma = {mp.nstr(mp.log(mp.pi) + mp.euler, 15)}"
      f"  (gamma = Laurent constant of zeta at s = 1; log pi from pi^(-s/2))")

print("\n3. One-box condition in the effective-string regime (closed flux loop of length L, d = 4, Arvis ground state):")
print("   F_e(L) ~ L E_0(L) = sigma L^2 sqrt(1 - pi (d-2) / (3 sigma L^2)); Luescher term alone: sigma L^2 - pi (d-2)/6")
lm4 = mp.mpf("1.91")
c = mp.pi * 2 / 3
x_arvis = (c + mp.sqrt(c**2 + 4 * lm4**2)) / 2
x_lue = lm4 + mp.pi * 2 / 6
print(f"  Luescher shift pi (d-2)/6 = {mp.nstr(mp.pi*2/6, 6)} (from (d-2) (2 pi / L) zeta(-1) per unit time, times L)")
print(f"  F_e > {lm4} needs sigma L^2 > {mp.nstr(x_lue, 5)} (Luescher), > {mp.nstr(x_arvis, 5)} (Arvis):"
      f"  L sqrt(sigma) > {mp.nstr(mp.sqrt(x_lue), 4)} / {mp.nstr(mp.sqrt(x_arvis), 4)}")
print(f"  Arvis tachyon point sigma L^2 = pi (d-2)/3 = {mp.nstr(c, 5)} (L sqrt(sigma) = {mp.nstr(mp.sqrt(c), 4)}):"
      " the effective string is not valid below it")
