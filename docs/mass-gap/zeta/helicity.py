"""Exploration (not a test of DMP): where the 1/12 in the strong force's screening comes from, and why the gluon's ratio is 1/zeta(-1).

A charged particle of spin projection s_z in a constant magnetic field B has Landau levels E^2 = p_z^2 + eB(2n + 1) - 2 eB s_z (g = 2).
Its one-loop vacuum energy, in Schwinger's proper time with x = tau * eB, carries the level sum

    sum_n exp(-x (2n + 1 - 2 s_z)) = exp(2 x s_z) / (2 sinh x).

The term of this expansion that is linear in x gives the B^2 log(cutoff) term of the vacuum energy, i.e. the particle's contribution to the
running of the coupling (the one-loop beta function). This script computes that coefficient exactly and compares it with zeta(-1) and
with the Bernoulli polynomial B2(1/2 - s_z) (the Hurwitz zeta route: sum over levels at offset 1/2 - s_z).

Usage: python helicity.py
"""

import sympy as sp

x, s = sp.symbols("x s")
zeta_m1 = sp.zeta(-1)

print("zeta(-1) =", zeta_m1, "  B2(1/2) =", sp.bernoulli(2, sp.Rational(1, 2)))
series = sp.series(sp.exp(2 * x * s) / (2 * sp.sinh(x)), x, 0, 3).removeO()
coeff = sp.simplify(sp.expand(series).coeff(x, 1))
print("coefficient of x in exp(2 x s_z)/(2 sinh x):", coeff)
print("  equals s_z^2 + zeta(-1):", sp.simplify(coeff - (s ** 2 + zeta_m1)) == 0)
print("  equals B2(1/2 - s_z)/... :", sp.simplify(coeff - sp.bernoulli(2, sp.Rational(1, 2) - s)) == 0)

print("\nper helicity state: binding (spin) part s_z^2, screening (orbital) part zeta(-1) = -1/12; ratio s_z^2 / zeta(-1) = -12 s_z^2")
for sz in (0, sp.Rational(1, 2), 1, sp.Rational(3, 2), 2):
    c = coeff.subs(s, sz)
    ratio = sz ** 2 / zeta_m1 if sz != 0 else 0
    print(f"  s_z = {str(sz):>3}: coefficient {str(c):>6}   binding/screening = {ratio}")

# Rebuild the one-loop coefficient b0 = (11/3) C_A - (4/3) T_F n_f - (1/3) T_S n_s (standard normalisation, per unit group factor):
# count the field's states with their helicities, fermions negative, Faddeev-Popov ghosts (two real scalars) negative; overall factor 2.
per = lambda sz: coeff.subs(s, sz)
gauge = 2 * (per(1) + per(-1) + 2 * per(0) - 2 * per(0))       # 4 vector components: s_z = +1, -1, 0, 0; minus 2 ghosts
dirac = -2 * (2 * per(sp.Rational(1, 2)) + 2 * per(-sp.Rational(1, 2)))  # 4 states, fermion sign
weyl = -2 * (per(sp.Rational(1, 2)) + per(-sp.Rational(1, 2)))
complex_scalar = 2 * (2 * per(0))
print("\nrebuilt one-loop coefficients per unit group factor")
print("(standard b0 = (11/3) C_A - (4/3) T_F per Dirac - (2/3) T_F per Weyl - (1/3) T_S per complex scalar):")
print("  gauge field   :", sp.nsimplify(gauge))
print("  Dirac fermion :", sp.nsimplify(dirac))
print("  Weyl fermion  :", sp.nsimplify(weyl))
print("  complex scalar:", sp.nsimplify(complex_scalar))
print("\ngauge field: 11/3 = 4 * (1 + zeta(-1)):", sp.simplify(gauge - 4 * (1 + zeta_m1)) == 0)
