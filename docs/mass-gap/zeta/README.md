# ζ(−1) in the strong force: an exploration (2026-11-21)

Status: an exploration the owner asked for ("still seems like an interesting thing to poke"). It reproduces known physics and standard
mathematics; it is not a test of DMP and claims nothing new about Yang–Mills.

## The question

The one-loop coefficient that makes the strong force grow at long distances is 11/3 per unit of the gluons' self-charge, and it splits
into a binding part +4 (the gluon's spin, anti-screening) and a screening part −1/3 (its charge moving in orbits, as in ordinary
diamagnetism): the Nielsen–Hughes decomposition. The ratio is −12. The owner asked whether that is related to ζ(−1) = −1/12.

## What the algebra says (`helicity.py`, exact, sympy)

A charged particle with spin projection s_z in a magnetic field has Landau levels E² = p_z² + eB(2n + 1) − 2eB s_z. Summing their
zero-point energies (in Schwinger's proper time, x = τ·eB) gives the level sum exp(2x s_z)/(2 sinh x); its term linear in x is the
particle's contribution to the running coupling. Its coefficient is, exactly,

  **s_z² + ζ(−1) = B₂(1/2 − s_z)**   (B₂ the second Bernoulli polynomial).

So per spin state the binding part is s_z² and the screening part is ζ(−1). The ratio is s_z²/ζ(−1) = −12 s_z²: **exactly 1/ζ(−1) for
spin 1**, −3 for spin 1/2, 0 for spin 0. Counting a field's states (vector field: s_z = ±1, 0, 0, minus two ghosts; fermions negative)
rebuilds the textbook coefficients exactly: gauge field 11/3, Dirac fermion −4/3, Weyl fermion −2/3, complex scalar −1/3. In one line:

  **11/3 = 4·(1 + ζ(−1))**: the 11 of asymptotic freedom is 12 + 12·ζ(−1).

**Why the 12s meet.** Both are the same Bernoulli number: the 1/12 is the x² term of x/sinh x (equivalently B₂(1/2) = −1/12), the number
that also makes ζ(−1) = −1/12. Both come from adding up the zero-point energies of an evenly spaced ladder of modes (Landau levels here,
string vibrations below). The ratio −12 is not a condition every theory must meet (quarks give −3 and theories with quarks are
asymptotically free); it is what a spin-1 carrier gives.

## The same ζ(−1) in the flux tube (to be measured)

A confining flux tube closed around a periodic box of length L vibrates, and the zero-point sum of its modes is (d − 2)(2π/L)·ζ(−1):
E(L) = σL − π/(3L) in four dimensions, the coefficient π/3 = −4π·ζ(−1) (the Lüscher term). The measurement with this project's GPU code
is pre-registered in [`PREREG-LUSCHER.md`](PREREG-LUSCHER.md) (SU(2), β = 2.3, five box sizes; fit `luscher.py`; runs queued after the
main GPU queue by `queue_luscher.ps1`).

## In DMP's words (a reading)

The screening third is what the gluons share with charged payload-like matter (it has the sign of ordinary electromagnetic screening);
the binding four is what only a self-charged spin-1 carrier has. ζ(−1) is the regularised "cost of all zero-point modes" of a ladder, and
it appears both in the screening of IM and in the vibration energy of the IM flux tube. That is a shared piece of mathematics, not a
mechanism, and no number here is predicted by DMP.
