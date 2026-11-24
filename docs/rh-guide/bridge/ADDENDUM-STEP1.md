# Bridge addendum, step 1: the sign argument and the OS link

Private working note, 2026-11-23. Follows `BRIDGE.md` (committed); that file is not changed. Marks as there:
**[Lean-bridge]** = proved in `docs/mass-gap/formal/ProofPhase/Bridge/`, standard axioms only (`axioms-step1.sh`,
`axioms-step1.log`); **[classical]**, **[reading]**, **[open]** as in the guide.

## 1. The sign argument (BRIDGE.md 1.4), now in Lean

Module `Bridge/Poles.lean`, 8 theorems **[Lean-bridge]**.

- **Abstract lemma** (`residue_nonneg_of_re_nonneg`). Suppose a function has non-negative real part at real points
  just to the right of x0, and is g(s) + R/(s - x0) there, with g continuous at x0. Then R >= 0. As sigma comes down
  to x0, R/(sigma - x0) goes to minus infinity when R < 0, while g stays bounded.
- **For positive transforms** (`laplace_residue_nonneg`, `lseries_residue_nonneg`). The Laplace transform of any
  measure, and an L-series with non-negative coefficients, have non-negative real part at real points. So neither can
  have a pole of negative residue approached from the right. The Laplace version needs no hypothesis on the measure.
- **Ray forms** (`laplace_ray_poles`, `landau_ray_poles`). Suppose the transform converges somewhere. Suppose also
  that around every real point x > theta right of which it converges, it equals g(s) + R/(s - x), with g holomorphic
  on a disc and R <= 0 (R = 0 is the pole-free case). Then it converges on all of (theta, inf), hence is holomorphic
  on Re s > theta. The would-be poles of negative residue are not there.

**What this does for the RH setting.** BRIDGE.md 1.4 computed that a real zero beta in (theta, 1) of L(chi, s) would
be a pole of the Mellin transform of the non-negative function C x^theta - G(x). Its residue would be
-m/(beta(1 - beta)) < 0, with m the multiplicity, read off the explicit formula for the weight Lambda(n)(x/n - 1).
`laplace_ray_poles` turns this into: under a one-sided bound, real zeros right of theta are excluded together with
the complex ones.

**Not formalized:** the identification of that Mellin transform with -L'/L(s)/(s(s - 1)) plus the elementary terms,
and the residue computation. Mathlib has no Mellin-transform form of the explicit formula for L'/L. **[classical]**

## 2. The OS link, stated with the spectral measure as a hypothesis

Module `Bridge/OSLink.lean`, 5 theorems, imports `ProofPhase.M1.UVTVOS` (unchanged) **[Lean-bridge]**.

- **The hypothesis that replaces the spectral theorem** (`TransferSpectralRep R g`): a finite measure mu on [0, 1]
  with Q g (tau^n g) = int lambda^n dmu(lambda) for all n. For the transfer operator `RPData.T`, which is bounded,
  symmetric, positive and a contraction, this is the spectral measure of Phi g. That is the spectral theorem
  **[classical]**, which Mathlib does not have.
- `moment_gap_iff`: for a finite measure on [0, 1], (exists C, forall n, int lambda^n dmu <= C e^{-mn}) holds iff
  mu puts no mass on (e^{-m}, 1].
- `hdec_iff_spectral`: given such representations for all block observables, the hypothesis `hdec` of
  `RPData.gap_of_RP` holds **iff** every block observable's spectral measure lives on [0, e^{-m}]. Equivalently,
  H = -log T >= m on the block observables.
- `gap_of_RP_spectral`: `gap_of_RP` with `hdec` replaced by that spectral condition. This is a real Lean composition
  with the OS layer, not a match by name.
- `hdec_iff_energy`: the same in the energy variable E = -log lambda, through `spectral_gap_iff_nat`, for a
  representation Q g (tau^n g) = int e^{-nE} dnu(E). The two forms differ only by a possible atom of mu at lambda = 0
  (the kernel of T), which affects n = 0 only. The moment form is the one the spectral theorem delivers directly.

**What remains open on this link:** constructing `TransferSpectralRep` from `RPData`. That needs the spectral theorem
for bounded self-adjoint operators on a real Hilbert space, at least in the form of a moment representation.
Equivalently, one needs the Hausdorff moment theorem applied to the positive-definite sequence n -> Q g (tau^n g).
**[open]** in Mathlib.

## 3. Build note

Both modules build with 0 warnings of their own. Building `OSLink` also rebuilds the existing
`ProofPhase/Interface/SpectralUpgrade.lean`, which prints Mathlib deprecation warnings (`ContinuousLinearMap.mul_apply`
and `one_apply`); that file is not part of this step and was not touched.
