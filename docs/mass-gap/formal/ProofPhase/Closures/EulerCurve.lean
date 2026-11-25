/-
Closures round (2026-11-24): the Euler ledger of one given curve; its counts are the curve's, by construction.
Released under Apache 2.0.

Paper: Part VII, VII.3.6 care point (claim VII.3.6d); `docs/paper/OPEN-CLAIMS-CLOSURES.md`.
-/

import ProofPhase.Unified.BSDAPI

/-!
# The Euler ledger of one given curve

`API.BSD.EulerData` takes the counts `N_p` as a bare sequence, with Hasse as an `External` input; that the sequence is
the counts of one curve was documented, not checked (claim VII.3.6d). Here the ledger is built **from** an integral
Weierstrass curve `W`:

* `curveCount W n` is Mathlib's number of points (`Nat.card` of the point type, the point at infinity included) of `W`
  read mod the `n`-th prime (`reduceMod`);
* `ofCurve W hH` is the `EulerData` with these counts; Hasse stays the named `External` input, now about `W`'s counts;
* `ofCurve_N` (S): its counts are `W`'s, by construction (`rfl`);
* `ofCurve_N_good` (S): at every prime of good reduction they equal the computed count of `Arsenal.BSD` (`count`, which
  runs), through `count_reduceMod`;
* `ofCurve_fac_good` (S): at such a prime the step factor is `count / p`;
* `E32Euler` and `E32Euler_N` (S): the curve `y² = x³ − x` (conductor 32), with its counts at every odd prime.

**What is not done here.** Mathlib (`WeierstrassCurve.LFunction`) defines the local factor at a prime through the
minimal model over the completion and its reduction over the residue field. Matching that factor's coefficient with
`curveCount` at a good prime needs: an integral model with unit discriminant at `p` is minimal there, its reduction is the
reduction of Mathlib's chosen minimal model up to isomorphism, and the residue field of the completion is `ZMod p`
(`IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv`). It is the classical definition of `a_p`
(Silverman, AEC, C.16) and is not stated here. At a prime of bad reduction `curveCount` counts the nonsingular points,
the convention of `EulerData`'s Hasse input.
-/

noncomputable section

namespace ProofPhase.Closures.EulerCurve

open Arsenal.BSD ProofPhase.API ProofPhase.API.BSD

/-- The `n`-th prime. -/
abbrev pr (n : ℕ) : ℕ := Nat.nth Nat.Prime n

instance (n : ℕ) : Fact (pr n).Prime := ⟨Nat.prime_nth_prime n⟩

instance (n : ℕ) : NeZero (pr n) := ⟨(Nat.prime_nth_prime n).ne_zero⟩

/-- **The counts of one curve**: Mathlib's number of points of `W` mod the `n`-th prime. -/
def curveCount (W : WeierstrassCurve ℤ) (n : ℕ) : ℤ := Nat.card (Pts (reduceMod W (pr n)))

/-- **The Euler ledger of `W`**: the counts are `W`'s; Hasse for these counts is the named external input. -/
def ofCurve (W : WeierstrassCurve ℤ)
    (hH : External "Hasse 1933-36: |p + 1 - N_p| <= 2 sqrt p for every elliptic curve over F_p (nonsingular points at bad p)"
      (∀ n, ((pr n : ℝ) + 1 - curveCount W n) ^ 2 ≤ 4 * (pr n : ℝ))) : EulerData where
  N := curveCount W
  hasse := hH

variable (W : WeierstrassCurve ℤ)
  (hH : External "Hasse 1933-36: |p + 1 - N_p| <= 2 sqrt p for every elliptic curve over F_p (nonsingular points at bad p)"
    (∀ n, ((pr n : ℝ) + 1 - curveCount W n) ^ 2 ≤ 4 * (pr n : ℝ)))

/-- **The counts of the ledger are the curve's** (S), by construction. -/
theorem ofCurve_N (n : ℕ) : (ofCurve W hH).N n = curveCount W n := rfl

/-- **At a prime of good reduction the count is the computed one** (S): Mathlib's count of `W` mod `p` is
`Arsenal.BSD.count`, which runs. -/
theorem ofCurve_N_good (n : ℕ) (hΔ : ((W.Δ : ℤ) : ZMod (pr n)) ≠ 0) :
    (ofCurve W hH).N n = count (reduceMod W (pr n)) := by
  rw [ofCurve_N, curveCount, count_reduceMod W (pr n) hΔ]

/-- **The step factor at a good prime is the curve's** (S): `N_p / p` with `N_p` the computed count. -/
theorem ofCurve_fac_good (n : ℕ) (hΔ : ((W.Δ : ℤ) : ZMod (pr n)) ≠ 0) :
    (ofCurve W hH).fac n = (count (reduceMod W (pr n)) : ℝ) / EulerData.p n := by
  have h := ofCurve_N_good W hH n hΔ
  simp only [EulerData.fac, EulerData.a]
  rw [h]
  push_cast
  ring

/-- **The ledger of `y² = x³ − x`** (conductor 32), with Hasse for its counts as the named input. -/
def E32Euler
    (hH : External "Hasse 1933-36: |p + 1 - N_p| <= 2 sqrt p for every elliptic curve over F_p (nonsingular points at bad p)"
      (∀ n, ((pr n : ℝ) + 1 - curveCount E32Z n) ^ 2 ≤ 4 * (pr n : ℝ))) : EulerData :=
  ofCurve E32Z hH

/-- **Its counts at every odd prime are the computed ones** (S). -/
theorem E32Euler_N
    (hH : External "Hasse 1933-36: |p + 1 - N_p| <= 2 sqrt p for every elliptic curve over F_p (nonsingular points at bad p)"
      (∀ n, ((pr n : ℝ) + 1 - curveCount E32Z n) ^ 2 ≤ 4 * (pr n : ℝ)))
    (n : ℕ) (h2 : pr n ≠ 2) : (E32Euler hH).N n = count (reduceMod E32Z (pr n)) := by
  show curveCount E32Z n = _
  rw [curveCount, count_E32 (pr n) h2]

end ProofPhase.Closures.EulerCurve
