/-
GRH attempt, Lee-Yang route, step c: the Lee-Yang mechanism in its smallest complete case. The two-site lemma,
Asano's contraction, and the circle theorem for the three-spin ferromagnetic Ising chain (2026-11-23). Released under
Apache 2.0.

Note: `docs/rh-guide/grh/LEE-YANG.md`.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# The Lee-Yang circle theorem, smallest cases, via Asano contraction

**The mechanism** (Lee-Yang 1952; Asano 1970). A ferromagnetic Ising system with fugacity variables `z_i` (one per
spin, `z = e^{-2h}` for a magnetic field `h`) has a partition function that is multi-affine in the `z_i`. Each bond
`(i, j)` with coupling `J ≥ 0` contributes the two-site factor `1 + a z_i + a z_j + z_i z_j`, `a = e^{-2J} ∈ [0, 1]`.

1. **Local positivity gives local zero-freeness** (`lee_yang_pair`): for real `|a| ≤ 1` the two-site factor does not
   vanish when both `|z_i|, |z_j| < 1`. The proof is one identity:
   `|1 + a z|^2 - |a + z|^2 = (1 - a^2)(1 - |z|^2)`.
2. **Asano contraction keeps zero-freeness** (`asano`): if `A + B z + C w + D z w ≠ 0` whenever `|z|, |w| < 1`, then
   `A + D z ≠ 0` whenever `|z| < 1`. Merging two copies of a spin variable (`z w ↦ z`, keeping only the terms where
   both or neither appear) is how the bonds are glued into a lattice.
3. **Symmetry puts the zeros on the circle** (`ising3_zeros_on_circle`): the glued partition function is non-zero for
   `|z| < 1` and satisfies `Z(z) = z^n Z(1/z)` (spin flip), so it is also non-zero for `|z| > 1`. Every zero has
   `|z| = 1`: the magnetic field is purely imaginary.

Steps 1-3 for the three-spin chain (two bonds, one contraction) are proved here. The general lattice is the same
argument by induction over bonds (classical, not formalized).

**Why it matters for the GRH route** (LEE-YANG.md): the structure is "zero-free on one side, plus a mirror". It is
the same architecture as the final step of the RH Lean proof (`Claim.strip`: no zeros right of 1/2, plus the
functional equation). Lee-Yang supplies the one-sided zero-freeness from *local factors that are themselves
zero-free on the open polydisc* (step 1), glued by contraction (step 2).
-/

open Complex

noncomputable section

namespace ProofPhase.GRH

/-- The two-site factor of a ferromagnetic bond, `1 + a z + a w + z w`. -/
def pairPoly (a : ℝ) (z w : ℂ) : ℂ := 1 + a * z + a * w + z * w

/-- The identity behind the Lee-Yang lemma: `|1 + a z|^2 - |a + z|^2 = (1 - a^2)(1 - |z|^2)`. -/
theorem lee_yang_identity (a : ℝ) (z : ℂ) :
    ‖1 + (a : ℂ) * z‖ ^ 2 - ‖(a : ℂ) + z‖ ^ 2 = (1 - a ^ 2) * (1 - ‖z‖ ^ 2) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

/-- **Lee-Yang, two sites.** A ferromagnetic bond factor has no zero with both variables in the open unit disc. -/
theorem lee_yang_pair {a : ℝ} (ha : |a| ≤ 1) {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    pairPoly a z w ≠ 0 := by
  intro h0
  have hsplit : pairPoly a z w = (1 + (a : ℂ) * z) + w * ((a : ℂ) + z) := by unfold pairPoly; ring
  rw [hsplit] at h0
  have hid := lee_yang_identity a z
  have ha2 : 0 ≤ 1 - a ^ 2 := by nlinarith [abs_nonneg a, sq_abs a]
  have hz2 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hge : ‖(a : ℂ) + z‖ ^ 2 ≤ ‖1 + (a : ℂ) * z‖ ^ 2 := by nlinarith [mul_nonneg ha2 hz2]
  have heq : ‖1 + (a : ℂ) * z‖ = ‖w‖ * ‖(a : ℂ) + z‖ := by
    rw [← norm_mul, show 1 + (a : ℂ) * z = -(w * ((a : ℂ) + z)) by linear_combination h0, norm_neg]
  by_cases hz0 : (a : ℂ) + z = 0
  · -- then `1 + a z = 0` too, which forces `a^2 = 1` and `|z| = 1`
    have h1 : 1 + (a : ℂ) * z = 0 := by rw [hz0, mul_zero] at h0; simpa using h0
    have hzz : z = -(a : ℂ) := by linear_combination hz0
    rw [hzz] at hz
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs] at hz
    rw [hzz] at h1
    have : (1 : ℂ) - (a : ℂ) ^ 2 = 0 := by linear_combination h1
    have ha1 : (1 : ℝ) - a ^ 2 = 0 := by exact_mod_cast this
    nlinarith [sq_abs a, abs_nonneg a]
  · have hpos : 0 < ‖(a : ℂ) + z‖ := norm_pos_iff.mpr hz0
    have : ‖(a : ℂ) + z‖ ≤ ‖w‖ * ‖(a : ℂ) + z‖ := by
      rw [← heq]
      have h1 := sq_le_sq' (by nlinarith [norm_nonneg ((a : ℂ) + z), norm_nonneg (1 + (a : ℂ) * z)]) hge
      nlinarith [norm_nonneg ((a : ℂ) + z), norm_nonneg (1 + (a : ℂ) * z)]
    have : 1 ≤ ‖w‖ := by
      by_contra hlt; push Not at hlt
      nlinarith
    linarith

/-- From zero-freeness on the bidisc: the "second variable" bound `|C + D z| ≤ |A + B z|` for `|z| < 1`. -/
theorem asano_bound {A B C D : ℂ}
    (h : ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → A + B * z + C * w + D * z * w ≠ 0) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖C + D * z‖ ≤ ‖A + B * z‖ := by
  by_contra hlt
  push Not at hlt
  have hne : C + D * z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hlt; exact absurd hlt (not_lt.mpr (norm_nonneg _))
  set w : ℂ := -(A + B * z) / (C + D * z) with hw
  have hwn : ‖w‖ < 1 := by
    rw [hw, norm_div, norm_neg, div_lt_one (norm_pos_iff.mpr hne)]; exact hlt
  have hw2 : w * (C + D * z) = -(A + B * z) := by rw [hw, div_mul_cancel₀ _ hne]
  apply h z w hz hwn
  linear_combination hw2

/-- **Asano contraction.** If `A + B z + C w + D z w` has no zero with `|z|, |w| < 1`, then `A + D z` has no zero with
`|z| < 1`. -/
theorem asano {A B C D : ℂ} (h : ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → A + B * z + C * w + D * z * w ≠ 0)
    {z : ℂ} (hz : ‖z‖ < 1) : A + D * z ≠ 0 := by
  have hA : A ≠ 0 := by simpa using h 0 0 (by simp) (by simp)
  have hswap : ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → A + C * z + B * w + D * z * w ≠ 0 := fun z w hz hw => by
    have := h w z hw hz
    intro h0; apply this; linear_combination h0
  -- for real `0 ≤ r < 1`: `|D| r ≤ |A|`, by the parallelogram law at `±r`
  have key : ∀ r : ℝ, 0 ≤ r → r < 1 → ‖D‖ * r ≤ ‖A‖ := by
    intro r hr0 hr1
    have hrn : ‖(r : ℂ)‖ < 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hr0]; exact hr1
    have hrn' : ‖-(r : ℂ)‖ < 1 := by rw [norm_neg]; exact hrn
    have p1 := asano_bound h hrn
    have p2 := asano_bound h hrn'
    have q1 := asano_bound hswap hrn
    have q2 := asano_bound hswap hrn'
    have par : ∀ x y : ℂ, ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := fun x y => by
      have := parallelogram_law_with_norm ℝ x y
      nlinarith [this]
    have e1 := par C (D * r); have e2 := par A (B * r); have e3 := par B (D * r); have e4 := par A (C * r)
    simp only [mul_neg, ← sub_eq_add_neg] at p2 q2
    have s1 : ‖C + D * r‖ ^ 2 + ‖C - D * r‖ ^ 2 ≤ ‖A + B * r‖ ^ 2 + ‖A - B * r‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) p1 2
      have := pow_le_pow_left₀ (norm_nonneg _) p2 2
      linarith
    have s2 : ‖B + D * r‖ ^ 2 + ‖B - D * r‖ ^ 2 ≤ ‖A + C * r‖ ^ 2 + ‖A - C * r‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) q1 2
      have := pow_le_pow_left₀ (norm_nonneg _) q2 2
      linarith
    have nr : ∀ X : ℂ, ‖X * (r : ℂ)‖ = ‖X‖ * r := fun X => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
    rw [e1, e2, nr, nr] at s1
    rw [e3, e4, nr, nr] at s2
    have hr2 : 0 ≤ 1 - r ^ 2 := by nlinarith
    have hint := mul_nonneg (add_nonneg (sq_nonneg ‖B‖) (sq_nonneg ‖C‖)) hr2
    have hsq : (‖D‖ * r) ^ 2 ≤ ‖A‖ ^ 2 := by nlinarith [hint, s1, s2]
    by_contra hgt
    push Not at hgt
    nlinarith [norm_nonneg A, hsq, hgt]
  intro h0
  have hAD : ‖A‖ = ‖D‖ * ‖z‖ := by
    rw [← norm_mul, show A = -(D * z) by linear_combination h0, norm_neg]
  by_cases hD : D = 0
  · rw [hD, norm_zero, zero_mul, norm_eq_zero] at hAD; exact hA hAD
  · obtain ⟨r, hzr, hr1⟩ := exists_between hz
    have h1 := key r ((norm_nonneg z).trans hzr.le) hr1
    have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
    have : ‖D‖ * ‖z‖ < ‖D‖ * r := mul_lt_mul_of_pos_left hzr hDpos
    have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
    linarith

/-- The two-bond contraction: gluing the bonds `(1, 2)` and `(2', 3)` along `2 = 2'`. -/
def chain3 (a b : ℝ) (z₁ z₂ z₃ : ℂ) : ℂ :=
  (1 + (a : ℂ) * z₁) * (1 + (b : ℂ) * z₃) + z₂ * ((a : ℂ) + z₁) * ((b : ℂ) + z₃)

/-- **Lee-Yang for the three-spin chain, multi-variable form**: no zero with all three `|z_i| < 1`. -/
theorem chain3_ne_zero {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) {z₁ z₂ z₃ : ℂ} (h₁ : ‖z₁‖ < 1)
    (h₂ : ‖z₂‖ < 1) (h₃ : ‖z₃‖ < 1) : chain3 a b z₁ z₂ z₃ ≠ 0 := by
  have hprod : ∀ x y : ℂ, ‖x‖ < 1 → ‖y‖ < 1 →
      (1 + (a : ℂ) * z₁) * (1 + (b : ℂ) * z₃) + ((a : ℂ) + z₁) * (1 + (b : ℂ) * z₃) * x +
        (1 + (a : ℂ) * z₁) * ((b : ℂ) + z₃) * y + ((a : ℂ) + z₁) * ((b : ℂ) + z₃) * x * y ≠ 0 := by
    intro x y hx hy h0
    have e : pairPoly a z₁ x * pairPoly b y z₃ =
        (1 + (a : ℂ) * z₁) * (1 + (b : ℂ) * z₃) + ((a : ℂ) + z₁) * (1 + (b : ℂ) * z₃) * x +
          (1 + (a : ℂ) * z₁) * ((b : ℂ) + z₃) * y + ((a : ℂ) + z₁) * ((b : ℂ) + z₃) * x * y := by
      unfold pairPoly; ring
    rw [← e] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact lee_yang_pair ha h₁ hx h
    · exact lee_yang_pair hb hy h₃ h
  have := asano hprod h₂
  unfold chain3
  intro h0; apply this; linear_combination h0

/-- The partition function of the three-spin ferromagnetic chain in the common fugacity `z`. -/
def ising3 (a b : ℝ) (z : ℂ) : ℂ := chain3 a b z z z

/-- Spin-flip symmetry: `z^3 Z(1/z) = Z(z)`. -/
theorem ising3_flip (a b : ℝ) {z : ℂ} (hz : z ≠ 0) : z ^ 3 * ising3 a b z⁻¹ = ising3 a b z := by
  unfold ising3 chain3
  field_simp
  ring

/-- **The Lee-Yang circle theorem for the three-spin ferromagnetic chain**: every zero of the partition function in
the fugacity lies on the unit circle (purely imaginary magnetic field). -/
theorem ising3_zeros_on_circle {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) {z : ℂ} (h0 : ising3 a b z = 0) :
    ‖z‖ = 1 := by
  rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
  · exact absurd h0 (chain3_ne_zero ha hb hlt hlt hlt)
  · exact heq
  · exfalso
    have hz : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hgt; linarith
    have hinv : ‖z⁻¹‖ < 1 := by
      rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hgt
    have := ising3_flip a b hz
    rw [h0] at this
    have h1 : ising3 a b z⁻¹ = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hz
      · exact h
    exact chain3_ne_zero ha hb hinv hinv hinv h1

/-- **The same for one bond**: `1 + 2 a z + z^2` has all its zeros on the unit circle when `|a| ≤ 1`. -/
theorem pair_zeros_on_circle {a : ℝ} (ha : |a| ≤ 1) {z : ℂ} (h0 : pairPoly a z z = 0) : ‖z‖ = 1 := by
  rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
  · exact absurd h0 (lee_yang_pair ha hlt hlt)
  · exact heq
  · exfalso
    have hz : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hgt; linarith
    have hinv : ‖z⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hgt
    have hflip : z ^ 2 * pairPoly a z⁻¹ z⁻¹ = pairPoly a z z := by unfold pairPoly; field_simp; ring
    rw [h0] at hflip
    rcases mul_eq_zero.mp hflip with h | h
    · exact hz (pow_eq_zero_iff (by norm_num) |>.mp h)
    · exact lee_yang_pair ha hinv hinv h

end ProofPhase.GRH
