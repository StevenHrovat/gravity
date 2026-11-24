/-
Grand Unified, the consequence from the G0 link (gu-scoping, round 2): charge quantisation from compactness
(2026-11-24). Released under Apache 2.0.

Note: `docs/unified/GU-SCOPING.md`, section 8.
-/

import Mathlib
import ProofPhase.General.GUCentre

/-!
# Charge quantisation from a compact U(1)

Every item is **classical** mathematics (the characters of the circle group; Pontryagin duality `Circle^ = ℤ`),
formalised here. Mathlib has the Fourier basis of `AddCircle` and Parseval's identity but, as far as checked, no
classification of the continuous characters of the circle; it is proved here from Parseval.

**1. Characters of the circle (`addCircle_char`, `circle_char`).** Every continuous map `χ : AddCircle T → Circle`
with `χ (x + y) = χ x * χ y` is `x ↦ toCircle (n • x)` for one integer `n`; every continuous group homomorphism
`Circle →* Circle` is `z ↦ z ^ n`. The integer is unique (`addCircle_char_unique`, `circle_char_unique`). Proof: the
Fourier coefficients of `χ` satisfy `c_n = (e_{-n}(y) χ(y)) c_n` for every `y` (translation invariance of Haar
measure); by Parseval not all `c_n` vanish (`Σ |c_n|² = ∫ |χ|² = 1`); a nonzero one forces `χ = e_n`.

**2. The contrast: a line does not quantise (`line_char`, `line_char_periodic_iff`).** On `ℝ` every real `a` gives
a continuous character `t ↦ e^{i a t}`; it factors through the circle `ℝ / 2πℤ` iff `a` is an integer. Compactness
of the phase group is exactly what forces integer charge.

**3. The centre sees the charge mod N (`centre_char_mod`).** For an `N`-th root of unity `ω` on the circle (the
centre of SU(N), `General/Centre.lean`), `ω ^ n = ω ^ (n mod N)`: the centre measures the charge modulo `N`.

**4. The chain to thirds (`g0_charge_thirds`).** Input: a field on which the hypercharge U(1) acts by a continuous
character `χ` of the circle, with SU(3) triality `t` and SU(2) duality `d`, and invariant under the Z_6 generator
`(ω, -1, ζ)` (the matter assignment, explicit hypothesis). Output: `χ z = z ^ q` for an integer `q` (derived, from
compactness), `6 ∣ 2t + 3d + q`, and every component has electric charge `Q = (3 s + q)/6` with `Q + t/3 ∈ ℤ`
(the thirds, from the input).
-/

open Complex MeasureTheory AddCircle Real

noncomputable section

namespace ProofPhase.General

namespace GU

section AddCircleChar

variable {T : ℝ} [hT : Fact (0 < T)]

/-- Translation: the `n`-th Fourier coefficient of a character picks up the factor `e_{-n}(y) χ(y)`. -/
theorem fourierCoeff_char_shift (χ : AddCircle T → Circle) (ha : ∀ x y, χ (x + y) = χ x * χ y) (n : ℤ)
    (y : AddCircle T) :
    fourierCoeff (fun x => (χ x : ℂ)) n =
      (fourier (-n) y * (χ y : ℂ)) * fourierCoeff (fun x => (χ x : ℂ)) n := by
  unfold fourierCoeff
  rw [← integral_const_mul]
  rw [← integral_add_left_eq_self (μ := haarAddCircle)
    (fun t => fourier (-n) t • (χ t : ℂ)) y]
  congr 1
  ext x
  simp only [smul_eq_mul, fourier_apply, smul_add, toCircle_add, Circle.coe_mul, ha]
  ring

/-- **Characters of the additive circle.** A continuous `χ : AddCircle T → Circle` with
`χ (x + y) = χ x * χ y` is `x ↦ toCircle (n • x)` for some integer `n`. -/
theorem addCircle_char (χ : AddCircle T → Circle) (hc : Continuous χ) (ha : ∀ x y, χ (x + y) = χ x * χ y) :
    ∃ n : ℤ, ∀ x, χ x = toCircle (n • x) := by
  let g : C(AddCircle T, ℂ) := ⟨fun x => (χ x : ℂ), continuous_subtype_val.comp hc⟩
  have hg : ∀ m, fourierCoeff g m = fourierCoeff (fun x => (χ x : ℂ)) m := fun _ => rfl
  -- some Fourier coefficient is nonzero (Parseval)
  obtain ⟨n, hn⟩ : ∃ n, fourierCoeff (fun x => (χ x : ℂ)) n ≠ 0 := by
    by_contra h
    push Not at h
    have H := hasSum_sq_fourierCoeff (ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ g)
    simp only [fourierCoeff_toLp, hg, h, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at H
    have h1 : ∫ t : AddCircle T, ‖(ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ g) t‖ ^ 2 ∂haarAddCircle = 1 := by
      have : ∫ t : AddCircle T, ‖(ContinuousMap.toLp (E := ℂ) 2 haarAddCircle ℂ g) t‖ ^ 2 ∂haarAddCircle =
          ∫ t : AddCircle T, ‖g t‖ ^ 2 ∂haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) haarAddCircle g] with t ht
        rw [ht]
      rw [this]
      simp [g, Circle.norm_coe]
    rw [h1] at H
    exact one_ne_zero (H.unique hasSum_zero)
  refine ⟨n, fun y => ?_⟩
  have hs := fourierCoeff_char_shift χ ha n y
  set c := fourierCoeff (fun x => (χ x : ℂ)) n
  have ha1 : fourier (-n) y * (χ y : ℂ) = 1 := by
    have : (fourier (-n) y * (χ y : ℂ) - 1) * c = 0 := by linear_combination -hs
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hn
  have hf1 : fourier (-n) y * fourier n y = 1 := by
    rw [← fourier_add, neg_add_cancel, fourier_zero]
  have hne : fourier (-n) y ≠ 0 := left_ne_zero_of_mul_eq_one hf1
  apply Circle.ext
  rw [← fourier_apply]
  exact mul_left_cancel₀ hne (ha1.trans hf1.symm)

/-- The integer of a character of the additive circle is unique. -/
theorem addCircle_char_unique (n m : ℤ) (h : ∀ x : AddCircle T, toCircle (n • x) = toCircle (m • x)) :
    n = m := by
  have e : (fourier n : C(AddCircle T, ℂ)) = fourier m := by
    ext x; simp only [fourier_apply, h]
  have := congrFun (fourierCoeff_fourier (T := T) n) n
  rw [e, fourierCoeff_fourier, Pi.single_apply, Pi.single_apply] at this
  by_contra hnm
  simp [hnm] at this

end AddCircleChar

/-- `toCircle` on `AddCircle (2π)` is `Circle.exp`. -/
theorem toCircle_two_pi (t : ℝ) : @toCircle (2 * π) (t : AddCircle (2 * π)) = Circle.exp t := by
  rw [toCircle_apply_mk]
  congr 1
  field_simp

/-- **Characters of the circle group.** Every continuous group homomorphism `Circle →* Circle` is `z ↦ z ^ n`
for an integer `n`: every charge under a compact U(1) is an integer multiple of one unit. -/
theorem circle_char (χ : Circle →* Circle) (hc : Continuous χ) : ∃ n : ℤ, ∀ z, χ z = z ^ n := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  obtain ⟨n, hn⟩ := addCircle_char (T := 2 * π) (fun x => χ (toCircle x)) (hc.comp continuous_toCircle)
    (fun x y => by rw [toCircle_add, map_mul])
  refine ⟨n, fun z => ?_⟩
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  have := hn (t : AddCircle (2 * π))
  rwa [toCircle_two_pi, toCircle_zsmul, toCircle_two_pi] at this

/-- The charge is unique: `z ^ n = z ^ m` for all `z` on the circle forces `n = m`. -/
theorem circle_char_unique (n m : ℤ) (h : ∀ z : Circle, z ^ n = z ^ m) : n = m := by
  have : Fact (0 < 2 * π) := ⟨two_pi_pos⟩
  exact addCircle_char_unique (T := 2 * π) n m (fun x => by rw [toCircle_zsmul, toCircle_zsmul, h])

/-- **The line does not quantise.** For every real `a`, `t ↦ e^{i a t}` is a continuous character of `ℝ`. -/
theorem line_char (a : ℝ) :
    Continuous (fun t : ℝ => Circle.exp (a * t)) ∧
      ∀ s t : ℝ, Circle.exp (a * (s + t)) = Circle.exp (a * s) * Circle.exp (a * t) :=
  ⟨Circle.exp.continuous.comp (continuous_const.mul continuous_id),
    fun s t => by rw [mul_add, Circle.exp_add]⟩

/-- **Compactness is what quantises.** The character `t ↦ e^{i a t}` of `ℝ` is `2π`-periodic (factors through
the circle `ℝ / 2πℤ`) iff `a` is an integer. -/
theorem line_char_periodic_iff (a : ℝ) :
    (∀ t : ℝ, Circle.exp (a * (t + 2 * π)) = Circle.exp (a * t)) ↔ ∃ n : ℤ, a = n := by
  constructor
  · intro h
    have h0 := h 0
    rw [zero_add, mul_zero] at h0
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h0
    refine ⟨m, ?_⟩
    have hpi : (2 * π) ≠ 0 := by positivity
    have : (a - m) * (2 * π) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' hpi
  · rintro ⟨n, rfl⟩ t
    exact Circle.exp_eq_exp.mpr ⟨n, by ring⟩

/-- **The centre measures the charge mod N.** For `ω ^ N = 1` (an element of the SU(N) centre on the circle),
`ω ^ n = ω ^ (n % N)`. -/
theorem centre_char_mod (ω : Circle) (N : ℕ) (hω : ω ^ N = 1) (n : ℤ) : ω ^ n = ω ^ (n % (N : ℤ)) := by
  conv_lhs => rw [← Int.mul_ediv_add_emod n N]
  rw [zpow_add, zpow_mul, zpow_natCast, hω, one_zpow, one_mul]

/-- The sixth root `ζ = e^{2πi/6}` as a point of the circle. -/
def zetaC : Circle := Circle.exp (π / 3)

theorem coe_zetaC : (zetaC : ℂ) = zeta6 := by
  rw [zetaC, Circle.coe_exp, zeta6]
  congr 1
  push_cast
  ring

/-- **The chain from the G0 link to thirds.** Input (explicit): a field on which hypercharge acts by a continuous
character `χ` of the circle, with SU(3) triality `t` and SU(2) duality `d`, invariant under the Z_6 generator
`(ω, -1, ζ)`. Derived from compactness: `χ = z ↦ z ^ q` with `q` an integer. Then `6 ∣ 2t + 3d + q`, and every
component (`2 T_3 = s`, `s ≡ d mod 2`) has `Q = (3 s + q)/6` with `Q + t/3` an integer. -/
theorem g0_charge_thirds (χ : Circle →* Circle) (hc : Continuous χ) (t d : ℕ)
    (hinv : (zeta6 ^ 2) ^ t * (zeta6 ^ 3) ^ d * (χ zetaC : ℂ) = 1) :
    ∃ q : ℤ, (∀ z, χ z = z ^ q) ∧ (6 : ℤ) ∣ 2 * t + 3 * d + q ∧
      ∀ s : ℤ, 2 ∣ s - d → ∃ n : ℤ, ((3 * s + q : ℤ) : ℚ) / 6 + (t : ℚ) / 3 = n := by
  obtain ⟨q, hq⟩ := circle_char χ hc
  have hinv' : centrePhase (zeta6 ^ 2) (zeta6 ^ 3) zeta6 ⟨t, d, q⟩ = 1 := by
    rw [hq, Circle.coe_zpow, coe_zetaC] at hinv
    exact hinv
  have h6 := (gen_trivial_iff ⟨t, d, q⟩).mp hinv'
  exact ⟨q, hq, h6, fun s hs => charge_thirds t d q s h6 hs⟩

end GU

end ProofPhase.General
