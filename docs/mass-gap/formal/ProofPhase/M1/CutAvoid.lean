/-
Proof phase, M1 tools (m1-tools): the deterministic half of Lemma NT′(a), the root bound of cut avoidance
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/NT-A.md`.
-/

import Mathlib

/-!
# Cut avoidance at the root: sign-corrected points in a cap

Elements of SU(2) are unit vectors of `ℝ⁴` (unit quaternions), and the angle of `g h⁻¹` is the angle between `g` and
`h` as vectors (`Re tr (g h⁻¹) = ⟪g, h⟫`). Changing the sign of an element is multiplication by the central `-1`.

* **`inner_ge_of_cap`**: unit vectors `a, b` in the cap `⟪·, u⟫ ≥ s ≥ 0` around a unit vector `u` satisfy
  `⟪a, b⟫ ≥ 2s² - 1` (so their angle is at most `2 arccos s`).
* **`signCorrect_inner_ge`**: if `|⟪x, u⟫| ≥ s`, the sign-corrected `σ x` (`σ = sign ⟪x, u⟫`) lies in that cap.
* **`cap_of_away`**: if every element of a finite family is at least `s` away (in inner product) from the hyperplane
  `u⊥`, the sign-corrected family has all pairwise inner products `≥ 2s² - 1`.
* **`angle_le_two_arccos`**: the corresponding angle bound `∠ ≤ 2 arccos s`.

The other half of NT′(a), the existence of such a `u` with `s = s_8 = 0.0983…` for 8 points of `S³` (a union bound with
the cap measure of `S³`), is proved on paper in `NT-A.md`; with it every star has a sign pattern whose corrected
relative angles are all `≤ 2 arccos s_8 = 168.7°`.
-/

open RealInnerProductSpace

noncomputable section

namespace ProofPhase.M1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Two unit vectors in a cap around `u` are at most twice the cap radius apart.** -/
theorem inner_ge_of_cap {a b u : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hu : ‖u‖ = 1) {s : ℝ} (hs : 0 ≤ s)
    (has : s ≤ ⟪a, u⟫) (hbs : s ≤ ⟪b, u⟫) : 2 * s ^ 2 - 1 ≤ ⟪a, b⟫ := by
  set α := ⟪a, u⟫; set β := ⟪b, u⟫
  set a' := a - α • u; set b' := b - β • u
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hua : ⟪u, a⟫ = α := real_inner_comm a u
  have hub : ⟪u, b⟫ = β := real_inner_comm b u
  have hab : ⟪a, b⟫ = α * β + ⟪a', b'⟫ := by
    simp only [a', b', inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, huu,
      hua, hub, RCLike.conj_to_real]
    ring
  have hna : ‖a'‖ ^ 2 = 1 - α ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [a', inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, huu,
      hua, RCLike.conj_to_real, real_inner_self_eq_norm_sq, ha]
    ring
  have hnb : ‖b'‖ ^ 2 = 1 - β ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [b', inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, huu,
      hub, RCLike.conj_to_real, real_inner_self_eq_norm_sq, hb]
    ring
  have hαβ : s ^ 2 ≤ α * β := by nlinarith
  have hA : ‖a'‖ ^ 2 ≤ 1 - s ^ 2 := by rw [hna]; nlinarith
  have hB : ‖b'‖ ^ 2 ≤ 1 - s ^ 2 := by rw [hnb]; nlinarith
  have hprod : ‖a'‖ * ‖b'‖ ≤ 1 - s ^ 2 := by
    have h1 : (‖a'‖ * ‖b'‖) ^ 2 ≤ (1 - s ^ 2) ^ 2 := by
      rw [mul_pow]
      calc ‖a'‖ ^ 2 * ‖b'‖ ^ 2 ≤ (1 - s ^ 2) * (1 - s ^ 2) :=
            mul_le_mul hA hB (sq_nonneg _) (le_trans (sq_nonneg _) hA)
        _ = (1 - s ^ 2) ^ 2 := by ring
    have h2 : 0 ≤ 1 - s ^ 2 := le_trans (sq_nonneg _) hA
    nlinarith [h1, mul_nonneg (norm_nonneg a') (norm_nonneg b'), h2]
  have hcs : -(‖a'‖ * ‖b'‖) ≤ ⟪a', b'⟫ := by
    have := abs_real_inner_le_norm a' b'
    linarith [neg_abs_le ⟪a', b'⟫]
  rw [hab]; linarith

/-- The sign that moves `x` to the side of `u`. -/
def capSign (x u : E) : ℝ := if 0 ≤ ⟪x, u⟫ then 1 else -1

theorem capSign_sq (x u : E) : capSign x u * capSign x u = 1 := by
  unfold capSign; split_ifs <;> norm_num

theorem norm_capSign_smul (x u : E) : ‖capSign x u • x‖ = ‖x‖ := by
  rw [norm_smul]; unfold capSign; split_ifs <;> simp

/-- **Sign correction lands in the cap.** -/
theorem signCorrect_inner_ge {x u : E} {s : ℝ} (hx : s ≤ |⟪x, u⟫|) : s ≤ ⟪capSign x u • x, u⟫ := by
  rw [inner_smul_left]; unfold capSign
  split_ifs with h
  · simpa [abs_of_nonneg h] using hx
  · have h' : ⟪x, u⟫ < 0 := lt_of_not_ge h
    simp [abs_of_neg h'] at hx ⊢; linarith

/-- **The deterministic half of NT′(a).** A finite family of unit vectors, each at least `s` away from `u⊥`: the
sign-corrected family has all pairwise inner products `≥ 2s² - 1`. -/
theorem cap_of_away {ι : Type*} (x : ι → E) (hx : ∀ i, ‖x i‖ = 1) {u : E} (hu : ‖u‖ = 1) {s : ℝ} (hs : 0 ≤ s)
    (haway : ∀ i, s ≤ |⟪x i, u⟫|) (i j : ι) :
    2 * s ^ 2 - 1 ≤ ⟪capSign (x i) u • x i, capSign (x j) u • x j⟫ :=
  inner_ge_of_cap ((norm_capSign_smul _ _).trans (hx i)) ((norm_capSign_smul _ _).trans (hx j)) hu hs
    (signCorrect_inner_ge (haway i)) (signCorrect_inner_ge (haway j))

/-- **The angle form:** pairwise angles of the corrected family are at most `2 arccos s` (`0 ≤ s ≤ 1`). -/
theorem angle_le_two_arccos {ι : Type*} (x : ι → E) (hx : ∀ i, ‖x i‖ = 1) {u : E} (hu : ‖u‖ = 1) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (haway : ∀ i, s ≤ |⟪x i, u⟫|) (i j : ι) :
    InnerProductGeometry.angle (capSign (x i) u • x i) (capSign (x j) u • x j) ≤ 2 * Real.arccos s := by
  have hni := (norm_capSign_smul (x i) u).trans (hx i)
  have hnj := (norm_capSign_smul (x j) u).trans (hx j)
  unfold InnerProductGeometry.angle
  rw [hni, hnj, mul_one, div_one]
  have hcos : Real.cos (2 * Real.arccos s) = 2 * s ^ 2 - 1 := by
    rw [Real.cos_two_mul, Real.cos_arccos (by linarith) hs1]
  have hrange : 2 * Real.arccos s ≤ Real.pi := by
    have := Real.arccos_le_pi_div_two.2 hs; linarith
  have h0 : 0 ≤ 2 * Real.arccos s := by have := Real.arccos_nonneg s; linarith
  calc Real.arccos ⟪capSign (x i) u • x i, capSign (x j) u • x j⟫
      ≤ Real.arccos (Real.cos (2 * Real.arccos s)) := by
        apply Real.arccos_le_arccos
        rw [hcos]; exact cap_of_away x hx hu hs haway i j
    _ = 2 * Real.arccos s := Real.arccos_cos h0 hrange

end ProofPhase.M1
