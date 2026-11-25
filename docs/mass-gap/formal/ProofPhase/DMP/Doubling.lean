/-
Proof phase, cycle 5, workstream 5 (the DMP-native line): the doubling law for two act numbers, abstract form
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5e-dmp/NOTE.md`; blueprint v4 draft, section 6
(`weak-coupling/proof-phase/c4-fable/BLUEPRINT-v4-DRAFT.md`).
-/

import Mathlib

/-!
# The doubling law for two act numbers (abstract; pure real analysis)

Boxes of side `s n = 2ⁿ L₀`. For each box two **act numbers**: the vacuum act number `z n = s n · E₀(s n)` (box side times
the energy gap of the centre-neutral sector) and the flux act number `ze n = s n · E_e(s n)`. Everything in this file is
about sequences of real numbers; the objects are attached in `ProofPhase.DMP.VacuumAct`.

**The hypotheses of blueprint v4, section 6.2, exactly.**
* **D-S** (start): `ζ ≤ z 0 ∧ ζe ≤ ze 0`.
* **D-T** (`DoublingLaw`): for every `n`, above both thresholds (`ζ ≤ z n`, `ζe ≤ ze n`) the vacuum act number at least
  doubles up to a loss, `2 (1 − η n) z n ≤ z (n+1)`, and the flux threshold persists, `ζe ≤ ze (n+1)`.
* **loss** (`AdmissibleLoss`): `0 ≤ η n ≤ ½`, `Σ η < ∞`. (The bound `½` keeps the vacuum threshold: `2(1 − η) ≥ 1`; any
  finitely many larger losses are absorbed by starting later, `floor_of_eventual_start`.)
* **D-ID** (`BoxGaps`): the objects exist: for every box a downward-closed "gap at least `E`" predicate whose supremum is
  attained when positive. On the lattice this is a theorem (`ProofPhase.DMP.latticeBoxGaps`); in the continuum (spacing
  first at fixed physical box) it is the open identification-and-existence input.

**Proved.**
* `floor_of_doubling`: D-S ∧ D-T ∧ loss ⇒ `E n = z n / s n ≥ (ζ / L₀) · exp(−2 Σ η) > 0` for all `n`.
  `BoxGaps.floor`: the same for the gap predicates (D-ID ∧ D-S ∧ D-T ⇒ every dyadic box has gap `≥ m`).
* `floor_of_eventual_start`: every box has a positive gap (finite boxes do, on the lattice by Perron-Frobenius) and D-S ∧ D-T
  hold from some box `N` on ⇒ a uniform floor for all `n`. `crossing_of_growth`: a start `a > 0` and a uniform growth `δ`
  of `z` on the stretch `[a, ζ)` (no fixed point of the step map there) reach the threshold in finitely many doublings.
  Together: inward reach (small boxes, `z > 0`) + a crossing on a compact stretch + D-T above it ⇒ the floor.
* Unit tests. `frozen_violates_doubling`: a constant act number (free massless field, `z₀ = 2π` at every `L`) satisfies D-T
  only with `η ≥ ½` at every step, never with a summable loss. `bounded_violates_doubling`: no bounded act number (the
  lattice photon `2L·arsinh(sin(π/L)) < 2π`, an infrared fixed point of Banks-Zaks type) satisfies D-S ∧ D-T ∧ loss.
* **What D-T is** (`doubling_of_antitone_gap`): if `E n` is antitone with `E n ≥ m > 0` (a gap approached from above along
  the dyadic boxes), then D-T holds with equality for `η n = 1 − E(n+1)/E n`, which is nonnegative and summable. So, in this
  monotone case, D-T with a summable loss *is* the gap restricted to dyadic boxes: the doubling law relabels the infrared
  statement, it does not weaken it. The factor `2` is the doubling of the extent and nothing else (`z = s · E`).

**Claim discipline.** Every theorem here is elementary real analysis. Substantive content: none about Yang-Mills; the
content is the exact form of the hypotheses (the two thresholds, the summable loss, the bound `½`) and the two unit tests,
which show the hypotheses cannot be met by a scale-invariant act number.
-/

open Filter Topology Finset

noncomputable section

namespace ProofPhase.DMP

/-! ## The loss bound -/

/-- `exp(−2x) ≤ 1 − x` on `[0, ½]`. -/
theorem exp_neg_two_mul_le_one_sub {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1 / 2) : Real.exp (-2 * x) ≤ 1 - x := by
  have he : 2 * x + 1 ≤ Real.exp (2 * x) := Real.add_one_le_exp (2 * x)
  have key : 1 ≤ (1 - x) * Real.exp (2 * x) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - x) (by linarith : (0 : ℝ) ≤ Real.exp (2 * x) - (2 * x + 1)),
      mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]
  have hmul : Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by rw [← Real.exp_add]; simp
  calc Real.exp (-2 * x) = Real.exp (-2 * x) * 1 := by ring
    _ ≤ Real.exp (-2 * x) * ((1 - x) * Real.exp (2 * x)) := mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
    _ = 1 - x := by rw [mul_comm (1 - x), ← mul_assoc, hmul, one_mul]

/-- `∏_{k<n} (1 − η k) ≥ exp(−2 Σ_{k<n} η k)` for `0 ≤ η ≤ ½`. -/
theorem exp_le_prod_one_sub {η : ℕ → ℝ} (h0 : ∀ n, 0 ≤ η n) (h1 : ∀ n, η n ≤ 1 / 2) (n : ℕ) :
    Real.exp (-2 * ∑ k ∈ range n, η k) ≤ ∏ k ∈ range n, (1 - η k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, prod_range_succ, mul_add, Real.exp_add]
    exact mul_le_mul ih (exp_neg_two_mul_le_one_sub (h0 n) (h1 n)) (Real.exp_pos _).le
      ((Real.exp_pos _).le.trans ih)

/-! ## The hypotheses -/

/-- **The loss of a doubling law**: `0 ≤ η n ≤ ½` and `Σ η < ∞`. -/
def AdmissibleLoss (η : ℕ → ℝ) : Prop := (∀ n, 0 ≤ η n) ∧ (∀ n, η n ≤ 1 / 2) ∧ Summable η

/-- **D-T, the doubling law** (blueprint v4, section 6.2): above both thresholds the vacuum act number at least doubles up
to the loss `η n`, and the flux threshold persists. `z n`, `ze n` are the act numbers of the box `2ⁿ L₀`. -/
def DoublingLaw (z ze : ℕ → ℝ) (ζ ζe : ℝ) (η : ℕ → ℝ) : Prop :=
  ∀ n, ζ ≤ z n → ζe ≤ ze n → 2 * (1 - η n) * z n ≤ z (n + 1) ∧ ζe ≤ ze (n + 1)

/-- **D-S, the start**: both act numbers above their thresholds in the first box. -/
def DoublingStart (z ze : ℕ → ℝ) (ζ ζe : ℝ) : Prop := ζ ≤ z 0 ∧ ζe ≤ ze 0

/-! ## The doubling theorem -/

/-- The invariant: thresholds kept, and `z n ≥ z 0 · 2ⁿ ∏_{k<n} (1 − η k)`. -/
theorem doubling_invariant {z ze η : ℕ → ℝ} {ζ ζe : ℝ} (hζ : 0 ≤ ζ) (hη : AdmissibleLoss η)
    (hS : DoublingStart z ze ζ ζe) (hT : DoublingLaw z ze ζ ζe η) :
    ∀ n, ζ ≤ z n ∧ ζe ≤ ze n ∧ z 0 * (2 ^ n * ∏ k ∈ range n, (1 - η k)) ≤ z n := by
  intro n
  induction n with
  | zero => exact ⟨hS.1, hS.2, by simp⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨d1, d2⟩ := hT n h1 h2
    have hf : 1 ≤ 2 * (1 - η n) := by linarith [hη.2.1 n]
    have hz : 0 ≤ z n := hζ.trans h1
    refine ⟨?_, d2, ?_⟩
    · nlinarith
    · calc z 0 * (2 ^ (n + 1) * ∏ k ∈ range (n + 1), (1 - η k))
          = (z 0 * (2 ^ n * ∏ k ∈ range n, (1 - η k))) * (2 * (1 - η n)) := by
            rw [pow_succ, prod_range_succ]; ring
        _ ≤ z n * (2 * (1 - η n)) := mul_le_mul_of_nonneg_right h3 (by linarith)
        _ = 2 * (1 - η n) * z n := by ring
        _ ≤ z (n + 1) := d1

/-- **The doubling theorem (D-S ∧ D-T ⇒ floor).** With boxes of side `2ⁿ L₀`, every box has
`z n / (2ⁿ L₀) ≥ (ζ / L₀) · exp(−2 Σ η) > 0`: the energy gap `E n = z n / s n` is bounded below uniformly in `n`. -/
theorem floor_of_doubling {z ze η : ℕ → ℝ} {ζ ζe L₀ : ℝ} (hL₀ : 0 < L₀) (hζ : 0 < ζ) (hη : AdmissibleLoss η)
    (hS : DoublingStart z ze ζ ζe) (hT : DoublingLaw z ze ζ ζe η) (n : ℕ) :
    ζ / L₀ * Real.exp (-2 * ∑' k, η k) ≤ z n / (2 ^ n * L₀) := by
  obtain ⟨-, -, h3⟩ := doubling_invariant hζ.le hη hS hT n
  have hsum : ∑ k ∈ range n, η k ≤ ∑' k, η k :=
    hη.2.2.sum_le_tsum (range n) (fun k _ => hη.1 k)
  have hprod : Real.exp (-2 * ∑' k, η k) ≤ ∏ k ∈ range n, (1 - η k) :=
    (Real.exp_le_exp.2 (by linarith)).trans (exp_le_prod_one_sub hη.1 hη.2.1 n)
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hz0 : ζ * (2 ^ n * Real.exp (-2 * ∑' k, η k)) ≤ z n :=
    calc ζ * (2 ^ n * Real.exp (-2 * ∑' k, η k)) ≤ z 0 * (2 ^ n * ∏ k ∈ range n, (1 - η k)) :=
          mul_le_mul hS.1 (mul_le_mul_of_nonneg_left hprod h2n.le) (by positivity) (hζ.le.trans hS.1)
      _ ≤ z n := h3
  rw [le_div_iff₀ (by positivity)]
  calc ζ / L₀ * Real.exp (-2 * ∑' k, η k) * (2 ^ n * L₀) = ζ * (2 ^ n * Real.exp (-2 * ∑' k, η k)) := by
        field_simp
    _ ≤ z n := hz0

/-- The floor is positive. -/
theorem floor_pos {η : ℕ → ℝ} {ζ L₀ : ℝ} (hL₀ : 0 < L₀) (hζ : 0 < ζ) : 0 < ζ / L₀ * Real.exp (-2 * ∑' k, η k) := by
  positivity

/-! ## Starting later; reaching the threshold -/

/-- **Floor with a late start.** If every box has a positive act number, and D-S and D-T hold for the boxes from `N` on,
then the gaps of all dyadic boxes have one positive lower bound. -/
theorem floor_of_eventual_start {z ze η : ℕ → ℝ} {ζ ζe L₀ : ℝ} (hL₀ : 0 < L₀) (hζ : 0 < ζ) (hpos : ∀ n, 0 < z n)
    (N : ℕ) (hη : AdmissibleLoss η) (hS : DoublingStart (fun k => z (N + k)) (fun k => ze (N + k)) ζ ζe)
    (hT : DoublingLaw (fun k => z (N + k)) (fun k => ze (N + k)) ζ ζe η) :
    ∃ m : ℝ, 0 < m ∧ ∀ n, m ≤ z n / (2 ^ n * L₀) := by
  set m₁ := ζ / (2 ^ N * L₀) * Real.exp (-2 * ∑' k, η k) with hm₁
  have hL' : 0 < 2 ^ N * L₀ := by positivity
  have hm₁pos : 0 < m₁ := floor_pos hL' hζ
  set m₂ := (range (N + 1)).inf' ⟨0, by simp⟩ (fun n => z n / (2 ^ n * L₀)) with hm₂
  have hm₂pos : 0 < m₂ := (Finset.lt_inf'_iff _).2 fun n _ => div_pos (hpos n) (by positivity)
  refine ⟨min m₁ m₂, lt_min hm₁pos hm₂pos, fun n => ?_⟩
  rcases lt_or_ge n N with h | h
  · exact (min_le_right _ _).trans (Finset.inf'_le _ (by simp; omega))
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    refine (min_le_left _ _).trans ?_
    have := floor_of_doubling hL' hζ hη hS hT k
    calc m₁ ≤ z (N + k) / (2 ^ k * (2 ^ N * L₀)) := this
      _ = z (N + k) / (2 ^ (N + k) * L₀) := by rw [pow_add]; ring_nf

/-- **Crossing from inward reach** (r3-monotone's reach, for the vacuum act number). A start `a ≤ z 0` and a uniform
growth `z (n+1) ≥ z n + δ` whenever `z n ∈ [a, ζ)` reach `ζ` after finitely many doublings. On a compact stretch of a
continuous step map without fixed point, such a `δ` exists (compactness); a fixed point in the stretch (Banks-Zaks) kills it. -/
theorem crossing_of_growth {z : ℕ → ℝ} {a ζ δ : ℝ} (hδ : 0 < δ) (h0 : a ≤ z 0)
    (hg : ∀ n, a ≤ z n → z n < ζ → z n + δ ≤ z (n + 1)) : ∃ N, ζ ≤ z N := by
  by_contra hne
  push Not at hne
  have hlin : ∀ n, a ≤ z n ∧ z 0 + n * δ ≤ z n := by
    intro n
    induction n with
    | zero => exact ⟨h0, by simp⟩
    | succ n ih =>
      have := hg n ih.1 (hne n)
      refine ⟨by linarith, ?_⟩
      push_cast; linarith [ih.2]
  obtain ⟨n, hn⟩ := exists_nat_gt ((ζ - z 0) / δ)
  have h1 := (hlin n).2
  have h2 := hne n
  rw [div_lt_iff₀ hδ] at hn
  linarith

/-! ## Unit tests: frozen and bounded act numbers -/

/-- **Photon test (frozen act number).** A constant act number `c > 0` above the threshold (a free massless field:
`z₀ = 2π` at every box size) satisfies the doubling law only with loss `η n ≥ ½` at every step; so never with a summable
loss. -/
theorem frozen_violates_doubling {c ζ ζe : ℝ} {ze η : ℕ → ℝ} (hc : 0 < c) (hζ : ζ ≤ c) (hze : ∀ n, ζe ≤ ze n)
    (hT : DoublingLaw (fun _ => c) ze ζ ζe η) : (∀ n, 1 / 2 ≤ η n) ∧ ¬ Summable η := by
  have hh : ∀ n, 1 / 2 ≤ η n := by
    intro n
    have := (hT n hζ (hze n)).1
    simp only at this
    nlinarith
  refine ⟨hh, fun hs => ?_⟩
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hs.tendsto_atTop_zero).2 (1 / 2) (by norm_num)).exists
  linarith [hh n]

/-- **Bounded act numbers fail the doubling law** (lattice photon `2L·arsinh(sin(π/L)) ↑ 2π`; an infrared fixed point).
No sequence bounded above meets D-S, D-T and an admissible loss with `ζ > 0`. -/
theorem bounded_violates_doubling {z ze η : ℕ → ℝ} {ζ ζe B : ℝ} (hζ : 0 < ζ) (hB : ∀ n, z n ≤ B)
    (hη : AdmissibleLoss η) (hS : DoublingStart z ze ζ ζe) : ¬ DoublingLaw z ze ζ ζe η := by
  intro hT
  set c := ζ * Real.exp (-2 * ∑' k, η k) with hc
  have hcpos : 0 < c := by positivity
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / c) (by norm_num : (1 : ℝ) < 2)
  have hfl := floor_of_doubling (L₀ := 1) one_pos hζ hη hS hT n
  rw [div_one, mul_one, le_div_iff₀ (by positivity)] at hfl
  rw [div_lt_iff₀ hcpos] at hn
  have : c * 2 ^ n ≤ z n := by
    calc c * 2 ^ n = ζ * Real.exp (-2 * ∑' k, η k) * 2 ^ n := by rw [hc]
      _ ≤ z n := hfl
  linarith [hB n]

/-! ## What D-T is: the gap along dyadic boxes (monotone case) -/

/-- **D-T relabels the gap (monotone case).** If the dyadic box gaps `E n` decrease and stay above `m > 0`, the doubling law
holds with equality, `E (n+1) = (1 − η n) E n` (equivalently `z (n+1) = 2 (1 − η n) z n`), for `η n = 1 − E(n+1)/E n`,
and this loss is nonnegative and summable (`Σ η ≤ log(E 0 / m)`). -/
theorem doubling_of_antitone_gap {E : ℕ → ℝ} {m : ℝ} (hm : 0 < m) (hE : ∀ n, m ≤ E n) (hanti : Antitone E) :
    (∀ n, 0 ≤ 1 - E (n + 1) / E n) ∧ Summable (fun n => 1 - E (n + 1) / E n) ∧
      ∀ n, E (n + 1) = (1 - (1 - E (n + 1) / E n)) * E n := by
  have hpos : ∀ n, 0 < E n := fun n => hm.trans_le (hE n)
  have hle : ∀ n, E (n + 1) ≤ E n := fun n => hanti (Nat.le_succ n)
  have h0 : ∀ n, 0 ≤ 1 - E (n + 1) / E n := fun n => by
    rw [sub_nonneg, div_le_one (hpos n)]; exact hle n
  have hlog : ∀ n, 1 - E (n + 1) / E n ≤ Real.log (E n) - Real.log (E (n + 1)) := by
    intro n
    have h := Real.log_le_sub_one_of_pos (div_pos (hpos (n + 1)) (hpos n))
    rw [Real.log_div (hpos (n + 1)).ne' (hpos n).ne'] at h
    linarith
  refine ⟨h0, summable_of_sum_range_le h0 (c := Real.log (E 0) - Real.log m) fun n => ?_, fun n => ?_⟩
  · calc ∑ i ∈ range n, (1 - E (i + 1) / E i) ≤ ∑ i ∈ range n, (Real.log (E i) - Real.log (E (i + 1))) :=
          sum_le_sum fun i _ => hlog i
      _ = Real.log (E 0) - Real.log (E n) := sum_range_sub' (fun i => Real.log (E i)) n
      _ ≤ Real.log (E 0) - Real.log m := by linarith [Real.log_le_log hm (hE n)]
  · field_simp [(hpos n).ne']
    ring

/-! ## D-ID, abstractly: boxes with gap predicates -/

/-- **D-ID (abstract).** A family of boxes `n` (side `2ⁿ L₀`) with "the box has gap at least `E`" predicates, downward closed
and attained at their supremum when that is positive. The box gap is `gap n = sSup {E | Q n E}`. -/
structure BoxGaps where
  Q : ℕ → ℝ → Prop
  mono : ∀ n E E', E' ≤ E → Q n E → Q n E'
  attained : ∀ n, 0 < sSup {E | Q n E} → Q n (sSup {E | Q n E})

namespace BoxGaps

variable (B : BoxGaps)

/-- The box gap. -/
def gap (n : ℕ) : ℝ := sSup {E | B.Q n E}

/-- The vacuum act number of box `n`: side times gap. -/
def act (L₀ : ℝ) (n : ℕ) : ℝ := 2 ^ n * L₀ * B.gap n

/-- **D-ID ∧ D-S ∧ D-T ⇒ every dyadic box has gap `≥ m`**, with `m = (ζ/L₀) exp(−2 Σ η) > 0`: the predicate `Q n m` holds
for all `n`. -/
theorem floor {L₀ ζ ζe : ℝ} {ze η : ℕ → ℝ} (hL₀ : 0 < L₀) (hζ : 0 < ζ) (hη : AdmissibleLoss η)
    (hS : DoublingStart (B.act L₀) ze ζ ζe) (hT : DoublingLaw (B.act L₀) ze ζ ζe η) :
    ∃ m : ℝ, 0 < m ∧ ∀ n, B.Q n m := by
  refine ⟨_, floor_pos (η := η) hL₀ hζ, fun n => ?_⟩
  have h := floor_of_doubling hL₀ hζ hη hS hT n
  have hs : (0 : ℝ) < 2 ^ n * L₀ := by positivity
  have hg : B.act L₀ n / (2 ^ n * L₀) = B.gap n := by unfold act; field_simp
  rw [hg] at h
  have hgpos : 0 < B.gap n := (floor_pos (η := η) hL₀ hζ).trans_le h
  exact B.mono n _ _ h (B.attained n hgpos)

end BoxGaps

/-! ## Passing to a volume limit -/

/-- **The box bound survives any limit of correlations.** If the correlations `h n` of box `n` obey
`|h n t| ≤ h n 0 · e^{−m t}` and converge pointwise along a subsequence to `g`, then `|g t| ≤ g 0 · e^{−m t}`. -/
theorem decay_of_limit {h : ℕ → ℕ → ℝ} {g : ℕ → ℝ} {m : ℝ}
    (hb : ∀ n t, |h n t| ≤ h n 0 * Real.exp (-(m * t))) {φ : ℕ → ℕ}
    (hlim : ∀ t, Tendsto (fun k => h (φ k) t) atTop (𝓝 (g t))) (t : ℕ) :
    |g t| ≤ g 0 * Real.exp (-(m * t)) :=
  le_of_tendsto_of_tendsto ((hlim t).abs) ((hlim 0).mul_const _) (Eventually.of_forall fun k => hb (φ k) t)

end ProofPhase.DMP
