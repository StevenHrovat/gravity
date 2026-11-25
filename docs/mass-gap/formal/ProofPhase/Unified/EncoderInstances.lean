/-
The unified lossy-step theorem: the encoder in its three use cases (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/ENCODER.md`, section 3.
-/

import ProofPhase.Unified.Encoder
import ProofPhase.Unified.YangMills
import ProofPhase.Unified.GRH
import ProofPhase.Proof.CPDuality
import ProofPhase.RouteB.Duality

/-!
# The encoder in three use cases

**Yang-Mills** (the centre twist on the box boundary; electric profile, reflection coefficient `c = Z_tw/Z`).
* `ym_factor`: `elec(Z_tw/Z) = e^{−F_e}`: the electric factor of the box is the encoder's factor.
* `su2_encoder`: for SU(2) at every `β ≠ 0` (with `0 < Z_tw` stated, as in `su2_handover`), the factor lies in `(0, 1)`.
* `ym_encoder_rotation`: the lattice rotation (0 2)(1 3) moves the encoder from the temporal plane to the spatial plane
  with the same factor ('t Hooft's duality, `tHooft_rotation`).
* `ymOneBox_iff_refl`: **O1 in encoder terms**: `YMOneBox` holds exactly when `Z_tw/Z` stays above some
  `c₀ > (μ − 1)/(μ + 1)` for every outside.
* `handover_refl`: the hand-over encoder is self-dual, `c = √2 − 1` (`elec_selfdual`), and lies below `(μ − 1)/(μ + 1)`
  for `μ ≥ 3`.

**GRH** (the scale step; Szego profile).
* `grh_lag_encoder`: under the sign (`ScaleSign`), the lag encoder `t m / t 0` (the state `z^m` against its image `1`)
  lies in the closed unit disk and its Szego factor is in `[0, 1]`; for `m = 1` this is the first reflection coefficient.
* `sign_fails_of_refl`: one lag encoder outside the disk refutes the sign.

**NP vs coNP** (what a proof line names; the restriction step's survival share).
* `survShare_mem`: the share lies in `[0, 1]`.
* `clause_share_le`: a clause naming `w` literals survives at most a `1 − w/(2n)` share: finitely below one.
* `thr_share_one`: the cutting-planes threshold line (`k ≥ 2`) survives every single restriction: factor exactly one.

No axioms beyond the standard ones.
-/

open Finset
open scoped ComplexConjugate

noncomputable section

namespace ProofPhase.Unified

/-! ## 1. Yang-Mills: the centre twist on the box boundary -/

section YM

open ProofPhase.Flip

theorem ym_refl_mem {Z Ztw : ℝ} (hT : 0 < Ztw) (hlt : Ztw < Z) : 0 < Ztw / Z ∧ Ztw / Z < 1 :=
  ⟨div_pos hT (by linarith), (div_lt_one (by linarith)).2 hlt⟩

/-- **The box's electric factor is the encoder's factor**: `elec(Z_tw/Z) = e^{−F_e}`. -/
theorem ym_factor {Z Ztw : ℝ} (hT : 0 < Ztw) (hlt : Ztw < Z) : elec (Ztw / Z) = Real.exp (-elecF Z Ztw) := by
  rw [elec_ratio (by linarith), elecF, neg_neg, Real.exp_log (div_pos (by linarith) (by linarith))]

/-- **SU(2): the encoder's factor lies in `(0, 1)` at every `β ≠ 0`** (`su2_Ztw_lt_Z`; `0 < Z_tw` stated). -/
theorem su2_encoder (L : ℕ) [NeZero L] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L)
    {T : ℕ} [NeZero T] (hT : Even T) (hpos : 0 < su2Ztw L β P c T) :
    0 < elec (su2Ztw L β P c T / su2Z L β P T) ∧ elec (su2Ztw L β P c T / su2Z L β P T) < 1 ∧
      elec (su2Ztw L β P c T / su2Z L β P T) = Real.exp (-elecF (su2Z L β P T) (su2Ztw L β P c T)) := by
  have hlt := su2_Ztw_lt_Z L hβ P c hT
  have hm := ym_refl_mem hpos hlt
  exact ⟨(elec_mem hm.1 hm.2).1, (elec_mem hm.1 hm.2).2, ym_factor hpos hlt⟩

/-- **O1 in encoder terms**: the one-box statement holds exactly when the reflection coefficient `Z_tw/Z` stays above
some `c₀ > (μ − 1)/(μ + 1)`, uniformly over the outsides `ω`. -/
theorem ymOneBox_iff_refl {Ω : Type*} {Z Ztw : Ω → ℝ} (hT : ∀ ω, 0 < Ztw ω) (hlt : ∀ ω, Ztw ω < Z ω) {μ : ℝ}
    (hμ : 1 < μ) :
    YMOneBox (fun ω => elecF (Z ω) (Ztw ω)) μ ↔ ∃ c₀, (μ - 1) / (μ + 1) < c₀ ∧ ∀ ω, c₀ ≤ Ztw ω / Z ω := by
  have hF : (fun ω => elecF (Z ω) (Ztw ω)) = fun ω => -Real.log (elec (Ztw ω / Z ω)) := by
    funext ω
    rw [elec_ratio (by linarith [hT ω, hlt ω])]
    rfl
  rw [YMOneBox, hF, oneBox_iff_refl (fun ω => (ym_refl_mem (hT ω) (hlt ω)).1)
    (fun ω => (ym_refl_mem (hT ω) (hlt ω)).2) hμ, elec_inv (by linarith)]

/-- **The hand-over encoder is below what O1 needs**: the self-dual `c = √2 − 1` is below `(μ − 1)/(μ + 1)` for
`μ ≥ 3`. -/
theorem handover_refl {μ : ℝ} (hμ : 3 ≤ μ) : √2 - 1 < (μ - 1) / (μ + 1) := by
  have hs : √2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  rw [lt_div_iff₀ (by linarith)]
  nlinarith [mul_pos (sub_pos.2 hs) (show (0 : ℝ) < μ + 1 by linarith)]

end YM

section YMRotation

open MeasureTheory Positivity ProofPhase.RouteB

variable {N : ℕ} {G : Type*} [Group G] {n : ℕ} [HasGaugeTrace G n] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] [NeZero N]

/-- **The one rotation acts on the encoder**: the lattice rotation (0 2)(1 3) moves the twist from the temporal plane
(electric side) to the spatial plane (magnetic side) with the same reflection coefficient, hence the same factor. -/
theorem ym_encoder_rotation (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ) (β : ℝ) :
    elec (twistZ (G := G) (N := N) n β (twistPlane 0 1) / twistZ (G := G) (N := N) n β ∅) =
      elec (twistZ (G := G) (N := N) n β (twistPlane 2 3) / twistZ (G := G) (N := N) n β ∅) := by
  rw [tHooft_rotation hc hU β]

end YMRotation

/-! ## 2. GRH: the scale step -/

section GRH

open ProofPhase.GRH

/-- **Under the sign, every lag encoder lies in the unit disk**: the state `z^m` against its image `1` has reflection
coefficient `t m / t 0`, and its Szego factor is in `[0, 1]`. For `m = 1` this is the first reflection coefficient. -/
theorem grh_lag_encoder {t : ℤ → ℂ} (ht : ∀ m, t (-m) = conj (t m)) (h : ScaleSign t) (h0 : 0 < (t 0).re) (m : ℕ) :
    ‖t m / t 0‖ ≤ 1 ∧ 0 ≤ szego (t m / t 0) := by
  have hpos := (scaleSign_iff t).1 h
  have hb := toep_moment_bound t ht (fun s c => pos_of_sections hpos.2 s c) m
  have hn : (t 0).re ≤ ‖t 0‖ := Complex.re_le_norm (t 0)
  have hb1 : ‖t m / t 0‖ ≤ 1 := by
    rw [norm_div, div_le_one (by linarith)]
    linarith
  exact ⟨hb1, szego_nonneg hb1⟩

/-- **One lag encoder outside the disk refutes the sign.** -/
theorem sign_fails_of_refl {t : ℤ → ℂ} (ht : ∀ m, t (-m) = conj (t m)) (h0 : 0 < (t 0).re) {m : ℕ}
    (hm : 1 < ‖t m / t 0‖) : ¬ ScaleSign t := fun h =>
  absurd (grh_lag_encoder ht h h0 m).1 (not_le.2 hm)

end GRH

/-! ## 3. NP vs coNP: what a proof line names -/

section NP

open ProofPhase.Proof ProofPhase.Proof.Edge
open scoped Classical

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **The restriction step's factor for one line**: the share of single-literal restrictions (fix one variable to one
value) that leave the line alive (do not force it true). -/
def survShare (L : (α → Bool) → Prop) : ℝ :=
  ((univ.filter fun l : α × Bool => ¬ ForcesTrue L {l.1} (fun _ => l.2)).card : ℝ) / Fintype.card (α × Bool)

omit [DecidableEq α] in
theorem survShare_mem (L : (α → Bool) → Prop) : 0 ≤ survShare L ∧ survShare L ≤ 1 := by
  refine ⟨by unfold survShare; positivity, ?_⟩
  unfold survShare
  exact div_le_one_of_le₀ (by exact_mod_cast card_le_univ _) (by positivity)

/-- **A clause pays for what it names**: a clause naming `w` literals survives at most a `1 − w/(2n)` share of the
single restrictions (any of its own literals kills it). -/
theorem clause_share_le [Nonempty α] (C : Clause α) :
    survShare (fun a => ¬ Falsifies a C) ≤ 1 - (C.card : ℝ) / (2 * Fintype.card α) := by
  have hsub : (univ.filter fun l : α × Bool => ¬ ForcesTrue (fun a => ¬ Falsifies a C) {l.1} (fun _ => l.2)) ⊆
      univ \ C := by
    intro l hl
    simp only [mem_filter, mem_univ, true_and] at hl
    refine mem_sdiff.2 ⟨mem_univ _, fun hlC => hl fun a ha => ?_⟩
    exact clause_killed hlC a (by simpa using ha l.1 (mem_singleton_self _))
  have hcard := card_le_card hsub
  rw [card_univ_sdiff] at hcard
  have hC : C.card ≤ Fintype.card (α × Bool) := card_le_univ C
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have h2 : (Fintype.card (α × Bool) : ℝ) = 2 * Fintype.card α := by
    rw [Fintype.card_prod, Fintype.card_bool]; push_cast; ring
  unfold survShare
  rw [h2, div_le_iff₀ (by positivity)]
  have : ((Fintype.card (α × Bool) - C.card : ℕ) : ℝ) = 2 * Fintype.card α - C.card := by
    rw [Nat.cast_sub hC, h2]
  have hcard' : ((univ.filter fun l : α × Bool =>
      ¬ ForcesTrue (fun a => ¬ Falsifies a C) {l.1} (fun _ => l.2)).card : ℝ) ≤ 2 * Fintype.card α - C.card := by
    rw [← this]; exact_mod_cast hcard
  have hsimp : (1 - (C.card : ℝ) / (2 * Fintype.card α)) * (2 * Fintype.card α) = 2 * Fintype.card α - C.card := by
    field_simp
  rw [hsimp]
  exact hcard'

/-- **The cutting-planes threshold line names the crossing losslessly**: for `k ≥ 2` no single restriction forces
`thr B k` true, so its factor is exactly one. -/
theorem thr_share_one [Nonempty α] (B : Finset α) {k : ℕ} (hk : 2 ≤ k) : survShare (thr B k) = 1 := by
  have hall : (univ.filter fun l : α × Bool => ¬ ForcesTrue (thr B k) {l.1} (fun _ => l.2)) = univ := by
    refine filter_true_of_mem fun l _ hF => ?_
    obtain ⟨a, ha, hna⟩ := thr_survives (k := k) B {l.1} (by rw [card_singleton]; omega) (fun _ => l.2)
    exact hna (hF a ha)
  unfold survShare
  rw [hall, card_univ]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

end NP

end ProofPhase.Unified
