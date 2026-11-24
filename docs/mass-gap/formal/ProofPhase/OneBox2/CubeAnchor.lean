/-
Proof phase, cycle 8, workstream 3 (c8c-concrete): the strong-coupling anchor of the wall-cut criterion
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c8c-concrete/NOTE.md`, section 3.
-/

import ProofPhase.OneBox2.Cube

/-!
# The wall-cut criterion is non-empty: the strong-coupling anchor for every cube and every boundary condition

`lifted_influence_cut_id`: for cells that are single links, the influence of an outside link `z` on the cut box
`Q ∩ b` (inside the cube law with outside frozen at `σ₀`) is `|Q ∩ b| · tanh(m(Q ∩ b, z) · 2β)`: the whole-box TV bound
`influence_block` applied to the cut block at the cut boundary condition; if `z` is itself outside the cube the cut
boundary condition does not move and the influence is `0`.  `wallCutOneBox_strong`: under the hypotheses of
`wilsonOneBox_strong`, `WallCutOneBox T` holds, with the same box (one site), the same numbers `κ`, for every cube.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.SingleLink Influence ProofPhase.Torus ProofPhase.V3 ProofPhase.V4 ProofPhase.OneBox

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OneBox2

section CutLifted

variable {N : ℕ} [NeZero N]

theorem cutPre_id (Q b : Finset (LatticeLink 4 N)) :
    cutPre Q (id : LatticeLink 4 N → LatticeLink 4 N) b = Q ∩ b := by
  unfold cutPre; rw [cellPre_id]

/-- **The influence of one outside link on a cut box of cells that are single links.** -/
theorem lifted_influence_cut_id {β : ℝ} (hβ : 0 ≤ β) (b : Finset (LatticeLink 4 N)) (hb : b.Nonempty)
    (Q : Finset (LatticeLink 4 N)) (σ₀ : GaugeConnection SU2 4 N) {z : LatticeLink 4 N} (hz : z ∉ b) :
    IsInfluenceBound b (cubeBoxSpec (id : LatticeLink 4 N → LatticeLink 4 N) β Q σ₀ b) z
      (((Q ∩ b).card : ℝ) *
        Real.tanh ((((touching (Q ∩ b)).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * ((2 : ℕ) : ℝ) * β)) := by
  intro W s F L hF hdep hosc
  obtain ⟨y0, hy0⟩ := hb
  have hL : 0 ≤ L := by
    have := hosc W y0 (W y0) hy0
    rw [Function.update_eq_self, sub_self, abs_zero] at this
    exact this
  set Bf : Finset (LatticeLink 4 N) := Q ∩ b with hBf
  have hBfb : Bf ⊆ b := inter_subset_right
  have hzBf : z ∉ Bf := fun h => hz (hBfb h)
  set G : GaugeConnection SU2 4 N → ℝ := fun U' => F (cellLift id (1 : SU2) (splice Bf σ₀ U')) with hG
  have hGW : ∀ (W' : LatticeLink 4 N → (LatticeLink 4 N → SU2)) U',
      F (liftMap id (1 : SU2) b Bf σ₀ W' U') = G U' := by
    intro W' U'
    exact hdep _ _ fun i hi => splice_of_mem hi _ _
  have hmG : Measurable G :=
    hF.meas.comp ((measurable_cellLift id (1 : SU2)).comp (measurable_splice_right Bf σ₀))
  have hbG : BM G := by
    obtain ⟨C, hC⟩ := hF.bdd
    exact ⟨hmG, C, fun U' => hC _⟩
  have hdepG : DepOn G Bf := by
    intro x y hxy
    have : splice Bf σ₀ x = splice Bf σ₀ y := by
      funext i
      by_cases hi : i ∈ Bf
      · simp [splice, hi, hxy i hi]
      · simp [splice, hi]
    simp only [hG, this]
  have hoscG : OscBound G (fun a => if a ∈ Bf then L else 0) := by
    intro ξ y t
    by_cases hy : y ∈ Bf
    · simp only [hy, if_true, hG]
      rw [splice_update_right hy, cellLift_id_update]
      exact hosc _ y _ (hBfb hy)
    · simp only [hy, if_false]
      rw [hdepG.update_eq hy]
      simp
  have hD : ∀ x y, G x - G y ≤ (Bf.card : ℝ) * L := by
    intro x y
    have h1 := hoscG.abs_sub_splice_le hdepG Bf x y
    have h2 : G (splice Bf x y) = G y := hdepG _ _ fun i hi => splice_of_mem hi _ _
    rw [h2, inter_self, sum_ite_of_true (fun a ha => ha), sum_const, nsmul_eq_mul] at h1
    exact (le_abs_self _).trans h1
  have hDnn : 0 ≤ (Bf.card : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL
  have hb' : ∀ W' : LatticeLink 4 N → (LatticeLink 4 N → SU2),
      ∫ ξ, F ξ ∂(cubeBoxSpec (id : LatticeLink 4 N → LatticeLink 4 N) β Q σ₀ b W') =
        ∫ U', G U' ∂(gaugeSpec (G := SU2) 2 (wilsonWeight β) Bf (splice Q σ₀ (cellProj id W'))) := by
    intro W'
    unfold cubeBoxSpec liftSpec cutSpec
    rw [cutPre_id, integral_map (measurable_liftMap id (1 : SU2) b Bf σ₀ W').aemeasurable
      hF.meas.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun U' => hGW W' U')
  rw [hb', hb']
  have hσ' : cellProj (id : LatticeLink 4 N → LatticeLink 4 N) (Function.update W z s) =
      Function.update (cellProj (id : LatticeLink 4 N → LatticeLink 4 N) W) z (s z) := by
    funext e
    by_cases he : e = z
    · subst he; simp [cellProj]
    · simp [cellProj, he]
  rw [hσ']
  have htan : 0 ≤ Real.tanh ((((touching Bf).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * ((2 : ℕ) : ℝ) * β) :=
    tanh_nonneg (by positivity)
  by_cases hzQ : z ∈ Q
  · have hs : splice Q σ₀ (Function.update (cellProj (id : LatticeLink 4 N → LatticeLink 4 N) W) z (s z)) =
        Function.update (splice Q σ₀ (cellProj (id : LatticeLink 4 N → LatticeLink 4 N) W)) z (s z) :=
      splice_update_right hzQ _ _ _
    rw [hs]
    have := influence_block (β := β) hβ Bf hzBf (splice Q σ₀ (cellProj id W)) (s z) hbG hDnn hD
    calc _ ≤ ((Bf.card : ℝ) * L) * Real.tanh ((((touching Bf).filter (fun p => z ∈ plaqLinks p)).card : ℝ) *
          ((2 : ℕ) : ℝ) * β) := this
      _ = _ := by ring
  · have hs : splice Q σ₀ (Function.update (cellProj (id : LatticeLink 4 N → LatticeLink 4 N) W) z (s z)) =
        splice Q σ₀ (cellProj (id : LatticeLink 4 N → LatticeLink 4 N) W) := by
      funext i
      by_cases hi : i ∈ Q
      · have : i ≠ z := fun h => hzQ (h ▸ hi)
        simp [splice, hi, Function.update_of_ne this]
      · simp [splice, hi]
    rw [hs, sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) htan) hL

/-- The anchor influence bounds of the cut boxes, for every cube and boundary condition (the transport along
`N = M` is the identity). -/
theorem anchor_influence_cut {N M : ℕ} [NeZero N] [NeZero M] (h : N = M) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ (Q : Finset (LatticeLink 4 N)) (σ₀ : GaugeConnection SU2 4 N) (t : FinLatticeSites 4 M) (z : LatticeLink 4 M),
      z ∉ boxBlock ({0} : Finset (FinLatticeSites 4 M)) t →
      IsInfluenceBound (boxBlock ({0} : Finset (FinLatticeSites 4 M)) t)
        (cubeBoxSpec (castLink h) β Q σ₀ (boxBlock ({0} : Finset (FinLatticeSites 4 M)) t)) z
        (kapAnchor β (z.site - t)) := by
  subst h
  intro Q σ₀ t z hz
  rw [castLink_refl]
  exact isInfluenceBound_mono (boxBlock_zero_nonempty t)
    (lifted_influence_cut_id hβ _ (boxBlock_zero_nonempty t) Q σ₀ hz)
    (kexact_le hβ t _ inter_subset_right hz)

end CutLifted

/-- **The strong-coupling anchor of the wall-cut criterion: `WallCutOneBox` is non-empty.** Same tuning and same
hypotheses as `wilsonOneBox_strong` (`T.ℓ k = 1`, `0 ≤ β_k`, `1944 tanh(2β_k) ≤ g < 1`, i.e. `β_k < 2.57 × 10⁻⁴` at
the edge): the influence bounds hold for every cube `Q` and every boundary condition `σ₀`, with the box a single
site and the numbers `κ(u) = 24 tanh(2β)` at the `≤ 80` neighbouring positions. -/
theorem wallCutOneBox_strong (T : Tuning) (hℓ : ∀ k, T.ℓ k = 1) {g : ℝ} (hg : g < 1)
    (hβ : ∀ k, 0 ≤ T.β k ∧ 1944 * Real.tanh (2 * T.β k) ≤ g) : WallCutOneBox T := by
  have hside : ∀ k j, T.side k j = coarseSide j := fun k j => by simp [Tuning.side, coarseSide, hℓ k]
  have hg0 : 0 ≤ g := by
    obtain ⟨h0, h1⟩ := hβ 0
    exact le_trans (mul_nonneg (by norm_num) (tanh_nonneg (by linarith))) h1
  obtain ⟨lam, hlam, hlg⟩ := exists_rate hg0 hg
  have ha : ∀ k, T.a k = T.L₁ := fun k => by simp [Tuning.a, hℓ k]
  refine ⟨fun k j => castLink (hside k j), 0, 0, ⟨fun k j e e' => ?_, fun k j e e' => ?_⟩, lam, g * Real.exp lam, 0, 1,
    hlam, by positivity, hlg, 0, fun k _ j => ?_⟩
  · rw [linkDist_castLink, ha k, add_zero]
  · rw [linkDist_castLink, ha k, mul_zero, add_zero]
  · refine ⟨{0}, kapAnchor (T.β k), by simp, by simp, by simp [siteDist_self],
      fun Q σ₀ t z hz => anchor_influence_cut (hside k j) (hβ k).1 Q σ₀ t z hz, ?_⟩
    have h1 := oneBoxSum_anchor (N := coarseSide j) (hβ k).1 hlam.le
    unfold OneBoxSum at h1 ⊢
    refine h1.trans ?_
    rw [mul_one] at h1 ⊢
    simp only [card_singleton, Nat.cast_one, mul_one]
    exact mul_le_mul_of_nonneg_right (hβ k).2 (Real.exp_pos _).le

end ProofPhase.OneBox2
