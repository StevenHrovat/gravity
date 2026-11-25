/-
Proof phase, cycle 8, workstream 3 (c8c-concrete): the strong-coupling anchor of the one-box criterion
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c8c-concrete/NOTE.md`, section 2.
-/

import ProofPhase.OneBox2.Concrete

/-!
# The strong-coupling anchor: `WilsonOneBox` holds for SU(2) at small `β`

**Box influence of one boundary link** (`influence_block`): for a block `B` of links and a link `z ∉ B`, changing the
boundary condition at `z` changes the box law by at most `D · tanh(m(B, z) · n β)` on test functions of range `≤ D`,
where `m(B, z)` is the number of plaquettes through `z` that touch `B` (the single-link TV lemma of
`OneScale.SingleLink`, applied to the whole box as one Gibbs measure).  For a box of at most `4` links at one site this
is the whole criterion: no comparison argument is needed.

**The anchor** (`wilsonOneBox_strong`): along a tuning with one lattice step per cell (`T.ℓ k = 1`, cells are single
links, fixed spacing) and `0 ≤ T.β k`, `1944 · tanh(2 T.β k) < 1`, the one-box criterion holds with the box a
single site (`Λ₀ = {0}`, `n_max = 1`, `D₀ = 0`) and every outside link at the 80 neighbouring positions having influence
`≤ 24 tanh(2β)`.  Explicitly `β < artanh(1/1944)/2 ≈ 2.57 × 10⁻⁴`.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.SingleLink Influence ProofPhase.Torus ProofPhase.V3 ProofPhase.V4 ProofPhase.OneBox

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OneBox2

/-! ## The influence of one boundary link on a box, as a Gibbs measure -/

section Block

variable {N : ℕ} [NeZero N]

/-- The log-weight of the box specification: `β ∑_{p touching B} Re tr U_p(splice B U ξ)`. -/
def logWB (β : ℝ) (B : Finset (LatticeLink 4 N)) (U ξ : GaugeConnection SU2 4 N) : ℝ :=
  ∑ p ∈ touching B, β * xp 2 p (splice B U ξ)

/-- **The box law is a Gibbs measure.** -/
theorem gaugeSpec_eq_gibbs_block (β : ℝ) (B : Finset (LatticeLink 4 N)) (U : GaugeConnection SU2 4 N) :
    gaugeSpec (G := SU2) 2 (fun x => Real.exp (β * x)) B U =
      gibbs (prodMeasure (ι := LatticeLink 4 N) (haarG SU2)) (logWB β B U) := by
  have hW : ∀ ξ, plaqProd 2 (fun x => Real.exp (β * x)) (touching B) (splice B U ξ) =
      Real.exp (logWB β B U ξ) := by
    intro ξ
    simp only [plaqProd, logWB, Real.exp_sum]
  unfold gaugeSpec locSpec gibbs partitionFn locZ
  simp_rw [hW]

/-- The part of the log-weight that changes with the boundary link `z`: the plaquettes through `z`. -/
def fPartB (B : Finset (LatticeLink 4 N)) (z : LatticeLink 4 N) (U ξ : GaugeConnection SU2 4 N) : ℝ :=
  ∑ p ∈ (touching B).filter (fun p => z ∈ plaqLinks p), xp 2 p (splice B U ξ)

/-- The part that does not change. -/
def psiPartB (β : ℝ) (B : Finset (LatticeLink 4 N)) (z : LatticeLink 4 N) (U ξ : GaugeConnection SU2 4 N) : ℝ :=
  ∑ p ∈ (touching B).filter (fun p => z ∉ plaqLinks p), β * xp 2 p (splice B U ξ)

theorem logWB_eq (β : ℝ) (B : Finset (LatticeLink 4 N)) (z : LatticeLink 4 N) (U : GaugeConnection SU2 4 N) :
    logWB β B U = fun ξ => β * fPartB B z U ξ + psiPartB β B z U ξ := by
  funext ξ
  unfold logWB fPartB psiPartB
  rw [mul_sum, sum_filter_add_sum_filter_not]

theorem psiPartB_update {B : Finset (LatticeLink 4 N)} {z : LatticeLink 4 N} (hz : z ∉ B) (β : ℝ)
    (U : GaugeConnection SU2 4 N) (s : SU2) : psiPartB β B z (Function.update U z s) = psiPartB β B z U := by
  funext ξ
  unfold psiPartB
  refine sum_congr rfl fun p hp => ?_
  simp only [mem_filter] at hp
  rw [splice_update_left hz]
  have hx : xp 2 p (Function.update (splice B U ξ) z s) = xp 2 p (splice B U ξ) := by
    have hh : plaquetteHolonomy (Function.update (splice B U ξ) z s) p = plaquetteHolonomy (splice B U ξ) p :=
      plaquetteHolonomy_dependsOn p _ _ fun l hl => by
        have : l ≠ z := fun h => hp.2 (h ▸ hl)
        simp [Function.update_of_ne this]
    unfold xp
    rw [hh]
  rw [hx]

theorem abs_fPartB_le (B : Finset (LatticeLink 4 N)) (z : LatticeLink 4 N) (U ξ : GaugeConnection SU2 4 N) :
    |fPartB B z U ξ| ≤ (((touching B).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * ((2 : ℕ) : ℝ) := by
  unfold fPartB
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ (touching B).filter (fun p => z ∈ plaqLinks p), |xp 2 p (splice B U ξ)|
      ≤ ∑ _p ∈ (touching B).filter (fun p => z ∈ plaqLinks p), ((2 : ℕ) : ℝ) :=
        sum_le_sum fun p _ => abs_xp_le su2_hU' p _
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem abs_logWB_le (β : ℝ) (B : Finset (LatticeLink 4 N)) (U ξ : GaugeConnection SU2 4 N) :
    |logWB β B U ξ| ≤ ((touching B).card : ℝ) * (|β| * ((2 : ℕ) : ℝ)) := by
  unfold logWB
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ touching B, |β * xp 2 p (splice B U ξ)| ≤ ∑ _p ∈ touching B, |β| * ((2 : ℕ) : ℝ) :=
        sum_le_sum fun p _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_xp_le su2_hU' p _) (abs_nonneg _)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem abs_psiPartB_le (β : ℝ) (B : Finset (LatticeLink 4 N)) (z : LatticeLink 4 N) (U ξ : GaugeConnection SU2 4 N) :
    |psiPartB β B z U ξ| ≤ ((touching B).card : ℝ) * (|β| * ((2 : ℕ) : ℝ)) := by
  unfold psiPartB
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ (touching B).filter (fun p => z ∉ plaqLinks p), |β * xp 2 p (splice B U ξ)|
      ≤ ∑ _p ∈ touching B, |β| * ((2 : ℕ) : ℝ) := by
        refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => abs_nonneg _).trans ?_
        exact sum_le_sum fun p _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_xp_le su2_hU' p _) (abs_nonneg _)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem measurable_fPartB (B : Finset (LatticeLink 4 N)) (z : LatticeLink 4 N) (U : GaugeConnection SU2 4 N) :
    Measurable (fPartB B z U) :=
  Finset.measurable_sum _ fun p _ => (measurable_xp su2_hc' p).comp (measurable_splice_right B U)

theorem measurable_psiPartB (β : ℝ) (B : Finset (LatticeLink 4 N)) (z : LatticeLink 4 N)
    (U : GaugeConnection SU2 4 N) : Measurable (psiPartB β B z U) :=
  Finset.measurable_sum _ fun p _ =>
    measurable_const.mul ((measurable_xp su2_hc' p).comp (measurable_splice_right B U))

theorem measurable_logWB (β : ℝ) (B : Finset (LatticeLink 4 N)) (U : GaugeConnection SU2 4 N) :
    Measurable (logWB β B U) :=
  Finset.measurable_sum _ fun p _ =>
    measurable_const.mul ((measurable_xp su2_hc' p).comp (measurable_splice_right B U))

/-- **Influence of one boundary link on a whole box** (Lemma 2.4 for the box Gibbs measure): for `z ∉ B`, `β ≥ 0`
and a bounded measurable `F` of range `≤ D`,
`|q_B^U(F) − q_B^{U[z := s]}(F)| ≤ D · tanh(m(B, z) · 2 β)`, `m(B, z)` the number of plaquettes through `z`
touching `B`. -/
theorem influence_block {β : ℝ} (hβ : 0 ≤ β) (B : Finset (LatticeLink 4 N)) {z : LatticeLink 4 N} (hz : z ∉ B)
    (U : GaugeConnection SU2 4 N) (s : SU2) {F : GaugeConnection SU2 4 N → ℝ} (hF : BM F) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ x y, F x - F y ≤ D) :
    |∫ ξ, F ξ ∂(gaugeSpec (G := SU2) 2 (fun x => Real.exp (β * x)) B U) -
        ∫ ξ, F ξ ∂(gaugeSpec (G := SU2) 2 (fun x => Real.exp (β * x)) B (Function.update U z s))| ≤
      D * Real.tanh ((((touching B).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * ((2 : ℕ) : ℝ) * β) := by
  set U' := Function.update U z s
  set π := prodMeasure (ι := LatticeLink 4 N) (haarG SU2)
  rw [gaugeSpec_eq_gibbs_block, gaugeSpec_eq_gibbs_block]
  obtain ⟨C, hC⟩ := hF.bdd
  have hψ : psiPartB β B z U' = psiPartB β B z U := psiPartB_update hz β U s
  have htv : ∀ V V' : GaugeConnection SU2 4 N, psiPartB β B z V' = psiPartB β B z V →
      tv (gibbs π (logWB β B V)) (gibbs π (logWB β B V')) ≤
        Real.tanh ((((touching B).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * ((2 : ℕ) : ℝ) * β) := by
    intro V V' hVV'
    rw [logWB_eq β B z V, logWB_eq β B z V', hVV']
    exact tv_single_link_le_tanh π (measurable_fPartB B z V) (measurable_fPartB B z V')
      (measurable_psiPartB β B z V) (n := (((touching B).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * ((2 : ℕ) : ℝ))
      hβ (abs_fPartB_le B z V) (abs_fPartB_le B z V') (abs_psiPartB_le β B z V)
  exact abs_integral_gibbs_sub_le π (measurable_logWB β B U) (measurable_logWB β B U')
    (abs_logWB_le β B U) (abs_logWB_le β B U') hF.meas hC hD0 hD (htv U U' hψ) (htv U' U hψ.symm)

end Block

/-! ## The lifted box law for cells that are single links -/

section Lifted

variable {N : ℕ} [NeZero N]

theorem cellPre_id (b : Finset (LatticeLink 4 N)) : cellPre (id : LatticeLink 4 N → LatticeLink 4 N) b = b := by
  ext e; simp [cellPre]

theorem cellLift_id_update (ξ : GaugeConnection SU2 4 N) (y : LatticeLink 4 N) (t : SU2) :
    cellLift (id : LatticeLink 4 N → LatticeLink 4 N) (1 : SU2) (Function.update ξ y t) =
      Function.update (cellLift (id : LatticeLink 4 N → LatticeLink 4 N) (1 : SU2) ξ) y
        (fun e => if e = y then t else 1) := by
  funext c e
  by_cases hc : c = y
  · subst hc
    by_cases he : e = c <;> simp [cellLift, he]
  · by_cases he : e = c
    · subst he
      simp [cellLift, hc]
    · simp [cellLift, he, hc]

/-- **The influence of one outside link on the box law regrouped by cells, for cells that are single links.** -/
theorem lifted_influence_id {β : ℝ} (hβ : 0 ≤ β) (b : Finset (LatticeLink 4 N)) (hb : b.Nonempty)
    {z : LatticeLink 4 N} (hz : z ∉ b) :
    IsInfluenceBound b (wilsonBoxSpec (id : LatticeLink 4 N → LatticeLink 4 N) β b) z
      ((b.card : ℝ) *
        Real.tanh ((((touching b).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * ((2 : ℕ) : ℝ) * β)) := by
  intro W s F L hF hdep hosc
  obtain ⟨y0, hy0⟩ := hb
  have hL : 0 ≤ L := by
    have := hosc W y0 (W y0) hy0
    rw [Function.update_eq_self, sub_self, abs_zero] at this
    exact this
  set ρ : GaugeConnection SU2 4 N := fun _ => 1
  set G : GaugeConnection SU2 4 N → ℝ := fun U' => F (cellLift id (1 : SU2) (splice b ρ U')) with hG
  -- the function does not see the boundary
  have hGW : ∀ (W' : LatticeLink 4 N → (LatticeLink 4 N → SU2)) U',
      F (liftMap id (1 : SU2) b b ρ W' U') = G U' := by
    intro W' U'
    exact hdep _ _ fun i hi => splice_of_mem hi _ _
  have hmG : Measurable G := hF.meas.comp ((measurable_cellLift id (1 : SU2)).comp (measurable_splice_right b ρ))
  have hbG : BM G := by
    obtain ⟨C, hC⟩ := hF.bdd
    exact ⟨hmG, C, fun U' => hC _⟩
  have hdepG : DepOn G b := by
    intro x y hxy
    refine hdep _ _ fun c hc => ?_
    funext e
    simp only [cellLift, id]
    by_cases he : e = c
    · subst he; simp [splice_of_mem hc, hxy e hc]
    · simp [he]
  have hoscG : OscBound G (fun a => if a ∈ b then L else 0) := by
    intro ξ y t
    by_cases hy : y ∈ b
    · simp only [hy, if_true, hG]
      rw [splice_update_right hy, cellLift_id_update]
      exact hosc _ y _ hy
    · simp only [hy, if_false]
      rw [hdepG.update_eq hy]
      simp
  have hD : ∀ x y, G x - G y ≤ (b.card : ℝ) * L := by
    intro x y
    have h1 := hoscG.abs_sub_splice_le hdepG b x y
    have h2 : G (splice b x y) = G y := hdepG _ _ fun i hi => splice_of_mem hi _ _
    rw [h2, inter_self, sum_ite_of_true (fun a ha => ha), sum_const, nsmul_eq_mul] at h1
    exact (le_abs_self _).trans h1
  have hDnn : 0 ≤ (b.card : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL
  -- unfold and move to the fine level
  have hσ' : cellProj (id : LatticeLink 4 N → LatticeLink 4 N) (Function.update W z s) =
      Function.update (cellProj (id : LatticeLink 4 N → LatticeLink 4 N) W) z (s z) := by
    funext e
    by_cases he : e = z
    · subst he; simp [cellProj]
    · simp [cellProj, he]
  have hb' : ∀ W' : LatticeLink 4 N → (LatticeLink 4 N → SU2),
      ∫ ξ, F ξ ∂(wilsonBoxSpec (id : LatticeLink 4 N → LatticeLink 4 N) β b W') =
        ∫ U', G U' ∂(gaugeSpec (G := SU2) 2 (fun x => Real.exp (β * x)) b (cellProj id W')) := by
    intro W'
    unfold wilsonBoxSpec liftSpec
    rw [cellPre_id, integral_map (measurable_liftMap id (1 : SU2) b b ρ W').aemeasurable hF.meas.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun U' => hGW W' U')
  rw [hb', hb', hσ']
  have := influence_block hβ b hz (cellProj id W) (s z) hbG hDnn hD
  calc _ ≤ ((b.card : ℝ) * L) * Real.tanh ((((touching b).filter (fun p => z ∈ plaqLinks p)).card : ℝ) *
        ((2 : ℕ) : ℝ) * β) := this
    _ = _ := by ring

end Lifted

/-! ## Counting: the box of one site -/

section Count

variable {N : ℕ} [NeZero N]

theorem eq_of_cyc_le_one {a : ZMod N} (h : cyc a ≤ 1) : a = 0 ∨ a = 1 ∨ a = -1 := by
  rw [cyc_eq_min] at h
  have hlt := ZMod.val_lt a
  have ha : ((a.val : ℕ) : ZMod N) = a := ZMod.natCast_zmod_val a
  rcases min_le_iff.1 h with h1 | h1
  · rcases (by omega : a.val = 0 ∨ a.val = 1) with hv | hv
    · left; rw [← ha, hv]; simp
    · right; left; rw [← ha, hv]; simp
  · right; right
    have h3 : a.val = N - 1 := by omega
    rw [← ha, h3, Nat.cast_sub (by omega : 1 ≤ N)]
    simp

/-- At most `3⁴ = 81` sites are within distance `1` of the origin. -/
theorem card_near_le :
    (univ.filter (fun u : FinLatticeSites 4 N => siteDist u 0 ≤ 1)).card ≤ 81 := by
  let g : (Fin 4 → Fin 3) → FinLatticeSites 4 N := fun v i => ![(0 : ZMod N), 1, -1] (v i)
  have hsub : univ.filter (fun u : FinLatticeSites 4 N => siteDist u 0 ≤ 1) ⊆ univ.image g := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    have : ∀ i, ∃ j : Fin 3, ![(0 : ZMod N), 1, -1] j = u i := by
      intro i
      have hi : cyc (u i - (0 : FinLatticeSites 4 N) i) ≤ 1 := (cyc_le_siteDist _ _ i).trans hu
      simp only [Pi.zero_apply, sub_zero] at hi
      rcases eq_of_cyc_le_one hi with h | h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
      · exact ⟨2, by simp [h]⟩
    choose v hv using this
    exact mem_image.2 ⟨v, mem_univ _, funext hv⟩
  calc _ ≤ (univ.image g).card := card_le_card hsub
    _ ≤ (univ : Finset (Fin 4 → Fin 3)).card := card_image_le
    _ = 81 := by simp [Fintype.card_fun]

/-- The anchor influence numbers: `24 tanh(2β)` at the positions within distance `1`, `0` elsewhere. -/
def kapAnchor (β : ℝ) (u : FinLatticeSites 4 N) : ℝ := if siteDist u 0 ≤ 1 then 24 * Real.tanh (2 * β) else 0

theorem kapAnchor_nonneg {β : ℝ} (hβ : 0 ≤ β) (u : FinLatticeSites 4 N) : 0 ≤ kapAnchor β u := by
  unfold kapAnchor
  split_ifs
  · exact mul_nonneg (by norm_num) (tanh_nonneg (by linarith))
  · exact le_rfl

theorem boxBlock_zero_site (t : FinLatticeSites 4 N) (l : LatticeLink 4 N) :
    l ∈ boxBlock ({0} : Finset (FinLatticeSites 4 N)) t ↔ l.site = t := by
  simp [boxBlock, sub_eq_zero]

theorem boxBlock_zero_nonempty (t : FinLatticeSites 4 N) : (boxBlock ({0} : Finset (FinLatticeSites 4 N)) t).Nonempty :=
  ⟨⟨t, 0⟩, (boxBlock_zero_site t _).2 rfl⟩

/-- An influence bound on a nonempty block can be weakened to any larger coefficient. -/
theorem isInfluenceBound_mono {ι S : Type*} [DecidableEq ι] [MeasurableSpace S] {B : Finset ι} (hB : B.Nonempty)
    {q : (ι → S) → Measure (ι → S)} {z : ι} {k k' : ℝ} (h : IsInfluenceBound B q z k) (hk : k ≤ k') :
    IsInfluenceBound B q z k' := by
  intro σ s F L hF hdep hosc
  obtain ⟨y, hy⟩ := hB
  have hL : 0 ≤ L := by
    have := hosc σ y (σ y) hy
    rwa [Function.update_eq_self, sub_self, abs_zero] at this
  exact (h σ s F L hF hdep hosc).trans (mul_le_mul_of_nonneg_right hk hL)

/-- **The exact influence number is below the anchor number**, for the box of one site or any sub-block of it
(a cut box). -/
theorem kexact_le {β : ℝ} (hβ : 0 ≤ β) (t : FinLatticeSites 4 N) {z : LatticeLink 4 N}
    (B : Finset (LatticeLink 4 N)) (hB : B ⊆ boxBlock ({0} : Finset (FinLatticeSites 4 N)) t)
    (hz : z ∉ boxBlock ({0} : Finset (FinLatticeSites 4 N)) t) :
    (B.card : ℝ) *
      Real.tanh ((((touching B).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * ((2 : ℕ) : ℝ) * β) ≤
        kapAnchor β (z.site - t) := by
  set m := ((touching B).filter (fun p => z ∈ plaqLinks p)).card with hm
  have hcard : (B.card : ℝ) ≤ 4 := by
    have := (card_le_card hB).trans (card_boxBlock ({0} : Finset (FinLatticeSites 4 N)) t)
    simp only [card_singleton, mul_one] at this
    exact_mod_cast this
  have hm6 : (m : ℝ) ≤ 6 := by
    have h1 : m ≤ (plaqsAt z).card := by
      refine card_le_card fun p hp => ?_
      simp only [mem_filter] at hp
      simp [plaqsAt, hp.2]
    have h2 := OneScale.SingleLink.card_plaqsAt_le (d := 4) (N := N) z
    exact_mod_cast h1.trans (h2.trans (by norm_num))
  have ht0 : 0 ≤ Real.tanh (2 * β) := tanh_nonneg (by linarith)
  have hcast : (m : ℝ) * ((2 : ℕ) : ℝ) * β = (m : ℝ) * (2 * β) := by push_cast; ring
  have hkey : Real.tanh ((m : ℝ) * ((2 : ℕ) : ℝ) * β) ≤ 6 * Real.tanh (2 * β) := by
    rw [hcast]
    exact (tanh_nat_mul_le (by linarith) m).trans (mul_le_mul_of_nonneg_right hm6 ht0)
  have hnn : 0 ≤ Real.tanh ((m : ℝ) * ((2 : ℕ) : ℝ) * β) := tanh_nonneg (by positivity)
  by_cases hm0 : m = 0
  · have : ((m : ℕ) : ℝ) = 0 := by rw [hm0]; simp
    rw [this]
    simp only [zero_mul, Real.tanh_zero, mul_zero]
    exact kapAnchor_nonneg hβ _
  · -- `z` shares a plaquette with the box, so it is near
    obtain ⟨p, hp⟩ := card_pos.1 (Nat.pos_of_ne_zero hm0)
    simp only [mem_filter, touching, mem_univ, true_and] at hp
    obtain ⟨⟨l, hl, hlb⟩, hzp⟩ := hp
    have hls : l.site = t := (boxBlock_zero_site t l).1 (hB hlb)
    have h1 := linkDist_le_one_of_plaq hl hzp
    simp only [linkDist, hls] at h1
    have h1' : siteDist z.site t ≤ 1 := by exact_mod_cast h1
    have h2 : siteDist (z.site - t) 0 ≤ 1 := by
      have := siteDist_sub_right z.site t t
      rw [sub_self] at this
      rw [this]; exact h1'
    simp only [kapAnchor, h2, if_true]
    calc (B.card : ℝ) * Real.tanh ((m : ℝ) * ((2 : ℕ) : ℝ) * β) ≤ 4 * (6 * Real.tanh (2 * β)) :=
          mul_le_mul hcard hkey hnn (by norm_num)
      _ = 24 * Real.tanh (2 * β) := by ring

/-- **The one-box sum at the anchor**: with `γ₀ = 1944 tanh(2β)`. -/
theorem oneBoxSum_anchor {β : ℝ} (hβ : 0 ≤ β) {lam : ℝ} (hlam : 0 ≤ lam) :
    OneBoxSum (kapAnchor β) (boxReach ({0} : Finset (FinLatticeSites 4 N))) {0} lam
      (1944 * Real.tanh (2 * β) * Real.exp (lam * 1)) := by
  have ht0 : 0 ≤ Real.tanh (2 * β) := tanh_nonneg (by linarith)
  refine oneBoxSum_of_finiteRange (U := FinLatticeSites 4 N) (E₁ := 1) hlam (kapAnchor_nonneg hβ) ?_ ?_
  · intro u hu
    unfold kapAnchor at hu
    have hu' : siteDist u 0 ≤ 1 := by
      by_contra hc; simp [hc] at hu
    unfold boxReach
    simp only [Finset.sup_singleton]
    exact_mod_cast hu'
  · calc ∑ u ∈ univ.filter (fun u => u ∉ ({0} : Finset (FinLatticeSites 4 N))), kapAnchor β u
        ≤ ∑ u : FinLatticeSites 4 N, kapAnchor β u :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun u _ _ => kapAnchor_nonneg hβ u
      _ = ((univ.filter (fun u : FinLatticeSites 4 N => siteDist u 0 ≤ 1)).card : ℝ) * (24 * Real.tanh (2 * β)) := by
          simp only [kapAnchor, Finset.sum_ite, sum_const, nsmul_eq_mul, mul_zero, add_zero]
      _ ≤ 81 * (24 * Real.tanh (2 * β)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_near_le) (by positivity)
      _ = 1944 * Real.tanh (2 * β) * (({0} : Finset (FinLatticeSites 4 N)).card : ℝ) := by
          simp; ring

end Count

/-! ## The tuning with one lattice step per cell -/

section Tune

/-- Transport a link along an equality of the torus size. -/
def castLink {N M : ℕ} (h : N = M) (e : LatticeLink 4 N) : LatticeLink 4 M := h ▸ e

theorem castLink_refl {N : ℕ} : castLink (rfl : N = N) = (id : LatticeLink 4 N → LatticeLink 4 N) := rfl

theorem linkDist_castLink {N M : ℕ} [NeZero N] [NeZero M] (h : N = M) (e e' : LatticeLink 4 N) :
    linkDist (castLink h e) (castLink h e') = linkDist e e' := by
  subst h; rfl

/-- The influence bounds of the anchor, for cells that are single links (the transport along `N = M` is the
identity). -/
theorem anchor_influence {N M : ℕ} [NeZero N] [NeZero M] (h : N = M) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ t z, z ∉ boxBlock ({0} : Finset (FinLatticeSites 4 M)) t →
      IsInfluenceBoundOn (ActAdm (liftAct (castLink h) (gaugeAct N)) (boxBlock ({0} : Finset (FinLatticeSites 4 M)) t))
        (boxBlock ({0} : Finset (FinLatticeSites 4 M)) t)
        (wilsonBoxSpec (castLink h) β (boxBlock ({0} : Finset (FinLatticeSites 4 M)) t)) z
        (kapAnchor β (z.site - t)) := by
  subst h
  intro t z hz
  rw [castLink_refl]
  exact isInfluenceBoundOn_of (isInfluenceBound_mono (boxBlock_zero_nonempty t)
    (lifted_influence_id hβ _ (boxBlock_zero_nonempty t) hz) (kexact_le hβ t _ subset_rfl hz))

/-- **The strong-coupling anchor: `WilsonOneBox` is non-empty.** Along a tuning with one lattice step per cell
(`T.ℓ k = 1`: cells are single links, the spacing is fixed) and bare couplings with `0 ≤ β_k` and
`1944 · tanh(2 β_k) ≤ g < 1` (explicitly `β_k ≤ artanh(g/1944)/2`; for `g → 1`, `β_k < 2.57 × 10⁻⁴`), the one-box
criterion with the actual Wilson box law holds, with the box a single site (`Λ₀ = {0}`, `n_max = 1`, `D₀ = 0`),
every outside link at the `≤ 80` neighbouring positions having influence `≤ 24 tanh(2β_k)`, and
`γ = g e^{λ} < 1`. -/
theorem wilsonOneBox_strong (T : Tuning) (hℓ : ∀ k, T.ℓ k = 1) {g : ℝ} (hg : g < 1)
    (hβ : ∀ k, 0 ≤ T.β k ∧ 1944 * Real.tanh (2 * T.β k) ≤ g) : WilsonOneBox T := by
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
      anchor_influence (hside k j) (hβ k).1, ?_⟩
    have h1 := oneBoxSum_anchor (N := coarseSide j) (hβ k).1 hlam.le
    unfold OneBoxSum at h1 ⊢
    refine h1.trans ?_
    rw [mul_one] at h1 ⊢
    simp only [card_singleton, Nat.cast_one, mul_one]
    exact mul_le_mul_of_nonneg_right (hβ k).2 (Real.exp_pos _).le

/-- **Constant coupling version**: `T.ℓ k = 1` and `T.β k = β` for all `k`, with `1944 tanh(2β) < 1`, i.e.
`0 ≤ β < artanh(1/1944)/2 ≈ 2.57 × 10⁻⁴`. -/
theorem wilsonOneBox_strong_const (T : Tuning) (hℓ : ∀ k, T.ℓ k = 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβk : ∀ k, T.β k = β)
    (hβ : 1944 * Real.tanh (2 * β) < 1) : WilsonOneBox T :=
  wilsonOneBox_strong T hℓ hβ fun k => ⟨by rw [hβk k]; exact hβ0, by rw [hβk k]⟩

end Tune

end ProofPhase.OneBox2
