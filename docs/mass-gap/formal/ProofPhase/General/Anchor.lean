/-
Proof phase, generalisation phase 1b: the strong-coupling anchor over any gauge group and dimension (2026-11-24).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1b.
-/

import ProofPhase.General.Concrete
import ProofPhase.OneBox2.Anchor

/-!
# The strong-coupling anchor: `WilsonOneBox` holds at small `β`, over any gauge group and dimension

`OneBox2/Anchor` for any `Gr` of the package in dimension `d` and representation dimension `nr`. The numbers of the
SU(2), `d = 4` file become the lattice counts: a block of one site has `d` links, a link lies in at most `2(d − 1)`
plaquettes (`OneScale.SingleLink.card_plaqsAt_le`), at most `3^d` sites lie within distance one (`card_near_le` of
phase 1), and `tanh(2β)` is `tanh(nr β)` (the bound `|Re tr| ≤ nr`). So

* `anchorK d = d · 2(d − 1)` replaces `24` (`= 4 · 6`): the influence number of an outside link is
  `≤ anchorK d · tanh(nr β)` (`kapAnchor`);
* `anchorG d = 3^d · anchorK d` replaces `1944` (`= 81 · 24`): `wilsonOneBox_strong` holds when
  `anchorG d · tanh(nr β_k) ≤ g < 1`.

The SU(2), `d = 4` statements are recovered by `d = 4`, `nr = 2` (`anchorK 4 = 24`, `anchorG 4 = 1944`).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.SingleLink Influence

open ProofPhase.OneBox (liftAct ActAdm IsInfluenceBoundOn isInfluenceBoundOn_of OneBoxSum oneBoxSum_of_finiteRange
  ActInv SpecCovariant)
open ProofPhase.OneBox2 (liftMap liftSpec measurable_liftMap isInfluenceBound_mono)
open ProofPhase.V3 (cellLift cellProj measurable_cellLift)

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

/-- The influence number of an outside link in the anchor: `d` links per site times `2(d − 1)` plaquettes per link
(`24` for `d = 4`). -/
def anchorK (d : ℕ) : ℝ := ((d * (2 * (d - 1)) : ℕ) : ℝ)

/-- The one-box sum constant at the anchor: `3^d` neighbouring sites times `anchorK d` (`1944` for `d = 4`). -/
def anchorG (d : ℕ) : ℝ := ((3 ^ d * (d * (2 * (d - 1))) : ℕ) : ℝ)

theorem anchorK_four : anchorK 4 = 24 := by norm_num [anchorK]

theorem anchorG_four : anchorG 4 = 1944 := by norm_num [anchorG]

theorem anchorK_nonneg (d : ℕ) : 0 ≤ anchorK d := Nat.cast_nonneg _

theorem anchorG_eq (d : ℕ) : anchorG d = 3 ^ d * anchorK d := by
  unfold anchorG anchorK; push_cast; ring

section Anchor

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] [GaugeRep Gr nr] {d : ℕ} [NeZero d]

section Block

variable {N : ℕ} [NeZero N]

def logWB (β : ℝ) (B : Finset (LatticeLink d N)) (U ξ : GaugeConnection Gr d N) : ℝ :=
  ∑ p ∈ touching B, β * xp nr p (splice B U ξ)

theorem gaugeSpec_eq_gibbs_block (β : ℝ) (B : Finset (LatticeLink d N)) (U : GaugeConnection Gr d N) :
    gaugeSpec (G := Gr) nr (fun x => Real.exp (β * x)) B U =
      gibbs (prodMeasure (ι := LatticeLink d N) (haarG Gr)) (logWB nr β B U) := by
  have hW : ∀ ξ, plaqProd nr (fun x => Real.exp (β * x)) (touching B) (splice B U ξ) =
      Real.exp (logWB nr β B U ξ) := by
    intro ξ
    simp only [plaqProd, logWB, Real.exp_sum]
  unfold gaugeSpec locSpec gibbs partitionFn locZ
  simp_rw [hW]

def fPartB (B : Finset (LatticeLink d N)) (z : LatticeLink d N) (U ξ : GaugeConnection Gr d N) : ℝ :=
  ∑ p ∈ (touching B).filter (fun p => z ∈ plaqLinks p), xp nr p (splice B U ξ)

def psiPartB (β : ℝ) (B : Finset (LatticeLink d N)) (z : LatticeLink d N) (U ξ : GaugeConnection Gr d N) : ℝ :=
  ∑ p ∈ (touching B).filter (fun p => z ∉ plaqLinks p), β * xp nr p (splice B U ξ)

theorem logWB_eq (β : ℝ) (B : Finset (LatticeLink d N)) (z : LatticeLink d N) (U : GaugeConnection Gr d N) :
    logWB nr β B U = fun ξ => β * fPartB nr B z U ξ + psiPartB nr β B z U ξ := by
  funext ξ
  unfold logWB fPartB psiPartB
  rw [mul_sum, sum_filter_add_sum_filter_not]

theorem psiPartB_update {B : Finset (LatticeLink d N)} {z : LatticeLink d N} (hz : z ∉ B) (β : ℝ)
    (U : GaugeConnection Gr d N) (s : Gr) : psiPartB nr β B z (Function.update U z s) = psiPartB nr β B z U := by
  funext ξ
  unfold psiPartB
  refine sum_congr rfl fun p hp => ?_
  simp only [mem_filter] at hp
  rw [splice_update_left hz]
  have hx : xp nr p (Function.update (splice B U ξ) z s) = xp nr p (splice B U ξ) := by
    have hh : plaquetteHolonomy (Function.update (splice B U ξ) z s) p = plaquetteHolonomy (splice B U ξ) p :=
      plaquetteHolonomy_dependsOn p _ _ fun l hl => by
        have : l ≠ z := fun h => hp.2 (h ▸ hl)
        simp [Function.update_of_ne this]
    unfold xp
    rw [hh]
  rw [hx]

theorem abs_fPartB_le (B : Finset (LatticeLink d N)) (z : LatticeLink d N) (U ξ : GaugeConnection Gr d N) :
    |fPartB nr B z U ξ| ≤ (((touching B).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * (nr : ℝ) := by
  unfold fPartB
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ (touching B).filter (fun p => z ∈ plaqLinks p), |xp nr p (splice B U ξ)|
      ≤ ∑ _p ∈ (touching B).filter (fun p => z ∈ plaqLinks p), (nr : ℝ) :=
        sum_le_sum fun p _ => abs_xp_le GaugeRep.unitary_rep p _
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem abs_logWB_le (β : ℝ) (B : Finset (LatticeLink d N)) (U ξ : GaugeConnection Gr d N) :
    |logWB nr β B U ξ| ≤ ((touching B).card : ℝ) * (|β| * (nr : ℝ)) := by
  unfold logWB
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ touching B, |β * xp nr p (splice B U ξ)| ≤ ∑ _p ∈ touching B, |β| * (nr : ℝ) :=
        sum_le_sum fun p _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_xp_le GaugeRep.unitary_rep p _) (abs_nonneg _)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem abs_psiPartB_le (β : ℝ) (B : Finset (LatticeLink d N)) (z : LatticeLink d N) (U ξ : GaugeConnection Gr d N) :
    |psiPartB nr β B z U ξ| ≤ ((touching B).card : ℝ) * (|β| * (nr : ℝ)) := by
  unfold psiPartB
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ (touching B).filter (fun p => z ∉ plaqLinks p), |β * xp nr p (splice B U ξ)|
      ≤ ∑ _p ∈ touching B, |β| * (nr : ℝ) := by
        refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => abs_nonneg _).trans ?_
        exact sum_le_sum fun p _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_xp_le GaugeRep.unitary_rep p _) (abs_nonneg _)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem measurable_fPartB (B : Finset (LatticeLink d N)) (z : LatticeLink d N) (U : GaugeConnection Gr d N) :
    Measurable (fPartB nr B z U) :=
  Finset.measurable_sum _ fun p _ => (measurable_xp GaugeRep.continuous_rep p).comp (measurable_splice_right B U)

theorem measurable_psiPartB (β : ℝ) (B : Finset (LatticeLink d N)) (z : LatticeLink d N)
    (U : GaugeConnection Gr d N) : Measurable (psiPartB nr β B z U) :=
  Finset.measurable_sum _ fun p _ =>
    measurable_const.mul ((measurable_xp GaugeRep.continuous_rep p).comp (measurable_splice_right B U))

theorem measurable_logWB (β : ℝ) (B : Finset (LatticeLink d N)) (U : GaugeConnection Gr d N) :
    Measurable (logWB nr β B U) :=
  Finset.measurable_sum _ fun p _ =>
    measurable_const.mul ((measurable_xp GaugeRep.continuous_rep p).comp (measurable_splice_right B U))

theorem influence_block {β : ℝ} (hβ : 0 ≤ β) (B : Finset (LatticeLink d N)) {z : LatticeLink d N} (hz : z ∉ B)
    (U : GaugeConnection Gr d N) (s : Gr) {F : GaugeConnection Gr d N → ℝ} (hF : BM F) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ x y, F x - F y ≤ D) :
    |∫ ξ, F ξ ∂(gaugeSpec (G := Gr) nr (fun x => Real.exp (β * x)) B U) -
        ∫ ξ, F ξ ∂(gaugeSpec (G := Gr) nr (fun x => Real.exp (β * x)) B (Function.update U z s))| ≤
      D * Real.tanh ((((touching B).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * (nr : ℝ) * β) := by
  set U' := Function.update U z s
  set π := prodMeasure (ι := LatticeLink d N) (haarG Gr)
  rw [gaugeSpec_eq_gibbs_block, gaugeSpec_eq_gibbs_block]
  obtain ⟨C, hC⟩ := hF.bdd
  have hψ : psiPartB nr β B z U' = psiPartB nr β B z U := psiPartB_update nr hz β U s
  have htv : ∀ V V' : GaugeConnection Gr d N, psiPartB nr β B z V' = psiPartB nr β B z V →
      tv (gibbs π (logWB nr β B V)) (gibbs π (logWB nr β B V')) ≤
        Real.tanh ((((touching B).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * (nr : ℝ) * β) := by
    intro V V' hVV'
    rw [logWB_eq nr β B z V, logWB_eq nr β B z V', hVV']
    exact tv_single_link_le_tanh π (measurable_fPartB nr B z V) (measurable_fPartB nr B z V')
      (measurable_psiPartB nr β B z V) (n := (((touching B).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * (nr : ℝ))
      hβ (abs_fPartB_le nr B z V) (abs_fPartB_le nr B z V') (abs_psiPartB_le nr β B z V)
  exact abs_integral_gibbs_sub_le π (measurable_logWB nr β B U) (measurable_logWB nr β B U')
    (abs_logWB_le nr β B U) (abs_logWB_le nr β B U') hF.meas hC hD0 hD (htv U U' hψ) (htv U' U hψ.symm)

end Block

section Lifted

variable {N : ℕ} [NeZero N]

theorem cellPre_id (b : Finset (LatticeLink d N)) : cellPre (id : LatticeLink d N → LatticeLink d N) b = b := by
  ext e; simp [cellPre]

theorem cellLift_id_update (ξ : GaugeConnection Gr d N) (y : LatticeLink d N) (t : Gr) :
    cellLift (id : LatticeLink d N → LatticeLink d N) (1 : Gr) (Function.update ξ y t) =
      Function.update (cellLift (id : LatticeLink d N → LatticeLink d N) (1 : Gr) ξ) y
        (fun e => if e = y then t else 1) := by
  funext c e
  by_cases hc : c = y
  · subst hc
    by_cases he : e = c <;> simp [cellLift, he]
  · by_cases he : e = c
    · subst he
      simp [cellLift, hc]
    · simp [cellLift, he, hc]

theorem lifted_influence_id {β : ℝ} (hβ : 0 ≤ β) (b : Finset (LatticeLink d N)) (hb : b.Nonempty)
    {z : LatticeLink d N} (hz : z ∉ b) :
    IsInfluenceBound b (wilsonBoxSpec Gr nr (id : LatticeLink d N → LatticeLink d N) β b) z
      ((b.card : ℝ) *
        Real.tanh ((((touching b).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * (nr : ℝ) * β)) := by
  intro W s F L hF hdep hosc
  obtain ⟨y0, hy0⟩ := hb
  have hL : 0 ≤ L := by
    have := hosc W y0 (W y0) hy0
    rw [Function.update_eq_self, sub_self, abs_zero] at this
    exact this
  set ρ : GaugeConnection Gr d N := fun _ => 1
  set G : GaugeConnection Gr d N → ℝ := fun U' => F (cellLift id (1 : Gr) (splice b ρ U')) with hG
  -- the function does not see the boundary
  have hGW : ∀ (W' : LatticeLink d N → (LatticeLink d N → Gr)) U',
      F (liftMap id (1 : Gr) b b ρ W' U') = G U' := by
    intro W' U'
    exact hdep _ _ fun i hi => splice_of_mem hi _ _
  have hmG : Measurable G := hF.meas.comp ((measurable_cellLift id (1 : Gr)).comp (measurable_splice_right b ρ))
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
    · simp only [hy, ite_true, hG]
      rw [splice_update_right hy, cellLift_id_update]
      exact hosc _ y _ hy
    · simp only [hy, ite_false]
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
  have hσ' : cellProj (id : LatticeLink d N → LatticeLink d N) (Function.update W z s) =
      Function.update (cellProj (id : LatticeLink d N → LatticeLink d N) W) z (s z) := by
    funext e
    by_cases he : e = z
    · subst he; simp [cellProj]
    · simp [cellProj, he]
  have hb' : ∀ W' : LatticeLink d N → (LatticeLink d N → Gr),
      ∫ ξ, F ξ ∂(wilsonBoxSpec Gr nr (id : LatticeLink d N → LatticeLink d N) β b W') =
        ∫ U', G U' ∂(gaugeSpec (G := Gr) nr (fun x => Real.exp (β * x)) b (cellProj id W')) := by
    intro W'
    unfold wilsonBoxSpec liftSpec
    rw [cellPre_id, integral_map (measurable_liftMap id (1 : Gr) b b ρ W').aemeasurable hF.meas.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun U' => hGW W' U')
  rw [hb', hb', hσ']
  have := influence_block nr hβ b hz (cellProj id W) (s z) hbG hDnn hD
  calc _ ≤ ((b.card : ℝ) * L) * Real.tanh ((((touching b).filter (fun p => z ∈ plaqLinks p)).card : ℝ) *
        (nr : ℝ) * β) := this
    _ = _ := by ring

end Lifted

theorem anchorG_nonneg (d : ℕ) : 0 ≤ anchorG d := Nat.cast_nonneg _

/-! ## Counting: the box of one site -/

section Count

variable {N : ℕ} [NeZero N]

/-- The anchor influence numbers: `anchorK d · tanh(nr β)` at the positions within distance `1`, `0` elsewhere
(`24 tanh(2β)` for SU(2), `d = 4`). -/
def kapAnchor (β : ℝ) (u : FinLatticeSites d N) : ℝ :=
  if siteDist u 0 ≤ 1 then anchorK d * Real.tanh (nr * β) else 0

theorem kapAnchor_nonneg {β : ℝ} (hβ : 0 ≤ β) (u : FinLatticeSites d N) : 0 ≤ kapAnchor nr β u := by
  unfold kapAnchor
  split_ifs
  · exact mul_nonneg (anchorK_nonneg d) (tanh_nonneg (mul_nonneg (Nat.cast_nonneg nr) hβ))
  · exact le_rfl

theorem boxBlock_zero_site (t : FinLatticeSites d N) (l : LatticeLink d N) :
    l ∈ boxBlock ({0} : Finset (FinLatticeSites d N)) t ↔ l.site = t := by
  simp [boxBlock, sub_eq_zero]

theorem boxBlock_zero_nonempty (t : FinLatticeSites d N) :
    (boxBlock ({0} : Finset (FinLatticeSites d N)) t).Nonempty :=
  ⟨⟨t, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩, (boxBlock_zero_site t _).2 rfl⟩

/-- **The exact influence number is below the anchor number**, for the box of one site or any sub-block of it
(a cut box). -/
theorem kexact_le {β : ℝ} (hβ : 0 ≤ β) (t : FinLatticeSites d N) {z : LatticeLink d N}
    (B : Finset (LatticeLink d N)) (hB : B ⊆ boxBlock ({0} : Finset (FinLatticeSites d N)) t)
    (_hz : z ∉ boxBlock ({0} : Finset (FinLatticeSites d N)) t) :
    (B.card : ℝ) *
      Real.tanh ((((touching B).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * (nr : ℝ) * β) ≤
        kapAnchor nr β (z.site - t) := by
  set m := ((touching B).filter (fun p => z ∈ plaqLinks p)).card with hm
  have hcard : (B.card : ℝ) ≤ d := by
    have := (card_le_card hB).trans (card_boxBlock ({0} : Finset (FinLatticeSites d N)) t)
    simp only [card_singleton, mul_one] at this
    exact_mod_cast this
  have hm6 : (m : ℝ) ≤ ((2 * (d - 1) : ℕ) : ℝ) := by
    have h1 : m ≤ (plaqsAt z).card := by
      refine card_le_card fun p hp => ?_
      simp only [mem_filter] at hp
      simp [plaqsAt, hp.2]
    have h2 := OneScale.SingleLink.card_plaqsAt_le (d := d) (N := N) z
    exact_mod_cast h1.trans h2
  have hnr : 0 ≤ (nr : ℝ) * β := mul_nonneg (Nat.cast_nonneg nr) hβ
  have ht0 : 0 ≤ Real.tanh ((nr : ℝ) * β) := tanh_nonneg hnr
  have hcast : (m : ℝ) * (nr : ℝ) * β = (m : ℝ) * ((nr : ℝ) * β) := by ring
  have hkey : Real.tanh ((m : ℝ) * (nr : ℝ) * β) ≤ ((2 * (d - 1) : ℕ) : ℝ) * Real.tanh ((nr : ℝ) * β) := by
    rw [hcast]
    exact (tanh_nat_mul_le hnr m).trans (mul_le_mul_of_nonneg_right hm6 ht0)
  have hnn : 0 ≤ Real.tanh ((m : ℝ) * (nr : ℝ) * β) := tanh_nonneg (by positivity)
  by_cases hm0 : m = 0
  · have : ((m : ℕ) : ℝ) = 0 := by rw [hm0]; simp
    rw [this]
    simp only [zero_mul, Real.tanh_zero, mul_zero]
    exact kapAnchor_nonneg nr hβ _
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
    simp only [kapAnchor, h2, ite_true]
    calc (B.card : ℝ) * Real.tanh ((m : ℝ) * (nr : ℝ) * β)
        ≤ (d : ℝ) * (((2 * (d - 1) : ℕ) : ℝ) * Real.tanh ((nr : ℝ) * β)) :=
          mul_le_mul hcard hkey hnn (Nat.cast_nonneg d)
      _ = anchorK d * Real.tanh ((nr : ℝ) * β) := by unfold anchorK; push_cast; ring

/-- **The one-box sum at the anchor**: with `γ₀ = anchorG d · tanh(nr β)` (`1944 tanh(2β)` for `d = 4`). -/
theorem oneBoxSum_anchor {β : ℝ} (hβ : 0 ≤ β) {lam : ℝ} (hlam : 0 ≤ lam) :
    OneBoxSum (kapAnchor nr β) (boxReach ({0} : Finset (FinLatticeSites d N))) {0} lam
      (anchorG d * Real.tanh ((nr : ℝ) * β) * Real.exp (lam * 1)) := by
  have ht0 : 0 ≤ Real.tanh ((nr : ℝ) * β) := tanh_nonneg (mul_nonneg (Nat.cast_nonneg nr) hβ)
  refine oneBoxSum_of_finiteRange (U := FinLatticeSites d N) (E₁ := 1) hlam (kapAnchor_nonneg nr hβ) ?_ ?_
  · intro u hu
    unfold kapAnchor at hu
    have hu' : siteDist u 0 ≤ 1 := by
      by_contra hc; simp [hc] at hu
    unfold boxReach
    simp only [Finset.sup_singleton]
    exact_mod_cast hu'
  · calc ∑ u ∈ univ.filter (fun u => u ∉ ({0} : Finset (FinLatticeSites d N))), kapAnchor nr β u
        ≤ ∑ u : FinLatticeSites d N, kapAnchor nr β u :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun u _ _ => kapAnchor_nonneg nr hβ u
      _ = ((univ.filter (fun u : FinLatticeSites d N => siteDist u 0 ≤ 1)).card : ℝ) *
            (anchorK d * Real.tanh ((nr : ℝ) * β)) := by
          simp only [kapAnchor, Finset.sum_ite, sum_const, nsmul_eq_mul, mul_zero, add_zero]
      _ ≤ (3 : ℝ) ^ d * (anchorK d * Real.tanh ((nr : ℝ) * β)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_near_le) (mul_nonneg (anchorK_nonneg d) ht0)
      _ = anchorG d * Real.tanh ((nr : ℝ) * β) * (({0} : Finset (FinLatticeSites d N)).card : ℝ) := by
          rw [anchorG_eq]; simp; ring

end Count

/-! ## The tuning with one lattice step per cell -/

section Tune

/-- Transport a link along an equality of the torus size. -/
def castLink {N M : ℕ} (h : N = M) (e : LatticeLink d N) : LatticeLink d M := h ▸ e

theorem castLink_refl {N : ℕ} : castLink (d := d) (rfl : N = N) = (id : LatticeLink d N → LatticeLink d N) := rfl

theorem linkDist_castLink {N M : ℕ} [NeZero N] [NeZero M] (h : N = M) (e e' : LatticeLink d N) :
    linkDist (castLink h e) (castLink h e') = linkDist e e' := by
  subst h; rfl

/-- The influence bounds of the anchor, for cells that are single links (the transport along `N = M` is the
identity). -/
theorem anchor_influence {N M : ℕ} [NeZero N] [NeZero M] (h : N = M) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ t z, z ∉ boxBlock ({0} : Finset (FinLatticeSites d M)) t →
      IsInfluenceBoundOn (ActAdm (liftAct (castLink (d := d) h) (gaugeAct N))
          (boxBlock ({0} : Finset (FinLatticeSites d M)) t))
        (boxBlock ({0} : Finset (FinLatticeSites d M)) t)
        (wilsonBoxSpec Gr nr (castLink (d := d) h) β (boxBlock ({0} : Finset (FinLatticeSites d M)) t)) z
        (kapAnchor nr β (z.site - t)) := by
  subst h
  intro t z hz
  rw [castLink_refl]
  exact isInfluenceBoundOn_of (isInfluenceBound_mono (boxBlock_zero_nonempty t)
    (lifted_influence_id nr hβ _ (boxBlock_zero_nonempty t) hz) (kexact_le nr hβ t _ subset_rfl hz))

section Explicit

variable (Gr) (d)

/-- **The strong-coupling anchor: `WilsonOneBox` is non-empty.** Along a tuning with one lattice step per cell
(`T.ℓ k = 1`) and bare couplings with `0 ≤ β_k` and `anchorG d · tanh(nr β_k) ≤ g < 1`, the one-box criterion with the
actual Wilson box law holds, with the box a single site (`Λ₀ = {0}`, `n_max = 1`, `D₀ = 0`) and `γ = g e^{λ} < 1`. -/
theorem wilsonOneBox_strong (T : Tuning) (hℓ : ∀ k, T.ℓ k = 1) {g : ℝ} (hg : g < 1)
    (hβ : ∀ k, 0 ≤ T.β k ∧ anchorG d * Real.tanh ((nr : ℝ) * T.β k) ≤ g) : WilsonOneBox Gr nr d T := by
  have hside : ∀ k j, T.side k j = coarseSide j := fun k j => by simp [Tuning.side, coarseSide, hℓ k]
  have hg0 : 0 ≤ g := by
    obtain ⟨h0, h1⟩ := hβ 0
    exact le_trans (mul_nonneg (anchorG_nonneg d) (tanh_nonneg (mul_nonneg (Nat.cast_nonneg nr) h0))) h1
  obtain ⟨lam, hlam, hlg⟩ := exists_rate hg0 hg
  have ha : ∀ k, T.a k = T.L₁ := fun k => by simp [Tuning.a, hℓ k]
  refine ⟨fun k j => castLink (hside k j), 0, 0, ⟨fun k j e e' => ?_, fun k j e e' => ?_⟩, lam, g * Real.exp lam, 0, 1,
    hlam, by positivity, hlg, 0, fun k _ j => ?_⟩
  · rw [linkDist_castLink, ha k, add_zero]
  · rw [linkDist_castLink, ha k, mul_zero, add_zero]
  · refine ⟨{0}, kapAnchor nr (T.β k), by simp, by simp, by simp [siteDist_self],
      anchor_influence nr (hside k j) (hβ k).1, ?_⟩
    have h1 := oneBoxSum_anchor nr (d := d) (N := coarseSide j) (hβ k).1 hlam.le
    unfold OneBoxSum at h1 ⊢
    refine h1.trans ?_
    rw [mul_one] at h1 ⊢
    simp only [card_singleton, Nat.cast_one, mul_one]
    exact mul_le_mul_of_nonneg_right (hβ k).2 (Real.exp_pos _).le

/-- **Constant coupling version**: `T.ℓ k = 1` and `T.β k = β` for all `k`, with `anchorG d · tanh(nr β) < 1`. -/
theorem wilsonOneBox_strong_const (T : Tuning) (hℓ : ∀ k, T.ℓ k = 1) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβk : ∀ k, T.β k = β) (hβ : anchorG d * Real.tanh ((nr : ℝ) * β) < 1) : WilsonOneBox Gr nr d T :=
  wilsonOneBox_strong Gr nr d T hℓ hβ fun k => ⟨by rw [hβk k]; exact hβ0, by rw [hβk k]⟩

end Explicit

end Tune

end Anchor


/-! ## The SU(2), `d = 4` instances -/

section Instance

variable {N : ℕ} [NeZero N]

theorem kapAnchor_four (β : ℝ) (u : FinLatticeSites 4 N) :
    kapAnchor 2 β u = ProofPhase.OneBox2.kapAnchor β u := by
  unfold kapAnchor ProofPhase.OneBox2.kapAnchor
  rw [anchorK_four]
  norm_num

/-- `ProofPhase.OneBox2.influence_block` from the generic theorem. -/
theorem influence_block_su2 {β : ℝ} (hβ : 0 ≤ β) (B : Finset (LatticeLink 4 N)) {z : LatticeLink 4 N} (hz : z ∉ B)
    (U : GaugeConnection SU2 4 N) (s : SU2) {F : GaugeConnection SU2 4 N → ℝ} (hF : BM F) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ x y, F x - F y ≤ D) :
    |∫ ξ, F ξ ∂(gaugeSpec (G := SU2) 2 (fun x => Real.exp (β * x)) B U) -
        ∫ ξ, F ξ ∂(gaugeSpec (G := SU2) 2 (fun x => Real.exp (β * x)) B (Function.update U z s))| ≤
      D * Real.tanh ((((touching B).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * ((2 : ℕ) : ℝ) * β) :=
  influence_block (Gr := SU2) 2 (d := 4) hβ B hz U s hF hD0 hD

/-- `ProofPhase.OneBox2.lifted_influence_id` from the generic theorem. -/
theorem lifted_influence_id_su2 {β : ℝ} (hβ : 0 ≤ β) (b : Finset (LatticeLink 4 N)) (hb : b.Nonempty)
    {z : LatticeLink 4 N} (hz : z ∉ b) :
    IsInfluenceBound b (ProofPhase.OneBox2.wilsonBoxSpec (id : LatticeLink 4 N → LatticeLink 4 N) β b) z
      ((b.card : ℝ) *
        Real.tanh ((((touching b).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * ((2 : ℕ) : ℝ) * β)) :=
  lifted_influence_id (Gr := SU2) 2 (d := 4) hβ b hb hz

/-- `ProofPhase.OneBox2.kexact_le` from the generic theorem (`anchorK 4 = 24`). -/
theorem kexact_le_su2 {β : ℝ} (hβ : 0 ≤ β) (t : FinLatticeSites 4 N) {z : LatticeLink 4 N}
    (B : Finset (LatticeLink 4 N)) (hB : B ⊆ boxBlock ({0} : Finset (FinLatticeSites 4 N)) t)
    (hz : z ∉ boxBlock ({0} : Finset (FinLatticeSites 4 N)) t) :
    (B.card : ℝ) *
      Real.tanh ((((touching B).filter (fun p => z ∈ plaqLinks p)).card : ℝ) * ((2 : ℕ) : ℝ) * β) ≤
        ProofPhase.OneBox2.kapAnchor β (z.site - t) := by
  rw [← kapAnchor_four]
  exact kexact_le 2 hβ t B hB hz

/-- `ProofPhase.OneBox2.oneBoxSum_anchor` from the generic theorem (`anchorG 4 = 1944`). -/
theorem oneBoxSum_anchor_su2 {β : ℝ} (hβ : 0 ≤ β) {lam : ℝ} (hlam : 0 ≤ lam) :
    OneBoxSum (ProofPhase.OneBox2.kapAnchor β) (boxReach ({0} : Finset (FinLatticeSites 4 N))) {0} lam
      (1944 * Real.tanh (2 * β) * Real.exp (lam * 1)) := by
  have h := oneBoxSum_anchor 2 (d := 4) (N := N) hβ hlam
  have e : kapAnchor (d := 4) (N := N) 2 = ProofPhase.OneBox2.kapAnchor (N := N) := by
    funext β' u; exact kapAnchor_four β' u
  rw [anchorG_four] at h
  have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  simp only [e, e2] at h
  exact h

/-- `ProofPhase.OneBox2.wilsonOneBox_strong` from the generic theorem. -/
theorem wilsonOneBox_strong_su2 (T : Tuning) (hℓ : ∀ k, T.ℓ k = 1) {g : ℝ} (hg : g < 1)
    (hβ : ∀ k, 0 ≤ T.β k ∧ 1944 * Real.tanh (2 * T.β k) ≤ g) : ProofPhase.OneBox2.WilsonOneBox T :=
  wilsonOneBox_strong SU2 2 4 T hℓ hg fun k => by
    obtain ⟨h0, h1⟩ := hβ k
    refine ⟨h0, ?_⟩
    rw [anchorG_four]
    have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [e2]
    exact h1

/-- `ProofPhase.OneBox2.wilsonOneBox_strong_const` from the generic theorem. -/
theorem wilsonOneBox_strong_const_su2 (T : Tuning) (hℓ : ∀ k, T.ℓ k = 1) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβk : ∀ k, T.β k = β) (hβ : 1944 * Real.tanh (2 * β) < 1) : ProofPhase.OneBox2.WilsonOneBox T :=
  wilsonOneBox_strong_su2 T hℓ hβ fun k => ⟨by rw [hβk k]; exact hβ0, by rw [hβk k]⟩

example : @ProofPhase.OneBox2.influence_block = @influence_block_su2 := rfl
example : @ProofPhase.OneBox2.lifted_influence_id = @lifted_influence_id_su2 := rfl

end Instance

end ProofPhase.General
