/-
Proof phase, cycle 5, workstream 3 (c5c-repair): reference actions of general support and "eventually ≤ ε₀" closeness,
replacing the plaquette-only `H1LocalLipW ∧ LimitDprimeW` pair (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5c-repair/NOTE.md`, section 2.
-/

import ProofPhase.Repair.WeightedW

/-!
# General-support reference actions and the repaired openness lemma

The review `c4-fable/REVIEW.md` §1.2: `V3.H1LocalLipW T B Vk Vinf` takes a limit action `Vinf` whose terms live on single
plaquettes and asks the W₁ deviations of the blocked actions from it to tend to zero (with a finite range). The refit
measured a rectangle coupling at about 200 standard errors, so no plaquette-only `Vinf` is the limit of the true blocked
actions; and the openness argument never needed a limit, only "eventually `≤ ε₀`" with `ε₀ < 1 − γ`.

**What is already general.** The Gibbs layer of the library (`Attempts.R3.Potential`, `gibbsMeasure`, `siteSpec`) takes
an arbitrary finite family of terms with arbitrary supports, and `CoarsePot j` (one term per finite set of coarse links)
is the general-support class itself. Only `Vinf` (plaquette-indexed) and `LimitDprimeW` (range 1) were plaquette-bound.

* `regroup supp V` (S): any family of terms with supports `supp x` (plaquettes, rectangles, any loops, any finite sets)
  regrouped as one term per support set. `potential_regroup`, `siteLog_regroup`, **`siteSpec_regroup`**,
  **`gibbsMeasure_regroup`**: the regrouped potential is a `Potential (fun A => A)` with the **same** Gibbs measure and the
  **same** single-site specifications, hence the same influence coefficients (`siteInfluenceW_regroup`). So a fitted
  action with rectangles and larger loops is a `CoarsePot` with no loss.
* **`RefDprimeWw Vref λ γ`** (named hypothesis; replaces `Certified.LimitDprimeW`): a reference coarse action of general
  support (`Vref j : CoarsePot j`, any `j`) whose single-link W₁ influences have weighted column sums `≤ γ` at rate `λ`,
  in every volume.
* **`CloseWw T B Vref λ ε₀`** (named hypothesis, open; replaces `V3.H1LocalLipW`): **from some level on**, in every
  volume, the blocked law is the Gibbs measure of a bounded coarse potential whose single-link W₁ boundary derivatives
  differ from those of `Vref` by coefficients with weighted column sums `≤ ε₀`. No limit, no range, no plaquette clause.
* **`levelDprimeWw_of_ref`** (S, the repaired openness lemma): `RefDprimeWw ∧ CloseWw` with `γ + ε₀ < 1` give
  `LevelDprimeWw T B λ`.
* **`ref_close_of_h1LocalLip`** (S): the old pair `H1LocalLipW ∧ LimitDprimeW` implies the new pair (with the plaquette
  action regrouped, at an explicit rate `λ > 0`): nothing proved through the old pair is lost.
* `refDprimeWw_of_limitDprimeW` (S): every `LimitDprimeW` action (the certified two-coupling window, the certified
  measured box) is a weighted reference action at every rate `λ ≥ 0` with `γ e^{λ}`.
* `refDprimeWw_wilson` (S, under the computational input `CertifiedAdjointW`): the **Wilson action** at strong coupling
  (`|β_F| ≤ 0.0685`, `β_A = 0`) satisfies `RefDprimeWw` at some `λ > 0`: the model case of satisfiability.

**Which is right: repair the pair or delete it (draft S5)?** Both, in different places (NOTE §2.3). As an *input of the
top theorem* the pair should go: `LevelDprimeWw` is weaker (implied by the pair, `levelDprimeWw_of_ref`) and says exactly
what is used. As a *lemma* the repaired pair is worth keeping: it is the only bridge from a certificate about a fixed
fitted action to the level condition, and its "eventually `≤ ε₀`" closeness is the place where a rare-defect version
(c5d) will plug in.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.LinkDist ProofPhase.Certified

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Repair

/-! ## 1. Regrouping a potential of arbitrary supports -/

section Regroup

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {X : Type*} [Fintype X]

/-- **Regrouping:** one term per support set, the sum of the terms with that support. -/
def regroup (supp : X → Finset ι) (V : X → (ι → S) → ℝ) : Finset ι → (ι → S) → ℝ :=
  fun A σ => ∑ x ∈ univ.filter (fun x => supp x = A), V x σ

theorem potential_regroup {supp : X → Finset ι} {V : X → (ι → S) → ℝ} (hV : Attempts.R3.Potential supp V) :
    Attempts.R3.Potential (fun A => A) (regroup supp V) where
  meas A := Finset.measurable_sum _ fun x _ => hV.meas x
  bdd := by
    obtain ⟨K, hK⟩ := hV.bdd
    refine ⟨(Fintype.card X : ℝ) * |K|, fun A σ => ?_⟩
    show |∑ x ∈ univ.filter (fun x => supp x = A), V x σ| ≤ _
    refine (Attempts.R3.abs_sum_le_card hK σ).trans ?_
    calc ((univ.filter (fun x => supp x = A)).card : ℝ) * K
        ≤ (univ.filter (fun x => supp x = A)).card * |K| :=
          mul_le_mul_of_nonneg_left (le_abs_self K) (Nat.cast_nonneg _)
      _ ≤ (Fintype.card X : ℝ) * |K| :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (card_filter_le _ _).trans_eq card_univ) (abs_nonneg K)
  dep A σ σ' h := by
    unfold regroup
    refine sum_congr rfl fun x hx => hV.dep x σ σ' fun i hi => h i ?_
    rw [← (mem_filter.1 hx).2]; exact hi

/-- Regrouping does not change the summed log-weight at a site. -/
theorem siteLog_regroup (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (i : ι) (σ : ι → S) :
    Attempts.R3.siteLog (fun A => A) (regroup supp V) i σ = Attempts.R3.siteLog supp V i σ := by
  unfold Attempts.R3.siteLog regroup
  rw [← Finset.sum_fiberwise_of_maps_to (s := Attempts.R3.factorsAt supp i)
    (t := Attempts.R3.factorsAt (fun A : Finset ι => A) i) (g := supp) (fun x hx => by
      simpa [Attempts.R3.factorsAt] using hx)]
  refine sum_congr rfl fun A hA => sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [Attempts.R3.factorsAt, mem_filter, mem_univ, true_and] at hA ⊢
  constructor
  · intro h; exact ⟨h ▸ hA, h⟩
  · intro h; exact h.2

/-- Regrouping does not change the total log-weight. -/
theorem totalLog_regroup (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (σ : ι → S) :
    Attempts.R3.totalLog (regroup supp V) σ = Attempts.R3.totalLog V σ := by
  unfold Attempts.R3.totalLog regroup
  exact Finset.sum_fiberwise univ supp (fun x => V x σ)

variable (ν : Measure S) [IsProbabilityMeasure ν]

/-- **Regrouping does not change the single-site specifications.** -/
theorem siteSpec_regroup (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (i : ι) :
    Attempts.R3.siteSpec ν (fun A => A) (regroup supp V) i = Attempts.R3.siteSpec ν supp V i := by
  unfold Attempts.R3.siteSpec Attempts.R3.siteWeight
  simp_rw [siteLog_regroup]

/-- **Regrouping does not change the Gibbs measure.** -/
theorem gibbsMeasure_regroup (supp : X → Finset ι) (V : X → (ι → S) → ℝ) :
    Attempts.R3.gibbsMeasure ν (regroup supp V) = Attempts.R3.gibbsMeasure ν V := by
  unfold Attempts.R3.gibbsMeasure
  simp_rw [totalLog_regroup]

/-- Hence the same W₁ influence coefficients. -/
theorem siteInfluenceW_regroup (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (c : S → S → ℝ) (k : ι → ι → ℝ) :
    SiteInfluenceW ν (fun A => A) (regroup supp V) c k ↔ SiteInfluenceW ν supp V c k := by
  unfold SiteInfluenceW
  simp_rw [siteSpec_regroup]

end Regroup

/-- Deviation coefficients of W₁ boundary derivatives are nonnegative whenever the cost takes one positive value. -/
theorem influenceDevW_nonneg {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {c : S → S → ℝ}
    (hc0 : ∀ a b, 0 ≤ c a b) {B : Finset ι} {q q' : (ι → S) → Measure (ι → S)} {z : ι} {δ : ℝ}
    (h : OneScale.Effective.InfluenceDevW c B q q' z δ) (hpos : ∃ a b, 0 < c a b) : 0 ≤ δ := by
  obtain ⟨a, b, hab⟩ := hpos
  have h' := h (fun _ => a) b (fun _ => 0) 1 ⟨measurable_const, ⟨0, fun _ => by simp⟩⟩
    (fun _ _ _ => rfl) (fun ξ y t _ => by simpa using hc0 (ξ y) t)
  simp only [integral_zero, sub_self, abs_zero, mul_one] at h'
  exact nonneg_of_mul_nonneg_left h' hab

/-! ## 2. The reference action and eventual closeness -/

open ProofPhase.V3

/-- **D′ in weighted W₁ form for a reference coarse action of general support** (named hypothesis; replaces
`Certified.LimitDprimeW`): in every volume `j`, the single-link W₁ influences of `Vref j` (any finite supports) have
weighted column sums `≤ γ` at rate `λ`. -/
def RefDprimeWw (Vref : ∀ j, CoarsePot j) (lam γ : ℝ) : Prop :=
  ∀ j, ∃ kk : LatticeLink 4 (coarseSide j) → LatticeLink 4 (coarseSide j) → ℝ,
    SiteInfluenceW (haarG SU2) (fun A => A) (Vref j) geodSU2 kk ∧ WeightedColumnW kk linkDist lam γ

/-- **Eventual W₁ closeness to a reference action (named hypothesis, open; replaces `V3.H1LocalLipW`).** From some level
on, in every volume, the blocked law is the Gibbs measure of a bounded coarse potential (any supports) whose single-link
W₁ boundary derivatives differ from those of `Vref j` by coefficients with weighted column sums `≤ ε₀`. -/
def CloseWw (T : Tuning) (B : BlockingFamily T) (Vref : ∀ j, CoarsePot j) (lam ε₀ : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j, ∃ V : CoarsePot j,
    blockedLaw T B k j = Attempts.R3.gibbsMeasure (haarG SU2) V ∧ Attempts.R3.Potential (fun A => A) V ∧
    ∃ δ : LatticeLink 4 (coarseSide j) → LatticeLink 4 (coarseSide j) → ℝ,
      (∀ i z, z ∉ ({i} : Finset (LatticeLink 4 (coarseSide j))) →
        OneScale.Effective.InfluenceDevW geodSU2 {i}
          (Attempts.R3.siteSpec (haarG SU2) (fun A => A) (Vref j) i)
          (Attempts.R3.siteSpec (haarG SU2) (fun A => A) V i) z (δ i z)) ∧
      WeightedColumnW δ linkDist lam ε₀

/-- **The repaired openness lemma** (S): `RefDprimeWw Vref λ γ ∧ CloseWw T B Vref λ ε₀` with `γ, ε₀ ≥ 0`,
`γ + ε₀ < 1` give `LevelDprimeWw T B λ`. -/
theorem levelDprimeWw_of_ref {T : Tuning} {B : BlockingFamily T} {Vref : ∀ j, CoarsePot j} {lam γ ε₀ : ℝ}
    (hγ0 : 0 ≤ γ) (hε0 : 0 ≤ ε₀) (h1 : γ + ε₀ < 1) (href : RefDprimeWw Vref lam γ)
    (hclose : CloseWw T B Vref lam ε₀) : LevelDprimeWw T B lam := by
  obtain ⟨k₀, H⟩ := hclose
  refine ⟨γ + ε₀, by linarith, h1, k₀, fun k hk j => ?_⟩
  obtain ⟨V, hgibbs, hpot, δ, hdev, hcolδ⟩ := H k hk j
  obtain ⟨kL, hkL, hcolL⟩ := href j
  refine ⟨V, hgibbs, hpot, fun i z => kL i z + δ i z, fun i z hz => (hkL i z hz).of_devW (hdev i z hz), ?_⟩
  intro z
  have := add_le_add (hcolL z) (hcolδ z)
  simpa only [add_mul, sum_add_distrib] using this

/-- **Every `LimitDprimeW` action is a weighted reference action** (S): the plaquette action regrouped, at every rate
`λ ≥ 0`, with `γ e^{λ}` (range 1). Applies to the certified two-coupling window and the certified measured box. -/
theorem refDprimeWw_of_limitDprimeW
    {Vinf : ∀ j, LatticePlaquette 4 (coarseSide j) → GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (h : LimitDprimeW Vinf) : ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∀ lam : ℝ, 0 ≤ lam →
      RefDprimeWw (fun j => regroup (plaqSupp (N := coarseSide j)) (Vinf j)) lam (γ * Real.exp lam) := by
  obtain ⟨γ, hγ0, hγ1, hlim⟩ := h
  refine ⟨γ, hγ0, hγ1, fun lam hlam j => ?_⟩
  obtain ⟨kL, hkL, hcolL, hrangeL⟩ := hlim j
  refine ⟨kL, (siteInfluenceW_regroup _ _ _ _ _).2 hkL, ?_⟩
  have h := weightedColumn_le_of_range (siteInfluenceW_nonneg (haarG SU2) geodSU2_nonneg hkL exists_geodSU2_pos)
    linkDist hlam hcolL (D₁ := 1) (fun i z _ h => hrangeL i z h)
  rwa [mul_one] at h

/-- **The old pair implies the new pair** (S): `H1LocalLipW T B Vk Vinf ∧ LimitDprimeW Vinf` give, at an explicit rate
`λ > 0`, `RefDprimeWw` for the regrouped plaquette action and `CloseWw` with `γ + ε₀ < 1`. -/
theorem ref_close_of_h1LocalLip {T : Tuning} {B : BlockingFamily T} {Vk : ∀ j, ℕ → CoarsePot j}
    {Vinf : ∀ j, LatticePlaquette 4 (coarseSide j) → GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (h1 : H1LocalLipW T B Vk Vinf) (h2 : LimitDprimeW Vinf) :
    ∃ lam γ ε₀ : ℝ, 0 < lam ∧ 0 ≤ γ ∧ 0 ≤ ε₀ ∧ γ + ε₀ < 1 ∧
      RefDprimeWw (fun j => regroup (plaqSupp (N := coarseSide j)) (Vinf j)) lam γ ∧
      CloseWw T B (fun j => regroup (plaqSupp (N := coarseSide j)) (Vinf j)) lam ε₀ := by
  obtain ⟨hgibbs, hpot, D₁, δ, ε, hε, hdev, hcolδ, hrange⟩ := h1
  obtain ⟨γ, hγ0, hγ1, hlim⟩ := h2
  set γ'' := (1 + 3 * γ) / 4 with hγ''
  have hγ''0 : 0 ≤ γ'' := by positivity
  have hγ''1 : γ'' < 1 := by rw [hγ'']; linarith
  obtain ⟨lam₀, hlam₀, hρ₀⟩ := OneScale.SingleLink.exists_rate hγ''0 hγ''1
  set Dm := max 1 D₁
  have hDm : 0 < Dm := lt_of_lt_of_le one_pos (le_max_left _ _)
  set lam := lam₀ / Dm with hlamdef
  have hlam : 0 < lam := by positivity
  have hlD : lam * Dm = lam₀ := div_mul_cancel₀ lam₀ hDm.ne'
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((tendsto_order.1 hε).2 ((1 - γ) / 4) (by linarith))
  refine ⟨lam, γ * Real.exp lam₀, (1 - γ) / 4 * Real.exp lam₀, hlam, mul_nonneg hγ0 (Real.exp_pos _).le,
    mul_nonneg (by linarith) (Real.exp_pos _).le, ?_, ?_, ?_⟩
  · have e : γ * Real.exp lam₀ + (1 - γ) / 4 * Real.exp lam₀ = γ'' * Real.exp lam₀ := by rw [hγ'']; ring
    rw [e]; exact hρ₀
  · intro j
    obtain ⟨kL, hkL, hcolL, hrangeL⟩ := hlim j
    refine ⟨kL, (siteInfluenceW_regroup _ _ _ _ _).2 hkL, ?_⟩
    have h := weightedColumn_le_of_range (siteInfluenceW_nonneg (haarG SU2) geodSU2_nonneg hkL exists_geodSU2_pos)
      linkDist hlam.le hcolL (D₁ := Dm) (fun i z _ h => (hrangeL i z h).trans (le_max_left _ _))
    rwa [hlD] at h
  · refine ⟨k₀, fun k hk j => ⟨Vk j k, hgibbs k j, hpot j k, δ k j, fun i z hz => ?_, ?_⟩⟩
    · rw [siteSpec_regroup]; exact hdev k j i z hz
    · have hδ0 : ∀ i z, z ∉ ({i} : Finset (LatticeLink 4 (coarseSide j))) → 0 ≤ δ k j i z := fun i z hz =>
        influenceDevW_nonneg geodSU2_nonneg (hdev k j i z hz) exists_geodSU2_pos
      have h := weightedColumn_le_of_range hδ0 linkDist hlam.le (hcolδ k j) (D₁ := Dm)
        (fun i z hz h => (hrange k j i z hz h).trans (le_max_right _ _))
      rw [hlD] at h
      exact fun z => (h z).trans (mul_le_mul_of_nonneg_right (hk₀ k hk).le (Real.exp_pos _).le)

/-- **The old openness lemma, re-derived through the repaired chain** (S): `H1LocalLipW ∧ LimitDprimeW ⇒
∃ λ > 0, LevelDprimeWw T B λ` (compare `V3.levelDprimeW_of_h1LocalLip`). -/
theorem levelDprimeWw_of_h1LocalLip {T : Tuning} {B : BlockingFamily T} {Vk : ∀ j, ℕ → CoarsePot j}
    {Vinf : ∀ j, LatticePlaquette 4 (coarseSide j) → GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (h1 : H1LocalLipW T B Vk Vinf) (h2 : LimitDprimeW Vinf) : ∃ lam : ℝ, 0 < lam ∧ LevelDprimeWw T B lam := by
  obtain ⟨lam, γ, ε₀, hlam, hγ0, hε0, hsum, href, hclose⟩ := ref_close_of_h1LocalLip h1 h2
  exact ⟨lam, hlam, levelDprimeWw_of_ref hγ0 hε0 hsum href hclose⟩

/-! ## 3. Satisfiability: the Wilson action at strong coupling -/

/-- **Model case** (S, under the computational input `CertifiedAdjointW`): the Wilson action `β_F t_p` with
`|β_F| ≤ cornerF 5 = 0.0685` (`β_A = 0`) satisfies `RefDprimeWw` at some rate `λ > 0` with `γ < 1`, in every volume. -/
theorem refDprimeWw_wilson (hcert : CertifiedAdjointW) {βF : ℝ} (hF : |βF| ≤ cornerF 5) :
    ∃ lam γ : ℝ, 0 < lam ∧ 0 ≤ γ ∧ γ < 1 ∧
      RefDprimeWw (fun j => regroup (plaqSupp (N := coarseSide j)) (twoCoupling βF 0)) lam γ := by
  obtain ⟨lam, hlam, hρ⟩ := exists_rate_corner 5
  refine ⟨lam, 18 * cornerK 5 * Real.exp lam, hlam,
    mul_nonneg (mul_nonneg (by norm_num) (cornerK_nonneg 5)) (Real.exp_pos _).le, hρ, fun j => ?_⟩
  have hk := hcert 5 (coarseSide j) (two_le_coarseSide j) βF 0 (by norm_num [cornerA]) hF
  refine ⟨fun (i z : LatticeLink 4 (coarseSide j)) => cornerK 5 * (OneScale.SingleLink.common i z : ℝ),
    (siteInfluenceW_regroup _ _ _ _ _).2 hk, ?_⟩
  have h := weightedColumn_le_of_range
    (k := fun (i z : LatticeLink 4 (coarseSide j)) => cornerK 5 * (OneScale.SingleLink.common i z : ℝ))
    (fun i z _ => mul_nonneg (cornerK_nonneg 5) (Nat.cast_nonneg _)) linkDist hlam.le (D₁ := 1)
    (fun z => column_le 5 z) (fun i z _ h => dist_le_of_common 5 h)
  rwa [mul_one] at h

end ProofPhase.Repair
