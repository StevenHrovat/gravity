/-
Proof phase, cycle 7, workstream 1 (c7c-onebox): the one-box criterion on the torus; the `L_*` law route
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c7c-onebox/NOTE.md`, sections 1, 2 and 4.
-/

import ProofPhase.OneBox.Criterion
import ProofPhase.V4.Top

/-!
# The one-box criterion on the 4D torus, and the route through `LawGapBddW`

**Boxes on the torus.** On `(ℤ/M)⁴` the blocks are the translates `Λ₀ + t` of one box `Λ₀` of sites; a block owns all
links (or cells) based at its sites (`boxBlock`). The relative position of a link `x` to the block `t` is
`x.site − t`, bijective in `t` (`isBoxFamily_torus`). The growth exponent is the reach `Ê(u) = max_{u' ∈ Λ₀} d(u, u')`
(`boxReach`), the block diameter is the diameter of `Λ₀`, block sizes are `≤ 4|Λ₀|`.

**Finite range.** `oneBoxSum_of_finiteRange`: an unweighted check `∑_{u ∉ Λ₀} κ(u) ≤ γ₀ |Λ₀|` with influences that
vanish beyond reach `E₁` gives the weighted one-box sum with `γ = γ₀ e^{λ E₁}`: choose `λ > 0` small. The Wilson box
specification has range one cell, so the numerics only has to check the unweighted sum.

**The law route** (`OneBoxLaw ρ λ`): a family of laws `ρ k j` on tori `(ℤ/M_j)⁴` whose box specifications satisfy the
one-box sum, uniformly in `k ≥ k₀` and `j`, with box size `≤ n_max` and box diameter `≤ D₀`. Then
`lawGapBddW_of_oneBoxLaw`: `OneBoxLaw ρ λ ⇒ LawGapBddW ρ λ` (influences tested on all bounded functions; for a law with a
gauge-covariant specification this costs nothing, NOTE §3.3). For the `L_*`-blocked laws: `blockGapBddW_of_oneBoxLaw`
and `yang_mills_assembly_v4_onebox` (`OnLCP' ∧ NonTrivial ∧ OneBoxLaw (blockedLaw T B) λ ∧ ObsTransferPhysTW ⇒` the
v4 conclusions).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  ProofPhase.Torus ProofPhase.V3 ProofPhase.V4

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OneBox

/-! ## Finite range -/

/-- **Finite range turns the unweighted one-box check into the weighted one.** -/
theorem oneBoxSum_of_finiteRange {U : Type*} [Fintype U] [DecidableEq U] {κ Ehat : U → ℝ} {Λ₀ : Finset U}
    {γ₀ E₁ lam : ℝ} (hlam : 0 ≤ lam) (hκ0 : ∀ u, 0 ≤ κ u) (hrange : ∀ u, κ u ≠ 0 → Ehat u ≤ E₁)
    (hsum : ∑ u ∈ univ.filter (fun u => u ∉ Λ₀), κ u ≤ γ₀ * Λ₀.card) :
    OneBoxSum κ Ehat Λ₀ lam (γ₀ * Real.exp (lam * E₁)) := by
  unfold OneBoxSum
  have h1 : ∀ u, κ u * Real.exp (lam * Ehat u) ≤ κ u * Real.exp (lam * E₁) := by
    intro u
    by_cases hu : κ u = 0
    · simp [hu]
    · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hrange u hu) hlam)) (hκ0 u)
  calc ∑ u ∈ univ.filter (fun u => u ∉ Λ₀), κ u * Real.exp (lam * Ehat u)
      ≤ ∑ u ∈ univ.filter (fun u => u ∉ Λ₀), κ u * Real.exp (lam * E₁) := sum_le_sum fun u _ => h1 u
    _ = (∑ u ∈ univ.filter (fun u => u ∉ Λ₀), κ u) * Real.exp (lam * E₁) := by rw [sum_mul]
    _ ≤ γ₀ * Λ₀.card * Real.exp (lam * E₁) := mul_le_mul_of_nonneg_right hsum (Real.exp_pos _).le
    _ = γ₀ * Real.exp (lam * E₁) * Λ₀.card := by ring

/-! ## Boxes on the torus -/

section Torus

variable {M : ℕ} [NeZero M]

/-- The block `Λ₀ + t`: all links based at a site of the translated box. -/
def boxBlock (Λ₀ : Finset (FinLatticeSites 4 M)) (t : FinLatticeSites 4 M) : Finset (LatticeLink 4 M) :=
  univ.filter fun x => x.site - t ∈ Λ₀

/-- The reach of the box from the relative position `u`: `max_{u' ∈ Λ₀} d(u, u')`. -/
def boxReach (Λ₀ : Finset (FinLatticeSites 4 M)) (u : FinLatticeSites 4 M) : ℝ :=
  ((Λ₀.sup fun u' => siteDist u u' : ℕ) : ℝ)

theorem siteDist_sub_right (x y t : FinLatticeSites 4 M) : siteDist (x - t) (y - t) = siteDist x y := by
  unfold siteDist
  congr 1
  funext i
  simp [Pi.sub_apply, sub_sub_sub_cancel_right]

/-- The translates of a box form a box family on the links of the torus. -/
theorem isBoxFamily_torus (Λ₀ : Finset (FinLatticeSites 4 M)) :
    IsBoxFamily (boxBlock Λ₀) (fun t (x : LatticeLink 4 M) => x.site - t) Λ₀ where
  bij x := ⟨fun t t' h => by simpa using h, fun u => ⟨x.site - u, by simp⟩⟩
  mem t x := by simp [boxBlock]

theorem boxBlock_reach (Λ₀ : Finset (FinLatticeSites 4 M)) (t : FinLatticeSites 4 M) (x y : LatticeLink 4 M)
    (hy : y ∈ boxBlock Λ₀ t) : linkDist x y ≤ boxReach Λ₀ (x.site - t) := by
  unfold linkDist boxReach
  rw [← siteDist_sub_right x.site y.site t]
  exact_mod_cast Finset.le_sup (f := fun u' => siteDist (x.site - t) u') (mem_filter.1 hy).2

theorem boxBlock_diam {Λ₀ : Finset (FinLatticeSites 4 M)} {D₀ : ℝ}
    (hD : ∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) (t : FinLatticeSites 4 M) :
    ∀ x ∈ boxBlock Λ₀ t, ∀ y ∈ boxBlock Λ₀ t, linkDist x y ≤ D₀ := by
  intro x hx y hy
  unfold linkDist
  rw [← siteDist_sub_right x.site y.site t]
  exact hD _ (mem_filter.1 hx).2 _ (mem_filter.1 hy).2

theorem card_boxBlock (Λ₀ : Finset (FinLatticeSites 4 M)) (t : FinLatticeSites 4 M) :
    (boxBlock Λ₀ t).card ≤ 4 * Λ₀.card := by
  have h := Finset.card_le_card_of_injOn (s := boxBlock Λ₀ t) (t := Λ₀ ×ˢ (univ : Finset (Fin 4)))
    (fun x => (x.site - t, x.dir)) (fun x hx => by
      simp only [coe_product, coe_univ, Set.mem_prod, mem_coe, Set.mem_univ, and_true]
      exact (mem_filter.1 hx).2)
    (fun x _ y _ e => by
      simp only [Prod.mk.injEq, sub_left_inj] at e
      cases x; cases y; simp_all)
  rw [card_product, card_univ, Fintype.card_fin] at h
  linarith

end Torus

/-! ## The law route -/

section Law

variable {M : ℕ → ℕ} [∀ j, NeZero (M j)]

/-- The trivial action (no gauge group): every function is invariant and admissible. -/
def noAct {ι S : Type*} : Empty → ι → S → S := fun γ => γ.elim

theorem isInfluenceBoundOn_noAct {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {B : Finset ι}
    {q : (ι → S) → Measure (ι → S)} {z : ι} {k : ℝ} (h : IsInfluenceBound B q z k) :
    IsInfluenceBoundOn (ActAdm (noAct (ι := ι) (S := S)) B) B q z k :=
  isInfluenceBoundOn_of h

/-- **The one-box criterion for a family of laws on tori** (gap strength; the open input of this route). Uniformly in
`k ≥ k₀` and `j`: a box `Λ₀` of at most `n_max` sites and diameter `≤ D₀`, a block specification of `ρ k j` whose blocks
are the translates of `Λ₀`, box influences `κ(u)` from the relative outside positions `u` (tested on bounded functions
of the box), and the one-box sum `∑_{u ∉ Λ₀} κ(u) e^{λ Ê(u)} ≤ γ |Λ₀|`, `γ < 1`. -/
def OneBoxLaw (ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))) (lam : ℝ) : Prop :=
  ∃ (γ D₀ : ℝ) (nmax : ℕ), 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
    ∃ (Λ₀ : Finset (FinLatticeSites 4 (M j))) (κ : FinLatticeSites 4 (M j) → ℝ)
      (P : BlockSpec (ρ k j) (FinLatticeSites 4 (M j))),
      1 ≤ Λ₀.card ∧ Λ₀.card ≤ nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) ∧
      (∀ t, P.block t = boxBlock Λ₀ t) ∧
      (∀ t z, z ∉ P.block t → IsInfluenceBound (P.block t) (P.spec t) z (κ (z.site - t))) ∧
      OneBoxSum κ (boxReach Λ₀) Λ₀ lam γ

/-- **One box gives the W₁ gap (bounded form) in every volume** (S). Constant `2 · 4 n_max e^{λD₀}/(1 − γ)`. -/
theorem lawGapBddW_of_oneBoxLaw {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ} (hlam : 0 ≤ lam)
    (hρ : ∀ k j, IsProbabilityMeasure (ρ k j)) (h : OneBoxLaw ρ lam) : LawGapBddW ρ lam := by
  obtain ⟨γ, D₀, nmax, hγ0, hγ1, k₀, H⟩ := h
  have hg1 : 0 < 1 - γ := by linarith
  refine ⟨2 * (4 * nmax) * Real.exp (lam * D₀) / (1 - γ), by positivity, k₀,
    fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg _ hR0 hR => ?_⟩
  obtain ⟨Λ₀, κ, P, hΛ1, hΛn, hdiam, hblock, hk, hsum⟩ := H k hk j
  have := hρ k j
  have : Nonempty (LatticeLink 4 (M j)) := ⟨⟨fun _ => 0, 0⟩⟩
  have hbox : IsBoxFamily P.block (fun t (x : LatticeLink 4 (M j)) => x.site - t) Λ₀ := by
    have := isBoxFamily_torus Λ₀
    exact ⟨this.bij, fun t x => by rw [hblock t]; exact this.mem t x⟩
  have hvg : OscBound g (fun _ => (2 : ℝ)) := fun V x s =>
    (abs_sub _ _).trans (by linarith [bg V, bg (Function.update V x s)])
  have hcov := abs_cov_le_of_oneBox (a := noAct) P (fun t x => x.site - t) Λ₀ hbox hΛ1
    (fun γ => γ.elim) (fun _ γ => γ.elim) κ (boxReach Λ₀)
    (fun t z hz => isInfluenceBoundOn_noAct (hk t z hz)) (b := 4 * nmax)
    (fun t => by rw [hblock t]; exact (card_boxBlock Λ₀ t).trans (by omega))
    linkDist linkDist_self linkDist_triangle (D₀ := D₀)
    (fun t => by rw [hblock t]; exact boxBlock_diam hdiam t)
    (fun t x y _ hy => by rw [hblock t] at hy; exact boxBlock_reach Λ₀ t x y hy) hlam hγ0 hγ1 hsum
    ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩ (fun γ => γ.elim) hfA hgS hvf (by norm_num) hvg hR
  refine hcov.trans ?_
  have hS := sum_osc_nonneg hvf A
  have e1 : Real.exp (-(lam * (R - D₀))) = Real.exp (lam * D₀) * Real.exp (-(lam * R)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1]
  have hE := Real.exp_pos (lam * D₀)
  have hE' := Real.exp_pos (-(lam * R))
  have hn : ((4 * nmax : ℕ) : ℝ) = 4 * (nmax : ℝ) := by push_cast; ring
  rw [hn]
  have key : 4 * (nmax : ℝ) / (1 - γ) * (∑ x ∈ A, vf x) * 2 ≤
      2 * (4 * nmax) / (1 - γ) * (1 + ∑ a ∈ A, vf a) * (1 + Lg) := by
    have h0 : 0 ≤ 4 * (nmax : ℝ) / (1 - γ) := by positivity
    have h1 : (∑ x ∈ A, vf x) ≤ (1 + ∑ a ∈ A, vf a) * (1 + Lg) := by nlinarith
    calc 4 * (nmax : ℝ) / (1 - γ) * (∑ x ∈ A, vf x) * 2
        = 2 * (4 * nmax) / (1 - γ) * (∑ x ∈ A, vf x) := by ring
      _ ≤ 2 * (4 * nmax) / (1 - γ) * ((1 + ∑ a ∈ A, vf a) * (1 + Lg)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  calc 4 * (nmax : ℝ) / (1 - γ) * (∑ x ∈ A, vf x) * 2 * (Real.exp (lam * D₀) * Real.exp (-(lam * R)))
      = (4 * (nmax : ℝ) / (1 - γ) * (∑ x ∈ A, vf x) * 2) * Real.exp (lam * D₀) * Real.exp (-(lam * R)) := by ring
    _ ≤ (2 * (4 * nmax) / (1 - γ) * (1 + ∑ a ∈ A, vf a) * (1 + Lg)) * Real.exp (lam * D₀) *
          Real.exp (-(lam * R)) := by gcongr
    _ = 2 * (4 * nmax) * Real.exp (lam * D₀) / (1 - γ) * (1 + ∑ a ∈ A, vf a) * (1 + Lg) *
          Real.exp (-(lam * R)) := by ring

end Law

/-- **The `L_*` blocked laws: one box gives the bounded W₁ block gap** (S). -/
theorem blockGapBddW_of_oneBoxLaw {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : OneBoxLaw (M := coarseSide) (blockedLaw T B) lam) : BlockGapBddW T B lam := by
  refine (blockGapBddW_iff_lawGapBddW B lam).2 (lawGapBddW_of_oneBoxLaw hlam (fun k j => ?_) h)
  have := UV.ymProb T k j
  exact (Measure.isProbabilityMeasure_map_iff (B k j).meas.aemeasurable).2 inferInstance

/-- **Assembly v4 with the one-box criterion for the `L_*` theory as the infrared input** (S). -/
theorem yang_mills_assembly_v4_onebox {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (B : BlockingFamily T)
    {lam : ℝ} (hlam : 0 < lam) (hIR : OneBoxLaw (M := coarseSide) (blockedLaw T B) lam)
    (hUV : ObsTransferPhysTW T B) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T :=
  yang_mills_assembly_v4_bdd hL hN B hlam (blockGapBddW_of_oneBoxLaw B hlam.le hIR) hUV

end ProofPhase.OneBox
