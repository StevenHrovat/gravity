/-
Proof phase, generalisation phase 1: the one-box criterion on the torus `(ℤ/M)^d` for any link alphabet `G` and any
dimension `d` (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`.
-/

import ProofPhase.OneBox.Torus
import ProofPhase.General.Counting
import AreaLaw.Concrete

/-!
# The one-box criterion on the `d`-dimensional torus

The generic version of `ProofPhase.OneBox.Torus` (`oneBoxSum_of_finiteRange` there is already group- and
dimension-free). Boxes `Λ₀ + t` on `(ℤ/M)^d`, a block owns all links based at its sites, so a block has at most
`d |Λ₀|` links (`card_boxBlock`). The law route `OneBoxLaw ρ λ ⇒ LawGapBddW ρ λ` is stated for laws on
`GaugeConnection G d (M j)` with `G` any measurable alphabet and a pseudo-distance `c` on `G` for the Lipschitz class
of the test function `g` (the proof never uses the Lipschitz hypothesis). The SU(2), `d = 4` statements are
re-derived in `ProofPhase.General.Instances`.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.LinkDist
open ProofPhase.OneBox (IsBoxFamily OneBoxSum abs_cov_le_of_oneBox noAct isInfluenceBoundOn_noAct)

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Torus

variable {d M : ℕ} [NeZero M]

/-- The block `Λ₀ + t`: all links based at a site of the translated box. -/
def boxBlock (Λ₀ : Finset (FinLatticeSites d M)) (t : FinLatticeSites d M) : Finset (LatticeLink d M) :=
  univ.filter fun x => x.site - t ∈ Λ₀

/-- The reach of the box from the relative position `u`: `max_{u' ∈ Λ₀} d(u, u')`. -/
def boxReach (Λ₀ : Finset (FinLatticeSites d M)) (u : FinLatticeSites d M) : ℝ :=
  ((Λ₀.sup fun u' => siteDist u u' : ℕ) : ℝ)

theorem siteDist_sub_right (x y t : FinLatticeSites d M) : siteDist (x - t) (y - t) = siteDist x y := by
  unfold siteDist
  congr 1
  funext i
  simp [Pi.sub_apply, sub_sub_sub_cancel_right]

/-- The translates of a box form a box family on the links of the torus. -/
theorem isBoxFamily_torus (Λ₀ : Finset (FinLatticeSites d M)) :
    IsBoxFamily (boxBlock Λ₀) (fun t (x : LatticeLink d M) => x.site - t) Λ₀ where
  bij x := ⟨fun t t' h => by simpa using h, fun u => ⟨x.site - u, by simp⟩⟩
  mem t x := by simp [boxBlock]

theorem boxBlock_reach (Λ₀ : Finset (FinLatticeSites d M)) (t : FinLatticeSites d M) (x y : LatticeLink d M)
    (hy : y ∈ boxBlock Λ₀ t) : linkDist x y ≤ boxReach Λ₀ (x.site - t) := by
  unfold linkDist boxReach
  rw [← siteDist_sub_right x.site y.site t]
  exact_mod_cast Finset.le_sup (f := fun u' => siteDist (x.site - t) u') (mem_filter.1 hy).2

theorem boxBlock_diam {Λ₀ : Finset (FinLatticeSites d M)} {D₀ : ℝ}
    (hD : ∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) (t : FinLatticeSites d M) :
    ∀ x ∈ boxBlock Λ₀ t, ∀ y ∈ boxBlock Λ₀ t, linkDist x y ≤ D₀ := by
  intro x hx y hy
  unfold linkDist
  rw [← siteDist_sub_right x.site y.site t]
  exact hD _ (mem_filter.1 hx).2 _ (mem_filter.1 hy).2

/-- **The block bound in dimension `d`**: a block has at most `d |Λ₀|` links (one per direction per site). -/
theorem card_boxBlock (Λ₀ : Finset (FinLatticeSites d M)) (t : FinLatticeSites d M) :
    (boxBlock Λ₀ t).card ≤ d * Λ₀.card := by
  have h := Finset.card_le_card_of_injOn (s := boxBlock Λ₀ t) (t := Λ₀ ×ˢ (univ : Finset (Fin d)))
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

variable {G : Type*} [MeasurableSpace G] {d : ℕ} [NeZero d] {M : ℕ → ℕ} [∀ j, NeZero (M j)]

/-- **The W₁ gap of a family of laws, bounded form**, for laws on `GaugeConnection G d (M j)` and a pseudo-distance `c`
on `G` for the Lipschitz class of `g`. (`LawGapBddW` of `ProofPhase.V4.Gap` is the case `G = SU2`, `d = 4`,
`c = geodSU2`.) -/
def LawGapBddW (c : G → G → ℝ) (ρ : ℕ → ∀ j, Measure (GaugeConnection G d (M j))) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection G d (M j) → ℝ) (A Sg : Finset (LatticeLink d (M j)))
    (vf : LatticeLink d (M j) → ℝ) (Lg R : ℝ),
    Measurable f → Measurable g → (∀ V, |f V| ≤ 1) → (∀ V, |g V| ≤ 1) → DepOn f A → DepOn g Sg →
    OscBound f vf → 0 ≤ Lg → LipBound c g (fun _ => Lg) → 0 ≤ R →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ V, f V * g V ∂(ρ k j) - (∫ V, f V ∂(ρ k j)) * ∫ V, g V ∂(ρ k j)| ≤
      C * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(lam * R))

/-- **The one-box criterion for a family of laws on `d`-dimensional tori** (gap strength). Uniformly in `k ≥ k₀` and
`j`: a box `Λ₀` of at most `n_max` sites and diameter `≤ D₀`, a block specification of `ρ k j` whose blocks are the
translates of `Λ₀`, box influences `κ(u)`, and the one-box sum `∑_{u ∉ Λ₀} κ(u) e^{λ Ê(u)} ≤ γ |Λ₀|`, `γ < 1`. -/
def OneBoxLaw (ρ : ℕ → ∀ j, Measure (GaugeConnection G d (M j))) (lam : ℝ) : Prop :=
  ∃ (γ D₀ : ℝ) (nmax : ℕ), 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
    ∃ (Λ₀ : Finset (FinLatticeSites d (M j))) (κ : FinLatticeSites d (M j) → ℝ)
      (P : BlockSpec (ρ k j) (FinLatticeSites d (M j))),
      1 ≤ Λ₀.card ∧ Λ₀.card ≤ nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) ∧
      (∀ t, P.block t = boxBlock Λ₀ t) ∧
      (∀ t z, z ∉ P.block t → IsInfluenceBound (P.block t) (P.spec t) z (κ (z.site - t))) ∧
      OneBoxSum κ (boxReach Λ₀) Λ₀ lam γ

/-- **One box gives the W₁ gap (bounded form) in every volume** (S), for any alphabet `G` and dimension `d`.
Constant `2 · d n_max e^{λD₀}/(1 − γ)`. -/
theorem lawGapBddW_of_oneBoxLaw [Nonempty G] {c : G → G → ℝ} {ρ : ℕ → ∀ j, Measure (GaugeConnection G d (M j))} {lam : ℝ}
    (hlam : 0 ≤ lam) (hρ : ∀ k j, IsProbabilityMeasure (ρ k j)) (h : OneBoxLaw ρ lam) :
    LawGapBddW c ρ lam := by
  obtain ⟨γ, D₀, nmax, hγ0, hγ1, k₀, H⟩ := h
  have hg1 : 0 < 1 - γ := by linarith
  refine ⟨2 * (d * nmax) * Real.exp (lam * D₀) / (1 - γ), by positivity, k₀,
    fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg _ hR0 hR => ?_⟩
  obtain ⟨Λ₀, κ, P, hΛ1, hΛn, hdiam, hblock, hk, hsum⟩ := H k hk j
  have := hρ k j
  have : Nonempty (LatticeLink d (M j)) := ⟨⟨fun _ => 0, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩⟩
  have hbox : IsBoxFamily P.block (fun t (x : LatticeLink d (M j)) => x.site - t) Λ₀ := by
    have := isBoxFamily_torus Λ₀
    exact ⟨this.bij, fun t x => by rw [hblock t]; exact this.mem t x⟩
  have hvg : OscBound g (fun _ => (2 : ℝ)) := fun V x s =>
    (abs_sub _ _).trans (by linarith [bg V, bg (Function.update V x s)])
  have hcov := abs_cov_le_of_oneBox (a := noAct) P (fun t x => x.site - t) Λ₀ hbox hΛ1
    (fun γ => γ.elim) (fun _ γ => γ.elim) κ (boxReach Λ₀)
    (fun t z hz => isInfluenceBoundOn_noAct (hk t z hz)) (b := d * nmax)
    (fun t => by rw [hblock t]; exact (card_boxBlock Λ₀ t).trans (Nat.mul_le_mul_left d hΛn))
    linkDist linkDist_self linkDist_triangle (D₀ := D₀)
    (fun t => by rw [hblock t]; exact boxBlock_diam hdiam t)
    (fun t x y _ hy => by rw [hblock t] at hy; exact boxBlock_reach Λ₀ t x y hy) hlam hγ0 hγ1 hsum
    ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩ (fun γ => γ.elim) hfA hgS hvf (by norm_num) hvg hR
  refine hcov.trans ?_
  have hS : 0 ≤ ∑ a ∈ A, vf a := Finset.sum_nonneg fun a _ => hvf.nonneg (fun _ => Classical.arbitrary G) a
  have e1 : Real.exp (-(lam * (R - D₀))) = Real.exp (lam * D₀) * Real.exp (-(lam * R)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1]
  have hE := Real.exp_pos (lam * D₀)
  have hE' := Real.exp_pos (-(lam * R))
  have hn : ((d * nmax : ℕ) : ℝ) = d * (nmax : ℝ) := by push_cast; ring
  rw [hn]
  have key : d * (nmax : ℝ) / (1 - γ) * (∑ x ∈ A, vf x) * 2 ≤
      2 * (d * nmax) / (1 - γ) * (1 + ∑ a ∈ A, vf a) * (1 + Lg) := by
    have h0 : 0 ≤ d * (nmax : ℝ) / (1 - γ) := by positivity
    have h1 : (∑ x ∈ A, vf x) ≤ (1 + ∑ a ∈ A, vf a) * (1 + Lg) := by nlinarith
    calc d * (nmax : ℝ) / (1 - γ) * (∑ x ∈ A, vf x) * 2
        = 2 * (d * nmax) / (1 - γ) * (∑ x ∈ A, vf x) := by ring
      _ ≤ 2 * (d * nmax) / (1 - γ) * ((1 + ∑ a ∈ A, vf a) * (1 + Lg)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  calc d * (nmax : ℝ) / (1 - γ) * (∑ x ∈ A, vf x) * 2 * (Real.exp (lam * D₀) * Real.exp (-(lam * R)))
      = (d * (nmax : ℝ) / (1 - γ) * (∑ x ∈ A, vf x) * 2) * Real.exp (lam * D₀) * Real.exp (-(lam * R)) := by ring
    _ ≤ (2 * (d * nmax) / (1 - γ) * (1 + ∑ a ∈ A, vf a) * (1 + Lg)) * Real.exp (lam * D₀) *
          Real.exp (-(lam * R)) := by gcongr
    _ = 2 * (d * nmax) * Real.exp (lam * D₀) / (1 - γ) * (1 + ∑ a ∈ A, vf a) * (1 + Lg) *
          Real.exp (-(lam * R)) := by ring

end Law

end ProofPhase.General
