/-
Proof phase, cycle 8, workstream 1 (c8a-saturation): the one-box criterion split into a centre (tie) part and an adjoint
(stateless) part, the budget a tie forces, and the assembly from the two parts (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c8a-saturation/NOTE.md`, section 5.
-/

import ProofPhase.OneBox.Tests
import ProofPhase.Saturation.Tests

/-!
# What saturation supplies to the one-box criterion, and what remains

The box influence of one outside cell is the distance between two box laws, `q(σ)` and `q(σ')` (`σ'` = `σ` with the cell
changed). Put a **hybrid law** `r` between them: the centre (binary) layer distributed as under `σ'`, the adjoint layer
conditionally as under `σ` (or the other way round; only the triangle inequality is used). Then

  `influence ≤ κ_A + κ_Z`,  `κ_A` = distance `q(σ) ↔ r` (adjoint conditional moved, centre law fixed),
                              `κ_Z` = distance `r ↔ q(σ')` (centre law moved, adjoint conditional fixed)

(`isInfluenceBoundOn_split`), and the one-box sums add (`oneBoxSum_add`): **centre budget `γ_Z` plus adjoint budget `γ_A`,
`γ_Z + γ_A < 1`** gives the criterion (`fineOneBox_of_split`) and with it the full assembly conclusion
(`yang_mills_assembly_split`).

* **Ties live in the centre part** (`tie_forces_budget`): two boundary conditions that differ on outside cells at distinct
  relative positions and move a centre-layer test function (oscillation `≤ 1` per cell) by `θ |Λ₀|` force
  `∑_u κ_Z(u) ≥ θ |Λ₀|`, so `γ_Z ≥ θ`. Saturation is the statement that makes `γ_Z` small (NOTE, section 5: quenched
  saturation ⇒ Dobrushin for the binary layer at every adjoint background ⇒ `κ_Z(u)` decays into the box ⇒ `∑ κ_Z = O(ℓ³)`).
* **The adjoint part is not supplied by saturation.** For SU(2)×U(1) the U(1) photon sits in the adjoint (quotient) layer and
  its harmonic-measure response gives `γ_A ≥ 1` at every box size (c7c, section 5); for a two-phase mixture the phases are
  told apart by centre-even data, again `γ_A`. Both keep their saturated centre layer (`mixture_saturation`, `flipP_product`).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity ProofPhase.Torus ProofPhase.V3 ProofPhase.V4 ProofPhase.RouteA ProofPhase.OneBox

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Saturation

/-! ## 1. The split -/

section Split

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-- **The influence splits at a hybrid law** `r σ s` (centre layer as under the moved boundary condition, adjoint layer as
    under the old one). -/
theorem isInfluenceBoundOn_split {Adm : (ι → S) → ((ι → S) → ℝ) → Prop} {B : Finset ι}
    {q : (ι → S) → Measure (ι → S)} {z : ι} {kZ kA : ℝ} (r : (ι → S) → S → Measure (ι → S))
    (hA : ∀ (σ : ι → S) (s : S) (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B → Adm (Function.update σ z s) F →
      (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) →
      |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(r σ s)| ≤ kA * L)
    (hZ : ∀ (σ : ι → S) (s : S) (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B → Adm (Function.update σ z s) F →
      (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) →
      |∫ ξ, F ξ ∂(r σ s) - ∫ ξ, F ξ ∂(q (Function.update σ z s))| ≤ kZ * L) :
    IsInfluenceBoundOn Adm B q z (kZ + kA) := by
  intro σ s F L hF hdep hadm hosc
  calc |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q (Function.update σ z s))|
      ≤ |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(r σ s)| + |∫ ξ, F ξ ∂(r σ s) - ∫ ξ, F ξ ∂(q (Function.update σ z s))| :=
        abs_sub_le _ _ _
    _ ≤ kA * L + kZ * L := add_le_add (hA σ s F L hF hdep hadm hosc) (hZ σ s F L hF hdep hadm hosc)
    _ = (kZ + kA) * L := by ring

end Split

/-! ## 2. The budgets add -/

section Budget

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **Centre budget plus adjoint budget.** -/
theorem oneBoxSum_add {κZ κA Ehat : U → ℝ} {Λ₀ : Finset U} {lam γZ γA : ℝ} (hZ : OneBoxSum κZ Ehat Λ₀ lam γZ)
    (hA : OneBoxSum κA Ehat Λ₀ lam γA) : OneBoxSum (fun u => κZ u + κA u) Ehat Λ₀ lam (γZ + γA) := by
  unfold OneBoxSum at *
  simp_rw [add_mul]
  rw [sum_add_distrib]
  linarith

/-- With `λ, Ê ≥ 0` and `κ ≥ 0`, the one-box sum bounds the plain influence sum: `∑_{u ∉ Λ₀} κ(u) ≤ γ |Λ₀|`. -/
theorem sum_le_of_oneBoxSum {κ Ehat : U → ℝ} {Λ₀ : Finset U} {lam γ : ℝ} (hlam : 0 ≤ lam) (hE : ∀ u, 0 ≤ Ehat u)
    (hκ : ∀ u, 0 ≤ κ u) (h : OneBoxSum κ Ehat Λ₀ lam γ) :
    ∑ u ∈ univ.filter (fun u => u ∉ Λ₀), κ u ≤ γ * Λ₀.card := by
  refine le_trans (sum_le_sum fun u _ => ?_) h
  have : 1 ≤ Real.exp (lam * Ehat u) := Real.one_le_exp (mul_nonneg hlam (hE u))
  nlinarith [hκ u]

end Budget

/-! ## 3. A tie forces the centre budget -/

section Tie

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {U : Type*} [Fintype U] [DecidableEq U]

/-- **A tie forces the centre budget** (S). Let `qZ` be the box specification of the centre layer of the block `B`, with
    influences `kZ z ≤ κZ (rel z)` from outside cells. If two boundary conditions differ only on a set `Zs` of outside cells
    at distinct relative positions and move a test function of the block (bounded, measurable, oscillation `≤ 1` per cell)
    by at least `θ |Λ₀|`, then `θ |Λ₀| ≤ ∑_{u ∉ Λ₀} κZ(u)`; with the centre one-box sum, `θ ≤ γ_Z`. -/
theorem tie_forces_budget {B : Finset ι} {qZ : (ι → S) → Measure (ι → S)} {kZ : ι → ℝ}
    (hk : ∀ z, z ∉ B → IsInfluenceBound B qZ z (kZ z)) (rel : ι → U) {Λ₀ : Finset U} {κZ Ehat : U → ℝ}
    (hκ0 : ∀ u, 0 ≤ κZ u) (hkκ : ∀ z, z ∉ B → kZ z ≤ κZ (rel z)) (Zs : Finset ι) (hZs : ∀ z ∈ Zs, z ∉ B)
    (hZΛ : ∀ z ∈ Zs, rel z ∉ Λ₀) (hinj : Set.InjOn rel Zs) {F : (ι → S) → ℝ} (hF : BM F) (hdep : DepOn F B)
    (hosc : ∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ 1) {σ σ' : ι → S} (hσ : ∀ i ∉ Zs, σ i = σ' i)
    {θ : ℝ} (htie : θ * Λ₀.card ≤ |∫ ξ, F ξ ∂(qZ σ) - ∫ ξ, F ξ ∂(qZ σ')|)
    {lam γZ : ℝ} (hlam : 0 ≤ lam) (hE : ∀ u, 0 ≤ Ehat u) (hsum : OneBoxSum κZ Ehat Λ₀ lam γZ) (hΛ : 0 < Λ₀.card) :
    θ ≤ γZ := by
  have ht := influence_telescope hk hF hdep hosc Zs hZs hσ
  rw [mul_one] at ht
  have h1 : ∑ z ∈ Zs, kZ z ≤ ∑ u ∈ Zs.image rel, κZ u := by
    rw [sum_image hinj]; exact sum_le_sum fun z hz => hkκ z (hZs z hz)
  have h2 : ∑ u ∈ Zs.image rel, κZ u ≤ ∑ u ∈ univ.filter (fun u => u ∉ Λ₀), κZ u := by
    refine sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) fun u _ _ => hκ0 u
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hu
    exact mem_filter.mpr ⟨mem_univ _, hZΛ z hz⟩
  have h3 := sum_le_of_oneBoxSum hlam hE hκ0 hsum
  have hc : (0 : ℝ) < Λ₀.card := by exact_mod_cast hΛ
  have : θ * Λ₀.card ≤ γZ * Λ₀.card := by linarith
  exact le_of_mul_le_mul_right this hc

end Tie

/-! ## 4. The criterion from its two parts -/

/-- **The one-box criterion in split form** (named, open): as `FineOneBox`, with the influence of each outside cell split
    at a hybrid law into a centre part `κZ` (the saturation / no-tie part) and an adjoint part `κA` (the stateless part), and
    the two budgets `γZ + γA < 1`. -/
def FineOneBoxSplit (T : Tuning) : Prop :=
  ∃ (cell : ∀ k j, LatticeLink 4 (T.side k j) → LatticeLink 4 (coarseSide j)) (c₀ c₁ : ℝ),
    CellGeometry T cell c₀ c₁ ∧
    ∃ (lam γZ γA D₀ : ℝ) (nmax : ℕ), 0 < lam ∧ 0 ≤ γZ ∧ 0 ≤ γA ∧ γZ + γA < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
      ∃ (Λ₀ : Finset (FinLatticeSites 4 (coarseSide j))) (κZ κA : FinLatticeSites 4 (coarseSide j) → ℝ)
        (P : BlockSpec ((T.ym k j).map (cellLift (cell k j) (1 : SU2))) (FinLatticeSites 4 (coarseSide j)))
        (r : FinLatticeSites 4 (coarseSide j) → LatticeLink 4 (coarseSide j) →
          (LatticeLink 4 (coarseSide j) → (LatticeLink 4 (T.side k j) → SU2)) → (LatticeLink 4 (T.side k j) → SU2) →
          Measure (LatticeLink 4 (coarseSide j) → (LatticeLink 4 (T.side k j) → SU2))),
        1 ≤ Λ₀.card ∧ Λ₀.card ≤ nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) ∧
        (∀ t, P.block t = boxBlock Λ₀ t) ∧
        (∀ t, SpecCovariant (liftAct (cell k j) (gaugeAct (T.side k j))) (P.spec t)) ∧
        (∀ t z, z ∉ P.block t → ∀ σ s F (L : ℝ), BM F → DepOn F (P.block t) →
          ActAdm (liftAct (cell k j) (gaugeAct (T.side k j))) (P.block t) (Function.update σ z s) F →
          (∀ ξ y w, y ∈ P.block t → |F ξ - F (Function.update ξ y w)| ≤ L) →
          |∫ ξ, F ξ ∂(P.spec t σ) - ∫ ξ, F ξ ∂(r t z σ s)| ≤ κA (z.site - t) * L) ∧
        (∀ t z, z ∉ P.block t → ∀ σ s F (L : ℝ), BM F → DepOn F (P.block t) →
          ActAdm (liftAct (cell k j) (gaugeAct (T.side k j))) (P.block t) (Function.update σ z s) F →
          (∀ ξ y w, y ∈ P.block t → |F ξ - F (Function.update ξ y w)| ≤ L) →
          |∫ ξ, F ξ ∂(r t z σ s) - ∫ ξ, F ξ ∂(P.spec t (Function.update σ z s))| ≤ κZ (z.site - t) * L) ∧
        OneBoxSum κZ (boxReach Λ₀) Λ₀ lam γZ ∧ OneBoxSum κA (boxReach Λ₀) Λ₀ lam γA

/-- **The split criterion is the one-box criterion** (S). -/
theorem fineOneBox_of_split {T : Tuning} (h : FineOneBoxSplit T) : FineOneBox T := by
  obtain ⟨cell, c₀, c₁, hgeo, lam, γZ, γA, D₀, nmax, hlam, hZ0, hA0, hγ, k₀, H⟩ := h
  refine ⟨cell, c₀, c₁, hgeo, lam, γZ + γA, D₀, nmax, hlam, by linarith, hγ, k₀, fun k hk j => ?_⟩
  obtain ⟨Λ₀, κZ, κA, P, r, h1, h2, h3, h4, h5, hA, hZ, hsZ, hsA⟩ := H k hk j
  refine ⟨Λ₀, fun u => κZ u + κA u, P, h1, h2, h3, h4, h5, fun t z hz => ?_, oneBoxSum_add hsZ hsA⟩
  exact isInfluenceBoundOn_split (r t z) (hA t z hz) (hZ t z hz)

/-- **The assembly from the two parts** (S): line of constant physics, non-triviality, and the one-box criterion in split
    form (centre budget + adjoint budget `< 1`) give the conclusions of `yang_mills_assembly_onebox`. -/
theorem yang_mills_assembly_split {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (h : FineOneBoxSplit T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T :=
  yang_mills_assembly_onebox hL hN (fineOneBox_of_split h)

end ProofPhase.Saturation
