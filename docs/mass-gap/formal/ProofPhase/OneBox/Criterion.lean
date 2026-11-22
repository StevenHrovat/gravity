/-
Proof phase, cycle 7, workstream 1 (c7c-onebox): the one-box criterion, generic layer (2026-11-22). Released under
Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c7c-onebox/NOTE.md`, sections 1 to 3.
-/

import ProofPhase.OneBox.Restricted

/-!
# The one-box criterion (worst-case boundary, Dobrushin–Shlosman form), generic layer

**Gauge layer.** A coordinatewise action `a γ i : S → S` (for the lattice gauge field: `U_l ↦ g(l.site) U_l
g(l.target)⁻¹`). `act a γ σ` is the action on configurations, `ActInv a h` says `h` is invariant, and
`ActAdm a B σ F` says `F` is invariant under every `γ` that **fixes the boundary condition `σ` off `B`** (for a box: the
gauge transformations of the box interior, and the global centre ones). A block specification is **covariant**
(`SpecCovariant`) if `q(γσ) = γ_* q(σ)`: true for the Gibbs (DLR) box specification of a gauge-invariant action with
Haar prior. Then the invariant class is closed under the averaged block operator and restricts to admissible functions
(`admData_of_covariant`), so Theorem A needs the box influences **only on gauge-invariant test functions of the box
with frozen boundary** (`ProofPhase.OneBox.theoremA_on`). This is the gauge handling: no gauge fixing, no orbit metric.

**Translation layer.** Blocks `j : J` are translates of one box: a relative-position map `rel : J → ι → U` (on the
torus: `rel t x = x.site − t`), bijective in `j` for each `x`, and `block j = {x | rel j x ∈ Λ₀}`
(`IsBoxFamily`). Then every site is covered exactly `|Λ₀|` times (`coverage_box`), and the weighted Dobrushin–Shlosman
sum at `x` is the **one-box sum** `∑_{u ∉ Λ₀} κ(u) e^{λ Ê(u)}` (`sum_box`), where `κ(u)` bounds the influence of the
outside position `u` on the box and `Ê(u)` its distance to the far side of the box.

**The criterion** (`OneBoxSum κ Ê Λ₀ λ γ`): `∑_{u ∉ Λ₀} κ(u) e^{λ Ê(u)} ≤ γ |Λ₀|`, `γ < 1`: the boundary influence summed
over the outside of **one** box is less than the box volume (the margin beats the surface count).

**The theorem** (`abs_cov_le_of_oneBox`): one-box sum + box family + influences on the admissible class + covariance
⇒ `|Cov(f, g)| ≤ b/(1 − γ) · (∑_A v_f) · L_g · e^{−λ(R − D₀)}` for `g` invariant, uniformly in everything else.
-/

open MeasureTheory Finset OneScale

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OneBox

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-! ## The gauge layer -/

section Gauge

variable {Γ : Type*} (a : Γ → ι → S → S)

/-- The coordinatewise action on configurations. -/
def act (γ : Γ) (σ : ι → S) : ι → S := fun i => a γ i (σ i)

/-- `h` is invariant under the action. -/
def ActInv (h : (ι → S) → ℝ) : Prop := ∀ γ σ, h (act a γ σ) = h σ

/-- `F` is invariant under every group element that fixes the boundary condition `σ` off `B`. -/
def ActAdm (B : Finset ι) (σ : ι → S) (F : (ι → S) → ℝ) : Prop :=
  ∀ γ, (∀ i ∉ B, a γ i (σ i) = σ i) → ∀ ξ, F (act a γ ξ) = F ξ

/-- A block specification is covariant under the action. -/
def SpecCovariant (q : (ι → S) → Measure (ι → S)) : Prop := ∀ γ σ, q (act a γ σ) = (q σ).map (act a γ)

variable {a}

theorem splice_act (B : Finset ι) (γ : Γ) (σ ξ : ι → S) :
    splice B (act a γ σ) (act a γ ξ) = act a γ (splice B σ ξ) := by
  funext i; by_cases hi : i ∈ B <;> simp [splice, act, hi]

theorem splice_act_right {B : Finset ι} {γ : Γ} {σ : ι → S} (hγ : ∀ i ∉ B, a γ i (σ i) = σ i) (ξ : ι → S) :
    splice B σ (act a γ ξ) = act a γ (splice B σ ξ) := by
  funext i; by_cases hi : i ∈ B <;> simp [splice, act, hi, hγ i]

theorem measurable_act (ha : ∀ γ i, Measurable (a γ i)) (γ : Γ) : Measurable (act (ι := ι) a γ) :=
  measurable_pi_iff.mpr fun i => (ha γ i).comp (measurable_pi_apply i)

/-- An invariant function, frozen off `B` at `σ`, is admissible at `σ`. -/
theorem actAdm_restrict {h : (ι → S) → ℝ} (hh : ActInv a h) (B : Finset ι) (σ : ι → S) :
    ActAdm a B σ (fun ξ => h (splice B σ ξ)) := by
  intro γ hγ ξ
  simp only
  rw [splice_act_right hγ, hh]

/-- A covariant block specification maps invariant functions to invariant functions. -/
theorem actInv_blockAvg (ha : ∀ γ i, Measurable (a γ i)) {B : Finset ι} {q : (ι → S) → Measure (ι → S)}
    (hq : SpecCovariant a q) {h : (ι → S) → ℝ} (hb : BM h) (hh : ActInv a h) : ActInv a (blockAvg B q h) := by
  intro γ σ
  unfold blockAvg
  rw [hq γ σ, integral_map (f := fun ξ => h (splice B (act a γ σ) ξ)) (measurable_act ha γ).aemeasurable
    (hb.meas.comp (measurable_splice_right B _)).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show h (splice B (act a γ σ) (act a γ ξ)) = h (splice B σ ξ)
  rw [splice_act, hh]

variable {J : Type*} [Fintype J] {μ : Measure (ι → S)} (P : BlockSpec μ J)

/-- **Admissibility data from a covariant block specification.** -/
theorem admData_of_covariant (ha : ∀ γ i, Measurable (a γ i)) (hq : ∀ j, SpecCovariant a (P.spec j)) :
    AdmData P (fun j => ActAdm a (P.block j)) (ActInv a) where
  avg h hb hh γ σ := by
    unfold BlockSpec.avg
    congr 1
    exact sum_congr rfl fun j _ => actInv_blockAvg ha (hq j) hb hh γ σ
  restrict j h σ hh := actAdm_restrict hh (P.block j) σ

end Gauge

/-! ## The translation layer -/

section Box

variable {J U : Type*} [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U]

/-- **A box family**: `rel j x` is the position of `x` relative to block `j`, bijective in `j` for each `x`, and the
blocks are the translates `{x | rel j x ∈ Λ₀}` of one box `Λ₀`. -/
structure IsBoxFamily (block : J → Finset ι) (rel : J → ι → U) (Λ₀ : Finset U) : Prop where
  bij : ∀ x, Function.Bijective (fun j => rel j x)
  mem : ∀ j x, x ∈ block j ↔ rel j x ∈ Λ₀

/-- **The one-box sum**: `∑_{u ∉ Λ₀} κ(u) e^{λ Ê(u)} ≤ γ |Λ₀|`. -/
def OneBoxSum (κ Ehat : U → ℝ) (Λ₀ : Finset U) (lam γ : ℝ) : Prop :=
  ∑ u ∈ univ.filter (fun u => u ∉ Λ₀), κ u * Real.exp (lam * Ehat u) ≤ γ * Λ₀.card

variable {block : J → Finset ι} {rel : J → ι → U} {Λ₀ : Finset U}

/-- Every site is covered `|Λ₀|` times. -/
theorem coverage_box (h : IsBoxFamily block rel Λ₀) (x : ι) : coverage block x = Λ₀.card := by
  unfold coverage
  refine Finset.card_nbij (fun j => rel j x) (fun j hj => ?_) (fun j _ j' _ e => (h.bij x).1 e) (fun u hu => ?_)
  · exact (h.mem j x).1 (mem_filter.1 hj).2
  · obtain ⟨j, hj⟩ := (h.bij x).2 u
    have hj' : rel j x = u := hj
    exact ⟨j, mem_filter.2 ⟨mem_univ _, (h.mem j x).2 (hj' ▸ hu)⟩, hj⟩

/-- The sum over the blocks not containing `x` is the sum over the outside of the box. -/
theorem sum_box (h : IsBoxFamily block rel Λ₀) (x : ι) (φ : U → ℝ) :
    ∑ j ∈ univ.filter (fun j => x ∉ block j), φ (rel j x) = ∑ u ∈ univ.filter (fun u => u ∉ Λ₀), φ u := by
  refine Finset.sum_nbij (fun j => rel j x) (fun j hj => ?_) (fun j _ j' _ e => (h.bij x).1 e) (fun u hu => ?_)
    (fun j _ => rfl)
  · exact mem_filter.2 ⟨mem_univ _, fun hm => (mem_filter.1 hj).2 ((h.mem j x).2 hm)⟩
  · obtain ⟨j, hj⟩ := (h.bij x).2 u
    refine ⟨j, mem_filter.2 ⟨mem_univ _, fun hm => (mem_filter.1 hu).2 ?_⟩, hj⟩
    rw [← hj]; exact (h.mem j x).1 hm

/-- **The one-box sum is the weighted Dobrushin–Shlosman condition** for the box family, with influences
`k_j(x) = κ(rel j x)` and growth exponents `E_j(x) = Ê(rel j x)`. -/
theorem gdsw_of_oneBox (h : IsBoxFamily block rel Λ₀) {κ Ehat : U → ℝ} {lam γ : ℝ}
    (hc : OneBoxSum κ Ehat Λ₀ lam γ) :
    Attempts.R3.GDSw block (fun j x => κ (rel j x)) (fun j x => Real.exp (lam * Ehat (rel j x))) γ := by
  intro x
  rw [sum_box h x (fun u => κ u * Real.exp (lam * Ehat u)), coverage_box h x]
  exact hc

end Box

/-! ## The theorem -/

section Main

variable {Γ : Type*} {a : Γ → ι → S → S} {J U : Type*} [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U]
  {μ : Measure (ι → S)}

/-- **One box gives decay in the whole volume** (S). A law `μ` with a block specification whose blocks are the
translates of one box `Λ₀` (`IsBoxFamily`, block sizes `≤ b`, block diameters `≤ D₀`), covariant under a coordinatewise
action, whose box influence from the relative outside position `u` is `≤ κ(u)` **on gauge-invariant test functions of
the box with frozen boundary**, with `Ê(u)` bounding the distance from `u` to the box, and the **one-box sum**
`∑_{u ∉ Λ₀} κ(u) e^{λÊ(u)} ≤ γ|Λ₀|`, `γ < 1`: for bounded measurable `f` (oscillations `v_f` on `A`) and invariant `g`
(oscillation `≤ L_g` on `S_g`) at distance `≥ R`, `|Cov(f, g)| ≤ b/(1 − γ) · (∑_A v_f) · L_g · e^{−λ(R − D₀)}`. -/
theorem abs_cov_le_of_oneBox [IsProbabilityMeasure μ] [Nonempty ι] (P : BlockSpec μ J) (rel : J → ι → U)
    (Λ₀ : Finset U) (hbox : IsBoxFamily P.block rel Λ₀) (hΛ : 1 ≤ Λ₀.card)
    (ha : ∀ γ i, Measurable (a γ i)) (hq : ∀ j, SpecCovariant a (P.spec j))
    (κ Ehat : U → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundOn (ActAdm a (P.block j)) (P.block j) (P.spec j) z (κ (rel j z)))
    {b : ℕ} (hb : ∀ j, (P.block j).card ≤ b)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {D₀ : ℝ} (hD₀ : ∀ j, ∀ x ∈ P.block j, ∀ y ∈ P.block j, dist x y ≤ D₀)
    (hE : ∀ j x y, x ∉ P.block j → y ∈ P.block j → dist x y ≤ Ehat (rel j x))
    {lam γ : ℝ} (hlam : 0 ≤ lam) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hsum : OneBoxSum κ Ehat Λ₀ lam γ)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) (hgI : ActInv a g) {A Sg : Finset ι} (hfA : DepOn f A)
    (hgS : DepOn g Sg) {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    {R : ℝ} (hR : ∀ x ∈ A, ∀ y ∈ Sg, R ≤ dist x y) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      b / (1 - γ) * (∑ x ∈ A, vf x) * Lg * Real.exp (-(lam * (R - D₀))) := by
  have hcov : ∀ x, Λ₀.card ≤ coverage P.block x := fun x => (coverage_box hbox x).ge
  have hcmax : ∀ x, coverage P.block x ≤ Λ₀.card := fun x => (coverage_box hbox x).le
  have h := theoremA_on P (admData_of_covariant P ha hq) (fun j x => κ (rel j x)) hk hΛ hcov hcmax hb dist hd0
    htri hD₀ (fun j x => Ehat (rel j x)) hE hlam hγ hγ1 (gdsw_of_oneBox hbox hsum) hf hg hgI hfA hgS hvf hLg hvg
    hR
  refine h.trans (le_of_eq ?_)
  have hc : (Λ₀.card : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ Λ₀.card := by exact_mod_cast hΛ
                                    linarith
  field_simp

end Main

end ProofPhase.OneBox
