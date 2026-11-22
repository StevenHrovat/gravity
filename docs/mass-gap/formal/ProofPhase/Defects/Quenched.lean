/-
Proof phase, cycle 5, workstream 4 (c5d-supplier): Dobrushin's theorem (W₁ form) with free defects, for one fixed
defect set (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5d-supplier/NOTE.md`, Part B.
-/

import OneScale.Lipschitz
import ProofPhase.Defects.EffDist

/-!
# The quenched defect theorem (W₁ form)

**Statement (`quenched_defect_W`, S given `OneScale.BlockSpec.cov_le_weighted_W`).** Fix a defect set `Bad` of the
sites `ι`, a graph `G` on `ι`, and a block specification `P` of the measure `μ` with W₁ influence coefficients `k`
satisfying GDS with `γ`. Measure distances with the **effective distance** `ρ = effDist G Bad` (defect sites free) and
assume

* every non-zero influence reaches at most `ρ`-distance `D₁` into the influenced block (finite range **in `ρ`**), and
* every block has `ρ`-diameter at most `D₀`,
* `γ e^{λ D₁} < 1`.

Then for `f` bounded on `A` (oscillations `v_a`) and `g` Lipschitz with constant `L_g` on `S_g`,

  `|Cov_μ(f, g)| ≤ L_g D_c / (1 − γ e^{λD₁}) · e^{λD₀} · ∑_{a ∈ A} v_a · m(a) · e^{−λ ρ(a, S_g)}`,

`m(a) = ∑_{j ∋ a} |B_j|` the block mass at `a`.

**What the defects buy.** The hypotheses are the usual ones, but in the metric `ρ`. A defect cluster can sit inside one
block with a collar of good sites: its base diameter is arbitrary, its `ρ`-diameter is the collar crossing cost. The
influences that GDS must control are those **into** a block from outside, through the collar; inside a block nothing
needs to contract. The price is that distance is only counted on good sites: the bound decays in `ρ(a, S_g)`, not in
the base distance. Turning `ρ` into the base distance is the Peierls step (`EffDist.expect_effWeight_le`, and
`Annealed.lean`), and needs the defects to be rare.

**What is not claimed.** That such blocks exist for a given action (that is the content: GDS for collared defect
blocks); anything about the photon beyond the unit test in the note (its good sites already fail GDS).
-/

open MeasureTheory Finset OneScale SimpleGraph

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Defects

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-- The block mass at `a`: the total size of the blocks containing `a`. -/
def blockMass {J : Type*} [Fintype J] (block : J → Finset ι) (a : ι) : ℝ :=
  ∑ j ∈ univ.filter (fun j => a ∈ block j), ((block j).card : ℝ)

theorem blockMass_nonneg {J : Type*} [Fintype J] (block : J → Finset ι) (a : ι) : 0 ≤ blockMass block a :=
  sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- Exchange of the block sum and the site sum. -/
theorem sum_block_inter_comm {J : Type*} [Fintype J] (block : J → Finset ι) (A : Finset ι) (F : J → ι → ℝ) :
    ∑ j, ∑ a ∈ block j ∩ A, F j a = ∑ a ∈ A, ∑ j ∈ univ.filter (fun j => a ∈ block j), F j a := by
  have h1 : ∀ j, ∑ a ∈ block j ∩ A, F j a = ∑ a ∈ A, if a ∈ block j then F j a else 0 := by
    intro j
    rw [← sum_filter]
    congr 1
    ext a
    simp [and_comm]
  simp_rw [h1]
  rw [sum_comm]
  exact sum_congr rfl fun a _ => (sum_filter _ _).symm

variable {G : SimpleGraph ι} [DecidableRel G.Adj]

/-- **Dobrushin's theorem (W₁, blocks) with free defects, quenched.** -/
theorem quenched_defect_W {μ : Measure (ι → S)} [IsProbabilityMeasure μ] [Nonempty ι] {J : Type*} [Fintype J]
    (P : BlockSpec μ J) (hG : G.Preconnected) (Bad : Finset ι)
    {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc) (k : J → ι → ℝ)
    (hk : ∀ j z, z ∉ P.block j → IsInfluenceBoundW c (P.block j) (P.spec j) z (k j z))
    {γ : ℝ} (hγ : 0 ≤ γ) (hgds : GDS P.block k γ) {cmin : ℕ} (hc1 : 1 ≤ cmin)
    (hcov : ∀ x, cmin ≤ coverage P.block x)
    {D₀ D₁ lam : ℝ} (hlam : 0 ≤ lam)
    (hD₁ : ∀ j x y, x ∉ P.block j → y ∈ P.block j → k j x ≠ 0 → (effDist G Bad x {y} : ℝ) ≤ D₁)
    (hD₀ : ∀ j, ∀ a ∈ P.block j, ∀ y ∈ P.block j, (effDist G Bad a {y} : ℝ) ≤ D₀)
    (hρ : γ * Real.exp (lam * D₁) < 1)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hSg : Sg.Nonempty) (hfA : DepOn f A)
    (hgS : DepOn g Sg) {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg)
    (hvg : LipBound c g (fun _ => Lg)) :
    |∫ σ, f σ * g σ ∂μ - (∫ σ, f σ ∂μ) * ∫ σ, g σ ∂μ| ≤
      Lg * Dc / (1 - γ * Real.exp (lam * D₁)) * Real.exp (lam * D₀) *
        ∑ a ∈ A, vf a * blockMass P.block a * effWeight G Bad lam Sg a := by
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure μ
  obtain ⟨x₀⟩ := (inferInstance : Nonempty ι)
  have hDc : 0 ≤ Dc := (hc0 (σ₀ x₀) (σ₀ x₀)).trans (hcD _ _)
  set w := effWeight G Bad lam Sg with hwdef
  set E := Real.exp (lam * D₁)
  have hw0 : ∀ x, 0 ≤ w x := effWeight_nonneg Bad lam Sg
  have hwk : ∀ j x y, x ∉ P.block j → y ∈ P.block j → k j x ≠ 0 → w y ≤ E * w x :=
    fun j x y hx hy hkx => effWeight_le_of_effDist hG Bad hlam hSg (hD₁ j x y hx hy hkx)
  have hvg' : LipBound c g (fun x => Lg * w x) := by
    intro σ x s
    by_cases hx : x ∈ Sg
    · have h1 : w x = 1 := effWeight_of_mem Bad lam hx
      simp only [h1, mul_one]
      exact hvg σ x s
    · rw [hgS.update_eq hx σ s, sub_self, abs_zero]
      exact mul_nonneg (mul_nonneg hLg (hw0 x)) (hc0 _ _)
  have hcore := P.cov_le_weighted_W hc0 hcD k hk hγ hgds hc1 hcov hw0 (Real.exp_pos _).le hwk hρ hf hg hfA hvf
    hLg hvg'
  refine hcore.trans ?_
  have hvf0 : ∀ a, 0 ≤ vf a := fun a => hvf.nonneg σ₀ a
  have hgap : 0 < 1 - γ * E := by linarith
  have hcm : (1 : ℝ) ≤ cmin := by exact_mod_cast hc1
  set e0 := Real.exp (lam * D₀)
  have he0 : 0 ≤ e0 := (Real.exp_pos _).le
  -- the block sum, bounded per site
  have hblock : ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y ≤
      e0 * ∑ a ∈ A, vf a * blockMass P.block a * w a := by
    have h1 : ∀ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y ≤
        ∑ a ∈ P.block j ∩ A, vf a * (((P.block j).card : ℝ) * (e0 * w a)) := by
      intro j
      rw [sum_mul]
      refine sum_le_sum fun a ha => mul_le_mul_of_nonneg_left ?_ (hvf0 a)
      have ha' := (mem_inter.1 ha).1
      calc ∑ y ∈ P.block j, w y ≤ ∑ _y ∈ P.block j, e0 * w a :=
            sum_le_sum fun y hy => effWeight_le_of_effDist hG Bad hlam hSg (hD₀ j a ha' y hy)
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    refine (sum_le_sum fun j _ => h1 j).trans (le_of_eq ?_)
    rw [sum_block_inter_comm, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    unfold blockMass
    rw [mul_sum, sum_mul, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    ring
  have hsum0 : 0 ≤ ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y :=
    sum_nonneg fun j _ => mul_nonneg (sum_nonneg fun a _ => hvf0 a) (sum_nonneg fun y _ => hw0 y)
  have hpre : Lg * Dc / (cmin * (1 - γ * E)) ≤ Lg * Dc / (1 - γ * E) := by
    refine div_le_div_of_nonneg_left (mul_nonneg hLg hDc) hgap ?_
    nlinarith
  calc Lg * Dc / (cmin * (1 - γ * E)) * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y
      ≤ Lg * Dc / (1 - γ * E) * ∑ j, (∑ a ∈ P.block j ∩ A, vf a) * ∑ y ∈ P.block j, w y :=
        mul_le_mul_of_nonneg_right hpre hsum0
    _ ≤ Lg * Dc / (1 - γ * E) * (e0 * ∑ a ∈ A, vf a * blockMass P.block a * w a) :=
        mul_le_mul_of_nonneg_left hblock (div_nonneg (mul_nonneg hLg hDc) hgap.le)
    _ = _ := by ring

end ProofPhase.Defects
