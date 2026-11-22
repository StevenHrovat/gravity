/-
Proof phase, cycle 7, workstream 1 (c7c-onebox): the formal half of the unit tests of the one-box criterion
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c7c-onebox/NOTE.md`, section 5.
-/

import ProofPhase.OneBox.Fine

/-!
# Unit tests of the one-box criterion: the two failure mechanisms, formally

Every failing unit test of NOTE §5 fails through one of two mechanisms; both are theorems here.

* **Power-law or persistent correlations** (photon, U(1) factor of SU(2)×U(1), mixtures, ordered phases):
  `not_oneBoxLaw_of_power`: a family of laws with covariances `≥ c R^{−p}` at arbitrarily large distance `R` (bounded
  observables, bounded oscillation sum and Lipschitz constant; `p = 0` persistent) fails `OneBoxLaw` for every `λ > 0`.
  `not_fineOneBox_of_not_torusDecayLoc`: a tuning without torus decay fails `FineOneBox`.
* **The boundary decides the interior** (frozen sectors of 2I and of Z₂ at weak coupling, two coexisting phases; this
  mechanism also fails models whose local correlations do decay): `influence_telescope`: if two boundary conditions
  differ on a set `Z` of outside sites, the box laws differ by at most `(∑_{z ∈ Z} k(z)) · L` on every test function
  with oscillation `≤ L` per site. So the influence sum over the boundary is **at least** the distance between the box
  laws under any two boundary conditions: if some pair of boundary conditions moves a fraction `θ` of the box (two
  phases, two sectors), the one-box sum is `≥ θ|Λ₀|`-sized and the criterion fails once `θ ≥ γ`.
* The passing anchor (strong coupling) is `OneScale.SingleLink.wilson_singleLink_decay` (Theorem A with the box a single
  link, `18 tanh(2β) < 1`); NOTE §5.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  ProofPhase.Torus ProofPhase.V3 ProofPhase.V4 ProofPhase.Certified

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OneBox

/-! ## The boundary decides: the telescoping lower bound -/

section Telescope

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-- **Telescoping over the boundary.** If `k z` bounds the influence of each outside site `z` on the block `B`, two
boundary conditions that differ only on `Z` (outside `B`) move every test function of the block with oscillation `≤ L`
per site by at most `(∑_{z ∈ Z} k z) · L`. Read backwards: the influence sum is at least the distance of the box laws
under any two boundary conditions. -/
theorem influence_telescope {B : Finset ι} {q : (ι → S) → Measure (ι → S)} {k : ι → ℝ}
    (hk : ∀ z, z ∉ B → IsInfluenceBound B q z (k z)) {F : (ι → S) → ℝ} {L : ℝ} (hF : BM F) (hdep : DepOn F B)
    (hosc : ∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) (Z : Finset ι) :
    (∀ z ∈ Z, z ∉ B) → ∀ {σ σ' : ι → S}, (∀ i ∉ Z, σ i = σ' i) →
      |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q σ')| ≤ (∑ z ∈ Z, k z) * L := by
  induction Z using Finset.induction_on with
  | empty =>
    intro _ σ σ' hT
    have : σ = σ' := funext fun i => hT i (Finset.notMem_empty i)
    simp [this]
  | insert a Z ha ih =>
    intro hZ σ σ' hT
    set σ'' := Function.update σ a (σ' a)
    have h1 : ∀ i ∉ Z, σ'' i = σ' i := by
      intro i hi
      by_cases hia : i = a
      · subst hia; simp [σ'']
      · simp only [σ'', Function.update_of_ne hia]
        exact hT i (by simp [hia, hi])
    have hA := hk a (hZ a (mem_insert_self a Z)) σ (σ' a) F L hF hdep hosc
    have hB := ih (fun z hz => hZ z (mem_insert_of_mem hz)) h1
    rw [Finset.sum_insert ha, add_mul]
    calc |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q σ')|
        ≤ |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q σ'')| + |∫ ξ, F ξ ∂(q σ'') - ∫ ξ, F ξ ∂(q σ')| := abs_sub_le _ _ _
      _ ≤ k a * L + (∑ z ∈ Z, k z) * L := add_le_add hA hB

end Telescope

/-! ## Power-law and persistent correlations -/

section Power

variable {M : ℕ → ℕ} [∀ j, NeZero (M j)]

/-- **Power-law correlations** (exponent `p`; `p = 0`: persistent): for every distance `R ≥ 0` and every level `k₀`
some covariance at distance `≥ R` and level `≥ k₀` is `≥ c R^{−p}` (stated as `c ≤ R^p |Cov|`), for bounded observables
with oscillation sum `≤ V₀` and Lipschitz constant `≤ L₀`. The photon (`⟨F F⟩ ~ |x|^{−4}`) and every massless or
two-phase law have them. -/
def PowerCorr (ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))) (p : ℕ) : Prop :=
  ∃ c V₀ L₀ : ℝ, 0 < c ∧ 0 ≤ V₀ ∧ 0 ≤ L₀ ∧ ∀ (k₀ : ℕ) (R : ℝ), 0 ≤ R → ∃ k, k₀ ≤ k ∧ ∃ (j : ℕ)
    (f g : GaugeConnection SU2 4 (M j) → ℝ) (A Sg : Finset (LatticeLink 4 (M j))) (vf : LatticeLink 4 (M j) → ℝ)
    (Lg : ℝ), Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A ∧ DepOn g Sg ∧
    OscBound f vf ∧ ∑ a ∈ A, vf a ≤ V₀ ∧ 0 ≤ Lg ∧ Lg ≤ L₀ ∧ LipBound geodSU2 g (fun _ => Lg) ∧
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) ∧
    c ≤ R ^ p * |∫ V, f V * g V ∂(ρ k j) - (∫ V, f V ∂(ρ k j)) * ∫ V, g V ∂(ρ k j)|

/-- Power-law correlations exclude the bounded W₁ gap at any rate `λ > 0`. -/
theorem not_lawGapBddW_of_power {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ} {p : ℕ}
    (hlam : 0 < lam) (hP : PowerCorr ρ p) : ¬ LawGapBddW ρ lam := by
  rintro ⟨C, hC, k₀, H⟩
  obtain ⟨c, V₀, L₀, hc, hV₀, hL₀, HP⟩ := hP
  set K := C * (1 + V₀) * (1 + L₀)
  have hK : 0 ≤ K := by positivity
  have h1 : Tendsto (fun R : ℝ => lam * R) atTop atTop := tendsto_id.const_mul_atTop hlam
  have h2 : Tendsto (fun R : ℝ => K * (R ^ p * Real.exp (-(lam * R)))) atTop (𝓝 0) := by
    have h3 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p).comp h1).const_mul (K / lam ^ p)
    rw [mul_zero] at h3
    refine h3.congr fun R => ?_
    simp only [Function.comp]
    have : lam ^ p ≠ 0 := pow_ne_zero _ hlam.ne'
    rw [mul_pow]; field_simp
  obtain ⟨R, hR1, hR0⟩ := ((h2.eventually (gt_mem_nhds hc)).and (eventually_ge_atTop 0)).exists
  obtain ⟨k, hk, j, f, g, A, Sg, vf, Lg, mf, mg, bf, bg, hfA, hgS, hvf, hV, hLg0, hLg, hlip, hsep, hcov⟩ :=
    HP k₀ R hR0
  have hb := H k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg0 hlip hR0 hsep
  have hS := sum_osc_nonneg hvf A
  have : C * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(lam * R)) ≤ K * Real.exp (-(lam * R)) := by
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC) (by linarith) (by linarith) (by positivity)
  have hRp : 0 ≤ R ^ p := pow_nonneg hR0 p
  have h4 := mul_le_mul_of_nonneg_left (hb.trans this) hRp
  nlinarith

/-- **Unit test (power-law or persistent correlations): the one-box criterion fails** for every `λ > 0`. -/
theorem not_oneBoxLaw_of_power {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ} {p : ℕ}
    (hlam : 0 < lam) (hρ : ∀ k j, IsProbabilityMeasure (ρ k j)) (hP : PowerCorr ρ p) : ¬ OneBoxLaw ρ lam :=
  fun h => not_lawGapBddW_of_power hlam hP (lawGapBddW_of_oneBoxLaw hlam.le hρ h)

end Power

/-- **Unit test (fine route): a tuning without torus decay fails the fine one-box criterion.** -/
theorem not_fineOneBox_of_not_torusDecayLoc {T : Tuning} (h : ¬ TorusDecayLoc T.toV) : ¬ FineOneBox T :=
  fun hB => h (torusDecayLoc_of_fineDecayInv (fineDecayInv_of_fineOneBox hB))

end ProofPhase.OneBox
