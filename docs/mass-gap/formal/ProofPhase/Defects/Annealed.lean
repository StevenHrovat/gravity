/-
Proof phase, cycle 5, workstream 4 (c5d-supplier): Dobrushin's theorem with rare defects, averaged over a random defect
set (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5d-supplier/NOTE.md`, Part B.
-/

import ProofPhase.Defects.Quenched

/-!
# Dobrushin with rare defects: the averaged (annealed-in-the-environment) theorem

**Setting.** A random defect set `B` with law `q` (nonnegative weights on `Finset ι`), dominated on cylinders by a
Bernoulli field: `∑_B q B · 1[U ⊆ B] ≤ p₀^{|U|}` (`EffDist.lean`). For each `B` a probability measure `μ B` (the law
**given** the defect set: for an external environment the quenched law; for Balaban's large-field set the law
conditioned on `{Bad = B}`) whose block specification satisfies, in the effective metric of `B`, the hypotheses of
`quenched_defect_W` (`DefectSpecW`).

**Headline (`defect_decay_W`, S).** With `x := Δ (p₀ + e^{−2λ}) < 1` and `R ≤ dist_G(a, s)` for `a ∈ A`, `s ∈ S_g`,
and a second-moment bound `E_q m_B(a)² ≤ M²` on the block mass at the sites of `A`:

  `E_q |Cov_{μ B}(f, g)| ≤ L_g D_c / (1 − γ e^{λD₁}) · e^{λD₀} · M · (∑_{a ∈ A} v_a) · √(x^R / (1 − x))`.

The right side decays like `(√x)^R`, uniformly in the size of `ι` (no volume anywhere). Good sites must contract
(`γ e^{λD₁} < 1` on the influences that GDS sees), defects must be rare (`p₀` small against `1/Δ`), and the price of
the defects is the rate: `λ` in the quenched bound becomes `−½ log(Δ (p₀ + e^{−2λ}))` after averaging.

**Exactly what this is, and what it is not.** It bounds the average over the environment of the **conditional**
covariance. For a measure `μ = ∑_B q B μ_B` (`mixture_cov_eq`, D):

  `Cov_μ(f, g) = E_q Cov_{μ_B}(f, g) + Cov_q(μ_B f, μ_B g)`.

The second term (the environment term) is **not** controlled by these hypotheses, and cannot be: a two-point mixture
`q = ½ δ_∅ + ½ δ_{B₁}` with product measures `μ_B` has every conditional covariance zero (so every hypothesis holds with
`γ = 0`), while `Cov_q` of the defect indicators near `A` and near `S_g` is a constant independent of the distance
(the mixture unit test, NOTE.md B.4). An annealed decay statement for `μ` itself needs in addition that the environment
mixes: for an external i.i.d. environment this follows from a comparison argument (not formalised); for a defect set
that is a function of the field (Balaban's large-field set, OpenAI's `flags`) it is a statement of the same kind as the
conclusion, at small density, and is the precise missing piece (NOTE.md B.5).
-/

open MeasureTheory Finset OneScale SimpleGraph

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Defects

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]
variable {G : SimpleGraph ι} [DecidableRel G.Adj]

/-! ## The averaging step -/

/-- **Averaging a quenched bound over a cylinder-dominated defect set** (S, Cauchy–Schwarz plus the Peierls bound). -/
theorem annealed_of_quenched (hG : G.Preconnected) {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (q : Finset ι → ℝ) (hq : ∀ B, 0 ≤ q B) {p0 : ℝ} (hp0 : 0 ≤ p0)
    (hcyl : ∀ U : Finset ι, ∑ B, q B * (if U ⊆ B then 1 else 0) ≤ p0 ^ U.card)
    {lam : ℝ} (hlam : 0 ≤ lam) {Sg A : Finset ι} (hSg : Sg.Nonempty) {R : ℕ}
    (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ G.dist a s)
    (hx : (Δ : ℝ) * (p0 + Real.exp (-(2 * lam))) < 1)
    (Cv : Finset ι → ℝ) {K : ℝ} (hK : 0 ≤ K) {vf : ι → ℝ} (hvf0 : ∀ a, 0 ≤ vf a)
    (m : Finset ι → ι → ℝ) (hm0 : ∀ B a, 0 ≤ m B a)
    (hquen : ∀ B, Cv B ≤ K * ∑ a ∈ A, vf a * m B a * effWeight G B lam Sg a)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a ∈ A, ∑ B, q B * m B a ^ 2 ≤ M ^ 2) :
    ∑ B, q B * Cv B ≤
      K * M * (∑ a ∈ A, vf a) *
        Real.sqrt (((Δ : ℝ) * (p0 + Real.exp (-(2 * lam)))) ^ R /
          (1 - (Δ : ℝ) * (p0 + Real.exp (-(2 * lam))))) := by
  set x := (Δ : ℝ) * (p0 + Real.exp (-(2 * lam)))
  set Q := Real.sqrt (x ^ R / (1 - x))
  set w := fun B a => effWeight G B lam Sg a
  have hw0 : ∀ B a, 0 ≤ w B a := fun B a => effWeight_nonneg B lam Sg a
  -- the square of the weight is the weight at rate `2λ`
  have hw2 : ∀ B a, w B a ^ 2 = effWeight G B (2 * lam) Sg a := by
    intro B a
    simp only [w, effWeight, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- per site: Cauchy–Schwarz and Peierls
  have hsite : ∀ a ∈ A, ∑ B, q B * (m B a * w B a) ≤ M * Q := by
    intro a ha
    have hcs : ∑ B, q B * (m B a * w B a) ≤
        Real.sqrt (∑ B, q B * m B a ^ 2) * Real.sqrt (∑ B, q B * w B a ^ 2) := by
      have h := Real.sum_sqrt_mul_sqrt_le univ (f := fun B => q B * m B a ^ 2) (g := fun B => q B * w B a ^ 2)
        (fun B => mul_nonneg (hq B) (sq_nonneg _)) (fun B => mul_nonneg (hq B) (sq_nonneg _))
      refine le_trans (le_of_eq ?_) h
      refine sum_congr rfl fun B _ => ?_
      rw [← Real.sqrt_mul (mul_nonneg (hq B) (sq_nonneg _))]
      have : q B * m B a ^ 2 * (q B * w B a ^ 2) = (q B * (m B a * w B a)) ^ 2 := by ring
      rw [this, Real.sqrt_sq (mul_nonneg (hq B) (mul_nonneg (hm0 B a) (hw0 B a)))]
    have hpe : ∑ B, q B * w B a ^ 2 ≤ x ^ R / (1 - x) := by
      simp_rw [hw2]
      have h2lam : 0 ≤ 2 * lam := by linarith
      exact expect_effWeight_le_geom hG hdeg q hq hp0 hcyl h2lam hSg a (hR a ha) hx
    refine hcs.trans (mul_le_mul ?_ (Real.sqrt_le_sqrt hpe) (Real.sqrt_nonneg _) hM0)
    calc Real.sqrt (∑ B, q B * m B a ^ 2) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt (hM a ha)
      _ = M := Real.sqrt_sq hM0
  calc ∑ B, q B * Cv B ≤ ∑ B, q B * (K * ∑ a ∈ A, vf a * m B a * w B a) :=
        sum_le_sum fun B _ => mul_le_mul_of_nonneg_left (hquen B) (hq B)
    _ = K * ∑ a ∈ A, vf a * ∑ B, q B * (m B a * w B a) := by
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun a _ => sum_congr rfl fun B _ => ?_
        ring
    _ ≤ K * ∑ a ∈ A, vf a * (M * Q) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hsite a ha) (hvf0 a)) hK
    _ = K * M * (∑ a ∈ A, vf a) * Q := by rw [← sum_mul]; ring

/-! ## The per-environment hypotheses and the headline -/

/-- **The quenched defect hypotheses for one defect set `B`** (W₁ form): a block specification of `μB` with W₁
influence coefficients satisfying GDS with `γ`, coverage `≥ 1`, influences of finite range `D₁` and blocks of diameter
`≤ D₀` **in the effective metric of `B`**, and block masses `≤ mB`. -/
def DefectSpecW (G : SimpleGraph ι) [DecidableRel G.Adj] (c : S → S → ℝ) (μB : Measure (ι → S)) (B : Finset ι)
    (γ D₀ D₁ : ℝ) (mB : ι → ℝ) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (P : BlockSpec μB J) (k : J → ι → ℝ) (cmin : ℕ),
    (∀ j z, z ∉ P.block j → IsInfluenceBoundW c (P.block j) (P.spec j) z (k j z)) ∧
    GDS P.block k γ ∧ 1 ≤ cmin ∧ (∀ x, cmin ≤ coverage P.block x) ∧
    (∀ j x y, x ∉ P.block j → y ∈ P.block j → k j x ≠ 0 → (effDist G B x {y} : ℝ) ≤ D₁) ∧
    (∀ j, ∀ a ∈ P.block j, ∀ y ∈ P.block j, (effDist G B a {y} : ℝ) ≤ D₀) ∧
    (∀ a, blockMass P.block a ≤ mB a)

/-- **Dobrushin's theorem with rare defects** (W₁ form, averaged over the defect set). -/
theorem defect_decay_W [Nonempty ι] (hG : G.Preconnected) {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (q : Finset ι → ℝ) (hq : ∀ B, 0 ≤ q B) {p0 : ℝ} (hp0 : 0 ≤ p0)
    (hcyl : ∀ U : Finset ι, ∑ B, q B * (if U ⊆ B then 1 else 0) ≤ p0 ^ U.card)
    (μ : Finset ι → Measure (ι → S)) [∀ B, IsProbabilityMeasure (μ B)]
    {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc)
    {γ D₀ D₁ lam : ℝ} (hγ : 0 ≤ γ) (hlam : 0 ≤ lam) (hρ : γ * Real.exp (lam * D₁) < 1)
    (m : Finset ι → ι → ℝ) (hspec : ∀ B, DefectSpecW G c (μ B) B γ D₀ D₁ (m B))
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hSg : Sg.Nonempty) (hfA : DepOn f A)
    (hgS : DepOn g Sg) {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg)
    (hvg : LipBound c g (fun _ => Lg)) {R : ℕ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ G.dist a s)
    (hx : (Δ : ℝ) * (p0 + Real.exp (-(2 * lam))) < 1)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a ∈ A, ∑ B, q B * m B a ^ 2 ≤ M ^ 2) :
    ∑ B, q B * |∫ σ, f σ * g σ ∂(μ B) - (∫ σ, f σ ∂(μ B)) * ∫ σ, g σ ∂(μ B)| ≤
      Lg * Dc / (1 - γ * Real.exp (lam * D₁)) * Real.exp (lam * D₀) * M * (∑ a ∈ A, vf a) *
        Real.sqrt (((Δ : ℝ) * (p0 + Real.exp (-(2 * lam)))) ^ R /
          (1 - (Δ : ℝ) * (p0 + Real.exp (-(2 * lam))))) := by
  obtain ⟨σ₀⟩ := nonempty_of_isProbabilityMeasure (μ ∅)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty ι)
  have hDc : 0 ≤ Dc := (hc0 (σ₀ x₀) (σ₀ x₀)).trans (hcD _ _)
  have hvf0 : ∀ a, 0 ≤ vf a := fun a => hvf.nonneg σ₀ a
  have hgap : 0 < 1 - γ * Real.exp (lam * D₁) := by linarith
  set K := Lg * Dc / (1 - γ * Real.exp (lam * D₁)) * Real.exp (lam * D₀)
  have hK : 0 ≤ K := mul_nonneg (div_nonneg (mul_nonneg hLg hDc) hgap.le) (Real.exp_pos _).le
  -- the quenched bound with the block mass replaced by `m B`
  have hquen : ∀ B, |∫ σ, f σ * g σ ∂(μ B) - (∫ σ, f σ ∂(μ B)) * ∫ σ, g σ ∂(μ B)| ≤
      K * ∑ a ∈ A, vf a * max (m B a) 0 * effWeight G B lam Sg a := by
    intro B
    obtain ⟨J, hJ, P, k, cmin, hk, hgds, hc1, hcov, hD₁, hD₀, hmass⟩ := hspec B
    have h := quenched_defect_W P hG B hc0 hcD k hk hγ hgds hc1 hcov hlam hD₁ hD₀ hρ hf hg hSg hfA hgS hvf hLg hvg
    refine h.trans (mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => ?_) hK)
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (hvf0 a)) (effWeight_nonneg B lam Sg a)
    exact (hmass a).trans (le_max_left _ _)
  have hM' : ∀ a ∈ A, ∑ B, q B * max (m B a) 0 ^ 2 ≤ M ^ 2 := by
    intro a ha
    refine le_trans (sum_le_sum fun B _ => mul_le_mul_of_nonneg_left ?_ (hq B)) (hM a ha)
    rcases le_total (m B a) 0 with h | h
    · rw [max_eq_right h]; simp [sq_nonneg]
    · rw [max_eq_left h]
  have := annealed_of_quenched hG hdeg q hq hp0 hcyl hlam hSg hR hx _ hK hvf0 (fun B a => max (m B a) 0)
    (fun B a => le_max_right _ _) hquen hM0 hM'
  exact this.trans (le_of_eq (by ring))

/-! ## The environment term -/

/-- **Total covariance for a mixture** (D, an identity; it is the covariance of `μ = ∑_B q B μ_B` when
`∑ q = 1`). With the conditional
moments `Ff B = μ_B f`, `Fg B = μ_B g`, `Ffg B = μ_B (f g)`: the covariance of the mixture is the average conditional
covariance plus the covariance of the conditional means under `q`. -/
theorem mixture_cov_eq {T : Type*} (s : Finset T) (q Ff Fg Ffg : T → ℝ) :
    (∑ B ∈ s, q B * Ffg B) - (∑ B ∈ s, q B * Ff B) * (∑ B ∈ s, q B * Fg B) =
      ∑ B ∈ s, q B * (Ffg B - Ff B * Fg B) +
        ((∑ B ∈ s, q B * (Ff B * Fg B)) - (∑ B ∈ s, q B * Ff B) * (∑ B ∈ s, q B * Fg B)) := by
  have : ∑ B ∈ s, q B * (Ffg B - Ff B * Fg B) = ∑ B ∈ s, q B * Ffg B - ∑ B ∈ s, q B * (Ff B * Fg B) := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun B _ => by ring
  rw [this]; ring

/-- **The environment term is not small in general** (D, the mixture unit test). Two environments with weight `½`,
conditional means `0, 1` for both observables: the mixture covariance is `¼` although every conditional covariance
vanishes. -/
theorem mixture_counterexample :
    let q : Bool → ℝ := fun _ => 1 / 2
    let F : Bool → ℝ := fun b => if b then 1 else 0
    (∑ b, q b * (F b * F b)) - (∑ b, q b * F b) * (∑ b, q b * F b) = 1 / 4 := by
  simp
  norm_num

end ProofPhase.Defects
