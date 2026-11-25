/-
The one-scale reduction, Theorem C on the finite torus (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §6.1 (fact (iv)), §6.2 (Lemma 6.1), §6.3, §6.4.
-/

import OneScale.Doubling
import Positivity

/-!
# Theorem C on the finite periodic lattice: reflection positivity gives the doubling inequality

On the torus `(ℤ/Nℤ)^d`, `N` even, with a plaquette weight `φ ≥ 0` (`Positivity.PlaqWeight`, which includes Wilson for
every real `β`, soft and hard admissible weights), the reflected form
`⟨F, F'⟩ = ∫ F · (F' ∘ Θ) · ∏_p φ(Re tr U_p) d(productHaar)` (`rpForm`, unnormalised; the normalisation `1/Z` does not
change any statement below, all of which are homogeneous) is positive semidefinite on bounded measurable functions of the
closed positive half (`Positivity.rp_plaquette_weight_gram`, site reflection positivity).

* `hankel_cs`: for a family `F_j` (`j ≤ K`) of such functions whose Gram matrix is Hankel, `⟨F_j, F_k⟩ = H(j + k)`,
  Cauchy–Schwarz gives `H(j + k)² ≤ H(2j) H(2k)` and `H(2j) ≥ 0`.
* `torus_doubling` (**Lemma 6.2 on the torus**) and `torus_theoremC` (**Theorem C, finite torus**):
  `|H(m)| ≤ H(0)^{1 - 2^{-r}} H(2^r m)^{2^{-r}}`, and with a decay bound `|H(2^r m)| ≤ C e^{-λ 2^r m}` (Theorem A),
  `|H(m)| ≤ H(0)^{1 - 2^{-r}} C^{2^{-r}} e^{-λ m}`.

**Not formalised here (stated as the hypothesis `hH`):** the Hankel identity itself (Lemma 6.1:
`⟨F̊_j, F̊_k⟩ = Cov(F_{j+k}, F ∘ Θ)` for the time translates `F_j = F ∘ S_j`), which needs the time-translation invariance
of the torus measure and `S_k ∘ Θ = Θ ∘ S_{-k}` (new lattice lemmas, proof note §6.1 (ii), (iii)); and the bound on
`H(2^r m)` from Theorem A, which needs a torus distance in which the slabs `[2^r m, 2^r m + s]` and `[-s, 0]` are
`≥ 2^r m` apart (stated as the hypothesis `hdecay`).

Reflection positivity of lattice gauge theory is due to Osterwalder–Seiler (1978); the doubling argument is standard.
-/

open MeasureTheory Finset AreaLaw.Concrete Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale.TorusRP

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n] [HasHaarProbability G] [(haarG G).IsInvInvariant]

/-- The (unnormalised) reflected form `⟨F, F'⟩ = ∫ F · (F' ∘ Θ) · ∏_p φ(Re tr U_p) d(productHaar)`. -/
def rpForm (n : ℕ) [HasGaugeTrace G n] (φ : ℝ → ℝ) (F F' : GaugeConnection G d N → ℝ) : ℝ :=
  ∫ U, F U * F' (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), φ (xp n p U) ∂(productHaar G d N)

variable (hN : Even N) (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
include hN hc hU

/-- **Cauchy–Schwarz for a Hankel family of positive-half observables** (facts (iv) and Lemma 6.1 of the note). -/
theorem hankel_cs {φ : ℝ → ℝ} (hφ : PlaqWeight n φ) {F : ℕ → GaugeConnection G d N → ℝ} {K : ℕ}
    (hF : ∀ j, j ≤ K → LinkDep (F j) (posHalfLinks d N) ∧ Measurable (F j) ∧ ∃ M, ∀ U, |F j U| ≤ M)
    {H : ℕ → ℝ} (hH : ∀ j k, j ≤ K → k ≤ K → rpForm n φ (F j) (F k) = H (j + k)) :
    (∀ j k, j ≤ K → k ≤ K → H (j + k) ^ 2 ≤ H (2 * j) * H (2 * k)) ∧ (∀ j, j ≤ K → 0 ≤ H (2 * j)) := by
  refine ⟨fun j k hj hk => ?_, fun j hj => ?_⟩
  · have hq : ∀ t : ℝ, 0 ≤ H (2 * j) * (t * t) + 2 * H (j + k) * t + H (2 * k) := by
      intro t
      have h := rp_plaquette_weight_gram hN hc hU hφ (univ : Finset (Fin 2)) ![F j, F k]
        (by intro i _; fin_cases i
            · exact hF j hj
            · exact hF k hk) ![t, 1]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
      have e1 := hH j j hj hj
      have e2 := hH j k hj hk
      have e3 := hH k j hk hj
      have e4 := hH k k hk hk
      unfold rpForm at e1 e2 e3 e4
      rw [e1, e2, e3, e4, add_comm k j] at h
      rw [two_mul j, two_mul k]
      nlinarith [h]
    have := sq_le_mul_of_quadratic_nonneg hq
    linarith [mul_comm (H (2 * k)) (H (2 * j))]
  · have h := rp_plaquette_weight hN hc hU hφ (hF j hj).1 (hF j hj).2.1 (hF j hj).2.2
    have e := hH j j hj hj
    unfold rpForm at e
    rw [e] at h
    rwa [two_mul]

/-- **Lemma 6.2 on the finite torus.** -/
theorem torus_doubling {φ : ℝ → ℝ} (hφ : PlaqWeight n φ) {F : ℕ → GaugeConnection G d N → ℝ} {K : ℕ}
    (hF : ∀ j, j ≤ K → LinkDep (F j) (posHalfLinks d N) ∧ Measurable (F j) ∧ ∃ M, ∀ U, |F j U| ≤ M)
    {H : ℕ → ℝ} (hH : ∀ j k, j ≤ K → k ≤ K → rpForm n φ (F j) (F k) = H (j + k)) {m r : ℕ} (hr : 1 ≤ r)
    (hmK : 2 ^ (r - 1) * m ≤ K) :
    |H m| ≤ H 0 ^ (1 - (1 / 2 : ℝ) ^ r) * H (2 ^ r * m) ^ ((1 / 2 : ℝ) ^ r) := by
  obtain ⟨hcs, hpos⟩ := hankel_cs hN hc hU hφ hF hH
  exact doubling hcs hpos r hr hmK

/-- **Theorem C on the finite torus.** With the Hankel structure (`hH`) and a decay bound at distance `2^r m`
(`hdecay`, supplied by Theorem A), `|H(m)| ≤ H(0)^{1 - 2^{-r}} C^{2^{-r}} e^{-λ m}`. -/
theorem torus_theoremC {φ : ℝ → ℝ} (hφ : PlaqWeight n φ) {F : ℕ → GaugeConnection G d N → ℝ} {K : ℕ}
    (hF : ∀ j, j ≤ K → LinkDep (F j) (posHalfLinks d N) ∧ Measurable (F j) ∧ ∃ M, ∀ U, |F j U| ≤ M)
    {H : ℕ → ℝ} (hH : ∀ j k, j ≤ K → k ≤ K → rpForm n φ (F j) (F k) = H (j + k)) {m r : ℕ} (hr : 1 ≤ r)
    (hmK : 2 ^ (r - 1) * m ≤ K) {C lam : ℝ} (hC : 0 ≤ C)
    (hdecay : |H (2 ^ r * m)| ≤ C * Real.exp (-(lam * (2 ^ r * m : ℕ)))) :
    |H m| ≤ H 0 ^ (1 - (1 / 2 : ℝ) ^ r) * C ^ ((1 / 2 : ℝ) ^ r) * Real.exp (-(lam * m)) := by
  obtain ⟨hcs, hpos⟩ := hankel_cs hN hc hU hφ hF hH
  exact doubling_decay hcs hpos hr hmK hC hdecay

end OneScale.TorusRP
