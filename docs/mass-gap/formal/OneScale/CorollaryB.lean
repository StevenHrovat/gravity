/-
The one-scale reduction, Corollary B, lattice part (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §7 (Corollary B.1) and §4.1 (the rate condition).
-/

import OneScale.Gauge
import OneScale.Doubling

/-!
# Corollary B (lattice part): one physical scale

A sequence of lattice spacings `a_k → 0`, a physical length `L₀ > 0`, thin cubes of side `ℓ_k = ⌈L₀ / a_k⌉`
(so `D₁ = ℓ_k + 1`), and one `γ ∈ (0, 1)`.

* `UniformGDS` — **the open hypothesis (OS_k)** of the note: at every level `k`, GDS with the same `γ` for the family of
  thin cubes of side `ℓ_k` on the level-`k` torus, for the gauge measure with weight `φ_k`. **This is the open problem;
  nothing here proves it.**
* `rate_lt_of_lt`: any `λ < log(1/γ)/D₁` satisfies Theorem A's condition `γ e^{λ D₁} < 1`.
* `LevelDecay`: the conclusion of Theorem A + Theorem C + Corollary C1 at level `k`, in lattice units:
  `|h_k(n)| ≤ h_k(0) e^{-λ n}` for every `λ < log(1/γ)/(ℓ_k + 1)`.
* `corollaryB_lattice` (**Corollary B.1, lattice part**): from `LevelDecay` at every level, in physical units
  (time `t = n a_k`): `|h_k(n)| ≤ h_k(0) exp(-log(1/γ) · n a_k / (L₀ + 2 a_k))`; the physical rate
  `m_k = log(1/γ)/((ℓ_k + 1) a_k)` satisfies `m_k ≥ log(1/γ)/(L₀ + 2 a_k)` and `m_k → log(1/γ)/L₀`.

**What links `UniformGDS` to `LevelDecay`, and what of it is formal.** Theorem A on the torus
(`OneScale.BlockSpec.theoremA_H` with `OneScale.Gauge.gaugeBlockSpec`, formal), Theorem C on the finite torus
(`OneScale.TorusRP.torus_theoremC`, formal given the Hankel identity), Corollary C1 (`OneScale.prefactor_free`, formal).
Not formal: the Hankel identity (time-translation invariance, note Lemma 6.1), a torus link distance with the slab
separation used in Theorem C, and the existence of limit points (note Lemma 6.3). The spectral reading of the rate as a
transfer-matrix gap (note Theorem C2, Osterwalder–Seiler reconstruction) is not formalised; here "gap" means the
exponential decay rate of the limit correlations.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale.CorollaryB

/-! ## Thin cubes and the open hypothesis -/

section Hypothesis

open OneScale.Gauge

variable {d : ℕ}

/-- The thin cube of side `ℓ` at the site `x` of the torus: links with both ends in `x + {0, …, ℓ}^d` (mod `N`). -/
def thinCube {N : ℕ} [NeZero N] (ℓ : ℕ) (x : FinLatticeSites d N) : Finset (LatticeLink d N) :=
  univ.filter fun l => ∀ i, (l.site i - x i).val ≤ ℓ ∧ (l.target i - x i).val ≤ ℓ

/-- The cube side at level `k`: `ℓ_k = ⌈L₀ / a_k⌉`. -/
def side (L₀ : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℕ := ⌈L₀ / a k⌉₊

/-- **Hypothesis (OS_k) — OPEN.** At every level `k` (torus `(ℤ/N_kℤ)^d`, weight `φ_k`, e.g. Wilson at `β_k`),
there are influence bounds `κ_x(z)` for the thin cubes of side `ℓ_k = ⌈L₀/a_k⌉` (one block per site `x`) satisfying
GDS with the same `γ`. This is the uniform one-scale bound of the proof note (§7, "the hypothesis (OS_k) ... is the open
problem"); it is stated, not proved. -/
def UniformGDS {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] (n : ℕ) [HasGaugeTrace G n]
    (Nk : ℕ → ℕ) [∀ k, NeZero (Nk k)] (φ : ℕ → ℝ → ℝ) (L₀ γ : ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ κ : FinLatticeSites d (Nk k) → LatticeLink d (Nk k) → ℝ,
    (∀ x z, z ∉ thinCube (side L₀ a k) x →
      IsInfluenceBound (thinCube (side L₀ a k) x)
        (gaugeSpec (G := G) n (φ k) (thinCube (side L₀ a k) x)) z (κ x z)) ∧
    GDS (thinCube (side L₀ a k)) κ γ

end Hypothesis

/-! ## The rate condition of Theorem A -/

/-- Any `λ < log(1/γ)/D₁` satisfies `γ e^{λ D₁} < 1` (`0 < γ`, `0 < D₁`). -/
theorem rate_lt_of_lt {γ D₁ lam : ℝ} (hγ : 0 < γ) (hD : 0 < D₁) (hlam : lam < Real.log (1 / γ) / D₁) :
    γ * Real.exp (lam * D₁) < 1 := by
  have h1 : lam * D₁ < Real.log (1 / γ) := by rwa [lt_div_iff₀ hD] at hlam
  have h2 : Real.exp (lam * D₁) < 1 / γ := by
    rw [← Real.exp_log (one_div_pos.2 hγ)]; exact Real.exp_lt_exp.2 h1
  calc γ * Real.exp (lam * D₁) < γ * (1 / γ) := mul_lt_mul_of_pos_left h2 hγ
    _ = 1 := by field_simp

/-! ## Physical units -/

/-- `(ℓ + 1) a ≤ L₀ + 2a` for `ℓ = ⌈L₀/a⌉`. -/
theorem side_mul_le {L₀ : ℝ} (hL₀ : 0 ≤ L₀) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (k : ℕ) :
    ((side L₀ a k : ℝ) + 1) * a k ≤ L₀ + 2 * a k := by
  have h := Nat.ceil_lt_add_one (div_nonneg hL₀ (ha k).le)
  have : (side L₀ a k : ℝ) ≤ L₀ / a k + 1 := by unfold side; exact h.le
  calc ((side L₀ a k : ℝ) + 1) * a k ≤ (L₀ / a k + 2) * a k :=
        mul_le_mul_of_nonneg_right (by linarith) (ha k).le
    _ = L₀ + 2 * a k := by rw [add_mul, div_mul_cancel₀ _ (ha k).ne']

/-- `(ℓ + 1) a ≥ L₀ + a` for `ℓ = ⌈L₀/a⌉`. -/
theorem le_side_mul {L₀ : ℝ} {a : ℕ → ℝ} (ha : ∀ k, 0 < a k) (k : ℕ) :
    L₀ + a k ≤ ((side L₀ a k : ℝ) + 1) * a k := by
  have : L₀ / a k ≤ (side L₀ a k : ℝ) := by unfold side; exact Nat.le_ceil _
  calc L₀ + a k = (L₀ / a k + 1) * a k := by rw [add_mul, div_mul_cancel₀ _ (ha k).ne', one_mul]
    _ ≤ ((side L₀ a k : ℝ) + 1) * a k := mul_le_mul_of_nonneg_right (by linarith) (ha k).le

/-- The physical rate at level `k`: `m_k = log(1/γ)/((ℓ_k + 1) a_k)`. -/
def physMass (L₀ γ : ℝ) (a : ℕ → ℝ) (k : ℕ) : ℝ := Real.log (1 / γ) / (((side L₀ a k : ℝ) + 1) * a k)

/-- The conclusion of Theorem A + Theorem C + Corollary C1 at level `k`, in lattice units: the limit correlation
`h_k` decays at every rate below `log(1/γ)/(ℓ_k + 1)`, with prefactor `h_k(0)`. -/
def LevelDecay (L₀ γ : ℝ) (a : ℕ → ℝ) (h : ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ lam : ℝ, 0 ≤ lam → lam < Real.log (1 / γ) / ((side L₀ a k : ℝ) + 1) →
    ∀ n : ℕ, |h k n| ≤ h k 0 * Real.exp (-(lam * n))

/-- **Corollary B.1 (lattice part, physical units).** If at every level the limit correlations decay at every rate
below `log(1/γ)/(ℓ_k + 1)` (what Theorem A + C + C1 give under `UniformGDS`), then
1. `|h_k(n)| ≤ h_k(0) · exp(-(log(1/γ)/(L₀ + 2a_k)) · n a_k)` (decay in physical time `t = n a_k` with mass
   at least `log(1/γ)/(L₀ + 2a_k)`);
2. `m_k ≥ log(1/γ)/(L₀ + 2a_k)`;
3. `m_k → log(1/γ)/L₀` as `a_k → 0`. -/
theorem corollaryB_lattice {L₀ γ : ℝ} (hL₀ : 0 < L₀) (hγ0 : 0 < γ) (hγ1 : γ < 1) {a : ℕ → ℝ}
    (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0)) {h : ℕ → ℕ → ℝ} (hdec : LevelDecay L₀ γ a h) :
    (∀ k n, |h k n| ≤ h k 0 * Real.exp (-(Real.log (1 / γ) / (L₀ + 2 * a k) * (n * a k)))) ∧
    (∀ k, Real.log (1 / γ) / (L₀ + 2 * a k) ≤ physMass L₀ γ a k) ∧
    Tendsto (physMass L₀ γ a) atTop (𝓝 (Real.log (1 / γ) / L₀)) := by
  have hlog : 0 < Real.log (1 / γ) := Real.log_pos (by rw [lt_div_iff₀ hγ0]; linarith)
  have hmass : ∀ k, Real.log (1 / γ) / (L₀ + 2 * a k) ≤ physMass L₀ γ a k := by
    intro k
    unfold physMass
    have hpos : 0 < ((side L₀ a k : ℝ) + 1) * a k := mul_pos (by positivity) (ha k)
    exact div_le_div_of_nonneg_left hlog.le hpos (side_mul_le hL₀.le ha k)
  refine ⟨fun k n => ?_, hmass, ?_⟩
  · set Λ := Real.log (1 / γ) / ((side L₀ a k : ℝ) + 1)
    have hΛ : 0 < Λ := div_pos hlog (by positivity)
    -- `h_k(0) ≥ 0` (rate `0`, `n = 0`)
    have hh0 : 0 ≤ h k 0 := by
      have := hdec k 0 le_rfl hΛ 0
      simp only [Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
      exact (abs_nonneg _).trans this
    -- pass to the endpoint rate `Λ`
    have hend : |h k n| ≤ h k 0 * Real.exp (-(Λ * n)) := by
      have hlim : Tendsto (fun lam : ℝ => h k 0 * Real.exp (-(lam * n))) (𝓝[<] Λ)
          (𝓝 (h k 0 * Real.exp (-(Λ * n)))) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds
        exact ((Real.continuous_exp.comp ((continuous_id.mul continuous_const).neg)).const_mul _).tendsto Λ
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT hΛ] with lam hl
      exact hdec k lam hl.1.le hl.2 n
    refine hend.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hh0)
    -- `Λ n ≥ (log(1/γ)/(L₀ + 2a)) n a`
    have hm := hmass k
    unfold physMass at hm
    have e : Λ = physMass L₀ γ a k * a k := by
      have := (ha k).ne'
      unfold physMass; simp only [Λ]; field_simp
    rw [e]
    unfold physMass
    have hn : (0 : ℝ) ≤ n * a k := mul_nonneg (Nat.cast_nonneg _) (ha k).le
    have := mul_le_mul_of_nonneg_right hm hn
    nlinarith [this]
  · -- squeeze `(ℓ_k + 1) a_k` between `L₀ + a_k` and `L₀ + 2 a_k`
    have hlo : Tendsto (fun k => L₀ + a k) atTop (𝓝 L₀) := by
      simpa using tendsto_const_nhds.add ha0
    have hhi : Tendsto (fun k => L₀ + 2 * a k) atTop (𝓝 L₀) := by
      simpa using tendsto_const_nhds.add (ha0.const_mul 2)
    have hden : Tendsto (fun k => ((side L₀ a k : ℝ) + 1) * a k) atTop (𝓝 L₀) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun k => le_side_mul ha k)
        (fun k => side_mul_le hL₀.le ha k)
    exact tendsto_const_nhds.div hden hL₀.ne'

end OneScale.CorollaryB
