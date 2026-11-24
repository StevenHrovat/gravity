/-
Proof phase, cycle 4, workstream 1 (c4a-condmass): `CondMass`, the conditioned fine system has a mass at the block
scale (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c4a-condmass/NOTE.md`.
-/

import ProofPhase.V3.TimeSep
import ProofPhase.UV.Split

/-!
# `CondMass`: a Dobrushin–Shlosman condition for the fine field conditioned on the block field

**The hypothesis.** For a blocking family `B` of the SU(2) Wilson measure along a tuning `T`, `CondMass T B` says: from some
level on, in every volume, the fine field **conditioned on the block field** satisfies a Dobrushin–Shlosman condition at
the block scale, with constants independent of the level, the volume and the block configuration. Precisely:

* **Cells (super-sites).** A map `cell k j` from the fine links to the coarse links (each coarse link owns a cell of fine
  links of physical size `L₁`), with the two-sided comparison `CellGeometry` of physical and coarse distances
  (`a_k d(e, e') ≤ L₁ (d(cell e, cell e') + c₀)` and `L₁ d(cell e, cell e') ≤ a_k d(e, e') + L₁ c₁`). The fine
  configuration is regrouped into one super-site value per cell (`cellLift`; the super-site space is the whole fine
  configuration space with the links of other cells set to `1`, so no dependent types are needed).
* **The conditional laws.** A family `κ y` of probability measures (a regular conditional law of the fine field given
  `Φ = B U = y`): `E[H | Φ](U) = ∫ H dκ(Φ U)` almost surely, for every measurable `|H| ≤ 1`.
* **The condition** (`CellDobrushin`): for almost every block configuration `y`, the conditional law `κ y`, lifted to the
  cells, is consistent with a block specification (blocks of cells, any shape) with the weighted Dobrushin–Shlosman
  condition `GDSw` of `Attempts.R3.TailDecay` (oscillation, i.e. sup/TV, influences; exponential weights at the rate `λ`
  per coarse unit), `γ < 1`, block sizes `≤ b`, coverage in `[c₋, c₊]`, block diameters `≤ D₀`: all constants uniform.

**Why this form** (NOTE.md §1): the sup/TV (oscillation) form is the one whose decay theorem covers **bounded measurable**
observables, which is what `ObsTransferPhys` quantifies over (the W₁ form gives decay only against Lipschitz observables);
it is a **block** form, because single fine links are stiff at weak coupling (a neighbouring link moves a fine link's law
by order one in total variation, for every level), while a block of `n⁴` cells feels its outside only through a boundary
layer whose depth is set by the conditional mass, a bounded number of cells uniformly in the level: the surface-to-volume
ratio `~ 1/n` then makes the column sums small (the Dobrushin–Shlosman mechanism). A log-Sobolev form would need an LSI ⇒
spatial-mixing theorem that is not in the library and is not more plausible here.

**The theorems.**
* `condCov`, `condDefect_eq_integral_condCov`, `abs_condDefect_le_of_ae` (D/S small, generic): the conditional decoupling
  defect of `ObsTransferPhys` (c) is the integral of the conditional covariance `E[FG|m] − E[F|m] E[G|m]`, so an almost
  sure bound on the conditional covariance bounds (c).
* `abs_cov_le_of_cellDobrushin` (S, generic: Theorem A with weights on the super-sites): a law with `CellDobrushin` has
  `|Cov(F, G)| ≤ b/(c₋(1 − γ)) · c₊ · 2 #cells(F) · 2 · e^{−λ(R − D₀)}` for `|F|, |G| ≤ 1` whose cells are at coarse
  distance `≥ R`.
* `condMassDecay_of_condMass` (S): `CondMass ⇒ CondMassDecay` (the conditional covariance of bounded observables of
  physical extent `≤ R` at physical distance `≥ D` is `≤ c_R e^{−(λ/L₁) D}` almost surely, uniformly in level and volume).
* `obsTransferPhysT_of_condMass` (S): `CondMassDecay ∧ ObsQuasiLocT ⇒ ObsTransferPhysT`: `CondMass` supplies part (c);
  parts (a), (b) (quasi-locality of `E[F|Φ]`) are the separate named input `ObsQuasiLocT` (for a deterministic blocking
  they do not follow from `CondMass`; for a noisy blocking they do, on paper, NOTE.md §2).

**Claim level.** Group-blind proofs; the hypotheses are about the blocked SU(2) Wilson laws along `T`. `CondMass` holds for
the photon at Gaussian level in the time direction (c3a) and gives it no gap: it is not the gap.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift OneScale.CubeChain Positivity ProofPhase.Existence ProofPhase.RouteA ProofPhase.Torus
  ProofPhase.H1

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.V3

/-! ## The conditional covariance (generic) -/

section Generic

variable {X : Type*} {mX : MeasurableSpace X} (μ : Measure[mX] X) [IsProbabilityMeasure μ]

/-- **The conditional covariance** `E[FG|m] − E[F|m] E[G|m]` (a random variable). -/
def condCov (m : MeasurableSpace X) (F G : X → ℝ) : X → ℝ :=
  fun x => μ[fun y => F y * G y | m] x - μ[F | m] x * μ[G | m] x

variable {μ}

/-- **The defect of (c) is the mean conditional covariance** (D). -/
theorem condDefect_eq_integral_condCov {m : MeasurableSpace X} (hm : m ≤ mX) {F G : X → ℝ} (hF : UV.Bdd1 μ F)
    (hG : UV.Bdd1 μ G) : UV.condDefect μ m F G = ∫ x, condCov μ m F G x ∂μ := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  unfold UV.condDefect condCov
  rw [integral_sub integrable_condExp ((hF.condExp hm).mul (hG.condExp hm)).integrable, integral_condExp hm]

/-- **An almost sure bound on the conditional covariance bounds the conditional decoupling defect** (S, small). -/
theorem abs_condDefect_le_of_ae {m : MeasurableSpace X} (hm : m ≤ mX) {F G : X → ℝ} (hF : UV.Bdd1 μ F)
    (hG : UV.Bdd1 μ G) {ε : ℝ} (h : ∀ᵐ x ∂μ, |condCov μ m F G x| ≤ ε) : |UV.condDefect μ m F G| ≤ ε := by
  rw [condDefect_eq_integral_condCov hm hF hG]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := condCov μ m F G) (C := ε)
    (h.mono fun x hx => by rwa [Real.norm_eq_abs])
  simpa using this

end Generic

/-! ## Super-sites (generic) -/

section Cells

variable {L C S : Type*} [Fintype C] [DecidableEq C] [MeasurableSpace S]

/-- **Regroup a configuration by cells**: the value at the cell `c` is the configuration with the links outside `c` set
to `s₀`. -/
def cellLift (cell : L → C) (s₀ : S) (U : L → S) : C → (L → S) := fun c e => if cell e = c then U e else s₀

/-- Read a configuration back from its cell values. -/
def cellProj (cell : L → C) (W : C → (L → S)) : L → S := fun e => W (cell e) e

theorem cellProj_cellLift (cell : L → C) (s₀ : S) (U : L → S) : cellProj cell (cellLift cell s₀ U) = U := by
  funext e; simp [cellProj, cellLift]

theorem measurable_cellLift (cell : L → C) (s₀ : S) : Measurable (cellLift cell s₀) := by
  refine measurable_pi_iff.mpr fun c => measurable_pi_iff.mpr fun e => ?_
  by_cases h : cell e = c
  · simp only [cellLift, h, ↓reduceIte]; exact measurable_pi_apply e
  · simp only [cellLift, h, ↓reduceIte]; exact measurable_const

theorem measurable_cellProj (cell : L → C) : Measurable (cellProj (S := S) cell) :=
  measurable_pi_iff.mpr fun e => (measurable_pi_apply e).comp (measurable_pi_apply (cell e))

theorem depOn_comp_cellProj {F : (L → S) → ℝ} {A : Finset L} (hF : DepOn F A) (cell : L → C) :
    DepOn (fun W => F (cellProj cell W)) (A.image cell) := by
  intro W W' h
  apply hF
  intro e he
  show W (cell e) e = W' (cell e) e
  rw [h (cell e) (Finset.mem_image_of_mem cell he)]

/-- **The Dobrushin–Shlosman condition at the cell scale** for a law `ρ` of the fine configuration: the lifted law
`ρ ∘ cellLift⁻¹` is consistent with a block specification `P` (blocks of cells) with oscillation influence coefficients
`k`, weighted condition `GDSw` with weights `e^{λ E}` and `γ`, block sizes `≤ b`, coverage in `[c₋, c₊]`, block
diameters `≤ D₀` for the cell distance `dist`. -/
def CellDobrushin (ρ : Measure (L → S)) (cell : L → C) (s₀ : S) (dist : C → C → ℝ) (lam γ D₀ : ℝ)
    (b cmin cmax : ℕ) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (P : BlockSpec (ρ.map (cellLift cell s₀)) J) (k E : J → C → ℝ),
    (∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (k j z)) ∧
    (∀ x, cmin ≤ coverage P.block x) ∧ (∀ x, coverage P.block x ≤ cmax) ∧ (∀ j, (P.block j).card ≤ b) ∧
    (∀ j, ∀ x ∈ P.block j, ∀ y ∈ P.block j, dist x y ≤ D₀) ∧
    (∀ j x y, x ∉ P.block j → y ∈ P.block j → dist x y ≤ E j x) ∧
    Attempts.R3.GDSw P.block k (fun j x => Real.exp (lam * E j x)) γ

/-- **Decay under the cell condition** (S: Theorem A with weights, `Attempts.R3.theoremA_w`, on the super-sites). -/
theorem abs_cov_le_of_cellDobrushin [Nonempty C] (ρ : Measure (L → S)) [IsProbabilityMeasure ρ] {cell : L → C}
    {s₀ : S} {dist : C → C → ℝ} (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {lam γ D₀ : ℝ} {b cmin cmax : ℕ} (hlam : 0 ≤ lam) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hc1 : 1 ≤ cmin)
    (hD : CellDobrushin ρ cell s₀ dist lam γ D₀ b cmin cmax)
    {F G : (L → S) → ℝ} (mF : Measurable F) (mG : Measurable G) (bF : ∀ U, |F U| ≤ 1) (bG : ∀ U, |G U| ≤ 1)
    {A₀ B₀ : Finset L} (dF : DepOn F A₀) (dG : DepOn G B₀) {R : ℝ}
    (hR : ∀ a ∈ A₀, ∀ a' ∈ B₀, R ≤ dist (cell a) (cell a')) :
    |∫ U, F U * G U ∂ρ - (∫ U, F U ∂ρ) * ∫ U, G U ∂ρ| ≤
      b / (cmin * (1 - γ)) * (cmax * (2 * ((A₀.image cell).card : ℝ))) * 2 * Real.exp (-(lam * (R - D₀))) := by
  obtain ⟨J, hJ, P, k, E, hk, hcov, hcmax, hb, hD₀, hE, hgds⟩ := hD
  have : IsProbabilityMeasure (ρ.map (cellLift cell s₀)) := inferInstance
  have hf : BM (fun W => F (cellProj cell W)) := ⟨mF.comp (measurable_cellProj cell), 1, fun W => bF _⟩
  have hg : BM (fun W => G (cellProj cell W)) := ⟨mG.comp (measurable_cellProj cell), 1, fun W => bG _⟩
  have hvf : OscBound (fun W => F (cellProj cell W)) (fun _ => (2 : ℝ)) := fun W x s =>
    (abs_sub _ _).trans (by linarith [bF (cellProj cell W), bF (cellProj cell (Function.update W x s))])
  have hvg : OscBound (fun W => G (cellProj cell W)) (fun _ => (2 : ℝ)) := fun W x s =>
    (abs_sub _ _).trans (by linarith [bG (cellProj cell W), bG (cellProj cell (Function.update W x s))])
  have hR' : ∀ a ∈ A₀.image cell, ∀ s ∈ B₀.image cell, R ≤ dist a s := by
    intro a ha s hs
    obtain ⟨e, he, rfl⟩ := mem_image.1 ha
    obtain ⟨e', he', rfl⟩ := mem_image.1 hs
    exact hR e he e' he'
  have h := Attempts.R3.theoremA_w P k hk hc1 hcov hcmax hb dist hd0 htri hD₀ E hE hlam hγ0 hγ1 hgds hf hg
    (depOn_comp_cellProj dF cell) (depOn_comp_cellProj dG cell) hvf (by norm_num : (0 : ℝ) ≤ 2) hvg hR'
  have e := OneScale.Effective.cov_map ρ (measurable_cellLift cell s₀) hf hg
  simp only [cellProj_cellLift] at e
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

end Cells

/-! ## `CondMass` on the real objects -/

/-- **Cells of physical size `L₁`**: the cell map compares physical and coarse distances from both sides. -/
def CellGeometry (T : Tuning) (cell : ∀ k j, LatticeLink 4 (T.side k j) → LatticeLink 4 (coarseSide j))
    (c₀ c₁ : ℝ) : Prop :=
  (∀ k j (e e' : LatticeLink 4 (T.side k j)),
    T.a k * linkDist e e' ≤ T.L₁ * (linkDist (cell k j e) (cell k j e') + c₀)) ∧
  (∀ k j (e e' : LatticeLink 4 (T.side k j)),
    T.L₁ * linkDist (cell k j e) (cell k j e') ≤ T.a k * linkDist e e' + T.L₁ * c₁)

/-- **`CondMass` (named hypothesis, open): the fine field conditioned on the block field has a mass at the block scale.**
There are cells of physical size `L₁`, constants `λ > 0`, `γ ∈ [0, 1)`, `D₀`, `b`, `c₋ ≥ 1`, `c₊` and a level `k₀` such
that for every level `k ≥ k₀` and volume `j` there is a regular conditional law `κ` of the fine field given the block
field, and for almost every block configuration `y` the conditional law `κ y` satisfies the Dobrushin–Shlosman condition
at the cell scale (`CellDobrushin`) with these constants. -/
def CondMass (T : Tuning) (B : BlockingFamily T) : Prop :=
  ∃ (cell : ∀ k j, LatticeLink 4 (T.side k j) → LatticeLink 4 (coarseSide j)) (c₀ c₁ : ℝ),
    CellGeometry T cell c₀ c₁ ∧
    ∃ (lam γ D₀ : ℝ) (b cmin cmax : ℕ), 0 < lam ∧ 0 ≤ γ ∧ γ < 1 ∧ 1 ≤ cmin ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
      ∃ κ : GaugeConnection SU2 4 (coarseSide j) → Measure (GaugeConnection SU2 4 (T.side k j)),
        (∀ y, IsProbabilityMeasure (κ y)) ∧
        (∀ H : GaugeConnection SU2 4 (T.side k j) → ℝ, Measurable H → (∀ U, |H U| ≤ 1) →
          condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) H =ᵐ[T.ym k j]
            fun U => ∫ V, H V ∂(κ ((B k j).B U))) ∧
        ∀ᵐ y ∂(blockedLaw T B k j), CellDobrushin (κ y) (cell k j) (1 : SU2) linkDist lam γ D₀ b cmin cmax

/-- **The decay form of `CondMass`**: one rate `m > 0`; for every physical extent `R` a constant `c` and a level `k₀`
such that for bounded measurable fine observables `F`, `G` (the support of `F` of physical extent `≤ R`) at physical
distance `≥ D`, the conditional covariance given the block field is `≤ c e^{−mD}` almost surely. -/
def CondMassDecay (T : Tuning) (B : BlockingFamily T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → DepOn F A₀ → DepOn G B₀ →
    PhysExtent T k A₀ R → (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    ∀ᵐ U ∂(T.ym k j),
      |condCov (T.ym k j) (MeasurableSpace.comap (B k j).B inferInstance) F G U| ≤ c * Real.exp (-(m * D))

/-- **`CondMass` gives the decay of the conditional covariance** (S): rate `λ/L₁`, constant
`b/(c₋(1 − γ)) · c₊ · 2 K_R · 2 · e^{λ(c₀ + D₀)}` with `K_R = 4(2⌊R/L₁ + c₁⌋ + 1)⁴` (the number of cells an observable
of physical extent `≤ R` can meet). -/
theorem condMassDecay_of_condMass {T : Tuning} {B : BlockingFamily T} (h : CondMass T B) : CondMassDecay T B := by
  obtain ⟨cell, c₀, c₁, ⟨geo1, geo2⟩, lam, γ, D₀, b, cmin, cmax, hlam, hγ0, hγ1, hc1, k₀, H⟩ := h
  have hL1 := T.L₁_pos
  refine ⟨lam / T.L₁, by positivity, fun R => ?_⟩
  set r : ℕ := ⌊R / T.L₁ + c₁⌋₊
  set K : ℝ := ((4 * (2 * r + 1) ^ 4 : ℕ) : ℝ)
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hcm : (1 : ℝ) ≤ cmin := by exact_mod_cast hc1
  have hpre : 0 ≤ (b : ℝ) / (cmin * (1 - γ)) :=
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (by linarith) (by linarith))
  set c := (b : ℝ) / (cmin * (1 - γ)) * (cmax * (2 * K)) * 2 * Real.exp (lam * (c₀ + D₀))
  have hc : 0 ≤ c := by positivity
  refine ⟨c, hc, k₀, fun k hk j F G A₀ B₀ D mF mG bF bG dF dG eA hsep => ?_⟩
  obtain ⟨κ, hprob, hce, hae⟩ := H k hk j
  haveI := UV.ymProb T k j
  have hae' : ∀ᵐ U ∂(T.ym k j), CellDobrushin (κ ((B k j).B U)) (cell k j) (1 : SU2) linkDist lam γ D₀ b cmin cmax :=
    ae_of_ae_map (B k j).meas.aemeasurable hae
  have bFG : ∀ U, |F U * G U| ≤ 1 := fun U => by
    rw [abs_mul]; exact mul_le_one₀ (bF U) (abs_nonneg _) (bG U)
  -- the cells met by `F`
  have hcard : (((A₀.image (cell k j)).card : ℕ) : ℝ) ≤ K := by
    have hsd : ∀ x ∈ A₀.image (cell k j), ∀ x' ∈ A₀.image (cell k j), siteDist x.site x'.site ≤ r := by
      intro x hx x' hx'
      obtain ⟨e, he, rfl⟩ := mem_image.1 hx
      obtain ⟨e', he', rfl⟩ := mem_image.1 hx'
      have h1 := geo2 k j e e'
      have h2 := eA e he e' he'
      have h3 : linkDist (cell k j e) (cell k j e') ≤ R / T.L₁ + c₁ := by
        rw [div_add' _ _ _ hL1.ne', le_div_iff₀ hL1]; nlinarith
      exact Nat.le_floor (by exact_mod_cast h3)
    have hc := card_le_of_siteDist hsd
    simp only [K]
    exact_mod_cast hc
  have hR : ∀ a ∈ A₀, ∀ a' ∈ B₀, D / T.L₁ - c₀ ≤ linkDist (cell k j a) (cell k j a') := by
    intro a ha a' ha'
    have h1 := geo1 k j a a'
    have h2 := hsep a ha a' ha'
    rw [sub_le_iff_le_add, div_le_iff₀ hL1]
    nlinarith
  filter_upwards [hae', hce (fun U => F U * G U) (mF.mul mG) bFG, hce F mF bF, hce G mG bG] with U hU h1 h2 h3
  unfold condCov
  rw [h1, h2, h3]
  haveI := hprob ((B k j).B U)
  have : Nonempty (LatticeLink 4 (coarseSide j)) := ⟨⟨fun _ => 0, 0⟩⟩
  have hcov := abs_cov_le_of_cellDobrushin (κ ((B k j).B U)) linkDist_self linkDist_triangle hlam.le hγ0 hγ1 hc1
    hU mF mG bF bG dF dG hR
  refine hcov.trans ?_
  have eexp : Real.exp (-(lam * (D / T.L₁ - c₀ - D₀))) =
      Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  rw [eexp]
  have hcK : (cmax : ℝ) * (2 * ((A₀.image (cell k j)).card : ℝ)) ≤ cmax * (2 * K) :=
    mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  calc (b : ℝ) / (cmin * (1 - γ)) * (cmax * (2 * ((A₀.image (cell k j)).card : ℝ))) * 2 *
        (Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D)))
      ≤ (b : ℝ) / (cmin * (1 - γ)) * (cmax * (2 * K)) * 2 *
        (Real.exp (lam * (c₀ + D₀)) * Real.exp (-(lam / T.L₁ * D))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcK hpre) (by norm_num))
          (by positivity)
    _ = c * Real.exp (-(lam / T.L₁ * D)) := by simp only [c]; ring

/-! ## `CondMass` supplies part (c) of the time-separated transfer -/

/-- **Parts (a), (b) of the time-separated transfer (named hypothesis, open):** quasi-locality of the conditional
expectations given the block field, for time-separated pairs: `ObsTransferPhysT` without the conditional decoupling. -/
def ObsQuasiLocT (T : Tuning) (B : BlockingFamily T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c K : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ), 0 ≤ D →
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e') →
    ∃ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink 4 (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ 4) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U - f ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U - g ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D))

/-- The time-separated transfer gives its quasi-locality part (D). -/
theorem obsQuasiLocT_of_obsTransferPhysT {T : Tuning} {B : BlockingFamily T} (h : ObsTransferPhysT T B) :
    ObsQuasiLocT T B := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, K, hc, k₀, Hk⟩ := H R
  refine ⟨c, K, hc, k₀, fun k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hsep', hEF, hEG, -⟩ :=
    Hk k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep
  exact ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hsep', hEF, hEG⟩

/-- **`CondMass` (decay form) and quasi-locality give the time-separated transfer** (S): the conditional decoupling
(c) follows from the almost sure bound on the conditional covariance (`abs_condDefect_le_of_ae`). -/
theorem obsTransferPhysT_of_condMassDecay {T : Tuning} {B : BlockingFamily T} (h1 : CondMassDecay T B)
    (h2 : ObsQuasiLocT T B) : ObsTransferPhysT T B := by
  obtain ⟨m₁, hm₁, H1⟩ := h1
  obtain ⟨m₂, hm₂, H2⟩ := h2
  refine ⟨min m₁ m₂, lt_min hm₁ hm₂, fun R => ?_⟩
  obtain ⟨c₁, hc₁, k₁, Hk1⟩ := H1 R
  obtain ⟨c₂, K, hc₂, k₂, Hk2⟩ := H2 R
  refine ⟨c₁ + c₂, K, by positivity, max k₁ k₂,
    fun k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hsep', hEF, hEG⟩ :=
    Hk2 k ((le_max_right _ _).trans hk) j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep
  have hae := Hk1 k ((le_max_left _ _).trans hk) j F G A₀ B₀ D mF mG bF bG dF dG eA
    (fun e he e' he' => (hsep e he e' he').trans
      (mul_le_mul_of_nonneg_left (timeDist_le_linkDist e e') (T.a_pos k).le))
  haveI := UV.ymProb T k j
  have hdec := abs_condDefect_le_of_ae (B k j).meas.comap_le (UV.Bdd1.of_measurable mF bF)
    (UV.Bdd1.of_measurable mG bG) hae
  have hE1 : Real.exp (-(m₁ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left m₁ m₂])
  have hE2 : Real.exp (-(m₂ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right m₁ m₂])
  have hx := Real.exp_pos (-(min m₁ m₂ * D))
  refine ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hsep', ?_, ?_, ?_⟩
  · refine hEF.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hEG.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hdec.trans ?_
    calc c₁ * Real.exp (-(m₁ * D)) ≤ c₁ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE1 hc₁
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le

/-- **`CondMass ∧ ObsQuasiLocT ⇒ ObsTransferPhysT`** (S). -/
theorem obsTransferPhysT_of_condMass {T : Tuning} {B : BlockingFamily T} (h1 : CondMass T B)
    (h2 : ObsQuasiLocT T B) : ObsTransferPhysT T B :=
  obsTransferPhysT_of_condMassDecay (condMassDecay_of_condMass h1) h2

end ProofPhase.V3
