/-
Proof phase, cycle 4, workstream 1 (c4a-condmass): the W₁ route in Lean (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c4a-condmass/NOTE.md`.
-/

import ProofPhase.V3.CondMass
import ProofPhase.Certified.AdjointW

/-!
# The W₁ blocked route: `LevelDprimeW`, `H1LocalLipW`, the certified window, and the torus decay

c3b's refit at `L√σ = 2.80` reaches the W₁ window, not the sup window, so the route must use the W₁ form of D′ at `L₁`.
c3c proved the W₁ form for the two-coupling family (`Certified.LimitDprimeW`, from the computer-assisted
`CertifiedAdjointW`) and described the W₁ blocked route on paper. This file puts it into Lean.

* `LevelDprimeW T B λ` (**named hypothesis, open; the W₁ analogue of `H1.LevelDprime`**): from some level on, in every
  volume, the blocked SU(2) Wilson law at `L₁` is the Gibbs measure of bounded coarse potentials whose single-link W₁
  influences (geodesic cost on SU(2)) have column sums `≤ γ` and range `≤ D₁`, with `γ e^{λ D₁} < 1`.
* `BlockGapUnifW` and `blockGapUnifW_of_levelDprimeW` (S, c3c's `decay_of_siteW` on each blocked law): block covariances
  of a bounded `f` and a Lipschitz `g` decay at rate `λ`, uniformly in the level and the volume.
* `H1LocalLipW T B Vk Vinf` (**named hypothesis, open; the Lean form of c3c's `H1LocalLip`**): the blocked laws are Gibbs
  measures of the coarse potentials `Vk`, and the single-link W₁ boundary derivatives of their conditional laws differ from
  those of the limit plaquette action `Vinf` by coefficients `δ_k` whose column sums tend to zero uniformly in the volume
  (with a common range `D₁`). This is "H1 in the C¹ (W₁) norm"; c3c §5 bounds `δ_k` by the sup and Lipschitz norms of
  `V_k − V_∞` on paper (`πη + (3π/2) G (e^{2ε} − 1)`).
* `levelDprimeW_of_h1LocalLip` (S, the W₁ openness lemma): `H1LocalLipW ∧ LimitDprimeW ⇒ ∃ λ > 0, LevelDprimeW`.
  `levelDprimeW_of_certified`: with the limit in c3c's certified window, `CertifiedAdjointW ∧ H1LocalLipW ⇒` the same.
* `ObsTransferPhysTW`, `ObsQuasiLocTW` (named hypotheses): the time-separated transfer and its quasi-locality part with
  the approximant `g` of the second observable **Lipschitz** (constant `≤ K`), as the W₁ decay theorem requires.
  `obsTransferPhysTW_of_condMass` (S): `CondMass ∧ ObsQuasiLocTW ⇒ ObsTransferPhysTW`.
* `torusDecayLoc_of_blockGapUnifW` (S), `LevelTorusRouteW`, `bothOrdersLoc_of_levelRouteW` (S): the W₁ route gives the
  gap for bounded physical extent in both orders of limits.

**Limitation (named).** `LevelDprimeW` and `H1LocalLipW` ask a finite range `D₁` of the W₁ coefficients, because the
library's W₁ Theorem A (`OneScale.BlockSpec.theoremA_W`, through c3c's `decay_of_siteW`) is the finite-range form; effective
actions have exponential tails. Removing it needs a weighted W₁ Theorem A (the W analogue of `Attempts.R3.theoremA_w`, a
line-by-line port); `D₁` can be taken as large as wanted.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift OneScale.CubeChain Positivity ProofPhase.Existence ProofPhase.RouteA ProofPhase.Torus
  ProofPhase.H1 ProofPhase.Certified

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.V3

/-! ## D′ in W₁ form along the levels -/

/-- **D′ in W₁ form along the levels (named hypothesis, open).** -/
def LevelDprimeW (T : Tuning) (B : BlockingFamily T) (lam : ℝ) : Prop :=
  ∃ γ D₁ : ℝ, 0 ≤ γ ∧ γ * Real.exp (lam * D₁) < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j, ∃ V : CoarsePot j,
    blockedLaw T B k j = Attempts.R3.gibbsMeasure (haarG SU2) V ∧ Attempts.R3.Potential (fun A => A) V ∧
    ∃ kk : LatticeLink 4 (coarseSide j) → LatticeLink 4 (coarseSide j) → ℝ,
      SiteInfluenceW (haarG SU2) (fun A => A) V geodSU2 kk ∧
      (∀ z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (LatticeLink 4 (coarseSide j)))), kk i z ≤ γ) ∧
      (∀ i z, z ∉ ({i} : Finset (LatticeLink 4 (coarseSide j))) → kk i z ≠ 0 → linkDist z i ≤ D₁)

/-- **The W₁ block gap, uniform in level and volume** (interface): bounded `f` against Lipschitz `g`. -/
def BlockGapUnifW (T : Tuning) (B : BlockingFamily T) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
    (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg R : ℝ),
    BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → LipBound geodSU2 g (fun _ => Lg) →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
        (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
      C * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R))

/-- **`LevelDprimeW` gives the W₁ block gap** (S: c3c's `decay_of_siteW` on each blocked law). -/
theorem blockGapUnifW_of_levelDprimeW {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : LevelDprimeW T B lam) : BlockGapUnifW T B lam := by
  obtain ⟨γ, D₁, hγ0, hρ, k₀, H⟩ := h
  refine ⟨Real.pi / (1 - γ * Real.exp (lam * D₁)), div_nonneg Real.pi_pos.le (by linarith), k₀,
    fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ?_⟩
  obtain ⟨V, hgibbs, hpot, kk, hk', hcol, hD₁⟩ := H k hk j
  have : Nonempty (LatticeLink 4 (coarseSide j)) := ⟨⟨fun _ => 0, 0⟩⟩
  rw [Effective.cov_map (T.ym k j) (B k j).meas hf hg]
  have e : (T.ym k j).map (B k j).B = Attempts.R3.gibbsMeasure (haarG SU2) V := hgibbs
  rw [e]
  exact decay_of_siteW (haarG SU2) hpot geodSU2_nonneg geodSU2_le_pi hk' hγ0 hcol linkDist linkDist_self
    linkDist_triangle hD₁ hlam hρ hf hg hfA hgS hvf hLg hvg hR

/-! ## `H1LocalLip` and the W₁ openness lemma -/

/-- **H1 in the W₁ (C¹) norm (named hypothesis, open).** The blocked laws are Gibbs measures of bounded coarse
potentials `Vk`; the single-link W₁ boundary derivatives of their conditional laws differ from those of the limit
plaquette action `Vinf` by coefficients `δ_k(i, z)` (range `≤ D₁`) whose column sums are `≤ ε_k → 0`, uniformly in the
volume. -/
def H1LocalLipW (T : Tuning) (B : BlockingFamily T) (Vk : ∀ j, ℕ → CoarsePot j)
    (Vinf : ∀ j, LatticePlaquette 4 (coarseSide j) → GaugeConnection SU2 4 (coarseSide j) → ℝ) : Prop :=
  (∀ k j, blockedLaw T B k j = Attempts.R3.gibbsMeasure (haarG SU2) (Vk j k)) ∧
  (∀ j k, Attempts.R3.Potential (fun A => A) (Vk j k)) ∧
  ∃ (D₁ : ℝ) (δ : ∀ k j : ℕ, LatticeLink 4 (coarseSide j) → LatticeLink 4 (coarseSide j) → ℝ) (ε : ℕ → ℝ),
    Tendsto ε atTop (𝓝 0) ∧
    (∀ k j (i z : LatticeLink 4 (coarseSide j)), z ∉ ({i} : Finset (LatticeLink 4 (coarseSide j))) →
      OneScale.Effective.InfluenceDevW geodSU2 {i}
        (Attempts.R3.siteSpec (haarG SU2) (plaqSupp (N := coarseSide j)) (Vinf j) i)
        (Attempts.R3.siteSpec (haarG SU2) (fun A => A) (Vk j k) i) z (δ k j i z)) ∧
    (∀ k j (z : LatticeLink 4 (coarseSide j)),
      ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (LatticeLink 4 (coarseSide j)))), δ k j i z ≤ ε k) ∧
    (∀ k j (i z : LatticeLink 4 (coarseSide j)), z ∉ ({i} : Finset (LatticeLink 4 (coarseSide j))) →
      δ k j i z ≠ 0 → linkDist z i ≤ D₁)

/-- **The W₁ openness lemma** (S): `H1LocalLipW ∧ LimitDprimeW ⇒ LevelDprimeW` at some rate `λ > 0`, with
`γ' = (1 + γ)/2` and range `max(1, D₁)`. -/
theorem levelDprimeW_of_h1LocalLip {T : Tuning} {B : BlockingFamily T} {Vk : ∀ j, ℕ → CoarsePot j}
    {Vinf : ∀ j, LatticePlaquette 4 (coarseSide j) → GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (h1 : H1LocalLipW T B Vk Vinf) (h2 : LimitDprimeW Vinf) : ∃ lam : ℝ, 0 < lam ∧ LevelDprimeW T B lam := by
  obtain ⟨hgibbs, hpot, D₁, δ, ε, hε, hdev, hcolδ, hrange⟩ := h1
  obtain ⟨γ, hγ0, hγ1, hlim⟩ := h2
  set γ' := (1 + γ) / 2
  have hγ'0 : 0 ≤ γ' := by positivity
  have hγ'1 : γ' < 1 := by simp only [γ']; linarith
  obtain ⟨lam₀, hlam₀, hρ₀⟩ := OneScale.SingleLink.exists_rate hγ'0 hγ'1
  set Dm := max 1 D₁
  have hDm : 0 < Dm := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨lam₀ / Dm, by positivity, γ', Dm, hγ'0, ?_, ?_⟩
  · rw [div_mul_cancel₀ lam₀ hDm.ne']; exact hρ₀
  · obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((tendsto_order.1 hε).2 ((1 - γ) / 2) (by linarith))
    refine ⟨k₀, fun k hk j => ?_⟩
    obtain ⟨kL, hkL, hcolL, hrangeL⟩ := hlim j
    refine ⟨Vk j k, hgibbs k j, hpot j k, fun i z => kL i z + δ k j i z, ?_, ?_, ?_⟩
    · intro i z hz
      exact (hkL i z hz).of_devW (hdev k j i z hz)
    · intro z
      rw [Finset.sum_add_distrib]
      have h1 := hcolL z
      have h2 := hcolδ k j z
      have h3 := hk₀ k hk
      simp only [γ']
      linarith
    · intro i z hz hne
      by_cases h0 : kL i z = 0
      · have hδ : δ k j i z ≠ 0 := by
          intro h; apply hne; show kL i z + δ k j i z = 0; rw [h0, h, add_zero]
        exact (hrange k j i z hz hδ).trans (le_max_right _ _)
      · exact (hrangeL i z h0).trans (le_max_left _ _)

/-- **With the limit in c3c's certified window** (the two-coupling action, `|β_A| ≤ cornerA c`, `|β_F| ≤ cornerF c`):
`CertifiedAdjointW ∧ H1LocalLipW ⇒ LevelDprimeW` at some rate `λ > 0`. -/
theorem levelDprimeW_of_certified {T : Tuning} {B : BlockingFamily T} (hcert : CertifiedAdjointW) (c : Fin 6)
    {βF βA : ℝ} (hA : |βA| ≤ cornerA c) (hF : |βF| ≤ cornerF c) {Vk : ∀ j, ℕ → CoarsePot j}
    (h1 : H1LocalLipW T B Vk (fun _ => twoCoupling βF βA)) : ∃ lam : ℝ, 0 < lam ∧ LevelDprimeW T B lam :=
  levelDprimeW_of_h1LocalLip h1 (limitDprimeW_twoCoupling hcert c hA hF)

/-! ## The time-separated transfer with a Lipschitz approximant -/

/-- **The time-separated transfer for the W₁ route (named hypothesis, open):** `ObsTransferPhysT` with the approximant
`g` of the second observable Lipschitz for the geodesic cost, constant `≤ K` per coarse link (`0 ≤ K`). -/
def ObsTransferPhysTW (T : Tuning) (B : BlockingFamily T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ), 0 ≤ D →
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e') →
    ∃ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink 4 (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ 4) ∧
      LipBound geodSU2 g (fun _ => K) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U - f ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U - g ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(T.ym k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U ∂(T.ym k j)|
        ≤ c * Real.exp (-(m * D))

/-- **Quasi-locality part of `ObsTransferPhysTW` (named hypothesis, open):** parts (a), (b) with a Lipschitz `g`. -/
def ObsQuasiLocTW (T : Tuning) (B : BlockingFamily T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ), 0 ≤ D →
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e') →
    ∃ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink 4 (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ 4) ∧
      LipBound geodSU2 g (fun _ => K) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U - f ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U - g ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D))

/-- **`CondMass` (decay form) and quasi-locality give the W₁ transfer** (S, as `obsTransferPhysT_of_condMassDecay`). -/
theorem obsTransferPhysTW_of_condMassDecay {T : Tuning} {B : BlockingFamily T} (h1 : CondMassDecay T B)
    (h2 : ObsQuasiLocTW T B) : ObsTransferPhysTW T B := by
  obtain ⟨m₁, hm₁, H1⟩ := h1
  obtain ⟨m₂, hm₂, H2⟩ := h2
  refine ⟨min m₁ m₂, lt_min hm₁ hm₂, fun R => ?_⟩
  obtain ⟨c₁, hc₁, k₁, Hk1⟩ := H1 R
  obtain ⟨c₂, K, hc₂, hK, k₂, Hk2⟩ := H2 R
  refine ⟨c₁ + c₂, K, by positivity, hK, max k₁ k₂,
    fun k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hlip, hsep', hEF, hEG⟩ :=
    Hk2 k ((le_max_right _ _).trans hk) j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep
  have hae := Hk1 k ((le_max_left _ _).trans hk) j F G A₀ B₀ D mF mG bF bG dF dG eA
    (fun e he e' he' => (hsep e he e' he').trans
      (mul_le_mul_of_nonneg_left (timeDist_le_linkDist e e') (T.a_pos k).le))
  have := UV.ymProb T k j
  have hdec := abs_condDefect_le_of_ae (B k j).meas.comap_le (UV.Bdd1.of_measurable mF bF)
    (UV.Bdd1.of_measurable mG bG) hae
  have hE1 : Real.exp (-(m₁ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left m₁ m₂])
  have hE2 : Real.exp (-(m₂ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right m₁ m₂])
  have hx := Real.exp_pos (-(min m₁ m₂ * D))
  refine ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hlip, hsep', ?_, ?_, ?_⟩
  · refine hEF.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hEG.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hdec.trans ?_
    calc c₁ * Real.exp (-(m₁ * D)) ≤ c₁ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE1 hc₁
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le

/-- **`CondMass ∧ ObsQuasiLocTW ⇒ ObsTransferPhysTW`** (S). -/
theorem obsTransferPhysTW_of_condMass {T : Tuning} {B : BlockingFamily T} (h1 : CondMass T B)
    (h2 : ObsQuasiLocTW T B) : ObsTransferPhysTW T B :=
  obsTransferPhysTW_of_condMassDecay (condMassDecay_of_condMass h1) h2

/-! ## Torus decay through the W₁ block gap -/

/-- **The one-level estimate with a W₁ block gap** (as `RouteA.wcorr_le_blocked`, with `g` Lipschitz). -/
theorem wcorr_le_blockedW (T : Tuning) (B : BlockingFamily T) {k j : ℕ} {s : ℝ} {V : ℕ → ℕ} (O : SlabObs T s V)
    (n : ℕ) {C lam ε Kv Lg : ℝ}
    (hgap : ∀ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
      (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg' R : ℝ),
      BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg' → LipBound geodSU2 g (fun _ => Lg') →
      (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
      |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
          (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
        C * (∑ a ∈ A, vf a) * Lg' * Real.exp (-(lam * R)))
    (hC : 0 ≤ C)
    (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j)))
    (mf : Measurable f) (mg : Measurable g) (bf : ∀ V, |f V| ≤ 1) (bg : ∀ V, |g V| ≤ 1)
    (dfA : DepOn f A') (dgB : DepOn g B') (vf : LatticeLink 4 (coarseSide j) → ℝ) (hvf : OscBound f vf)
    (hsumv : ∑ a ∈ A', vf a ≤ Kv) (hLg : 0 ≤ Lg) (hlip : LipBound geodSU2 g (fun _ => Lg))
    (hsep : ∀ x ∈ A', ∀ y ∈ B', (n * T.a k) / 2 ≤ T.L₁ * linkDist x y)
    (hEF : ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j)
        (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) U - f ((B k j).B U)| ∂(T.ym k j) ≤ ε)
    (hEG : ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j)
        (fun U => O.F k j (thetaConn U)) U - g ((B k j).B U)| ∂(T.ym k j) ≤ ε)
    (hdec : |∫ U, O.F k j (tShift (n : ZMod (T.side k j)) U) * O.F k j (thetaConn U) ∂(T.ym k j) -
        ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j)
            (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) U *
          condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) (fun U => O.F k j (thetaConn U)) U
            ∂(T.ym k j)| ≤ ε) :
    |T.wcorr k j (O.F k j) n| ≤ C * Kv * Lg * Real.exp (-(lam * ((n * T.a k) / (2 * T.L₁)))) + 5 * ε := by
  have := isProbabilityMeasure_gaugeMeasure (d := 4) (N := T.side k j) (G := SU2) (n := 2) continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (posWeight_wilson 2 (T.β k))
  have hFm := O.meas k j
  have hF1 := O.bdd k j
  have htr := cov_transfer (T.ym k j) (B k j).meas (hFm.comp (measurable_tShift _))
    (hFm.comp measurePreserving_thetaConn.measurable) (fun U => hF1 _) (fun U => hF1 _) mf mg bf bg hEF hEG hdec
  have hL1 := T.L₁_pos
  have hR : ∀ x ∈ A', ∀ y ∈ B', (n * T.a k) / (2 * T.L₁) ≤ linkDist x y := by
    intro x hx y hy
    rw [div_le_iff₀ (by positivity)]
    have := hsep x hx y hy
    nlinarith
  have hblk := hgap f g A' B' vf Lg _ ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩ dfA dgB hvf hLg hlip hR
  have hblk' : |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
      (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
      C * Kv * Lg * Real.exp (-(lam * ((n * T.a k) / (2 * T.L₁)))) :=
    hblk.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsumv hC) hLg)
      (Real.exp_pos _).le)
  unfold Tuning.wcorr corr
  exact htr.trans (by linarith)

/-- **Torus decay from the W₁ block gap and the W₁ time-separated transfer** (S). -/
theorem torusDecayLoc_of_blockGapUnifW {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    (hB : BlockGapUnifW T B lam) (h3 : ObsTransferPhysTW T B) : TorusDecayLoc T.toV := by
  obtain ⟨C, hC, k₀, hgap⟩ := hB
  obtain ⟨m, hm, htrP⟩ := h3
  have hL1 := T.L₁_pos
  set a := lam / 4
  have ha : 0 < a := by positivity
  set m' := min (lam / (4 * T.L₁)) m
  have hm' : 0 < m' := lt_min (by positivity) hm
  refine ⟨m', hm', fun s R => ?_⟩
  obtain ⟨c, K, hc, hK, k₁, htr⟩ := htrP (R + T.L₁)
  refine ⟨max k₀ k₁, C * (2 * K) * K * (24 / a ^ 4 * Real.exp a) + 5 * c, by positivity,
    fun k hk Vb j O hO n hn => ?_⟩
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hk₁ : k₁ ≤ k := (le_max_right _ _).trans hk
  obtain ⟨hdA, hdB, -, -, -⟩ := slab_transfer_data T O hn
  have hsepT := slab_time_sep T O hn
  have hak := T.a_pos k
  have haL : T.a k ≤ T.L₁ := div_le_self hL1.le (by exact_mod_cast T.ℓ_pos k)
  have eA : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j))))
      (R + T.L₁) := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    rw [linkDist_shiftLink]
    have : T.a k * linkDist l l' ≤ R := hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
    linarith
  have eB : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image mirrorLink) (R + T.L₁) := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    have h1 : T.a k * linkDist l l' ≤ R := hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
    have h2 := mul_le_mul_of_nonneg_left (linkDist_mirrorLink_le l l') hak.le
    nlinarith
  set D := (n : ℝ) * T.a k
  have hD : 0 ≤ D := by positivity
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, ⟨vf, hvf, hsv⟩, hlip, hsep', hEF, hEG, hdec⟩ :=
    htr k hk₁ j _ _ _ _ D hD ((O.meas k j).comp (measurable_tShift _))
      ((O.meas k j).comp measurePreserving_thetaConn.measurable) (fun U => O.bdd k j _) (fun U => O.bdd k j _)
      (gaugeInvariant_tShift (O.gauge k j) _) (gaugeInvariant_thetaConn (O.gauge k j)) hdA hdB eA eB hsepT
  have hx : 0 ≤ D / T.L₁ := by positivity
  have hsv' : ∑ a ∈ A', vf a ≤ 2 * (K * (1 + D / T.L₁) ^ 4) := by linarith
  have hmain := wcorr_le_blockedW T B O n (hgap k hk₀ j) hC f g A' B' mf mg bf bg dfA dgB vf hvf hsv' hK hlip
    hsep' hEF hEG hdec
  have hpoly := poly_exp_le ha hx
  have e1 : lam * (D / (2 * T.L₁)) = 2 * a * (D / T.L₁) := by simp only [a]; field_simp; ring
  have e2 : a * (D / T.L₁) = lam / (4 * T.L₁) * D := by simp only [a]; field_simp
  have hE1 : Real.exp (-(lam / (4 * T.L₁) * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (lam / (4 * T.L₁)) m])
  have hE2 : Real.exp (-(m * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (lam / (4 * T.L₁)) m])
  have hCK : 0 ≤ C * (2 * K) * K := by positivity
  show |T.wcorr k j (O.F k j) n| ≤ _
  calc |T.wcorr k j (O.F k j) n|
      ≤ C * (2 * (K * (1 + D / T.L₁) ^ 4)) * K * Real.exp (-(lam * (D / (2 * T.L₁)))) +
          5 * (c * Real.exp (-(m * D))) := hmain
    _ = C * (2 * K) * K * ((1 + D / T.L₁) ^ 4 * Real.exp (-(2 * a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m * D)) := by rw [e1]; ring
    _ ≤ C * (2 * K) * K * (24 / a ^ 4 * Real.exp a * Real.exp (-(a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m' * D)) := by
        gcongr
    _ = C * (2 * K) * K * (24 / a ^ 4 * Real.exp a) * Real.exp (-(lam / (4 * T.L₁) * D)) +
          5 * c * Real.exp (-(m' * D)) := by rw [e2]; ring
    _ ≤ C * (2 * K) * K * (24 / a ^ 4 * Real.exp a) * Real.exp (-(m' * D)) +
          5 * c * Real.exp (-(m' * D)) := by gcongr
    _ = (C * (2 * K) * K * (24 / a ^ 4 * Real.exp a) + 5 * c) * Real.exp (-(m' * (n * T.a k))) := by
        ring

/-- **The torus route in W₁ form** (open inputs): a blocking family, `λ > 0`, `LevelDprimeW`, `ObsTransferPhysTW`. -/
def LevelTorusRouteW (T : Tuning) : Prop :=
  ∃ (B : BlockingFamily T) (lam : ℝ), 0 < lam ∧ LevelDprimeW T B lam ∧ ObsTransferPhysTW T B

/-- **The W₁ route gives the gap in both orders of limits** (S). -/
theorem bothOrdersLoc_of_levelRouteW {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : LevelTorusRouteW T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV := by
  obtain ⟨B, lam, hlam, hD, h3⟩ := h
  have hT := torusDecayLoc_of_blockGapUnifW B hlam (blockGapUnifW_of_levelDprimeW B hlam.le hD) h3
  exact ⟨hT, bothOrdersLoc_of_torusDecayLoc ha hT⟩

end ProofPhase.V3
