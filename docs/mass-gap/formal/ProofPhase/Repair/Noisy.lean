/-
Proof phase, cycle 5, workstream 3 (c5c-repair): noisy local blockings, reflection positivity, and the Gibbs
representation of their blocked laws (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5c-repair/NOTE.md`, section 3.
-/

import ProofPhase.RouteA.Blocking
import ProofPhase.Repair.GeneralSupport

/-!
# Noisy blockings: reflection positivity and densities

The review `c4-fable/REVIEW.md` §1.3: every D′ input asks that the blocked law be the Gibbs measure of a bounded
potential with respect to Haar measure. For the deterministic good blocking (project a smeared sum to SU(2)) nobody knows
that the image law has a density bounded above and below. A **noisy** blocking (each coarse link = smeared value times an
independent noise of bounded density) removes the problem: the blocked law then has a density between the noise bounds.

**The structure.** The randomness of the block variable is carried by auxiliary noise variables
`η = (c, a, a') ∈ Y₀ × Y₊ × Y₊` with law `ν₀ ⊗ ν₊ ⊗ ν₊`: `c` for the coarse links fixed by the reflection, `a` for the
positive ones, `a'` for the negative ones (indexed by their mirror images). `NoisyRPBlocking` asks that the block map
`B : (fine field, noise) → coarse field` be jointly measurable, commute with the reflection when `a` and `a'` are
swapped, and that a coarse observable of the closed positive half read only the closed positive fine half, `c` and `a`.
A deterministic `RPBlocking` is the case of trivial noise (`RPBlocking.toNoisy`, same blocked law: `blockedLaw_toNoisy`).

* **`noisy_blocked_wilson_rp`** (S): reflection positivity of every noisy blocked layer, in the form of
  `blocked_wilson_rp` with the noise integrated: `∫ dη ∫ F(B(U, η)) F(Θ B(U, η)) e^{−S_W(U)} dHaar(U) ≥ 0`. Proof:
  integrate out `a` and `a'` first (`integral_prod_mul`), which leaves `∫ H_c(U) H_c(ΘU) e^{−S_W} ≥ 0` for every `c`
  (`wilson_rp`).
* `NoisyBlockingFamily`, `noisyBlockedLaw`, `noisyFamily_rp` (S): the family version (the proposed generalisation of
  `BlockingFamily`, NOTE §3.3).
* **`gibbs_of_density`** (S): a probability law with a density (w.r.t. product Haar) between `m > 0` and `M` is the
  Gibbs measure of a bounded `Potential (fun A => A)` (one global term `log ρ`). So the Gibbs clause of every D′ input
  is satisfiable whenever the blocked law has such a density.
* **`map_prod_eq_withDensity`** (S): if for every fine field the noise pushes forward to a law with density
  `κ(U, ·) ∈ [m, M]`, then the blocked law has the density `ρ = ∫ κ(U, ·) dμ(U) ∈ [m, M]`.
* **`noisy_blockedLaw_gibbs`** (S): together: a noisy blocking whose kernel has a density in `[m, M]` (`KernelDensity`)
  has, at every level and in every volume, a blocked law that is the Gibbs measure of a bounded coarse potential.

**Claim level.** All proved (no `sorry`, no new axiom). The **concrete** multiplicative noisy blocking (smeared value
times independent heat-kernel noise per coarse link) is described with its exact formulas in NOTE §3.2; that it satisfies
the three structure fields and `KernelDensity` is shown there on paper (Haar invariance, class-function noise), not in
Lean. The Dobrushin content (the columns) is untouched by this file: a single global term gives the right conditional
laws but no locality; locality of the blocked potential is the content of `LevelDprimeWw` / `CloseWw`.
-/

open MeasureTheory Finset AreaLaw.Concrete Positivity OneScale

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Repair

/-! ## 1. Noisy reflection-respecting blockings and reflection positivity -/

section Noisy

/-- **A noisy reflection-respecting blocking** from `(ℤ/Nℤ)^d` to `(ℤ/Mℤ)^d` with noise `(c, a, a') ∈ Y₀ × Y₊ × Y₊`
(`c`: the coarse links fixed by the reflection; `a`, `a'`: the positive links and the mirrors of the positive links). -/
structure NoisyRPBlocking (G : Type*) [Group G] [MeasurableSpace G] (d N M : ℕ) [NeZero d] [NeZero N] [NeZero M]
    (Y0 Yp : Type*) [MeasurableSpace Y0] [MeasurableSpace Yp] where
  B : GaugeConnection G d N → Y0 × Yp × Yp → GaugeConnection G d M
  meas : Measurable (fun q : GaugeConnection G d N × (Y0 × Yp × Yp) => B q.1 q.2)
  theta : ∀ U c a a', B (thetaConn U) (c, a', a) = thetaConn (B U (c, a, a'))
  half : ∀ F : GaugeConnection G d M → ℝ, LinkDep F (posHalfLinks d M) →
    ∀ U U' c a a₁ a₂, (∀ l ∈ posHalfLinks d N, U l = U' l) → F (B U (c, a, a₁)) = F (B U' (c, a, a₂))

variable {G : Type*} [Group G] [MeasurableSpace G] {d N M : ℕ} [NeZero d] [NeZero N] [NeZero M]
  {Y0 Yp : Type*} [MeasurableSpace Y0] [MeasurableSpace Yp]

theorem NoisyRPBlocking.measurable_comp (P : NoisyRPBlocking G d N M Y0 Yp) {α : Type*} [MeasurableSpace α]
    {u : α → GaugeConnection G d N} {η : α → Y0 × Yp × Yp} (hu : Measurable u) (hη : Measurable η) :
    Measurable (fun x => P.B (u x) (η x)) :=
  P.meas.comp (hu.prodMk hη)

/-- **A deterministic blocking is a noisy one with trivial noise.** -/
def _root_.ProofPhase.RPBlocking.toNoisy (P : RPBlocking G d N M) : NoisyRPBlocking G d N M Unit Unit where
  B U _ := P.B U
  meas := P.meas.comp measurable_fst
  theta U _ _ _ := P.theta U
  half F hF U U' _ _ _ _ h := P.half F hF U U' h

end Noisy

section RP

variable {d M N : ℕ} [NeZero d] [NeZero M] [NeZero N]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n] [HasHaarProbability G] [(haarG G).IsInvInvariant]
  {Y0 Yp : Type*} [MeasurableSpace Y0] [MeasurableSpace Yp]

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

include hc hU in
/-- **Reflection positivity of a noisy blocked layer, for each fixed `c`** (the plane noise), with `a, a'`
integrated: `∫_{(a, a')} ∫_U F(B(U, c, a, a')) F(Θ B(U, c, a, a')) e^{−S_W(U)} ≥ 0`. -/
theorem noisy_rp_fixed (hN : Even N) (P : NoisyRPBlocking G d N M Y0 Yp) (νp : Measure Yp)
    [IsProbabilityMeasure νp] (β : ℝ) {F : GaugeConnection G d M → ℝ} (hF : LinkDep F (posHalfLinks d M))
    (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) (c : Y0) :
    0 ≤ ∫ q : Yp × Yp, ∫ U, F (P.B U (c, q.1, q.2)) * F (thetaConn (P.B U (c, q.1, q.2))) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N) ∂(νp.prod νp) := by
  obtain ⟨C, hC⟩ := bF
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (fun _ => 1))
  set W : GaugeConnection G d N → ℝ := fun U => ∏ p ∈ (univ : Finset (LatticePlaquette d N)),
    Real.exp (β * xp n p U) with hWdef
  have mW : Measurable W := measurable_wilsonWeight hc β _
  obtain ⟨Wb, hWb⟩ := isBdd_wilsonWeight hU β (univ : Finset (LatticePlaquette d N))
  set Gf : Yp → GaugeConnection G d N → ℝ := fun a U => F (P.B U (c, a, a)) with hGf
  have e1 : ∀ U a a', F (P.B U (c, a, a')) = Gf a U := fun U a a' =>
    P.half F hF U U c a a' a (fun _ _ => rfl)
  have e2 : ∀ U a a', F (thetaConn (P.B U (c, a, a'))) = Gf a' (thetaConn U) := by
    intro U a a'
    rw [← P.theta]; exact e1 _ _ _
  have mGf : Measurable (fun r : Yp × GaugeConnection G d N => Gf r.1 r.2) :=
    mF.comp (P.measurable_comp measurable_snd (measurable_const.prodMk (measurable_fst.prodMk measurable_fst)))
  -- the positive-half function `H(U) = ∫ Gf(a, U) dν₊(a)`
  set H : GaugeConnection G d N → ℝ := fun U => ∫ a, Gf a U ∂νp with hHdef
  have mH : Measurable H := by
    have : StronglyMeasurable (fun r : GaugeConnection G d N × Yp => Gf r.2 r.1) :=
      (mGf.comp measurable_swap).stronglyMeasurable
    exact this.integral_prod_right'.measurable
  have hHdep : LinkDep H (posHalfLinks d N) := by
    intro U U' h
    show (∫ a, Gf a U ∂νp) = ∫ a, Gf a U' ∂νp
    congr 1
    funext a
    exact P.half F hF U U' c a a a h
  have hHbdd : ∃ C', ∀ U, |H U| ≤ C' := by
    refine ⟨C, fun U => ?_⟩
    have := norm_integral_le_of_norm_le_const (μ := νp) (f := fun a => Gf a U) (C := C)
      (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hC _)
    simpa [Real.norm_eq_abs] using this
  -- rewrite the integrand
  have hrw : ∀ q : Yp × Yp, ∀ U, F (P.B U (c, q.1, q.2)) * F (thetaConn (P.B U (c, q.1, q.2))) * W U =
      Gf q.1 U * Gf q.2 (thetaConn U) * W U := fun q U => by rw [e1, e2]
  show 0 ≤ ∫ q : Yp × Yp, ∫ U, F (P.B U (c, q.1, q.2)) * F (thetaConn (P.B U (c, q.1, q.2))) * W U
    ∂(productHaar G d N) ∂(νp.prod νp)
  simp_rw [hrw]
  -- swap the noise and the field integrals
  have mΦ : Measurable (fun r : (Yp × Yp) × GaugeConnection G d N =>
      Gf r.1.1 r.2 * Gf r.1.2 (thetaConn r.2) * W r.2) :=
    ((mGf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (mGf.comp ((measurable_snd.comp measurable_fst).prodMk (measurable_thetaConn.comp measurable_snd)))).mul
      (mW.comp measurable_snd)
  have hint : Integrable (Function.uncurry fun (q : Yp × Yp) (U : GaugeConnection G d N) =>
      Gf q.1 U * Gf q.2 (thetaConn U) * W U) ((νp.prod νp).prod (productHaar G d N)) := by
    refine Integrable.of_bound mΦ.aestronglyMeasurable (C * C * Wb) (Filter.Eventually.of_forall fun r => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    have h1 := hC (P.B r.2 (c, r.1.1, r.1.1))
    have h2 := hC (P.B (thetaConn r.2) (c, r.1.2, r.1.2))
    have h3 : |W r.2| ≤ Wb := by have := hWb r.2; rwa [Real.norm_eq_abs] at this
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hC0) h3 (abs_nonneg _) (mul_nonneg hC0 hC0)
  rw [integral_integral_swap hint]
  have hq : ∀ U, ∫ q : Yp × Yp, Gf q.1 U * Gf q.2 (thetaConn U) * W U ∂(νp.prod νp) =
      H U * H (thetaConn U) * W U := by
    intro U
    rw [integral_mul_const]
    congr 1
    exact integral_prod_mul (fun a => Gf a U) (fun a => Gf a (thetaConn U))
  simp_rw [hq]
  exact wilson_rp hN hc hU β hHdep mH hHbdd

include hc hU in
/-- **Reflection positivity of every noisy blocked layer** (S; generalises `blocked_wilson_rp`): for every bounded
measurable coarse observable `F` of the closed coarse positive half,
`∫ dν₀(c) ∫ d(ν₊ ⊗ ν₊)(a, a') ∫ F(B(U, c, a, a')) F(Θ B(U, c, a, a')) e^{−S_W(U)} dHaar(U) ≥ 0`. -/
theorem noisy_blocked_wilson_rp (hN : Even N) (P : NoisyRPBlocking G d N M Y0 Yp) (ν0 : Measure Y0) (νp : Measure Yp)
    [IsProbabilityMeasure νp] (β : ℝ) {F : GaugeConnection G d M → ℝ} (hF : LinkDep F (posHalfLinks d M))
    (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) :
    0 ≤ ∫ c, ∫ q : Yp × Yp, ∫ U, F (P.B U (c, q.1, q.2)) * F (thetaConn (P.B U (c, q.1, q.2))) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
          ∂(productHaar G d N) ∂(νp.prod νp) ∂ν0 :=
  integral_nonneg fun c => noisy_rp_fixed hc hU hN P νp β hF mF bF c

include hc hU in
/-- **The deterministic case is recovered** (S): with trivial noise, `noisy_blocked_wilson_rp` is
`blocked_wilson_rp`. -/
theorem blocked_wilson_rp_of_noisy (hN : Even N) (P : RPBlocking G d N M) (β : ℝ) {F : GaugeConnection G d M → ℝ}
    (hF : LinkDep F (posHalfLinks d M)) (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) :
    0 ≤ ∫ U, F (P.B U) * F (thetaConn (P.B U)) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N) := by
  have h := noisy_rp_fixed hc hU hN P.toNoisy (Measure.dirac ()) β hF mF bF ()
  simpa [RPBlocking.toNoisy] using h

end RP

/-! ## 2. Densities and the Gibbs representation -/

section Density

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν]

/-- **A law with a density in `[m, M]`, `m > 0`, is the Gibbs measure of a bounded potential** (one global term
`log ρ` on the set of all coordinates; the other terms vanish). -/
theorem gibbs_of_density (μ : Measure (ι → S)) [IsProbabilityMeasure μ] {ρ : (ι → S) → ℝ} (hρm : Measurable ρ)
    {m Mx : ℝ} (hm : 0 < m) (hlo : ∀ σ, m ≤ ρ σ) (hhi : ∀ σ, ρ σ ≤ Mx)
    (hμ : μ = (prodMeasure ν).withDensity (fun σ => ENNReal.ofReal (ρ σ))) :
    ∃ V : Finset ι → (ι → S) → ℝ, Attempts.R3.Potential (fun A => A) V ∧ μ = Attempts.R3.gibbsMeasure ν V := by
  have hρpos : ∀ σ, 0 < ρ σ := fun σ => hm.trans_le (hlo σ)
  set V : Finset ι → (ι → S) → ℝ := fun A σ => if A = univ then Real.log (ρ σ) else 0 with hV
  have htot : ∀ σ, Attempts.R3.totalLog V σ = Real.log (ρ σ) := by
    intro σ
    unfold Attempts.R3.totalLog
    simp [hV]
  have hint : Integrable ρ (prodMeasure ν) :=
    Integrable.of_bound hρm.aestronglyMeasurable Mx (Filter.Eventually.of_forall fun σ => by
      rw [Real.norm_eq_abs, abs_of_pos (hρpos σ)]; exact hhi σ)
  have hZ : ∫ τ, ρ τ ∂(prodMeasure ν) = 1 := by
    have h1 : μ Set.univ = 1 := measure_univ
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun σ => (hρpos σ).le)] at h1
    have h0 : 0 ≤ ∫ τ, ρ τ ∂(prodMeasure ν) := integral_nonneg fun σ => (hρpos σ).le
    have := (ENNReal.ofReal_eq_one).1 h1
    exact this
  refine ⟨V, ⟨fun A => ?_, ⟨max |Real.log m| |Real.log Mx|, fun A σ => ?_⟩, fun A σ σ' h => ?_⟩, ?_⟩
  · by_cases hA : A = univ
    · simp only [hV, hA, ite_true]; exact hρm.log
    · simp only [hV, hA, ite_false]; exact measurable_const
  · by_cases hA : A = univ
    · simp only [hV, hA, ite_true]
      exact abs_le_max_abs_abs (Real.log_le_log hm (hlo σ)) (Real.log_le_log (hρpos σ) (hhi σ))
    · simp only [hV, hA, ite_false, abs_zero]; exact (abs_nonneg _).trans (le_max_left _ _)
  · by_cases hA : A = univ
    · simp only [hV, hA, ite_true]
      have : σ = σ' := funext fun i => h i (by rw [hA]; exact mem_univ i)
      rw [this]
    · simp only [hV, hA, ite_false]
  · have hg : Attempts.R3.gibbsMeasure ν V = weightMeasure ν ρ := by
      unfold Attempts.R3.gibbsMeasure
      congr 1
      funext τ
      rw [htot, Real.exp_log (hρpos τ)]
    rw [hg, hμ]
    unfold weightMeasure
    rw [hZ]
    simp only [div_one]

/-- **A noise kernel with a density gives the blocked law a density.** If `μ` is a probability law of the fine field,
`ν` that of the noise, and for every fine field `x` the noise pushes forward under `Φ(x, ·)` to the law with density
`κ(x, ·)` (jointly measurable, in `[m, M]`), then `(μ ⊗ ν) ∘ Φ⁻¹` has the density `∫ κ(x, ·) dμ(x)`. -/
theorem map_prod_eq_withDensity {X E : Type*} [MeasurableSpace X] [MeasurableSpace E] (μ : Measure X)
    [IsProbabilityMeasure μ] (η : Measure E) [IsProbabilityMeasure η] {Φ : X × E → (ι → S)} (hΦ : Measurable Φ)
    {κ : X → (ι → S) → ℝ} (hκ : Measurable (Function.uncurry κ)) {m Mx : ℝ} (hlo : ∀ x σ, m ≤ κ x σ)
    (hm : 0 ≤ m) (hhi : ∀ x σ, κ x σ ≤ Mx)
    (hker : ∀ x, η.map (fun e => Φ (x, e)) = (prodMeasure ν).withDensity (fun σ => ENNReal.ofReal (κ x σ))) :
    (μ.prod η).map Φ = (prodMeasure ν).withDensity (fun σ => ENNReal.ofReal (∫ x, κ x σ ∂μ)) := by
  have hκ0 : ∀ x σ, 0 ≤ κ x σ := fun x σ => hm.trans (hlo x σ)
  have mκ : ∀ σ, Measurable (fun x => κ x σ) := fun σ => hκ.comp (measurable_id.prodMk measurable_const)
  have hκint : ∀ σ, Integrable (fun x => κ x σ) μ := fun σ =>
    Integrable.of_bound (mκ σ).aestronglyMeasurable Mx
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hκ0 x σ)]; exact hhi x σ)
  ext s hs
  rw [Measure.map_apply hΦ hs, Measure.prod_apply (hΦ hs)]
  have hsec : ∀ x, η (Prod.mk x ⁻¹' (Φ ⁻¹' s)) = ∫⁻ σ in s, ENNReal.ofReal (κ x σ) ∂(prodMeasure ν) := by
    intro x
    have mx : Measurable (fun e => Φ (x, e)) := hΦ.comp (measurable_const.prodMk measurable_id)
    rw [← withDensity_apply _ hs, ← hker x, Measure.map_apply mx hs]
    rfl
  simp_rw [hsec]
  rw [withDensity_apply _ hs]
  rw [lintegral_lintegral_swap hκ.ennreal_ofReal.aemeasurable]
  refine lintegral_congr fun σ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hκint σ) (Filter.Eventually.of_forall fun x => hκ0 x σ)]

end Density

/-! ## 3. The noisy blocking family -/

open ProofPhase.V3

/-- **Noisy blocking family** (proposed generalisation of `BlockingFamily`, NOTE §3.3): at every level and volume, a
noisy reflection-respecting blocking of the fine torus onto the coarse one, with noise laws `ν₀`, `ν₊`. -/
structure NoisyBlockingFamily (T : Tuning) (Y0 Yp : ℕ → Type) [∀ j, MeasurableSpace (Y0 j)]
    [∀ j, MeasurableSpace (Yp j)] where
  blk : ∀ k j, NoisyRPBlocking SU2 4 (T.side k j) (coarseSide j) (Y0 j) (Yp j)
  ν0 : ∀ k j : ℕ, Measure (Y0 j)
  νp : ∀ k j : ℕ, Measure (Yp j)
  prob0 : ∀ k j : ℕ, IsProbabilityMeasure (ν0 k j)
  probp : ∀ k j : ℕ, IsProbabilityMeasure (νp k j)

variable {Y0 Yp : ℕ → Type} [∀ j, MeasurableSpace (Y0 j)] [∀ j, MeasurableSpace (Yp j)]

/-- The noise law `ν₀ ⊗ ν₊ ⊗ ν₊`. -/
def NoisyBlockingFamily.noise {T : Tuning} (NB : NoisyBlockingFamily T Y0 Yp) (k j : ℕ) : Measure (Y0 j × Yp j × Yp j) :=
  (NB.ν0 k j).prod ((NB.νp k j).prod (NB.νp k j))

/-- The joint law of the fine field and the noise. -/
def NoisyBlockingFamily.joint {T : Tuning} (NB : NoisyBlockingFamily T Y0 Yp) (k j : ℕ) :
    Measure (GaugeConnection SU2 4 (T.side k j) × (Y0 j × Yp j × Yp j)) :=
  (T.ym k j).prod (NB.noise k j)

/-- **The noisy blocked law**: the image of the joint law under the block map. -/
def noisyBlockedLaw {T : Tuning} (NB : NoisyBlockingFamily T Y0 Yp) (k j : ℕ) :
    Measure (GaugeConnection SU2 4 (coarseSide j)) :=
  (NB.joint k j).map (fun q => (NB.blk k j).B q.1 q.2)

/-- **Every layer of a noisy blocking family is reflection positive** (S). -/
theorem noisyFamily_rp {T : Tuning} (NB : NoisyBlockingFamily T Y0 Yp) (k j : ℕ)
    {F : GaugeConnection SU2 4 (coarseSide j) → ℝ} (hF : LinkDep F (posHalfLinks 4 (coarseSide j)))
    (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) :
    0 ≤ ∫ c, ∫ q : Yp j × Yp j, ∫ U, F ((NB.blk k j).B U (c, q.1, q.2)) *
        F (thetaConn ((NB.blk k j).B U (c, q.1, q.2))) *
        ∏ p ∈ (univ : Finset (LatticePlaquette 4 (T.side k j))), Real.exp (T.β k * xp 2 p U)
          ∂(productHaar SU2 4 (T.side k j)) ∂((NB.νp k j).prod (NB.νp k j)) ∂(NB.ν0 k j) := by
  haveI := NB.probp k j
  exact noisy_blocked_wilson_rp continuous_subtype_val (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
    (T.even_side k j) (NB.blk k j) (NB.ν0 k j) (NB.νp k j) (T.β k) hF mF bF

/-- **Kernel density** (the property a concrete noisy blocking must have): for every fine field `U`, the block variable
`B(U, η)` has, under the noise, a law with a density `κ(U, ·)` w.r.t. product Haar, jointly measurable, between `m > 0`
and `M` (uniform in `U`; the constants may depend on the level and the volume). -/
def KernelDensity {T : Tuning} (NB : NoisyBlockingFamily T Y0 Yp) (k j : ℕ) : Prop :=
  ∃ (κ : GaugeConnection SU2 4 (T.side k j) → GaugeConnection SU2 4 (coarseSide j) → ℝ) (m Mx : ℝ),
    Measurable (Function.uncurry κ) ∧ 0 < m ∧ (∀ U φ, m ≤ κ U φ) ∧ (∀ U φ, κ U φ ≤ Mx) ∧
    ∀ U, (NB.noise k j).map (fun η => (NB.blk k j).B U η) =
      (productHaar SU2 4 (coarseSide j)).withDensity (fun φ => ENNReal.ofReal (κ U φ))

/-- **The Gibbs representation for noisy blockings** (S): with a kernel density, the noisy blocked law is the Gibbs
measure of a bounded coarse potential (review §1.3 removed). -/
theorem noisy_blockedLaw_gibbs {T : Tuning} (NB : NoisyBlockingFamily T Y0 Yp) (k j : ℕ) (hK : KernelDensity NB k j) :
    ∃ V : CoarsePot j, Attempts.R3.Potential (fun A => A) V ∧
      noisyBlockedLaw NB k j = Attempts.R3.gibbsMeasure (haarG SU2) V := by
  obtain ⟨κ, m, Mx, hκ, hm, hlo, hhi, hker⟩ := hK
  haveI := NB.probp k j
  haveI := NB.prob0 k j
  haveI := ProofPhase.UV.ymProb T k j
  haveI : IsProbabilityMeasure (NB.noise k j) := by unfold NoisyBlockingFamily.noise; infer_instance
  have hdens := map_prod_eq_withDensity (ι := LatticeLink 4 (coarseSide j)) (haarG SU2) (T.ym k j) (NB.noise k j)
    ((NB.blk k j).meas) hκ hlo hm.le hhi hker
  have hρm : Measurable (fun φ => ∫ U, κ U φ ∂(T.ym k j)) :=
    (hκ.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable
  have mκ : ∀ φ, Measurable (fun U => κ U φ) := fun φ => hκ.comp (measurable_id.prodMk measurable_const)
  have hκi : ∀ φ, Integrable (fun U => κ U φ) (T.ym k j) := fun φ =>
    Integrable.of_bound (mκ φ).aestronglyMeasurable Mx (Filter.Eventually.of_forall fun U => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hm.le.trans (hlo U φ))]; exact hhi U φ)
  have hlo' : ∀ φ, m ≤ ∫ U, κ U φ ∂(T.ym k j) := fun φ => by
    have := integral_mono (integrable_const m) (hκi φ) (fun U => hlo U φ)
    simpa using this
  have hhi' : ∀ φ, ∫ U, κ U φ ∂(T.ym k j) ≤ Mx := fun φ => by
    have := integral_mono (hκi φ) (integrable_const Mx) (fun U => hhi U φ)
    simpa using this
  haveI : IsProbabilityMeasure (NB.joint k j) := by unfold NoisyBlockingFamily.joint; infer_instance
  haveI : IsProbabilityMeasure (noisyBlockedLaw NB k j) := by
    unfold noisyBlockedLaw
    infer_instance
  exact gibbs_of_density (haarG SU2) (noisyBlockedLaw NB k j) hρm hm hlo' hhi' hdens

/-- **The deterministic family embeds** (S): a `BlockingFamily` is a noisy one with trivial noise, and its noisy
blocked law is the old blocked law. -/
def BlockingFamily.toNoisy {T : Tuning} (B : BlockingFamily T) :
    NoisyBlockingFamily T (fun _ => Unit) (fun _ => Unit) where
  blk k j := (B k j).toNoisy
  ν0 _ _ := Measure.dirac ()
  νp _ _ := Measure.dirac ()
  prob0 _ _ := inferInstance
  probp _ _ := inferInstance

theorem blockedLaw_toNoisy {T : Tuning} (B : BlockingFamily T) (k j : ℕ) :
    noisyBlockedLaw (BlockingFamily.toNoisy B) k j = blockedLaw T B k j := by
  unfold noisyBlockedLaw blockedLaw NoisyBlockingFamily.joint NoisyBlockingFamily.noise
  have e : (fun q : GaugeConnection SU2 4 (T.side k j) × (Unit × Unit × Unit) =>
      ((BlockingFamily.toNoisy B).blk k j).B q.1 q.2) = (B k j).B ∘ Prod.fst := rfl
  rw [e, ← Measure.map_map (B k j).meas measurable_fst, Measure.map_fst_prod]
  simp [BlockingFamily.toNoisy]

end ProofPhase.Repair
