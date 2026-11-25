/-
The one-scale reduction, time translation and the Hankel identity (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §6.1 (facts (i), (ii), (iii)), §6.2 (Lemma 6.1), §6.4.
-/

import OneScale.TorusRP
import OneScale.LinkDist

/-!
# Time translation, the Hankel identity, and Theorem C with the Hankel hypothesis discharged

On the torus `(ℤ/Nℤ)^d` (direction `0` is time):

* `shiftSite j`, `shiftLink j`, `shiftPlaq j`: the time translation `t ↦ t + j` on sites, links and plaquettes;
  `tShift j U = U ∘ shiftLink j` on connections (the note's `S_j`, `(S_j U)(l) = U(l + j e₀)`).
* `measurePreserving_tShift`: `S_j` preserves `productHaar` (it permutes the coordinates).
* `prod_xp_tShift`: `∏_p φ(Re tr U_p)` is `S_j`-invariant (the plaquettes are permuted), **fact (ii)**.
* `prod_xp_thetaConn`: the weight is `Θ`-invariant (with `measurePreserving_thetaConn`, **fact (i)**).
* `tShift_thetaConn`: **`S_k ∘ Θ = Θ ∘ S_{-k}`**, **fact (iii)** (`mirror(l + k e₀) = mirror(l) - k e₀`).
* `hankel_identity`: **Lemma 6.1** in unnormalised form: for every constant `c`,
  `⟨F_j - c, F_k - c⟩ = ⟨F_{j+k} - c, F - c⟩` for the reflected form `rpForm` of `OneScale.TorusRP`.
* `rpForm_eq`, `integral_tShift`, `integral_thetaConn`, `hankel_corr`: the normalised form: with `c = μ(F)`,
  `⟨F_j - c, F_k - c⟩ = Z · Cov_μ(F_{j+k}, F ∘ Θ)` (`corr`), `Z` the partition function.
* `torus_theoremC_corr`: **Theorem C on the finite torus for the covariances `corr`** (`OneScale.TorusRP.torus_theoremC`
  with its hypothesis `hH` discharged): if `F_j` depends on the closed positive half for `j ≤ K` and
  `|Cov(F_{2^r m}, F ∘ Θ)| ≤ C e^{-λ 2^r m}`, then
  `|Cov(F_m, F ∘ Θ)| ≤ Cov(F, F ∘ Θ)^{1 - 2^{-r}} C^{2^{-r}} e^{-λ m}`.
* `torus_theoremC_hankel`: the same, unnormalised (`H(m) = ⟨F_m - c, F - c⟩`), for every `PlaqWeight` (hard admissible
  weights included).
* `linkDep_tShift_of_slab`: an observable of the time slab `[0, s]` (base times) translated by `j` with `j + s < N/2`
  depends on the closed positive half only.

The remaining hypothesis of `torus_theoremC_corr` (the decay bound at distance `2^r m`) is supplied by Theorem A in
`OneScale.CubeChain`. Osterwalder–Seiler (1978) for the reflection-positivity structure; the formalisation is ours.
-/

open MeasureTheory Finset AreaLaw.Concrete Positivity OneScale.LinkDist

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale.TimeShift

variable {d N : ℕ} [NeZero d]

/-! ## Time translation on sites, links and plaquettes -/

/-- The time translation `t ↦ t + j` of a site. -/
def shiftSite (j : ZMod N) (x : FinLatticeSites d N) : FinLatticeSites d N := Function.update x 0 (x 0 + j)

theorem shiftSite_zero_coord (j : ZMod N) (x : FinLatticeSites d N) : shiftSite j x 0 = x 0 + j := by
  simp [shiftSite]

theorem shiftSite_add (j k : ZMod N) (x : FinLatticeSites d N) :
    shiftSite j (shiftSite k x) = shiftSite (k + j) x := by
  funext i
  by_cases hi : i = 0
  · subst hi; simp [shiftSite, add_assoc]
  · simp [shiftSite, hi]

theorem shiftSite_zero (x : FinLatticeSites d N) : shiftSite 0 x = x := by
  funext i
  by_cases hi : i = 0
  · subst hi; simp [shiftSite]
  · simp [shiftSite, hi]

theorem shiftSite_siteShift (j : ZMod N) (x : FinLatticeSites d N) (μ : Fin d) :
    shiftSite j (siteShift d N x μ) = siteShift d N (shiftSite j x) μ := by
  funext i
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hμ : μ = 0
    · subst hμ
      simp only [shiftSite, siteShift, Function.update_apply, ↓reduceIte]
      ring
    · simp [shiftSite, siteShift, Function.update_apply, hμ, Ne.symm hμ]
  · by_cases hiμ : i = μ
    · subst hiμ; simp [shiftSite, siteShift, Function.update_apply, hi0]
    · simp [shiftSite, siteShift, Function.update_apply, hi0, hiμ]

theorem tflipSite_shiftSite (k : ZMod N) (x : FinLatticeSites d N) :
    tflipSite (shiftSite k x) = shiftSite (-k) (tflipSite x) := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp only [tflipSite, shiftSite, Function.update_apply, ↓reduceIte]
    ring
  · simp [tflipSite, shiftSite, Function.update_apply, hi]

theorem reflSite_shiftSite (k : ZMod N) (x : FinLatticeSites d N) :
    reflSite (shiftSite k x) = shiftSite (-k) (reflSite x) := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp only [reflSite, shiftSite, Function.update_apply, ↓reduceIte]
    ring
  · simp [reflSite, shiftSite, Function.update_apply, hi]

/-- The time translation of a link. -/
def shiftLink (j : ZMod N) (l : LatticeLink d N) : LatticeLink d N := ⟨shiftSite j l.site, l.dir⟩

/-- The time translation of a plaquette. -/
def shiftPlaq (j : ZMod N) (p : LatticePlaquette d N) : LatticePlaquette d N :=
  ⟨shiftSite j p.site, p.dir1, p.dir2, p.h_lt⟩

theorem shiftLink_add (j k : ZMod N) (l : LatticeLink d N) :
    shiftLink j (shiftLink k l) = shiftLink (k + j) l := by
  simp [shiftLink, shiftSite_add]

theorem shiftLink_zero (l : LatticeLink d N) : shiftLink 0 l = l := by
  simp [shiftLink, shiftSite_zero]

theorem shiftPlaq_add (j k : ZMod N) (p : LatticePlaquette d N) :
    shiftPlaq j (shiftPlaq k p) = shiftPlaq (k + j) p := by
  simp [shiftPlaq, shiftSite_add]

theorem shiftPlaq_zero (p : LatticePlaquette d N) : shiftPlaq 0 p = p := by
  simp [shiftPlaq, shiftSite_zero]

/-- The time translation of links as a permutation. -/
def shiftLinkEquiv (j : ZMod N) : LatticeLink d N ≃ LatticeLink d N where
  toFun := shiftLink j
  invFun := shiftLink (-j)
  left_inv l := by simp [shiftLink_add, shiftLink_zero]
  right_inv l := by simp [shiftLink_add, shiftLink_zero]

/-- The time translation of plaquettes as a permutation. -/
def shiftPlaqEquiv (j : ZMod N) : LatticePlaquette d N ≃ LatticePlaquette d N where
  toFun := shiftPlaq j
  invFun := shiftPlaq (-j)
  left_inv p := by simp [shiftPlaq_add, shiftPlaq_zero]
  right_inv p := by simp [shiftPlaq_add, shiftPlaq_zero]

theorem boundaryLinks_shiftPlaq (j : ZMod N) (p : LatticePlaquette d N) (k : Fin 4) :
    (shiftPlaq j p).boundaryLinks k = shiftLink j (p.boundaryLinks k) := by
  fin_cases k <;> simp [LatticePlaquette.boundaryLinks, shiftPlaq, shiftLink, shiftSite_siteShift]

/-- `mirror(l + k e₀) = mirror(l) - k e₀`. -/
theorem mirrorLink_shiftLink (k : ZMod N) (l : LatticeLink d N) :
    mirrorLink (shiftLink k l) = shiftLink (-k) (mirrorLink l) := by
  rcases l with ⟨s, μ⟩
  by_cases hμ : μ = 0
  · simp [mirrorLink, shiftLink, hμ, tflipSite_shiftSite]
  · simp [mirrorLink, shiftLink, hμ, reflSite_shiftSite]

/-! ## Time translation of connections -/

section Conn

variable {G : Type*} [Group G]

/-- The time translation `S_j` of a connection: `(S_j U)(l) = U(l + j e₀)`. -/
def tShift (j : ZMod N) (U : GaugeConnection G d N) : GaugeConnection G d N := fun l => U (shiftLink j l)

theorem tShift_tShift (j k : ZMod N) (U : GaugeConnection G d N) : tShift j (tShift k U) = tShift (j + k) U := by
  funext l
  simp only [tShift, shiftLink_add]

theorem tShift_zero (U : GaugeConnection G d N) : tShift 0 U = U := by
  funext l
  simp only [tShift, shiftLink_zero]

/-- **Fact (iii): `S_k ∘ Θ = Θ ∘ S_{-k}`.** -/
theorem tShift_thetaConn (k : ZMod N) (U : GaugeConnection G d N) :
    tShift k (thetaConn U) = thetaConn (tShift (-k) U) := by
  funext l
  show thetaConn U (shiftLink k l) = thetaConn (tShift (-k) U) l
  unfold thetaConn
  rw [mirrorLink_shiftLink]
  rfl

theorem plaquetteHolonomy_tShift (j : ZMod N) (U : GaugeConnection G d N) (p : LatticePlaquette d N) :
    plaquetteHolonomy (tShift j U) p = plaquetteHolonomy U (shiftPlaq j p) := by
  simp only [plaquetteHolonomy, tShift, boundaryLinks_shiftPlaq]

variable {n : ℕ} [HasGaugeTrace G n]

theorem xp_tShift (j : ZMod N) (U : GaugeConnection G d N) (p : LatticePlaquette d N) :
    xp n p (tShift j U) = xp n (shiftPlaq j p) U := by
  unfold xp; rw [plaquetteHolonomy_tShift]

variable [NeZero N]

/-- **Fact (ii), weight part**: the plaquette weight is invariant under time translation. -/
theorem prod_xp_tShift (φ : ℝ → ℝ) (j : ZMod N) (U : GaugeConnection G d N) :
    ∏ p : LatticePlaquette d N, φ (xp n p (tShift j U)) = ∏ p : LatticePlaquette d N, φ (xp n p U) := by
  simp_rw [xp_tShift]
  exact Equiv.prod_comp (shiftPlaqEquiv j) (fun p => φ (xp n p U))

/-- **Fact (i), weight part**: the plaquette weight is invariant under the site reflection. -/
theorem prod_xp_thetaConn (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (φ : ℝ → ℝ) (U : GaugeConnection G d N) :
    ∏ p : LatticePlaquette d N, φ (xp n p (thetaConn U)) = ∏ p : LatticePlaquette d N, φ (xp n p U) := by
  simp_rw [xp_thetaConn (gaugeReTr_inv_of_unitary hU)]
  exact Equiv.prod_comp (Function.Involutive.toPerm _ mirrorPlaq_involutive) (fun p => φ (xp n p U))

/-- **Fact (ii), measure part**: `S_j` preserves the product Haar measure. -/
theorem measurePreserving_tShift [MeasurableSpace G] [HasHaarProbability G] (j : ZMod N) :
    MeasurePreserving (tShift (G := G) (d := d) j) (productHaar G d N) (productHaar G d N) :=
  measurePreserving_reindex (haarG G) (shiftLinkEquiv j)

end Conn

/-! ## Slab observables translated into the positive half -/

variable [NeZero N]

theorem val_shift_time {x : ZMod N} {j : ℕ} (h : x.val + j < N) : (x + (j : ZMod N)).val = x.val + j := by
  have hj : (j : ZMod N).val = j := ZMod.val_cast_of_lt (by omega)
  rw [ZMod.val_add_of_lt (by rw [hj]; exact h), hj]

/-- A link with base time `< N/2` lies in the closed positive half. -/
theorem mem_posHalfLinks_of_time_lt {l : LatticeLink d N} (h : (l.site 0).val < N / 2) : l ∈ posHalfLinks d N := by
  unfold posHalfLinks
  rw [Finset.mem_filter]
  refine ⟨mem_univ _, ?_⟩
  unfold IsPosLink IsFixedLink
  by_cases hd : l.dir = 0
  · exact Or.inl (Or.inr ⟨hd, h⟩)
  · by_cases h0 : (l.site 0).val = 0
    · exact Or.inr ⟨hd, Or.inl h0⟩
    · exact Or.inl (Or.inl ⟨hd, Nat.pos_of_ne_zero h0, h⟩)

/-- A slab observable translated by `j` with `j + s < N/2` depends only on the closed positive half. -/
theorem linkDep_tShift_of_slab {G : Type*} [Group G] {F : GaugeConnection G d N → ℝ} {s : ℕ}
    (hF : LinkDep F (timeSlab 0 s)) {j : ℕ} (hj : j + s < N / 2) :
    LinkDep (fun U => F (tShift (j : ZMod N) U)) (posHalfLinks d N) := by
  intro U V hUV
  apply hF
  intro l hl
  rw [mem_timeSlab] at hl
  apply hUV
  apply mem_posHalfLinks_of_time_lt
  have hN2 : N / 2 ≤ N := Nat.div_le_self _ _
  show ((shiftSite (j : ZMod N) l.site) 0).val < N / 2
  rw [shiftSite_zero_coord, val_shift_time (by omega)]
  omega

/-! ## The Hankel identity -/

section Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n] [HasHaarProbability G] [(haarG G).IsInvInvariant]

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

theorem measurable_tShift (j : ZMod N) : Measurable (tShift (G := G) (d := d) j) :=
  (measurePreserving_tShift j).measurable

include hc in
/-- **Lemma 6.1 (Hankel identity), unnormalised.** For every constant `c` and `j, k ≥ 0`:
`⟨F_j - c, F_k - c⟩ = ⟨F_{j+k} - c, F - c⟩`, where `⟨A, B⟩ = ∫ A · (B ∘ Θ) · ∏_p φ(Re tr U_p) d(productHaar)`. -/
theorem hankel_identity {φ : ℝ → ℝ} (hφ : PlaqWeight n φ) {F : GaugeConnection G d N → ℝ} (hF : Measurable F)
    (c : ℝ) (j k : ℕ) :
    TorusRP.rpForm n φ (fun U => F (tShift (j : ZMod N) U) - c) (fun U => F (tShift (k : ZMod N) U) - c) =
      TorusRP.rpForm n φ (fun U => F (tShift ((j + k : ℕ) : ZMod N) U) - c) (fun U => F U - c) := by
  unfold TorusRP.rpForm
  set J : GaugeConnection G d N → ℝ := fun V => (F (tShift ((j + k : ℕ) : ZMod N) V) - c) * (F (thetaConn V) - c) *
    ∏ p ∈ (univ : Finset (LatticePlaquette d N)), φ (xp n p V) with hJdef
  have hJ : Measurable J :=
    (((hF.comp (measurable_tShift _)).sub_const c).mul ((hF.comp measurePreserving_thetaConn.measurable).sub_const c)).mul
      (measurable_phi_prod hc hφ _)
  have hpt : ∀ U : GaugeConnection G d N, (F (tShift (j : ZMod N) U) - c) * (F (tShift (k : ZMod N) (thetaConn U)) - c) *
      ∏ p ∈ (univ : Finset (LatticePlaquette d N)), φ (xp n p U) = J (tShift (-(k : ZMod N)) U) := by
    intro U
    simp only [hJdef]
    rw [tShift_tShift, ← tShift_thetaConn, prod_xp_tShift]
    have e : ((j + k : ℕ) : ZMod N) + -(k : ZMod N) = (j : ZMod N) := by push_cast; ring
    rw [e]
  calc ∫ U, (F (tShift (j : ZMod N) U) - c) * (F (tShift (k : ZMod N) (thetaConn U)) - c) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d N)), φ (xp n p U) ∂(productHaar G d N)
      = ∫ U, J (tShift (-(k : ZMod N)) U) ∂(productHaar G d N) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ V, J V ∂(productHaar G d N) :=
        integral_comp_of_measurePreserving (measurePreserving_tShift _) hJ.aestronglyMeasurable

/-! ## Normalisation -/

open OneScale.Gauge

/-- The partition function `Z = ∫ ∏_p φ(Re tr U_p) d(productHaar)`. -/
def partZ (n : ℕ) [HasGaugeTrace G n] (φ : ℝ → ℝ) : ℝ :=
  ∫ U, plaqProd (d := d) (N := N) n φ univ U ∂(productHaar G d N)

include hc hU in
theorem partZ_pos {φ : ℝ → ℝ} (hφ : PosWeight n φ) : 0 < partZ (d := d) (N := N) (G := G) n φ := by
  have hW := localWeight_plaqProd (d := d) (N := N) hc hU hφ univ
  obtain ⟨c, hc0, h⟩ := hW.lower
  have := integral_mono (integrable_const c) (hW.bm.integrable (prodMeasure (ι := LatticeLink d N) (haarG G))) h
  simp only [integral_const, probReal_univ, one_smul] at this
  exact hc0.trans_le this

/-- `PosWeight` (hypothesis (Φ)) implies `PlaqWeight` (the hypothesis of the reflection-positivity files). -/
theorem plaqWeight_of_posWeight {φ : ℝ → ℝ} (hφ : PosWeight n φ) : PlaqWeight n φ where
  meas := hφ.meas
  nonneg := by
    obtain ⟨c, hc0, h⟩ := hφ.lower
    exact fun x hx => hc0.le.trans (h x hx)
  bdd := by
    obtain ⟨c, hc0, h⟩ := hφ.lower
    obtain ⟨C, hC⟩ := hφ.upper
    exact ⟨C, fun x hx => by rw [abs_of_nonneg (hc0.le.trans (h x hx))]; exact hC x hx⟩

include hc hU in
/-- The reflected form is `Z` times the normalised expectation. -/
theorem rpForm_eq {φ : ℝ → ℝ} (hφ : PosWeight n φ) (A B : GaugeConnection G d N → ℝ) :
    TorusRP.rpForm n φ A B = partZ (d := d) (N := N) (G := G) n φ * ∫ U, A U * B (thetaConn U) ∂(gaugeMeasure n φ) := by
  have hW := localWeight_plaqProd (d := d) (N := N) hc hU hφ univ
  have hZ := partZ_pos (d := d) (N := N) hc hU hφ
  unfold gaugeMeasure
  rw [integral_weightMeasure hW.bm (fun U => (hW.pos U).le), ← integral_const_mul]
  unfold TorusRP.rpForm
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  change A U * B (thetaConn U) * plaqProd n φ univ U =
    partZ n φ * (plaqProd n φ univ U / partZ n φ * (A U * B (thetaConn U)))
  field_simp

include hc hU in
/-- Invariance of the normalised measure under a weight-preserving, Haar-preserving map. -/
theorem integral_comp_gaugeMeasure {φ : ℝ → ℝ} (hφ : PosWeight n φ) {T : GaugeConnection G d N → GaugeConnection G d N}
    (hT : MeasurePreserving T (productHaar G d N) (productHaar G d N))
    (hWT : ∀ U, plaqProd n φ univ (T U) = plaqProd n φ univ U) {F : GaugeConnection G d N → ℝ} (hF : Measurable F) :
    ∫ U, F (T U) ∂(gaugeMeasure n φ) = ∫ U, F U ∂(gaugeMeasure n φ) := by
  have hW := localWeight_plaqProd (d := d) (N := N) hc hU hφ univ
  unfold gaugeMeasure
  rw [integral_weightMeasure hW.bm (fun U => (hW.pos U).le), integral_weightMeasure hW.bm (fun U => (hW.pos U).le)]
  have hg : Measurable (fun U : GaugeConnection G d N => plaqProd n φ univ U /
      (∫ τ, plaqProd n φ univ τ ∂(prodMeasure (ι := LatticeLink d N) (haarG G))) * F U) :=
    (hW.meas.div_const _).mul hF
  have hT' : MeasurePreserving T (prodMeasure (ι := LatticeLink d N) (haarG G)) (prodMeasure (haarG G)) := hT
  have h := integral_comp_of_measurePreserving hT' hg.aestronglyMeasurable
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [hWT]

include hc hU in
/-- **Fact (ii)**: `μ(F ∘ S_j) = μ(F)`. -/
theorem integral_tShift {φ : ℝ → ℝ} (hφ : PosWeight n φ) {F : GaugeConnection G d N → ℝ} (hF : Measurable F)
    (j : ZMod N) : ∫ U, F (tShift j U) ∂(gaugeMeasure n φ) = ∫ U, F U ∂(gaugeMeasure n φ) :=
  integral_comp_gaugeMeasure hc hU hφ (measurePreserving_tShift j) (fun U => prod_xp_tShift φ j U) hF

include hc hU in
/-- **Fact (i)**: `μ(F ∘ Θ) = μ(F)`. -/
theorem integral_thetaConn {φ : ℝ → ℝ} (hφ : PosWeight n φ) {F : GaugeConnection G d N → ℝ} (hF : Measurable F) :
    ∫ U, F (thetaConn U) ∂(gaugeMeasure n φ) = ∫ U, F U ∂(gaugeMeasure n φ) :=
  integral_comp_gaugeMeasure hc hU hφ measurePreserving_thetaConn (fun U => prod_xp_thetaConn hU φ U) hF

/-- The connected reflected correlation `H_N(m) = Cov_μ(F_m, F ∘ Θ)` (note §6.2). -/
def corr (n : ℕ) [HasGaugeTrace G n] (φ : ℝ → ℝ) (F : GaugeConnection G d N → ℝ) (m : ℕ) : ℝ :=
  ∫ U, F (tShift (m : ZMod N) U) * F (thetaConn U) ∂(gaugeMeasure n φ) -
    (∫ U, F (tShift (m : ZMod N) U) ∂(gaugeMeasure n φ)) * ∫ U, F (thetaConn U) ∂(gaugeMeasure n φ)

theorem integral_centered_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hfg : Integrable (fun x => f x * g x) μ) (c : ℝ) :
    ∫ x, (f x - c) * (g x - c) ∂μ = ∫ x, f x * g x ∂μ - c * ∫ x, f x ∂μ - c * ∫ x, g x ∂μ + c * c := by
  have hcf : Integrable (fun x => c * f x) μ := hf.const_mul c
  have hcg : Integrable (fun x => c * g x) μ := hg.const_mul c
  have h2 : Integrable (fun x => f x * g x - c * f x) μ := hfg.sub hcf
  have h1 : Integrable (fun x => f x * g x - c * f x - c * g x) μ := h2.sub hcg
  calc ∫ x, (f x - c) * (g x - c) ∂μ = ∫ x, ((f x * g x - c * f x - c * g x) + c * c) ∂μ := by
        congr 1; funext x; ring
    _ = ∫ x, (f x * g x - c * f x - c * g x) ∂μ + ∫ _x, c * c ∂μ := integral_add h1 (integrable_const _)
    _ = ∫ x, (f x * g x - c * f x) ∂μ - ∫ x, c * g x ∂μ + c * c := by
        rw [integral_sub h2 hcg, integral_const, probReal_univ, one_smul]
    _ = ∫ x, f x * g x ∂μ - ∫ x, c * f x ∂μ - ∫ x, c * g x ∂μ + c * c := by rw [integral_sub hfg hcf]
    _ = _ := by rw [integral_const_mul, integral_const_mul]

include hc hU in
/-- **Lemma 6.1 (Hankel identity), normalised.** With `c = μ(F)`:
`⟨F_j - c, F_k - c⟩ = Z · Cov_μ(F_{j+k}, F ∘ Θ)`. -/
theorem hankel_corr {φ : ℝ → ℝ} (hφ : PosWeight n φ) {F : GaugeConnection G d N → ℝ} (hF : BM F) (j k : ℕ) :
    TorusRP.rpForm n φ (fun U => F (tShift (j : ZMod N) U) - ∫ V, F V ∂(gaugeMeasure n φ))
      (fun U => F (tShift (k : ZMod N) U) - ∫ V, F V ∂(gaugeMeasure n φ)) =
      partZ (d := d) (N := N) (G := G) n φ * corr n φ F (j + k) := by
  haveI := isProbabilityMeasure_gaugeMeasure (d := d) (N := N) hc hU hφ
  set μ := gaugeMeasure (d := d) (N := N) (G := G) n φ
  set c := ∫ V, F V ∂μ
  rw [hankel_identity hc (plaqWeight_of_posWeight hφ) hF.meas c j k, rpForm_eq hc hU hφ]
  congr 1
  have hS : BM (fun U => F (tShift ((j + k : ℕ) : ZMod N) U)) := by
    obtain ⟨M, hM⟩ := hF.bdd
    exact ⟨hF.meas.comp (measurable_tShift _), ⟨M, fun U => hM _⟩⟩
  have hT : BM (fun U => F (thetaConn U)) := by
    obtain ⟨M, hM⟩ := hF.bdd
    exact ⟨hF.meas.comp measurePreserving_thetaConn.measurable, ⟨M, fun U => hM _⟩⟩
  have e1 : ∫ U, F (tShift ((j + k : ℕ) : ZMod N) U) ∂μ = c := integral_tShift hc hU hφ hF.meas _
  have e2 : ∫ U, F (thetaConn U) ∂μ = c := integral_thetaConn hc hU hφ hF.meas
  have h := integral_centered_mul (μ := μ) (hS.integrable μ) (hT.integrable μ) ((hS.mul hT).integrable μ) c
  unfold corr
  simp only [μ] at h e1 e2 ⊢
  rw [h, e1, e2]
  ring

/-! ## Theorem C on the finite torus, Hankel hypothesis discharged -/

variable (hN : Even N)

include hN hc hU in
/-- **Theorem C on the finite torus, for the covariances** `H(m) = Cov_μ(F_m, F ∘ Θ)` (note §6.4), with the Hankel
identity proved (`hankel_corr`) rather than assumed. If the translates `F_j`, `j ≤ K`, depend only on the closed positive
half, `2^{r-1} m ≤ K`, `r ≥ 1`, and Theorem A (or anything else) gives `|H(2^r m)| ≤ C e^{-λ 2^r m}`, then
`|H(m)| ≤ H(0)^{1 - 2^{-r}} C^{2^{-r}} e^{-λ m}`, and `H(0) ≥ 0`. -/
theorem torus_theoremC_corr {φ : ℝ → ℝ} (hφ : PosWeight n φ) {F : GaugeConnection G d N → ℝ} (hF : BM F) {K : ℕ}
    (hpos : ∀ j, j ≤ K → LinkDep (fun U => F (tShift (j : ZMod N) U)) (posHalfLinks d N))
    {m r : ℕ} (hr : 1 ≤ r) (hmK : 2 ^ (r - 1) * m ≤ K) {C lam : ℝ} (hC : 0 ≤ C)
    (hdecay : |corr n φ F (2 ^ r * m)| ≤ C * Real.exp (-(lam * (2 ^ r * m : ℕ)))) :
    0 ≤ corr n φ F 0 ∧
      |corr n φ F m| ≤ corr n φ F 0 ^ (1 - (1 / 2 : ℝ) ^ r) * C ^ ((1 / 2 : ℝ) ^ r) * Real.exp (-(lam * m)) := by
  have hZ := partZ_pos (d := d) (N := N) hc hU hφ
  set Z := partZ (d := d) (N := N) (G := G) n φ
  set c := ∫ V, F V ∂(gaugeMeasure (d := d) (N := N) (G := G) n φ)
  set Fs : ℕ → GaugeConnection G d N → ℝ := fun j U => F (tShift (j : ZMod N) U) - c
  set H : ℕ → ℝ := fun m => Z * corr n φ F m
  obtain ⟨M, hM⟩ := hF.bdd
  have hFs : ∀ j, j ≤ K → LinkDep (Fs j) (posHalfLinks d N) ∧ Measurable (Fs j) ∧ ∃ M, ∀ U, |Fs j U| ≤ M := by
    intro j hj
    refine ⟨fun U V h => ?_, (hF.meas.comp (measurable_tShift _)).sub_const c, ⟨M + |c|, fun U => ?_⟩⟩
    · have e : F (tShift (j : ZMod N) U) = F (tShift (j : ZMod N) V) := hpos j hj U V h
      simp only [Fs]; rw [e]
    · exact (abs_sub _ _).trans (add_le_add (hM _) le_rfl)
  have hH : ∀ j k, j ≤ K → k ≤ K → TorusRP.rpForm n φ (Fs j) (Fs k) = H (j + k) :=
    fun j k _ _ => hankel_corr hc hU hφ hF j k
  have hφ' := plaqWeight_of_posWeight hφ
  have h0 : 0 ≤ corr n φ F 0 := by
    have := (TorusRP.hankel_cs hN hc hU hφ' hFs hH).2 0 (Nat.zero_le _)
    simp only [H, mul_zero] at this
    exact nonneg_of_mul_nonneg_right (by linarith) hZ
  refine ⟨h0, ?_⟩
  have hdec' : |H (2 ^ r * m)| ≤ (Z * C) * Real.exp (-(lam * (2 ^ r * m : ℕ))) := by
    simp only [H, abs_mul, abs_of_pos hZ, mul_assoc]
    exact mul_le_mul_of_nonneg_left hdecay hZ.le
  have h := TorusRP.torus_theoremC hN hc hU hφ' hFs hH hr hmK (mul_nonneg hZ.le hC) hdec'
  set a : ℝ := (1 / 2 : ℝ) ^ r
  simp only [H, abs_mul, abs_of_pos hZ] at h
  rw [Real.mul_rpow hZ.le h0, Real.mul_rpow hZ.le hC] at h
  have hZa : Z ^ (1 - a) * Z ^ a = Z := by
    rw [← Real.rpow_add hZ, sub_add_cancel, Real.rpow_one]
  have e : Z ^ (1 - a) * corr n φ F 0 ^ (1 - a) * (Z ^ a * C ^ a) * Real.exp (-(lam * m)) =
      (Z ^ (1 - a) * Z ^ a) * (corr n φ F 0 ^ (1 - a) * C ^ a * Real.exp (-(lam * m))) := by ring
  rw [hZa] at e
  rw [e] at h
  exact le_of_mul_le_mul_left h hZ

/-- The unnormalised reflected correlation `H(m) = ⟨F_m - c, F - c⟩` (any constant `c`). -/
def hankelH (n : ℕ) [HasGaugeTrace G n] (φ : ℝ → ℝ) (F : GaugeConnection G d N → ℝ) (c : ℝ) (m : ℕ) : ℝ :=
  TorusRP.rpForm n φ (fun U => F (tShift (m : ZMod N) U) - c) (fun U => F U - c)

include hN hc hU in
/-- **`OneScale.TorusRP.torus_theoremC` with the Hankel hypothesis `hH` discharged**, unnormalised form, for every
plaquette weight `φ ≥ 0` of `Positivity.PlaqWeight` (Wilson, soft and hard admissible weights): for the translates
`F_j = F ∘ S_j` and any constant `c`,
`|H(m)| ≤ H(0)^{1 - 2^{-r}} C^{2^{-r}} e^{-λ m}` with `H(m) = ⟨F_m - c, F - c⟩`, given the decay bound at `2^r m`. -/
theorem torus_theoremC_hankel {φ : ℝ → ℝ} (hφ : PlaqWeight n φ) {F : GaugeConnection G d N → ℝ} (hFm : Measurable F)
    (hFb : ∃ M, ∀ U, |F U| ≤ M) (c : ℝ) {K : ℕ}
    (hpos : ∀ j, j ≤ K → LinkDep (fun U => F (tShift (j : ZMod N) U)) (posHalfLinks d N))
    {m r : ℕ} (hr : 1 ≤ r) (hmK : 2 ^ (r - 1) * m ≤ K) {C lam : ℝ} (hC : 0 ≤ C)
    (hdecay : |hankelH n φ F c (2 ^ r * m)| ≤ C * Real.exp (-(lam * (2 ^ r * m : ℕ)))) :
    |hankelH n φ F c m| ≤
      hankelH n φ F c 0 ^ (1 - (1 / 2 : ℝ) ^ r) * C ^ ((1 / 2 : ℝ) ^ r) * Real.exp (-(lam * m)) := by
  obtain ⟨M, hM⟩ := hFb
  refine TorusRP.torus_theoremC hN hc hU hφ (F := fun j U => F (tShift (j : ZMod N) U) - c)
    (H := hankelH n φ F c) (fun j hj => ⟨?_, ?_, ?_⟩) (fun j k _ _ => hankel_identity hc hφ hFm c j k) hr hmK hC
    hdecay
  · intro U V h
    have e : F (tShift (j : ZMod N) U) = F (tShift (j : ZMod N) V) := hpos j hj U V h
    simp only [e]
  · exact (hFm.comp (measurable_tShift _)).sub_const c
  · exact ⟨M + |c|, fun U => (abs_sub _ _).trans (add_le_add (hM _) le_rfl)⟩

end Measure

end OneScale.TimeShift
