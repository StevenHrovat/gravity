/-
Proof phase (round 5), workstream 1 (Route A): the blocked route's last link in Lean (missing link L1 of
`ASSEMBLY.md`), 2026-11-22. Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/ws1-routeA/NOTE.md`, section 3.
-/

import ProofPhase.RouteA.Blocking
import ProofPhase.Existence.Bridge

/-!
# The blocked route at `L₁` gives `SlabDecay` (and, with a level-uniform transfer, `TorusDecay`)

`Assembly.lean` proves `blockGap_of_blockedRoute`: `H1Local ∧ LimitDprime` give decay of **block** observables `f ∘ Φ` of
the SU(2) Wilson measure. The missing link L1 was the passage to the **slab** observables of `SlabDecay` (arbitrary
measurable gauge-invariant fine observables, `|F| ≤ 1`): on paper the law of total covariance plus the slab geometry
(`r3-robust/NOTE.md` §6). Here it is in Lean.

* `cov_transfer` (generic, any probability space and measurable map `Φ`): if `E[F|Φ]`, `E[G|Φ]` are `ε`-close in `L¹` to
  `f ∘ Φ`, `g ∘ Φ` (`|f|, |g| ≤ 1`) and `F`, `G` decouple given `Φ` up to `ε`, then
  `|Cov(F, G)| ≤ |Cov(f ∘ Φ, g ∘ Φ)| + 5ε`.
* `gaugeInvariant_tShift`, `gaugeInvariant_thetaConn`: time translates and reflections of gauge-invariant observables
  are gauge invariant.
* `wcorr_le_blocked`: the one-level, one-volume estimate for the reflected slab correlation of the SU(2) Wilson measure.
* **`slabDecay_of_blockedRoute`**: `H1Local ∧ LimitDprime(λ > 0) ∧ ObsTransfer ⇒ SlabDecay` (missing link L1 closed).
  The constant grows with the level through the support bound `V k` (the coarse support of `E[F|Φ]` is bounded by the
  fine support count in `ObsTransfer`).
* `ObsTransferU` and **`torusDecay_of_blockedRouteU`**: with a **level-uniform** transfer (the block approximant's total
  Dobrushin oscillation bounded by `2K(1 + D/L₁)⁴` uniformly in the level, for every support bound `Vb`) the same chain
  gives `TorusDecay`, the level-uniform form of workstream 4 (`ProofPhase.Existence.Bridge`), and with it the gap in
  both orders of limits. Why `ObsTransfer` reaches only `SlabDecay`: its coarse support bound is proportional to the fine
  support count, and physical observables at level `k` have of order `ℓ_k⁴` fine links.
* `massGap_of_blockedRoute`, `bothOrders_of_blockedRouteU`, `massGap_of_goodBlocking`: the assembled statements; the last
  one with the concrete reflection-positive blocking of `ProofPhase.RouteA.Blocking`.

**Claim level.** Substantive as a reduction (it uses the Wilson measure's translation and reflection structure, the slab
separation `sep_shift_mirror`, and conditional expectations); all physics is in the hypotheses `H1Local`, `LimitDprime`,
`ObsTransfer`(`U`), which are open. `LimitDprime` is confinement-strength (a worst-case Dobrushin condition at `L₁`).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift OneScale.CubeChain Positivity Attempts.R4.Layer ProofPhase.Existence

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.RouteA

/-! ## The transfer of covariances through a conditional expectation (generic) -/

section Transfer

variable {X Y : Type*} [MX : MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) [IsProbabilityMeasure μ]

theorem integrable_of_abs_le {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ} (h : ∀ᵐ x ∂μ, |f x| ≤ C) :
    Integrable f μ :=
  Integrable.of_bound hf C (h.mono fun x hx => by rwa [Real.norm_eq_abs])

theorem abs_integral_le_one {f : X → ℝ} (h : ∀ᵐ x ∂μ, |f x| ≤ 1) : |∫ x, f x ∂μ| ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := 1) (h.mono fun x hx => by rwa [Real.norm_eq_abs])
  simpa using this

/-- **Covariances pass through a conditional expectation.** -/
theorem cov_transfer {Φ : X → Y} (hΦ : Measurable Φ) {F G : X → ℝ} {f g : Y → ℝ}
    (hF : Measurable F) (hG : Measurable G) (hF1 : ∀ x, |F x| ≤ 1) (hG1 : ∀ x, |G x| ≤ 1)
    (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ y, |f y| ≤ 1) (hg1 : ∀ y, |g y| ≤ 1) {ε : ℝ}
    (hEF : ∫ x, |μ[F | MeasurableSpace.comap Φ inferInstance] x - f (Φ x)| ∂μ ≤ ε)
    (hEG : ∫ x, |μ[G | MeasurableSpace.comap Φ inferInstance] x - g (Φ x)| ∂μ ≤ ε)
    (hdec : |∫ x, F x * G x ∂μ - ∫ x, μ[F | MeasurableSpace.comap Φ inferInstance] x *
        μ[G | MeasurableSpace.comap Φ inferInstance] x ∂μ| ≤ ε) :
    |∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * ∫ x, G x ∂μ| ≤
      |∫ x, f (Φ x) * g (Φ x) ∂μ - (∫ x, f (Φ x) ∂μ) * ∫ x, g (Φ x) ∂μ| + 5 * ε := by
  have hm : MeasurableSpace.comap Φ (inferInstance : MeasurableSpace Y) ≤ MX := hΦ.comap_le
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  set EF := μ[F | MeasurableSpace.comap Φ inferInstance]
  set EG := μ[G | MeasurableSpace.comap Φ inferInstance]
  have iF : Integrable F μ := integrable_of_abs_le μ hF.aestronglyMeasurable (ae_of_all _ hF1)
  have iG : Integrable G μ := integrable_of_abs_le μ hG.aestronglyMeasurable (ae_of_all _ hG1)
  have ifΦ : Integrable (fun x => f (Φ x)) μ :=
    integrable_of_abs_le μ (hf.comp hΦ).aestronglyMeasurable (ae_of_all _ fun x => hf1 _)
  have igΦ : Integrable (fun x => g (Φ x)) μ :=
    integrable_of_abs_le μ (hg.comp hΦ).aestronglyMeasurable (ae_of_all _ fun x => hg1 _)
  have iEF : Integrable EF μ := integrable_condExp
  have iEG : Integrable EG μ := integrable_condExp
  have bEF : ∀ᵐ x ∂μ, |EF x| ≤ 1 := ae_bdd_abs_condExp_of_ae_bdd_abs (ae_of_all _ hF1)
  have bEG : ∀ᵐ x ∂μ, |EG x| ≤ 1 := ae_bdd_abs_condExp_of_ae_bdd_abs (ae_of_all _ hG1)
  have hIF : ∫ x, EF x ∂μ = ∫ x, F x ∂μ := integral_condExp hm
  have hIG : ∫ x, EG x ∂μ = ∫ x, G x ∂μ := integral_condExp hm
  have iEFf : Integrable (fun x => EF x - f (Φ x)) μ := iEF.sub ifΦ
  have iEGg : Integrable (fun x => EG x - g (Φ x)) μ := iEG.sub igΦ
  have hε : 0 ≤ ε := (integral_nonneg fun x => abs_nonneg _).trans hEF
  -- the means
  have ha : |∫ x, F x ∂μ - ∫ x, f (Φ x) ∂μ| ≤ ε := by
    rw [← hIF, ← integral_sub iEF ifΦ]
    exact (abs_integral_le_integral_abs).trans hEF
  have hb : |∫ x, G x ∂μ - ∫ x, g (Φ x) ∂μ| ≤ ε := by
    rw [← hIG, ← integral_sub iEG igΦ]
    exact (abs_integral_le_integral_abs).trans hEG
  -- the conditional products
  have iEFEG : Integrable (fun x => EF x * EG x) μ :=
    integrable_of_abs_le μ (iEF.aestronglyMeasurable.mul iEG.aestronglyMeasurable) (by
      filter_upwards [bEF, bEG] with x h1 h2
      rw [abs_mul]; exact mul_le_one₀ h1 (abs_nonneg _) h2)
  have ifg : Integrable (fun x => f (Φ x) * g (Φ x)) μ :=
    integrable_of_abs_le μ (((hf.comp hΦ).mul (hg.comp hΦ))).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [abs_mul]; exact mul_le_one₀ (hf1 _) (abs_nonneg _) (hg1 _))
  have hc : |∫ x, EF x * EG x ∂μ - ∫ x, f (Φ x) * g (Φ x) ∂μ| ≤ 2 * ε := by
    rw [← integral_sub iEFEG ifg]
    refine (abs_integral_le_integral_abs).trans ?_
    have hle : ∀ᵐ x ∂μ, |EF x * EG x - f (Φ x) * g (Φ x)| ≤ |EF x - f (Φ x)| + |EG x - g (Φ x)| := by
      filter_upwards [bEG] with x hx
      have e : EF x * EG x - f (Φ x) * g (Φ x) = (EF x - f (Φ x)) * EG x + f (Φ x) * (EG x - g (Φ x)) := by ring
      rw [e]
      calc _ ≤ |(EF x - f (Φ x)) * EG x| + |f (Φ x) * (EG x - g (Φ x))| := abs_add_le _ _
        _ = |EF x - f (Φ x)| * |EG x| + |f (Φ x)| * |EG x - g (Φ x)| := by rw [abs_mul, abs_mul]
        _ ≤ |EF x - f (Φ x)| * 1 + 1 * |EG x - g (Φ x)| := by
          gcongr
          exact hf1 _
        _ = _ := by ring
    calc ∫ x, |EF x * EG x - f (Φ x) * g (Φ x)| ∂μ
        ≤ ∫ x, (|EF x - f (Φ x)| + |EG x - g (Φ x)|) ∂μ :=
          integral_mono_ae (iEFEG.sub ifg).abs (iEFf.abs.add iEGg.abs) hle
      _ = ∫ x, |EF x - f (Φ x)| ∂μ + ∫ x, |EG x - g (Φ x)| ∂μ := integral_add iEFf.abs iEGg.abs
      _ ≤ 2 * ε := by linarith
  -- the products of means
  have bIG : |∫ x, G x ∂μ| ≤ 1 := abs_integral_le_one μ (ae_of_all _ hG1)
  have bIf : |∫ x, f (Φ x) ∂μ| ≤ 1 := abs_integral_le_one μ (ae_of_all _ fun x => hf1 _)
  have hd : |(∫ x, F x ∂μ) * ∫ x, G x ∂μ - (∫ x, f (Φ x) ∂μ) * ∫ x, g (Φ x) ∂μ| ≤ 2 * ε := by
    have e : (∫ x, F x ∂μ) * ∫ x, G x ∂μ - (∫ x, f (Φ x) ∂μ) * ∫ x, g (Φ x) ∂μ =
        (∫ x, F x ∂μ - ∫ x, f (Φ x) ∂μ) * ∫ x, G x ∂μ +
          (∫ x, f (Φ x) ∂μ) * (∫ x, G x ∂μ - ∫ x, g (Φ x) ∂μ) := by ring
    rw [e]
    calc _ ≤ |(∫ x, F x ∂μ - ∫ x, f (Φ x) ∂μ) * ∫ x, G x ∂μ| +
          |(∫ x, f (Φ x) ∂μ) * (∫ x, G x ∂μ - ∫ x, g (Φ x) ∂μ)| := abs_add_le _ _
      _ = |∫ x, F x ∂μ - ∫ x, f (Φ x) ∂μ| * |∫ x, G x ∂μ| +
          |∫ x, f (Φ x) ∂μ| * |∫ x, G x ∂μ - ∫ x, g (Φ x) ∂μ| := by rw [abs_mul, abs_mul]
      _ ≤ ε * 1 + 1 * ε := by gcongr <;> assumption
      _ = 2 * ε := by ring
  -- assemble
  set Y0 := ∫ x, f (Φ x) * g (Φ x) ∂μ - (∫ x, f (Φ x) ∂μ) * ∫ x, g (Φ x) ∂μ
  have key : ∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * ∫ x, G x ∂μ =
      Y0 + (∫ x, F x * G x ∂μ - ∫ x, EF x * EG x ∂μ) + (∫ x, EF x * EG x ∂μ - ∫ x, f (Φ x) * g (Φ x) ∂μ) -
        ((∫ x, F x ∂μ) * ∫ x, G x ∂μ - (∫ x, f (Φ x) ∂μ) * ∫ x, g (Φ x) ∂μ) := by
    simp only [Y0]; ring
  rw [key]
  have h1 := abs_le.mp hdec
  have h2 := abs_le.mp hc
  have h3 := abs_le.mp hd
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [neg_abs_le Y0, le_abs_self Y0]

end Transfer

/-! ## Gauge invariance of translates and reflections -/

section Gauge

variable {d N : ℕ} [NeZero d] [NeZero N] {G : Type*} [Group G]

theorem gaugeInvariant_tShift {F : GaugeConnection G d N → ℝ} (hF : GaugeInvariant F) (j : ZMod N) :
    GaugeInvariant (fun U => F (tShift j U)) := by
  intro g U
  have e : tShift j (gaugeTransformConnection g U) =
      gaugeTransformConnection (fun x => g (shiftSite j x)) (tShift j U) := by
    funext l
    simp only [tShift, gaugeTransformConnection, shiftLink, LatticeLink.target, shiftSite_siteShift]
  show F (tShift j (gaugeTransformConnection g U)) = F (tShift j U)
  rw [e, hF]

theorem gaugeInvariant_thetaConn {F : GaugeConnection G d N → ℝ} (hF : GaugeInvariant F) :
    GaugeInvariant (fun U => F (thetaConn U)) := by
  intro g U
  have e : thetaConn (gaugeTransformConnection g U) =
      gaugeTransformConnection (fun x => g (reflSite x)) (thetaConn U) := by
    funext l
    rcases l with ⟨x, μ⟩
    by_cases hμ : μ = 0
    · subst hμ
      simp only [thetaConn, mirrorLink, gaugeTransformConnection, LatticeLink.target, ↓reduceIte,
        siteShift_tflipSite_zero, reflSite_siteShift_zero]
      group
    · simp only [thetaConn, mirrorLink, gaugeTransformConnection, LatticeLink.target, hμ, ↓reduceIte,
        reflSite_siteShift _ hμ]
  show F (thetaConn (gaugeTransformConnection g U)) = F (thetaConn U)
  rw [e, hF]

end Gauge

/-! ## Support intersections and the polynomial factor -/

theorem DepOn.inter {ι S : Type*} [DecidableEq ι] {h : (ι → S) → ℝ} {A B : Finset ι} (hA : DepOn h A) (hB : DepOn h B) :
    DepOn h (A ∩ B) := by
  intro σ σ' hσ
  set τ : ι → S := fun i => if i ∈ A then σ i else σ' i
  have h1 : h σ = h τ := hA _ _ fun i hi => by simp [τ, hi]
  have h2 : h τ = h σ' := hB _ _ fun i hi => by
    by_cases hiA : i ∈ A
    · simp only [τ, hiA, ↓reduceIte]; exact hσ i (Finset.mem_inter.mpr ⟨hiA, hi⟩)
    · simp [τ, hiA]
  rw [h1, h2]

theorem poly_exp_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    (1 + x) ^ 4 * Real.exp (-(2 * a * x)) ≤ 24 / a ^ 4 * Real.exp a * Real.exp (-(a * x)) := by
  have h := Real.pow_div_factorial_le_exp (a * (1 + x)) (by positivity) 4
  have hf : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at h
  have h4 : (1 + x) ^ 4 ≤ Real.exp (a * (1 + x)) * (24 / a ^ 4) := by
    calc (1 + x) ^ 4 = (a * (1 + x)) ^ 4 / 24 * (24 / a ^ 4) := by field_simp
      _ ≤ Real.exp (a * (1 + x)) * (24 / a ^ 4) := by gcongr
  calc (1 + x) ^ 4 * Real.exp (-(2 * a * x)) ≤ Real.exp (a * (1 + x)) * (24 / a ^ 4) * Real.exp (-(2 * a * x)) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = 24 / a ^ 4 * (Real.exp (a * (1 + x)) * Real.exp (-(2 * a * x))) := by ring
    _ = 24 / a ^ 4 * Real.exp a * Real.exp (-(a * x)) := by
        rw [mul_assoc (24 / a ^ 4) (Real.exp a), ← Real.exp_add, ← Real.exp_add]; congr 2; ring

/-! ## The one-level estimate -/

/-- **The reflected slab correlation through the blocking**, at one level `k` and one volume `j`: given the block-gap
bound at this level (the conclusion of `blockGap_of_blockedRoute`) and the transfer data for `F ∘ S_n` and `F ∘ Θ`
(coarse observables `f`, `g`, `|·| ≤ 1`, a Dobrushin oscillation bound `v_f` of `f` with `∑_{A'} v_f ≤ Kv`, coarse
separation `≥ D/(2L₁)` with `D = n a_k`, and the three transfer estimates with error `ε`), the reflected correlation is at
most `(1 − γ)⁻¹ · Kv · 2 · e^{−λ D/(2L₁)} + 5ε`. -/
theorem wcorr_le_blocked (T : Tuning) (B : BlockingFamily T) {k j : ℕ} {s : ℝ} {V : ℕ → ℕ} (O : SlabObs T s V)
    (n : ℕ) {γ lam ε Kv : ℝ}
    (hgap : ∀ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
      (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg R : ℝ),
      OneScale.BM f → OneScale.BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) →
      (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
      |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
          (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
        (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)))
    (hγ : γ < 1)
    (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j)))
    (mf : Measurable f) (mg : Measurable g) (bf : ∀ V, |f V| ≤ 1) (bg : ∀ V, |g V| ≤ 1)
    (dfA : DepOn f A') (dgB : DepOn g B') (vf : LatticeLink 4 (coarseSide j) → ℝ) (hvf : OscBound f vf)
    (hsumv : ∑ a ∈ A', vf a ≤ Kv)
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
    |T.wcorr k j (O.F k j) n| ≤
      (1 - γ)⁻¹ * Kv * 2 * Real.exp (-(lam * ((n * T.a k) / (2 * T.L₁)))) + 5 * ε := by
  haveI := isProbabilityMeasure_gaugeMeasure (d := 4) (N := T.side k j) (G := SU2) (n := 2) continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (posWeight_wilson 2 (T.β k))
  have hFm := O.meas k j
  have hF1 := O.bdd k j
  have htr := cov_transfer (T.ym k j) (B k j).meas (hFm.comp (measurable_tShift _))
    (hFm.comp measurePreserving_thetaConn.measurable) (fun U => hF1 _) (fun U => hF1 _) mf mg bf bg hEF hEG hdec
  -- the block-gap bound for `f`, `g`
  have hvg : OscBound g (fun _ => (2 : ℝ)) := by
    intro σ x s'
    have := bg σ; have := bg (Function.update σ x s')
    exact (abs_sub _ _).trans (by linarith)
  have hL1 := T.L₁_pos
  have hR : ∀ x ∈ A', ∀ y ∈ B', (n * T.a k) / (2 * T.L₁) ≤ linkDist x y := by
    intro x hx y hy
    rw [div_le_iff₀ (by positivity)]
    have := hsep x hx y hy
    nlinarith
  have hblk := hgap f g A' B' vf 2 _ ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩ dfA dgB hvf (by norm_num) hvg hR
  have hγ' : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.mpr (by linarith)
  have hblk' : |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
      (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
      (1 - γ)⁻¹ * Kv * 2 * Real.exp (-(lam * ((n * T.a k) / (2 * T.L₁)))) := by
    refine hblk.trans ?_
    gcongr
  unfold Tuning.wcorr corr
  exact htr.trans (by linarith)

/-! ## `SlabDecay` from the blocked route (missing link L1) -/

/-- A function `|f| ≤ 1` of the links in `A'` has the oscillation bound `2·1_{A'}`, of total `2|A'|`. -/
theorem oscBound_indicator {ι S : Type*} [DecidableEq ι] [Fintype ι] {f : (ι → S) → ℝ} {A' : Finset ι}
    (bf : ∀ V, |f V| ≤ 1) (dfA : DepOn f A') :
    OscBound f (fun l => if l ∈ A' then 2 else 0) ∧ ∑ a ∈ A', (if a ∈ A' then (2 : ℝ) else 0) = 2 * A'.card := by
  refine ⟨fun σ x s' => ?_, ?_⟩
  · by_cases hx : x ∈ A'
    · simp only [hx, ↓reduceIte]
      have := bf σ; have := bf (Function.update σ x s')
      exact (abs_sub _ _).trans (by linarith)
    · simp only [hx, ↓reduceIte]
      have : f σ = f (Function.update σ x s') :=
        dfA _ _ fun i hi => by rw [Function.update_of_ne (by rintro rfl; exact hx hi)]
      rw [this, sub_self, abs_zero]
  · rw [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]; ring

/-- The data of a slab observable at time `n` against its reflection, in the form `ObsTransfer` consumes. -/
theorem slab_transfer_data (T : Tuning) {k j : ℕ} {s : ℝ} {V : ℕ → ℕ} (O : SlabObs T s V) {n : ℕ}
    (hn : 2 * n + 2 * T.thick k s + 2 ≤ T.side k j) :
    let A₀ := ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j)))
    let B₀ := ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image mirrorLink
    DepOn (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) A₀ ∧
      DepOn (fun U => O.F k j (thetaConn U)) B₀ ∧ A₀.card ≤ V k ∧ B₀.card ≤ V k ∧
      ∀ e ∈ A₀, ∀ e' ∈ B₀, n * T.a k ≤ T.a k * linkDist e e' := by
  intro A₀ B₀
  have hdep := DepOn.inter (O.dep k j) (O.slab k j)
  have hc : ((O.supp k j) ∩ timeSlab 0 (T.thick k s)).card ≤ V k :=
    (Finset.card_le_card Finset.inter_subset_left).trans (O.supp_card k j)
  refine ⟨?_, ?_, (Finset.card_image_le).trans hc, (Finset.card_image_le).trans hc, ?_⟩
  · intro U U' h
    apply hdep
    intro l hl
    exact h _ (mem_image_of_mem _ hl)
  · intro U U' h
    apply hdep
    intro l hl
    have := h _ (mem_image_of_mem _ hl)
    simp only [thetaConn, this]
  · intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := mem_image.1 he'
    have := sep_shift_mirror hn (Finset.mem_inter.mp hl).2 (Finset.mem_inter.mp hl').2
    rw [mul_comm (n : ℝ) (T.a k)]
    exact mul_le_mul_of_nonneg_left this (T.a_pos k).le

/-- **Missing link L1 (closed): the blocked route at `L₁` gives `SlabDecay`.** For any reflection-respecting blocking
family `B` of the SU(2) Wilson measure along `T`: `H1Local` (blocked laws are Gibbs with locally converging coarse
potentials), `LimitDprime` with `λ > 0` (the limit potentials satisfy D′_λ, worst case, at `L₁`), and `ObsTransfer`
(conditional decoupling and quasi-locality of `E[F|Φ]`) imply `SlabDecay T` with the physical rate
`min(λ/(4L₁), m)`. -/
theorem slabDecay_of_blockedRoute {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf)
    (h2 : LimitDprime lam Vinf) (h3 : ObsTransfer T B) : SlabDecay T := by
  obtain ⟨γ, -, hγ1, k₀, hgap⟩ := blockGap_of_blockedRoute B hlam.le h1 h2
  obtain ⟨c, m, hc, hm, K, k₁, htr⟩ := h3
  have hL1 := T.L₁_pos
  set a := lam / 4
  have ha : 0 < a := by positivity
  set m' := min (lam / (4 * T.L₁)) m
  have hm' : 0 < m' := lt_min (by positivity) hm
  refine ⟨m', hm', fun s V => ⟨max k₀ k₁, fun k hk => ?_⟩⟩
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hk₁ : k₁ ≤ k := (le_max_right _ _).trans hk
  set K' := |K| * ((V k : ℝ) + 1)
  have hγ' : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.mpr (by linarith)
  refine ⟨(1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a) + 5 * c, by positivity, fun j O n hn => ?_⟩
  obtain ⟨hdA, hdB, hcA, hcB, hsep⟩ := slab_transfer_data T O hn
  have hak := T.a_pos k
  set D := (n : ℝ) * T.a k
  have hD : 0 ≤ D := by positivity
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hA', -, hsep', hEF, hEG, hdec⟩ :=
    htr k hk₁ j _ _ _ _ D ((O.meas k j).comp (measurable_tShift _))
      ((O.meas k j).comp measurePreserving_thetaConn.measurable) (fun U => O.bdd k j _) (fun U => O.bdd k j _)
      (gaugeInvariant_tShift (O.gauge k j) _) (gaugeInvariant_thetaConn (O.gauge k j)) hdA hdB hsep
  have hx : 0 ≤ D / T.L₁ := by positivity
  have hcard : (A'.card : ℝ) ≤ K' * (1 + D / T.L₁) ^ 4 := by
    have hcA' : ((((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image
        (shiftLink (n : ZMod (T.side k j)))).card : ℝ) ≤ V k := by exact_mod_cast hcA
    refine hA'.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K))
  obtain ⟨hvf, hsum⟩ := oscBound_indicator bf dfA
  have hmain := wcorr_le_blocked T B O n (hgap k hk₀ j) hγ1 f g A' B' mf mg bf bg dfA dgB _ hvf
    (Kv := 2 * (K' * (1 + D / T.L₁) ^ 4)) (by rw [hsum]; linarith) hsep' hEF hEG hdec
  -- absorb the polynomial factor
  have hpoly := poly_exp_le ha hx
  have e1 : lam * (D / (2 * T.L₁)) = 2 * a * (D / T.L₁) := by simp only [a]; field_simp; ring
  have e2 : a * (D / T.L₁) = lam / (4 * T.L₁) * D := by simp only [a]; field_simp
  have hE1 : Real.exp (-(lam / (4 * T.L₁) * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (lam / (4 * T.L₁)) m])
  have hE2 : Real.exp (-(m * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (lam / (4 * T.L₁)) m])
  have hK' : 0 ≤ K' := by positivity
  calc |T.wcorr k j (O.F k j) n|
      ≤ (1 - γ)⁻¹ * (2 * (K' * (1 + D / T.L₁) ^ 4)) * 2 * Real.exp (-(lam * (D / (2 * T.L₁)))) +
          5 * (c * Real.exp (-(m * D))) := hmain
    _ = (1 - γ)⁻¹ * (2 * K') * 2 * ((1 + D / T.L₁) ^ 4 * Real.exp (-(2 * a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m * D)) := by rw [e1]; ring
    _ ≤ (1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a * Real.exp (-(a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m' * D)) := by
        gcongr
    _ = (1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a) * Real.exp (-(lam / (4 * T.L₁) * D)) +
          5 * c * Real.exp (-(m' * D)) := by rw [e2]; ring
    _ ≤ (1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a) * Real.exp (-(m' * D)) +
          5 * c * Real.exp (-(m' * D)) := by gcongr
    _ = ((1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a) + 5 * c) * Real.exp (-(m' * (n * T.a k))) := by
        ring

/-- **The blocked route, assembled** (route A without `SlabDecay` as a hypothesis): on a line of constant physics,
`H1Local ∧ LimitDprime ∧ ObsTransfer` for a reflection-respecting blocking give the mass gap of every continuum limit
point, the lattice-uniform gap, and reflection positivity of the limit. -/
theorem massGap_of_blockedRoute {T : Tuning} (hL : OnLCP T) (B : BlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf)
    (h2 : LimitDprime lam Vinf) (h3 : ObsTransfer T B) : MassGap T ∧ LatticeGap T ∧ LimitRP T :=
  assembly_routeA hL (slabDecay_of_blockedRoute B hlam h1 h2 h3)

/-- **The same with the concrete good blocking** (slice smearing with weight `w`, time decimation; dyadic resolution). -/
theorem massGap_of_goodBlocking {T : Tuning} (hL : OnLCP T) (w : ℝ) (nk : ℕ → ℕ) (hn : ∀ k, T.ℓ k = 2 ^ nk k)
    {lam : ℝ} (hlam : 0 < lam) {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j}
    (h1 : H1Local T (goodBlocking T w nk hn) lam Vk Vinf) (h2 : LimitDprime lam Vinf)
    (h3 : ObsTransfer T (goodBlocking T w nk hn)) : MassGap T ∧ LatticeGap T ∧ LimitRP T :=
  massGap_of_blockedRoute hL _ hlam h1 h2 h3

/-! ## `TorusDecay` from a level-uniform transfer -/

/-- **P5.2, level-uniform form (open; neither weaker nor stronger than `ObsTransfer` as stated).** As `ObsTransfer`, but
for every support bound `Vb` the approximating block observable `f` comes with a Dobrushin oscillation bound `v_f` whose
total over its coarse support is at most `2K (1 + D/L₁)⁴`, **uniformly in the level** (instead of a coarse support count
proportional to the fine support count). This is the form that averaged observables (a sum of `N` local terms divided by
`N`, oscillation `O(1/N)` per term) can satisfy as `N = Vb k` grows; a coarse support count cannot be level-uniform for
them. The rate `m` is one for all `Vb`. -/
def ObsTransferU (T : Tuning) (B : BlockingFamily T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ Vb : ℕ → ℕ, ∃ c K : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → A₀.card ≤ Vb k → B₀.card ≤ Vb k →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    ∃ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink 4 (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ 4) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U - f ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U - g ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(T.ym k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U ∂(T.ym k j)|
        ≤ c * Real.exp (-(m * D))

/-- **The blocked route with a level-uniform transfer gives `TorusDecay`** (workstream 4's level-uniform hypothesis): one
physical rate, one constant for all levels from some level on. -/
theorem torusDecay_of_blockedRouteU {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf)
    (h2 : LimitDprime lam Vinf) (h3 : ObsTransferU T B) : TorusDecay T.toV := by
  obtain ⟨γ, -, hγ1, k₀, hgap⟩ := blockGap_of_blockedRoute B hlam.le h1 h2
  obtain ⟨m, hm, htrU⟩ := h3
  have hL1 := T.L₁_pos
  set a := lam / 4
  have ha : 0 < a := by positivity
  set m' := min (lam / (4 * T.L₁)) m
  have hm' : 0 < m' := lt_min (by positivity) hm
  refine ⟨m', hm', fun s Vb => ?_⟩
  obtain ⟨c, K, hc, k₁, htr⟩ := htrU Vb
  set K' := |K|
  have hγ' : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.mpr (by linarith)
  refine ⟨max k₀ k₁, (1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a) + 5 * c, by positivity,
    fun k hk j O n hn => ?_⟩
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hk₁ : k₁ ≤ k := (le_max_right _ _).trans hk
  obtain ⟨hdA, hdB, hcA, hcB, hsep⟩ := slab_transfer_data T O hn
  have hak := T.a_pos k
  set D := (n : ℝ) * T.a k
  have hD : 0 ≤ D := by positivity
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, ⟨vf, hvf, hsv⟩, hsep', hEF, hEG, hdec⟩ :=
    htr k hk₁ j _ _ _ _ D ((O.meas k j).comp (measurable_tShift _))
      ((O.meas k j).comp measurePreserving_thetaConn.measurable) (fun U => O.bdd k j _) (fun U => O.bdd k j _)
      (gaugeInvariant_tShift (O.gauge k j) _) (gaugeInvariant_thetaConn (O.gauge k j)) hdA hdB hcA hcB hsep
  have hx : 0 ≤ D / T.L₁ := by positivity
  have hsv' : ∑ a ∈ A', vf a ≤ 2 * (K' * (1 + D / T.L₁) ^ 4) := by
    refine hsv.trans ?_
    have : K * (1 + D / T.L₁) ^ 4 ≤ K' * (1 + D / T.L₁) ^ 4 :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    linarith
  have hmain := wcorr_le_blocked T B O n (hgap k hk₀ j) hγ1 f g A' B' mf mg bf bg dfA dgB vf hvf hsv' hsep' hEF hEG
    hdec
  have hpoly := poly_exp_le ha hx
  have e1 : lam * (D / (2 * T.L₁)) = 2 * a * (D / T.L₁) := by simp only [a]; field_simp; ring
  have e2 : a * (D / T.L₁) = lam / (4 * T.L₁) * D := by simp only [a]; field_simp
  have hE1 : Real.exp (-(lam / (4 * T.L₁) * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (lam / (4 * T.L₁)) m])
  have hE2 : Real.exp (-(m * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (lam / (4 * T.L₁)) m])
  have hK' : 0 ≤ K' := abs_nonneg K
  show |T.wcorr k j (O.F k j) n| ≤ _
  calc |T.wcorr k j (O.F k j) n|
      ≤ (1 - γ)⁻¹ * (2 * (K' * (1 + D / T.L₁) ^ 4)) * 2 * Real.exp (-(lam * (D / (2 * T.L₁)))) +
          5 * (c * Real.exp (-(m * D))) := hmain
    _ = (1 - γ)⁻¹ * (2 * K') * 2 * ((1 + D / T.L₁) ^ 4 * Real.exp (-(2 * a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m * D)) := by rw [e1]; ring
    _ ≤ (1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a * Real.exp (-(a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m' * D)) := by
        gcongr
    _ = (1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a) * Real.exp (-(lam / (4 * T.L₁) * D)) +
          5 * c * Real.exp (-(m' * D)) := by rw [e2]; ring
    _ ≤ (1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a) * Real.exp (-(m' * D)) +
          5 * c * Real.exp (-(m' * D)) := by gcongr
    _ = ((1 - γ)⁻¹ * (2 * K') * 2 * (24 / a ^ 4 * Real.exp a) + 5 * c) * Real.exp (-(m' * (n * T.a k))) := by
        ring

/-- **Both orders of limits from the blocked route** with a level-uniform transfer (via workstream 4's
`bothOrders_of_torusDecay`): the gap of every continuum limit point, volume first then spacing (`MassGap`), and spacing
first at fixed physical volume then volume (`MassGapMF`, the OpenAI construction's order). -/
theorem bothOrders_of_blockedRouteU {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (B : BlockingFamily T) {lam : ℝ}
    (hlam : 0 < lam) {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf)
    (h2 : LimitDprime lam Vinf) (h3 : ObsTransferU T B) : MassGap T ∧ MassGapMF T.toV :=
  bothOrders_of_torusDecay ha (torusDecay_of_blockedRouteU B hlam h1 h2 h3)

end ProofPhase.RouteA
