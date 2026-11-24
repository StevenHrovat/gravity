/-
Proof phase, windowed OS reconstruction (os-windowed), module 2: the periodic-lattice gauge measure as windowed
reflection-positive data (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/os-windowed/NOTE.md`; pack `m1-tools/PACK-OSDATA.md`, route A.
-/

import ProofPhase.OS.Window
import ProofPhase.Objects
import ProofPhase.M1.UVTVReflect

/-!
# The torus measure as windowed reflection-positive data

On `(ℤ/Nℤ)^d`, `N` even, with any plaquette weight of class (Φ) (`PosWeight`, Wilson at every `β`) and the normalised
gauge measure `μ = gaugeMeasure n φ`:

* `bObs`: the bounded measurable observables;
* `torusWin`: `WinRP bObs` with `Q u v = ∫ u · (v ∘ Θ) dμ`, `τ u = u ∘ S_1`, and `P` the observables of the closed
  positive half. `symm` from `Θ`-invariance, `τ_symm` from `S_1`-invariance and `S_k Θ = Θ S_{-k}`, `pos` from the
  repository's site reflection positivity `ProofPhase.rp_gaugeMeasure`. Nothing else: no link reflection.
* `admissible_of_slab`: an observable of the time slab `[0, w]` is `K`-admissible when `K + w < N/2`.
* `H_sub_mean`: `H (h - E h) t = corr n φ h t`, the connected reflected correlation of the assembly.
* `torus_gap_approx` (**the finite-volume estimate**): for `|F| ≤ 1` and an approximant `g` (`|g| ≤ M`), both on the
  slab `[0, w]`, with `∫ (F∘Θ - g∘Θ)(F - g) dμ ≤ ε` and a decay bound `|corr g t| ≤ C e^{-λ t}` while it fits:
  `|corr F t| ≤ (2 + 2√(2ε) + ε + 2^{-r} C) e^{-λ t} + (2 + 2M) √ε` whenever `2^{r+1} t + 2w + 2 ≤ N`.
* `measurePreserving_thetaConn_gauge`, `approx_le_of_UVTV` (**the bridge to M1**): if `g` is a version of
  `E[F | 𝓗]`, the approximation error is at most M1's (B) term plus twice its (A) term
  (`M1.UVTV.os_split_reflection`).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OS

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n] [HasHaarProbability G] [(haarG G).IsInvInvariant]

/-! ### Bounded measurable observables -/

variable (G d N) in
/-- The bounded measurable observables of the gauge field. -/
def bObs : Submodule ℝ (GaugeConnection G d N → ℝ) where
  carrier := {u | Measurable u ∧ ∃ M, ∀ U, |u U| ≤ M}
  zero_mem' := ⟨measurable_const, 0, fun U => by simp⟩
  add_mem' := by
    rintro u v ⟨mu, Cu, hCu⟩ ⟨mv, Cv, hCv⟩
    exact ⟨mu.add mv, Cu + Cv, fun U => (abs_add_le _ _).trans (add_le_add (hCu U) (hCv U))⟩
  smul_mem' := by
    rintro c u ⟨mu, C, hC⟩
    refine ⟨mu.const_smul c, |c| * C, fun U => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC U) (abs_nonneg c)

/-- Package a bounded measurable function as an observable. -/
def mkObs (u : GaugeConnection G d N → ℝ) (hu : Measurable u) (hb : ∃ M, ∀ U, |u U| ≤ M) : bObs d N G :=
  ⟨u, hu, hb⟩

theorem integrable_obs_comp (μ : Measure (GaugeConnection G d N)) [IsFiniteMeasure μ] (u v : bObs d N G)
    {f g : GaugeConnection G d N → GaugeConnection G d N} (hf : Measurable f) (hg : Measurable g) :
    Integrable (fun U => (u : GaugeConnection G d N → ℝ) (f U) * (v : GaugeConnection G d N → ℝ) (g U)) μ := by
  obtain ⟨mu, Cu, hCu⟩ := u.2
  obtain ⟨mv, Cv, hCv⟩ := v.2
  refine Integrable.of_bound (C := Cu * Cv) ((mu.comp hf).mul (mv.comp hg)).aestronglyMeasurable
    (ae_of_all _ fun U => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hCu _) (hCv _) (abs_nonneg _) ((abs_nonneg _).trans (hCu (f U)))

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
  (hN : Even N) {φ : ℝ → ℝ} (hφ : PosWeight n φ)

/-! ### The OS form, the step, the positive half -/

include hc hU hφ in
/-- The OS form `Q u v = ∫ u · (v ∘ Θ) dμ`. -/
def torusQ : bObs d N G →ₗ[ℝ] bObs d N G →ₗ[ℝ] ℝ :=
  haveI := isProbabilityMeasure_gaugeMeasure (d := d) (N := N) hc hU hφ
  LinearMap.mk₂ ℝ (fun u v => ∫ U, (u : GaugeConnection G d N → ℝ) U * (v : GaugeConnection G d N → ℝ) (thetaConn U)
      ∂(gaugeMeasure n φ))
    (fun u₁ u₂ v => by
      simp only [Submodule.coe_add, Pi.add_apply, add_mul]
      exact integral_add (integrable_obs_comp _ u₁ v measurable_id measurePreserving_thetaConn.measurable)
        (integrable_obs_comp _ u₂ v measurable_id measurePreserving_thetaConn.measurable))
    (fun c u v => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul c _)
    (fun u v₁ v₂ => by
      simp only [Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_obs_comp _ u v₁ measurable_id measurePreserving_thetaConn.measurable)
        (integrable_obs_comp _ u v₂ measurable_id measurePreserving_thetaConn.measurable))
    (fun c u v => by
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
      exact integral_const_mul c _)

theorem torusQ_apply (u v : bObs d N G) :
    torusQ hc hU hφ u v = ∫ U, (u : GaugeConnection G d N → ℝ) U * (v : GaugeConnection G d N → ℝ) (thetaConn U)
      ∂(gaugeMeasure n φ) := rfl

/-- The time translation by one step, `u ↦ u ∘ S_1`. -/
def shiftObs : bObs d N G →ₗ[ℝ] bObs d N G where
  toFun u := ⟨fun U => (u : GaugeConnection G d N → ℝ) (tShift 1 U), u.2.1.comp (measurable_tShift 1), by
    obtain ⟨M, hM⟩ := u.2.2
    exact ⟨M, fun U => hM _⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem shiftObs_pow_coe (u : bObs d N G) (t : ℕ) :
    (((shiftObs ^ t) u : bObs d N G) : GaugeConnection G d N → ℝ) =
      fun U => (u : GaugeConnection G d N → ℝ) (tShift (t : ZMod N) U) := by
  induction t with
  | zero => funext U; simp [tShift_zero]
  | succ t ih =>
      rw [pow_succ', Module.End.mul_apply]
      funext U
      change (((shiftObs ^ t) u : bObs d N G) : GaugeConnection G d N → ℝ) (tShift 1 U) = _
      rw [ih]
      simp only [tShift_tShift]
      congr 2
      push_cast
      ring

variable (G d N) in
/-- The observables of the closed positive half. -/
def posObs : Submodule ℝ (bObs d N G) where
  carrier := {u | LinkDep (u : GaugeConnection G d N → ℝ) (posHalfLinks d N)}
  zero_mem' := fun U V _ => rfl
  add_mem' := by
    intro u v hu hv U V h
    simp only [Submodule.coe_add, Pi.add_apply]
    rw [hu U V h, hv U V h]
  smul_mem' := by
    intro c u hu U V h
    simp only [Submodule.coe_smul, Pi.smul_apply]
    rw [hu U V h]

include hc hU hφ in
theorem torusQ_symm (u v : bObs d N G) : torusQ hc hU hφ u v = torusQ hc hU hφ v u := by
  rw [torusQ_apply, torusQ_apply]
  have hm : Measurable fun U => (u : GaugeConnection G d N → ℝ) U * (v : GaugeConnection G d N → ℝ) (thetaConn U) :=
    u.2.1.mul (v.2.1.comp measurePreserving_thetaConn.measurable)
  rw [← integral_thetaConn hc hU hφ hm]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only [thetaConn_involutive U]
  ring

include hc hU hφ in
theorem torusQ_τ_symm (u v : bObs d N G) :
    torusQ hc hU hφ (shiftObs u) v = torusQ hc hU hφ u (shiftObs v) := by
  rw [torusQ_apply, torusQ_apply]
  set g : GaugeConnection G d N → ℝ := fun U =>
    (u : GaugeConnection G d N → ℝ) U * (v : GaugeConnection G d N → ℝ) (thetaConn (tShift (-1) U)) with hgdef
  have hm : Measurable g :=
    u.2.1.mul (v.2.1.comp (measurePreserving_thetaConn.measurable.comp (measurable_tShift _)))
  have h := integral_tShift hc hU hφ hm 1
  have e1 : (fun U => g (tShift 1 U)) = fun U => (u : GaugeConnection G d N → ℝ) (tShift 1 U) *
      (v : GaugeConnection G d N → ℝ) (thetaConn U) := by
    funext U
    simp only [hgdef, tShift_tShift, neg_add_cancel, tShift_zero]
  have e2 : g = fun U => (u : GaugeConnection G d N → ℝ) U *
      (v : GaugeConnection G d N → ℝ) (tShift 1 (thetaConn U)) := by
    funext U
    simp only [hgdef, tShift_thetaConn]
  rw [e1, e2] at h
  exact h

include hc hU hN hφ in
/-- **The periodic-lattice gauge measure as windowed reflection-positive data.** -/
def torusWin : WinRP (bObs d N G) where
  Q := torusQ hc hU hφ
  symm := torusQ_symm hc hU hφ
  τ := shiftObs
  τ_symm := torusQ_τ_symm hc hU hφ
  P := posObs d N G
  pos u hu := rp_gaugeMeasure hc hU hN hφ hu u.2.1 u.2.2

theorem torusWin_Q (u v : bObs d N G) :
    (torusWin hc hU hN hφ).Q u v = ∫ U, (u : GaugeConnection G d N → ℝ) U *
      (v : GaugeConnection G d N → ℝ) (thetaConn U) ∂(gaugeMeasure n φ) := rfl

theorem torusWin_pow_coe (u : bObs d N G) (t : ℕ) :
    ((((torusWin hc hU hN hφ).τ ^ t) u : bObs d N G) : GaugeConnection G d N → ℝ) =
      fun U => (u : GaugeConnection G d N → ℝ) (tShift (t : ZMod N) U) :=
  shiftObs_pow_coe u t

/-! ### Admissibility, bounds, the connected correlation -/

/-- An observable of the time slab `[0, w]` is `K`-admissible when `K + w < N/2`. -/
theorem admissible_of_slab {u : bObs d N G} {w : ℕ} (hu : LinkDep (u : GaugeConnection G d N → ℝ) (timeSlab 0 w)) {K : ℕ}
    (hK : K + w < N / 2) : (torusWin hc hU hN hφ).Adm K u := by
  intro i hi
  show LinkDep _ (posHalfLinks d N)
  rw [torusWin_pow_coe]
  exact linkDep_tShift_of_slab hu (by omega)

include hc hU hφ in
theorem abs_torusQ_le (u v : bObs d N G) {a b : ℝ} (ha : ∀ U, |(u : GaugeConnection G d N → ℝ) U| ≤ a)
    (hb : ∀ U, |(v : GaugeConnection G d N → ℝ) U| ≤ b) : |torusQ hc hU hφ u v| ≤ a * b := by
  have := isProbabilityMeasure_gaugeMeasure (d := d) (N := N) hc hU hφ
  rw [torusQ_apply]
  have := norm_integral_le_of_norm_le_const (μ := gaugeMeasure n φ)
    (f := fun U => (u : GaugeConnection G d N → ℝ) U * (v : GaugeConnection G d N → ℝ) (thetaConn U)) (C := a * b)
    (Eventually.of_forall fun U => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (ha U) (hb _) (abs_nonneg _) ((abs_nonneg _).trans (ha U)))
  simpa using this

/-- The centred observable `h - E h`. -/
def centred (h : GaugeConnection G d N → ℝ) (hh : BM h) (c : ℝ) : bObs d N G :=
  mkObs (fun U => h U - c) (hh.meas.sub_const c) (by
    obtain ⟨M, hM⟩ := hh.bdd
    exact ⟨M + |c|, fun U => (abs_sub _ _).trans (add_le_add (hM U) le_rfl)⟩)

theorem centred_coe (h : GaugeConnection G d N → ℝ) (hh : BM h) (c : ℝ) :
    ((centred h hh c : bObs d N G) : GaugeConnection G d N → ℝ) = fun U => h U - c := rfl

include hc hU hφ in
/-- **The reflected correlation of the centred observable is the assembly's connected correlation**:
`H (h - E h) t = corr n φ h t`. -/
theorem H_centred (h : GaugeConnection G d N → ℝ) (hh : BM h) (t : ℕ) :
    (torusWin hc hU hN hφ).H (centred h hh (∫ U, h U ∂(gaugeMeasure n φ))) t = corr n φ h t := by
  have := isProbabilityMeasure_gaugeMeasure (d := d) (N := N) hc hU hφ
  set μ := gaugeMeasure (d := d) (N := N) (G := G) n φ
  set c := ∫ U, h U ∂μ
  unfold WinRP.H
  rw [(torusWin hc hU hN hφ).symm, torusWin_Q, torusWin_pow_coe, centred_coe]
  have hS : BM (fun U => h (tShift (t : ZMod N) U)) := by
    obtain ⟨M, hM⟩ := hh.bdd
    exact ⟨hh.meas.comp (measurable_tShift _), ⟨M, fun U => hM _⟩⟩
  have hT : BM (fun U => h (thetaConn U)) := by
    obtain ⟨M, hM⟩ := hh.bdd
    exact ⟨hh.meas.comp measurePreserving_thetaConn.measurable, ⟨M, fun U => hM _⟩⟩
  have e1 : ∫ U, h (tShift (t : ZMod N) U) ∂μ = c := integral_tShift hc hU hφ hh.meas _
  have e2 : ∫ U, h (thetaConn U) ∂μ = c := integral_thetaConn hc hU hφ hh.meas
  have hc' := integral_centered_mul (μ := μ) (hS.integrable μ) (hT.integrable μ) ((hS.mul hT).integrable μ) c
  unfold corr
  simp only [μ] at hc' e1 e2 ⊢
  rw [hc', e1, e2]
  ring

/-! ### The finite-volume estimate -/

include hc hU hN hφ in
/-- **The windowed gap with an approximant, on the finite torus.** `F` with `|F| ≤ 1` and an approximant `g` with
`|g| ≤ M`, both on the time slab `[0, w]`; the OS distance `∫ (F∘Θ - g∘Θ)(F - g) dμ ≤ ε`; the approximant's connected
correlation decays, `|corr g t| ≤ C e^{-λ t}` while `2t + 2w + 2 ≤ N`. Then for `r ≥ 1` and `2^{r+1} t + 2w + 2 ≤ N`:
`|corr F t| ≤ (2 + 2√(2ε) + ε + 2^{-r} C) e^{-λ t} + (2 + 2M) √ε`. -/
theorem torus_gap_approx {F g : GaugeConnection G d N → ℝ} (hFm : Measurable F) (hF1 : ∀ U, |F U| ≤ 1)
    (hgm : Measurable g) {M : ℝ} (hg : ∀ U, |g U| ≤ M) {w : ℕ} (hFs : LinkDep F (timeSlab 0 w))
    (hgs : LinkDep g (timeSlab 0 w)) {ε : ℝ}
    (hε : ∫ U, (F (thetaConn U) - g (thetaConn U)) * (F U - g U) ∂(gaugeMeasure n φ) ≤ ε)
    {C lam : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ t : ℕ, 2 * t + 2 * w + 2 ≤ N → |corr n φ g t| ≤ C * Real.exp (-(lam * t)))
    {t r : ℕ} (hr : 1 ≤ r) (hNr : 2 ^ (r + 1) * t + 2 * w + 2 ≤ N) :
    |corr n φ F t| ≤ (2 + 2 * Real.sqrt (2 * ε) + ε + (1 / 2 : ℝ) ^ r * C) * Real.exp (-(lam * t)) +
      (2 + 2 * M) * Real.sqrt ε := by
  have := isProbabilityMeasure_gaugeMeasure (d := d) (N := N) hc hU hφ
  set μ := gaugeMeasure (d := d) (N := N) (G := G) n φ
  set R := torusWin (d := d) (N := N) hc hU hN hφ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hg (fun _ => 1))
  have hFb : BM F := ⟨hFm, 1, hF1⟩
  have hgb : BM g := ⟨hgm, M, hg⟩
  set cF := ∫ U, F U ∂μ
  set cg := ∫ U, g U ∂μ
  have hcF : |cF| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := F) (C := 1)
      (Eventually.of_forall fun U => by rw [Real.norm_eq_abs]; exact hF1 U)
    simpa using this
  have hcg : |cg| ≤ M := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := M)
      (Eventually.of_forall fun U => by rw [Real.norm_eq_abs]; exact hg U)
    simpa using this
  set xF := centred F hFb cF
  set xg := centred g hgb cg
  -- the window
  set K := 2 ^ (r - 1) * t with hK
  have hpow : 2 ^ (r + 1) * t = 4 * K := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [hK, Nat.add_sub_cancel, pow_succ]
    ring
  have hKw : K + w < N / 2 := by omega
  have hslab : ∀ (h : GaugeConnection G d N → ℝ) (c : ℝ), LinkDep h (timeSlab 0 w) →
      LinkDep (fun U => h U - c) (timeSlab 0 w) := by
    intro h c hh U V hUV
    simp only [hh U V hUV]
  have hAF : R.Adm K xF := admissible_of_slab hc hU hN hφ (hslab F cF hFs) hKw
  have hAg : R.Adm K xg := admissible_of_slab hc hU hN hφ (hslab g cg hgs) hKw
  -- the approximation error in the OS seminorm
  have hε' : R.Q (xF - xg) (xF - xg) ≤ ε := by
    set y : GaugeConnection G d N → ℝ := fun U => F U - g U
    have hyb : BM y := hFb.sub hgb
    have hyθ : BM (fun U => y (thetaConn U)) := by
      obtain ⟨B, hB⟩ := hyb.bdd
      exact ⟨hyb.meas.comp measurePreserving_thetaConn.measurable, ⟨B, fun U => hB _⟩⟩
    have ey : ∫ U, y U ∂μ = cF - cg := integral_sub (hFb.integrable μ) (hgb.integrable μ)
    have eyθ : ∫ U, y (thetaConn U) ∂μ = cF - cg := by rw [integral_thetaConn hc hU hφ hyb.meas, ey]
    have key := integral_centered_mul (μ := μ) (hyb.integrable μ) (hyθ.integrable μ)
      ((hyb.mul hyθ).integrable μ) (cF - cg)
    have e : R.Q (xF - xg) (xF - xg) = ∫ U, (y U - (cF - cg)) * (y (thetaConn U) - (cF - cg)) ∂μ := by
      rw [torusWin_Q]
      refine integral_congr_ae (ae_of_all _ fun U => ?_)
      simp only [Submodule.coe_sub, Pi.sub_apply, xF, xg, centred_coe, y]
      ring
    have hε2 : ∫ U, y U * y (thetaConn U) ∂μ ≤ ε := by
      refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun U => ?_))) hε
      simp only [y]; ring
    rw [e, key, ey, eyθ]
    nlinarith [sq_nonneg (cF - cg)]
  have hε0 : 0 ≤ ε := (R.pos _ (hAF.sub R hAg).mem).trans hε'
  -- bounds for the translates
  have hxF2 : ∀ U, |((R.τ ^ t) xF : GaugeConnection G d N → ℝ) U| ≤ 2 := by
    intro U
    rw [torusWin_pow_coe, centred_coe]
    exact (abs_sub _ _).trans (by linarith [hF1 (tShift (t : ZMod N) U)])
  have hxg2 : ∀ U, |((R.τ ^ t) xg : GaugeConnection G d N → ℝ) U| ≤ 2 * M := by
    intro U
    rw [torusWin_pow_coe, centred_coe]
    exact (abs_sub _ _).trans (by linarith [hg (tShift (t : ZMod N) U)])
  have hBF : R.Q ((R.τ ^ t) xF) ((R.τ ^ t) xF) ≤ 2 * 2 :=
    (le_abs_self _).trans (abs_torusQ_le hc hU hφ _ _ hxF2 hxF2)
  have hBf : R.Q ((R.τ ^ t) xg) ((R.τ ^ t) xg) ≤ (2 * M) * (2 * M) :=
    (le_abs_self _).trans (abs_torusQ_le hc hU hφ _ _ hxg2 hxg2)
  -- the approximant's decay at time `2^r t`
  have hdec' : |R.H xg (2 ^ r * t)| ≤ C * Real.exp (-(lam * (2 ^ r * t : ℕ))) := by
    rw [H_centred hc hU hN hφ g hgb]
    exact hdec _ (by rw [show 2 * (2 ^ r * t) = 2 ^ (r + 1) * t by ring]; omega)
  have hmain := R.win_gap_approx hAF hAg hr le_rfl hε' hBF hBf hC hdec'
  rw [H_centred hc hU hN hφ F hFb] at hmain
  -- `Q xF xF = corr F 0 ∈ [0, 2]`
  have hQF : R.Q xF xF = corr n φ F 0 := by
    rw [← R.H_zero, H_centred hc hU hN hφ F hFb]
  have hQF0 : 0 ≤ R.Q xF xF := R.pos _ hAF.mem
  have hQF2 : R.Q xF xF ≤ 2 := by
    rw [hQF]; exact (le_abs_self _).trans (abs_corr_le_two hc hU hφ hFm hF1 0)
  have hs1 : Real.sqrt (R.Q xF xF * ε) ≤ Real.sqrt (2 * ε) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hQF2 hε0)
  have hs2 : Real.sqrt (ε * (2 * 2)) = 2 * Real.sqrt ε := by
    rw [Real.sqrt_mul hε0, show (2 : ℝ) * 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; ring
  have hs3 : Real.sqrt ((2 * M) * (2 * M) * ε) = 2 * M * Real.sqrt ε := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]
  rw [hs2, hs3] at hmain
  have hE := (Real.exp_pos (-(lam * t))).le
  refine hmain.trans ?_
  have : (R.Q xF xF + 2 * Real.sqrt (R.Q xF xF * ε) + ε + (1 / 2 : ℝ) ^ r * C) * Real.exp (-(lam * t)) ≤
      (2 + 2 * Real.sqrt (2 * ε) + ε + (1 / 2 : ℝ) ^ r * C) * Real.exp (-(lam * t)) :=
    mul_le_mul_of_nonneg_right (by linarith) hE
  nlinarith

/-! ### The bridge to M1's split -/

include hc hU hφ in
/-- `Θ` preserves the normalised gauge measure. -/
theorem measurePreserving_thetaConn_gauge :
    MeasurePreserving (thetaConn (G := G) (d := d) (N := N)) (gaugeMeasure n φ) (gaugeMeasure n φ) := by
  have := isProbabilityMeasure_gaugeMeasure (d := d) (N := N) hc hU hφ
  have hm : Measurable (thetaConn (G := G) (d := d) (N := N)) := measurePreserving_thetaConn.measurable
  refine ⟨hm, ?_⟩
  ext A hA
  rw [Measure.map_apply hm hA]
  have h := integral_thetaConn hc hU hφ (F := A.indicator (1 : GaugeConnection G d N → ℝ))
    (measurable_one.indicator hA)
  have e : (fun U => A.indicator (1 : GaugeConnection G d N → ℝ) (thetaConn U)) =
      (thetaConn ⁻¹' A).indicator 1 := by
    funext U
    simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
  rw [e, integral_indicator_one (hm hA), integral_indicator_one hA] at h
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h

include hc hU hφ in
/-- **M1's split bounds the approximation error.** If `g` is a version of `E[F | 𝓗_ℓ]` and `𝓕_ℓ` contains `𝓗_ℓ` and
`Θ⁻¹𝓗_ℓ`, then `∫ (F∘Θ - g∘Θ)(F - g) dμ ≤ b_B + 2 b_A`, with M1's (B) term
`E|ccov 𝓕_ℓ (F∘Θ) F| ≤ b_B` and (A) term `E|E[F∘Θ | 𝓕_ℓ] - E[F∘Θ | Θ⁻¹𝓗_ℓ]| ≤ b_A`. -/
theorem approx_le_of_UVTV (𝓕s 𝓗s : ℕ → MeasurableSpace (GaugeConnection G d N)) (ℓ : ℕ)
    (hF𝓕 : 𝓕s ℓ ≤ MeasurableSpace.pi) (hH : 𝓗s ℓ ≤ MeasurableSpace.pi) (hH𝓕 : 𝓗s ℓ ≤ 𝓕s ℓ)
    (hθH : (𝓗s ℓ).comap thetaConn ≤ 𝓕s ℓ) {F g : GaugeConnection G d N → ℝ} (hFm : Measurable F)
    (hF1 : ∀ U, |F U| ≤ 1) (hg : g =ᵐ[gaugeMeasure n φ] (gaugeMeasure n φ)[F|𝓗s ℓ]) {bA bB : ℝ}
    (hB : ∫ U, |M1.UVTV.ccov (gaugeMeasure n φ) (𝓕s ℓ) (F ∘ thetaConn) F U| ∂(gaugeMeasure n φ) ≤ bB)
    (hA : ∫ U, |(gaugeMeasure n φ)[F ∘ thetaConn|𝓕s ℓ] U -
      (gaugeMeasure n φ)[F ∘ thetaConn|(𝓗s ℓ).comap thetaConn] U| ∂(gaugeMeasure n φ) ≤ bA) :
    ∫ U, (F (thetaConn U) - g (thetaConn U)) * (F U - g U) ∂(gaugeMeasure n φ) ≤ bB + 2 * bA := by
  have := isProbabilityMeasure_gaugeMeasure (d := d) (N := N) hc hU hφ
  have hθ := measurePreserving_thetaConn_gauge (d := d) (N := N) hc hU hφ
  have hsplit := M1.UVTV.os_split_reflection hθ 𝓕s 𝓗s ℓ hF𝓕 hH hH𝓕 hθH hFm.aestronglyMeasurable
    (ae_of_all _ hF1)
  have hgθ := hθ.quasiMeasurePreserving.ae_eq_comp hg
  have e : ∫ U, (F (thetaConn U) - g (thetaConn U)) * (F U - g U) ∂(gaugeMeasure n φ) =
      ∫ U, (F (thetaConn U) - (gaugeMeasure n φ)[F|𝓗s ℓ] (thetaConn U)) *
        (F U - (gaugeMeasure n φ)[F|𝓗s ℓ] U) ∂(gaugeMeasure n φ) := by
    refine integral_congr_ae ?_
    filter_upwards [hg, hgθ] with U h1 h2
    simp only [Function.comp_apply] at h2
    rw [h1, h2]
  rw [e]
  exact (le_abs_self _).trans (hsplit.trans (add_le_add hB (by linarith)))

end ProofPhase.OS
