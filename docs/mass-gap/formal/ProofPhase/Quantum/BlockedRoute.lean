/-
Proof phase (round 5), workstream 3: the blocked route's last link (blueprint P7.4) and a genuine link metric
(2026-11-22). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/r3-robust/NOTE.md` §6 (law of total covariance);
`docs/mass-gap/weak-coupling/proof-phase/ws3-quantum/NOTE.md` (this workstream).
-/

import ProofPhase.Assembly

/-!
# P7.4: `H1Local ∧ LimitDprime ∧ ObsTransfer ⇒ SlabDecay`, proved

`ProofPhase.Assembly` proved `blockGap_of_blockedRoute` (decay of block observables `f ∘ Φ` of the SU(2) Wilson measure,
uniform in the level and the volume) and left the last link, from block observables to the fine slab correlations of
`SlabDecay`, on paper. It is proved here.

**`slabDecay_of_blockedRoute` (substantive).** For a tuning `T`, a blocking family `B`, `λ > 0`: `H1Local T B λ Vk Vinf`,
`LimitDprime λ Vinf` and `ObsTransfer T B` imply `SlabDecay T`, with the physical rate `min(m, λ/(4L₁))` (`m` the rate of
`ObsTransfer`). Proof, for a slab observable `F` at level `k`, torus `j`, lattice time `n` (`2n + 2⌈s/a⌉ + 2 ≤ N`):
1. `F ∘ S_n` and `F ∘ Θ` are measurable, bounded by one, **gauge invariant** (`gaugeInvariant_comp_tShift`,
   `gaugeInvariant_comp_thetaConn`: translation and reflection commute with gauge transformations up to a relabelled
   transformation), and depend on the translated and the mirrored copies of `supp ∩ slab` (at most `V k` links each),
   which are at link distance `≥ n` (`OneScale.CubeChain.sep_shift_mirror`); so `ObsTransfer` applies with physical
   distance `D = n a_k` and gives coarse observables `f`, `g`.
2. **Law of total covariance** (`abs_cov_sub_le_condExp`, any probability space, any sub-σ-algebra):
   `|Cov(F', G') − Cov(f ∘ Φ, g ∘ Φ)| ≤ 5 c e^{-mD}` from the three estimates of `ObsTransfer`.
3. `blockGap_of_blockedRoute` bounds `Cov(f ∘ Φ, g ∘ Φ)` by `4 (1 − γ)⁻¹ |A'| e^{-λD/(2L₁)}`, and `|A'| ≤ |K| (V k + 1)
   (1 + D/L₁)⁴`; the polynomial is absorbed by half the exponential (`poly4_exp_bound`).
The constant depends on the level only through the support bound `V k` (allowed by `SlabDecay`).

Consequences: `openPieces_of_blockedRoute` (the blocked route is a proved sufficient condition for route A's field, so
`OpenPieces` holds; since cycle 2 the crossover lists the blocked route itself, second disjunct), and
`assembly_blockedRoute`.

**Why not `TorusDecay`** (workstream 4's level-uniform form): `ObsTransfer` bounds the number of coarse links of `f` by
`K (|A₀| + 1)(1 + D/L₁)⁴`, with `|A₀|` the number of **fine** links of the observable; for `SlabObs` families `|A₀| ≤ V k`
may grow with the level, so the constant does too. With the coarse support counted in L₁ cells (a physical size) the
same proof would give a level-uniform constant for observables of bounded physical size; `TorusDecay` quantifies over
all support bounds `V`, which this route cannot give.

**The link metric (review finding 5).** `linkDist` (`ℓ^∞` cyclic distance of base sites) is a pseudometric, not a metric:
distinct links at one site are at distance `0` (`linkDist_not_definite`). The round-3 theorems need only `d(x, x) = 0`
and the triangle inequality, so they are correct as stated; requiring a metric would only weaken them. A genuine metric
is `linkMetric = linkDist + [e ≠ e']` (`linkMetric_self`, `linkMetric_symm`, `linkMetric_triangle`,
`eq_of_linkMetric_eq_zero`), and the block decay holds in it at the cost of a factor `e^{λ}` (`blockGap_linkMetric`).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift OneScale.CubeChain Positivity

open scoped Classical NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Quantum

/-! ## Gauge invariance of translated and reflected observables -/

section GaugeCov

variable {G : Type*} [Group G] {d N : ℕ} [NeZero d]

theorem tShift_gaugeTransform (j : ZMod N) (g : GaugeTransform G d N) (U : GaugeConnection G d N) :
    tShift j (gaugeTransformConnection g U) = gaugeTransformConnection (fun x => g (shiftSite j x)) (tShift j U) := by
  funext l
  simp only [tShift, gaugeTransformConnection, shiftLink, LatticeLink.target, shiftSite_siteShift]

theorem thetaConn_gaugeTransform (g : GaugeTransform G d N) (U : GaugeConnection G d N) :
    thetaConn (gaugeTransformConnection g U) = gaugeTransformConnection (fun x => g (reflSite x)) (thetaConn U) := by
  funext l
  rcases l with ⟨x, μ⟩
  by_cases hμ : μ = 0
  · subst hμ
    simp only [thetaConn, mirrorLink, ↓reduceIte, gaugeTransformConnection, LatticeLink.target,
      siteShift_tflipSite_zero, reflSite_siteShift_zero, mul_inv_rev, inv_inv, mul_assoc]
  · simp only [thetaConn, mirrorLink, hμ, ↓reduceIte, gaugeTransformConnection, LatticeLink.target,
      reflSite_siteShift x hμ]

theorem gaugeInvariant_comp_tShift {F : GaugeConnection G d N → ℝ} (hF : GaugeInvariant F) (j : ZMod N) :
    GaugeInvariant (fun U => F (tShift j U)) := fun g U => by
  show F (tShift j (gaugeTransformConnection g U)) = F (tShift j U)
  rw [tShift_gaugeTransform]; exact hF _ _

theorem gaugeInvariant_comp_thetaConn {F : GaugeConnection G d N → ℝ} (hF : GaugeInvariant F) :
    GaugeInvariant (fun U => F (thetaConn U)) := fun g U => by
  show F (thetaConn (gaugeTransformConnection g U)) = F (thetaConn U)
  rw [thetaConn_gaugeTransform]; exact hF _ _

end GaugeCov

/-- A function depending only on `A` and only on `S` depends only on `S ∩ A`. -/
theorem depOn_filter {ι S : Type*} [DecidableEq ι] {F : (ι → S) → ℝ} {A S' : Finset ι} (hA : DepOn F A) (hS : DepOn F S') :
    DepOn F (S'.filter (· ∈ A)) := by
  intro σ σ' h
  set τ : ι → S := fun i => if i ∈ A then σ i else σ' i
  have h1 : F σ = F τ := hA _ _ fun i hi => by simp [τ, hi]
  have h2 : F τ = F σ' := hS _ _ fun i hi => by
    by_cases hiA : i ∈ A
    · simp only [τ, hiA, ↓reduceIte]; exact h i (mem_filter.2 ⟨hi, hiA⟩)
    · simp [τ, hiA]
  rw [h1, h2]

theorem depOn_tShift_image {G : Type*} [Group G] {N : ℕ} {F : GaugeConnection G 4 N → ℝ}
    {S : Finset (LatticeLink 4 N)} (h : DepOn F S) (j : ZMod N) :
    DepOn (fun U => F (tShift j U)) (S.image (shiftLink j)) := by
  intro U V hUV
  apply h
  intro l hl
  exact hUV _ (mem_image_of_mem _ hl)

theorem depOn_theta_image {G : Type*} [Group G] {N : ℕ} {F : GaugeConnection G 4 N → ℝ}
    {S : Finset (LatticeLink 4 N)} (h : DepOn F S) :
    DepOn (fun U => F (thetaConn U)) (S.image mirrorLink) := by
  intro U V hUV
  apply h
  intro l hl
  have := hUV _ (mem_image_of_mem _ hl)
  simp only [thetaConn, this]

/-! ## The law of total covariance with approximate conditional expectations -/

theorem abs_cov_sub_le_condExp {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F G f g : Ω → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hF1 : ∀ x, |F x| ≤ 1) (hG1 : ∀ x, |G x| ≤ 1) (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ x, |f x| ≤ 1)
    (hg1 : ∀ x, |g x| ≤ 1) {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {δ : ℝ} (hqf : ∫ x, |μ[F|m] x - f x| ∂μ ≤ δ) (hqg : ∫ x, |μ[G|m] x - g x| ∂μ ≤ δ)
    (hdec : |∫ x, F x * G x ∂μ - ∫ x, μ[F|m] x * μ[G|m] x ∂μ| ≤ δ) :
    |(∫ x, F x * G x ∂μ - (∫ x, F x ∂μ) * ∫ x, G x ∂μ) -
        (∫ x, f x * g x ∂μ - (∫ x, f x ∂μ) * ∫ x, g x ∂μ)| ≤ 5 * δ := by
  set a := μ[F|m]
  set b := μ[G|m]
  have bnd : ∀ {h : Ω → ℝ}, Measurable[mΩ] h → (∀ x, |h x| ≤ 1) → Integrable h μ := fun hm' h1 =>
    Integrable.of_bound hm'.aestronglyMeasurable 1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact h1 x)
  have ha_sm : AEStronglyMeasurable[mΩ] a μ := (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  have hb_sm : AEStronglyMeasurable[mΩ] b μ := (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  have ha1 : ∀ᵐ x ∂μ, |a x| ≤ 1 := by
    have := ae_bdd_condExp_of_ae_bdd (m := m) (μ := μ) (f := F) (R := (1 : ℝ≥0))
      (Eventually.of_forall fun x => by simpa using hF1 x)
    simpa using this
  have hb1 : ∀ᵐ x ∂μ, |b x| ≤ 1 := by
    have := ae_bdd_condExp_of_ae_bdd (m := m) (μ := μ) (f := G) (R := (1 : ℝ≥0))
      (Eventually.of_forall fun x => by simpa using hG1 x)
    simpa using this
  have ia : Integrable a μ := integrable_condExp
  have ib : Integrable b μ := integrable_condExp
  have iab : Integrable (fun x => a x * b x) μ :=
    Integrable.of_bound (ha_sm.mul hb_sm) 1 (by
      filter_upwards [ha1, hb1] with x h1 h2
      rw [Real.norm_eq_abs, abs_mul]; nlinarith [abs_nonneg (a x), abs_nonneg (b x)])
  have ifg : Integrable (fun x => f x * g x) μ :=
    bnd (hf.mul hg) fun x => by rw [abs_mul]; nlinarith [abs_nonneg (f x), abs_nonneg (g x), hf1 x, hg1 x]
  have iF := bnd hF hF1
  have iG := bnd hG hG1
  have i_f := bnd hf hf1
  have i_g := bnd hg hg1
  -- (i) the products
  have k1 : |∫ x, a x * b x ∂μ - ∫ x, f x * g x ∂μ| ≤ 2 * δ := by
    rw [← integral_sub iab ifg]
    refine (abs_integral_le_integral_abs).trans ?_
    have hpt : ∀ᵐ x ∂μ, |a x * b x - f x * g x| ≤ |a x - f x| + |b x - g x| := by
      filter_upwards [hb1] with x hbx
      have e : a x * b x - f x * g x = (a x - f x) * b x + f x * (b x - g x) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      have h1 : |a x - f x| * |b x| ≤ |a x - f x| := by nlinarith [abs_nonneg (a x - f x), abs_nonneg (b x)]
      have h2 : |f x| * |b x - g x| ≤ |b x - g x| := by nlinarith [abs_nonneg (b x - g x), abs_nonneg (f x), hf1 x]
      linarith
    have iA : Integrable (fun x => |a x - f x|) μ := (ia.sub i_f).abs
    have iB : Integrable (fun x => |b x - g x|) μ := (ib.sub i_g).abs
    calc ∫ x, |a x * b x - f x * g x| ∂μ ≤ ∫ x, (|a x - f x| + |b x - g x|) ∂μ :=
          integral_mono_ae (iab.sub ifg).abs (iA.add iB) hpt
      _ = ∫ x, |a x - f x| ∂μ + ∫ x, |b x - g x| ∂μ := integral_add iA iB
      _ ≤ 2 * δ := by linarith
  -- (ii) the means
  have mean : ∀ {H h : Ω → ℝ}, Integrable h μ → ∫ x, |μ[H|m] x - h x| ∂μ ≤ δ →
      |∫ x, H x ∂μ - ∫ x, h x ∂μ| ≤ δ := by
    intro H h ih hq
    rw [← integral_condExp hm, ← integral_sub integrable_condExp ih]
    exact (abs_integral_le_integral_abs).trans hq
  have kF := mean i_f hqf
  have kG := mean i_g hqg
  have hEG : |∫ x, G x ∂μ| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := G) (C := 1)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hG1 x)
    simpa using this
  have hEf : |∫ x, f x ∂μ| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := 1)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hf1 x)
    simpa using this
  generalize ∫ x, F x * G x ∂μ = P at hdec ⊢
  generalize ∫ x, a x * b x ∂μ = Pab at hdec k1
  generalize ∫ x, f x * g x ∂μ = Pfg at k1 ⊢
  generalize ∫ x, F x ∂μ = EF at kF ⊢
  generalize ∫ x, G x ∂μ = EG at kG hEG ⊢
  generalize ∫ x, f x ∂μ = Ef at kF hEf ⊢
  generalize ∫ x, g x ∂μ = Eg at kG ⊢
  have p1 : |(EF - Ef) * EG| ≤ δ := by
    rw [abs_mul]; nlinarith [abs_nonneg (EF - Ef), abs_nonneg EG]
  have p2 : |Ef * (EG - Eg)| ≤ δ := by
    rw [abs_mul]; nlinarith [abs_nonneg (EG - Eg), abs_nonneg Ef]
  have e : P - EF * EG - (Pfg - Ef * Eg) = (P - Pab) + (Pab - Pfg) - ((EF - Ef) * EG + Ef * (EG - Eg)) := by ring
  rw [e]
  have q1 := abs_sub (P - Pab + (Pab - Pfg)) ((EF - Ef) * EG + Ef * (EG - Eg))
  have q2 := abs_add_le (P - Pab) (Pab - Pfg)
  have q3 := abs_add_le ((EF - Ef) * EG) (Ef * (EG - Eg))
  linarith

/-! ## Polynomial times exponential -/

theorem poly4_exp_bound {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ 4 * Real.exp (-(r * x)) ≤ C := by
  refine ⟨24 * Real.exp r / r ^ 4, by positivity, fun x hx => ?_⟩
  have h := Real.pow_div_factorial_le_exp (x := r * (1 + x)) (by positivity) 4
  have h24 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24, mul_pow, div_le_iff₀ (by norm_num : (0 : ℝ) < 24)] at h
  have hsplit : Real.exp (r * (1 + x)) = Real.exp r * Real.exp (r * x) := by rw [← Real.exp_add]; ring_nf
  have hinv : Real.exp (r * x) * Real.exp (-(r * x)) = 1 := by rw [← Real.exp_add]; simp
  rw [hsplit] at h
  rw [le_div_iff₀ (by positivity)]
  have he := Real.exp_pos (-(r * x))
  calc (1 + x) ^ 4 * Real.exp (-(r * x)) * r ^ 4 = (r ^ 4 * (1 + x) ^ 4) * Real.exp (-(r * x)) := by ring
    _ ≤ (Real.exp r * Real.exp (r * x) * 24) * Real.exp (-(r * x)) := mul_le_mul_of_nonneg_right h he.le
    _ = 24 * Real.exp r * (Real.exp (r * x) * Real.exp (-(r * x))) := by ring
    _ = 24 * Real.exp r := by rw [hinv, mul_one]

/-! ## P7.4 -/

theorem ym_prob (T : Tuning) (k j : ℕ) : IsProbabilityMeasure (T.ym k j) :=
  isProbabilityMeasure_gaugeMeasure (d := 4) (N := T.side k j) continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (posWeight_wilson 2 (T.β k))

/-- **P7.4, the blocked route's last link (proved).** `H1Local ∧ LimitDprime ∧ ObsTransfer ⇒ SlabDecay` (for `λ > 0`). -/
theorem slabDecay_of_blockedRoute {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf)
    (h2 : LimitDprime lam Vinf) (h3 : ObsTransfer T B) : SlabDecay T := by
  obtain ⟨γ, hγ0, hγ1, k₁, hblock⟩ := blockGap_of_blockedRoute B hlam.le h1 h2
  obtain ⟨c, m, hc, hm, K, k₂, hobs⟩ := h3
  have hL₁ := T.L₁_pos
  set β := lam / (4 * T.L₁) with hβdef
  have hβ : 0 < β := div_pos hlam (by linarith)
  obtain ⟨Cp, hCp0, hCp⟩ := poly4_exp_bound (r := lam / 4) (by linarith)
  refine ⟨min m β, lt_min hm hβ, fun s Vb => ⟨max k₁ k₂, fun k hk => ?_⟩⟩
  have hQ : 0 ≤ (1 - γ)⁻¹ := (inv_pos.2 (by linarith)).le
  refine ⟨4 * (1 - γ)⁻¹ * |K| * ((Vb k : ℝ) + 1) * Cp + 5 * c, by positivity, ?_⟩
  intro j O n hn
  have hak := T.a_pos k
  -- the observables
  set N := T.side k j
  set t := T.thick k s
  set F := O.F k j
  set S0 := (O.supp k j).filter (· ∈ timeSlab (d := 4) (N := N) 0 t)
  have hFS0 : DepOn F S0 := depOn_filter (O.slab k j) (O.dep k j)
  have hS0slab : ∀ l ∈ S0, l ∈ timeSlab (d := 4) (N := N) 0 t := fun l hl => (mem_filter.1 hl).2
  have hF₁A := depOn_tShift_image hFS0 (n : ZMod N)
  have hG₁B := depOn_theta_image hFS0
  set D : ℝ := T.a k * n
  have hD0 : 0 ≤ D := by positivity
  have hsep : ∀ e ∈ S0.image (shiftLink (n : ZMod N)), ∀ e' ∈ S0.image mirrorLink, D ≤ T.a k * linkDist e e' := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := mem_image.1 he'
    exact mul_le_mul_of_nonneg_left (sep_shift_mirror hn (hS0slab l hl) (hS0slab l' hl')) hak.le
  have hA₀ : (S0.image (shiftLink (n : ZMod N))).card ≤ Vb k :=
    (card_image_le.trans (card_filter_le _ _)).trans (O.supp_card k j)
  have hF₁m : Measurable (fun U => F (tShift (n : ZMod N) U)) := (O.meas k j).comp (measurable_tShift _)
  have hG₁m : Measurable (fun U : GaugeConnection SU2 4 N => F (thetaConn U)) := (O.meas k j).comp measurePreserving_thetaConn.measurable
  obtain ⟨f, g, A', B', hfm, hgm, hf1, hg1, hfA, hgB, hA', -, hsep', hqf, hqg, hdec⟩ :=
    hobs k (le_of_max_le_right hk) j _ _ _ _ D hF₁m hG₁m (fun U => O.bdd k j _) (fun U => O.bdd k j _)
      (gaugeInvariant_comp_tShift (O.gauge k j) _) (gaugeInvariant_comp_thetaConn (O.gauge k j)) hF₁A hG₁B hsep
  -- the block observables
  set vf : LatticeLink 4 (coarseSide j) → ℝ := fun l => if l ∈ A' then 2 else 0
  have hvf : OscBound f vf := by
    intro σ x s'
    by_cases hx : x ∈ A'
    · simp only [vf, hx, ↓reduceIte]
      have := hf1 σ; have := hf1 (Function.update σ x s')
      exact (abs_sub _ _).trans (by linarith)
    · simp only [vf, hx, ↓reduceIte]
      have : f σ = f (Function.update σ x s') :=
        hfA _ _ fun i hi => by rw [Function.update_of_ne (by rintro rfl; exact hx hi)]
      rw [this, sub_self, abs_zero]
  have hvg : OscBound g (fun _ => 2) := fun σ x s' => by
    have := hg1 σ; have := hg1 (Function.update σ x s')
    exact (abs_sub _ _).trans (by linarith)
  have hR : ∀ x ∈ A', ∀ y ∈ B', D / (2 * T.L₁) ≤ linkDist x y := fun x hx y hy => by
    rw [div_le_iff₀ (by positivity)]; have := hsep' x hx y hy; linarith
  have hblk := hblock k (le_of_max_le_left hk) j f g A' B' vf 2 (D / (2 * T.L₁)) ⟨hfm, 1, hf1⟩ ⟨hgm, 1, hg1⟩ hfA
    hgB hvf (by norm_num) hvg hR
  have hsum : ∑ a ∈ A', vf a = 2 * A'.card := by
    simp only [vf]; rw [sum_ite_mem, inter_self, sum_const, nsmul_eq_mul]; ring
  rw [hsum] at hblk
  -- the law of total covariance
  have hmB : MeasurableSpace.comap (B k j).B inferInstance ≤ (inferInstance : MeasurableSpace _) :=
    (B k j).meas.comap_le
  have := ym_prob T k j
  have htot : |(∫ U, F (tShift (n : ZMod N) U) * F (thetaConn U) ∂(T.ym k j) -
        (∫ U, F (tShift (n : ZMod N) U) ∂(T.ym k j)) * ∫ U, F (thetaConn U) ∂(T.ym k j)) -
      (∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
        (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j))| ≤
      5 * (c * Real.exp (-(m * D))) := abs_cov_sub_le_condExp (T.ym k j) hF₁m hG₁m (fun U => O.bdd k j _) (fun U => O.bdd k j _)
    (hfm.comp (B k j).meas) (hgm.comp (B k j).meas) (fun U => hf1 _) (fun U => hg1 _) hmB hqf hqg hdec
  have ew : T.wcorr k j (O.F k j) n =
      ∫ U, F (tShift (n : ZMod N) U) * F (thetaConn U) ∂(T.ym k j) -
        (∫ U, F (tShift (n : ZMod N) U) ∂(T.ym k j)) * ∫ U, F (thetaConn U) ∂(T.ym k j) := rfl
  rw [ew]
  -- the arithmetic
  set x : ℝ := D / T.L₁
  have hx0 : 0 ≤ x := by positivity
  have hX : (A'.card : ℝ) ≤ |K| * ((Vb k : ℝ) + 1) * (1 + x) ^ 4 := by
    refine hA'.trans ?_
    have hp : 0 ≤ (1 + x) ^ 4 := by positivity
    have hc0 : ((S0.image (shiftLink (n : ZMod N))).card : ℝ) + 1 ≤ (Vb k : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hA₀ 1
    calc K * (((S0.image (shiftLink (n : ZMod N))).card : ℝ) + 1) * (1 + D / T.L₁) ^ 4 ≤ |K| * (((S0.image (shiftLink (n : ZMod N))).card : ℝ) + 1) * (1 + x) ^ 4 := by
          gcongr; exact le_abs_self K
      _ ≤ |K| * ((Vb k : ℝ) + 1) * (1 + x) ^ 4 := by gcongr
  set E := Real.exp (-(min m β * (n * T.a k)))
  have hE1 : Real.exp (-(lam * (D / (2 * T.L₁)))) =
      Real.exp (-(lam / 4 * x)) * Real.exp (-(β * (n * T.a k))) := by
    rw [← Real.exp_add]; congr 1; simp only [x, D, β]; field_simp; ring
  have hβE : Real.exp (-(β * (n * T.a k))) ≤ E :=
    Real.exp_le_exp.2 (by have := min_le_right m β; nlinarith [mul_nonneg (Nat.cast_nonneg n) hak.le])
  have hmE : Real.exp (-(m * D)) ≤ E :=
    Real.exp_le_exp.2 (by
      have := min_le_left m β
      have : D = n * T.a k := by simp only [D]; ring
      rw [this]; nlinarith [mul_nonneg (Nat.cast_nonneg n) hak.le])
  have hpoly : (1 + x) ^ 4 * Real.exp (-(lam * (D / (2 * T.L₁)))) ≤ Cp * E := by
    rw [hE1, ← mul_assoc]
    exact mul_le_mul (hCp x hx0) hβE (Real.exp_pos _).le hCp0
  have hcov : |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
      (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
        4 * (1 - γ)⁻¹ * |K| * ((Vb k : ℝ) + 1) * Cp * E := by
    refine hblk.trans ?_
    have hK0 : 0 ≤ |K| * ((Vb k : ℝ) + 1) := by positivity
    calc (1 - γ)⁻¹ * (2 * (A'.card : ℝ)) * 2 * Real.exp (-(lam * (D / (2 * T.L₁))))
        = 4 * (1 - γ)⁻¹ * ((A'.card : ℝ) * Real.exp (-(lam * (D / (2 * T.L₁))))) := by ring
      _ ≤ 4 * (1 - γ)⁻¹ * ((|K| * ((Vb k : ℝ) + 1) * (1 + x) ^ 4) * Real.exp (-(lam * (D / (2 * T.L₁))))) := by
          gcongr
      _ = 4 * (1 - γ)⁻¹ * (|K| * ((Vb k : ℝ) + 1)) * ((1 + x) ^ 4 * Real.exp (-(lam * (D / (2 * T.L₁))))) := by
          ring
      _ ≤ 4 * (1 - γ)⁻¹ * (|K| * ((Vb k : ℝ) + 1)) * (Cp * E) := by gcongr
      _ = _ := by ring
  have h5 : 5 * (c * Real.exp (-(m * D))) ≤ 5 * c * E := by
    have := mul_le_mul_of_nonneg_left hmE hc; linarith
  have q := abs_sub_abs_le_abs_sub
    (∫ U, F (tShift (n : ZMod N) U) * F (thetaConn U) ∂(T.ym k j) -
      (∫ U, F (tShift (n : ZMod N) U) ∂(T.ym k j)) * ∫ U, F (thetaConn U) ∂(T.ym k j))
    (∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
      (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j))
  have hE0 : 0 < E := Real.exp_pos _
  calc _ ≤ 4 * (1 - γ)⁻¹ * |K| * ((Vb k : ℝ) + 1) * Cp * E + 5 * c * E := by linarith
    _ = _ := by ring

/-- The blocked route as one proposition about a tuning. -/
def BlockedRoute (T : Tuning) : Prop :=
  ∃ (B : BlockingFamily T) (lam : ℝ) (Vk : ∀ j, ℕ → CoarsePot j) (Vinf : ∀ j, CoarsePot j),
    0 < lam ∧ H1Local T B lam Vk Vinf ∧ LimitDprime lam Vinf ∧ ObsTransfer T B

theorem slabDecay_of_blockedRoute' {T : Tuning} (h : BlockedRoute T) : SlabDecay T := by
  obtain ⟨B, lam, Vk, Vinf, hlam, h1, h2, h3⟩ := h
  exact slabDecay_of_blockedRoute B hlam h1 h2 h3

/-- **The blocked route discharges route A's field:** with the line of constant physics and non-triviality, it gives
`OpenPieces` (crossover by route A). (Cycle 2, workstream C: `OpenPieces.crossover` now lists the blocked route itself;
`BlockedRoute` here is the same proposition as `ProofPhase.BlockedSlabRoute`, the second disjunct.) -/
theorem openPieces_of_blockedRoute {T : Tuning} (hL : OnLCP T) (hN : NonTrivial T) (h : BlockedRoute T) :
    OpenPieces T :=
  ⟨hL, hN, Or.inr (Or.inl h)⟩

/-- **Assembly through the blocked route.** -/
theorem assembly_blockedRoute {T : Tuning} (hL : OnLCP T) (h : BlockedRoute T) :
    MassGap T ∧ LatticeGap T ∧ LimitRP T :=
  assembly_routeA hL (slabDecay_of_blockedRoute' h)

/-! ## A genuine metric on links (review finding 5) -/

section Metric

variable {d N : ℕ} [NeZero N]

/-- `linkDist` is not definite: two distinct links at the same base site are at distance `0`. -/
theorem linkDist_not_definite :
    ∃ e e' : LatticeLink 4 N, e ≠ e' ∧ linkDist e e' = 0 := by
  refine ⟨⟨fun _ => 0, 0⟩, ⟨fun _ => 0, 1⟩, fun h => ?_, ?_⟩
  · have := congrArg LatticeLink.dir h
    simp at this
  · simp [linkDist, siteDist_self]

/-- **A metric on links**: `linkDist` plus the discrete metric. -/
def linkMetric (e e' : LatticeLink d N) : ℝ := linkDist e e' + if e = e' then 0 else 1

theorem linkMetric_self (e : LatticeLink d N) : linkMetric e e = 0 := by simp [linkMetric, linkDist_self]

theorem linkMetric_symm (e e' : LatticeLink d N) : linkMetric e e' = linkMetric e' e := by
  unfold linkMetric; rw [linkDist_symm]; by_cases h : e = e' <;> simp [h, eq_comm]

theorem linkMetric_triangle (e e' e'' : LatticeLink d N) :
    linkMetric e e'' ≤ linkMetric e e' + linkMetric e' e'' := by
  unfold linkMetric
  have := linkDist_triangle e e' e''
  by_cases h1 : e = e' <;> by_cases h2 : e' = e'' <;> by_cases h3 : e = e'' <;> simp_all <;> linarith

theorem eq_of_linkMetric_eq_zero {e e' : LatticeLink d N} (h : linkMetric e e' = 0) : e = e' := by
  by_contra hne
  unfold linkMetric at h
  simp only [hne, ↓reduceIte] at h
  linarith [linkDist_nonneg e e']

theorem linkMetric_le (e e' : LatticeLink d N) : linkMetric e e' ≤ linkDist e e' + 1 := by
  unfold linkMetric; split_ifs <;> linarith

/-- **The blocked route's block decay in the metric `linkMetric`** (cost: a factor `e^{λ}`). -/
theorem blockGap_linkMetric {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 ≤ lam)
    {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf)
    (h2 : LimitDprime lam Vinf) :
    ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
      (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
      (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg R : ℝ),
      BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) →
      (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkMetric x y) →
      |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
          (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
        Real.exp lam * ((1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R))) := by
  obtain ⟨γ, hγ0, hγ1, k₀, h⟩ := blockGap_of_blockedRoute B hlam h1 h2
  refine ⟨γ, hγ0, hγ1, k₀, fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ?_⟩
  have := h k hk j f g A Sg vf Lg (R - 1) hf hg hfA hgS hvf hLg hvg
    (fun x hx y hy => by have := (hR x hx y hy).trans (linkMetric_le x y); linarith)
  refine this.trans (le_of_eq ?_)
  rw [show -(lam * (R - 1)) = lam + -(lam * R) by ring, Real.exp_add]
  ring

end Metric

end ProofPhase.Quantum
