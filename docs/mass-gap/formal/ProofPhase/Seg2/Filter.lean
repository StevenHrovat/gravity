/-
Proof phase, cycle 4, workstream 3 (c4c-seg2): segment 2 (L_* -> L1) as filter stability, 2026-11-22. Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c4c-seg2/NOTE.md`.
-/

import ProofPhase.UV.Split

/-!
# Conditional decoupling from smoother stability (filter-stability form of Lemma X)

Dictionary (see the note, section 1). Euclidean time is the "time" of a hidden Markov model: the hidden state at coarse time
`t` is the fine field on the time slice `t * L1` (the transfer-matrix chain); the observations are the coarse links of the
good blocking, each of which is a function of one time strip (spatial smearing within slices, temporal decimation). For a
pair of observables `F`, `G` separated in time, the Markov property of the Wilson measure in time makes `F` and `G`
conditionally uncorrelated given the observations **and** the two slices that cut the time circle between them (paper,
note section 1.3). The quantity of part (c) of `ObsTransferPhys` is
then controlled by the **smoother-stability defect** `int |E[F | obs, slice] - E[F | obs]|`: how much learning the hidden
state at a distant time changes the conditional expectation of `F` given all observations. This is filter (smoother)
stability, the forgetting of the "initial condition" in the HMM sense.

**Generic (any probability space).** With `m` the observation sigma-algebra and `K >= m`:
* `abs_condDefect_le_dev`: `|condDefect m f g| <= int |f - E[f|m]|` for `|f|, |g| <= 1`.
* `condDefect_eq_of_condUncorr`: if `condDefect K F G = 0` (conditional uncorrelatedness given `K`, the Markov split),
  then `condDefect m F G = condDefect m E[F|K] E[G|K]`.
* **`abs_condDefect_le_smoother`**: under the Markov split, `|condDefect m F G| <= int |E[F|K] - E[F|m]|`
  (and the same with `G`, `abs_condDefect_le_smoother'`).
* **`smoother_chain_of_steps`** (annealed contraction along a chain): sigma-algebras `K 0, K 1, ...` above `m`, a Markov
  property along the chain for `F`, and a conditional contraction of each step of `F`'s smoother defect with
  `m`-measurable weights `theta i` in `[0, 1]` give `int |E[F|K n] - E[F|m]| <= 2 int prod_{i<n} theta i`. Bad
  observation configurations (large fields) may have `theta = 1`; only the average of the product enters.
  `smoother_chain`: the same from the model-level `CondContract` (every centred function; not volume-uniform for whole
  slices, see the note).
* `abs_condDefect_le_chain`, `abs_condDefect_le_chain_const`: the two combined; with constant `theta0`, `<= 2 theta0^n`.
* `approx_of_smoother`: part (b) (`E[F|obs] ~ E[F|near obs]`) from the same stability defect for two observation
  sigma-algebras plus the Markov property for the far observations.

**Yang-Mills instance.** `CondDecouple T B Sep` is part (c) of `ObsTransferPhys` restricted to pairs satisfying a
separation predicate `Sep` (time separation gives c3a's proposed `ObsTransferPhysT`, part (c)). `SmootherStable T B Sep`
is the named hypothesis (Markov split at slice sigma-algebras plus an exponentially small smoother-stability defect);
`AnnealedContraction T B Sep` is one sufficient condition for it (a chain of slices with annealed step contraction).
`condDecouple_of_smootherStable`, `smootherStable_of_annealedContraction`, `condDecouple_of_annealedContraction`.

**Claim level.** Generic measure theory; substantive only as a reduction and as the exact location of the content. No
estimate is proved for any interacting theory; nothing here distinguishes SU(2) from U(1) or Z2 (it must not: the
conclusion holds for the photon with the good blocking, which has no gap).
-/

open MeasureTheory Finset Filter AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Seg2

open ProofPhase.UV

/-! ## Generic: smoother stability controls conditional decoupling -/

section Generic

variable {X : Type*} {mX : MeasurableSpace X}

/-- **Conditional contraction of one step of the conditional chain** (annealed Dobrushin coefficient). For every
`K`-measurable `u` with `|u| <= 2` and `E[u|m] = 0`: `E[|E[u|K']| | m] <= theta * E[|u| | m]` almost everywhere. With
`theta` constant this is a uniform (quenched) contraction; with `theta` an `m`-measurable function it allows observation
configurations on which the step does not contract. -/
def CondContract (μ : Measure[mX] X) (m K K' : MeasurableSpace X) (θ : X → ℝ) : Prop :=
  ∀ u : X → ℝ, StronglyMeasurable[K] u → (∀ᵐ x ∂μ, |u x| ≤ 2) → μ[u | m] =ᵐ[μ] 0 →
    μ[fun x => |μ[u | K'] x| | m] ≤ᵐ[μ] fun x => θ x * μ[fun x => |u x| | m] x

variable {μ : Measure[mX] X} [IsProbabilityMeasure μ]

theorem condDefect_comm (m : MeasurableSpace X) (F G : X → ℝ) :
    condDefect μ m F G = condDefect μ m G F := by
  unfold condDefect
  congr 1
  · exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  · exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)

/-- The defect is bounded by the `L¹` distance of `f` from its conditional expectation. -/
theorem abs_condDefect_le_dev {m : MeasurableSpace X} (hm : m ≤ mX) {f g : X → ℝ} (hf : Bdd1 μ f)
    (hg : Bdd1 μ g) :
    |condDefect μ m f g| ≤ ∫ x, |f x - μ[f | m] x| ∂μ := by
  have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have hEf := hf.condExp hm
  have hEg := hg.condExp hm
  have hb : ∀ᵐ x ∂μ, ‖μ[f | m] x‖ ≤ 1 := hEf.2.mono fun x hx => by rwa [Real.norm_eq_abs]
  have hpull : μ[μ[f | m] * g | m] =ᵐ[μ] μ[f | m] * μ[g | m] :=
    condExp_stronglyMeasurable_mul_of_bound hm stronglyMeasurable_condExp hg.integrable 1 hb
  have key : ∫ x, μ[f | m] x * μ[g | m] x ∂μ = ∫ x, μ[f | m] x * g x ∂μ := by
    calc ∫ x, μ[f | m] x * μ[g | m] x ∂μ = ∫ x, μ[μ[f | m] * g | m] x ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hpull] with x hx
          rw [hx]; rfl
      _ = ∫ x, (μ[f | m] * g) x ∂μ := integral_condExp hm
      _ = ∫ x, μ[f | m] x * g x ∂μ := rfl
  have i1 : Integrable (fun x => f x * g x) μ := (hf.mul hg).integrable
  have i2 : Integrable (fun x => μ[f | m] x * g x) μ := (hEf.mul hg).integrable
  have e : condDefect μ m f g = ∫ x, (f x - μ[f | m] x) * g x ∂μ := by
    unfold condDefect
    rw [key, ← integral_sub i1 i2]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [e]
  have i3 : Integrable (fun x => |f x - μ[f | m] x|) μ := (hf.integrable.sub hEf.integrable).abs
  have i4 : Integrable (fun x => (f x - μ[f | m] x) * g x) μ :=
    (i1.sub i2).congr (ae_of_all _ fun x => by simp only [Pi.sub_apply]; ring)
  refine abs_integral_le_integral_abs.trans (integral_mono_ae i4.abs i3 ?_)
  filter_upwards [hg.2] with x hx
  show |(f x - μ[f | m] x) * g x| ≤ |f x - μ[f | m] x|
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) hx

/-- **The Markov split.** If `F`, `G` are conditionally uncorrelated given `K >= m`, the defect given `m` is the defect of
their conditional expectations given `K`. -/
theorem condDefect_eq_of_condUncorr {m K : MeasurableSpace X} (hm : m ≤ K) (hK : K ≤ mX) {F G : X → ℝ}
    (hM : condDefect μ K F G = 0) :
    condDefect μ m F G = condDefect μ m (μ[F | K]) (μ[G | K]) := by
  rw [condDefect_tower hm hK, hM, zero_add]

/-- **Smoother stability controls conditional decoupling.** Under the Markov split at `K >= m`, the defect given the
observations `m` is at most the smoother-stability defect `int |E[F|K] - E[F|m]|`. -/
theorem abs_condDefect_le_smoother {m K : MeasurableSpace X} (hm : m ≤ K) (hK : K ≤ mX) {F G : X → ℝ}
    (hF : Bdd1 μ F) (hG : Bdd1 μ G) (hM : condDefect μ K F G = 0) :
    |condDefect μ m F G| ≤ ∫ x, |μ[F | K] x - μ[F | m] x| ∂μ := by
  have : IsFiniteMeasure (μ.trim hK) := isFiniteMeasure_trim hK
  rw [condDefect_eq_of_condUncorr hm hK hM]
  refine (abs_condDefect_le_dev (hm.trans hK) (hF.condExp hK) (hG.condExp hK)).trans (le_of_eq ?_)
  refine integral_congr_ae ?_
  filter_upwards [condExp_condExp_of_le (f := F) (μ := μ) hm hK] with x hx
  rw [hx]

/-- The same with the roles of `F` and `G` exchanged (stability measured on the far side). -/
theorem abs_condDefect_le_smoother' {m K : MeasurableSpace X} (hm : m ≤ K) (hK : K ≤ mX) {F G : X → ℝ}
    (hF : Bdd1 μ F) (hG : Bdd1 μ G) (hM : condDefect μ K F G = 0) :
    |condDefect μ m F G| ≤ ∫ x, |μ[G | K] x - μ[G | m] x| ∂μ := by
  rw [condDefect_comm] at hM ⊢
  exact abs_condDefect_le_smoother hm hK hG hF hM

/-- **Part (b) from smoother stability.** `𝒩 ≤ m` (near observations), `K >= m` and `K' >= 𝒩` (each with the hidden slice),
and the Markov property `E[F|K] = E[F|K']` (given the slice, the far observations carry no information about `F`). Then
`int |E[F|m] - E[F|𝒩]|` is at most the sum of the two smoother-stability defects. -/
theorem approx_of_smoother {m 𝒩 K K' : MeasurableSpace X} {F : X → ℝ}
    (hM : μ[F | K] =ᵐ[μ] μ[F | K']) :
    ∫ x, |μ[F | m] x - μ[F | 𝒩] x| ∂μ ≤
      ∫ x, |μ[F | K] x - μ[F | m] x| ∂μ + ∫ x, |μ[F | K'] x - μ[F | 𝒩] x| ∂μ := by
  have i1 : Integrable (fun x => |μ[F | K] x - μ[F | m] x|) μ := (integrable_condExp.sub integrable_condExp).abs
  have i2 : Integrable (fun x => |μ[F | K'] x - μ[F | 𝒩] x|) μ := (integrable_condExp.sub integrable_condExp).abs
  rw [← integral_add i1 i2]
  refine integral_mono_ae (integrable_condExp.sub integrable_condExp).abs (i1.add i2) ?_
  filter_upwards [hM] with x hx
  show |μ[F | m] x - μ[F | 𝒩] x| ≤ |μ[F | K] x - μ[F | m] x| + |μ[F | K'] x - μ[F | 𝒩] x|
  rw [← hx]
  have e : μ[F | m] x - μ[F | 𝒩] x = -(μ[F | K] x - μ[F | m] x) + (μ[F | K] x - μ[F | 𝒩] x) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]

/-- **Annealed contraction along a chain (smoother stability from a conditional Dobrushin bound).** Sigma-algebras
`K i >= m`, a Markov property along the chain for `F` (`E[E[F|K i] | K (i+1)] = E[F|K (i+1)]`), and conditional contraction
of every step with `m`-measurable weights `theta i` in `[0, 1]`. Then
`int |E[F|K n] - E[F|m]| <= 2 int prod_{i<n} theta i`. -/
theorem smoother_chain_of_steps {m : MeasurableSpace X} (hm : m ≤ mX) (K : ℕ → MeasurableSpace X)
    (hmK : ∀ i, m ≤ K i) (hK : ∀ i, K i ≤ mX) (θ : ℕ → X → ℝ) (hθm : ∀ i, StronglyMeasurable[m] (θ i))
    (hθ0 : ∀ i x, 0 ≤ θ i x) (hθ1 : ∀ i x, θ i x ≤ 1) {F : X → ℝ} (hF : Bdd1 μ F)
    (hMk : ∀ i, μ[μ[F | K i] | K (i + 1)] =ᵐ[μ] μ[F | K (i + 1)])
    (hS : ∀ i, μ[fun x => |μ[fun y => μ[F | K i] y - μ[F | m] y | K (i + 1)] x| | m] ≤ᵐ[μ]
      fun x => θ i x * μ[fun x => |μ[F | K i] x - μ[F | m] x| | m] x) (n : ℕ) :
    ∫ x, |μ[F | K n] x - μ[F | m] x| ∂μ ≤ 2 * ∫ x, (∏ i ∈ range n, θ i x) ∂μ := by
  have hfm : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  set u : ℕ → X → ℝ := fun i x => μ[F | K i] x - μ[F | m] x with hu
  have hEm := hF.condExp hm
  -- (B) bound
  have hB : ∀ i, ∀ᵐ x ∂μ, |u i x| ≤ 2 := fun i => by
    have hEK := hF.condExp (hK i)
    filter_upwards [hEK.2, hEm.2] with x h1 h2
    calc |u i x| ≤ |μ[F | K i] x| + |μ[F | m] x| := abs_sub _ _
      _ ≤ 2 := by linarith
  -- (D) one step of the chain
  have hD : ∀ i, μ[u i | K (i + 1)] =ᵐ[μ] u (i + 1) := fun i => by
    have : IsFiniteMeasure (μ.trim (hK (i + 1))) := isFiniteMeasure_trim (hK (i + 1))
    have hconst : μ[μ[F | m] | K (i + 1)] = μ[F | m] :=
      condExp_of_stronglyMeasurable (hK (i + 1)) (stronglyMeasurable_condExp.mono (hmK (i + 1))) integrable_condExp
    filter_upwards [condExp_sub (m := K (i + 1)) (μ := μ) (integrable_condExp (m := K i) (f := F))
        (integrable_condExp (m := m) (f := F)), hMk i] with x h1 h2
    have e : u i = μ[F | K i] - μ[F | m] := rfl
    rw [e, h1, Pi.sub_apply, h2, hconst]
  -- (E) the product bound, conditionally on the observations
  have hE : ∀ n, μ[fun x => |u n x| | m] ≤ᵐ[μ]
      fun x => (∏ i ∈ range n, θ i x) * μ[fun x => |u 0 x| | m] x := by
    intro n
    induction n with
    | zero => exact ae_of_all _ fun x => by simp
    | succ n ih =>
      have h1 : μ[fun x => |u (n + 1) x| | m] =ᵐ[μ] μ[fun x => |μ[u n | K (n + 1)] x| | m] := by
        refine condExp_congr_ae ?_
        filter_upwards [hD n] with x hx
        rw [hx]
      have h2 := hS n
      filter_upwards [h1, h2, ih] with x e1 e2 e3
      rw [e1, prod_range_succ]
      calc μ[fun x => |μ[u n | K (n + 1)] x| | m] x ≤ θ n x * μ[fun x => |u n x| | m] x := e2
        _ ≤ θ n x * ((∏ i ∈ range n, θ i x) * μ[fun x => |u 0 x| | m] x) :=
            mul_le_mul_of_nonneg_left e3 (hθ0 n x)
        _ = (∏ i ∈ range n, θ i x) * θ n x * μ[fun x => |u 0 x| | m] x := by ring
  -- (F) integrate
  have hint_abs : Integrable (fun x => |u n x|) μ := (integrable_condExp.sub integrable_condExp).abs
  have hb0 : ∀ᵐ x ∂μ, |μ[fun x => |u 0 x| | m] x| ≤ 2 :=
    ae_bdd_abs_condExp_of_ae_bdd_abs ((hB 0).mono fun x hx => by rwa [abs_abs])
  have hprod_meas : AEStronglyMeasurable[mX] (fun x => ∏ i ∈ range n, θ i x) μ := by
    have h : StronglyMeasurable[m] (∏ i ∈ range n, θ i) :=
      Finset.stronglyMeasurable_prod (range n) (fun i _ => hθm i)
    have h' : StronglyMeasurable[mX] (∏ i ∈ range n, θ i) := h.mono hm
    have e : (∏ i ∈ range n, θ i) = fun x => ∏ i ∈ range n, θ i x := by
      funext x; exact Finset.prod_apply x (range n) θ
    rw [e] at h'
    exact h'.aestronglyMeasurable
  have hprod_b : ∀ x, |∏ i ∈ range n, θ i x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (prod_nonneg fun i _ => hθ0 i x)]
    exact prod_le_one₀ (fun i _ => hθ0 i x) (fun i _ => hθ1 i x)
  have hprod_int : Integrable (fun x => ∏ i ∈ range n, θ i x) μ :=
    integrable_of_ae_abs_le hprod_meas (ae_of_all _ hprod_b)
  have hrhs_int : Integrable (fun x => (∏ i ∈ range n, θ i x) * μ[fun x => |u 0 x| | m] x) μ := by
    refine integrable_of_ae_abs_le (hprod_meas.mul integrable_condExp.aestronglyMeasurable) (C := 2) ?_
    filter_upwards [hb0] with x hx
    rw [abs_mul]
    calc |∏ i ∈ range n, θ i x| * |μ[fun x => |u 0 x| | m] x| ≤ 1 * 2 :=
          mul_le_mul (hprod_b x) hx (abs_nonneg _) zero_le_one
      _ = 2 := by ring
  calc ∫ x, |μ[F | K n] x - μ[F | m] x| ∂μ = ∫ x, μ[fun x => |u n x| | m] x ∂μ :=
        (integral_condExp hm).symm
    _ ≤ ∫ x, (∏ i ∈ range n, θ i x) * μ[fun x => |u 0 x| | m] x ∂μ :=
        integral_mono_ae integrable_condExp hrhs_int (hE n)
    _ ≤ ∫ x, (∏ i ∈ range n, θ i x) * 2 ∂μ := by
        refine integral_mono_ae hrhs_int (hprod_int.mul_const 2) ?_
        filter_upwards [hb0] with x hx
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hx)
          (prod_nonneg fun i _ => hθ0 i x)
    _ = 2 * ∫ x, (∏ i ∈ range n, θ i x) ∂μ := by rw [integral_mul_const, mul_comm]

/-- The chain bound from the model-level contraction `CondContract` (for every centred function, not only those of `F`).
Caution (note, section 4.2): for sigma-algebras containing a whole time slice, `CondContract` with `theta < 1` cannot hold
uniformly in the volume (total-variation contraction does not tensorise); the dimension-free form is local
(`smoother_chain_of_steps` with `F`-specific steps, or a Dobrushin matrix condition). -/
theorem smoother_chain {m : MeasurableSpace X} (hm : m ≤ mX) (K : ℕ → MeasurableSpace X) (hmK : ∀ i, m ≤ K i)
    (hK : ∀ i, K i ≤ mX) (θ : ℕ → X → ℝ) (hθm : ∀ i, StronglyMeasurable[m] (θ i)) (hθ0 : ∀ i x, 0 ≤ θ i x)
    (hθ1 : ∀ i x, θ i x ≤ 1) (hC : ∀ i, CondContract μ m (K i) (K (i + 1)) (θ i)) {F : X → ℝ} (hF : Bdd1 μ F)
    (hMk : ∀ i, μ[μ[F | K i] | K (i + 1)] =ᵐ[μ] μ[F | K (i + 1)]) (n : ℕ) :
    ∫ x, |μ[F | K n] x - μ[F | m] x| ∂μ ≤ 2 * ∫ x, (∏ i ∈ range n, θ i x) ∂μ := by
  have hfm : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have hEm := hF.condExp hm
  refine smoother_chain_of_steps hm K hmK hK θ hθm hθ0 hθ1 hF hMk (fun i => ?_) n
  have : IsFiniteMeasure (μ.trim (hK i)) := isFiniteMeasure_trim (hK i)
  have hEK := hF.condExp (hK i)
  refine hC i (fun y => μ[F | K i] y - μ[F | m] y)
    (stronglyMeasurable_condExp.sub (stronglyMeasurable_condExp.mono (hmK i))) ?_ ?_
  · filter_upwards [hEK.2, hEm.2] with x h1 h2
    calc |μ[F | K i] x - μ[F | m] x| ≤ |μ[F | K i] x| + |μ[F | m] x| := abs_sub _ _
      _ ≤ 2 := by linarith
  · filter_upwards [condExp_sub (m := m) (μ := μ) (integrable_condExp (m := K i) (f := F))
        (integrable_condExp (m := m) (f := F)),
      condExp_condExp_of_le (f := F) (μ := μ) (hmK i) (hK i),
      condExp_condExp_of_le (f := F) (μ := μ) (le_refl m) hm] with x h1 h2 h3
    have e : (fun y => μ[F | K i] y - μ[F | m] y) = μ[F | K i] - μ[F | m] := rfl
    rw [e, h1, Pi.sub_apply, h2, h3, sub_self]; rfl

/-- **Conditional decoupling from annealed contraction.** The chain bound combined with the Markov split at the end of
the chain. -/
theorem abs_condDefect_le_chain {m : MeasurableSpace X} (hm : m ≤ mX) (K : ℕ → MeasurableSpace X)
    (hmK : ∀ i, m ≤ K i) (hK : ∀ i, K i ≤ mX) (θ : ℕ → X → ℝ) (hθm : ∀ i, StronglyMeasurable[m] (θ i))
    (hθ0 : ∀ i x, 0 ≤ θ i x) (hθ1 : ∀ i x, θ i x ≤ 1) (hC : ∀ i, CondContract μ m (K i) (K (i + 1)) (θ i))
    {F G : X → ℝ} (hF : Bdd1 μ F) (hG : Bdd1 μ G)
    (hMk : ∀ i, μ[μ[F | K i] | K (i + 1)] =ᵐ[μ] μ[F | K (i + 1)]) (n : ℕ) (hMn : condDefect μ (K n) F G = 0) :
    |condDefect μ m F G| ≤ 2 * ∫ x, (∏ i ∈ range n, θ i x) ∂μ :=
  (abs_condDefect_le_smoother (hmK n) (hK n) hF hG hMn).trans
    (smoother_chain hm K hmK hK θ hθm hθ0 hθ1 hC hF hMk n)

/-- The uniform (quenched) case: a constant contraction `theta0` per step gives `2 theta0^n`. -/
theorem abs_condDefect_le_chain_const {m : MeasurableSpace X} (hm : m ≤ mX) (K : ℕ → MeasurableSpace X)
    (hmK : ∀ i, m ≤ K i) (hK : ∀ i, K i ≤ mX) {θ₀ : ℝ} (h0 : 0 ≤ θ₀) (h1 : θ₀ ≤ 1)
    (hC : ∀ i, CondContract μ m (K i) (K (i + 1)) (fun _ => θ₀))
    {F G : X → ℝ} (hF : Bdd1 μ F) (hG : Bdd1 μ G)
    (hMk : ∀ i, μ[μ[F | K i] | K (i + 1)] =ᵐ[μ] μ[F | K (i + 1)]) (n : ℕ) (hMn : condDefect μ (K n) F G = 0) :
    |condDefect μ m F G| ≤ 2 * θ₀ ^ n := by
  have h := abs_condDefect_le_chain hm K hmK hK (fun _ _ => θ₀) (fun _ => stronglyMeasurable_const)
    (fun _ _ => h0) (fun _ _ => h1) hC hF hG hMk n hMn
  simpa [prod_const, card_range, integral_const] using h

end Generic

/-! ## The Yang–Mills instance -/

section YM

/-- The block sigma-algebra of the blocking family at level `k`, volume `j`. -/
abbrev blockSigma (T : Tuning) (B : BlockingFamily T) (k j : ℕ) :
    MeasurableSpace (GaugeConnection SU2 4 (T.side k j)) :=
  MeasurableSpace.comap (B k j).B inferInstance

/-- A separation predicate on pairs of supports at physical distance `D` (time separation by a slab gives c3a's
`ObsTransferPhysT`; the reduction below is uniform in the choice). -/
abbrev SepPred (T : Tuning) : Type :=
  ∀ k j : ℕ, Finset (LatticeLink 4 (T.side k j)) → Finset (LatticeLink 4 (T.side k j)) → ℝ → Prop

/-- **Part (c) of `ObsTransferPhys`, restricted to pairs satisfying `Sep`** (same quantifiers and constants). -/
def CondDecouple (T : Tuning) (B : BlockingFamily T) (Sep : SepPred T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R → Sep k j A₀ B₀ D →
    |condDefect (T.ym k j) (blockSigma T B k j) F G| ≤ c * Real.exp (-(m * D))

/-- The (c) clause of `ObsTransferPhys` is literally `|condDefect|`. -/
theorem condClause_eq (T : Tuning) (B : BlockingFamily T) (k j : ℕ) (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) :
    |∫ U, F U * G U ∂(T.ym k j) -
        ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U *
          condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U ∂(T.ym k j)|
      = |condDefect (T.ym k j) (blockSigma T B k j) F G| := rfl

/-- **The named hypothesis (filter-stability form of Lemma X in the time direction).** For every admissible separated
pair there are a chain of sigma-algebras `K i` above the block sigma-algebra (intended: block field plus the fine field
on the slice at the `i`-th coarse time between the supports), the Markov properties along the chain and at its end
(paper: locality of the Wilson action in time), and annealed conditional contraction weights `theta i` (functions of the
block field, in `[0, 1]`) for the steps of `F`'s own smoother defect, whose averaged product is exponentially small in
`D`. The steps are `F`-specific on purpose: a contraction for every function of a whole slice cannot hold uniformly in
the volume (note, section 4.2). -/
def AnnealedContraction (T : Tuning) (B : BlockingFamily T) (Sep : SepPred T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R → Sep k j A₀ B₀ D →
    ∃ (n : ℕ) (K : ℕ → MeasurableSpace (GaugeConnection SU2 4 (T.side k j)))
      (θ : ℕ → GaugeConnection SU2 4 (T.side k j) → ℝ),
      (∀ i, blockSigma T B k j ≤ K i ∧
        K i ≤ (MeasurableSpace.pi : MeasurableSpace (GaugeConnection SU2 4 (T.side k j)))) ∧
      (∀ i, StronglyMeasurable[blockSigma T B k j] (θ i) ∧ ∀ U, 0 ≤ θ i U ∧ θ i U ≤ 1) ∧
      (∀ i, condExp (blockSigma T B k j) (T.ym k j)
          (fun x => |condExp (K (i + 1)) (T.ym k j)
            (fun y => condExp (K i) (T.ym k j) F y - condExp (blockSigma T B k j) (T.ym k j) F y) x|)
        ≤ᵐ[T.ym k j] fun x => θ i x * condExp (blockSigma T B k j) (T.ym k j)
          (fun x => |condExp (K i) (T.ym k j) F x - condExp (blockSigma T B k j) (T.ym k j) F x|) x) ∧
      (∀ i, condExp (K (i + 1)) (T.ym k j) (condExp (K i) (T.ym k j) F) =ᵐ[T.ym k j]
        condExp (K (i + 1)) (T.ym k j) F) ∧
      condDefect (T.ym k j) (K n) F G = 0 ∧
      2 * ∫ U, (∏ i ∈ range n, θ i U) ∂(T.ym k j) ≤ c * Real.exp (-(m * D))

/-- **The smoother-stability hypothesis (the exact filter-stability form of part (c)).** For every admissible separated
pair there is a sigma-algebra `K` above the block sigma-algebra (intended: block field plus the fine field on the two
time slices that cut the time circle between the supports) such that `F` and `G` are conditionally uncorrelated given
`K` (paper: Markov property of the Wilson measure in time) and the smoother-stability defect
`int |E[F|K] - E[F|blocks]|` is exponentially small in `D`. -/
def SmootherStable (T : Tuning) (B : BlockingFamily T) (Sep : SepPred T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c : ℝ, 0 ≤ c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R → Sep k j A₀ B₀ D →
    ∃ K : MeasurableSpace (GaugeConnection SU2 4 (T.side k j)),
      blockSigma T B k j ≤ K ∧ K ≤ (MeasurableSpace.pi : MeasurableSpace (GaugeConnection SU2 4 (T.side k j))) ∧
      condDefect (T.ym k j) K F G = 0 ∧
      ∫ U, |condExp K (T.ym k j) F U - condExp (blockSigma T B k j) (T.ym k j) F U| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D))

/-- **Reduction (Lean): smoother stability gives part (c) for the separated pairs**, on the SU(2) Wilson measure along
the tuning, for any blocking family and any separation predicate. -/
theorem condDecouple_of_smootherStable {T : Tuning} {B : BlockingFamily T} {Sep : SepPred T}
    (h : SmootherStable T B Sep) : CondDecouple T B Sep := by
  obtain ⟨m, hm, hR⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, hc, k₀, hk⟩ := hR R
  refine ⟨c, hc, k₀, fun k hk₀ j F G A₀ B₀ D hFm hGm hF1 hG1 hFi hGi hFd hGd hA hB hS => ?_⟩
  have := ymProb T k j
  obtain ⟨K, hBK, hK, hMn, hbd⟩ := hk k hk₀ j F G A₀ B₀ D hFm hGm hF1 hG1 hFi hGi hFd hGd hA hB hS
  exact (abs_condDefect_le_smoother hBK hK (Bdd1.of_measurable hFm hF1) (Bdd1.of_measurable hGm hG1) hMn).trans hbd

/-- **Reduction (Lean): annealed step-wise contraction along a chain of slices gives smoother stability.** -/
theorem smootherStable_of_annealedContraction {T : Tuning} {B : BlockingFamily T} {Sep : SepPred T}
    (h : AnnealedContraction T B Sep) : SmootherStable T B Sep := by
  obtain ⟨m, hm, hR⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, hc, k₀, hk⟩ := hR R
  refine ⟨c, hc, k₀, fun k hk₀ j F G A₀ B₀ D hFm hGm hF1 hG1 hFi hGi hFd hGd hA hB hS => ?_⟩
  have := ymProb T k j
  obtain ⟨n, K, θ, hK, hθ, hC, hMk, hMn, hbd⟩ := hk k hk₀ j F G A₀ B₀ D hFm hGm hF1 hG1 hFi hGi hFd hGd hA hB hS
  have hmeas : blockSigma T B k j ≤ (MeasurableSpace.pi : MeasurableSpace (GaugeConnection SU2 4 (T.side k j))) :=
    (B k j).meas.comap_le
  refine ⟨K n, (hK n).1, (hK n).2, hMn, ?_⟩
  exact (smoother_chain_of_steps hmeas K (fun i => (hK i).1) (fun i => (hK i).2) θ (fun i => (hθ i).1)
    (fun i U => ((hθ i).2 U).1) (fun i U => ((hθ i).2 U).2) (Bdd1.of_measurable hFm hF1) hMk hC n).trans hbd

/-- The composite: annealed step-wise contraction gives part (c) for the separated pairs. -/
theorem condDecouple_of_annealedContraction {T : Tuning} {B : BlockingFamily T} {Sep : SepPred T}
    (h : AnnealedContraction T B Sep) : CondDecouple T B Sep :=
  condDecouple_of_smootherStable (smootherStable_of_annealedContraction h)

end YM

end ProofPhase.Seg2
