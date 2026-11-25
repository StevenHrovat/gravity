/-
Proof phase, cycle 7, workstream b (c7b-centre): the combined statement (centre comparison + the repo's Z2 area law) and the
unit tests (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c7b-centre/NOTE.md`, sections 2 and 3.
-/

import ProofPhase.Centre.Z2Wilson

/-!
# Centre comparison plus strong-coupling Z2: an area law in every volume from one scale's worst-case centre coupling

**Named hypothesis `PlaqMixture`** (what it asserts): the Wilson loop expectation `W` of the (blocked) theory on the lattice
`(Z/NZ)^d` is a `μ`-mixture over backgrounds `v` of Z2 Ising correlations,
`W = ∫ w(v) ⟨σ_C⟩_{J(v)} dμ(v)`, where `⟨·⟩_J` is the Z2 gauge model with one interaction per plaquette (its four boundary
links) and coupling `J(v)_p` (any sign), `σ_C` is the product of the spins on the links of the loop, and `w` is bounded
(`|w| ≤ M`). For SU(2) with the Wilson action this is the statement that `U_ℓ = σ_ℓ V_ℓ` (`σ_ℓ = ±1`, `V_ℓ` in a
measurable section of `SU(2) → SO(3)`) turns Haar measure into the product of a uniform `σ` and the section law of `V`
(Haar is invariant under `U ↦ -U`), that `Re tr U_p = σ_p Re tr V_p'` with `V_p'` the SU(2) product of the section values,
and that the conditional law of `σ` given `V` has density `exp(β ∑_p σ_p r_p(V))`, `r_p = Re tr V_p'`; then
`μ(dv) ∝ Z(v) dP(v)`. It is a disintegration of the Haar measure, not proved here (the repo has no such disintegration).

* `centre_area_law`: the hypothesis, plus `|J(v)_p| ≤ b` for every background and plaquette and `e^b - 1` in the repo's strong
  coupling range, gives for the `R × T` loop `|W| ≤ M · e^{2·4d·2(R+T)} (√(e^{16d+1}(e^b - 1)))^{min(RT, N²-RT)}`:
  an area law in **every volume `N`** at once (the constants do not depend on `N`).
* `su2_area_law_of_mixture`: the bare SU(2) case, `b = 2β`, `M = 2`; the bound is **identical** to the repo's direct SU(2)
  strong-coupling bound `wilson_area_law_SU2` (`su2_bound_eq`), so the comparison route loses nothing at this level and
  reproduces the known theorem; it is new only when `b` is the **block-scale** worst-case effective centre coupling.

Unit tests (toy Z2 model with one site, one interaction: `corr = tanh J`): `comparison_sharp` (the bound is attained for a
one-point mixture with `J ≥ 0`, so neither the constant nor `J̄` can be improved), `toy_mixture_cancels` (a frustrated
mixture `±a` has `W = 0 ≤ tanh a`), `toy_vacuous` (`tanh b → 1` as `b → ∞`: the bound is empty when the worst-case coupling
is large, which is the deconfined / photon / 2I situation).
-/

open Finset MeasureTheory Filter Topology

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Centre

open AreaLaw.Assembly AreaLaw.Concrete

section Combined

variable {d N : ℕ} [NeZero N]

/-- **The named hypothesis**: the Wilson loop expectation `W` of the loop `C` is a mixture `∫ w(v) ⟨σ_C⟩_{J(v)} dμ(v)` of
plaquette-form Z2 correlations over backgrounds `v` (see the module doc for what it asserts for SU(2)). -/
def PlaqMixture {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (J : Ω → LatticePlaquette d N → ℝ) (w : Ω → ℝ)
    (C : List (PathStep d N)) (W : ℝ) : Prop :=
  W = ∫ v, w v * corr plaqSupp (J v) (pathSupp C) ∂μ

/-- **Centre comparison plus strong-coupling Z2.** -/
theorem centre_area_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (J : Ω → LatticePlaquette d N → ℝ) (w : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ v, |w v| ≤ M)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ v p, |J v p| ≤ b)
    (hsmall : Real.exp b - 1 ≤ 1 / (4 * Real.exp (16 * d + 1) * (16 * d + 1) ^ 4))
    (x : FinLatticeSites d N) {μ' ν : Fin d} (hμν : μ' < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < N) (hTN : T < N) (W : ℝ)
    (hmix : PlaqMixture μ J w (rectPath x μ' ν R T) W) :
    |W| ≤ M * (Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp b - 1)) ^ (min (R * T) (N * N - R * T))) := by
  have h1 := comparison_integral plaqSupp μ J w M hw (fun _ => b) hb (pathSupp (rectPath x μ' ν R T)) W hmix
  have h2 := wilson_area_law_Z2 hb0 hsmall x hμν R T hR hT hRN hTN
  rw [wilsonRatio_Z2_eq_corr] at h2
  refine h1.trans (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) h2) hM)

/-- The bound of `centre_area_law` at `b = 2β`, `M = 2` is the repo's direct SU(2) bound. -/
theorem su2_bound_eq (β : ℝ) (R T : ℕ) :
    (2 : ℝ) * (Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp (2 * β) - 1)) ^ (min (R * T) (N * N - R * T))) =
      2 * Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp (2 * β) - 1)) ^ (min (R * T) (N * N - R * T)) := by
  ring

/-- **SU(2), bare level**: under the mixture hypothesis for the SU(2) Wilson measure with `|J(v)_p| ≤ 2β`
(`J_p = β Re tr V_p'`, `|Re tr| ≤ 2`) and `|w| ≤ 2`, the area law of the repo's strong-coupling range follows through the
Z2 model. -/
theorem su2_area_law_of_mixture {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → LatticePlaquette d N → ℝ) (w : Ω → ℝ) (hw : ∀ v, |w v| ≤ 2) (hr : ∀ v p, |r v p| ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.exp (2 * β) - 1 ≤ 1 / (4 * Real.exp (16 * d + 1) * (16 * d + 1) ^ 4))
    (x : FinLatticeSites d N) {μ' ν : Fin d} (hμν : μ' < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < N) (hTN : T < N)
    (hmix : (∫ U, wilsonLoop 2 (rectPath x μ' ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d N)) /
        (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d N)) =
        ∫ v, w v * corr plaqSupp (fun p => β * r v p) (pathSupp (rectPath x μ' ν R T)) ∂μ) :
    |(∫ U, wilsonLoop 2 (rectPath x μ' ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d N)) /
        (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d N))| ≤
      2 * Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp (2 * β) - 1)) ^ (min (R * T) (N * N - R * T)) := by
  have hb : ∀ v p, |β * r v p| ≤ 2 * β := fun v p => by
    rw [abs_mul, abs_of_nonneg hβ]; nlinarith [hr v p, abs_nonneg (r v p)]
  have := centre_area_law μ (fun v p => β * r v p) w 2 (by norm_num) hw (b := 2 * β) (by linarith) hb hsmall x hμν R T hR hT hRN hTN _
    hmix
  rw [← su2_bound_eq β R T]; exact this

end Combined

/-! ## Unit tests on a one-site toy model -/

section Toy

/-- One site, one interaction on it. -/
def toySupp : Unit → Multiset Unit := fun _ => ({()} : Multiset Unit)

theorem sum_unit_fun (f : (Unit → Bool) → ℝ) : ∑ σ : Unit → Bool, f σ = f (fun _ => false) + f (fun _ => true) := by
  rw [← Fintype.sum_equiv (Equiv.funUnique Unit Bool).symm (fun b : Bool => f (fun _ => b)) f (fun b => rfl),
    Fintype.sum_bool]
  simp [add_comm]

theorem corr_toy (j : ℝ) : corr toySupp (fun _ => j) ({()} : Multiset Unit) = Real.tanh j := by
  have hm : ∀ σ : Unit → Bool, mono σ ({()} : Multiset Unit) = sgn (σ ()) := fun σ => by simp [mono]
  have he : ∀ σ : Unit → Bool, energy toySupp (fun _ => j) σ = j * sgn (σ ()) := fun σ => by
    simp [energy, toySupp, mono]
  unfold corr num Zf
  simp_rw [hm, he]
  rw [sum_unit_fun, sum_unit_fun]
  simp only [sgn, Bool.false_eq_true, ite_false, ite_true]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have : j * -1 = -j := by ring
  rw [mul_one, this]
  have h2 : (Real.exp j + Real.exp (-j)) ≠ 0 := by positivity
  field_simp
  ring

/-- **Unit test, Z2 itself / sharpness.** A one-point mixture with ferromagnetic couplings attains the bound: the comparison
cannot be improved (the constant `1` and the worst-case coupling are optimal). -/
theorem comparison_sharp {κ ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (supp : κ → Multiset ι)
    (J : κ → ℝ) (hJ : ∀ k, 0 ≤ J k) (C : Multiset ι) :
    |corr supp J C| = corr supp J C := abs_of_nonneg (corr_nonneg supp hJ C)

/-- **Unit test, mixture.** A frustrated two-point mixture (`J = +a` and `J = -a`, equal weights) has `W = 0`, below the bound
`tanh |a|`, the value at the worst-case coupling. -/
theorem toy_mixture_cancels (a : ℝ) :
    (1 / 2 : ℝ) * corr toySupp (fun _ => a) ({()} : Multiset Unit) +
      (1 / 2 : ℝ) * corr toySupp (fun _ => -a) ({()} : Multiset Unit) = 0 ∧
    0 ≤ corr toySupp (fun _ => |a|) ({()} : Multiset Unit) := by
  refine ⟨?_, corr_nonneg toySupp (fun _ => abs_nonneg a) _⟩
  rw [corr_toy, corr_toy, Real.tanh_neg]; ring

/-- **Unit test, the sign-frustrated bound on the toy model**: `|tanh a| ≤ tanh |a|`. -/
theorem toy_abs_corr (a : ℝ) :
    |corr toySupp (fun _ => a) ({()} : Multiset Unit)| ≤ corr toySupp (fun _ => |a|) ({()} : Multiset Unit) :=
  abs_corr_le_abs toySupp (fun _ => a) _

/-- **Unit test, deconfinement.** On the toy model the worst-case bound is `tanh b ≥ 1 - 2 e^{-2b}` (and `< 1`): it tends to
`1` as `b → ∞`. When the worst-case effective coupling is large (the photon, the 2I vortex, a deconfined direction) the
comparison bound is empty. -/
theorem toy_vacuous (b : ℝ) :
    1 - 2 * Real.exp (-2 * b) ≤ corr toySupp (fun _ => b) ({()} : Multiset Unit) ∧
    corr toySupp (fun _ => b) ({()} : Multiset Unit) < 1 := by
  rw [corr_toy]
  refine ⟨?_, Real.tanh_lt_one b⟩
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, le_div_iff₀ (by positivity)]
  have hu : 0 < Real.exp (-b) := Real.exp_pos _
  have h2 : Real.exp (-2 * b) = Real.exp (-b) * Real.exp (-b) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : Real.exp b * Real.exp (-b) = 1 := by rw [← Real.exp_add]; simp
  rw [h2]
  nlinarith [pow_pos hu 3, h1]

/-- The bound is monotone in the worst-case coupling (`corr_mono`), so a larger `J̄` can only weaken the conclusion. -/
theorem toy_monotone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    corr toySupp (fun _ => a) ({()} : Multiset Unit) ≤ corr toySupp (fun _ => b) ({()} : Multiset Unit) :=
  corr_mono toySupp (fun _ => ha) (fun _ => hab) _

end Toy

end ProofPhase.Centre
