/-
Round 4, attempt r4-layer (attempt 2 of the act-identity-per-layer brief), 2026-11-21. Released under Apache 2.0.

# The electric-flux sector as a transfer-matrix sector

Note: `docs/mass-gap/weak-coupling/attempts/r4-layer/NOTE.md`, section 1.

Two levels.

**(A) Operator level, any probability space (covers SU(2)).** A transfer kernel `K ≥ 0`, bounded and measurable, on a probability
space `(X, ν)` defines `(T ψ)(x) = ∫ K(x, y) ψ(y) dν(y)`. A measure-preserving involution `σ` with `K(σx, σy) = K(x, y)` (the
centre transformation `Ω̂` of 't Hooft: multiply the links of one row by the centre element `z`, `z² = 1`) splits the bounded
measurable states into the vacuum sector (`ψ ∘ σ = ψ`, electric flux `e = 0`) and the flux sector (`ψ ∘ σ = −ψ`, `e = 1`).
Proved:
* `top_parity`: `T` preserves each sector (the sectors are invariant).
* `flux_bound_of_vacuum_bound`: every `L²` bound of `T` on the vacuum sector is one on the flux sector (`|Tψ| ≤ T|ψ|` because
  `K ≥ 0`, and `|ψ|` is a vacuum-sector state with the same norm). Hence `lamFlux ≤ lamVac` (`lamFlux_le_lamVac`) and the flux
  energy `fluxEnergy = log (lamVac / lamFlux) ≥ 0` (`fluxEnergy_nonneg`), where `lamVac`, `lamFlux` are the sector norms of `T`
  (the best constants, attained: `lamVac_mem`, `lamFlux_mem`).
* `flux_correlator_decay`: for a flux-sector state `ψ` and any bounded `φ`,
  `(∫ φ · Tⁿψ)² ≤ (lamVac^n · e^{−E_e n})² · ‖φ‖² ‖ψ‖²`: flux correlators decay like `e^{−E_e n}` relative to the vacuum growth
  (the time to live of the flux, `1/E_e`, the TTL of the act identity).
The class of states can be restricted by any predicate `Q` closed under `|·|` and preserved by `T` (gauge invariance: the Gauss law).

**(B) Trace level, finite configuration spaces (covers the finite gauge groups Z₂, Q8, 2T, 2O, 2I).** For a symmetric matrix `T`
with non-negative entries and a permutation `σ` commuting with it:
* `twist_centre_transform`: `Z = Z₀ + Z₁`, `Z_tw = Z₀ − Z₁` with `Z_e = (Z ± Z_tw)/2`, `Z = tr Tⁿ`, `Z_tw = tr(Ω̂ Tⁿ)`: the
  twisted (magnetic-flux) partition function is the centre (Fourier) transform of the electric-flux partition functions.
* `Ztw_nonneg`, `Zflux_nonneg` (even time extent), `Zvac_nonneg`, `Zflux_le_Zvac`: `0 ≤ Z₁ ≤ Z₀`, so `ρ = Z₁/Z₀ ∈ [0, 1]`.
* `freeFlux_nonneg`: the free-energy flux energy `F_e = −log(Z₁/Z₀) ≥ 0`.
* `freeFlux_eq_dual`: 't Hooft's duality on the finite lattice, `F_e = dual(F_m)` with `F_m = −log(Z_tw/Z)` and round 3's
  order-reversing involution `dual` (`Attempts.R3.Monotone.dual`); `dual_selfDual`: its unique fixed point is `log(1 + √2)`, where
  the electric and the magnetic free energy are equal.

Nothing here is specific to SU(2): every statement holds for every group with a central element of order 2 (the unit tests).
The identification of these objects with the 4D Wilson path integral (temporal gauge: `Z_Wilson = tr(P_G Tⁿ)`, `Z_tw = tr(Ω̂ P_G Tⁿ)`)
is standard (Osterwalder–Seiler 1978, Luescher 1977) and is not formalised; `LayerKernel.lean` proves the kernel properties of the
Wilson temporal-gauge kernel that (A) uses.
-/

import Mathlib
import Positivity.Abstract
import Attempts.R3.MonotoneCrossing

open MeasureTheory

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.R4.Layer

/-! ## (A) Operator level -/

section Operator

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]

/-- Bounded measurable states. -/
def BM (f : X → ℝ) : Prop := Measurable f ∧ ∃ M, ∀ x, |f x| ≤ M

theorem BM.integrable {f : X → ℝ} (hf : BM f) : Integrable f ν := by
  obtain ⟨hm, M, hM⟩ := hf
  exact (integrable_const M).mono' hm.aestronglyMeasurable (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hM x)

theorem BM.mul {f g : X → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x * g x) := by
  obtain ⟨hfm, M, hM⟩ := hf
  obtain ⟨hgm, M', hM'⟩ := hg
  refine ⟨hfm.mul hgm, M * M', fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hM x) (hM' x) (abs_nonneg _) ((abs_nonneg _).trans (hM x))

theorem BM.abs {f : X → ℝ} (hf : BM f) : BM (fun x => |f x|) :=
  ⟨hf.1.abs, hf.2.imp fun M hM x => by simpa using hM x⟩

theorem BM.sq {f : X → ℝ} (hf : BM f) : BM (fun x => f x ^ 2) := by
  simpa [pow_two] using hf.mul hf

theorem BM.const (c : ℝ) : BM (fun _ : X => c) := ⟨measurable_const, |c|, fun _ => le_rfl⟩

theorem BM.add {f g : X → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x + g x) := by
  obtain ⟨hfm, M, hM⟩ := hf
  obtain ⟨hgm, M', hM'⟩ := hg
  exact ⟨hfm.add hgm, M + M', fun x => (abs_add_le _ _).trans (add_le_add (hM x) (hM' x))⟩

theorem BM.const_mul {f : X → ℝ} (hf : BM f) (c : ℝ) : BM (fun x => c * f x) := (BM.const c).mul hf

/-- **Cauchy–Schwarz** for bounded measurable functions on a probability space. -/
theorem cs_int {f g : X → ℝ} (hf : BM f) (hg : BM g) :
    (∫ x, f x * g x ∂ν) ^ 2 ≤ (∫ x, f x ^ 2 ∂ν) * ∫ x, g x ^ 2 ∂ν := by
  apply Positivity.sq_le_mul_of_quadratic_nonneg
  intro t
  have i1 := hf.sq.integrable ν
  have i2 := (hf.mul hg).integrable ν
  have i3 := hg.sq.integrable ν
  have h0 : 0 ≤ ∫ x, (f x + t * g x) ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
  have e : ∫ x, (f x + t * g x) ^ 2 ∂ν =
      (∫ x, f x ^ 2 ∂ν) + (2 * t) * (∫ x, f x * g x ∂ν) + (t * t) * ∫ x, g x ^ 2 ∂ν := by
    calc ∫ x, (f x + t * g x) ^ 2 ∂ν
        = ∫ x, (f x ^ 2 + (2 * t) * (f x * g x) + (t * t) * g x ^ 2) ∂ν :=
          integral_congr_ae (ae_of_all _ fun x => by ring)
      _ = _ := by
          rw [integral_add, integral_add, integral_const_mul, integral_const_mul]
          · exact i1
          · exact i2.const_mul _
          · exact i1.add (i2.const_mul _)
          · exact i3.const_mul _
  rw [e] at h0
  linarith

/-- A transfer kernel: measurable, non-negative, bounded. -/
structure TKernel (X : Type*) [MeasurableSpace X] where
  K : X → X → ℝ
  meas : Measurable (Function.uncurry K)
  nonneg : ∀ x y, 0 ≤ K x y
  bound : ℝ
  le_bound : ∀ x y, K x y ≤ bound

variable (k : TKernel X)

/-- The transfer operator `(T ψ)(x) = ∫ K(x, y) ψ(y) dν(y)`. -/
def top (ψ : X → ℝ) : X → ℝ := fun x => ∫ y, k.K x y * ψ y ∂ν

/-- The squared `L²` norm. -/
def nrm (ψ : X → ℝ) : ℝ := ∫ x, ψ x ^ 2 ∂ν

theorem kernel_section_measurable (x : X) : Measurable (k.K x) :=
  k.meas.comp measurable_prodMk_left

theorem kernel_section_BM (x : X) : BM (k.K x) :=
  ⟨kernel_section_measurable k x, |k.bound|, fun y => by
    rw [abs_of_nonneg (k.nonneg x y)]; exact (k.le_bound x y).trans (le_abs_self _)⟩

theorem abs_top_le_const {ψ : X → ℝ} (hψ : BM ψ) (x : X) :
    |top ν k ψ x| ≤ |k.bound| * ∫ y, |ψ y| ∂ν := by
  unfold top
  calc |∫ y, k.K x y * ψ y ∂ν| ≤ ∫ y, |k.K x y * ψ y| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ y, |k.bound| * |ψ y| ∂ν := by
        apply integral_mono (((kernel_section_BM k x).mul hψ).abs.integrable ν) (hψ.abs.const_mul _ |>.integrable ν)
        intro y
        dsimp only
        rw [abs_mul, abs_of_nonneg (k.nonneg x y)]
        exact mul_le_mul_of_nonneg_right ((k.le_bound x y).trans (le_abs_self _)) (abs_nonneg _)
    _ = |k.bound| * ∫ y, |ψ y| ∂ν := integral_const_mul _ _

/-- `T` maps bounded measurable states to bounded measurable states. -/
theorem top_BM {ψ : X → ℝ} (hψ : BM ψ) : BM (top ν k ψ) := by
  refine ⟨?_, |k.bound| * ∫ y, |ψ y| ∂ν, abs_top_le_const ν k hψ⟩
  have hm : Measurable (Function.uncurry fun x y => k.K x y * ψ y) := k.meas.mul (hψ.1.comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

/-- **`|T ψ| ≤ T |ψ|`**, because the kernel is non-negative. -/
theorem abs_top_le (ψ : X → ℝ) (x : X) : |top ν k ψ x| ≤ top ν k (fun y => |ψ y|) x := by
  unfold top
  calc |∫ y, k.K x y * ψ y ∂ν| ≤ ∫ y, |k.K x y * ψ y| ∂ν := abs_integral_le_integral_abs
    _ = ∫ y, k.K x y * |ψ y| ∂ν := by
        congr 1; funext y; rw [abs_mul, abs_of_nonneg (k.nonneg x y)]

theorem nrm_top_le_abs {ψ : X → ℝ} (hψ : BM ψ) : nrm ν (top ν k ψ) ≤ nrm ν (top ν k (fun y => |ψ y|)) := by
  unfold nrm
  apply integral_mono ((top_BM ν k hψ).sq.integrable ν) ((top_BM ν k hψ.abs).sq.integrable ν)
  intro x
  have h := abs_le.mp (abs_top_le ν k ψ x)
  exact sq_le_sq' h.1 h.2

theorem nrm_abs (ψ : X → ℝ) : nrm ν (fun y => |ψ y|) = nrm ν ψ := by
  unfold nrm; congr 1; funext y; exact sq_abs _

/-- The crude bound: `‖T ψ‖² ≤ K_max² ‖ψ‖²`. -/
theorem nrm_top_le_bound {ψ : X → ℝ} (hψ : BM ψ) : nrm ν (top ν k ψ) ≤ |k.bound| ^ 2 * nrm ν ψ := by
  have hJ : (∫ y, |ψ y| ∂ν) ^ 2 ≤ nrm ν ψ := by
    have h := cs_int ν hψ.abs (BM.const (1 : ℝ))
    have h1 : ∫ _x, (1 : ℝ) ^ 2 ∂ν = 1 := by simp
    rw [h1, mul_one] at h
    simp only [mul_one, sq_abs] at h
    exact h
  unfold nrm at hJ ⊢
  calc ∫ x, top ν k ψ x ^ 2 ∂ν ≤ ∫ _x, (|k.bound| * ∫ y, |ψ y| ∂ν) ^ 2 ∂ν := by
        apply integral_mono ((top_BM ν k hψ).sq.integrable ν) (integrable_const _)
        intro x
        have h := abs_le.mp ((abs_top_le_const ν k hψ x))
        exact sq_le_sq' h.1 h.2
    _ = |k.bound| ^ 2 * (∫ y, |ψ y| ∂ν) ^ 2 := by simp [mul_pow]
    _ ≤ |k.bound| ^ 2 * ∫ x, ψ x ^ 2 ∂ν := mul_le_mul_of_nonneg_left hJ (sq_nonneg _)

/-! ### The centre symmetry and the flux sectors -/

/-- The centre transformation `Ω̂`: a measure-preserving involution that leaves the kernel invariant. -/
structure CentreSym (ν : Measure X) (k : TKernel X) where
  σ : X → X
  meas : Measurable σ
  invol : Function.Involutive σ
  pres : MeasurePreserving σ ν ν
  kinv : ∀ x y, k.K (σ x) (σ y) = k.K x y

variable {ν k}
variable (c : CentreSym ν k)

/-- `ψ` has centre charge `ε` (`ε = 1`: vacuum sector `e = 0`; `ε = −1`: flux sector `e = 1`). -/
def HasParity (ε : ℝ) (ψ : X → ℝ) : Prop := ∀ x, ψ (c.σ x) = ε * ψ x

/-- **The sectors are invariant:** `T` commutes with `Ω̂`. -/
theorem top_parity {ε : ℝ} {ψ : X → ℝ} (hψ : BM ψ) (h : HasParity c ε ψ) : HasParity c ε (top ν k ψ) := by
  intro x
  unfold top
  have hg : AEStronglyMeasurable (fun y => k.K (c.σ x) y * ψ y) ν :=
    ((kernel_section_measurable k (c.σ x)).mul hψ.1).aestronglyMeasurable
  rw [← Positivity.integral_comp_of_measurePreserving c.pres hg]
  rw [← integral_const_mul]
  congr 1; funext y
  rw [c.kinv, h y]; ring

theorem abs_parity_of_odd {ψ : X → ℝ} (h : HasParity c (-1) ψ) : HasParity c 1 (fun y => |ψ y|) := by
  intro x; simp [h x]

/-- The states of a sector: bounded measurable, in the class `Q`, with centre charge `ε`. -/
def Sec (Q : (X → ℝ) → Prop) (ε : ℝ) (ψ : X → ℝ) : Prop := BM ψ ∧ Q ψ ∧ HasParity c ε ψ

variable (ν k) in
/-- The admissible `L²` bounds of `T` on a class of states `P`. -/
def bounds (P : (X → ℝ) → Prop) : Set ℝ :=
  {lam | 0 ≤ lam ∧ ∀ ψ, P ψ → nrm ν (top ν k ψ) ≤ lam ^ 2 * nrm ν ψ}

/-- **E_e ≥ 0 at the operator level:** every vacuum-sector bound is a flux-sector bound. -/
theorem flux_bound_of_vacuum_bound (Q : (X → ℝ) → Prop) (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|)) {lam : ℝ}
    (h : lam ∈ bounds ν k (Sec c Q 1)) : lam ∈ bounds ν k (Sec c Q (-1)) := by
  refine ⟨h.1, fun ψ hψ => ?_⟩
  have habs : Sec c Q 1 (fun x => |ψ x|) := ⟨hψ.1.abs, hQ ψ hψ.2.1, abs_parity_of_odd c hψ.2.2⟩
  calc nrm ν (top ν k ψ) ≤ nrm ν (top ν k (fun y => |ψ y|)) := nrm_top_le_abs ν k hψ.1
    _ ≤ lam ^ 2 * nrm ν (fun y => |ψ y|) := h.2 _ habs
    _ = lam ^ 2 * nrm ν ψ := by rw [nrm_abs]

variable (ν k) in
theorem isClosed_bounds (P : (X → ℝ) → Prop) : IsClosed (bounds ν k P) := by
  have e : bounds ν k P = {lam : ℝ | 0 ≤ lam} ∩
      ⋂ ψ, ⋂ (_ : P ψ), {lam : ℝ | nrm ν (top ν k ψ) ≤ lam ^ 2 * nrm ν ψ} := by
    ext lam; simp [bounds]
  rw [e]
  exact (isClosed_le continuous_const continuous_id).inter
    (isClosed_iInter fun ψ => isClosed_iInter fun _ => isClosed_le continuous_const (by fun_prop))

variable (ν k) in
theorem bounds_nonempty (P : (X → ℝ) → Prop) (hP : ∀ ψ, P ψ → BM ψ) : (bounds ν k P).Nonempty :=
  ⟨|k.bound|, abs_nonneg _, fun ψ hψ => nrm_top_le_bound ν k (hP ψ hψ)⟩

variable (ν k) in
theorem bounds_bddBelow (P : (X → ℝ) → Prop) : BddBelow (bounds ν k P) := ⟨0, fun _ h => h.1⟩

/-- The sector norm of `T` on the vacuum sector (`e = 0`). -/
def lamVac (Q : (X → ℝ) → Prop) : ℝ := sInf (bounds ν k (Sec c Q 1))

/-- The sector norm of `T` on the flux sector (`e = 1`). -/
def lamFlux (Q : (X → ℝ) → Prop) : ℝ := sInf (bounds ν k (Sec c Q (-1)))

theorem sInf_bounds_mem (P : (X → ℝ) → Prop) (hP : ∀ ψ, P ψ → BM ψ) : sInf (bounds ν k P) ∈ bounds ν k P :=
  (isClosed_bounds ν k P).csInf_mem (bounds_nonempty ν k P hP) (bounds_bddBelow ν k P)

/-- The vacuum sector norm is attained (it is a bound). -/
theorem lamVac_mem (Q : (X → ℝ) → Prop) : lamVac c Q ∈ bounds ν k (Sec c Q 1) :=
  sInf_bounds_mem _ fun _ h => h.1

/-- The flux sector norm is attained (it is a bound). -/
theorem lamFlux_mem (Q : (X → ℝ) → Prop) : lamFlux c Q ∈ bounds ν k (Sec c Q (-1)) :=
  sInf_bounds_mem _ fun _ h => h.1

/-- **The flux sector lies below the vacuum sector:** `lamFlux ≤ lamVac`. -/
theorem lamFlux_le_lamVac (Q : (X → ℝ) → Prop) (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|)) : lamFlux c Q ≤ lamVac c Q :=
  csInf_le_csInf (bounds_bddBelow ν k _) (bounds_nonempty ν k _ fun _ h => h.1)
    (fun _ h => flux_bound_of_vacuum_bound c Q hQ h)

/-- **The flux energy** `E_e = log(lamVac / lamFlux)`: the gap of the flux sector relative to the vacuum sector, per time step. -/
def fluxEnergy (Q : (X → ℝ) → Prop) : ℝ := Real.log (lamVac c Q / lamFlux c Q)

/-- **`E_e ≥ 0`.** -/
theorem fluxEnergy_nonneg (Q : (X → ℝ) → Prop) (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|)) : 0 ≤ fluxEnergy c Q := by
  unfold fluxEnergy
  have hle := lamFlux_le_lamVac c Q hQ
  rcases (lamFlux_mem c Q).1.eq_or_lt with h0 | hpos
  · rw [← h0, div_zero, Real.log_zero]
  · exact Real.log_nonneg ((one_le_div hpos).mpr hle)

/-- With a positive flux norm, `lamFlux = lamVac · e^{−E_e}`. -/
theorem lamFlux_eq (Q : (X → ℝ) → Prop) (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|)) (hpos : 0 < lamFlux c Q) :
    lamFlux c Q = lamVac c Q * Real.exp (-fluxEnergy c Q) := by
  have hv : 0 < lamVac c Q := hpos.trans_le (lamFlux_le_lamVac c Q hQ)
  unfold fluxEnergy
  rw [Real.exp_neg, Real.exp_log (div_pos hv hpos)]
  field_simp

/-- Iterating `T` inside a sector. -/
theorem sec_iterate (Q : (X → ℝ) → Prop) (hQT : ∀ ψ, BM ψ → Q ψ → Q (top ν k ψ)) {ε : ℝ} {ψ : X → ℝ}
    (hψ : Sec c Q ε ψ) (n : ℕ) : Sec c Q ε ((top ν k)^[n] ψ) := by
  induction n with
  | zero => simpa using hψ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨top_BM ν k ih.1, hQT _ ih.1 ih.2.1, top_parity c ih.1 ih.2.2⟩

/-- **Decay inside a sector:** a bound `lam` on the sector gives `‖Tⁿψ‖² ≤ lam^{2n} ‖ψ‖²`. -/
theorem sector_decay (Q : (X → ℝ) → Prop) (hQT : ∀ ψ, BM ψ → Q ψ → Q (top ν k ψ)) {ε lam : ℝ}
    (hlam : lam ∈ bounds ν k (Sec c Q ε)) {ψ : X → ℝ} (hψ : Sec c Q ε ψ) (n : ℕ) :
    nrm ν ((top ν k)^[n] ψ) ≤ (lam ^ 2) ^ n * nrm ν ψ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    calc nrm ν (top ν k ((top ν k)^[n] ψ)) ≤ lam ^ 2 * nrm ν ((top ν k)^[n] ψ) :=
          hlam.2 _ (sec_iterate c Q hQT hψ n)
      _ ≤ lam ^ 2 * ((lam ^ 2) ^ n * nrm ν ψ) := mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = _ := by ring

/-- **The flux sector's time to live.** For every bounded `φ` and every flux-sector state `ψ`,
    `(∫ φ · Tⁿψ)² ≤ (lamVac^n · e^{−E_e n})² · ‖φ‖² · ‖ψ‖²`: relative to the vacuum growth `lamVac^n`, flux correlators decay
    like `e^{−E_e n}`. -/
theorem flux_correlator_decay (Q : (X → ℝ) → Prop) (hQ : ∀ ψ, Q ψ → Q (fun x => |ψ x|))
    (hQT : ∀ ψ, BM ψ → Q ψ → Q (top ν k ψ)) {φ ψ : X → ℝ} (hφ : BM φ) (hψ : Sec c Q (-1) ψ) (n : ℕ) :
    (∫ x, φ x * (top ν k)^[n] ψ x ∂ν) ^ 2 ≤
      ((lamVac c Q) ^ n * Real.exp (-(fluxEnergy c Q * n))) ^ 2 * nrm ν φ * nrm ν ψ := by
  have hcs := cs_int ν hφ (sec_iterate c Q hQT hψ n).1
  have hdec := sector_decay c Q hQT (lamFlux_mem c Q) hψ n
  have hφ0 : 0 ≤ nrm ν φ := integral_nonneg fun x => sq_nonneg _
  have hψ0 : 0 ≤ nrm ν ψ := integral_nonneg fun x => sq_nonneg _
  have key : (lamFlux c Q ^ 2) ^ n ≤ ((lamVac c Q) ^ n * Real.exp (-(fluxEnergy c Q * n))) ^ 2 := by
    have hexp : Real.exp (-(fluxEnergy c Q * n)) = Real.exp (-fluxEnergy c Q) ^ n := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rcases (lamFlux_mem c Q).1.eq_or_lt with h0 | hpos
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · rw [← h0, zero_pow two_ne_zero, zero_pow (by omega)]; positivity
    · rw [lamFlux_eq c Q hQ hpos, hexp]; apply le_of_eq; ring
  calc (∫ x, φ x * (top ν k)^[n] ψ x ∂ν) ^ 2 ≤ nrm ν φ * nrm ν ((top ν k)^[n] ψ) := by
        simpa only [nrm] using hcs
    _ ≤ nrm ν φ * ((lamFlux c Q ^ 2) ^ n * nrm ν ψ) := mul_le_mul_of_nonneg_left hdec hφ0
    _ ≤ nrm ν φ * (((lamVac c Q) ^ n * Real.exp (-(fluxEnergy c Q * n))) ^ 2 * nrm ν ψ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right key hψ0) hφ0
    _ = _ := by ring

end Operator

/-! ## (B) Trace level: finite configuration spaces -/

section Trace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℝ) (σ : ι ≃ ι)

/-- The periodic partition function `Z(n) = tr Tⁿ` (time extent `n`). -/
def Zper (n : ℕ) : ℝ := (T ^ n).trace

/-- The twisted partition function `Z_tw(n) = tr(Ω̂ Tⁿ)`: one insertion of the centre transformation, i.e. one twisted sheet. -/
def Ztw (n : ℕ) : ℝ := ∑ i, (T ^ n) i (σ i)

/-- The electric-flux partition functions `Z_e(n) = tr(P_e Tⁿ)`, `P_e = (1 ± Ω̂)/2`; `ε = 1` is `e = 0`, `ε = −1` is `e = 1`. -/
def Zsec (ε : ℝ) (n : ℕ) : ℝ := (Zper T n + ε * Ztw T σ n) / 2

/-- **Electric–magnetic duality on the finite lattice, exact:** the twisted partition function is the centre (Fourier) transform
    of the electric-flux partition functions, `Z = Z₀ + Z₁`, `Z_tw = Z₀ − Z₁`. -/
theorem twist_centre_transform (n : ℕ) :
    Zper T n = Zsec T σ 1 n + Zsec T σ (-1) n ∧ Ztw T σ n = Zsec T σ 1 n - Zsec T σ (-1) n := by
  constructor <;> simp only [Zsec] <;> ring

theorem pow_entries_nonneg (h : ∀ i j, 0 ≤ T i j) (n : ℕ) : ∀ i j, 0 ≤ (T ^ n) i j := by
  induction n with
  | zero => intro i j; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    intro i j; rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (ih i k) (h k j)

theorem pow_sigma (hσ : ∀ i j, T (σ i) (σ j) = T i j) (n : ℕ) : ∀ i j, (T ^ n) (σ i) (σ j) = (T ^ n) i j := by
  induction n with
  | zero => intro i j; simp [Matrix.one_apply, σ.injective.eq_iff]
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply, Matrix.mul_apply, ← Equiv.sum_comp σ]
    exact Finset.sum_congr rfl fun k _ => by rw [ih, hσ]

/-- `Z_tw ≥ 0`: the twisted partition function is a sum of non-negative weights. -/
theorem Ztw_nonneg (h : ∀ i j, 0 ≤ T i j) (n : ℕ) : 0 ≤ Ztw T σ n :=
  Finset.sum_nonneg fun i _ => pow_entries_nonneg T h n i (σ i)

/-- The key identity: `2 (Z − Z_tw)` at even time extent is a sum of squares. -/
theorem two_mul_Zper_sub_Ztw (hT : T.transpose = T) (m : ℕ) :
    2 * (Zper T (2 * m) - Ztw T σ (2 * m)) = ∑ i, ∑ j, ((T ^ m) i j - (T ^ m) (σ i) j) ^ 2 := by
  set A := T ^ m with hA
  have hAs : ∀ i j, A j i = A i j := by
    intro i j
    have : A.transpose = A := by rw [hA, Matrix.transpose_pow, hT]
    exact congrFun (congrFun this i) j
  have hpow : T ^ (2 * m) = A * A := by rw [hA, two_mul, pow_add]
  have e1 : Zper T (2 * m) = ∑ i, ∑ j, A i j * A i j := by
    unfold Zper; rw [hpow, Matrix.trace]; simp only [Matrix.diag, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hAs i j]
  have e2 : Ztw T σ (2 * m) = ∑ i, ∑ j, A i j * A (σ i) j := by
    unfold Ztw; rw [hpow]; simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hAs (σ i) j]
  have e3 : ∑ i, ∑ j, A (σ i) j * A (σ i) j = ∑ i, ∑ j, A i j * A i j :=
    Equiv.sum_comp σ (fun i => ∑ j, A i j * A i j)
  have e4 : ∑ i, ∑ j, (A i j - A (σ i) j) ^ 2 =
      ∑ i, ∑ j, A i j * A i j + ∑ i, ∑ j, A (σ i) j * A (σ i) j - 2 * ∑ i, ∑ j, A i j * A (σ i) j := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e4, e3, e1, e2]; ring

/-- `Z₁ ≥ 0` (the flux sector) at even time extent. -/
theorem Zflux_nonneg (hT : T.transpose = T) (m : ℕ) :
    0 ≤ Zsec T σ (-1) (2 * m) := by
  have h := two_mul_Zper_sub_Ztw T σ hT m
  have : 0 ≤ ∑ i, ∑ j, ((T ^ m) i j - (T ^ m) (σ i) j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  unfold Zsec; linarith

/-- `Z₁ ≤ Z₀`: the flux sector never outweighs the vacuum sector (`ρ ≤ 1`), because `Z_tw ≥ 0`. -/
theorem Zflux_le_Zvac (h : ∀ i j, 0 ≤ T i j) (n : ℕ) : Zsec T σ (-1) n ≤ Zsec T σ 1 n := by
  have := Ztw_nonneg T σ h n
  unfold Zsec; linarith

/-- `Z₀ ≥ 0`. -/
theorem Zvac_nonneg (hT : T.transpose = T) (h : ∀ i j, 0 ≤ T i j) (m : ℕ) :
    0 ≤ Zsec T σ 1 (2 * m) :=
  (Zflux_nonneg T σ hT m).trans (Zflux_le_Zvac T σ h _)

/-- The free-energy flux energy `F_e = −log(Z₁/Z₀)` (for a long time extent `n`, `F_e ≈ E_e · n`). -/
def freeFlux (n : ℕ) : ℝ := -Real.log (Zsec T σ (-1) n / Zsec T σ 1 n)

/-- The magnetic (twist) free energy `F_m = −log(Z_tw/Z)`. -/
def freeTwist (n : ℕ) : ℝ := -Real.log (Ztw T σ n / Zper T n)

/-- **`F_e ≥ 0`** at even time extent. -/
theorem freeFlux_nonneg (hT : T.transpose = T) (h : ∀ i j, 0 ≤ T i j) (m : ℕ) :
    0 ≤ freeFlux T σ (2 * m) := by
  unfold freeFlux
  rw [neg_nonneg]
  apply Real.log_nonpos (div_nonneg (Zflux_nonneg T σ hT m) (Zvac_nonneg T σ hT h m))
  rcases (Zvac_nonneg T σ hT h m).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero]; norm_num
  · exact (div_le_one hpos).mpr (Zflux_le_Zvac T σ h _)

/-- **'t Hooft's duality, exact on the finite lattice:** `F_e = dual(F_m)`, with round 3's order-reversing involution
    `dual(x) = −log((1 − e^{−x})/(1 + e^{−x}))` (`Attempts.R3.Monotone.dual`). -/
theorem freeFlux_eq_dual (n : ℕ) (hZ : 0 < Zper T n) (htw : 0 < Ztw T σ n) :
    freeFlux T σ n = Attempts.R3.Monotone.dual (freeTwist T σ n) := by
  unfold freeFlux freeTwist Attempts.R3.Monotone.dual
  rw [neg_neg, Real.exp_log (div_pos htw hZ)]
  congr 2
  unfold Zsec
  field_simp
  ring

/-- **The self-dual point of the duality** is `log(1 + √2)`: the one value at which the electric and the magnetic free energies are
    equal. -/
theorem dual_selfDual : Attempts.R3.Monotone.dual (Real.log (1 + Real.sqrt 2)) = Real.log (1 + Real.sqrt 2) := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have hpos : 0 < 1 + Real.sqrt 2 := by positivity
  unfold Attempts.R3.Monotone.dual
  rw [Real.exp_neg, Real.exp_log hpos]
  have e : (1 - (1 + Real.sqrt 2)⁻¹) / (1 + (1 + Real.sqrt 2)⁻¹) = (1 + Real.sqrt 2)⁻¹ := by
    field_simp
    nlinarith [hs]
  rw [e, Real.log_inv, neg_neg]

end Trace

end Attempts.R4.Layer
