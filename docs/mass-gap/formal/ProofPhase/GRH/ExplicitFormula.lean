/-
The explicit formula, layer (b): Weil's explicit formula for zeta from one named classical input, the contour shift
(2026-11-23). Released under Apache 2.0.

Paper: `docs/unified/EXPLICIT-FORMULA.md`, section 3.
-/

import ProofPhase.GRH.ExplicitFormulaPrime

/-!
# Weil's explicit formula for `ζ`, from the contour shift

**Test functions.** `g : ℝ → ℂ` in log scale, continuous with compact support; its transform
`H(s) = ∫ g(x) e^{(s - 1/2) x} dx` (`laplace`). On the critical line `H(1/2 + i z) = ∫ g(x) e^{i z x} dx`, the transform the
ledger uses (`gridTest`, `weilSum`). `EFTest c g` adds the two integrability conditions the line integrals need on
`Re s = c` (they hold for `g ∈ C²_c` by two integrations by parts; not formalised here).

**The one named input, `ResidueShift` / `ContourShift`** (classical; Weil 1952, Iwaniec-Kowalski Thm 5.12): for the family
of nontrivial zeros `ρ` with multiplicity,
`(1/2πi) ∫_{(c)} (-Λ'/Λ) H - (1/2πi) ∫_{(1-c)} (-Λ'/Λ) H = H(1) + H(0) - ∑_ρ H(ρ)`, the zero sum converging absolutely.
This is the residue theorem on tall rectangles plus the vanishing of the horizontal sides along a sequence of heights
(needs zero counting and a bound for `Λ'/Λ` near the zeros; Mathlib has neither). Everything else is proved:

* `laplace_vpt`: `H` on the line `Re s = c` is the Fourier transform of the tilted test function;
* `laplace_one_sub`: `H_g(1 - s) = H_{g~}(s)`, `g~(x) = g(-x)`;
* `vline_reflect`: by the functional equation, the line `1 - c` is the line `c` of the reflected test function;
* `vline_wInt`: on the line `c > 1`, the integral is the prime sum minus half the real-place term (layer (a));
* **`explicit_formula`**: `∑_ρ H(ρ) = H(1) + H(0) - ∑ₙ Λ(n) n^{-1/2} (g(log n) + g(-log n)) + (A(g) + A(g~))/2`, with the
  real-place term `A(g) = (1/2πi) ∫_{(c)} (ψ(s/2) - log π) H(s) ds`;
* `explicit_formula_even`: for even `g`: `∑_ρ H(ρ) = H(1) + H(0) - 2 ∑ₙ Λ(n) n^{-1/2} g(log n) + A(g)`.

Standard axioms only.
-/

open Complex MeasureTheory FourierTransform
open scoped Real

noncomputable section

namespace ProofPhase.GRH.EF

/-! ### 1. The transform, the reflection, the line integral -/

/-- The transform of a test function in log scale, `H(s) = ∫ g(x) e^{(s - 1/2) x} dx`. -/
def laplace (g : ℝ → ℂ) (s : ℂ) : ℂ := ∫ x : ℝ, g x * Complex.exp ((s - 1 / 2) * x)

/-- The reflected test function `g~(x) = g(-x)`. -/
def refl (g : ℝ → ℂ) : ℝ → ℂ := fun x => g (-x)

/-- On the critical line the transform is the ledger's: `H(1/2 + i z) = ∫ g(x) e^{i z x} dx`. -/
theorem laplace_half (g : ℝ → ℂ) (z : ℂ) : laplace g (1 / 2 + I * z) = ∫ x : ℝ, g x * Complex.exp (I * z * x) := by
  simp only [laplace, add_sub_cancel_left]

/-- On the line `Re s = c`, `H` is the Fourier transform of `φ_c = g e^{(c - 1/2) x}`. -/
theorem laplace_vpt (c τ : ℝ) (g : ℝ → ℂ) : laplace g (vpt c τ) = 𝓕 (tilt c g) τ := by
  rw [Real.fourier_real_eq_integral_exp_smul, laplace]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [tilt, smul_eq_mul]
  rw [show (vpt c τ - 1 / 2) * (x : ℂ) = ((c - 1 / 2 : ℝ) : ℂ) * x + ↑(-2 * π * x * τ) * I by
    simp only [vpt]; push_cast; ring, Complex.exp_add]
  ring

/-- `H_g(1 - s) = H_{g~}(s)`. -/
theorem laplace_one_sub (g : ℝ → ℂ) (s : ℂ) : laplace g (1 - s) = laplace (refl g) s := by
  rw [laplace, laplace, ← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [refl]
  congr 2
  push_cast
  ring

/-- `refl` is an involution. -/
theorem refl_refl (g : ℝ → ℂ) : refl (refl g) = g := by
  funext x; simp [refl]

/-- The line integral `(1/2πi) ∫_{(c)} f(s) ds = ∫ f(c - 2πiτ) dτ`. -/
def vline (f : ℂ → ℂ) (c : ℝ) : ℂ := ∫ τ : ℝ, f (vpt c τ)

theorem vpt_one_sub (c τ : ℝ) : vpt (1 - c) τ = 1 - vpt c (-τ) := by
  simp only [vpt]; push_cast; ring

theorem vline_one_sub (f : ℂ → ℂ) (c : ℝ) : vline f (1 - c) = ∫ τ : ℝ, f (1 - vpt c τ) := by
  rw [vline]
  simp_rw [vpt_one_sub]
  exact integral_neg_eq_self (fun τ => f (1 - vpt c τ)) _

theorem vpt_ne_zero {c : ℝ} (hc : 1 < c) (τ : ℝ) : vpt c τ ≠ 0 := fun h => by
  have := congrArg Complex.re h; simp at this; linarith

theorem vpt_ne_one {c : ℝ} (hc : 1 < c) (τ : ℝ) : vpt c τ ≠ 1 := fun h => by
  have := congrArg Complex.re h; simp at this; linarith

/-! ### 2. The integrand `-Λ'/Λ · H` on the two lines -/

/-- The integrand of the explicit formula, `-Λ'/Λ (s) · H(s)` (`Λ` the completed zeta). -/
def wInt (g : ℝ → ℂ) : ℂ → ℂ := fun s => -logDeriv completedRiemannZeta s * laplace g s

/-- The functional equation moves the line `1 - c` to the line `c`, with the reflected test function. -/
theorem wInt_one_sub {c : ℝ} (hc : 1 < c) (g : ℝ → ℂ) (τ : ℝ) :
    wInt g (1 - vpt c τ) = -wInt (refl g) (vpt c τ) := by
  simp only [wInt]
  rw [logDeriv_completedZeta_one_sub (vpt_ne_zero hc τ) (vpt_ne_one hc τ), laplace_one_sub]
  ring

/-- **The reflection.** `(1/2πi) ∫_{(1-c)} (-Λ'/Λ) H_g = -(1/2πi) ∫_{(c)} (-Λ'/Λ) H_{g~}`. -/
theorem vline_reflect {c : ℝ} (hc : 1 < c) (g : ℝ → ℂ) : vline (wInt g) (1 - c) = -vline (wInt (refl g)) c := by
  rw [vline_one_sub, vline, ← integral_neg]
  exact integral_congr_ae (Filter.Eventually.of_forall fun τ => wInt_one_sub hc g τ)

/-- On the line `c > 1`: `-Λ'/Λ · H = L(Λ, ·) · H - (Γ_ℝ'/Γ_ℝ) · H`. -/
theorem wInt_vpt {c : ℝ} (hc : 1 < c) (g : ℝ → ℂ) (τ : ℝ) :
    wInt g (vpt c τ) = LSeries vM (vpt c τ) * 𝓕 (tilt c g) τ - logDeriv Gammaℝ (vpt c τ) * 𝓕 (tilt c g) τ := by
  have h1 : 1 < (vpt c τ).re := by simpa using hc
  simp only [wInt]
  rw [logDeriv_completedZeta h1, laplace_vpt, ← neg_logDeriv_zeta h1]
  ring

/-- **The test class on the line `c`**: continuous, compact support, and the two line integrals converge absolutely
(transform integrable; transform times the real-place weight integrable). -/
structure EFTest (c : ℝ) (g : ℝ → ℂ) : Prop where
  cont : Continuous g
  compact : HasCompactSupport g
  fourier : Integrable (𝓕 (tilt c g))
  arch : Integrable fun τ : ℝ => logDeriv Gammaℝ (vpt c τ) * 𝓕 (tilt c g) τ

/-- The trivial test function is admissible (the class is not empty; nontrivial members need decay, see the note). -/
theorem efTest_zero (c : ℝ) : EFTest c 0 := by
  have h0 : tilt c 0 = 0 := by funext x; simp [tilt]
  have hF : 𝓕 (tilt c 0) = 0 := by
    rw [h0]; funext τ; rw [Real.fourier_real_eq_integral_exp_smul]; simp
  exact ⟨continuous_const, HasCompactSupport.zero, by rw [hF]; exact integrable_zero _ _ _,
    by simp only [hF, Pi.zero_apply, mul_zero]; exact integrable_zero _ _ _⟩

theorem integrable_primeLine {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hT : EFTest c g) :
    Integrable fun τ : ℝ => LSeries vM (vpt c τ) * 𝓕 (tilt c g) τ :=
  (hT.fourier.norm.const_mul (∑' n, aw c n)).mono'
    ((continuous_LSeries_vM_vpt hc).aestronglyMeasurable.mul hT.fourier.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun τ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_LSeries_vM_vpt_le hc τ) (norm_nonneg _))

/-- The prime sum `∑ₙ Λ(n) n^{-1/2} g(log n)` (finitely many nonzero terms for compact support). -/
def primeSum (g : ℝ → ℂ) : ℂ := ∑' n : ℕ, (pw n : ℂ) * g (Real.log n)

/-- **The real-place term** `A(g) = (1/2πi) ∫_{(c)} (ψ(s/2) - log π) H(s) ds`. -/
def archTerm (c : ℝ) (g : ℝ → ℂ) : ℂ := vline (fun s => (digamma (s / 2) - Complex.log π) * laplace g s) c

theorem integral_arch {c : ℝ} (hc : 1 < c) (g : ℝ → ℂ) :
    ∫ τ : ℝ, logDeriv Gammaℝ (vpt c τ) * 𝓕 (tilt c g) τ = archTerm c g / 2 := by
  rw [archTerm, vline, ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  have h0 : 0 < (vpt c τ).re := by simp; linarith
  simp only
  rw [logDeriv_Gammaℝ h0, laplace_vpt]
  ring

/-- **The line `c > 1`.** `(1/2πi) ∫_{(c)} (-Λ'/Λ) H = ∑ₙ Λ(n) n^{-1/2} g(log n) - A(g)/2`. -/
theorem vline_wInt {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hT : EFTest c g) :
    vline (wInt g) c = primeSum g - archTerm c g / 2 := by
  rw [vline]
  simp_rw [wInt_vpt hc g]
  rw [integral_sub (integrable_primeLine hc hT) hT.arch, lineIntegral_primeSide hc hT.cont hT.compact hT.fourier,
    integral_arch hc, primeSum]

/-! ### 3. The named input and Weil's explicit formula -/

/-- **The contour shift for one family of points `ρ` (named hypothesis; classical for the nontrivial zeros).** The zero
sum converges, and `(1/2πi) ∫_{(c)} - (1/2πi) ∫_{(1-c)}` of `-Λ'/Λ · H` is the sum of the residues in the strip:
`H(1) + H(0)` from the poles of `Λ` at `1` and `0`, and `-H(ρ)` for each zero (with multiplicity). -/
def ResidueShift (c : ℝ) (g : ℝ → ℂ) {ι : Type} (ρ : ι → ℂ) : Prop :=
  Summable (fun i => laplace g (ρ i)) ∧
    vline (wInt g) c - vline (wInt g) (1 - c) = laplace g 1 + laplace g 0 - ∑' i, laplace g (ρ i)

/-- **The nontrivial zeros of `ζ` with multiplicity**, in the coordinate `ρ = 1/2 + i γ`: every member is a zero in the
open strip (the condition `StripZeros` of `TieIn.lean`), and each zero `z` of the strip occurs exactly
`ord_z ζ` times. -/
def NontrivialZeroFamily {ι : Type} (γ : ι → ℂ) : Prop :=
  (∀ i, 0 < (1 / 2 + I * γ i).re ∧ (1 / 2 + I * γ i).re < 1 ∧ riemannZeta (1 / 2 + I * γ i) = 0) ∧
    ∀ z : ℂ, 0 < z.re → z.re < 1 → {i | 1 / 2 + I * γ i = z}.encard = analyticOrderAt riemannZeta z

/-- **The contour shift (named classical hypothesis).** `ResidueShift` for every enumeration of the nontrivial zeros with
multiplicity. Classical for `g ∈ C²_c` (Weil 1952; Iwaniec-Kowalski, *Analytic Number Theory*, Thm 5.12 and its proof;
Davenport, *Multiplicative Number Theory*, ch. 17). Not in Mathlib: it needs the residue theorem on rectangles, the
zero count `N(T + 1) - N(T) = O(log T)` and the bound `Λ'/Λ(σ + iT) = ∑_{|γ - T| < 1} 1/(s - ρ) + O(log T)`. -/
def ContourShift (c : ℝ) (g : ℝ → ℂ) : Prop :=
  ∀ (ι : Type) (γ : ι → ℂ), NontrivialZeroFamily γ → ResidueShift c g (fun i => 1 / 2 + I * γ i)

/-- The right side of the explicit formula (poles, primes, real place). -/
def efRHS (c : ℝ) (g : ℝ → ℂ) : ℂ :=
  laplace g 1 + laplace g 0 - (primeSum g + primeSum (refl g)) + (archTerm c g + archTerm c (refl g)) / 2

/-- **Weil's explicit formula for `ζ`**, from the contour shift. For `c > 1` and `g`, `g~` admissible on the line `c`:
`∑_ρ H(ρ) = H(1) + H(0) - ∑ₙ Λ(n) n^{-1/2} (g(log n) + g(-log n)) + (A(g) + A(g~))/2`. -/
theorem explicit_formula {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hT : EFTest c g) (hT' : EFTest c (refl g))
    {ι : Type} {ρ : ι → ℂ} (hR : ResidueShift c g ρ) :
    Summable (fun i => laplace g (ρ i)) ∧ ∑' i, laplace g (ρ i) = efRHS c g := by
  refine ⟨hR.1, ?_⟩
  have h := hR.2
  rw [vline_reflect hc, vline_wInt hc hT, vline_wInt hc hT'] at h
  rw [efRHS]
  linear_combination h

/-- **The explicit formula for an even test function**:
`∑_ρ H(ρ) = H(1) + H(0) - 2 ∑ₙ Λ(n) n^{-1/2} g(log n) + A(g)`. -/
theorem explicit_formula_even {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hT : EFTest c g) (heven : ∀ x, g (-x) = g x)
    {ι : Type} {ρ : ι → ℂ} (hR : ResidueShift c g ρ) :
    ∑' i, laplace g (ρ i) = laplace g 1 + laplace g 0 - 2 * primeSum g + archTerm c g := by
  have hr : refl g = g := funext heven
  have h := (explicit_formula hc hT (by rw [hr]; exact hT) hR).2
  rw [efRHS, hr] at h
  rw [h]
  ring

/-- **The explicit formula for the nontrivial zeros**, in the ledger's coordinate: for an enumeration `γ` of the nontrivial
zeros with multiplicity and `g` satisfying the contour shift, `∑_γ ∫ g(x) e^{i γ x} dx = efRHS c g`. -/
theorem explicit_formula_zeros {c : ℝ} (hc : 1 < c) {g : ℝ → ℂ} (hT : EFTest c g) (hT' : EFTest c (refl g))
    (hCS : ContourShift c g) {ι : Type} {γ : ι → ℂ} (hZ : NontrivialZeroFamily γ) :
    Summable (fun i => ∫ x : ℝ, g x * Complex.exp (I * γ i * x)) ∧
      ∑' i, ∫ x : ℝ, g x * Complex.exp (I * γ i * x) = efRHS c g := by
  have h := explicit_formula hc hT hT' (hCS ι γ hZ)
  simp only [laplace_half] at h
  exact h

end ProofPhase.GRH.EF
