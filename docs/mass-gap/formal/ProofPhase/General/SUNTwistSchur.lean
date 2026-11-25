/-
SU(N) primes round (sun-primes): Schur's lemma for the SU(N) plaquette factor and the centre twists `ω^k`
(2026-11-23). Released under Apache 2.0.

Note: `docs/unified/SUN-PRIMES.md`, section 2.
-/

import ProofPhase.General.SUNTwist
import ProofPhase.General.Centre

/-!
# Schur's lemma on SU(N), and the centre twists

**1. Schur's lemma for the plaquette factor (`schur_SUN`).** For every `N ≥ 1`, every real `β` and every `M ∈ SU(N)`:
`∫ e^{β Re tr v} Re tr(v M) dv = λ_N(β) Re tr M` (Haar measure), with
`λ_N(β) = Re ∫ e^{β Re tr v} v₀₀ dv`. Proof: the matrix `S = ∫ e^{β Re tr v} v dv` commutes with conjugation by SU(N)
(Haar measure and the class function are conjugation invariant). Conjugating by `diag(i, −i, 1, …)` (in SU(N)) kills
the off-diagonal entries (`schurM_offdiag`); conjugating by a signed transposition (in SU(N)) equates the diagonal
entries (`schurM_diag`). Inversion `v ↦ v⁻¹ = v*` makes `S₀₀` real (`schurM_im`). This generalises `schur_SU2` of
`ProofPhase.Flip.Strict` (where the off-diagonal step used the explicit 2 × 2 form).

**2. `λ_N(β) ≠ 0` for `β ≠ 0`, `N ≥ 2` (`schurC_ne_zero_SUN`).** `∫ Re tr v dv = 0` because the centre element
`ω = e^{2πi/N} ≠ 1` multiplies the trace (`integral_trN_eq_zero`), and `β N λ_N(β) = ∫ (e^{β t} − 1) β t > 0`,
`t = Re tr v`, since the integrand is continuous, nonnegative and positive at `v = 1`.

**3. The centre twists (`zN`).** For `k ∈ ZMod N`, `zN k = ψ(k) · 1 ∈ SU(N)` with `ψ(k) = e^{2πi k/N}` the standard
additive character (Mathlib's `ZMod.stdAddChar`): central, `zN (k + l) = zN k · zN l`, `zN 0 = 1`, and
`Re tr (zN k) = N cos(2πk/N) ≠ N` for `k ≠ 0` (`reTr_zN_ne`).

**Claim discipline.** Classical facts (Schur's lemma, orthogonality of the centre), formalised here for every `N`.
-/

open MeasureTheory Finset Positivity AreaLaw.Concrete ProofPhase.RouteB ProofPhase.Flip

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section SchurSUN

variable {N : ℕ}

instance instOpenPosHaarSUN (N : ℕ) : (haarG (SUN N)).IsOpenPosMeasure := by
  show (Measure.haarMeasure ⊤).IsOpenPosMeasure; infer_instance

instance instHaarRightSUN (N : ℕ) : (haarG (SUN N)).IsMulRightInvariant := by
  show (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (SUN N))).IsMulRightInvariant
  have := isProbabilityMeasure_haarMeasure_top (G := SUN N)
  exact isMulRightInvariant_of_compact _

theorem continuous_trN : Continuous (gaugeReTr (SUN N) N) := continuous_gaugeReTr continuous_subtype_val

theorem trN_one : gaugeReTr (SUN N) N 1 = N := by simp [gaugeReTr, gaugeTrace]

theorem gaugeTrace_SUN (v : SUN N) : gaugeTrace (SUN N) N v = Matrix.trace (v : Matrix (Fin N) (Fin N) ℂ) := rfl

/-- The SU(N) plaquette factor `e^{β Re tr u}`. -/
def bwN (β : ℝ) (u : SUN N) : ℝ := Real.exp (β * gaugeReTr (SUN N) N u)

theorem continuous_bwN (β : ℝ) : Continuous (bwN (N := N) β) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_trN)

theorem bwN_pos (β : ℝ) (u : SUN N) : 0 < bwN β u := Real.exp_pos _

theorem bwN_conj (β : ℝ) (h v : SUN N) : bwN β (h * v * h⁻¹) = bwN β v := by unfold bwN; rw [gaugeReTr_conj]

theorem bwN_inv (β : ℝ) (v : SUN N) : bwN β v⁻¹ = bwN β v := by
  unfold bwN
  rw [gaugeReTr_inv_of_unitary (fun g : SUN N => Matrix.specialUnitaryGroup_le_unitaryGroup g.2)]

theorem continuous_entryN (i j : Fin N) : Continuous fun v : SUN N => (v : Matrix (Fin N) (Fin N) ℂ) i j :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

theorem continuous_bwEntryN (β : ℝ) (i j : Fin N) :
    Continuous fun v : SUN N => (bwN β v : ℂ) * (v : Matrix (Fin N) (Fin N) ℂ) i j :=
  (Complex.continuous_ofReal.comp (continuous_bwN β)).mul (continuous_entryN i j)

/-- The entries of the matrix `S = ∫ e^{β Re tr v} v dv`. -/
def schurM (β : ℝ) (i j : Fin N) : ℂ :=
  ∫ v, (bwN β v : ℂ) * (v : Matrix (Fin N) (Fin N) ℂ) i j ∂(haarG (SUN N))

theorem schurM_conj (β : ℝ) (h : SUN N) (i j : Fin N) :
    ∫ v, (bwN β v : ℂ) * ((h * v * h⁻¹ : SUN N) : Matrix (Fin N) (Fin N) ℂ) i j ∂(haarG (SUN N)) = schurM β i j := by
  have hmp : MeasurePreserving (fun v : SUN N => h * v * h⁻¹) (haarG (SUN N)) (haarG (SUN N)) :=
    (measurePreserving_mul_right (haarG (SUN N)) h⁻¹).comp (measurePreserving_mul_left (haarG (SUN N)) h)
  have := integral_comp_of_measurePreserving hmp
    (g := fun v : SUN N => (bwN β v : ℂ) * (v : Matrix (Fin N) (Fin N) ℂ) i j)
    (continuous_bwEntryN β i j).aestronglyMeasurable
  unfold schurM
  refine Eq.trans ?_ this
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [bwN_conj]

theorem coe_conj (h v : SUN N) :
    ((h * v * h⁻¹ : SUN N) : Matrix (Fin N) (Fin N) ℂ) =
      (h : Matrix (Fin N) (Fin N) ℂ) * v * star (h : Matrix (Fin N) (Fin N) ℂ) := rfl

/-! ### The diagonal element `diag(i, −i, 1, …)` -/

/-- The diagonal of `diag(i, −i, 1, …)`: `i` at `a`, `−i` at `b`. -/
def dIJ (a b : Fin N) (x : Fin N) : ℂ := (if x = a then Complex.I else 1) * (if x = b then -Complex.I else 1)

theorem dIJ_mul_star (a b : Fin N) (x : Fin N) : dIJ a b x * star (dIJ a b x) = 1 := by
  unfold dIJ
  split_ifs <;> simp [Complex.ext_iff]

theorem mem_dIJ {a b : Fin N} (hab : a ≠ b) :
    Matrix.diagonal (dIJ a b) ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨Matrix.mem_unitaryGroup_iff.2 ?_, ?_⟩
  · rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext x
    exact dIJ_mul_star a b x
  · rw [Matrix.det_diagonal]
    unfold dIJ
    rw [prod_mul_distrib, prod_ite_eq', prod_ite_eq']
    simp

/-- `diag(i, −i, 1, …) ∈ SU(N)`. -/
def suDN {a b : Fin N} (hab : a ≠ b) : SUN N := ⟨Matrix.diagonal (dIJ a b), mem_dIJ hab⟩

theorem suDN_conj {a b : Fin N} (hab : a ≠ b) (v : SUN N) :
    ((suDN hab * v * (suDN hab)⁻¹ : SUN N) : Matrix (Fin N) (Fin N) ℂ) a b =
      -(v : Matrix (Fin N) (Fin N) ℂ) a b := by
  rw [coe_conj]
  show (Matrix.diagonal (dIJ a b) * (v : Matrix (Fin N) (Fin N) ℂ) * star (Matrix.diagonal (dIJ a b))) a b = _
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp [dIJ, hab, hab.symm, Complex.conj_I]
  linear_combination ((v : Matrix (Fin N) (Fin N) ℂ) a b) * Complex.I_sq

/-! ### The signed transposition -/

/-- The sign vector `(−1 at a, 1 elsewhere)`. -/
def sIJ (a : Fin N) (x : Fin N) : ℂ := if x = a then -1 else 1

theorem sIJ_mul_star (a : Fin N) (x : Fin N) : sIJ a x * star (sIJ a x) = 1 := by
  unfold sIJ; split_ifs <;> simp

/-- The signed transposition `diag(s) · P_{(a b)}`. -/
def rIJ (a b : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (sIJ a) * (Equiv.swap a b).permMatrix ℂ

theorem rIJ_star (a b : Fin N) :
    star (rIJ a b) = ((Equiv.swap a b)⁻¹).permMatrix ℂ * Matrix.diagonal (star (sIJ a)) := by
  unfold rIJ
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_permMatrix,
    Matrix.diagonal_conjTranspose]

theorem mem_rIJ {a b : Fin N} (hab : a ≠ b) : rIJ a b ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨Matrix.mem_unitaryGroup_iff.2 ?_, ?_⟩
  · rw [rIJ_star]
    unfold rIJ
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((Equiv.swap a b).permMatrix ℂ), ← Matrix.permMatrix_mul,
      inv_mul_cancel, Matrix.permMatrix_one, Matrix.one_mul, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext x
    exact sIJ_mul_star a x
  · unfold rIJ
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation, Equiv.Perm.sign_swap hab]
    unfold sIJ
    rw [prod_ite_eq']
    simp

/-- The signed transposition as an element of SU(N). -/
def suRN {a b : Fin N} (hab : a ≠ b) : SUN N := ⟨rIJ a b, mem_rIJ hab⟩

theorem suRN_conj {a b : Fin N} (hab : a ≠ b) (v : SUN N) :
    ((suRN hab * v * (suRN hab)⁻¹ : SUN N) : Matrix (Fin N) (Fin N) ℂ) a a = (v : Matrix (Fin N) (Fin N) ℂ) b b := by
  rw [coe_conj]
  show (rIJ a b * (v : Matrix (Fin N) (Fin N) ℂ) * star (rIJ a b)) a a = _
  rw [rIJ_star]
  unfold rIJ
  have e : Matrix.diagonal (sIJ a) * (Equiv.swap a b).permMatrix ℂ * (v : Matrix (Fin N) (Fin N) ℂ) *
      (((Equiv.swap a b)⁻¹).permMatrix ℂ * Matrix.diagonal (star (sIJ a))) =
      Matrix.diagonal (sIJ a) * ((Equiv.swap a b).permMatrix ℂ * (v : Matrix (Fin N) (Fin N) ℂ) *
        ((Equiv.swap a b)⁻¹).permMatrix ℂ) * Matrix.diagonal (star (sIJ a)) := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_apply, id, Equiv.swap_inv, Equiv.symm_swap, Equiv.swap_apply_left, Pi.star_apply]
  simp [sIJ]

/-! ### Schur's lemma -/

theorem schurM_offdiag (β : ℝ) {a b : Fin N} (hab : a ≠ b) : schurM β a b = 0 := by
  have h := schurM_conj β (suDN hab) a b
  simp_rw [suDN_conj hab, mul_neg, integral_neg] at h
  change -schurM β a b = schurM β a b at h
  linear_combination (-1 / 2 : ℂ) * h

theorem schurM_diag (β : ℝ) (a b : Fin N) : schurM β a a = schurM β b b := by
  by_cases hab : a = b
  · rw [hab]
  · have h := schurM_conj β (suRN hab) a a
    simp_rw [suRN_conj hab] at h
    exact h.symm

theorem integrable_bwEntryN (β : ℝ) (i j : Fin N) :
    Integrable (fun v : SUN N => (bwN β v : ℂ) * (v : Matrix (Fin N) (Fin N) ℂ) i j) (haarG (SUN N)) :=
  integrable_of_continuous (continuous_bwEntryN β i j)

/-- The diagonal entries of `S` are real (inversion `v ↦ v⁻¹ = v*`). -/
theorem schurM_im (β : ℝ) (a : Fin N) : (schurM β a a).im = 0 := by
  have h1 : schurM β a a = ∫ v, (bwN β v⁻¹ : ℂ) * ((v⁻¹ : SUN N) : Matrix (Fin N) (Fin N) ℂ) a a ∂(haarG (SUN N)) :=
    (integral_inv_eq_self (fun v : SUN N => (bwN β v : ℂ) * (v : Matrix (Fin N) (Fin N) ℂ) a a)
      (haarG (SUN N))).symm
  have h2 : ∀ v : SUN N, (bwN β v⁻¹ : ℂ) * ((v⁻¹ : SUN N) : Matrix (Fin N) (Fin N) ℂ) a a =
      (starRingEnd ℂ) ((bwN β v : ℂ) * (v : Matrix (Fin N) (Fin N) ℂ) a a) := by
    intro v
    rw [bwN_inv, map_mul, Complex.conj_ofReal]
    congr 1
  simp_rw [h2, integral_conj] at h1
  have h3 := congrArg Complex.im h1
  rw [Complex.conj_im] at h3
  unfold schurM at h3 ⊢
  linarith

variable [NeZero N]

/-- **The Schur constant** `λ_N(β) = Re ∫ e^{β Re tr v} v₀₀ dv`. -/
def schurCN (β : ℝ) : ℝ := (schurM (N := N) β 0 0).re

theorem schurM_eq (β : ℝ) (a : Fin N) : schurM β a a = (schurCN (N := N) β : ℂ) := by
  rw [schurM_diag β a 0]
  exact Complex.ext rfl (by rw [schurM_im, Complex.ofReal_im])

theorem integral_bwN_tr_mul (β : ℝ) (M : Matrix (Fin N) (Fin N) ℂ) :
    ∫ v, bwN β v * (Matrix.trace ((v : Matrix (Fin N) (Fin N) ℂ) * M)).re ∂(haarG (SUN N)) =
      schurCN (N := N) β * (Matrix.trace M).re := by
  let t : Fin N → Fin N → SUN N → ℂ := fun i k v => (bwN β v : ℂ) * (v : Matrix (Fin N) (Fin N) ℂ) i k * M k i
  have it : ∀ i k, Integrable (t i k) (haarG (SUN N)) := fun i k => (integrable_bwEntryN β i k).mul_const _
  have e : ∀ v : SUN N, bwN β v * (Matrix.trace ((v : Matrix (Fin N) (Fin N) ℂ) * M)).re =
      Complex.reCLM (∑ i, ∑ k, t i k v) := by
    intro v
    rw [Complex.reCLM_apply, ← Complex.re_ofReal_mul, Matrix.trace, mul_sum]
    simp only [Matrix.diag, Matrix.mul_apply, mul_sum, t]
    congr 1
    refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
    ring
  simp_rw [e]
  rw [ContinuousLinearMap.integral_comp_comm Complex.reCLM (integrable_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun k _ => it i k)]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => it i k]
  have hi : ∀ i k, ∫ v, t i k v ∂(haarG (SUN N)) = schurM β i k * M k i := fun i k => integral_mul_const _ _
  simp_rw [integral_finsetSum _ fun k _ => it _ k, hi]
  have hs : ∀ i, ∑ k, schurM β i k * M k i = (schurCN (N := N) β : ℂ) * M i i := by
    intro i
    rw [sum_eq_single i (fun k _ hki => by rw [schurM_offdiag β (Ne.symm hki), zero_mul])
      (fun h => absurd (mem_univ i) h), schurM_eq]
  simp_rw [hs, ← mul_sum, Complex.reCLM_apply, Complex.re_ofReal_mul]
  rfl

/-- **Schur's lemma for the SU(N) plaquette factor**: `∫ e^{β Re tr v} Re tr(v M) dv = λ_N(β) Re tr M`. -/
theorem schur_SUN (β : ℝ) (M : SUN N) :
    ∫ v, bwN β v * gaugeReTr (SUN N) N (v * M) ∂(haarG (SUN N)) = schurCN (N := N) β * gaugeReTr (SUN N) N M :=
  integral_bwN_tr_mul β (M : Matrix (Fin N) (Fin N) ℂ)

/-! ### The centre twists `ω^k` -/

theorem stdAddChar_pow_N (k : ZMod N) : (ZMod.stdAddChar k : ℂ) ^ N = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]

/-- **The centre twist** `zN k = e^{2πi k/N} · 1 ∈ SU(N)`. -/
def zN (k : ZMod N) : SUN N := centreElt N (ZMod.stdAddChar k) (stdAddChar_pow_N k)

theorem zN_val (k : ZMod N) : ((zN k : SUN N) : Matrix (Fin N) (Fin N) ℂ) = (ZMod.stdAddChar k : ℂ) • 1 := rfl

theorem zN_central (k : ZMod N) (g : SUN N) : Commute (zN k) g := centreElt_central _ _ g

theorem zN_add (k l : ZMod N) : zN (k + l) = zN k * zN l := by
  apply Subtype.ext
  show (ZMod.stdAddChar (k + l) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) =
    ((ZMod.stdAddChar k : ℂ) • 1) * ((ZMod.stdAddChar l : ℂ) • 1)
  rw [AddChar.map_add_eq_mul, smul_mul_smul, mul_one]

theorem zN_zero : zN (0 : ZMod N) = 1 := by
  apply Subtype.ext
  show (ZMod.stdAddChar (0 : ZMod N) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) = 1
  rw [AddChar.map_zero_eq_one, one_smul]

theorem zN_neg (k : ZMod N) : zN (-k) = (zN k)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← zN_add, neg_add_cancel, zN_zero]

theorem gaugeTrace_zN_mul (k : ZMod N) (g : SUN N) :
    gaugeTrace (SUN N) N (zN k * g) = ZMod.stdAddChar k * gaugeTrace (SUN N) N g := by
  show Matrix.trace (((ZMod.stdAddChar k : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) * (g : Matrix (Fin N) (Fin N) ℂ)) = _
  rw [smul_mul_assoc, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  rfl

theorem norm_stdAddChar (k : ZMod N) : ‖(ZMod.stdAddChar k : ℂ)‖ = 1 := by
  rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _

/-- `Re tr (zN k) = N Re ψ(k) ≠ N` for `k ≠ 0`. -/
theorem reTr_zN_ne {k : ZMod N} (hk : k ≠ 0) : gaugeReTr (SUN N) N (zN k) ≠ N := by
  have ht : gaugeReTr (SUN N) N (zN k) = N * (ZMod.stdAddChar k : ℂ).re := by
    have := gaugeTrace_zN_mul k 1
    rw [mul_one] at this
    unfold gaugeReTr
    rw [this, gaugeTrace_SUN, OneMemClass.coe_one, Matrix.trace_one, Fintype.card_fin, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im]
    ring
  rw [ht]
  intro h
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hre : (ZMod.stdAddChar k : ℂ).re = 1 := by
    have := mul_left_cancel₀ hN (h.trans (mul_one (N : ℝ)).symm)
    exact this
  have hn := norm_stdAddChar k
  have him : (ZMod.stdAddChar k : ℂ).im = 0 := by
    have h2 := Complex.sq_norm (ZMod.stdAddChar k : ℂ)
    rw [hn, Complex.normSq_apply, hre] at h2
    nlinarith
  have h1 : (ZMod.stdAddChar k : ℂ) = ZMod.stdAddChar (0 : ZMod N) := by
    rw [AddChar.map_zero_eq_one]; exact Complex.ext hre him
  exact hk (ZMod.injective_stdAddChar h1)

/-- `∫ tr v dv = 0` on SU(N), `N ≥ 2` (the centre element `ψ(1) ≠ 1` multiplies the trace). -/
theorem integral_traceN_eq_zero [Fact (1 < N)] :
    ∫ v, gaugeTrace (SUN N) N v ∂(haarG (SUN N)) = 0 := by
  have hc : Continuous (gaugeTrace (SUN N) N) := continuous_subtype_val.matrix_trace
  have h := integral_comp_of_measurePreserving (measurePreserving_mul_left (haarG (SUN N)) (zN (1 : ZMod N)))
    hc.aestronglyMeasurable
  simp only [gaugeTrace_zN_mul, integral_const_mul] at h
  have h1 : (ZMod.stdAddChar (1 : ZMod N) : ℂ) ≠ 1 := by
    intro h1
    rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))] at h1
    exact one_ne_zero (ZMod.injective_stdAddChar h1)
  have h2 : ((ZMod.stdAddChar (1 : ZMod N) : ℂ) - 1) * ∫ v, gaugeTrace (SUN N) N v ∂(haarG (SUN N)) = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 h1)

theorem integral_trN_eq_zero [Fact (1 < N)] : ∫ v, gaugeReTr (SUN N) N v ∂(haarG (SUN N)) = 0 := by
  have hc : Continuous (gaugeTrace (SUN N) N) := continuous_subtype_val.matrix_trace
  calc ∫ v, gaugeReTr (SUN N) N v ∂(haarG (SUN N))
      = ∫ v, Complex.reCLM (gaugeTrace (SUN N) N v) ∂(haarG (SUN N)) := rfl
    _ = Complex.reCLM (∫ v, gaugeTrace (SUN N) N v ∂(haarG (SUN N))) :=
        ContinuousLinearMap.integral_comp_comm Complex.reCLM (integrable_of_continuous hc)
    _ = 0 := by rw [integral_traceN_eq_zero]; simp

/-- **`λ_N(β) ≠ 0` for `β ≠ 0`** (`N ≥ 2`; `β N λ_N(β) > 0`). -/
theorem schurCN_ne_zero [Fact (1 < N)] {β : ℝ} (hβ : β ≠ 0) : schurCN (N := N) β ≠ 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h1 : ∫ v, bwN β v * gaugeReTr (SUN N) N v ∂(haarG (SUN N)) = N * schurCN (N := N) β := by
    have := schur_SUN (N := N) β 1
    simp only [mul_one, trN_one] at this
    rw [this]; ring
  have hc : Continuous fun v : SUN N => (Real.exp (β * gaugeReTr (SUN N) N v) - 1) * (β * gaugeReTr (SUN N) N v) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_trN)).sub continuous_const).mul
      (continuous_const.mul continuous_trN)
  have h2 := integral_pos_of_continuous (μ := haarG (SUN N)) hc (fun v => expsub_mul_nonneg _) (x0 := 1)
    (expsub_mul_pos (by rw [trN_one]; exact mul_ne_zero hβ hNpos.ne'))
  have h3 : ∫ v, (Real.exp (β * gaugeReTr (SUN N) N v) - 1) * (β * gaugeReTr (SUN N) N v) ∂(haarG (SUN N)) =
      β * ∫ v, bwN β v * gaugeReTr (SUN N) N v ∂(haarG (SUN N)) -
        β * ∫ v, gaugeReTr (SUN N) N v ∂(haarG (SUN N)) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_sub (f := fun v => β * (bwN β v * gaugeReTr (SUN N) N v)) (g := fun v => β * gaugeReTr (SUN N) N v)
      (integrable_of_continuous ((continuous_const.mul ((continuous_bwN β).mul continuous_trN))))
      (integrable_of_continuous (continuous_const.mul continuous_trN))]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [bwN]; ring
  rw [h3, integral_trN_eq_zero, h1] at h2
  intro h0
  rw [h0] at h2
  simp at h2

end SchurSUN

end ProofPhase.General
