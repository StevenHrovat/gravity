/-
Proof phase, generalisation phase 2: the centre `Z_N` of SU(N) and the cost distance on SU(N) (2026-11-23).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 2.
-/

import ProofPhase.General.SUN

/-!
# The centre of SU(N) and the cost distance

**The centre.** For `ω` with `ω ^ N = 1` the scalar matrix `ω I` lies in `SU(N)` (`centreElt`; `|ω| = 1` follows from
`ω ^ N = 1`, and `det (ω I) = ω ^ N = 1`). The map `ζ ↦ ζ I` is an injective monoid homomorphism
`centreHom : rootsOfUnity N ℂ →* SUN N`, so the image is a copy of `Z_N` (it has `N` elements, `card_centre`), and every
element is central. It acts on the fundamental representation as the scalar `ζ` (`centreHom_rep`), and on the
conjugate representation as `ζ⁻¹`: the `N`-ality of a representation `ρ` is `k` when `ρ (ζ I) = ζ ^ k` for all `ζ`
(`HasNality`); the fundamental has `k = 1`, its complex conjugate `k = -1`. For `N = 2` and `ω = -1` the element is
`negOneSU2` (`centreElt_two_neg_one`).

**The cost distance.** `geodSUN a b = arccos (Re tr (a b⁻¹) / N)`: non-negative, at most `π`, zero on the diagonal, and
equal to `geodSU2` at `N = 2` (`geodSUN_two`). It is positive on some pair for `N ≥ 2` (`exists_geodSUN_pos`), e.g. on
`(ζ I, 1)` with `ζ = e^{2πi/N}`.
-/

open MeasureTheory Finset AreaLaw.Concrete

noncomputable section

namespace ProofPhase.General

section Centre

variable {N : ℕ} [NeZero N]

theorem norm_eq_one_of_pow_eq_one {ω : ℂ} (h : ω ^ N = 1) : ‖ω‖ = 1 := by
  have h1 : ‖ω‖ ^ N = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg ω) (NeZero.ne N)).1 h1

theorem scalar_mem_SUN {ω : ℂ} (h : ω ^ N = 1) :
    (ω • (1 : Matrix (Fin N) (Fin N) ℂ)) ∈ Matrix.specialUnitaryGroup (Fin N) ℂ := by
  have hn := norm_eq_one_of_pow_eq_one h
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, smul_mul_smul, mul_one]
    have : ω * star ω = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    rw [this, one_smul]
  · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, h]

/-- **The central element `ω I` of SU(N)** for `ω ^ N = 1`. -/
def centreElt (N : ℕ) [NeZero N] (ω : ℂ) (h : ω ^ N = 1) : SUN N := ⟨ω • 1, scalar_mem_SUN h⟩

@[simp] theorem centreElt_val (ω : ℂ) (h : ω ^ N = 1) :
    ((centreElt N ω h : SUN N) : Matrix (Fin N) (Fin N) ℂ) = ω • 1 := rfl

theorem centreElt_central (ω : ℂ) (h : ω ^ N = 1) (g : SUN N) : centreElt N ω h * g = g * centreElt N ω h :=
  Subtype.ext (by simp)

omit [NeZero N] in
theorem rootsOfUnity_pow (ζ : rootsOfUnity N ℂ) : ((ζ : ℂˣ) : ℂ) ^ N = 1 := by
  have h := ζ.2
  rw [mem_rootsOfUnity] at h
  have := congrArg Units.val h
  simpa using this

/-- **`Z_N` inside SU(N)**: the `N`-th roots of unity as scalar matrices. -/
def centreHom (N : ℕ) [NeZero N] : rootsOfUnity N ℂ →* SUN N where
  toFun ζ := centreElt N ((ζ : ℂˣ) : ℂ) (rootsOfUnity_pow ζ)
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [smul_smul, mul_comm])

theorem centreHom_val (ζ : rootsOfUnity N ℂ) :
    ((centreHom N ζ : SUN N) : Matrix (Fin N) (Fin N) ℂ) = ((ζ : ℂˣ) : ℂ) • 1 := rfl

theorem centreHom_injective : Function.Injective (centreHom N) := by
  intro a b hab
  have h := congrArg (fun g : SUN N => (g : Matrix (Fin N) (Fin N) ℂ) ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩) hab
  simp only [centreHom_val, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  exact Subtype.ext (Units.ext h)

theorem centreHom_central (ζ : rootsOfUnity N ℂ) (g : SUN N) : centreHom N ζ * g = g * centreHom N ζ :=
  centreElt_central _ (rootsOfUnity_pow ζ) g

/-- The centre of SU(N) has exactly `N` elements. -/
theorem card_centre : Nat.card (rootsOfUnity N ℂ) = N := Complex.card_rootsOfUnity N

/-- **The centre acts on the fundamental representation as the scalar `ζ`.** -/
theorem centreHom_rep (ζ : rootsOfUnity N ℂ) :
    HasGaugeTrace.rep (G := SUN N) (n := N) (centreHom N ζ) = ((ζ : ℂˣ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := rfl

/-- The trace of a central element: `tr (ζ I) = N ζ`. -/
theorem gaugeTrace_centreHom (ζ : rootsOfUnity N ℂ) : gaugeTrace (SUN N) N (centreHom N ζ) = N * ((ζ : ℂˣ) : ℂ) := by
  show Matrix.trace (((ζ : ℂˣ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) = _
  rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  simp [mul_comm]

/-- The `N`-ality of a representation: the centre acts as the `k`-th power of the root of unity. -/
def HasNality {m : ℕ} (ρ : SUN N →* Matrix (Fin m) (Fin m) ℂ) (k : ℤ) : Prop :=
  ∀ ζ : rootsOfUnity N ℂ, ρ (centreHom N ζ) = (((ζ : ℂˣ) ^ k : ℂˣ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)

/-- **The fundamental representation has `N`-ality 1.** -/
theorem hasNality_fundamental : HasNality (N := N) (HasGaugeTrace.rep (G := SUN N) (n := N)) 1 := by
  intro ζ
  rw [centreHom_rep, zpow_one]

/-- The complex-conjugate representation. -/
def conjRep (N : ℕ) : SUN N →* Matrix (Fin N) (Fin N) ℂ :=
  (starRingEnd ℂ).mapMatrix.toMonoidHom.comp (HasGaugeTrace.rep (G := SUN N) (n := N))

/-- **The conjugate representation has `N`-ality `-1`.** -/
theorem hasNality_conj : HasNality (N := N) (conjRep N) (-1) := by
  intro ζ
  have hn : ‖((ζ : ℂˣ) : ℂ)‖ = 1 := by
    exact norm_eq_one_of_pow_eq_one (rootsOfUnity_pow ζ)
  have hinv : (((ζ : ℂˣ) ^ (-1 : ℤ) : ℂˣ) : ℂ) = star ((ζ : ℂˣ) : ℂ) := by
    rw [zpow_neg_one, Units.val_inv_eq_inv_val]
    have h1 : ((ζ : ℂˣ) : ℂ) * star ((ζ : ℂˣ) : ℂ) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
    exact inv_eq_of_mul_eq_one_right h1
  rw [hinv]
  simp only [conjRep, MonoidHom.comp_apply, centreHom_rep]
  ext i j
  by_cases hij : i = j <;> simp [hij]

end Centre

/-- For `N = 2` and `ω = -1` the central element is `negOneSU2`. -/
theorem centreElt_two_neg_one : centreElt 2 (-1) (by norm_num) = negOneSU2 :=
  Subtype.ext (by simp [negOneSU2])

/-! ## The cost distance -/

/-- **The cost distance on SU(N)**: `arccos (Re tr (a b⁻¹) / N)`, the geodesic distance of `S³` for `N = 2`. -/
def geodSUN (N : ℕ) (a b : SUN N) : ℝ := Real.arccos (gaugeReTr (SUN N) N (a * b⁻¹) / N)

theorem geodSUN_nonneg {N : ℕ} (a b : SUN N) : 0 ≤ geodSUN N a b := Real.arccos_nonneg _

theorem geodSUN_le_pi {N : ℕ} (a b : SUN N) : geodSUN N a b ≤ Real.pi := Real.arccos_le_pi _

theorem geodSUN_self {N : ℕ} [NeZero N] (a : SUN N) : geodSUN N a a = 0 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  simp [geodSUN, gaugeReTr_one, hN]

/-- **The cost distance of SU(2) is the one of the repository.** -/
theorem geodSUN_two : geodSUN 2 = ProofPhase.Certified.geodSU2 := by
  funext a b
  simp [geodSUN, ProofPhase.Certified.geodSU2]

/-- **The cost distance takes a positive value for `N ≥ 2`**, on `(ζ I, 1)` with `ζ = e^{2πi/N}`. -/
theorem exists_geodSUN_pos {N : ℕ} [NeZero N] (hN : 2 ≤ N) : ∃ a b : SUN N, 0 < geodSUN N a b := by
  set ω : ℂ := Complex.exp (((2 * Real.pi / N : ℝ) : ℂ) * Complex.I) with hω
  have hpow : ω ^ N = 1 := by
    rw [hω, ← Complex.exp_nat_mul]
    have : (N : ℂ) * (((2 * Real.pi / N : ℝ) : ℂ) * Complex.I) = 2 * Real.pi * Complex.I := by
      have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
      push_cast
      field_simp
    rw [this]
    exact Complex.exp_two_pi_mul_I
  refine ⟨centreElt N ω hpow, 1, ?_⟩
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hre : gaugeReTr (SUN N) N (centreElt N ω hpow * (1 : SUN N)⁻¹) = N * Real.cos (2 * Real.pi / N) := by
    have : gaugeTrace (SUN N) N (centreElt N ω hpow * (1 : SUN N)⁻¹) = N * ω := by
      rw [inv_one, mul_one]
      show Matrix.trace (ω • (1 : Matrix (Fin N) (Fin N) ℂ)) = _
      rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
      simp [mul_comm]
    unfold gaugeReTr
    rw [this]
    have : (N * ω : ℂ).re = N * ω.re := by simp
    rw [this, hω, Complex.exp_ofReal_mul_I_re]
  unfold geodSUN
  rw [hre, mul_div_cancel_left₀ _ hN0]
  apply Real.arccos_pos.2
  have hx0 : 0 < 2 * Real.pi / N := by positivity
  have hx1 : 2 * Real.pi / N < 2 * Real.pi := by
    rw [div_lt_iff₀ hNpos]
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith [Real.pi_pos]
  rcases (Real.cos_le_one (2 * Real.pi / N)).lt_or_eq with h | h
  · exact h
  · exfalso
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hx1).1 h
    exact hx0.ne' this

end ProofPhase.General
