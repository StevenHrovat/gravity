/-
The ETM in ordinary terms: multiplication by complex numbers (2026-11-24).
Released under Apache 2.0.

Note: `docs/paper/draft/02-part-II-machine.md` (the machine, first paragraph).
-/

import ProofPhase.ETM.Machine
import ProofPhase.Unified.Encoder

/-!
# The machine is multiplication by complex numbers

**The translation.** Each step multiplies the carried amplitude by one complex number `c` with `‖c‖ ≤ 1`: its modulus is the cost
paid at the gate, its phase the rotation. A run multiplies its steps.

1. `cmach`: a sequence of multipliers with `‖c n‖ ≤ 1` is a running system (floor 0): the state is the tick and the amplitude,
   the step multiplies, the gate factor is `‖c n‖`, the mass is `‖z‖`. The ledger law holds with equality (`cmach_pays_eq`).
2. `cmach_iterate`: after `n` steps the amplitude is `(∏ c) * z`, so moduli multiply (`cmach_mass_eq`) and phases add.
3. `dominated`: every running system is dominated by a complex run: its mass after `n` steps is at most the modulus of the
   product of its own (real, nonnegative) factors `e^δ fac` times the start. The translation loses nothing on the cost side.
4. The two sides: multipliers uniformly below `θ < 1` settle (`cmach_reaches`, from the settle theorem); multipliers on the unit
   circle never change the mass (`cmach_lossless`). The universal machine's factors are all `1` (`etm_fac_one`): its settling
   lives in its content (halting), not in the number, which is where its undecidability sits (`etm_balance_undecidable`).
5. `encMach`: the reflection coefficients of a stream of encoders (`‖refl‖ ≤ 1`) are such multipliers, with cost
   `szego c = 1 - ‖c‖²` (`Unified.Encoder`).

Care point: the translation is exact for the cost and the rotation. The content a step carries (the program the universal machine
runs) lives in the state, not in the number.

No axioms beyond the standard ones.
-/

open Finset

noncomputable section

namespace ProofPhase.ETM

universe u

/-! ## 1. The complex machine -/

/-- One step of the complex machine: the tick advances and the amplitude is multiplied by the tick's multiplier. -/
def cstep (c : ℕ → ℂ) (p : ℕ × ℂ) : ℕ × ℂ := (p.1 + 1, c p.1 * p.2)

theorem cstep_iterate (c : ℕ → ℂ) (k : ℕ) (z : ℂ) (n : ℕ) :
    (cstep c)^[n] (k, z) = (k + n, (∏ i ∈ range n, c (k + i)) * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, prod_range_succ]
    refine Prod.ext (by simp [cstep, Nat.add_assoc]) ?_
    simp only [cstep]
    ring

/-- **The complex machine**: multipliers `c n` with `‖c n‖ ≤ 1`; the state is the tick and the amplitude; the step multiplies. -/
def cmach (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) : RunSys.{0} 0 where
  X := ℕ × ℂ
  step := cstep c
  fac p := ‖c p.1‖
  mass p := ‖p.2‖
  fac_nonneg _ := norm_nonneg _
  fac_le_one p := hc p.1
  mass_nonneg _ := norm_nonneg _
  pays p := by
    show ‖c p.1 * p.2‖ ≤ Real.exp 0 * ‖c p.1‖ * ‖p.2‖
    rw [Real.exp_zero, one_mul, norm_mul]

variable {c : ℕ → ℂ} {hc : ∀ n, ‖c n‖ ≤ 1}

/-- **The ledger law holds with equality**: each step pays exactly its modulus. -/
theorem cmach_pays_eq (p : ℕ × ℂ) :
    (cmach c hc).mass ((cmach c hc).step p) = (cmach c hc).fac p * (cmach c hc).mass p :=
  norm_mul _ _

/-- **A run multiplies its steps**: after `n` steps from tick `k` the amplitude is the product of the multipliers times `z`. -/
theorem cmach_iterate (k : ℕ) (z : ℂ) (n : ℕ) :
    (cmach c hc).step^[n] (k, z) = (k + n, (∏ i ∈ range n, c (k + i)) * z) :=
  cstep_iterate c k z n

/-- **Moduli multiply**: the mass after `n` steps is the product of the moduli times the start, exactly. -/
theorem cmach_mass_eq (k : ℕ) (z : ℂ) (n : ℕ) :
    (cmach c hc).mass ((cmach c hc).step^[n] (k, z)) = (∏ i ∈ range n, ‖c (k + i)‖) * ‖z‖ := by
  rw [cmach_iterate]
  show ‖(∏ i ∈ range n, c (k + i)) * z‖ = _
  rw [norm_mul, norm_prod]

/-! ## 2. Every running system is dominated by a complex run -/

/-- **Domination**: the mass of any running system after `n` steps is at most the modulus of the product of its own factors
`e^δ fac`, read as complex numbers, times the start. -/
theorem dominated {δ : ℝ} (S : RunSys.{u} δ) (x : S.X) (n : ℕ) :
    S.mass (S.step^[n] x) ≤
      ‖∏ i ∈ range n, ((Real.exp δ * S.fac (S.step^[i] x) : ℝ) : ℂ)‖ * S.mass x := by
  have h : ‖∏ i ∈ range n, ((Real.exp δ * S.fac (S.step^[i] x) : ℝ) : ℂ)‖ =
      ∏ i ∈ range n, Real.exp δ * S.fac (S.step^[i] x) := by
    rw [norm_prod]
    exact prod_congr rfl fun i _ =>
      Complex.norm_of_nonneg (mul_nonneg (Real.exp_pos δ).le (S.fac_nonneg _))
  rw [h]
  exact S.carry x n

/-! ## 3. The two sides: below the circle it settles; on the circle the number carries nothing -/

/-- **Below the circle, the run settles**: multipliers uniformly at most `θ < 1` reach balance within any `ε > 0`. -/
theorem cmach_reaches {θ : ℝ} (hθ : ∀ n, ‖c n‖ ≤ θ) (hθ1 : θ < 1) (p : ℕ × ℂ) {ε : ℝ} (hε : 0 < ε) :
    (cmach c hc).Reaches ε p :=
  (cmach c hc).reaches_of_contracting' ⟨fun q => hθ q.1, by rw [Real.exp_zero, one_mul]; exact hθ1⟩ p hε

/-- **On the circle the mass never changes**: unit multipliers are pure rotation. -/
theorem cmach_lossless (hu : ∀ n, ‖c n‖ = 1) (k : ℕ) (z : ℂ) (n : ℕ) :
    (cmach c hc).mass ((cmach c hc).step^[n] (k, z)) = ‖z‖ := by
  rw [cmach_mass_eq]
  simp [hu]

/-- **The universal machine sits on the circle**: every factor of the ETM is `1`. Its settling lives in its content (halting),
not in the number, and that is where it is undecidable (`etm_balance_undecidable`). -/
theorem etm_fac_one (s : EState) : etm.fac s = 1 := rfl

/-! ## 4. The encoder: reflection coefficients are the multipliers -/

/-- **The encoder's machine**: the reflection coefficients of a stream of encoders, each of modulus at most `1`. -/
def encMach {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (X : ℕ → Unified.Encoder ℂ E) : RunSys.{0} 0 :=
  cmach (fun n => (X n).refl) (fun n => (X n).norm_refl_le)

/-- In the encoder's machine each step pays its reflection coefficient's modulus, and its cost `szego` is `1 - ‖c‖²`. -/
theorem encMach_fac {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (X : ℕ → Unified.Encoder ℂ E) (k : ℕ) (z : ℂ) :
    (encMach X).fac (k, z) = ‖(X k).refl‖ ∧ Unified.szego (X k).refl = 1 - ‖(X k).refl‖ ^ 2 :=
  ⟨rfl, rfl⟩

/-! ## 5. Links between nodes: only rotation keeps identity -/

/-- **A rotation links the machine to itself**: multiplying every amplitude by a unit number `u` commutes with every step and
keeps the gate factor and the mass. -/
def rotHom (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (u : ℂ) (hu : ‖u‖ = 1) : RunSys.Hom (cmach c hc) (cmach c hc) where
  toFun p := (p.1, u * p.2)
  step_comm p := by
    show ((p.1 + 1, u * (c p.1 * p.2)) : ℕ × ℂ) = (p.1 + 1, c p.1 * (u * p.2))
    rw [mul_left_comm]
  fac_eq _ := rfl
  mass_eq p := by
    show ‖u * p.2‖ = ‖p.2‖
    rw [norm_mul, hu, one_mul]

/-- **Only rotation keeps identity**: a complex-linear map of the line that keeps every norm is multiplication by a number on the
unit circle. -/
theorem rot_of_isometry (f : ℂ →ₗ[ℂ] ℂ) (hf : ∀ z, ‖f z‖ = ‖z‖) : ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ z, f z = u * z := by
  refine ⟨f 1, by rw [hf 1, norm_one], fun z => ?_⟩
  have : f z = f (z • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

/-- **On the reals the circle is two points**: a real-linear map of the line that keeps every norm is multiplication by `1` or
`-1`, the identity or the half-turn. -/
theorem rot_of_isometry_real (f : ℝ →ₗ[ℝ] ℝ) (hf : ∀ x, ‖f x‖ = ‖x‖) :
    ∃ u : ℝ, (u = 1 ∨ u = -1) ∧ ∀ x, f x = u * x := by
  refine ⟨f 1, ?_, fun x => ?_⟩
  · have h : |f 1| = 1 := by simpa [Real.norm_eq_abs] using hf 1
    exact (abs_eq zero_le_one).1 h
  · have : f x = f (x • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul, mul_comm]

/-- **Ordinary multiplication is a cost times a half-turn**: every real number is its modulus times `1` or `-1`. -/
theorem real_eq_sign_mul_abs (r : ℝ) : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ r = s * |r| := by
  rcases le_total 0 r with h | h
  · exact ⟨1, Or.inl rfl, by rw [abs_of_nonneg h, one_mul]⟩
  · exact ⟨-1, Or.inr rfl, by rw [abs_of_nonpos h]; ring⟩

/-! ## 6. The translation in one statement -/

/-- **The ETM translation.** Multipliers of modulus at most one make a running system whose run is the product of its steps;
every running system is dominated by such a product; below the circle the run settles; on the circle the number carries nothing,
and the universal machine is on the circle. -/
theorem complex_translation :
    (∀ (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (k : ℕ) (z : ℂ) (n : ℕ),
      (cmach c hc).step^[n] (k, z) = (k + n, (∏ i ∈ range n, c (k + i)) * z)) ∧
    (∀ (δ : ℝ) (S : RunSys.{0} δ) (x : S.X) (n : ℕ),
      S.mass (S.step^[n] x) ≤ ‖∏ i ∈ range n, ((Real.exp δ * S.fac (S.step^[i] x) : ℝ) : ℂ)‖ * S.mass x) ∧
    (∀ (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (θ : ℝ), (∀ n, ‖c n‖ ≤ θ) → θ < 1 →
      ∀ (p : ℕ × ℂ) (ε : ℝ), 0 < ε → (cmach c hc).Reaches ε p) ∧
    (∀ (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1), (∀ n, ‖c n‖ = 1) →
      ∀ (k : ℕ) (z : ℂ) (n : ℕ), (cmach c hc).mass ((cmach c hc).step^[n] (k, z)) = ‖z‖) ∧
    (∀ s : EState, etm.fac s = 1) :=
  ⟨fun _ _ k z n => cmach_iterate k z n, fun _ S x n => dominated S x n,
    fun _ _ _ hθ hθ1 p _ hε => cmach_reaches hθ hθ1 p hε, fun _ _ hu k z n => cmach_lossless hu k z n, etm_fac_one⟩

end ProofPhase.ETM

end
