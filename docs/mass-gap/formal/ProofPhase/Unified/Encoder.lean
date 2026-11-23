/-
The unified lossy-step theorem: the encoder at a boundary (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/ENCODER.md`.
-/

import ProofPhase.Unified.Ledger

/-!
# The encoder: what a boundary passes on, and the step factor it determines

**The object.** A boundary has two sides. In a space of boundary states with a positive form (an inner product: this is
where positivity enters), the inside passes on one state `ψ` and the outside sees the same boundary as `ψ'`, the image of
`ψ` under the one rotation. Both sides certify the same norm, `‖ψ'‖ = ‖ψ‖ > 0`: the shared root. That is all an
`Encoder` holds. Its one number is the **reflection coefficient** `c = ⟪ψ, ψ'⟫ / ‖ψ‖²`, the overlap of the state with
its rotated image.

**What it determines.** The step's factor is a fixed function of `c` alone (a loss profile), and the ledger's cost is
`−log` of that factor. Two loss profiles occur:
* **Szego** (`szego c = 1 − ‖c‖²`): the share of `ψ` not carried by its mirror image (`szego_remainder`).
* **electric** (`elec c = (1 − c)/(1 + c)`): the odd part over the even part under the rotation
  (`encoder_elec`), the `ℤ/2` Fourier ratio `Z_{e=1}/Z_{e=0}`.

**Proved here (all general).**
* `norm_refl_le`: positivity and the shared root give `‖c‖ ≤ 1` (Cauchy-Schwarz). So the Szego factor lies in `[0, 1]`
  (`szego_mem`), and it is `1` exactly when `c = 0` (`szego_eq_one_iff`) and positive exactly when `‖c‖ < 1`
  (`szego_pos_iff`).
* `refl_map`: a symmetry of the form moves the encoder without changing `c`. `refl_swap`: read from the other side,
  `c` becomes its conjugate, and both loss profiles give the same factor (`szego_swap`, `elec_swap`): the step costs
  the same in both directions.
* `elec_elec`: the electric profile is an involution (the electric-magnetic duality), with the self-dual point
  `√2 − 1` (`elec_selfdual`), whose cost is `log(1 + √2) ≈ 0.881` (`selfdual_cost`).
* `markov_conditional`, `markov_sector`: if the joint weight factorises through the boundary label (the Markov property),
  the inside's law given the label does not depend on the outside, and each label's weight is the inside's part times
  the outside's message.
* `pays_of_factors`: a chain of encoder factors in `(0, 1]` is a ledger with cost `−log f` and floor `0`.
  `cost_eq_zero_iff`: cost zero is factor one (one certificate). `cost_nonneg_iff`: cost `≥ 0` is factor `≤ 1`.
* `costAboveFloor_of_factor_le`, `factor_le_of_costAboveFloor`: a cost above the floor `δ` is exactly a uniform bound
  of the factors below `e^{−δ}`: the hand-over certificate is a uniform distance of the encoder from lossless.
* `oneBox_iff_refl`: for the electric profile, cost above the floor `log μ` holds exactly when every reflection
  coefficient stays above some `c₀ > (μ − 1)/(μ + 1)` (`elec_inv`).

No axioms beyond the standard ones.
-/

open Finset
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace ProofPhase.Unified

/-! ## 1. The encoder -/

/-- **The encoder at a boundary.** `ψ` is the boundary state passed on by the inside, `ψ'` the same boundary seen from the
outside (the image of `ψ` under the one rotation). `root`: both sides certify the same norm. Positivity is the inner
product. -/
structure Encoder (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] where
  /-- The boundary state passed on by the inside. -/
  ψ : E
  /-- The boundary seen from the outside: the rotated image. -/
  ψ' : E
  /-- The shared root: both sides certify the same norm. -/
  root : ‖ψ'‖ = ‖ψ‖
  /-- The boundary carries something. -/
  ne : ψ ≠ 0

namespace Encoder

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- An encoder from a rotation: any norm-preserving map (linear or antilinear) and a nonzero state. -/
def ofRot (R : E → E) (hR : ∀ x, ‖R x‖ = ‖x‖) (ψ : E) (hψ : ψ ≠ 0) : Encoder 𝕜 E := ⟨ψ, R ψ, hR ψ, hψ⟩

variable (X : Encoder 𝕜 E)

/-- **The reflection coefficient** `c = ⟪ψ, ψ'⟫ / ‖ψ‖²`: the overlap of the boundary state with its rotated image. -/
def refl : 𝕜 := (((‖X.ψ‖ ^ 2)⁻¹ : ℝ) : 𝕜) * ⟪X.ψ, X.ψ'⟫_𝕜

theorem norm_pos : 0 < ‖X.ψ‖ := norm_pos_iff.2 X.ne

theorem inner_eq : ⟪X.ψ, X.ψ'⟫_𝕜 = ((‖X.ψ‖ ^ 2 : ℝ) : 𝕜) * X.refl := by
  have h : (‖X.ψ‖ ^ 2 : ℝ) ≠ 0 := by have := X.norm_pos; positivity
  rw [refl, ← mul_assoc, ← RCLike.ofReal_mul, mul_inv_cancel₀ h, RCLike.ofReal_one, one_mul]

/-- **Positivity and the shared root bound the reflection coefficient**: `‖c‖ ≤ 1` (Cauchy-Schwarz). -/
theorem norm_refl_le : ‖X.refl‖ ≤ 1 := by
  have h := norm_inner_le_norm (𝕜 := 𝕜) X.ψ X.ψ'
  rw [X.root] at h
  have hp := X.norm_pos
  rw [refl, norm_mul, RCLike.norm_ofReal, abs_of_pos (by positivity), inv_mul_le_iff₀ (by positivity), mul_one, sq]
  exact h

/-- The boundary seen from the other side. -/
def swap : Encoder 𝕜 E where
  ψ := X.ψ'
  ψ' := X.ψ
  root := X.root.symm
  ne := fun h => X.ne (norm_eq_zero.1 (by rw [← X.root, h, norm_zero]))

/-- **Read from the other side, the reflection coefficient is conjugated.** -/
theorem refl_swap : X.swap.refl = conj X.refl := by
  simp only [refl, swap]
  rw [X.root, map_mul, RCLike.conj_ofReal, inner_conj_symm]

/-- The encoder moved by a symmetry of the form. -/
def map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (S : E →ₗᵢ[𝕜] F) : Encoder 𝕜 F where
  ψ := S X.ψ
  ψ' := S X.ψ'
  root := by rw [S.norm_map, S.norm_map, X.root]
  ne := fun h => X.ne (norm_eq_zero.1 (by rw [← S.norm_map, h, norm_zero]))

/-- **A symmetry of the form does not change the reflection coefficient.** -/
theorem refl_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] (S : E →ₗᵢ[𝕜] F) :
    (X.map S).refl = X.refl := by
  simp only [refl, map, S.norm_map, S.inner_map_map]

end Encoder

/-! ## 2. The Szego loss profile -/

section Szego

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **The Szego factor** `1 − ‖c‖²`. -/
def szego (c : 𝕜) : ℝ := 1 - ‖c‖ ^ 2

theorem szego_le_one (c : 𝕜) : szego c ≤ 1 := by unfold szego; nlinarith [norm_nonneg c]

theorem szego_nonneg {c : 𝕜} (h : ‖c‖ ≤ 1) : 0 ≤ szego c := by unfold szego; nlinarith [norm_nonneg c]

/-- **The factor is positive exactly when the reflection coefficient is strictly inside the unit disk.** -/
theorem szego_pos_iff (c : 𝕜) : 0 < szego c ↔ ‖c‖ < 1 := by
  unfold szego
  constructor
  · intro h; by_contra h'; nlinarith [norm_nonneg c]
  · intro h; nlinarith [norm_nonneg c]

/-- **The factor is zero exactly at the closure `‖c‖ = 1`.** -/
theorem szego_eq_zero_iff (c : 𝕜) : szego c = 0 ↔ ‖c‖ = 1 := by
  unfold szego
  constructor
  · intro h
    have h2 : ‖c‖ ^ 2 = 1 ^ 2 := by linarith
    exact (pow_left_inj₀ (norm_nonneg c) zero_le_one two_ne_zero).1 h2
  · intro h; rw [h]; norm_num

/-- **Zero and one are one certificate**: the factor is exactly one when the reflection coefficient is zero. -/
theorem szego_eq_one_iff (c : 𝕜) : szego c = 1 ↔ c = 0 := by
  unfold szego
  constructor
  · intro h
    have : ‖c‖ ^ 2 = 0 := by linarith
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  · intro h; rw [h, norm_zero]; norm_num

theorem szego_conj (c : 𝕜) : szego (conj c) = szego c := by unfold szego; rw [RCLike.norm_conj]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (X : Encoder 𝕜 E)

/-- **Every encoder's Szego factor lies in `[0, 1]`.** -/
theorem szego_mem : 0 ≤ szego X.refl ∧ szego X.refl ≤ 1 := ⟨szego_nonneg X.norm_refl_le, szego_le_one _⟩

/-- **Both sides read the same Szego factor.** -/
theorem szego_swap : szego X.swap.refl = szego X.refl := by rw [X.refl_swap, szego_conj]

/-- **The Szego factor is the share of the boundary state not carried by its mirror image**: removing from `ψ` its
projection on `ψ'` leaves `‖ψ‖² (1 − ‖c‖²)`. -/
theorem szego_remainder : ‖X.ψ - conj X.refl • X.ψ'‖ ^ 2 = ‖X.ψ‖ ^ 2 * szego X.refl := by
  rw [@norm_sub_sq 𝕜, inner_smul_right, X.inner_eq, norm_smul, mul_pow, X.root, RCLike.norm_conj]
  have hc : conj X.refl * (((‖X.ψ‖ ^ 2 : ℝ) : 𝕜) * X.refl) = ((‖X.ψ‖ ^ 2 * ‖X.refl‖ ^ 2 : ℝ) : 𝕜) := by
    rw [mul_left_comm, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul]
  rw [hc, RCLike.ofReal_re]
  unfold szego
  ring

end Szego

/-! ## 3. The electric loss profile and its duality -/

/-- **The electric factor** `(1 − c)/(1 + c)`. -/
def elec (c : ℝ) : ℝ := (1 - c) / (1 + c)

/-- **The factor from the sector weights**: `elec(Z_tw/Z) = (Z − Z_tw)/(Z + Z_tw)`. -/
theorem elec_ratio {Z Ztw : ℝ} (hZ : 0 < Z) : elec (Ztw / Z) = (Z - Ztw) / (Z + Ztw) := by
  unfold elec
  rw [one_sub_div hZ.ne', one_add_div hZ.ne', div_div_div_cancel_right₀ hZ.ne']

theorem elec_zero : elec 0 = 1 := by norm_num [elec]

theorem elec_mem {c : ℝ} (h0 : 0 < c) (h1 : c < 1) : 0 < elec c ∧ elec c < 1 := by
  unfold elec
  refine ⟨div_pos (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

theorem elec_eq (c : ℝ) (h : c ≠ -1) : elec c = 2 / (1 + c) - 1 := by
  have h' : 1 + c ≠ 0 := fun h0 => h (by linarith)
  unfold elec
  field_simp
  ring

/-- **Zero and one are one certificate** (electric form). -/
theorem elec_eq_one_iff {c : ℝ} (h : -1 < c) : elec c = 1 ↔ c = 0 := by
  unfold elec
  rw [div_eq_one_iff_eq (by linarith)]
  constructor <;> intro h' <;> linarith

/-- **The electric profile is strictly decreasing** on `(−1, ∞)`. -/
theorem elec_lt_elec_iff {a b : ℝ} (ha : -1 < a) (hb : -1 < b) : elec a < elec b ↔ b < a := by
  rw [elec_eq a (by linarith), elec_eq b (by linarith), sub_lt_sub_iff_right,
    div_lt_div_iff_of_pos_left two_pos (by linarith) (by linarith)]
  constructor <;> intro h <;> linarith

theorem elec_le_elec_iff {a b : ℝ} (ha : -1 < a) (hb : -1 < b) : elec a ≤ elec b ↔ b ≤ a := by
  rw [← not_lt, elec_lt_elec_iff hb ha, not_lt]

/-- **The electric-magnetic duality**: the electric profile is an involution. -/
theorem elec_elec {c : ℝ} (h : c ≠ -1) : elec (elec c) = c := by
  have h' : 1 + c ≠ 0 := fun h0 => h (by linarith)
  unfold elec
  have h2 : 1 + (1 - c) / (1 + c) = 2 / (1 + c) := by field_simp; ring
  rw [h2]
  field_simp
  ring

/-- `elec(1/μ) = (μ − 1)/(μ + 1)`. -/
theorem elec_inv {μ : ℝ} (hμ : 0 < μ) : elec μ⁻¹ = (μ - 1) / (μ + 1) := by
  unfold elec
  field_simp

theorem sqrt_two_sub_one_pos : 0 < √2 - 1 := by
  have : 1 < √2 := by rw [Real.lt_sqrt zero_le_one]; norm_num
  linarith

theorem sqrt_two_mul : (√2 - 1) * (1 + √2) = 1 := by
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith

/-- **The self-dual point** `√2 − 1`. -/
theorem elec_selfdual : elec (√2 - 1) = √2 - 1 := by
  have h := sqrt_two_mul
  have h1 : (1 : ℝ) + (√2 - 1) = √2 := by ring
  have hs : 0 < √2 := by positivity
  unfold elec
  rw [h1, div_eq_iff hs.ne']
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- **The cost at the self-dual point is `log(1 + √2) ≈ 0.881`**, the hand-over value. -/
theorem selfdual_cost : -Real.log (√2 - 1) = Real.log (1 + √2) := by
  have h := sqrt_two_mul
  have hp := sqrt_two_sub_one_pos
  have hq : 0 < 1 + √2 := by positivity
  have := Real.log_mul hp.ne' hq.ne'
  rw [h, Real.log_one] at this
  linarith

section ElecEncoder

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (X : Encoder 𝕜 E)

/-- **The electric factor is the odd share over the even share under the rotation**:
`‖ψ − ψ'‖² / ‖ψ + ψ'‖² = elec(re c)`. -/
theorem encoder_elec (h : X.ψ + X.ψ' ≠ 0) :
    ‖X.ψ - X.ψ'‖ ^ 2 / ‖X.ψ + X.ψ'‖ ^ 2 = elec (RCLike.re X.refl) := by
  have hp := X.norm_pos
  have hn : (0 : ℝ) < ‖X.ψ‖ ^ 2 := by positivity
  have hplus : 0 < ‖X.ψ + X.ψ'‖ ^ 2 := by have := norm_pos_iff.2 h; positivity
  have hre : RCLike.re ⟪X.ψ, X.ψ'⟫_𝕜 = ‖X.ψ‖ ^ 2 * RCLike.re X.refl := by
    rw [X.inner_eq, RCLike.re_ofReal_mul]
  have hadd := @norm_add_sq 𝕜 _ _ _ _ X.ψ X.ψ'
  rw [@norm_sub_sq 𝕜, X.root, hre]
  rw [X.root, hre] at hadd
  rw [hadd] at hplus ⊢
  unfold elec
  have hd : 1 + RCLike.re X.refl ≠ 0 := by
    intro h0
    have : ‖X.ψ‖ ^ 2 + 2 * (‖X.ψ‖ ^ 2 * RCLike.re X.refl) + ‖X.ψ‖ ^ 2 = 2 * ‖X.ψ‖ ^ 2 * (1 + RCLike.re X.refl) := by
      ring
    rw [this, h0, mul_zero] at hplus
    exact lt_irrefl _ hplus
  rw [div_eq_div_iff hplus.ne' hd]
  ring

/-- **Both sides read the same electric factor.** -/
theorem elec_swap : elec (RCLike.re X.swap.refl) = elec (RCLike.re X.refl) := by
  rw [X.refl_swap, RCLike.conj_re]

end ElecEncoder

/-! ## 4. The Markov property: the outside reaches the inside only through the boundary label -/

section Markov

variable {I Λ O : Type*}

/-- **Markov across the boundary**: if the joint weight factorises through the label `l`, the inside's law given the
label does not depend on the outside `o`. -/
theorem markov_conditional (s : Finset I) (A : I → Λ → ℝ) (B : Λ → O → ℝ) (l : Λ) (o : O) (hB : B l o ≠ 0) (i : I) :
    A i l * B l o / ∑ j ∈ s, A j l * B l o = A i l / ∑ j ∈ s, A j l := by
  rw [← Finset.sum_mul, mul_div_mul_right _ _ hB]

/-- **Each label's weight is the inside's part times the outside's message.** -/
theorem markov_sector (s : Finset I) (u : Finset O) (A : I → Λ → ℝ) (B : Λ → O → ℝ) (l : Λ) :
    ∑ i ∈ s, ∑ o ∈ u, A i l * B l o = (∑ i ∈ s, A i l) * ∑ o ∈ u, B l o :=
  (Finset.sum_mul_sum s u (fun i => A i l) (fun o => B l o)).symm

end Markov

/-! ## 5. The encoder in the ledger -/

/-- **A chain of encoder factors is a ledger**: cost `−log f`, floor `0`. -/
theorem pays_of_factors {M f : ℕ → ℝ} {n : ℕ} (hf : ∀ i < n, 0 < f i) (h : ∀ i < n, M (i + 1) ≤ f i * M i) :
    Pays M (fun i => -Real.log (f i)) 0 n := fun i hi => by
  rw [zero_sub, neg_neg, Real.exp_log (hf i hi)]
  exact h i hi

/-- **Cost zero is factor one.** -/
theorem cost_eq_zero_iff {f : ℝ} (hf : 0 < f) : -Real.log f = 0 ↔ f = 1 := by
  constructor
  · intro h
    rw [← Real.exp_log hf, show Real.log f = 0 by linarith, Real.exp_zero]
  · intro h; rw [h, Real.log_one, neg_zero]

/-- **Cost at least zero is factor at most one.** -/
theorem cost_nonneg_iff {f : ℝ} (hf : 0 < f) : 0 ≤ -Real.log f ↔ f ≤ 1 := by
  constructor
  · intro h
    rw [← Real.exp_log hf]
    exact Real.exp_le_one_iff.2 (by linarith)
  · intro h
    have := Real.log_le_log hf h
    rw [Real.log_one] at this
    linarith

/-- **A uniform distance below `e^{−δ}` is a cost above the floor `δ`.** -/
theorem costAboveFloor_of_factor_le {Ω : Type*} {f : Ω → ℝ} {r δ : ℝ} (hf : ∀ ω, 0 < f ω) (hr0 : 0 < r)
    (hr : ∀ ω, f ω ≤ r) (hrδ : r < Real.exp (-δ)) : CostAboveFloor (fun ω => -Real.log (f ω)) δ := by
  refine ⟨-Real.log r, ?_, fun ω => ?_⟩
  · have := Real.log_lt_log hr0 hrδ
    rw [Real.log_exp] at this
    linarith
  · have := Real.log_le_log (hf ω) (hr ω)
    linarith

/-- **A cost above the floor `δ` is a uniform distance below `e^{−δ}`.** -/
theorem factor_le_of_costAboveFloor {Ω : Type*} {f : Ω → ℝ} {δ : ℝ} (hf : ∀ ω, 0 < f ω)
    (hc : CostAboveFloor (fun ω => -Real.log (f ω)) δ) : ∃ r, 0 < r ∧ r < Real.exp (-δ) ∧ ∀ ω, f ω ≤ r := by
  obtain ⟨κ, hκ, h⟩ := hc
  refine ⟨Real.exp (-κ), Real.exp_pos _, Real.exp_lt_exp.2 (by linarith), fun ω => ?_⟩
  rw [← Real.exp_log (hf ω)]
  exact Real.exp_le_exp.2 (by linarith [h ω])

/-- **The one-box form in encoder terms**: for the electric profile, cost above the floor `log μ` holds exactly when
every reflection coefficient stays above a fixed `c₀ > (μ − 1)/(μ + 1) = elec(1/μ)`. -/
theorem oneBox_iff_refl {Ω : Type*} {c : Ω → ℝ} (hc0 : ∀ ω, 0 < c ω) (hc1 : ∀ ω, c ω < 1) {μ : ℝ} (hμ : 1 < μ) :
    CostAboveFloor (fun ω => -Real.log (elec (c ω))) (Real.log μ) ↔ ∃ c₀, elec μ⁻¹ < c₀ ∧ ∀ ω, c₀ ≤ c ω := by
  have hμ0 : 0 < μ := by linarith
  have hexp : Real.exp (-Real.log μ) = μ⁻¹ := by rw [Real.exp_neg, Real.exp_log hμ0]
  have hinv0 : 0 < μ⁻¹ := inv_pos.2 hμ0
  have hinv1 : μ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hμ
  have hf : ∀ ω, 0 < elec (c ω) := fun ω => (elec_mem (hc0 ω) (hc1 ω)).1
  constructor
  · intro h
    obtain ⟨r, hr0, hrμ, hr⟩ := factor_le_of_costAboveFloor hf h
    rw [hexp] at hrμ
    refine ⟨elec r, (elec_lt_elec_iff (by linarith) (by linarith)).2 hrμ, fun ω => ?_⟩
    have h1 : elec r ≤ elec (elec (c ω)) :=
      (elec_le_elec_iff (by linarith) (by linarith [hf ω])).2 (hr ω)
    rwa [elec_elec (by linarith [hc0 ω])] at h1
  · rintro ⟨c₀, hc₀, hle⟩
    have hpos : 0 < elec μ⁻¹ := (elec_mem hinv0 hinv1).1
    by_cases h1 : 1 ≤ c₀
    · exact ⟨Real.log μ + 1, by linarith, fun ω => absurd (hle ω) (by linarith [hc1 ω])⟩
    · rw [not_le] at h1
      have hr := elec_mem (by linarith) h1
      refine costAboveFloor_of_factor_le hf hr.1 (fun ω => ?_) ?_
      · exact (elec_le_elec_iff (by linarith [hc0 ω]) (by linarith)).2 (hle ω)
      · rw [hexp, ← elec_elec (show μ⁻¹ ≠ -1 by linarith)]
        exact (elec_lt_elec_iff (by linarith) (by linarith)).2 hc₀

end ProofPhase.Unified
