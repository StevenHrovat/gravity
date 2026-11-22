/-
Proof phase, cycle 6, workstream 1 (c6a-flip): the flip probability as a function of the twist free energy, the floor
and the saturation statements, the binary-channel model, act growth with a defect, and the excess act
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c6a-flip/NOTE.md`, sections 2 to 5.
-/

import ProofPhase.DMP.VacuumAct
import Attempts.R3.MonotoneCrossing

/-!
# What a floor, a saturation and a growth law of the act each give

All statements here are real analysis about numbers that `ProofPhase.Flip.Bound` and `ProofPhase.DMP.VacuumAct` define
on the SU(2) Wilson measure; the SU(2) application is `su2_gap_of_doubling_defect`.

1. **Flip probability and free energies** (`flipP`, `twistF`, `elecF`). `p = Z_tw/(Z_tw + Z) = 1/(1 + e^{F_tw})`;
   `1 − 2p = (Z − Z_tw)/(Z + Z_tw) = e^{−F_e}` (the electric-flux ratio `Z_{e=1}/Z_{e=0}`); `½ − p = ½ tanh(F_tw/2)`;
   `F_e = dual(F_tw)` (round 3's involution). So `p ≤ ½ ⇔ Z_tw ≤ Z ⇔ Z_{e=1} ≥ 0`.
2. **Floor and saturation.** `FlipFloor p` (`∃ p_min > 0, ∀ n, p_min ≤ p n`) is equivalent to a bounded twist free energy
   (`flipFloor_iff`); `FlipSat p` (`p → ½`) is equivalent to `F_tw → 0` (`flipSat_iff`), 't Hooft's confinement
   criterion. Saturation implies the floor (`flipFloor_of_flipSat`), not conversely (a constant `p < ½`).
3. **Binary-channel model** (PREP's candidate, a model, not a theorem about the measure): a `±1` datum crossing `n` nested
   boundaries keeps the signal `∏(1 − 2p_k) = e^{−Σ F_e}` (`chainSignal_eq`). A floor gives `≤ (1 − 2p_min)^n`, which on
   dyadic boxes is a **power law** in `R = 2ⁿ` (`pow_eq_rpow_logb`) and never an exponential (`not_exponential`).
4. **Act growth with a defect.** `z(n+1) ≥ 2 z(n) − c` (the repaired super-additivity of the owner's reading; exact
   super-additivity is false for gapped models, c6c) gives `z(n) ≥ c + 2ⁿ (z 0 − c)` (`doubling_defect_floor`), hence on
   the SU(2) boxes one gap `(z₀(L₀) − c)/L₀` for every dyadic box (`su2_gap_of_doubling_defect`); a bounded act (photon,
   Heller endpoint) violates it (`bounded_violates_defect`). Fekete for super-additive sequences (`superadd_tendsto`). The
   flux-side version gives saturation of `p` (`flipSat_of_growth`).
5. **The excess act** (two witnesses). For a spectrum `x_i = λ_i/λ₀ ∈ [0, 1]`, `R(t) = Σ x_i^t`: `−log R` is
   super-additive in `t` (`excess_submul`), and the gap is bounded below by the **gluing deficit**
   `δ(t) = Z(t)²/Z(2t) − 1` (vacuum energy cancels): `x_j^t ≤ R(t) ≤ δ(t)` (`excess_le_deficit`). Positivity gives `δ ≥ 0`
   (`Z(2t) ≤ Z(t)²`), the one-witness side; a volume-uniform gap needs `δ(L) ≤ e^{−mL}` on symmetric boxes, the content.

**Claim discipline.** Sections 1, 2, 5: exact identities and equivalences (definitional / elementary). Section 3: a model.
Section 4: the SU(2) theorem is substantive only through `ProofPhase.DMP` (`E0` is the box gap); its premise is open.
-/

open Filter Topology Finset

noncomputable section

namespace ProofPhase.Flip

/-! ## 1. Flip probability and free energies -/

/-- The flip probability `p = Z_tw / (Z_tw + Z)`. -/
def flipP (Z Ztw : ℝ) : ℝ := Ztw / (Ztw + Z)

/-- The twist ('t Hooft, magnetic) free energy `F_tw = −log(Z_tw / Z)`. -/
def twistF (Z Ztw : ℝ) : ℝ := -Real.log (Ztw / Z)

/-- The electric-flux free energy `F_e = −log(Z_{e=1}/Z_{e=0}) = −log((Z − Z_tw)/(Z + Z_tw))`. -/
def elecF (Z Ztw : ℝ) : ℝ := -Real.log ((Z - Ztw) / (Z + Ztw))

theorem exp_twistF {Z Ztw : ℝ} (hZ : 0 < Z) (hT : 0 < Ztw) : Real.exp (twistF Z Ztw) = Z / Ztw := by
  unfold twistF
  rw [Real.exp_neg, Real.exp_log (div_pos hT hZ), inv_div]

theorem exp_neg_twistF {Z Ztw : ℝ} (hZ : 0 < Z) (hT : 0 < Ztw) : Real.exp (-twistF Z Ztw) = Ztw / Z := by
  unfold twistF
  rw [neg_neg, Real.exp_log (div_pos hT hZ)]

/-- **`p = 1/(1 + e^{F_tw})`.** -/
theorem flipP_eq {Z Ztw : ℝ} (hZ : 0 < Z) (hT : 0 < Ztw) : flipP Z Ztw = 1 / (1 + Real.exp (twistF Z Ztw)) := by
  rw [exp_twistF hZ hT, flipP]
  field_simp

/-- **`p ≤ ½ ⇔ Z_tw ≤ Z`.** -/
theorem flipP_le_half_iff {Z Ztw : ℝ} (h : 0 < Ztw + Z) : flipP Z Ztw ≤ 1 / 2 ↔ Ztw ≤ Z := by
  unfold flipP
  rw [div_le_iff₀ h]
  constructor <;> intro h' <;> linarith

/-- **`1 − 2p = (Z − Z_tw)/(Z + Z_tw)`**, the electric-flux ratio `Z_{e=1}/Z_{e=0}`. -/
theorem one_sub_two_flipP {Z Ztw : ℝ} (h : 0 < Ztw + Z) : 1 - 2 * flipP Z Ztw = (Z - Ztw) / (Z + Ztw) := by
  unfold flipP
  have h' : Z + Ztw ≠ 0 := by linarith
  field_simp
  ring

/-- **`1 − 2p = e^{−F_e}`** when `0 < Z_tw < Z`. -/
theorem one_sub_two_flipP_exp {Z Ztw : ℝ} (hT : 0 < Ztw) (hlt : Ztw < Z) :
    1 - 2 * flipP Z Ztw = Real.exp (-elecF Z Ztw) := by
  rw [one_sub_two_flipP (by linarith), elecF, neg_neg, Real.exp_log (div_pos (by linarith) (by linarith))]

/-- **`½ − p = ½ · (1 − e^{−F_tw})/(1 + e^{−F_tw}) = ½ tanh(F_tw/2)`.** -/
theorem half_sub_flipP {Z Ztw : ℝ} (hZ : 0 < Z) (hT : 0 < Ztw) :
    1 / 2 - flipP Z Ztw = 1 / 2 * ((1 - Real.exp (-twistF Z Ztw)) / (1 + Real.exp (-twistF Z Ztw))) := by
  rw [exp_neg_twistF hZ hT, flipP]
  field_simp
  ring

theorem tanh_half_eq (x : ℝ) : Real.tanh (x / 2) = (1 - Real.exp (-x)) / (1 + Real.exp (-x)) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hy : 0 < Real.exp (x / 2) := Real.exp_pos _
  have e1 : Real.exp (-(x / 2)) = (Real.exp (x / 2))⁻¹ := Real.exp_neg _
  have e2 : Real.exp (-x) = ((Real.exp (x / 2))⁻¹) ^ 2 := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; ring
  rw [e1, e2]
  field_simp

/-- **`½ − p = ½ tanh(F_tw / 2)`.** -/
theorem half_sub_flipP_tanh {Z Ztw : ℝ} (hZ : 0 < Z) (hT : 0 < Ztw) :
    1 / 2 - flipP Z Ztw = 1 / 2 * Real.tanh (twistF Z Ztw / 2) := by
  rw [half_sub_flipP hZ hT, tanh_half_eq]

/-- **'t Hooft's duality in flip form: `F_e = dual(F_tw)`.** -/
theorem elecF_eq_dual {Z Ztw : ℝ} (hZ : 0 < Z) (hT : 0 < Ztw) :
    elecF Z Ztw = Attempts.R3.Monotone.dual (twistF Z Ztw) := by
  unfold elecF Attempts.R3.Monotone.dual
  rw [exp_neg_twistF hZ hT]
  congr 2
  field_simp

/-! ## 2. Floor and saturation -/

/-- **The flip floor** along a sequence of boxes: `p` stays above a fixed positive level. -/
def FlipFloor (p : ℕ → ℝ) : Prop := ∃ pmin : ℝ, 0 < pmin ∧ ∀ n, pmin ≤ p n

/-- **Saturation of the reflection bound**: `p → ½` ('t Hooft's confinement criterion, `F_tw → 0`). -/
def FlipSat (p : ℕ → ℝ) : Prop := Tendsto p atTop (𝓝 (1 / 2))

theorem inv_one_add_exp_le {F G : ℝ} (h : F ≤ G) : 1 / (1 + Real.exp G) ≤ 1 / (1 + Real.exp F) :=
  one_div_le_one_div_of_le (by positivity) (by linarith [Real.exp_le_exp.2 h])

/-- **Floor ⇔ bounded twist free energy** (for `p = 1/(1 + e^F)`). -/
theorem flipFloor_iff {F : ℕ → ℝ} : FlipFloor (fun n => 1 / (1 + Real.exp (F n))) ↔ ∃ Fmax, ∀ n, F n ≤ Fmax := by
  constructor
  · rintro ⟨pmin, hp, h⟩
    refine ⟨Real.log (1 / pmin), fun n => ?_⟩
    have h1 := h n
    have hpos : 0 < 1 + Real.exp (F n) := by positivity
    rw [le_div_iff₀ hpos] at h1
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hp]
    nlinarith [Real.exp_pos (F n)]
  · rintro ⟨Fmax, h⟩
    exact ⟨1 / (1 + Real.exp Fmax), by positivity, fun n => inv_one_add_exp_le (h n)⟩

/-- **Saturation ⇔ `F_tw → 0`** (for `p = 1/(1 + e^F)`). -/
theorem flipSat_iff {F : ℕ → ℝ} : FlipSat (fun n => 1 / (1 + Real.exp (F n))) ↔ Tendsto F atTop (𝓝 0) := by
  have hc1 : Continuous fun x : ℝ => 1 / (1 + Real.exp x) :=
    continuous_const.div (continuous_const.add Real.continuous_exp) fun x => by positivity
  constructor
  · intro h
    have hc2 : ContinuousAt (fun q : ℝ => Real.log (1 / q - 1)) (1 / 2) := by
      apply ContinuousAt.log
      · exact ((continuousAt_const.div continuousAt_id (by norm_num)).sub continuousAt_const)
      · norm_num
    have e : ∀ n, Real.log (1 / (1 / (1 + Real.exp (F n))) - 1) = F n := by
      intro n; rw [one_div_one_div, add_sub_cancel_left, Real.log_exp]
    have := hc2.tendsto.comp h
    simp only [Function.comp_def, e] at this
    norm_num at this
    exact this
  · intro h
    have := (hc1.tendsto 0).comp h
    simp only [Function.comp_def, Real.exp_zero] at this
    unfold FlipSat
    convert this using 2
    norm_num

/-- **Saturation implies the floor** (when every box has `p > 0`). -/
theorem flipFloor_of_flipSat {p : ℕ → ℝ} (hpos : ∀ n, 0 < p n) (h : FlipSat p) : FlipFloor p := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually (le_mem_nhds (show (1 / 4 : ℝ) < 1 / 2 by norm_num)))
  refine ⟨min (1 / 4) ((range (N + 1)).inf' nonempty_range_add_one p), lt_min (by norm_num) ?_, fun n => ?_⟩
  · obtain ⟨k, -, hk⟩ := (range (N + 1)).exists_mem_eq_inf' nonempty_range_add_one p
    rw [hk]; exact hpos k
  · by_cases hn : N ≤ n
    · exact (min_le_left _ _).trans (hN n hn)
    · exact (min_le_right _ _).trans (inf'_le _ (mem_range.2 (by omega)))

/-! ## 3. The binary-channel model -/

/-- The signal of a `±1` datum after `n` crossings with flip probabilities `p k`: `∏_{k<n} (1 − 2 p_k)`. -/
def chainSignal (p : ℕ → ℝ) (n : ℕ) : ℝ := ∏ k ∈ range n, (1 - 2 * p k)

/-- **The signal is `e^{−Σ F_e}`**, `F_e = −log(1 − 2p)` the electric free energy per crossing. -/
theorem chainSignal_eq {p : ℕ → ℝ} (h : ∀ k, 2 * p k < 1) (n : ℕ) :
    chainSignal p n = Real.exp (-∑ k ∈ range n, -Real.log (1 - 2 * p k)) := by
  unfold chainSignal
  rw [Finset.sum_neg_distrib, neg_neg, Real.exp_sum]
  exact prod_congr rfl fun k _ => (Real.exp_log (by linarith [h k])).symm

/-- **A floor bounds the signal geometrically in the number of crossings.** -/
theorem chainSignal_le {p : ℕ → ℝ} {pmin : ℝ} (hmin : ∀ k, pmin ≤ p k) (hhalf : ∀ k, p k ≤ 1 / 2) (n : ℕ) :
    0 ≤ chainSignal p n ∧ chainSignal p n ≤ (1 - 2 * pmin) ^ n := by
  unfold chainSignal
  refine ⟨prod_nonneg fun k _ => by linarith [hhalf k], ?_⟩
  rw [show (1 - 2 * pmin) ^ n = ∏ _k ∈ range n, (1 - 2 * pmin) by rw [prod_const, card_range]]
  exact Finset.prod_le_prod₀ (h0 := fun k _ => by linarith [hhalf k]) (h1 := fun k _ => by linarith [hmin k])

/-- **On dyadic crossings a geometric signal is a power law** in `R = 2ⁿ`: `q^n = R^{log₂ q}`. -/
theorem pow_eq_rpow_logb {q : ℝ} (hq : 0 < q) (n : ℕ) : q ^ n = ((2 : ℝ) ^ n) ^ (Real.logb 2 q) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast 2 n, ← Real.rpow_mul (by norm_num), mul_comm,
    Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hq]

/-- `n·a + b < m·2ⁿ` eventually, for every `a, b` and `m > 0`. -/
theorem eventually_lt_two_pow {m : ℝ} (hm : 0 < m) (a b : ℝ) : ∃ n : ℕ, a * n + b < m * 2 ^ n := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ 1 / 2 ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num)
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num))
    simpa [Function.comp_def, one_div] using this
  have h3 : Tendsto (fun n : ℕ => |a| * ((n : ℝ) ^ 1 / 2 ^ n) + |b| * (1 / 2 ^ n)) atTop (𝓝 0) := by
    simpa using (h1.const_mul |a|).add (h2.const_mul |b|)
  obtain ⟨n, hn⟩ := (h3.eventually (gt_mem_nhds hm)).exists
  refine ⟨n, ?_⟩
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have e : |a| * ((n : ℝ) ^ 1 / 2 ^ n) + |b| * (1 / 2 ^ n) = (|a| * n + |b|) / 2 ^ n := by
    field_simp
  rw [e, div_lt_iff₀ hp] at hn
  have ha : a * n ≤ |a| * n := mul_le_mul_of_nonneg_right (le_abs_self a) (Nat.cast_nonneg n)
  linarith [le_abs_self b]

/-- **A floor never gives exponential decay in the dyadic size**: for `0 < q ≤ 1` there are no `m > 0`, `C` with
`q^n ≤ C e^{−m 2ⁿ}` for all `n` (`q > 0`; the constant-floor channel is `q = 1 − 2 p_min`). -/
theorem not_exponential {q : ℝ} (hq : 0 < q) :
    ¬∃ m C : ℝ, 0 < m ∧ ∀ n : ℕ, q ^ n ≤ C * Real.exp (-(m * 2 ^ n)) := by
  rintro ⟨m, C, hm, h⟩
  have hC : 0 < C := by
    have := h 0
    simp only [pow_zero] at this
    by_contra hC
    have hC' := not_lt.1 hC
    have := mul_nonpos_of_nonpos_of_nonneg hC' (Real.exp_pos (-(m * 1))).le
    linarith
  obtain ⟨n, hn⟩ := eventually_lt_two_pow hm (-Real.log q) (Real.log C)
  have h1 := h n
  have hl := Real.log_le_log (pow_pos hq n) h1
  rw [Real.log_pow, Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
  linarith

/-! ## 4. Act growth with a defect; Fekete; the flux side -/

/-- **The repaired super-additivity** `z(n+1) ≥ 2 z(n) − c` gives `z(n) − c ≥ 2ⁿ (z 0 − c)`. -/
theorem doubling_defect_floor {z : ℕ → ℝ} {c : ℝ} (h : ∀ n, 2 * z n - c ≤ z (n + 1)) (n : ℕ) :
    2 ^ n * (z 0 - c) ≤ z n - c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; linarith [h n]

/-- **Variable loss.** `z(n+1) ≥ 2 z(n) − c n` gives `z n / 2ⁿ ≥ z 0 − Σ_{k<n} c k / 2^{k+1}`: the loss may even grow
with the box, as long as `Σ c_k / 2^{k+1}` stays below the start act (a loss `o(L)` summably). -/
theorem doubling_variable_defect {z c : ℕ → ℝ} (h : ∀ n, 2 * z n - c n ≤ z (n + 1)) (n : ℕ) :
    z 0 - ∑ k ∈ range n, c k / 2 ^ (k + 1) ≤ z n / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hp : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    have e1 : z (n + 1) / 2 ^ (n + 1) - (z n / 2 ^ n - c n / 2 ^ (n + 1)) =
        (z (n + 1) - 2 * z n + c n) / 2 ^ (n + 1) := by
      rw [pow_succ]; field_simp; ring
    have e2 : 0 ≤ (z (n + 1) - 2 * z n + c n) / 2 ^ (n + 1) := div_nonneg (by linarith [h n]) hp.le
    linarith

/-- **A bounded act violates the repaired law** above its defect (photon `z₀ → 2π`, Heller endpoint, IR fixed point). -/
theorem bounded_violates_defect {z : ℕ → ℝ} {c B : ℝ} (hB : ∀ n, z n ≤ B) (h0 : c < z 0)
    (h : ∀ n, 2 * z n - c ≤ z (n + 1)) : False := by
  obtain ⟨n, hn⟩ := eventually_lt_two_pow (sub_pos.2 h0) 0 (B - c)
  have := doubling_defect_floor h n
  linarith [hB n]

/-- **Fekete for super-additive sequences**: if `a (m + n) ≥ a m + a n` and `a n ≤ C n`, then `a n / n` converges and
its limit bounds every `a n / n` (`n ≠ 0`) from above. -/
theorem superadd_tendsto {a : ℕ → ℝ} (hsup : ∀ m n, a m + a n ≤ a (m + n)) {C : ℝ} (hC : ∀ n, a n ≤ C * n) :
    ∃ l, Tendsto (fun n => a n / n) atTop (𝓝 l) ∧ ∀ n, n ≠ 0 → a n / n ≤ l := by
  have hsub : Subadditive fun n => -a n := fun m n => by linarith [hsup m n]
  have hbdd : BddBelow (Set.range fun n => -a n / (n : ℝ)) := by
    refine ⟨min (-C) 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [Nat.cast_zero, div_zero]; exact min_le_right _ _
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
      refine (min_le_left _ _).trans ?_
      rw [le_div_iff₀ hn']; linarith [hC n]
  refine ⟨-hsub.lim, ?_, fun n hn => ?_⟩
  · have := (hsub.tendsto_lim hbdd).neg
    simpa [neg_div] using this
  · have := hsub.lim_le_div hbdd hn
    rw [neg_div] at this; linarith

/-- **Flux-side growth gives saturation.** If `1 − 2p_n ≤ e^{−F_n}` and `F_n ≥ b + 2ⁿ a` with `a > 0`, then `p → ½`
(the flux act growing like `σL²` is more than enough). -/
theorem flipSat_of_growth {p F : ℕ → ℝ} {a b : ℝ} (ha : 0 < a) (hhalf : ∀ n, p n ≤ 1 / 2)
    (hF : ∀ n, 1 - 2 * p n ≤ Real.exp (-F n)) (hg : ∀ n, b + 2 ^ n * a ≤ F n) : FlipSat p := by
  have hlim : Tendsto (fun n : ℕ => Real.exp (-(b + 2 ^ n * a))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_left _ b ?_))
    exact (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).atTop_mul_const ha
  have hup : ∀ n, 1 / 2 - p n ≤ Real.exp (-(b + 2 ^ n * a)) / 2 := fun n => by
    have h1 := hF n
    have h2 := Real.exp_le_exp.2 (neg_le_neg (hg n))
    linarith
  have hlim2 : Tendsto (fun n : ℕ => Real.exp (-(b + 2 ^ n * a)) / 2) atTop (𝓝 0) := by
    simpa using hlim.div_const 2
  have hd : Tendsto (fun n => 1 / 2 - p n) atTop (𝓝 0) :=
    squeeze_zero (fun n => by linarith [hhalf n]) hup hlim2
  have := hd.const_sub (1 / 2)
  simp only [sub_sub_cancel, sub_zero] at this
  exact this

/-! ### The SU(2) boxes -/

open ProofPhase.DMP in
/-- **The gap from the repaired doubling law on the SU(2) boxes.** If the vacuum act numbers of the dyadic periodic
boxes obey `z₀(2ⁿ⁺¹L₀) ≥ 2 z₀(2ⁿL₀) − c` for all `n` with `0 ≤ c < z₀(L₀)`, then `m = (z₀(L₀) − c)/L₀ > 0` is a lower
bound of the box gap `E₀(2ⁿL₀)` for every `n`, and every connected time limit of every centre-even slice observable of
every dyadic box decays at rate `m`. -/
theorem su2_gap_of_doubling_defect {β : ℝ} {L₀ : ℕ} [NeZero L₀] {c : ℝ} (hc : 0 ≤ c) (h0 : c < z0 β (side L₀ 0))
    (h : ∀ n, 2 * z0 β (side L₀ n) - c ≤ z0 β (side L₀ (n + 1))) :
    ∀ n, (z0 β (side L₀ 0) - c) / L₀ ≤ E0 β (side L₀ n) ∧
      ∀ O : VacObs (side L₀ n), ∀ hh, IsConnLimit (su2W (side L₀ n) β ∅) O.f hh →
        ∀ t : ℕ, |hh t| ≤ hh 0 * Real.exp (-((z0 β (side L₀ 0) - c) / L₀ * t)) := by
  intro n
  have hL : (0 : ℝ) < L₀ := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L₀))
  have hm : 0 < (z0 β (side L₀ 0) - c) / L₀ := div_pos (by linarith) hL
  have key : 2 ^ n * (z0 β (side L₀ 0) - c) ≤ z0 β (side L₀ n) - c :=
    doubling_defect_floor (z := fun n => z0 β (side L₀ n)) h n
  have hs : ((side L₀ n : ℕ) : ℝ) = 2 ^ n * L₀ := by simp [side]
  have hE : (z0 β (side L₀ 0) - c) / L₀ ≤ E0 β (side L₀ n) := by
    have hz : z0 β (side L₀ n) = 2 ^ n * L₀ * E0 β (side L₀ n) := by rw [z0, hs]
    rw [div_le_iff₀ hL]
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have : 2 ^ n * (z0 β (side L₀ 0) - c) ≤ 2 ^ n * (E0 β (side L₀ n) * L₀) := by nlinarith
    exact le_of_mul_le_mul_left this h2
  refine ⟨hE, fun O hh hc' t => ?_⟩
  exact decayLB_of_le_E0 (hm.trans_le hE) hE hh ⟨O, hc'⟩ t

open ProofPhase.DMP in
/-- **The sector-loss hypothesis** (named, open; the owner's "only existence crosses"): per doubling the vacuum act loses
at most `log 64`, the logarithm of the number of centre-flux sectors of a periodic three-box (`e, m ∈ Z₂³`), a number
independent of `L`. -/
def SectorLoss (β : ℝ) (L₀ : ℕ) [NeZero L₀] : Prop :=
  ∀ n, 2 * z0 β (side L₀ n) - Real.log 64 ≤ z0 β (side L₀ (n + 1))

open ProofPhase.DMP in
/-- **Sector loss plus one start box above `log 64` gives one gap for all dyadic boxes** (an instance of
`su2_gap_of_doubling_defect`). -/
theorem su2_gap_of_sectorLoss {β : ℝ} {L₀ : ℕ} [NeZero L₀] (h : SectorLoss β L₀) (h0 : Real.log 64 < z0 β (side L₀ 0)) :
    ∀ n, (z0 β (side L₀ 0) - Real.log 64) / L₀ ≤ E0 β (side L₀ n) :=
  fun n => (su2_gap_of_doubling_defect (Real.log_nonneg (by norm_num)) h0 h n).1

/-! ## 5. The excess act: one witness against two -/

section Excess

variable {ι : Type*} [Fintype ι] (x : ι → ℝ)

/-- The excess partition function `R(t) = Σ_i x_i^t` (`x_i = λ_i/λ₀` over the excited states). -/
def excess (t : ℕ) : ℝ := ∑ i, x i ^ t

/-- **`−log R` is super-additive in the time extent**: `R(a + b) ≤ R(a) R(b)` (positivity alone). -/
theorem excess_submul (h0 : ∀ i, 0 ≤ x i) (a b : ℕ) : excess x (a + b) ≤ excess x a * excess x b := by
  unfold excess
  rw [sum_mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [pow_add]
  exact single_le_sum (f := fun j => x i ^ a * x j ^ b) (fun j _ => mul_nonneg (pow_nonneg (h0 i) a)
    (pow_nonneg (h0 j) b)) (mem_univ i)

/-- Every excited state bounds the excess from below: `x_j^t ≤ R(t)`. -/
theorem pow_le_excess (h0 : ∀ i, 0 ≤ x i) (j : ι) (t : ℕ) : x j ^ t ≤ excess x t :=
  single_le_sum (f := fun i => x i ^ t) (fun i _ => pow_nonneg (h0 i) t) (mem_univ j)

theorem excess_two_le (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) (t : ℕ) : excess x (2 * t) ≤ excess x t := by
  unfold excess
  refine sum_le_sum fun i _ => ?_
  rw [mul_comm, pow_mul]
  exact pow_le_pow_of_le_one (pow_nonneg (h0 i) t) (pow_le_one₀ (h0 i) (h1 i)) (by norm_num) |>.trans_eq (pow_one _)

/-- **Gluing deficit.** With `Z(t) = 1 + R(t)` (normalised by the top state), positivity gives `Z(2t) ≤ Z(t)²`
(the one-witness side), and the deficit `Z(t)²/Z(2t) − 1` bounds the excess from above. -/
theorem excess_le_deficit (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) (t : ℕ) :
    (1 + excess x (2 * t)) ≤ (1 + excess x t) ^ 2 ∧
      excess x t ≤ (1 + excess x t) ^ 2 / (1 + excess x (2 * t)) - 1 := by
  have hR : 0 ≤ excess x t := sum_nonneg fun i _ => pow_nonneg (h0 i) t
  have hR2 : 0 ≤ excess x (2 * t) := sum_nonneg fun i _ => pow_nonneg (h0 i) _
  have hle := excess_two_le x h0 h1 t
  refine ⟨by nlinarith, ?_⟩
  rw [le_sub_iff_add_le, le_div_iff₀ (by linarith)]
  nlinarith

/-- **The gap from the gluing deficit.** If an excited state has `x_j = e^{−Δ}` (one transfer step), then
`e^{−Δ t} ≤ Z(t)²/Z(2t) − 1`: a lower bound on the gap `Δ` from three partition functions with the vacuum energy
cancelled. -/
theorem gap_of_deficit (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) {j : ι} {Δ : ℝ} (hj : x j = Real.exp (-Δ)) (t : ℕ) :
    Real.exp (-(Δ * t)) ≤ (1 + excess x t) ^ 2 / (1 + excess x (2 * t)) - 1 := by
  have := pow_le_excess x h0 j t
  rw [hj, ← Real.exp_nat_mul] at this
  calc Real.exp (-(Δ * t)) = Real.exp (t * -Δ) := by ring_nf
    _ ≤ excess x t := this
    _ ≤ _ := (excess_le_deficit x h0 h1 t).2

end Excess

end ProofPhase.Flip
