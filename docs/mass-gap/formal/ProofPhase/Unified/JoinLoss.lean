/-
The join-loss round: O1 split into the electric side and the join loss, and what the transfer structure gives for the
join loss (2026-11-23). Released under Apache 2.0.

Note: `docs/unified/JOIN-LOSS.md`.
-/

import ProofPhase.Unified.GRHLens
import ProofPhase.Unified.YangMills

/-!
# O1 = electric side + join loss; the join loss in the sector form

**1. The split.** `F : ℕ → Ω → ℝ` is the electric cost `F_e` of a box of length `n` (in the series direction) with
outside `ω`.
* `JoinLoss F L l` (**named hypothesis, open**): for boxes of length at least `L`, joining two boxes in series loses at
  most `l`: for every outside `ω` of the joined box there are outsides `ω₁, ω₂` of the parts with
  `F a ω₁ + F b ω₂ − l ≤ F (a + b) ω`.
* `ElectricSide F L` (**named hypothesis, open**): `F L ω ≥ log(1 + √2)` for every outside (the hand-over value, on the
  electric side).
* `series_bound`: `k` boxes in series cost at least `k s − (k − 1) l`. `three_boxes`: `3 s − 2 l`.
* **`ymOneBox_of_split`**: side and join loss with `log μ + 2 l < 3 log(1 + √2)` give `YMOneBox` at `3 L`.
  `ymOneBox_lossless` (via `three_steps_clear`): `l = 0`, `μ ≤ 14`. **`ymOneBox_quarter`**: `l ≤ 1/4`, `μ ≤ 7`
  (`μ₄ = 6.77`). So the per-join threshold for three boxes is `(3 log(1 + √2) − log μ₄)/2 = 0.366`; the `0.244` of
  `GRH-LENS.md` 6.4 comes from the weaker iterated form `k (F − 2C)` of `flux_superadd_iter`, which charges `k` joins
  instead of `k − 1`.
* `joinLoss_of_flux`: `flux_superadd`'s hypotheses give `JoinLoss` with `l = 2C`.

**2. The sector form (transfer matrix, torus).** `Z₀, Z₁` the neutral and charged sector sums, `F = log Z₀ − log Z₁`.
* `joinLoss_eq`: the join loss is the difference of the two sectors' join excesses
  `φ_e(a, b) = log Z_e(a) + log Z_e(b) − log Z_e(a + b)`.
* `joinExcess_nonneg`: `φ_e ≥ 0` for a submultiplicative sector (power sums of a nonnegative spectrum, i.e. a positive
  transfer matrix: reflection positivity).
* `joinExcess_le_tail`: `φ_e(a, b) ≤ t_e(a) + t_e(b)`, `t_e(n) = log(Z_e(n)/λ_eⁿ)` the sector's **remnant tail** above
  its top eigenvalue `λ_e`.
* **`joinLoss_bounds`**: `−(t₁(a) + t₁(b)) ≤ l(a, b) ≤ t₀(a) + t₀(b)`.
* `tail_antitone`, `pZ_div_le`: for power sums the tail falls with the length, at most `log(1 + (d − 1) qⁿ)`.
* **`joinLoss_torus`**, **`ymOneBox_torus`**: on the torus, a neutral tail `t₀(L) ≤ τ` gives `JoinLoss … L (2τ)`, and
  with the electric side and `log μ + 4τ < 3 log(1 + √2)`, `YMOneBox` at `3 L`.
* `joinLoss_unbounded`: the structure alone (positive sectors, submultiplicativity, a unique neutral top above the
  charged top) bounds nothing: the join loss can exceed every `B`. A bound must use the size of the neutral tail.
* `joinLoss_le_iff_oplus`: in the hyperbolic ledger, a loss at most `τ` means
  `elec c(a + b) ≤ e^τ · elec(c(a) ⊕ c(b))`: the loss is the shortfall from the lossless `⊕`-composed point.

**Claim discipline.** Nothing here proves O1. Both named hypotheses stay open in four dimensions with outsides. The
sector form is for the torus (no outside) with the join along a direction of the twist plane, for a finite spectrum;
that the lattice transfer matrix gives power sums with nonnegative eigenvalues per sector is classical (reflection
positivity, Osterwalder-Seiler) and not formalised here for the gauge chain.
-/

open Finset ProofPhase.Crossover

noncomputable section

namespace ProofPhase.Unified

/-! ## 1. The split: O1 = electric side + join loss -/

section Split

variable {Ω : Type*}

/-- **The join loss (named hypothesis, open).** For boxes of length at least `L`, joining two in series loses at most
`l`: every outside `ω` of the joined box leaves outsides `ω₁, ω₂` of the two parts with
`F a ω₁ + F b ω₂ − l ≤ F (a + b) ω`. -/
def JoinLoss (F : ℕ → Ω → ℝ) (L : ℕ) (l : ℝ) : Prop :=
  ∀ a b : ℕ, L ≤ a → L ≤ b → ∀ ω : Ω, ∃ ω₁ ω₂ : Ω, F a ω₁ + F b ω₂ - l ≤ F (a + b) ω

/-- The box of length `L` costs at least `s`, for every outside. -/
def SideAt (F : ℕ → Ω → ℝ) (L : ℕ) (s : ℝ) : Prop := ∀ ω, s ≤ F L ω

/-- **The electric side at the hand-over (named hypothesis, open).** `F L ω ≥ log(1 + √2)` for every outside. -/
def ElectricSide (F : ℕ → Ω → ℝ) (L : ℕ) : Prop := SideAt F L (Real.log (1 + √2))

/-- **Boxes in series**: `k` boxes cost at least `k s − (k − 1) l` (one loss per join, `k − 1` joins). -/
theorem series_bound {F : ℕ → Ω → ℝ} {L : ℕ} {s l : ℝ} (hs : SideAt F L s) (hj : JoinLoss F L l) {k : ℕ}
    (hk : 1 ≤ k) : ∀ ω, (k : ℝ) * s - ((k : ℝ) - 1) * l ≤ F (k * L) ω := by
  induction k, hk using Nat.le_induction with
  | base => intro ω; simpa using hs ω
  | succ k hk ih =>
    intro ω
    have hkL : L ≤ k * L := by simpa using Nat.mul_le_mul hk (le_refl L)
    obtain ⟨ω₁, ω₂, h⟩ := hj (k * L) L hkL le_rfl ω
    have h1 := ih ω₁
    have h2 := hs ω₂
    rw [show (k + 1) * L = k * L + L by ring]
    have e : ((k + 1 : ℕ) : ℝ) * s - (((k + 1 : ℕ) : ℝ) - 1) * l = ((k : ℝ) * s - ((k : ℝ) - 1) * l) + s - l := by
      push_cast; ring
    rw [e]
    linarith

/-- **Three boxes in series**: `3 s − 2 l`. -/
theorem three_boxes {F : ℕ → Ω → ℝ} {L : ℕ} {s l : ℝ} (hs : SideAt F L s) (hj : JoinLoss F L l) (ω : Ω) :
    3 * s - 2 * l ≤ F (3 * L) ω := by
  have h := series_bound hs hj (k := 3) (by norm_num) ω
  norm_num at h
  linarith

/-- **O1 from the split.** The electric side at `L` and a join loss `l` with `log μ + 2 l < 3 log(1 + √2)` give the
one-box statement `YMOneBox` at `3 L`. -/
theorem ymOneBox_of_split {F : ℕ → Ω → ℝ} {L : ℕ} {l μ : ℝ} (hs : ElectricSide F L) (hj : JoinLoss F L l)
    (hl : Real.log μ + 2 * l < 3 * Real.log (1 + √2)) : YMOneBox (F (3 * L)) μ := by
  unfold YMOneBox CostAboveFloor
  exact ⟨3 * Real.log (1 + √2) - 2 * l, by linarith, fun ω => three_boxes hs hj ω⟩

/-- **The lossless case is `three_steps_clear`**: with no join loss, three hand-over boxes clear every `μ ≤ 14`. -/
theorem ymOneBox_lossless {F : ℕ → Ω → ℝ} {L : ℕ} {μ : ℝ} (hμ0 : 0 < μ) (hμ : μ ≤ 14) (hs : ElectricSide F L)
    (hj : JoinLoss F L 0) : YMOneBox (F (3 * L)) μ := by
  apply ymOneBox_of_split hs hj
  have hc := three_steps_clear hμ0.le hμ
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp : (√2 - 1) * (1 + √2) = 1 := by nlinarith
  have hq : 0 < (1 + √2) ^ 3 := by positivity
  have key : (√2 - 1) ^ 3 * μ * (1 + √2) ^ 3 = μ := by
    have h3 : ((√2 - 1) * (1 + √2)) ^ 3 = 1 := by rw [hp]; norm_num
    calc (√2 - 1) ^ 3 * μ * (1 + √2) ^ 3 = ((√2 - 1) * (1 + √2)) ^ 3 * μ := by ring
      _ = μ := by rw [h3, one_mul]
  have hlt : (√2 - 1) ^ 3 * μ * (1 + √2) ^ 3 < 1 * (1 + √2) ^ 3 := mul_lt_mul_of_pos_right hc hq
  rw [key, one_mul] at hlt
  calc Real.log μ + 2 * 0 = Real.log μ := by ring
    _ < Real.log ((1 + √2) ^ 3) := Real.log_lt_log hμ0 hlt
    _ = 3 * Real.log (1 + √2) := by rw [Real.log_pow]; norm_num

/-- **Three boxes clear the floor with a join loss up to `1/4`**, for every path entropy `μ ≤ 7` (`μ₄ = 6.77`):
`μ e^{2l} ≤ 14 < 7 + 5√2 = (1 + √2)³`. -/
theorem ymOneBox_quarter {F : ℕ → Ω → ℝ} {L : ℕ} {l μ : ℝ} (hμ0 : 0 < μ) (hμ : μ ≤ 7) (hl : l ≤ 1 / 4)
    (hs : ElectricSide F L) (hj : JoinLoss F L l) : YMOneBox (F (3 * L)) μ := by
  apply ymOneBox_of_split hs hj
  have he : Real.exp (2 * l) ≤ 2 := by
    have h1 := Real.add_one_le_exp (-(2 * l))
    have hmul : Real.exp (2 * l) * Real.exp (-(2 * l)) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [mul_nonneg (Real.exp_pos (2 * l)).le (show 0 ≤ Real.exp (-(2 * l)) - 1 / 2 by linarith)]
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs2 : 7 < 5 * √2 := by nlinarith [Real.sqrt_nonneg 2]
  have hcube : (1 + √2) ^ 3 = 7 + 5 * √2 := by linear_combination (3 + √2) * h2
  have hm : μ * Real.exp (2 * l) ≤ 7 * 2 := mul_le_mul hμ he (Real.exp_pos _).le (by norm_num)
  have hprod : μ * Real.exp (2 * l) < (1 + √2) ^ 3 := by rw [hcube]; linarith
  calc Real.log μ + 2 * l = Real.log (μ * Real.exp (2 * l)) := by
        rw [Real.log_mul hμ0.ne' (Real.exp_pos _).ne', Real.log_exp]
    _ < Real.log ((1 + √2) ^ 3) := Real.log_lt_log (by positivity) hprod
    _ = 3 * Real.log (1 + √2) := by rw [Real.log_pow]; norm_num

/-- **`flux_superadd` is a join loss**: its hypotheses, with the neutral excess act `c(n) = log(Z₀(n)/λⁿ) ≤ C` at
every length and every outside, give `JoinLoss` with `l = 2C` (same outside for the parts). -/
theorem joinLoss_of_flux {Z₀ Z₁ : Ω → ℕ → ℝ} {lam : ℝ} (hlam : 0 < lam) (h1 : ∀ ω n, 0 < Z₁ ω n)
    (h0 : ∀ ω n, lam ^ n ≤ Z₀ ω n) (hsub : ∀ ω a b, Z₁ ω (a + b) ≤ Z₁ ω a * Z₁ ω b) {C : ℝ}
    (hC : ∀ ω n, Real.log (Z₀ ω n / lam ^ n) ≤ C) (L : ℕ) :
    JoinLoss (fun n ω => Real.log (Z₀ ω n) - Real.log (Z₁ ω n)) L (2 * C) := by
  intro a b _ _ ω
  refine ⟨ω, ω, ?_⟩
  have h := flux_superadd hlam (h1 ω) (h0 ω) (hsub ω) a b
  have ha := hC ω a
  have hb := hC ω b
  dsimp only
  linarith

end Split

/-! ## 2. The sector form: the join loss is the difference of two remnant tails -/

section Sectors

/-- The join excess of one sector, `φ(a, b) = log Z(a) + log Z(b) − log Z(a + b)`. -/
def joinExcess (Z : ℕ → ℝ) (a b : ℕ) : ℝ := Real.log (Z a) + Real.log (Z b) - Real.log (Z (a + b))

/-- The electric cost from the two sectors, `F = log Z₀ − log Z₁`. -/
def fluxF (Z₀ Z₁ : ℕ → ℝ) (n : ℕ) : ℝ := Real.log (Z₀ n) - Real.log (Z₁ n)

/-- The join loss `l(a, b) = F(a) + F(b) − F(a + b)`. -/
def joinLossOf (Z₀ Z₁ : ℕ → ℝ) (a b : ℕ) : ℝ := fluxF Z₀ Z₁ a + fluxF Z₀ Z₁ b - fluxF Z₀ Z₁ (a + b)

/-- The remnant tail of a sector above `λ`: `t(n) = log(Z(n)/λⁿ)`. -/
def tail (Z : ℕ → ℝ) (lam : ℝ) (n : ℕ) : ℝ := Real.log (Z n / lam ^ n)

/-- **The join loss is the difference of the sectors' join excesses.** -/
theorem joinLoss_eq (Z₀ Z₁ : ℕ → ℝ) (a b : ℕ) :
    joinLossOf Z₀ Z₁ a b = joinExcess Z₀ a b - joinExcess Z₁ a b := by
  unfold joinLossOf fluxF joinExcess; ring

/-- **A submultiplicative sector has a nonnegative join excess.** -/
theorem joinExcess_nonneg {Z : ℕ → ℝ} (hZ : ∀ n, 0 < Z n) (hsub : ∀ a b, Z (a + b) ≤ Z a * Z b) (a b : ℕ) :
    0 ≤ joinExcess Z a b := by
  unfold joinExcess
  have h := Real.log_le_log (hZ _) (hsub a b)
  rw [Real.log_mul (hZ a).ne' (hZ b).ne'] at h
  linarith

/-- **The join excess is at most the two remnant tails**, for any `λ > 0` with `λⁿ ≤ Z(n)`. -/
theorem joinExcess_le_tail {Z : ℕ → ℝ} {lam : ℝ} (hlam : 0 < lam) (hZ : ∀ n, lam ^ n ≤ Z n) (a b : ℕ) :
    joinExcess Z a b ≤ tail Z lam a + tail Z lam b := by
  have hZp : ∀ n, 0 < Z n := fun n => (pow_pos hlam n).trans_le (hZ n)
  unfold joinExcess tail
  rw [Real.log_div (hZp a).ne' (pow_pos hlam a).ne', Real.log_div (hZp b).ne' (pow_pos hlam b).ne',
    Real.log_pow, Real.log_pow]
  have h := Real.log_le_log (pow_pos hlam _) (hZ (a + b))
  rw [Real.log_pow] at h
  push_cast at h
  rw [add_mul] at h
  linarith

/-- The tail is nonnegative when `λⁿ ≤ Z(n)`. -/
theorem tail_nonneg {Z : ℕ → ℝ} {lam : ℝ} (hlam : 0 < lam) (hZ : ∀ n, lam ^ n ≤ Z n) (n : ℕ) :
    0 ≤ tail Z lam n :=
  Real.log_nonneg ((one_le_div (pow_pos hlam n)).2 (hZ n))

/-- **The join loss lies between minus the charged tail and the neutral tail**:
`−(t₁(a) + t₁(b)) ≤ l(a, b) ≤ t₀(a) + t₀(b)`. -/
theorem joinLoss_bounds {Z₀ Z₁ : ℕ → ℝ} {lam₀ lam₁ : ℝ} (hl₀ : 0 < lam₀) (hl₁ : 0 < lam₁)
    (hZ₀ : ∀ n, lam₀ ^ n ≤ Z₀ n) (hZ₁ : ∀ n, lam₁ ^ n ≤ Z₁ n)
    (hs₀ : ∀ a b, Z₀ (a + b) ≤ Z₀ a * Z₀ b) (hs₁ : ∀ a b, Z₁ (a + b) ≤ Z₁ a * Z₁ b) (a b : ℕ) :
    -(tail Z₁ lam₁ a + tail Z₁ lam₁ b) ≤ joinLossOf Z₀ Z₁ a b ∧
      joinLossOf Z₀ Z₁ a b ≤ tail Z₀ lam₀ a + tail Z₀ lam₀ b := by
  have hp₀ : ∀ n, 0 < Z₀ n := fun n => (pow_pos hl₀ n).trans_le (hZ₀ n)
  have hp₁ : ∀ n, 0 < Z₁ n := fun n => (pow_pos hl₁ n).trans_le (hZ₁ n)
  rw [joinLoss_eq]
  have e0 := joinExcess_nonneg hp₀ hs₀ a b
  have e1 := joinExcess_nonneg hp₁ hs₁ a b
  have t0 := joinExcess_le_tail hl₀ hZ₀ a b
  have t1 := joinExcess_le_tail hl₁ hZ₁ a b
  constructor <;> linarith

variable {ι : Type*}

/-- A sector as a power sum of a spectrum `x` over the index set `s` (traces of powers of a transfer matrix). -/
def pZ (s : Finset ι) (x : ι → ℝ) (n : ℕ) : ℝ := ∑ i ∈ s, x i ^ n

/-- Power sums of a nonnegative spectrum are submultiplicative (`sum_pow_add_le`). -/
theorem pZ_submul {s : Finset ι} {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (a b : ℕ) :
    pZ s x (a + b) ≤ pZ s x a * pZ s x b :=
  sum_pow_add_le s x (fun i _ => hx i) a b

/-- Each eigenvalue's power is below the sector sum. -/
theorem pow_le_pZ {s : Finset ι} {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) {i₀ : ι} (hi : i₀ ∈ s) (n : ℕ) :
    x i₀ ^ n ≤ pZ s x n :=
  single_le_sum (f := fun i => x i ^ n) (fun i _ => pow_nonneg (hx i) n) hi

/-- **The relative sector sum falls with the length** when `λ` is the top of the spectrum. -/
theorem pZ_div_antitone {s : Finset ι} {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) {lam : ℝ} (hlam : 0 < lam)
    (hle : ∀ i ∈ s, x i ≤ lam) {m n : ℕ} (hmn : m ≤ n) : pZ s x n / lam ^ n ≤ pZ s x m / lam ^ m := by
  unfold pZ
  rw [sum_div, sum_div]
  refine sum_le_sum fun i hi => ?_
  rw [← div_pow, ← div_pow]
  exact pow_le_pow_of_le_one (div_nonneg (hx i) hlam.le) ((div_le_one hlam).2 (hle i hi)) hmn

/-- **The remnant tail falls with the length.** -/
theorem tail_antitone {s : Finset ι} {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) {i₀ : ι} (hi₀ : i₀ ∈ s) (hpos : 0 < x i₀)
    (htop : ∀ i ∈ s, x i ≤ x i₀) {m n : ℕ} (hmn : m ≤ n) : tail (pZ s x) (x i₀) n ≤ tail (pZ s x) (x i₀) m := by
  have hp : 0 < pZ s x n := (pow_pos hpos n).trans_le (pow_le_pZ hx hi₀ n)
  exact Real.log_le_log (div_pos hp (pow_pos hpos n)) (pZ_div_antitone hx hpos htop hmn)

/-- **The tail decays geometrically**: if every other eigenvalue is at most `q λ`, the relative sum is at most
`1 + (d − 1) qⁿ`, `d = |s|`. -/
theorem pZ_div_le {s : Finset ι} {x : ι → ℝ} [DecidableEq ι] {i₀ : ι} (hi₀ : i₀ ∈ s) (hpos : 0 < x i₀) {q : ℝ}
    (hq : ∀ i ∈ s, i ≠ i₀ → x i ≤ q * x i₀) (hx : ∀ i, 0 ≤ x i) (n : ℕ) :
    pZ s x n / x i₀ ^ n ≤ 1 + ((s.card : ℝ) - 1) * q ^ n := by
  have hpn : 0 < x i₀ ^ n := pow_pos hpos n
  have hsplit : pZ s x n = x i₀ ^ n + ∑ i ∈ s.erase i₀, x i ^ n := by
    unfold pZ; rw [add_sum_erase s (fun i => x i ^ n) hi₀]
  have hbound : ∑ i ∈ s.erase i₀, x i ^ n ≤ ((s.erase i₀).card : ℝ) * (q * x i₀) ^ n := by
    have := sum_le_card_nsmul (s.erase i₀) (fun i => x i ^ n) ((q * x i₀) ^ n) (fun i hi =>
      pow_le_pow_left₀ (hx i) (hq i (mem_of_mem_erase hi) (ne_of_mem_erase hi)) n)
    simpa [nsmul_eq_mul] using this
  have hcard : ((s.erase i₀).card : ℝ) = (s.card : ℝ) - 1 := by
    rw [card_erase_of_mem hi₀, Nat.cast_sub (card_pos.2 ⟨i₀, hi₀⟩)]; simp
  rw [div_le_iff₀ hpn, hsplit, add_mul, one_mul]
  rw [hcard, mul_pow] at hbound
  nlinarith [hbound]

/-- **The join loss on the torus is a `JoinLoss`**: if the neutral tail at length `L` is at most `τ`, every join of
boxes of length at least `L` loses at most `2τ` (no outside: `Ω = Unit`). -/
theorem joinLoss_torus {s₀ s₁ : Finset ι} {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) {i₀ i₁ : ι} (hi₀ : i₀ ∈ s₀)
    (hi₁ : i₁ ∈ s₁) (hp₀ : 0 < x i₀) (hp₁ : 0 < x i₁) (htop : ∀ i ∈ s₀, x i ≤ x i₀) {L : ℕ} {τ : ℝ}
    (hτ : tail (pZ s₀ x) (x i₀) L ≤ τ) :
    JoinLoss (fun n (_ : Unit) => fluxF (pZ s₀ x) (pZ s₁ x) n) L (2 * τ) := by
  intro a b ha hb _
  refine ⟨(), (), ?_⟩
  have hbd := (joinLoss_bounds hp₀ hp₁ (pow_le_pZ hx hi₀) (pow_le_pZ hx hi₁) (pZ_submul hx) (pZ_submul hx) a b).2
  have ta := tail_antitone hx hi₀ hp₀ htop ha
  have tb := tail_antitone hx hi₀ hp₀ htop hb
  unfold joinLossOf at hbd
  dsimp only
  linarith

/-- **O1 on the torus from the electric side and a small neutral tail**: `F(L) ≥ log(1 + √2)`, `t₀(L) ≤ τ` and
`log μ + 4τ < 3 log(1 + √2)` give `YMOneBox` at `3 L`. -/
theorem ymOneBox_torus {s₀ s₁ : Finset ι} {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) {i₀ i₁ : ι} (hi₀ : i₀ ∈ s₀)
    (hi₁ : i₁ ∈ s₁) (hp₀ : 0 < x i₀) (hp₁ : 0 < x i₁) (htop : ∀ i ∈ s₀, x i ≤ x i₀) {L : ℕ} {τ μ : ℝ}
    (hside : Real.log (1 + √2) ≤ fluxF (pZ s₀ x) (pZ s₁ x) L) (hτ : tail (pZ s₀ x) (x i₀) L ≤ τ)
    (hl : Real.log μ + 4 * τ < 3 * Real.log (1 + √2)) :
    YMOneBox (fun _ : Unit => fluxF (pZ s₀ x) (pZ s₁ x) (3 * L)) μ :=
  ymOneBox_of_split (F := fun n (_ : Unit) => fluxF (pZ s₀ x) (pZ s₁ x) n) (fun _ => hside)
    (joinLoss_torus hx hi₀ hi₁ hp₀ hp₁ htop hτ) (by linarith)

/-- **The structure alone bounds nothing.** Neutral sector `1, ½, …, ½` (`d` copies of `½`), charged sector `¼`:
positive, submultiplicative, unique neutral top above the charged top, and yet `l(1, 1) ≥ log(1 + d/2)`, above any
`B` for large `d`. A bound on the join loss must use the size of the neutral tail. -/
theorem joinLoss_unbounded (B : ℝ) :
    ∃ d : ℕ, B < joinLossOf (fun n => 1 + (d : ℝ) * (1 / 2 : ℝ) ^ n) (fun n => (1 / 4 : ℝ) ^ n) 1 1 := by
  refine ⟨⌈2 * Real.exp B⌉₊, ?_⟩
  set d : ℝ := (⌈2 * Real.exp B⌉₊ : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hdB : 2 * Real.exp B ≤ d := Nat.le_ceil _
  rw [joinLoss_eq]
  have e1 : joinExcess (fun n => (1 / 4 : ℝ) ^ n) 1 1 = 0 := by
    unfold joinExcess
    simp only [Real.log_pow]
    push_cast; ring
  have e0 : joinExcess (fun n => 1 + d * (1 / 2 : ℝ) ^ n) 1 1 =
      2 * Real.log (1 + d / 2) - Real.log (1 + d / 4) := by
    unfold joinExcess
    norm_num
    ring_nf
  rw [e1, e0, sub_zero]
  have hlog : Real.log (1 + d / 4) ≤ Real.log (1 + d / 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hB : B < Real.log (1 + d / 2) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith
  linarith

/-- **The join loss in the hyperbolic ledger**: a loss at most `τ` means `elec c(a + b) ≤ e^τ · elec(c(a) ⊕ c(b))`,
with `a ⊕ b = (a + b)/(1 + a b)` the lossless series composition (`elec_oplus`). -/
theorem joinLoss_le_iff_oplus {ca cb cab τ : ℝ} (ha : 0 < elec ca) (hb : 0 < elec cb) (hab : 0 < elec cab)
    (h1a : 1 + ca ≠ 0) (h1b : 1 + cb ≠ 0) (h1ab : 1 + ca * cb ≠ 0) :
    -Real.log (elec ca) + -Real.log (elec cb) - -Real.log (elec cab) ≤ τ ↔
      elec cab ≤ Real.exp τ * elec ((ca + cb) / (1 + ca * cb)) := by
  rw [elec_oplus h1a h1b h1ab]
  have e : Real.exp τ * (elec ca * elec cb) = Real.exp (τ + Real.log (elec ca) + Real.log (elec cb)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log ha, Real.exp_log hb]; ring
  rw [e, ← Real.log_le_iff_le_exp hab]
  constructor <;> intro h <;> linarith

end Sectors

end ProofPhase.Unified
