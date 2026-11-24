/-
Does GRH imply O1? The precise statement, and where the implication breaks (2026-11-24).
Released under Apache 2.0.

Note: `docs/unified/GRH-TO-O1.md`. Axiom list: `docs/unified/grh-to-o1-axioms.sh` and `.log`.
-/

import ProofPhase.API.YangMills
import ProofPhase.API.GRH
import ProofPhase.Unified.GRHLens
import Mathlib.Analysis.PSeries

/-!
# GRH and O1: no implication through the cards, zero margin on the GRH side, and the one model where zeta is the
# partition function

O1 is the open step of the Yang-Mills card (`API/YangMills.lean`, `YMOneBox`): the electric cost of the hand-over box
exceeds the path entropy `log μ`, uniformly over every outside. GRH comes in three forms here: Mathlib's
`RiemannHypothesis` (`ExtRH`), Dirichlet GRH (`ExtDirichletGRH`), and the open step of the GRH card (`ScaleSign`, Weil
positivity at every scale of a finite model of zeros). This file decides what "GRH implies O1" can mean and where it
breaks.

1. **O1 is a uniform ratio bound** (`ymOneBox_iff_ratio`). With sector weights `p₀ ω = Z_{e=0}`, `p₁ ω = Z_{e=1}`, O1 is
   exactly: some `μ' > μ` with `μ' p₁ ω ≤ p₀ ω` for every outside `ω`. So the bridge named in `GRH-LENS.md` 6.5 (a
   uniform ratio bound) is O1 itself, not a smaller statement. In margin form (`ymOneBox_iff_margin`): the shifted sector
   form `p₀ − μ p₁` is positive **with a strict margin** `δ p₁`, `δ > 0`, uniform over outsides.
2. **No implication through the cards** (`imp_all_iff_not`, `rh_imp_card_iff`, `dirichlet_imp_card_iff`,
   `grhCard_imp_card_iff`, `pair_model`). The open step of the Yang-Mills card fails on some input (`badInput`). Hence
   "RH implies O1 for every input of the card" is *equivalent* to "RH is false"; the same for Dirichlet GRH and for
   the GRH card's open step. `pair_model`: a GRH input whose open step and conclusion hold, next to a Yang-Mills input
   whose open step fails. Any proof of "GRH implies O1" must therefore use a statement that ties the gauge weights to
   zeta data (`ZetaCoupling`, section 5); no known result supplies one.
3. **The GRH-side positivity has margin exactly zero** (`grh_margin_exactly_zero`). In the finite model with `k` zeros on
   the line, the Toeplitz section at scale `k` is positive with margin `0` and with no positive margin: a polynomial
   vanishing at the `k` atoms is a null vector (`exists_null`, `toepForm_atoms_null`, `no_margin_at_closure`). O1 needs
   a strict margin (point 1). So the owner's lead "GRH is attuned by positivity towards O1, from the median" meets the
   obstruction exactly there: the positivity GRH supplies is a sign without margin; O1 is a positivity with margin, of a
   different form (the sector form shifted by `μ`). `positivity_without_o1`: positive sector weights (the encoder in the
   disk) with O1 false.
4. **The one model where zeta is the partition function: the zeros drop out** (section 4). Two-dimensional SU(2)
   Yang-Mills on a closed surface of genus `g`, zero area, has `Z = Σ n^{2−2g} = ζ(2g − 2)` (Witten 1991; external).
   The electric sectors split by the parity of the dimension `n`: `Z_{e=1} = 2^{−s} ζ(s)` and
   `Z_{e=0} = (1 − 2^{−s}) ζ(s)`, `s = 2g − 2` (`Ze1_eq`, `Ze0_eq`). Zeta cancels from every sector ratio:
   the sector domination `μ Z_{e=1} ≤ Z_{e=0}` holds exactly when `μ + 1 ≤ 2^s` (`sector_dom_iff`), and the twist ratio is
   `1 − 2^{1−s}` (`twist_ratio`), one Euler factor at `p = 2`. `zeta_re_eq` identifies `Z` with Mathlib's
   `riemannZeta s`. So even where zeta literally is the partition function, the O1-type statement is decided without
   the zeros, and RH plays no part.
5. **The missing claim, named** (`ZetaCoupling`). A coupling of the hand-over box's sector ratio to zeta data, effective
   under RH. With RH it gives O1 (`o1_of_coupling`); O1 gives it with RH unused (`coupling_of_o1`). So it is no easier
   than O1, and it is the exact intermediate claim no known result supplies.
6. **The candidate shared statement** (section 6). Growing support restricts one form (`sec_restrict`), it does not
   iterate a map. On one sequence of ticks, O1 at every tick drives the carried (Szego) margin to zero
   (`o1_ticks_kill_margin`, `uniform_margin_excludes_o1`). The multiplicative transport of a margin is a lower bound on
   the per-tick factor, O1 an upper bound; neither implies the other (`transport_not_decay`, `decay_not_transport`).
   Birkhoff's bounded projective spread on the two-sector cone and O1's uniform ratio bound are independent
   (`spread_without_o1`, `o1_without_spread`).

Nothing here proves GRH, O1 or the mass gap. Standard axioms only.
-/

noncomputable section

namespace ProofPhase.Unified.GRHToO1

open Finset ProofPhase.Unified
open scoped ComplexConjugate

universe v

/-! ### 1. O1 is a uniform ratio bound, and a positivity with a strict margin -/

/-- **O1 is a uniform ratio bound.** With positive sector weights `p₀ = Z_{e=0}`, `p₁ = Z_{e=1}` and the electric cost
`F_e = log(p₀/p₁)`, O1 holds exactly when one ratio `μ' > μ` dominates every outside: `μ' p₁ ω ≤ p₀ ω`. -/
theorem ymOneBox_iff_ratio {Ω : Type*} {p₀ p₁ : Ω → ℝ} (h0 : ∀ ω, 0 < p₀ ω) (h1 : ∀ ω, 0 < p₁ ω) {μ : ℝ}
    (hμ : 0 < μ) :
    YMOneBox (fun ω => Real.log (p₀ ω / p₁ ω)) μ ↔ ∃ μ' : ℝ, μ < μ' ∧ ∀ ω, μ' * p₁ ω ≤ p₀ ω := by
  unfold YMOneBox CostAboveFloor
  constructor
  · rintro ⟨κ, hκ, h⟩
    refine ⟨Real.exp κ, ?_, fun ω => ?_⟩
    · calc μ = Real.exp (Real.log μ) := (Real.exp_log hμ).symm
        _ < Real.exp κ := Real.exp_lt_exp.2 hκ
    · have hr : Real.exp κ ≤ p₀ ω / p₁ ω :=
        calc Real.exp κ ≤ Real.exp (Real.log (p₀ ω / p₁ ω)) := Real.exp_le_exp.2 (h ω)
          _ = p₀ ω / p₁ ω := Real.exp_log (div_pos (h0 ω) (h1 ω))
      rwa [le_div_iff₀ (h1 ω)] at hr
  · rintro ⟨μ', hμ', h⟩
    have hμ'0 : 0 < μ' := hμ.trans hμ'
    exact ⟨Real.log μ', Real.log_lt_log hμ hμ', fun ω =>
      Real.log_le_log hμ'0 ((le_div_iff₀ (h1 ω)).2 (h ω))⟩

/-- **O1 as a positivity with a strict margin**: the shifted sector form `p₀ − μ p₁` is at least `δ p₁` with one `δ > 0`
for every outside. -/
theorem ymOneBox_iff_margin {Ω : Type*} {p₀ p₁ : Ω → ℝ} (h0 : ∀ ω, 0 < p₀ ω) (h1 : ∀ ω, 0 < p₁ ω) {μ : ℝ}
    (hμ : 0 < μ) :
    YMOneBox (fun ω => Real.log (p₀ ω / p₁ ω)) μ ↔ ∃ δ : ℝ, 0 < δ ∧ ∀ ω, δ * p₁ ω ≤ p₀ ω - μ * p₁ ω := by
  rw [ymOneBox_iff_ratio h0 h1 hμ]
  constructor
  · rintro ⟨μ', hμ', h⟩
    exact ⟨μ' - μ, by linarith, fun ω => by linarith [h ω]⟩
  · rintro ⟨δ, hδ, h⟩
    exact ⟨μ + δ, by linarith, fun ω => by linarith [h ω]⟩

/-- The cost in the ratio form is the encoder's electric cost: `−log elec c = log(p₀/p₁)` for `c = (p₀ − p₁)/(p₀ + p₁)`
(`GRHLens.z2_sectors`). -/
theorem cost_eq_log_ratio {p₀ p₁ : ℝ} (h0 : 0 < p₀) (h1 : 0 ≤ p₁) :
    -Real.log (elec ((p₀ - p₁) / (p₀ + p₁))) = Real.log (p₀ / p₁) := by
  rw [(z2_sectors h0 h1).2.1, ← Real.log_inv, inv_div]

/-! ### 2. No implication through the cards -/

/-- **The logical shape.** For any statement `H` and any problem card whose open step fails on some input, "`H` implies
the open step on every input" is equivalent to "`H` is false". -/
theorem imp_all_iff_not {P : ProofPhase.API.Problem.{v}} {H : Prop} (hbad : ∃ i, ¬ P.Open i) :
    (H → ∀ i, P.Open i) ↔ ¬ H :=
  ⟨fun h hH => hbad.elim fun i hi => hi (h hH i), fun h hH => absurd hH h⟩

/-- A Yang-Mills input on which the open step fails: one outside, two continuations, electric cost `0`. -/
def badInput : ProofPhase.API.YangMills.Input where
  Ω := Unit
  d := 2
  d_pos := by norm_num
  w _ _ := 0
  Fe _ := 0
  w_nonneg _ _ := le_rfl
  w_le _ _ := (Real.exp_pos _).le
  outsides _ := ()

/-- On `badInput` the cost `0` is below the path entropy `log 2`, so O1 fails there. -/
theorem badInput_not_open : ¬ ProofPhase.API.YangMills.problem.Open badInput := by
  intro h
  obtain ⟨κ, hκ, hc⟩ := (h : YMOneBox badInput.Fe (Fintype.card (Fin badInput.d)))
  have h1 : κ ≤ 0 := hc ()
  have h2 : (0 : ℝ) < Real.log (Fintype.card (Fin badInput.d)) := by
    show (0 : ℝ) < Real.log (Fintype.card (Fin 2))
    rw [Fintype.card_fin]
    exact Real.log_pos (by norm_num)
  linarith

theorem ym_card_bad : ∃ i, ¬ ProofPhase.API.YangMills.problem.Open i := ⟨badInput, badInput_not_open⟩

/-- **RH implies O1 on every input of the card exactly when RH is false.** So no proof of "RH ⇒ O1" can treat the
Yang-Mills input as free data. -/
theorem rh_imp_card_iff :
    (ExtRH → ∀ i, ProofPhase.API.YangMills.problem.Open i) ↔ ¬ ExtRH :=
  imp_all_iff_not ym_card_bad

/-- The same for Dirichlet GRH. -/
theorem dirichlet_imp_card_iff :
    (ExtDirichletGRH → ∀ i, ProofPhase.API.YangMills.problem.Open i) ↔
      ¬ ExtDirichletGRH :=
  imp_all_iff_not ym_card_bad

/-- The same for the open step of the GRH card (Weil positivity at every scale of some finite model). -/
theorem grhCard_imp_card_iff :
    ((∃ g, ProofPhase.API.GRH.problem.Open g) → ∀ i, ProofPhase.API.YangMills.problem.Open i) ↔
      ¬ ∃ g, ProofPhase.API.GRH.problem.Open g :=
  imp_all_iff_not ym_card_bad

/-- One zero at the centre `s = 1/2` (`γ = 0`), weight `1`: the smallest finite model, all moments `1`. -/
def oneZero : ZeroModel 1 where
  γ _ := 0
  σ := id
  hσ _ := by simp
  ε := 1
  hε := one_pos
  hinj := fun a b _ => Subsingleton.elim a b
  w _ := 1
  hw _ := one_ne_zero
  t _ := 1
  ht _ := by simp
  hmom n := by simp

/-- **The pair model.** A GRH input whose open step (Weil positivity at every scale) and conclusion hold, next to a
Yang-Mills input whose open step fails. -/
theorem pair_model : ∃ (g : ProofPhase.API.GRH.Input) (y : ProofPhase.API.YangMills.Input),
    ProofPhase.API.GRH.problem.Open g ∧ ProofPhase.API.GRH.problem.Concl g ∧
      ¬ ProofPhase.API.YangMills.problem.Open y := by
  have hg : ProofPhase.API.GRH.problem.Open ⟨1, oneZero⟩ :=
    scaleSign_of_online oneZero (fun _ => ⟨1, zero_le_one, by simp [oneZero]⟩)
      (fun _ => by simp [oneZero])
  exact ⟨⟨1, oneZero⟩, badInput, hg, ProofPhase.API.GRH.problem.holds _ hg, badInput_not_open⟩

/-! ### 3. The GRH-side positivity has margin exactly zero -/

/-- The Toeplitz form of the moments of finitely many nonzero atoms vanishes on every vector whose polynomial vanishes
at all atoms. -/
theorem toepForm_atoms_null {k : ℕ} (z : Fin k → ℂ) (w : Fin k → ℂ) (hz : ∀ i, z i ≠ 0) (t : ℤ → ℂ)
    (ht : ∀ m : ℤ, t m = ∑ i, w i * z i ^ m) (s : Finset ℕ) (c : ℕ → ℂ)
    (hc : ∀ i, ∑ l ∈ s, c l * z i ^ l = 0) : ProofPhase.GRH.toepForm t s c = 0 := by
  unfold ProofPhase.GRH.toepForm
  have hm : ∀ j l : ℕ, t ((l : ℤ) - j) = ∑ i, w i * (z i ^ l * (z i ^ j)⁻¹) := by
    intro j l
    rw [ht]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zpow_sub₀ (hz i), zpow_natCast, zpow_natCast, div_eq_mul_inv]
  have hi : ∀ i, ∑ j ∈ s, ∑ l ∈ s, conj (c j) * c l * (w i * (z i ^ l * (z i ^ j)⁻¹)) = 0 := by
    intro i
    refine Finset.sum_eq_zero fun j _ => ?_
    have e : ∑ l ∈ s, conj (c j) * c l * (w i * (z i ^ l * (z i ^ j)⁻¹)) =
        conj (c j) * w i * (z i ^ j)⁻¹ * ∑ l ∈ s, c l * z i ^ l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e, hc i, mul_zero]
  calc ∑ j ∈ s, ∑ l ∈ s, conj (c j) * c l * t ((l : ℤ) - j)
      = ∑ j ∈ s, ∑ l ∈ s, ∑ i, conj (c j) * c l * (w i * (z i ^ l * (z i ^ j)⁻¹)) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        rw [hm, Finset.mul_sum]
    _ = ∑ j ∈ s, ∑ i, ∑ l ∈ s, conj (c j) * c l * (w i * (z i ^ l * (z i ^ j)⁻¹)) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i, ∑ j ∈ s, ∑ l ∈ s, conj (c j) * c l * (w i * (z i ^ l * (z i ^ j)⁻¹)) := Finset.sum_comm
    _ = 0 := Finset.sum_eq_zero fun i _ => hi i

/-- **A null vector at the closure.** For `k` points there is a vector on the cells `0 .. k`, with last entry `1`, whose
polynomial vanishes at every point: the coefficients of `∏ (X − z_i)`. -/
theorem exists_null {k : ℕ} (z : Fin k → ℂ) :
    ∃ c : ℕ → ℂ, c k = 1 ∧ ∀ i, ∑ l ∈ range (k + 1), c l * z i ^ l = 0 := by
  classical
  set P : Polynomial ℂ := ∏ i : Fin k, (Polynomial.X - Polynomial.C (z i)) with hP
  have hmon : P.Monic := Polynomial.monic_prod_X_sub_C z univ
  have hdeg : P.natDegree = k := by
    rw [hP, Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (z i))]
    simp
  refine ⟨fun l => P.coeff l, ?_, fun i => ?_⟩
  · show P.coeff k = 1
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  · rw [← Polynomial.eval_eq_sum_range' (by omega : P.natDegree < k + 1), hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (mem_univ i) (by simp)

/-- **No positive margin at the closure.** For moments of `k` nonzero atoms (every integer exponent), a certified margin
`e` of the section at scale `k` (cells `0 .. k`) is at most `0`. -/
theorem no_margin_at_closure {k : ℕ} (z : Fin k → ℂ) (w : Fin k → ℂ) (hz : ∀ i, z i ≠ 0) (t : ℤ → ℂ)
    (ht : ∀ m : ℤ, t m = ∑ i, w i * z i ^ m) {e : ℝ} (h : Sec t k e) : e ≤ 0 := by
  obtain ⟨c, hck, hc⟩ := exists_null z
  have hs := h c
  rw [toepForm_atoms_null z w hz t ht (range (k + 1)) c hc, Complex.zero_re] at hs
  have hpos : 1 ≤ ∑ j ∈ range (k + 1), ‖c j‖ ^ 2 := by
    have := Finset.single_le_sum (f := fun j => ‖c j‖ ^ 2) (fun j _ => sq_nonneg _)
      (mem_range.2 (Nat.lt_succ_self k))
    simp only [hck, norm_one, one_pow] at this
    exact this
  nlinarith

/-- **The GRH card's positivity has margin exactly zero.** In a finite model of `k` zeros with multiplicity weights,
under the card's open step (`ScaleSign`), the section at scale `k` is positive (margin `0` certified) and no positive
margin is: the sign holds with no slack. -/
theorem grh_margin_exactly_zero {k : ℕ} (Z : ZeroModel k) (hw : ∀ i, ∃ r : ℝ, 0 ≤ r ∧ Z.w i = r)
    (h : ScaleSign Z.t) : Sec Z.t k 0 ∧ ∀ e, Sec Z.t k e → e ≤ 0 := by
  refine ⟨fun c => ?_, fun e he => ?_⟩
  · rw [zero_mul]
    exact ((scaleSign_iff Z.t).1 h).2 k c
  · choose r _ hr using hw
    have hreal := (grh_instance Z h).1
    have hz : ∀ i, ‖Complex.exp (Complex.I * Z.γ i * Z.ε)‖ = 1 := by
      intro i
      rw [Complex.norm_exp]
      simp [Complex.mul_re, hreal i]
    have hmom' : ∀ n : ℕ, Z.t n = ∑ i, (r i : ℂ) * (Complex.exp (Complex.I * Z.γ i * Z.ε)) ^ n := fun n => by
      rw [Z.hmom n]
      simp [hr]
    have ht' := moments_zpow _ r hz Z.t Z.ht hmom'
    exact no_margin_at_closure _ (fun i => (r i : ℂ)) (fun i => Complex.exp_ne_zero _) Z.t ht' he

/-- **Positivity without O1.** Positive sector weights (both sectors, the encoder strictly inside the disk) with O1 false,
for every floor `μ ≥ 1` (the hand-over's `μ₄ = 6.77` included): equal weights. -/
theorem positivity_without_o1 {μ : ℝ} (hμ : 1 ≤ μ) :
    ∃ p₀ p₁ : Unit → ℝ, (∀ ω, 0 < p₀ ω) ∧ (∀ ω, 0 < p₁ ω) ∧
      (∀ ω, |(p₀ ω - p₁ ω) / (p₀ ω + p₁ ω)| < 1) ∧ ¬ YMOneBox (fun ω => Real.log (p₀ ω / p₁ ω)) μ := by
  refine ⟨fun _ => 1, fun _ => 1, fun _ => one_pos, fun _ => one_pos, fun _ => by norm_num, ?_⟩
  rintro ⟨κ, hκ, hc⟩
  have h1 : κ ≤ Real.log (1 / 1) := hc ()
  rw [div_one, Real.log_one] at h1
  have := Real.log_nonneg hμ
  linarith

/-! ### 4. The one model where zeta is the partition function: the zeros drop out

Two-dimensional SU(2) Yang-Mills on a closed surface of genus `g ≥ 2`, at zero area (the topological limit), has
`Z = Σ_{n ≥ 1} n^{2−2g}`, a sum over the irreducible representations (dimension `n`) [external: Witten 1991]. The centre
`−1` acts on the representation of dimension `n` by `(−1)^{n+1}`, so the electric sector `e = 0` collects the odd `n`
(integer spin) and `e = 1` the even `n` (half-integer spin) [classical]. With `s = 2g − 2 > 1` the weights are `n^{−s}`. -/

/-- The weight `n^{−s}` of the representation of dimension `n` (the `n = 0` term is `0`). -/
def dimWeight (s : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-s)

/-- The partition function: `Σ n^{−s}`, which is `ζ(s)` (`zeta_re_eq`). -/
def Z2d (s : ℝ) : ℝ := ∑' n, dimWeight s n

/-- The sector `e = 1` (even dimension, half-integer spin). -/
def Ze1 (s : ℝ) : ℝ := ∑' n, dimWeight s (2 * n)

/-- The sector `e = 0` (odd dimension, integer spin). -/
def Ze0 (s : ℝ) : ℝ := ∑' n, dimWeight s (2 * n + 1)

theorem summable_dimWeight {s : ℝ} (hs : 1 < s) : Summable (dimWeight s) :=
  Real.summable_nat_rpow.2 (by linarith)

theorem dimWeight_nonneg (s : ℝ) (n : ℕ) : 0 ≤ dimWeight s n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

theorem dimWeight_even (s : ℝ) (n : ℕ) : dimWeight s (2 * n) = 2 ^ (-s) * dimWeight s n := by
  unfold dimWeight
  push_cast
  exact Real.mul_rpow (by norm_num) (Nat.cast_nonneg n)

/-- **`Z_{e=1} = 2^{−s} ζ(s)`.** -/
theorem Ze1_eq (s : ℝ) : Ze1 s = 2 ^ (-s) * Z2d s := by
  unfold Ze1 Z2d
  simp_rw [dimWeight_even]
  exact tsum_mul_left

/-- **`Z_{e=0} = (1 − 2^{−s}) ζ(s)`.** -/
theorem Ze0_eq {s : ℝ} (hs : 1 < s) : Ze0 s = (1 - 2 ^ (-s)) * Z2d s := by
  have hsum := summable_dimWeight hs
  have he : Summable fun k => dimWeight s (2 * k) := by
    simp_rw [dimWeight_even]
    exact hsum.mul_left _
  have ho : Summable fun k => dimWeight s (2 * k + 1) :=
    hsum.comp_injective (fun a b h => by omega)
  have hsplit := tsum_even_add_odd he ho
  have h1 := Ze1_eq s
  unfold Ze1 at h1
  unfold Ze0
  unfold Z2d at h1 ⊢
  linarith

theorem Z2d_pos {s : ℝ} (hs : 1 < s) : 0 < Z2d s :=
  (summable_dimWeight hs).tsum_pos (dimWeight_nonneg s) 1 (by simp [dimWeight])

/-- **The sector domination in this model is decided by `s` alone**: `μ Z_{e=1} ≤ Z_{e=0}` exactly when `μ + 1 ≤ 2^s`.
Zeta cancels; no statement about its zeros enters. -/
theorem sector_dom_iff {s μ : ℝ} (hs : 1 < s) : μ * Ze1 s ≤ Ze0 s ↔ μ + 1 ≤ 2 ^ s := by
  have hZ := Z2d_pos hs
  have h2 : (0 : ℝ) < 2 ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hinv : (2 : ℝ) ^ s * (2 ^ s)⁻¹ = 1 := mul_inv_cancel₀ h2.ne'
  rw [Ze1_eq, Ze0_eq hs, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  constructor
  · intro h
    have hm := mul_le_mul_of_nonneg_left h h2.le
    have e1 : (2 : ℝ) ^ s * (μ * ((2 ^ s)⁻¹ * Z2d s)) = μ * Z2d s * ((2 : ℝ) ^ s * (2 ^ s)⁻¹) := by ring
    have e2 : (2 : ℝ) ^ s * ((1 - (2 ^ s)⁻¹) * Z2d s) = (2 ^ s - (2 : ℝ) ^ s * (2 ^ s)⁻¹) * Z2d s := by ring
    rw [e1, e2, hinv, mul_one] at hm
    have := le_of_mul_le_mul_right hm hZ
    linarith
  · intro h
    have h1 : μ ≤ 2 ^ s - 1 := by linarith
    have e : (1 - ((2 : ℝ) ^ s)⁻¹) * Z2d s = (2 ^ s - 1) * ((2 ^ s)⁻¹ * Z2d s) := by
      rw [show ((2 : ℝ) ^ s - 1) * ((2 ^ s)⁻¹ * Z2d s) = ((2 : ℝ) ^ s * (2 ^ s)⁻¹ - (2 ^ s)⁻¹) * Z2d s by ring, hinv]
    rw [e]
    exact mul_le_mul_of_nonneg_right h1 (mul_nonneg (inv_nonneg.2 h2.le) hZ.le)

/-- **The twist ratio is one Euler factor**: `Z_tw/Z = (Z_{e=0} − Z_{e=1})/Z = 1 − 2 · 2^{−s} = 1 − 2^{1−s}`. -/
theorem twist_ratio {s : ℝ} (hs : 1 < s) : (Ze0 s - Ze1 s) / Z2d s = 1 - 2 * 2 ^ (-s) := by
  rw [Ze0_eq hs, Ze1_eq, show (1 - (2 : ℝ) ^ (-s)) * Z2d s - 2 ^ (-s) * Z2d s = (1 - 2 * 2 ^ (-s)) * Z2d s by ring,
    mul_div_assoc, div_self (Z2d_pos hs).ne', mul_one]

/-- **The partition function is Mathlib's zeta**: `Z = re ζ(s)` for real `s > 1`. -/
theorem zeta_re_eq {s : ℝ} (hs : 1 < s) : (riemannZeta s).re = Z2d s := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hs)]
  have hterm : ∀ n : ℕ, (1 / (n : ℂ) ^ (s : ℂ)) = ((dimWeight s n : ℝ) : ℂ) := by
    intro n
    rw [dimWeight, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.ofReal_neg,
      Complex.cpow_neg, one_div]
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  rfl

/-! ### 5. The missing claim, named -/

/-- **The missing bridge** (no known result supplies it). A coupling of the hand-over box to zeta data: one bound `B`
on the sector ratio `p₁/p₀ = Z_{e=1}/Z_{e=0}`, valid for every outside, with `B ≤ 1/μ'` for some `μ' > μ` as soon as RH
holds. -/
def ZetaCoupling {Ω : Type*} (p₀ p₁ : Ω → ℝ) (μ : ℝ) : Prop :=
  ∃ B μ' : ℝ, μ < μ' ∧ (ExtRH → B ≤ 1 / μ') ∧ ∀ ω, p₁ ω / p₀ ω ≤ B

/-- **With the coupling, RH gives O1.** -/
theorem o1_of_coupling {Ω : Type*} {p₀ p₁ : Ω → ℝ} (h0 : ∀ ω, 0 < p₀ ω) (h1 : ∀ ω, 0 < p₁ ω) {μ : ℝ} (hμ : 0 < μ)
    (hC : ZetaCoupling p₀ p₁ μ) (hRH : ExtRH) :
    YMOneBox (fun ω => Real.log (p₀ ω / p₁ ω)) μ := by
  obtain ⟨B, μ', hμ', hB, hr⟩ := hC
  have hμ'0 : 0 < μ' := hμ.trans hμ'
  refine (ymOneBox_iff_ratio h0 h1 hμ).2 ⟨μ', hμ', fun ω => ?_⟩
  have h := (hr ω).trans (hB hRH)
  rw [div_le_div_iff₀ (h0 ω) hμ'0, one_mul] at h
  linarith

/-- **O1 gives the coupling, with RH unused**: the coupling is no easier than O1. -/
theorem coupling_of_o1 {Ω : Type*} {p₀ p₁ : Ω → ℝ} (h0 : ∀ ω, 0 < p₀ ω) (h1 : ∀ ω, 0 < p₁ ω) {μ : ℝ} (hμ : 0 < μ)
    (h : YMOneBox (fun ω => Real.log (p₀ ω / p₁ ω)) μ) : ZetaCoupling p₀ p₁ μ := by
  obtain ⟨μ', hμ', hr⟩ := (ymOneBox_iff_ratio h0 h1 hμ).1 h
  have hμ'0 : 0 < μ' := hμ.trans hμ'
  refine ⟨1 / μ', μ', hμ', fun _ => le_rfl, fun ω => ?_⟩
  rw [div_le_div_iff₀ (h0 ω) hμ'0, one_mul]
  linarith [hr ω]

/-! ### 6. The candidate shared statement: one tick, opposite bounds

The leads of 2026-11-24 (`PREP.md`, last entries): Weil's form has a certified positive margin at the start
`{∞, 2, 3}` (`GRH/OneBoxCert.lean`); carrying it outward needs a step multiplicative in the margin (`INDUCTION.md` 1);
the proposed shared statement is Birkhoff-Hopf, a tick of uniformly bounded projective diameter. Three checks:

* `sec_restrict`: growing support restricts one form to nested sections; the margin is monotone. It is not an iterate
  of a map.
* `o1_ticks_kill_margin`, `uniform_margin_excludes_o1`: on one sequence of ticks, encoders bounded away from the
  lossless point (O1 at each tick) drive the Szego product, the margin those ticks carry, to zero. A uniform margin and
  O1 at every tick exclude each other.
* `transport_not_decay`, `decay_not_transport`: the multiplicative transport of the margin is a *lower* bound on the
  per-tick factor; O1 is an *upper* bound on it. Neither implies the other.
* `spread_without_o1`, `o1_without_spread`: on the two-sector cone, a uniformly bounded Hilbert projective spread of
  the sector ratios over outsides (Birkhoff's diameter) and O1's uniform ratio bound are independent. -/

/-- **The margin is monotone: nested restriction, not iteration.** A certified margin at scale `k + 1` is a certified
margin at scale `k`. -/
theorem sec_restrict {t : ℤ → ℂ} {k : ℕ} {e : ℝ} (h : Sec t (k + 1) e) : Sec t k e := by
  intro c
  have hs : range (k + 1) ⊆ range (k + 1 + 1) := range_subset_range.2 (Nat.le_succ _)
  have hc := h (fun j => if j ∈ range (k + 1) then c j else 0)
  rw [toepForm_indicator t hs c] at hc
  have hn : ∑ j ∈ range (k + 1 + 1), ‖(if j ∈ range (k + 1) then c j else 0)‖ ^ 2 =
      ∑ j ∈ range (k + 1), ‖c j‖ ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_congr rfl (fun j hj => by simp [hj] :
      ∀ j ∈ range (k + 1), ‖(if j ∈ range (k + 1) then c j else 0)‖ ^ 2 = ‖c j‖ ^ 2)]
    simp
  rwa [hn] at hc

/-- **O1 at every tick drives the carried margin to zero.** If every encoder `c n` of a chain of ticks is at least
`θ > 0` from the lossless point (O1 at a tick is `c ≥ (μ − 1)/(μ + 1)`), the Szego product `∏ (1 − c n ^ 2)`, the
margin those ticks carry (`E_N = E_{N−1} (1 − k_N ^ 2)`, `INDUCTION.md` 1), falls below every `m > 0`. -/
theorem o1_ticks_kill_margin {c : ℕ → ℝ} {θ : ℝ} (hθ : 0 < θ) (hc : ∀ n, θ ≤ |c n| ∧ |c n| ≤ 1) {m : ℝ}
    (hm : 0 < m) : ∃ N, ∏ n ∈ range N, (1 - c n ^ 2) < m := by
  have hθ1 : θ ≤ 1 := (hc 0).1.trans (hc 0).2
  have hq1 : 1 - θ ^ 2 < 1 := by nlinarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hm hq1
  refine ⟨N, lt_of_le_of_lt ?_ hN⟩
  calc ∏ n ∈ range N, (1 - c n ^ 2) ≤ ∏ _n ∈ range N, (1 - θ ^ 2) := by
        refine Finset.prod_le_prod₀ (fun n _ => ?_) (fun n _ => ?_)
        · have h2 := (hc n).2
          nlinarith [sq_abs (c n), abs_nonneg (c n)]
        · have h2 := (hc n).1
          nlinarith [sq_abs (c n)]
    _ = (1 - θ ^ 2) ^ N := by rw [prod_const, card_range]

/-- **A uniform margin excludes O1 at every tick**: if the carried margin stays above `m > 0` at every scale, the
encoders cannot all stay `θ > 0` away from the lossless point. -/
theorem uniform_margin_excludes_o1 {c : ℕ → ℝ} {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m)
    (hmar : ∀ N, m ≤ ∏ n ∈ range N, (1 - c n ^ 2)) : ¬ ∀ n, θ ≤ |c n| ∧ |c n| ≤ 1 := by
  intro hc
  obtain ⟨N, hN⟩ := o1_ticks_kill_margin hθ hc hm
  linarith [hmar N]

/-- **The multiplicative transport of a margin** (the step `INDUCTION.md` asks for): one positive lower bound on every
per-tick factor. -/
def TransportStep (f : ℕ → ℝ) : Prop := ∃ q : ℝ, 0 < q ∧ ∀ n, q ≤ f n

/-- **O1 in factor form**: one upper bound `ρ < 1/μ` on every per-tick factor (the cost exceeds the floor `log μ`). -/
def DecayStep (f : ℕ → ℝ) (μ : ℝ) : Prop := ∃ ρ : ℝ, ρ * μ < 1 ∧ ∀ n, f n ≤ ρ

/-- Lossless ticks carry every margin and fail O1. -/
theorem transport_not_decay {μ : ℝ} (hμ : 1 ≤ μ) : TransportStep (fun _ => 1) ∧ ¬ DecayStep (fun _ => 1) μ := by
  refine ⟨⟨1, one_pos, fun _ => le_rfl⟩, ?_⟩
  rintro ⟨ρ, hρ, h⟩
  have h0 : (1 : ℝ) ≤ ρ := h 0
  nlinarith

/-- Ticks with factors `2^{−n}/(2μ)` satisfy O1 and carry no margin. -/
theorem decay_not_transport {μ : ℝ} (hμ : 0 < μ) :
    DecayStep (fun n => (1 / 2 : ℝ) ^ n / (2 * μ)) μ ∧ ¬ TransportStep (fun n => (1 / 2 : ℝ) ^ n / (2 * μ)) := by
  have h2 : 0 < 2 * μ := by positivity
  refine ⟨⟨1 / (2 * μ), ?_, fun n => ?_⟩, ?_⟩
  · rw [div_mul_eq_mul_div, one_mul, div_lt_one h2]
    linarith
  · show (1 / 2 : ℝ) ^ n / (2 * μ) ≤ 1 / (2 * μ)
    gcongr
    exact pow_le_one₀ (by norm_num) (by norm_num)
  · rintro ⟨q, hq, h⟩
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hq h2) (by norm_num : (1 / 2 : ℝ) < 1)
    have h' : q ≤ (1 / 2 : ℝ) ^ n / (2 * μ) := h n
    rw [le_div_iff₀ h2] at h'
    linarith

/-- **Birkhoff's diameter on the two-sector cone**: the Hilbert projective distance between the sector rays of any two
outsides, `|log(p₁/p₀)(ω) − log(p₁/p₀)(ω')|`, is bounded. -/
def BoundedSpread {Ω : Type*} (p₀ p₁ : Ω → ℝ) : Prop :=
  ∃ D : ℝ, ∀ ω ω', |Real.log (p₁ ω / p₀ ω) - Real.log (p₁ ω' / p₀ ω')| ≤ D

/-- **Bounded spread without O1**: all outsides at the same ray (diameter `0`), at the lossless-side ratio `1`. -/
theorem spread_without_o1 {μ : ℝ} (hμ : 1 ≤ μ) :
    ∃ p₀ p₁ : Unit → ℝ, (∀ ω, 0 < p₀ ω) ∧ (∀ ω, 0 < p₁ ω) ∧ BoundedSpread p₀ p₁ ∧
      ¬ YMOneBox (fun ω => Real.log (p₀ ω / p₁ ω)) μ := by
  refine ⟨fun _ => 1, fun _ => 1, fun _ => one_pos, fun _ => one_pos, ⟨0, fun _ _ => by simp⟩, ?_⟩
  rintro ⟨κ, hκ, hc⟩
  have h1 : κ ≤ Real.log (1 / 1) := hc ()
  rw [div_one, Real.log_one] at h1
  have := Real.log_nonneg hμ
  linarith

/-- **O1 without bounded spread**: ratios `e^{−n}/(2μ)` satisfy O1 with `μ' = 2μ`, and their rays are unboundedly far
apart. -/
theorem o1_without_spread {μ : ℝ} (hμ : 0 < μ) :
    ∃ p₀ p₁ : ℕ → ℝ, (∀ ω, 0 < p₀ ω) ∧ (∀ ω, 0 < p₁ ω) ∧
      YMOneBox (fun ω => Real.log (p₀ ω / p₁ ω)) μ ∧ ¬ BoundedSpread p₀ p₁ := by
  have h2 : 0 < 2 * μ := by positivity
  have hp1 : ∀ n : ℕ, 0 < Real.exp (-(n : ℝ)) / (2 * μ) := fun n => div_pos (Real.exp_pos _) h2
  refine ⟨fun _ => 1, fun n => Real.exp (-(n : ℝ)) / (2 * μ), fun _ => one_pos, hp1, ?_, ?_⟩
  · refine (ymOneBox_iff_ratio (fun _ => one_pos) hp1 hμ).2 ⟨2 * μ, by linarith, fun n => ?_⟩
    show 2 * μ * (Real.exp (-(n : ℝ)) / (2 * μ)) ≤ 1
    rw [mul_div_cancel₀ _ h2.ne']
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (Nat.cast_nonneg n))
  · rintro ⟨D, hD⟩
    obtain ⟨n, hn⟩ := exists_nat_gt D
    have h := hD n 0
    beta_reduce at h
    have e : ∀ m : ℕ, Real.log (Real.exp (-(m : ℝ)) / (2 * μ) / 1) = -(m : ℝ) - Real.log (2 * μ) := by
      intro m
      rw [div_one, Real.log_div (Real.exp_pos _).ne' h2.ne', Real.log_exp]
    rw [e, e, show -(n : ℝ) - Real.log (2 * μ) - (-((0 : ℕ) : ℝ) - Real.log (2 * μ)) = -(n : ℝ) by push_cast; ring,
      abs_neg, Nat.abs_cast] at h
    linarith

end ProofPhase.Unified.GRHToO1
