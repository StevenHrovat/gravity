/-
The unified lossy-step theorem: the Yang-Mills instance (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/UNIFIED.md`, section 3.1.
-/

import ProofPhase.Unified.Ledger
import ProofPhase.Mixing.Chain
import ProofPhase.Mixing.TimeGap
import ProofPhase.Crossover.CompositeHTF
import ProofPhase.Crossover.Containment
import ProofPhase.Crossover.HandOver

/-!
# Yang-Mills as a lossy chain: boxes are the steps, the electric free energy is the cost

The steps are boxes. Each box hands the influence on with a weight `e^{-F_e}`, `F_e` its electric free energy (a function
of the twist deficit, `Crossover/Equidist.lean`). Three readings, one ledger (`Unified/Ledger.lean`), three floors.

**1. Chain, transfer kernels (floor `0`).** `ym_chain`: kernels `K_i` (one per box, each with its own outside, so
nothing is assumed about the outside) contracting by `e^{-c i}` compose to a kernel contracting by `e^{-Σ c}`. This is
`Mixing/Chain.lean`'s `contracts_kcomp` fed into the certificate ledger `carry`; `ym_chain_rate` is the uniform case.

**2. Chain, electric free energy (floor `2C`, the excess act).** `ym_flux`: `F((k+1) L)` accrues `F(L)` per box less
`2C` (`Crossover/CompositeHTF.lean`'s `flux_superadd`); `ym_flux_bound`: `F((n+1) L) ≥ (n+1)(F(L) − 2C)`, re-derived
through the additive ledger `accrue`.

**3. Tubes, the paper's O1 (floor `log μ`, the path entropy).** `pathSum w ω n` is the sum over paths through `n`
boxes (one of `μ = |D|` continuations at each box) of the product of the box weights; `pathSum_eq` writes it as a
product of sums. If every box weight is at most `e^{-F_e(ω)}` (`ω` the box's outside), the path sum pays the cost `F_e`
up to the floor `log μ` (`pathSum_pays`).
* **`YMOneBox Fe μ`** (the named hypothesis, **open**, O1 = III.5.6): `CostAboveFloor Fe (log μ)`, the electric cost of a
  box exceeds the path entropy, uniformly over every outside.
* `ymOneBox_iff_tube`: O1 is the tube threshold `μ e^{−κ} < 1` (`Containment.lean`, `tube_threshold`).
* **`ym_instance`**: `YMOneBox` gives a rate `κ − log μ > 0`: `pathSum n ≤ e^{−n (κ − log μ)}`, summable.
* **`ym_gap`** (the plug-in): if the transfer correlations of an observable (spectral measure `ρ` on `[0, 1]`,
  `Mixing/TimeGap.lean`) are dominated by the path sum (the path expansion, a stated link), there is no spectral mass
  above `e^{−(κ − log μ)}`: a gap of at least `1 − e^{−(κ − log μ)}` per box (`gap_of_geometric`).
* **`handover_below_floor`** (why it is open): the proved per-box hand-over `log(1 + √2) = 0.881`
  (`Crossover/HandOver.lean`) is below `log μ` as soon as `μ ≥ 3`; `μ_4 = 6.77` (classical).

**What is not here.** The identification of the path sum with the SU(2) blocked laws (`V4/Gap.lean`, `BlockGapBddW`)
and the annealed-to-quenched step (III.5.7, built into `pathSum` as the product structure) are not proved; the relation of
the chain floor `2C` to the tube floor `log μ` is III.5.8 (open). No axioms beyond the standard ones.
-/

open Finset MeasureTheory

noncomputable section

namespace ProofPhase.Unified

open ProofPhase.Mixing ProofPhase.Crossover

/-! ### 1. Chain, transfer kernels -/

section Kernels

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The chain composes by contraction.** Boxes with transfer kernels contracting by `e^{-c i}` compose to a kernel
contracting by `e^{-Σ c}`: the influence across `n` boxes is at most `e^{-Σ c}`. -/
theorem ym_chain {Ks : ℕ → X → X → ℝ} (hs : ∀ i, IsStoch (Ks i)) {c : ℕ → ℝ}
    (hc : ∀ i, Contracts (Ks i) (Real.exp (-c i))) (n : ℕ) :
    Contracts (kchain Ks n) (Real.exp (-∑ i ∈ range n, c i)) := by
  have hcar : Carries (fun i e => Contracts (kchain Ks i) e) (fun i => Real.exp (0 - c i)) n := by
    intro i _ e he
    have h := contracts_kcomp (isStoch_kchain hs i) he (hc i)
    show Contracts (kcomp (kchain Ks i) (Ks i)) (Real.exp (0 - c i) * e)
    rwa [zero_sub, mul_comm]
  have h := carry hcar (e := 1) (by exact (isStoch_idK (X := X)).contracts_one)
  rw [prod_exp_cost, mul_one] at h
  simpa using h

/-- **Uniform boxes**: every box contracting by `e^{-κ}` gives `e^{-n κ}` across `n` boxes. -/
theorem ym_chain_rate {Ks : ℕ → X → X → ℝ} (hs : ∀ i, IsStoch (Ks i)) {κ : ℝ}
    (hc : ∀ i, Contracts (Ks i) (Real.exp (-κ))) (n : ℕ) : Contracts (kchain Ks n) (Real.exp (-(n * κ))) := by
  have h := ym_chain hs (c := fun _ => κ) hc n
  rwa [sum_const, card_range, nsmul_eq_mul] at h

end Kernels

/-! ### 2. Chain, electric free energy: the floor is the excess act -/

/-- **The electric free energy accrues per box, less the excess act**: `G k = F((k+1) L)` accrues `F(L)` with floor
`2C`. -/
theorem ym_flux {Z₀ Z₁ : ℕ → ℝ} {l : ℝ} (hl : 0 < l) (h1 : ∀ n, 0 < Z₁ n) (h0 : ∀ n, l ^ n ≤ Z₀ n)
    (hsub : ∀ a b, Z₁ (a + b) ≤ Z₁ a * Z₁ b) (L : ℕ) {C : ℝ}
    (hC : ∀ k, Real.log (Z₀ (k * L) / l ^ (k * L)) ≤ C) (n : ℕ) :
    Accrues (fun k => Real.log (Z₀ ((k + 1) * L)) - Real.log (Z₁ ((k + 1) * L)))
      (fun _ => Real.log (Z₀ L) - Real.log (Z₁ L)) (2 * C) n := by
  intro k _
  have hs := flux_superadd hl h1 h0 hsub ((k + 1) * L) L
  have hk := hC (k + 1)
  have hL : Real.log (Z₀ L / l ^ L) ≤ C := by simpa using hC 1
  rw [show (k + 1) * L + L = (k + 1 + 1) * L by ring] at hs
  simp only
  linarith

/-- **`F((n+1) L) ≥ (n+1)(F(L) − 2C)`**, from the additive ledger (`CompositeHTF.flux_superadd_iter` re-derived). -/
theorem ym_flux_bound {Z₀ Z₁ : ℕ → ℝ} {l : ℝ} (hl : 0 < l) (h1 : ∀ n, 0 < Z₁ n) (h0 : ∀ n, l ^ n ≤ Z₀ n)
    (hsub : ∀ a b, Z₁ (a + b) ≤ Z₁ a * Z₁ b) (L : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k, Real.log (Z₀ (k * L) / l ^ (k * L)) ≤ C) (n : ℕ) :
    (n + 1) * ((Real.log (Z₀ L) - Real.log (Z₁ L)) - 2 * C) ≤
      Real.log (Z₀ ((n + 1) * L)) - Real.log (Z₁ ((n + 1) * L)) := by
  have h := accrue (ym_flux hl h1 h0 hsub L hC n)
  simp only [zero_add, one_mul, sum_const, card_range, nsmul_eq_mul] at h
  nlinarith

/-! ### 3. Tubes: the floor is the path entropy (O1) -/

section Tubes

variable {Ω D : Type*} [Fintype D]

/-- **The path sum over `n` boxes**: a path picks one continuation `d : D` at each box; box `i`, in the outside `ω i`,
passes the weight `w (ω i) d`; a path weighs the product of its box weights (the product structure along paths). -/
def pathSum (w : Ω → D → ℝ) (ω : ℕ → Ω) (n : ℕ) : ℝ := ∑ p : Fin n → D, ∏ i : Fin n, w (ω i) (p i)

/-- The path sum is a product of per-box sums. -/
theorem pathSum_eq (w : Ω → D → ℝ) (ω : ℕ → Ω) (n : ℕ) :
    pathSum w ω n = ∏ i ∈ range n, ∑ d, w (ω i) d := by
  unfold pathSum
  rw [← Fintype.prod_sum (fun (i : Fin n) (d : D) => w (ω i) d)]
  exact Fin.prod_univ_eq_prod_range (fun i => ∑ d, w (ω i) d) n

theorem pathSum_zero (w : Ω → D → ℝ) (ω : ℕ → Ω) : pathSum w ω 0 = 1 := by
  rw [pathSum_eq, range_zero, prod_empty]

theorem pathSum_nonneg {w : Ω → D → ℝ} (hw0 : ∀ ω d, 0 ≤ w ω d) (ω : ℕ → Ω) (n : ℕ) : 0 ≤ pathSum w ω n := by
  rw [pathSum_eq]
  exact prod_nonneg fun i _ => sum_nonneg fun d _ => hw0 _ _

/-- **The path sum is a lossy chain**: cost `F_e` per box, floor `log μ` (`μ = |D|` continuations, the path entropy). -/
theorem pathSum_pays [Nonempty D] {w : Ω → D → ℝ} {Fe : Ω → ℝ} (hw0 : ∀ ω d, 0 ≤ w ω d)
    (hw : ∀ ω d, w ω d ≤ Real.exp (-Fe ω)) (ω : ℕ → Ω) (n : ℕ) :
    Pays (pathSum w ω) (fun i => Fe (ω i)) (Real.log (Fintype.card D)) n := by
  intro i _
  have hD : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hstep : ∑ d, w (ω i) d ≤ Real.exp (Real.log (Fintype.card D) - Fe (ω i)) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hD]
    calc ∑ d, w (ω i) d ≤ ∑ _d : D, Real.exp (-Fe (ω i)) := sum_le_sum fun d _ => hw _ d
      _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
  rw [pathSum_eq, prod_range_succ, ← pathSum_eq, mul_comm]
  exact mul_le_mul_of_nonneg_right hstep (pathSum_nonneg hw0 ω i)

/-- **O1, the one-box statement (Yang-Mills's named hypothesis; open).** The electric cost `Fe ω` of one box of fixed
physical size exceeds the path entropy `log μ`, uniformly over every outside `ω`. -/
def YMOneBox (Fe : Ω → ℝ) (μ : ℝ) : Prop := CostAboveFloor Fe (Real.log μ)

/-- O1 is the tube threshold of `Crossover/Containment.lean`: a uniform cost `κ` with `μ e^{−κ} < 1`, i.e. the path
sum's per-box ratio below one. -/
theorem ymOneBox_iff_tube {Fe : Ω → ℝ} {μ : ℝ} (hμ : 0 < μ) :
    YMOneBox Fe μ ↔ ∃ κ : ℝ, μ * Real.exp (-κ) < 1 ∧ ∀ ω, κ ≤ Fe ω := by
  unfold YMOneBox CostAboveFloor
  simp_rw [tube_threshold hμ]

/-- **The Yang-Mills instance.** Under O1 the path sum decays at the rate `κ − log μ > 0` per box and is summable:
influence runs in tubes. The only non-proved input is `YMOneBox`. -/
theorem ym_instance [Nonempty D] {w : Ω → D → ℝ} {Fe : Ω → ℝ} (hw0 : ∀ ω d, 0 ≤ w ω d)
    (hw : ∀ ω d, w ω d ≤ Real.exp (-Fe ω)) (h : YMOneBox Fe (Fintype.card D)) (ω : ℕ → Ω) :
    ∃ κ : ℝ, Real.log (Fintype.card D) < κ ∧
      (∀ n, pathSum w ω n ≤ Real.exp (-(n * (κ - Real.log (Fintype.card D))))) ∧ Summable (pathSum w ω) := by
  obtain ⟨κ, hκ, hdec, hsum⟩ :=
    rate_of_costAboveFloor h ω (pathSum_pays hw0 hw ω) (pathSum_nonneg hw0 ω)
  exact ⟨κ, hκ, fun n => by simpa [pathSum_zero] using hdec n, hsum⟩

/-- **The plug-in: from O1 to a spectral gap.** If the time correlations of an observable (spectral measure `ρ` on
`[0, 1]`) are dominated by the path sum, O1 leaves no spectral mass above `e^{−(κ − log μ)}`. -/
theorem ym_gap [Nonempty D] {w : Ω → D → ℝ} {Fe : Ω → ℝ} (hw0 : ∀ ω d, 0 ≤ w ω d)
    (hw : ∀ ω d, w ω d ≤ Real.exp (-Fe ω)) (h : YMOneBox Fe (Fintype.card D)) (ω : ℕ → Ω)
    {ρ : Measure ℝ} [IsFiniteMeasure ρ] (h0 : ∀ᵐ l ∂ρ, 0 ≤ l) (h1 : ∀ᵐ l ∂ρ, l ≤ 1) {K : ℝ} (hK : 0 ≤ K)
    (hdom : ∀ k : ℕ, acorr ρ k ≤ K * pathSum w ω k) :
    ∃ κ : ℝ, Real.log (Fintype.card D) < κ ∧ ρ (Set.Ioi (Real.exp (-(κ - Real.log (Fintype.card D))))) = 0 := by
  obtain ⟨κ, hκ, hdec, -⟩ := ym_instance hw0 hw h ω
  refine ⟨κ, hκ, gap_of_geometric h0 h1 (Real.exp_pos _) (K := K) fun k => ?_⟩
  refine (hdom k).trans (mul_le_mul_of_nonneg_left ((hdec k).trans (le_of_eq ?_)) hK)
  rw [← Real.exp_nat_mul]
  ring_nf

end Tubes

/-- **Why O1 is open: the proved hand-over is below the floor.** `log(1 + √2) < log μ` for `μ ≥ 3`; the per-box bound
`max(F_tw, F_e) ≥ log(1 + √2)` (`log_one_add_sqrt_two_le_max`) cannot meet `YMOneBox` against the path entropy of
`d ≥ 3` (`μ_4 = 6.77`, classical). -/
theorem handover_below_floor {μ : ℝ} (hμ : 3 ≤ μ) : Real.log (1 + √2) < Real.log μ := by
  have hs : √2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  exact Real.log_lt_log (by positivity) (by linarith)

end ProofPhase.Unified
