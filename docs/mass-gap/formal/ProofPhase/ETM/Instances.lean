/-
The Existence Turing Machine round: the systems already in Lean as running systems (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/ETM.md`, section 4.
-/

import ProofPhase.ETM.Machine
import ProofPhase.Unified.ProofSize
import ProofPhase.Unified.BlowupSUN
import ProofPhase.Mixing.Chain
import ProofPhase.General.SUNTwistWilson

/-!
# The instances as objects, each with its map into the universal object

Every object below has its unique morphism `trace` into `univ δ` (`RunSys.trace`, `RunSys.trace_unique`); this file
builds the objects and records what each one's ledger says.

* **Chains** (`ofChain`, `ofChainProd`): a factor stream and a mass stream paying it, on the states `ℕ`; the trace of
  `0` is the ledger itself (`ofChain_ledger`). `ofChainProd` carries the running product of the factors.
* **Markov / Dobrushin** (`markov`): states are pairs of probability vectors, the step pushes both through a Markov
  kernel `K`, the factor is a contraction coefficient `η` of `K`, the mass is their total-variation distance; the ledger
  law is `tv_pushv_le` (floor `0`). A Doeblin minorisation puts it in the contraction class (`markov_doeblin`), and the
  ETM bound is a mixing time (`markov_mixing`). Proved outright.
* **Lattice Yang-Mills, every SU(N)** (`ymBoxes`): boxes in series, each with the electric encoder factor
  `elec(Z_tw,k / Z)` of the SU(N) Wilson chain, in `(0, 1)` for `β ≠ 0`, `k ≠ 0` (`boxFactor_mem`, from
  `sunTwistRatio_mem` and `elec_mem`), mass the running product: in the contraction class (`ymBoxes_contracting`).
  Proved outright, at each finite lattice. The **influence** chain (`ymInfluence`) needs the step law
  `M (i+1) ≤ e^δ f M i` as an explicit argument: with `δ = log μ` that is the open one-box statement (O1, with the
  annealed product structure III.5.7).
* **GRH: the Toeplitz / Szego chain** (`szegoChain`, `szegoCoeffs`): the factor is the Szego factor `1 − |k|²` of each
  scale's reflection coefficient, the mass the running product (the prediction-error ratio, classical). Every chain of
  encoders is an object (positivity gives the factor in `[0, 1]`). Conversely, any running system realising a Szego
  factor stream forces every `|k| ≤ 1` (`sign_of_run`): being an object is exactly the sign. Whether Weil's scale steps
  are encoders is the open sign (beyond Dirichlet).
* **Proof systems, the size reading** (`proofRun`): restriction steps, factor `1 − θ`, mass the number of costly lines,
  run stopped after `b` steps; a costly line left at the end forces `1 ≤ (1 − θ)^b |Q 0|` (`proofRun_size`), pulled back
  from the universal ledger. A `CrossingCost` witness is the open input for strong systems.
* **Ricci flow, homothetic shrinker** (`shrinker`): at the dyadic times `t_k = (1 − 2^{−k})/(2λ)` the metric scale is
  `2^{−k}` (`shrink_dyadic`): factor `1/2`, in the contraction class. The **curvature** `λ 2^k` does not fit with floor
  below `log 2` (`growth_needs_floor`, `curvature_needs_floor`); it is an object only with floor `log 2` and cost `0`
  (`curvature`): the blowup is a run whose floor exceeds its cost.

No axioms beyond the standard ones.
-/

open Finset

noncomputable section

namespace ProofPhase.ETM

universe u

namespace RunSys

variable {δ : ℝ}

/-! ## Chains -/

/-- **A chain**: a factor stream and a mass stream that pays it, on the states `ℕ`. -/
def ofChain (f m : ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) (hm : ∀ i, 0 ≤ m i)
    (hp : ∀ i, m (i + 1) ≤ Real.exp δ * f i * m i) : RunSys.{0} δ where
  X := ℕ
  step := Nat.succ
  fac := f
  mass := m
  fac_nonneg := hf0
  fac_le_one := hf1
  mass_nonneg := hm
  pays := hp

theorem succ_iterate_zero (n : ℕ) : Nat.succ^[n] 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]

/-- The trace of `0` in a chain is the chain's own ledger. -/
theorem ofChain_ledger (f m : ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) (hm : ∀ i, 0 ≤ m i)
    (hp : ∀ i, m (i + 1) ≤ Real.exp δ * f i * m i) :
    (ofChain f m hf0 hf1 hm hp).ledger (0 : ℕ) = ⟨f, m, hf0, hf1, hm, hp⟩ := by
  refine Ledger.ext (funext fun n => ?_) (funext fun n => ?_)
  · show f (Nat.succ^[n] 0) = f n
    rw [succ_iterate_zero]
  · show m (Nat.succ^[n] 0) = m n
    rw [succ_iterate_zero]

/-- **The product chain**: mass the running product of the factors, floor `0`. -/
def ofChainProd (f : ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) : RunSys.{0} 0 :=
  ofChain f (fun i => ∏ j ∈ range i, f j) hf0 hf1 (fun i => prod_nonneg fun j _ => hf0 j) fun i => by
    rw [Real.exp_zero, one_mul, prod_range_succ, mul_comm]

/-- A constant factor `θ < 1` puts the product chain in the contraction class. -/
theorem ofChainProd_contracting {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1) :
    (ofChainProd (fun _ => θ) (fun _ => hθ0) (fun _ => hθ.le)).Contracting θ :=
  ⟨fun _ => le_rfl, by rw [Real.exp_zero, one_mul]; exact hθ⟩

/-! ## Markov chains (Dobrushin, Doeblin) -/

section Markov

open ProofPhase.Mixing

variable {Y : Type u} [Fintype Y] [DecidableEq Y]

/-- Pairs of probability vectors on `Y`. -/
def ProbPair (Y : Type u) [Fintype Y] : Type u :=
  {p : (Y → ℝ) × (Y → ℝ) // (∀ y, 0 ≤ p.1 y) ∧ (∀ y, 0 ≤ p.2 y) ∧ ∑ y, p.1 y = 1 ∧ ∑ y, p.2 y = 1}

omit [DecidableEq Y] in
theorem pushv_prob {a : Y → ℝ} (ha : ∀ y, 0 ≤ a y) (ha1 : ∑ y, a y = 1) {K : Y → Y → ℝ} (hK : IsStoch K) :
    (∀ y, 0 ≤ pushv a K y) ∧ ∑ y, pushv a K y = 1 := by
  refine ⟨fun y => sum_nonneg fun x _ => mul_nonneg (ha x) (hK.nonneg x y), ?_⟩
  simp only [pushv]
  rw [sum_comm]
  simp_rw [← mul_sum, hK.sum_one, mul_one, ha1]

/-- **A Markov chain as a running system**: the step pushes both vectors through `K`, the factor is a contraction
coefficient `η` of `K`, the mass the total-variation distance (floor `0`). -/
def markov (K : Y → Y → ℝ) (hK : IsStoch K) (η : ℝ) (hη : Contracts K η) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    RunSys.{u} 0 where
  X := ProbPair Y
  step p := ⟨(pushv p.1.1 K, pushv p.1.2 K), (pushv_prob p.2.1 (p.2.2.2).1 hK).1, (pushv_prob p.2.2.1 (p.2.2.2).2 hK).1,
    (pushv_prob p.2.1 (p.2.2.2).1 hK).2, (pushv_prob p.2.2.1 (p.2.2.2).2 hK).2⟩
  fac _ := η
  mass p := tv p.1.1 p.1.2
  fac_nonneg _ := hη0
  fac_le_one _ := hη1
  mass_nonneg p := tv_nonneg _ _
  pays p := by
    rw [Real.exp_zero, one_mul]
    exact tv_pushv_le p.2.1 p.2.2.1 (p.2.2.2).1 (p.2.2.2).2 hη

/-- **Doeblin puts the chain in the contraction class**: a minorisation `K x y ≥ ε ν y`, `0 < ε`, gives the factor
`1 − ε < 1`. -/
theorem markov_doeblin (K : Y → Y → ℝ) (hK : IsStoch K) {ν : Y → ℝ} (hν : ∑ y, ν y = 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hε : ∀ x y, ε * ν y ≤ K x y) :
    (markov K hK (1 - ε) (contracts_of_doeblin hK hν hε) (by linarith) (by linarith)).Contracting (1 - ε) :=
  ⟨fun _ => le_rfl, by rw [Real.exp_zero, one_mul]; linarith⟩

/-- **The ETM bound is a mixing time**: under Doeblin, two probability vectors pushed through `n ≥ balanceBound 1 τ q`
steps are within `τ` in total variation (`q ≥ 1 − ε` rational, `q < 1`). -/
theorem markov_mixing (K : Y → Y → ℝ) (hK : IsStoch K) {ν : Y → ℝ} (hν : ∑ y, ν y = 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hε : ∀ x y, ε * ν y ≤ K x y) (p : ProbPair Y) {τ q : ℚ} (hq : 1 - ε ≤ q) (hq1 : q < 1)
    (hτ : 0 < τ) :
    ∀ n ≥ balanceBound 1 τ q,
      (markov K hK (1 - ε) (contracts_of_doeblin hK hν hε) (by linarith) (by linarith)).Balanced τ p n := by
  refine RunSys.reaches_of_contracting _ (markov_doeblin K hK hν hε0 hε1 hε) p
    (by rw [Real.exp_zero, one_mul]; exact hq) hq1 ?_ hτ
  rw [Rat.cast_one]
  exact tv_le_one p.2.1 p.2.2.1 (p.2.2.2).1 (p.2.2.2).2

end Markov

/-! ## Lattice Yang-Mills, every SU(N) -/

section YangMills

open ProofPhase.General ProofPhase.Unified

variable (N : ℕ) [NeZero N] [Fact (1 < N)] (L : ℕ) [NeZero L]

/-- **The SU(N) box encoder factor**: the electric profile of the twist ratio `c_k = Z_tw,k / Z`. -/
def boxFactor (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T] (k : ZMod N) : ℝ :=
  elec (sunZtw N L β P c T k / sunZ N L β P T)

/-- **The SU(N) box factor lies strictly between `0` and `1`** (`β ≠ 0`, `k ≠ 0`, `T` even): a finite, positive
cost at every box. -/
theorem boxFactor_mem {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ} [NeZero T]
    (hT : Even T) {k : ZMod N} (hk : k ≠ 0) : 0 < boxFactor N L β P c T k ∧ boxFactor N L β P c T k < 1 :=
  elec_mem (sunTwistRatio_mem N L hβ P c hT hk).1 (sunTwistRatio_mem N L hβ P c hT hk).2

/-- **SU(N) boxes in series**: every box carries the box factor, mass the running product (the electric weight
through the boxes in series). Proved outright, at each finite lattice. -/
def ymBoxes {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ} [NeZero T]
    (hT : Even T) {k : ZMod N} (hk : k ≠ 0) : RunSys.{0} 0 :=
  ofChainProd (fun _ => boxFactor N L β P c T k) (fun _ => (boxFactor_mem N L hβ P c hT hk).1.le)
    (fun _ => (boxFactor_mem N L hβ P c hT hk).2.le)

/-- **The SU(N) box chain is in the contraction class**, with `θ` the box factor. -/
theorem ymBoxes_contracting {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ}
    [NeZero T] (hT : Even T) {k : ZMod N} (hk : k ≠ 0) :
    (ymBoxes N L hβ P c hT hk).Contracting (boxFactor N L β P c T k) :=
  ofChainProd_contracting (boxFactor_mem N L hβ P c hT hk).1.le (boxFactor_mem N L hβ P c hT hk).2

/-- **The influence chain** (needs the open step law): an influence `M` handed from box to box that pays the box
factor up to the floor `δ`. With `δ = log μ` the argument `hO1` is the one-box statement (O1, with III.5.7); it is a
hypothesis here, never proved. -/
def ymInfluence {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ} [NeZero T]
    (hT : Even T) {k : ZMod N} (hk : k ≠ 0) (M : ℕ → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hO1 : ∀ i, M (i + 1) ≤ Real.exp δ * boxFactor N L β P c T k * M i) : RunSys.{0} δ :=
  ofChain (fun _ => boxFactor N L β P c T k) M (fun _ => (boxFactor_mem N L hβ P c hT hk).1.le)
    (fun _ => (boxFactor_mem N L hβ P c hT hk).2.le) hM hO1

end YangMills

/-! ## GRH: the Toeplitz / Szego chain -/

section Szego

open ProofPhase.Unified

/-- **A chain of encoders** (one per scale) with the Szego factor: positivity puts every factor in `[0, 1]`. -/
def szegoChain {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (X : ℕ → Encoder 𝕜 E) : RunSys.{0} 0 :=
  ofChainProd (fun i => szego (X i).refl) (fun i => (szego_mem (X i)).1) (fun i => (szego_mem (X i)).2)

/-- **The Szego (Verblunsky) chain of reflection coefficients in the closed disk**: factor `1 − |k_i|²`, mass the
running product, which is the prediction-error ratio `E_n / E_0` of the Szego recursion (classical). -/
def szegoCoeffs {𝕜 : Type*} [RCLike 𝕜] (k : ℕ → 𝕜) (hk : ∀ i, ‖k i‖ ≤ 1) : RunSys.{0} 0 :=
  ofChainProd (fun i => szego (k i)) (fun i => szego_nonneg (hk i)) (fun _ => szego_le_one _)

/-- **Being an object is exactly the sign**: any running system whose factor stream is a Szego stream forces every
reflection coefficient into the closed disk. -/
theorem sign_of_run {𝕜 : Type*} [RCLike 𝕜] (S : RunSys.{u} δ) (x : S.X) (k : ℕ → 𝕜)
    (h : ∀ i, S.fac (S.step^[i] x) = szego (k i)) (i : ℕ) : ‖k i‖ ≤ 1 := by
  have h0 := S.fac_nonneg (S.step^[i] x)
  rw [h i] at h0
  unfold szego at h0
  nlinarith [norm_nonneg (k i)]

/-- Strictly inside the disk the factor is positive: a finite cost at every scale. -/
theorem szegoCoeffs_pos {𝕜 : Type*} [RCLike 𝕜] (k : ℕ → 𝕜) (hk : ∀ i, ‖k i‖ < 1) (i : ℕ) :
    0 < (szegoCoeffs k fun i => (hk i).le).fac i :=
  (szego_pos_iff (k i)).2 (hk i)

end Szego

/-! ## Proof systems: the size reading -/

section Proofs

/-- **A refutation under restrictions**: factor `1 − θ`, mass the number of costly lines `|Q i|` for `i ≤ b`, then
`0` (the run is stopped after `b` steps). -/
def proofRun {Line : Type*} (Q : ℕ → Finset Line) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {b : ℕ}
    (h : ∀ i < b, ((Q (i + 1)).card : ℝ) ≤ (1 - θ) * (Q i).card) : RunSys.{0} 0 :=
  ofChain (fun _ => 1 - θ) (fun i => if i ≤ b then ((Q i).card : ℝ) else 0) (fun _ => by linarith)
    (fun _ => by linarith) (fun i => by split_ifs <;> positivity) fun i => by
      rw [Real.exp_zero, one_mul]
      by_cases hi : i < b
      · rw [if_pos (show i + 1 ≤ b by omega), if_pos hi.le]
        exact h i hi
      · rw [if_neg (show ¬ i + 1 ≤ b by omega)]
        split_ifs <;> positivity

/-- **The size reading, pulled back from the universal ledger**: a costly line left after `b` steps forces
`1 ≤ (1 − θ)^b |Q 0|`. -/
theorem proofRun_size {Line : Type*} (Q : ℕ → Finset Line) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {b : ℕ}
    (h : ∀ i < b, ((Q (i + 1)).card : ℝ) ≤ (1 - θ) * (Q i).card) (hend : (Q b).Nonempty) :
    1 ≤ (1 - θ) ^ b * (Q 0).card := by
  have hc := (proofRun Q hθ0 hθ1 h).contract (θ := 1 - θ) (fun _ => le_rfl) (0 : ℕ) b
  have e1 : (proofRun Q hθ0 hθ1 h).mass ((proofRun Q hθ0 hθ1 h).step^[b] (0 : ℕ)) = (Q b).card := by
    show (if Nat.succ^[b] 0 ≤ b then ((Q (Nat.succ^[b] 0)).card : ℝ) else 0) = _
    rw [succ_iterate_zero, if_pos le_rfl]
  have e2 : (proofRun Q hθ0 hθ1 h).mass (0 : ℕ) = (Q 0).card := by
    show (if 0 ≤ b then ((Q 0).card : ℝ) else 0) = _
    rw [if_pos (Nat.zero_le b)]
  rw [e1, e2, Real.exp_zero, one_mul] at hc
  have : (1 : ℝ) ≤ (Q b).card := by exact_mod_cast hend.card_pos
  linarith

end Proofs

/-! ## Ricci flow: the homothetic shrinker -/

section Shrinker

open ProofPhase.Unified

/-- The dyadic times `t_k = (1 − 2^{−k}) / (2λ)`, accumulating at the extinction time `1/(2λ)`. -/
def dyadicTime (lam : ℝ) (k : ℕ) : ℝ := (1 - (1 / 2) ^ k) / (2 * lam)

/-- **At the dyadic times the metric scale is `2^{−k}`.** -/
theorem shrink_dyadic {lam : ℝ} (hlam : lam ≠ 0) (k : ℕ) : shrink lam (dyadicTime lam k) = (1 / 2) ^ k := by
  unfold shrink dyadicTime
  field_simp
  ring

/-- **The shrinker as a running system**: dyadic steps, factor `1/2`, mass the metric scale (floor `0`). -/
def shrinker {lam : ℝ} (hlam : lam ≠ 0) : RunSys.{0} 0 :=
  ofChain (fun _ => 1 / 2) (fun k => shrink lam (dyadicTime lam k)) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun k => by rw [shrink_dyadic hlam]; positivity) fun k => by
      rw [shrink_dyadic hlam, shrink_dyadic hlam, Real.exp_zero, one_mul, pow_succ, mul_comm]

/-- **The shrinker is in the contraction class**: it reaches every `ε`-neighbourhood of extinction in finitely many
dyadic steps. -/
theorem shrinker_contracting {lam : ℝ} (hlam : lam ≠ 0) : (shrinker hlam).Contracting (1 / 2) :=
  ⟨fun _ => le_rfl, by rw [Real.exp_zero, one_mul]; norm_num⟩

/-- **At the dyadic times the curvature is `λ 2^k`.** -/
theorem einstein_dyadic {lam : ℝ} (hlam : lam ≠ 0) (k : ℕ) : einsteinAt lam (dyadicTime lam k) = lam * 2 ^ k := by
  unfold einsteinAt
  rw [shrink_dyadic hlam, one_div, inv_pow, div_inv_eq_mul]

/-- **A growing mass needs a floor**: a run whose mass grows by `r > 0` per step from a positive start has floor at
least `log r`. -/
theorem growth_needs_floor (S : RunSys.{u} δ) (x : S.X) {r : ℝ} (hr : 0 < r) (hx : 0 < S.mass x)
    (h : S.mass (S.step x) = r * S.mass x) : Real.log r ≤ δ := by
  have h1 := S.pays x
  rw [h] at h1
  have h2 : Real.exp δ * S.fac x * S.mass x ≤ Real.exp δ * S.mass x :=
    mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (Real.exp_pos δ).le (S.fac_le_one x)) hx.le
  have h3 : r ≤ Real.exp δ := le_of_mul_le_mul_right (h1.trans h2) hx
  exact (Real.log_le_iff_le_exp hr).2 h3

/-- **The curvature does not fit below the floor `log 2`**: no running system with floor `δ < log 2` carries the
curvature stream `λ 2^k` (`λ > 0`). -/
theorem curvature_needs_floor (S : RunSys.{u} δ) (x : S.X) {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ k, S.mass (S.step^[k] x) = einsteinAt lam (dyadicTime lam k)) : Real.log 2 ≤ δ := by
  have h0 := h 0
  have h1 := h 1
  rw [einstein_dyadic hlam.ne'] at h0 h1
  simp only [Function.iterate_zero, id_eq, pow_zero, mul_one, Function.iterate_one, pow_one] at h0 h1
  refine growth_needs_floor S x two_pos (by rw [h0]; exact hlam) ?_
  rw [h1, h0]; ring

/-- **The curvature as a run with floor `log 2` and cost `0`**: the blowup is a run whose floor exceeds its cost. -/
def curvature {lam : ℝ} (hlam : 0 < lam) : RunSys.{0} (Real.log 2) :=
  ofChain (fun _ => 1) (fun k => einsteinAt lam (dyadicTime lam k)) (fun _ => zero_le_one) (fun _ => le_rfl)
    (fun k => by rw [einstein_dyadic hlam.ne']; positivity) fun k => by
      rw [einstein_dyadic hlam.ne', einstein_dyadic hlam.ne', Real.exp_log two_pos, pow_succ]
      nlinarith [pow_pos (two_pos (α := ℝ)) k]

end Shrinker

end RunSys

end ProofPhase.ETM
