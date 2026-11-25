/-
Proof phase, cycle 7, workstream 1 (c7a-fluxvac): does the flux act's accumulation give the vacuum doubling with a bounded
loss? Branch decomposition of the vacuum act, the flux window, the product counterexample, the sector-resolved gluing
deficit, and the flux-pair observable on the SU(2) boxes (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c7a-fluxvac/NOTE.md`.
-/

import ProofPhase.Flip.Floor

/-!
# Vacuum doubling from flux accumulation: what follows, and what has to be added

Notation: `z n = z₀(2ⁿL₀)` the vacuum act, `ze n = z_e(2ⁿL₀)` the flux act, `Doubles z c :⇔ ∀ n, 2 z n − c ≤ z (n+1)`
(the repaired super-additivity of c6a/c6c).

1. **The flux window** (`doubling_of_window`, `doubling_of_pair_window`). If the lowest centre-even state is a flux pair at
   both ends of a doubling (lower sector transfer at the big box, upper at the small box), the flux doubling gives the vacuum
   doubling with loss `a + 2b + 2c_e`. Exact algebra; it needs both directions of the sector transfer.
2. **Envelopes and branches** (`min_doubles`, `envelope_floor`, `flux_branch_doubles`, `branches_floor`). The vacuum law is
   not needed for `z₀` itself: a lower envelope `y ≤ z₀` that doubles suffices. With the lower sector transfer in branch
   form, `z₀ ≥ min(2 z_e − a, μ)`, the envelope doubles as soon as the flux act and the **non-flux branch `μ`** both double;
   the flux branch doubles with defect `2c_e − a` (negative in the data). So: flux accumulation + lower sector transfer +
   **doubling of the non-flux branch** ⇒ the gap.
3. **Unit tests** (`product_test`, `photon_flux_test`). The product SU(2) × U(1) satisfies flux doubling with gain, the
   upper and the lower sector transfer (with `μ` = the photon), and violates the vacuum law; the only premise of
   `branches_floor` it violates is the doubling of `μ`. The photon's own flux act is constant: its flux branch has no positive
   start.
4. **The sector-resolved gluing deficit** (`vac_deficit_eq`, `vac_deficit_le`). With `ρ = Z_{e=0}/Z` (the `e = 0` fraction,
   the average of the temporal twist ratios): `1 + δ₀ = (1 + δ) ρ(L)²/ρ(2L)`; for `ρ ≤ 1`, `δ₀ ≤ (1 + δ)/ρ(2L) − 1`. Flux
   saturation (`ρ → 1`) makes the vacuum-sector deficit equal the full one; the neutral content stays.
5. **The flux-pair observable on the SU(2) boxes** (`pairObs`, `su2_E0_le_pairRate`). `Φ²` (the square of Route B's summed
   Wilson line) is a centre-even bounded measurable slice observable, so the box gap is at most the decay rate of every
   non-vanishing connected limit of the flux-pair correlation: **the upper sector transfer, `E₀ ≤ E_pp`, is a theorem**. The
   lower one is not (the product).
6. **The SU(2) gap from the branches** (`su2_gap_of_envelope`, `su2_gap_of_branches`).
7. **The escape form** (`escape_floor`, `escape_of_flux`, `product_escape_test`, `su2_gap_of_flux_escape`): if every doubling
   keeps the vacuum law up to `c` or is paid by `K` flux acts, `z₀(2L) ≥ min(2 z₀(L) − c, K z_e(2L))`, flux accumulation
   supplies the escape condition and the gap follows. The open premise is the transplant/spanning dichotomy.

**Claim discipline.** Sections 1–4: real analysis (exact, elementary). Section 5: substantive but group-blind (centre
symmetry of `Φ` plus c5e's `E0_le_rate`). Section 6: the SU(2) statements are substantive only through c5e (`E0` is the box
gap); their premises (lower sector transfer, non-flux doubling) are open, and the flux doubling is measured, not proved.
-/

open Filter Topology Finset

noncomputable section

namespace ProofPhase.FluxVac

/-! ## 1. Doubling laws and the flux window -/

/-- **The doubling law with defect `c`** (repaired super-additivity along dyadic boxes). -/
def Doubles (z : ℕ → ℝ) (c : ℝ) : Prop := ∀ n, 2 * z n - c ≤ z (n + 1)

theorem Doubles.mono {z : ℕ → ℝ} {c c' : ℝ} (h : Doubles z c) (hc : c ≤ c') : Doubles z c' :=
  fun n => by linarith [h n]

/-- **The flux window.** Lower sector transfer at the big box (`z₀ ≥ 2 z_e − a`), upper sector transfer at the small box
(`z₀ ≤ 2 z_e + b`) and one flux doubling (`z_e(2L) ≥ 2 z_e(L) − c_e`) give one vacuum doubling with loss `a + 2b + 2c_e`. -/
theorem doubling_of_window {z ze : ℕ → ℝ} {a b ce : ℝ} (n : ℕ) (hlo : 2 * ze (n + 1) - a ≤ z (n + 1))
    (hup : z n ≤ 2 * ze n + b) (hflux : 2 * ze n - ce ≤ ze (n + 1)) :
    2 * z n - (a + 2 * b + 2 * ce) ≤ z (n + 1) := by
  linarith

/-- **The flux window in pair form.** With the flux-pair act `z_pp` (decay rate of the pair operator times `L`): the upper
side `z₀ ≤ z_pp` is a theorem on the SU(2) boxes (`su2_z0_le_pairAct`); with the lower side `z₀ ≥ z_pp − a` at the big box
and a pair doubling with defect `c_p`, one vacuum doubling with loss `a + c_p`. -/
theorem doubling_of_pair_window {z zpp : ℕ → ℝ} {a cp : ℝ} (n : ℕ) (hlo : zpp (n + 1) - a ≤ z (n + 1))
    (hup : z n ≤ zpp n) (hpair : 2 * zpp n - cp ≤ zpp (n + 1)) : 2 * z n - (a + cp) ≤ z (n + 1) := by
  linarith

/-! ## 2. Envelopes and branches -/

/-- **The minimum of two doubling sequences doubles**, with the larger defect. -/
theorem min_doubles {x y : ℕ → ℝ} {cx cy : ℝ} (hx : Doubles x cx) (hy : Doubles y cy) :
    Doubles (fun n => min (x n) (y n)) (max cx cy) := by
  intro n
  simp only
  refine le_min ?_ ?_
  · linarith [hx n, min_le_left (x n) (y n), le_max_left cx cy]
  · linarith [hy n, min_le_right (x n) (y n), le_max_right cx cy]

/-- **A doubling lower envelope is enough**: `y ≤ z` and `Doubles y c` give `z n − c ≥ 2ⁿ (y 0 − c)`. -/
theorem envelope_floor {z y : ℕ → ℝ} {c : ℝ} (hyz : ∀ n, y n ≤ z n) (hy : Doubles y c) (n : ℕ) :
    2 ^ n * (y 0 - c) ≤ z n - c :=
  (ProofPhase.Flip.doubling_defect_floor hy n).trans (by linarith [hyz n])

/-- **The flux branch doubles**: `Doubles z_e c_e` gives `Doubles (2 z_e − a) (2 c_e − a)`. A gain (`c_e < 0`, the data:
`z_e ≈ (L√σ)² − 0.9`) is passed on doubled. -/
theorem flux_branch_doubles {ze : ℕ → ℝ} {ce : ℝ} (a : ℝ) (h : Doubles ze ce) :
    Doubles (fun n => 2 * ze n - a) (2 * ce - a) := fun n => by
  simp only
  linarith [h n]

/-- **Vacuum floor from the branches.** Lower sector transfer in branch form `min(2 z_e − a, μ) ≤ z₀`, flux doubling with
defect `c_e`, doubling of the non-flux branch `μ` with defect `c_μ`: with `y₀ = min(2 z_e(0) − a, μ 0)` and
`c = max(2c_e − a, c_μ)`, `z₀ n − c ≥ 2ⁿ (y₀ − c)`. -/
theorem branches_floor {z ze μ : ℕ → ℝ} {a ce cμ : ℝ} (hlst : ∀ n, min (2 * ze n - a) (μ n) ≤ z n)
    (hflux : Doubles ze ce) (hμ : Doubles μ cμ) (n : ℕ) :
    2 ^ n * (min (2 * ze 0 - a) (μ 0) - max (2 * ce - a) cμ) ≤ z n - max (2 * ce - a) cμ :=
  envelope_floor (y := fun n => min (2 * ze n - a) (μ n)) hlst (min_doubles (flux_branch_doubles a hflux) hμ) n

/-! ## 3. Unit tests -/

/-- **The product SU(2) × U(1)** (act sequences): `z_e = 4ⁿ⁺¹` (flux doubling with gain 1), `z₀ = μ = 2π` (the photon).
It satisfies the upper sector transfer `z₀ ≤ 2 z_e` and the lower one `min(2 z_e − a, μ) ≤ z₀` for every `a`, and for every
`c < 2π` both the vacuum law and the non-flux doubling fail. So flux doubling + both sector transfers do not imply the vacuum
law; the premise of `branches_floor` that the product violates is exactly the doubling of `μ`. -/
theorem product_test :
    Doubles (fun n : ℕ => (4 : ℝ) ^ (n + 1)) (-1) ∧ (∀ n : ℕ, 2 * Real.pi ≤ 2 * (4 : ℝ) ^ (n + 1)) ∧
      (∀ a : ℝ, ∀ n : ℕ, min (2 * (4 : ℝ) ^ (n + 1) - a) (2 * Real.pi) ≤ 2 * Real.pi) ∧
      ∀ c : ℝ, c < 2 * Real.pi → ¬Doubles (fun _ => 2 * Real.pi) c := by
  refine ⟨fun n => ?_, fun n => ?_, fun a n => min_le_right _ _, fun c hc h => ?_⟩
  · simp only
    have : (1 : ℝ) ≤ 4 ^ (n + 1) := one_le_pow₀ (by norm_num)
    rw [pow_succ 4 (n + 1)]
    linarith
  · have h1 : (4 : ℝ) ≤ 4 ^ (n + 1) := by
      calc (4 : ℝ) = 4 ^ 1 := (pow_one 4).symm
        _ ≤ 4 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [Real.pi_lt_four]
  · have := h 0
    simp only at this
    linarith

/-- **The photon's flux act is constant** (`z_e = g²/2` at every `L`): a constant positive `k` doubles only with defect
`c_e ≥ k`, and then the flux branch has no positive start: `(2k − a) − (2c_e − a) ≤ 0`. -/
theorem photon_flux_test {k ce : ℝ} (h : Doubles (fun _ => k) ce) (a : ℝ) : (2 * k - a) - (2 * ce - a) ≤ 0 := by
  have := h 0
  simp only at this
  linarith

/-! ## 4. The sector-resolved gluing deficit -/

/-- **`1 + δ₀ = (1 + δ) ρ(L)²/ρ(2L)`**: `Z₁ = Z(L⁴)`, `Z₂ = Z(L³ × 2L)` (all sectors), `Y₁, Y₂` their `e = 0` parts. -/
theorem vac_deficit_eq {Z₁ Z₂ Y₁ Y₂ : ℝ} (h1 : 0 < Z₁) (h2 : 0 < Z₂) (k1 : 0 < Y₁) (k2 : 0 < Y₂) :
    Y₁ ^ 2 / Y₂ - 1 = (Z₁ ^ 2 / Z₂) * ((Y₁ / Z₁) ^ 2 / (Y₂ / Z₂)) - 1 := by
  congr 1
  field_simp

/-- **Flux saturation bounds the vacuum-sector deficit by the full one**: for `Y₁ ≤ Z₁` (`ρ(L) ≤ 1`),
`δ₀ ≤ (1 + δ)/ρ(2L) − 1`. -/
theorem vac_deficit_le {Z₁ Z₂ Y₁ Y₂ : ℝ} (h1 : 0 < Z₁) (h2 : 0 < Z₂) (k1 : 0 < Y₁) (k2 : 0 < Y₂) (hY : Y₁ ≤ Z₁) :
    Y₁ ^ 2 / Y₂ - 1 ≤ (Z₁ ^ 2 / Z₂) / (Y₂ / Z₂) - 1 := by
  rw [vac_deficit_eq h1 h2 k1 k2]
  have hr : (Y₁ / Z₁) ^ 2 ≤ 1 := pow_le_one₀ (div_nonneg k1.le h1.le) ((div_le_one h1).2 hY)
  have hA : 0 ≤ Z₁ ^ 2 / Z₂ := by positivity
  have hB : 0 < Y₂ / Z₂ := div_pos k2 h2
  have : (Z₁ ^ 2 / Z₂) * ((Y₁ / Z₁) ^ 2 / (Y₂ / Z₂)) ≤ (Z₁ ^ 2 / Z₂) / (Y₂ / Z₂) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hB.le
  linarith

/-! ## 5. The flux-pair observable on the SU(2) boxes -/

section SU2

open ProofPhase.DMP ProofPhase.RouteB AreaLaw.Concrete

theorem su2_hz : ∀ g : SU2, Commute negOneSU2 g :=
  fun g => Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * g.val = g.val * -1 by simp)

/-- A centre flip in a direction other than the line's leaves the Wilson line unchanged. -/
theorem polyLine_centreFlip_ne {L : ℕ} [NeZero L] {i : Fin 3} (hi : i ≠ 0) (c : ZMod L)
    (a : GaugeConnection SU2 3 L) (y : FinLatticeSites 3 L) :
    polyLine L (centreFlip negOneSU2 i c a) y = polyLine L a y := by
  unfold polyLine
  congr 1
  refine List.map_congr_left fun k _ => ?_
  have h0 : ¬((0 : Fin 3) = i) := fun h => hi h.symm
  simp [centreFlip, h0]

/-- **The flux-pair observable `Φ²`** (`Φ` = Route B's summed Wilson line around the first axis): centre-even, bounded,
measurable, i.e. a vacuum-sector observable of the box. It creates two units of Z₂ flux, which are none. -/
def pairObs (L : ℕ) [NeZero L] : VacObs L where
  f a := (polySum L 2 a) ^ 2
  meas := (measurable_polySum (G := SU2) (n := 2) L continuous_subtype_val).pow_const 2
  bound := ((2 : ℝ) * Fintype.card (FinLatticeSites 3 L)) ^ 2
  bdd a := by
    have h := abs_polySum_le (G := SU2) (n := 2) L (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) a
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by exact_mod_cast h) 2
  even i c a := by
    by_cases hi : i = 0
    · subst hi
      have e : centreFlip negOneSU2 (0 : Fin 3) c a = flipA L negOneSU2 c a := rfl
      simp only
      rw [e, polySum_flip (G := SU2) (n := 2) L su2_hz rfl c a, neg_sq]
    · simp only
      unfold polySum
      simp_rw [polyLine_centreFlip_ne hi c a]

/-- **The upper sector transfer is a theorem**: the box gap is at most the decay rate of every non-vanishing connected time
limit of the flux-pair correlation, `E₀(L) ≤ E_pp(L)`. -/
theorem su2_E0_le_pairRate {β : ℝ} {L : ℕ} [NeZero L] (hpos : 0 < E0 β L) {h : ℕ → ℝ}
    (hh : IsConnLimit (su2W L β ∅) (pairObs L).f h) (hp : ∀ s, 0 < h (2 * s)) : E0 β L ≤ rate h :=
  E0_le_rate hpos ⟨pairObs L, hh⟩ hp

/-- The same in act form: `z₀(L) ≤ L · E_pp(L)`. -/
theorem su2_z0_le_pairAct {β : ℝ} {L : ℕ} [NeZero L] (hpos : 0 < E0 β L) {h : ℕ → ℝ}
    (hh : IsConnLimit (su2W L β ∅) (pairObs L).f h) (hp : ∀ s, 0 < h (2 * s)) : z0 β L ≤ L * rate h :=
  mul_le_mul_of_nonneg_left (su2_E0_le_pairRate hpos hh hp) (Nat.cast_nonneg L)

/-! ## 6. The SU(2) gap from an envelope and from the branches -/

/-- **The gap from a doubling lower envelope** on the dyadic SU(2) boxes: `y n ≤ z₀(2ⁿL₀)`, `Doubles y c`, `0 ≤ c < y 0`
give `E₀(2ⁿL₀) ≥ (y 0 − c)/L₀` for every `n`, and the decay of every centre-even connected correlation at that rate. -/
theorem su2_gap_of_envelope {β : ℝ} {L₀ : ℕ} [NeZero L₀] {y : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (h0 : c < y 0)
    (hyz : ∀ n, y n ≤ z0 β (side L₀ n)) (hy : Doubles y c) :
    ∀ n, (y 0 - c) / L₀ ≤ E0 β (side L₀ n) ∧
      ∀ O : VacObs (side L₀ n), ∀ hh, IsConnLimit (su2W (side L₀ n) β ∅) O.f hh →
        ∀ t : ℕ, |hh t| ≤ hh 0 * Real.exp (-((y 0 - c) / L₀ * t)) := by
  intro n
  have hL : (0 : ℝ) < L₀ := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L₀))
  have hm : 0 < (y 0 - c) / L₀ := div_pos (by linarith) hL
  have key : 2 ^ n * (y 0 - c) ≤ z0 β (side L₀ n) - c := envelope_floor hyz hy n
  have hs : ((side L₀ n : ℕ) : ℝ) = 2 ^ n * L₀ := by simp [side]
  have hE : (y 0 - c) / L₀ ≤ E0 β (side L₀ n) := by
    have hz : z0 β (side L₀ n) = 2 ^ n * L₀ * E0 β (side L₀ n) := by rw [z0, hs]
    rw [div_le_iff₀ hL]
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have : 2 ^ n * (y 0 - c) ≤ 2 ^ n * (E0 β (side L₀ n) * L₀) := by nlinarith
    exact le_of_mul_le_mul_left this h2
  exact ⟨hE, fun O hh hc' t => decayLB_of_le_E0 (hm.trans_le hE) hE hh ⟨O, hc'⟩ t⟩

/-- **The SU(2) gap from flux accumulation plus the non-flux branch.** On the periodic dyadic boxes, with the flux act
`z_e = ze β (2ⁿL₀) ∅` and any sequence `μ` (the non-flux branch): if (i) `min(2 z_e − a, μ) ≤ z₀` (lower sector transfer,
open), (ii) `Doubles z_e c_e` (flux accumulation; measured, not proved), (iii) `Doubles μ c_μ` (open: the missing piece),
and the start exceeds the defect, then one gap for all dyadic boxes. -/
theorem su2_gap_of_branches {β : ℝ} {L₀ : ℕ} [NeZero L₀] {μ : ℕ → ℝ} {a ce cμ : ℝ}
    (hc : 0 ≤ max (2 * ce - a) cμ)
    (h0 : max (2 * ce - a) cμ < min (2 * ze β (side L₀ 0) ∅ - a) (μ 0))
    (hlst : ∀ n, min (2 * ze β (side L₀ n) ∅ - a) (μ n) ≤ z0 β (side L₀ n))
    (hflux : Doubles (fun n => ze β (side L₀ n) ∅) ce) (hμ : Doubles μ cμ) :
    ∀ n, (min (2 * ze β (side L₀ 0) ∅ - a) (μ 0) - max (2 * ce - a) cμ) / L₀ ≤ E0 β (side L₀ n) :=
  fun n => (su2_gap_of_envelope (y := fun n => min (2 * ze β (side L₀ n) ∅ - a) (μ n)) hc h0 hlst
    (min_doubles (flux_branch_doubles a hflux) hμ) n).1

end SU2

/-! ## 7. The doubling law with a flux escape -/

/-- **Doubling with a flux escape.** If every doubling either keeps the vacuum law or is paid by flux,
`z(n+1) ≥ min(2 z n − c, K z_e(n+1))` (every centre-even excitation of the big box either transplants into the small box
with act loss `≤ c`, or spans the big box and costs `K` flux acts), and the flux branch stays above the target line
`c + 2ⁿ⁺¹ (z 0 − c)`, then the vacuum act keeps the line: `z n ≥ c + 2ⁿ (z 0 − c)`. -/
theorem escape_floor {z ze : ℕ → ℝ} {c K : ℝ} (h : ∀ n, min (2 * z n - c) (K * ze (n + 1)) ≤ z (n + 1))
    (hesc : ∀ n, c + 2 ^ (n + 1) * (z 0 - c) ≤ K * ze (n + 1)) (n : ℕ) : c + 2 ^ n * (z 0 - c) ≤ z n := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine le_trans (le_min ?_ (hesc n)) (h n)
    rw [pow_succ]
    linarith

/-- **Flux accumulation supplies the escape condition**: if `z_e` doubles with defect `c_e` and
`A := K (z_e 0 − c_e) − 2 (z 0 − c) ≥ max(0, c − K c_e)` with `K ≥ 0` and `c ≤ z 0`, then `K z_e(n+1) ≥ c + 2ⁿ⁺¹ (z 0 − c)` for all `n`. -/
theorem escape_of_flux {z ze : ℕ → ℝ} {c K ce : ℝ} (hK : 0 ≤ K) (hz : c ≤ z 0) (hflux : Doubles ze ce)
    (hA0 : 0 ≤ K * (ze 0 - ce) - 2 * (z 0 - c)) (hA1 : c - K * ce ≤ K * (ze 0 - ce) - 2 * (z 0 - c)) (n : ℕ) :
    c + 2 ^ (n + 1) * (z 0 - c) ≤ K * ze (n + 1) := by
  have hf := ProofPhase.Flip.doubling_defect_floor hflux (n + 1)
  have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hK' : K * (2 ^ (n + 1) * (ze 0 - ce)) ≤ K * (ze (n + 1) - ce) := mul_le_mul_of_nonneg_left hf hK
  have e : 2 ^ (n + 1) * (K * (ze 0 - ce) - 2 * (z 0 - c)) =
      K * (2 ^ (n + 1) * (ze 0 - ce)) - 2 ^ (n + 1) * (2 * (z 0 - c)) := by ring
  have h2 : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have h3 : K * (ze 0 - ce) - 2 * (z 0 - c) ≤ 2 ^ (n + 1) * (K * (ze 0 - ce) - 2 * (z 0 - c)) := by
    rw [h2]; nlinarith
  have hK'' : K * (2 ^ (n + 1) * (ze 0 - ce)) + K * ce ≤ K * ze (n + 1) := by
    have := hK'; rw [mul_sub K (ze (n + 1)) ce] at this; linarith
  have hZ : (2 : ℝ) ^ (n + 1) * (2 * (z 0 - c)) = 2 * (2 ^ (n + 1) * (z 0 - c)) := by ring
  have hW : 0 ≤ (2 : ℝ) ^ (n + 1) * (z 0 - c) := mul_nonneg (by positivity) (by linarith)
  linarith

/-- **Product test for the escape form**: with `z₀ = 2π` (the photon) and any flux act `z_e ≥ 1`, `K ≥ 2π`, the escape law
fails for every `c < 2π`: the photon neither transplants (its act would have to double) nor costs flux. -/
theorem product_escape_test {ze : ℕ → ℝ} {c K : ℝ} (hc : c < 2 * Real.pi) (hK : 2 * Real.pi < K) (hze : ∀ n, 1 ≤ ze n) :
    ¬∀ n, min (2 * (2 * Real.pi) - c) (K * ze (n + 1)) ≤ 2 * Real.pi := by
  intro h
  have h0 := h 0
  have hK1 : K ≤ K * ze 1 := le_mul_of_one_le_right (by linarith [Real.pi_pos]) (hze 1)
  rcases min_le_iff.1 h0 with h' | h' <;> linarith

open ProofPhase.DMP in
/-- **The SU(2) gap from the escape form.** On the periodic dyadic boxes: if every doubling keeps the vacuum law up to `c`
or is paid by `K` flux acts of the big box, `z₀(2ⁿ⁺¹L₀) ≥ min(2 z₀(2ⁿL₀) − c, K z_e(2ⁿ⁺¹L₀))` (open: the transplant /
spanning dichotomy), flux accumulation supplies the escape condition (`escape_of_flux`), and `0 ≤ c < z₀(L₀)`, then
`E₀(2ⁿL₀) ≥ (z₀(L₀) − c)/L₀` for every `n`. -/
theorem su2_gap_of_flux_escape {β : ℝ} {L₀ : ℕ} [NeZero L₀] {c K ce : ℝ} (hc : 0 ≤ c) (h0 : c < z0 β (side L₀ 0))
    (hK : 0 ≤ K)
    (h : ∀ n, min (2 * z0 β (side L₀ n) - c) (K * ze β (side L₀ (n + 1)) ∅) ≤ z0 β (side L₀ (n + 1)))
    (hflux : Doubles (fun n => ze β (side L₀ n) ∅) ce)
    (hA0 : 0 ≤ K * (ze β (side L₀ 0) ∅ - ce) - 2 * (z0 β (side L₀ 0) - c))
    (hA1 : c - K * ce ≤ K * (ze β (side L₀ 0) ∅ - ce) - 2 * (z0 β (side L₀ 0) - c)) :
    ∀ n, (z0 β (side L₀ 0) - c) / L₀ ≤ E0 β (side L₀ n) := by
  have hesc := escape_of_flux (z := fun n => z0 β (side L₀ n)) (ze := fun n => ze β (side L₀ n) ∅) hK h0.le hflux hA0 hA1
  have hy : ∀ n, c + 2 ^ n * (z0 β (side L₀ 0) - c) ≤ z0 β (side L₀ n) :=
    escape_floor (z := fun n => z0 β (side L₀ n)) (ze := fun n => ze β (side L₀ n) ∅) h hesc
  have hd : Doubles (fun n => c + 2 ^ n * (z0 β (side L₀ 0) - c)) c := fun n => by
    simp only; rw [pow_succ]; linarith
  intro n
  have := (su2_gap_of_envelope (y := fun n => c + 2 ^ n * (z0 β (side L₀ 0) - c)) hc (by simp; linarith) hy hd n).1
  simpa using this

end ProofPhase.FluxVac
