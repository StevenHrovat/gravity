/-
The SU(N) hand-over over all N sectors, by the full turn (draft 5, 2026-11-25).
Released under Apache 2.0.

Paper: `docs/paper/D5/draft/03-part-III-yang-mills.md`, III.3.1c and III.5.4d (Draft 5); IM's `Arsenal.FullTurn`.
-/

import ProofPhase.General.SUNHandOver
import Arsenal.FullTurn

/-!
# The SU(N) hand-over by the full turn

`sun_handover` gives the rate `log (1 + √2)` from one twisted sector `k` and the pair `Z ± Z_tw,k`: the full turn over `±1`.
Here the full turn runs over all `N` sectors of the centre `Z_N`. The **electric sectors** are the full turn of the twisted
partition functions,

  `Z_el(e) = (1/N) ∑_k cos (2π k e / N) Z_tw,k`,

the real form of 't Hooft's electric-flux projection (real because `Z_tw,-k = Z_tw,k`, `sunZtw_neg`). One turn gives the two
identities `∑_e Z_el(e) = Z` (`sunZel_sum`) and `N Z_el(0) = ∑_k Z_tw,k` (`sunZel_zero`), and IM's balance
(`Arsenal.FullTurn.full_turn_balance_log`) turns them into the rate `log (1 + √N)`:

* `sun_handover_full_turn`: for every `N ≥ 2`, some nontrivial twist free energy or some nontrivial electric free energy of the
  SU(N) Wilson box is at least `log (1 + √N)`, given that the electric sectors are positive.
* `sun_handover_full_turn_mean`: the same for the mean over the `N - 1` nontrivial sectors of one type (IM's
  `full_turn_balance_mean`): a maximum over sectors is a rate along a path that turns once through them.
* `sunZel_pos_two`: for `N = 2` that positivity is a theorem (`Z ± Z_tw > 0`), so the `N = 2` rate is `log (1 + √2)`, the rate of
  `sun_handover`.

The positivity of the electric sectors for `N ≥ 3` is the one input stated as a hypothesis (each `Z_el(e)` is the trace of the
lattice transfer matrix on one electric-flux sector, `Z_el(e) = Tr(P_e T^T) ≥ 0`, positive in the transfer-matrix picture; not proved
here).
No axioms beyond the standard ones.
-/

open Finset ProofPhase.Flip

namespace ProofPhase.General

variable (N : ℕ) [NeZero N] (L : ℕ) [NeZero L]

/-- **The electric sectors**: the full turn of the twisted partition functions over the centre `Z_N`,
`Z_el(e) = (1/N) ∑_k cos (2π k e / N) Z_tw,k`. -/
noncomputable def sunZel (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T] (e : Fin N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k : ZMod N, Real.cos (2 * Real.pi * (e.val : ℝ) * (k.val : ℝ) / N) * sunZtw N L β P c T k

/-- One turn over the sectors `e`: `∑_e cos (2π e k / N)` is `N` for `k = 0` and `0` otherwise. -/
theorem sum_cos_sectors (k : ZMod N) :
    ∑ e : Fin N, Real.cos (2 * Real.pi * (e.val : ℝ) * (k.val : ℝ) / N) = if k = 0 then (N : ℝ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => Real.cos (2 * Real.pi * (j : ℝ) * (k.val : ℝ) / N)),
    Arsenal.FullTurn.full_turn_cos (Nat.pos_of_ne_zero (NeZero.ne N)) k.val]
  have h : N ∣ k.val ↔ k = 0 := by
    constructor
    · intro hd
      have hlt := ZMod.val_lt k
      rcases hd with ⟨q, hq⟩
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · rw [h0, mul_zero] at hq; exact (ZMod.val_eq_zero k).1 hq
      · have := Nat.mul_le_mul_left N h0; omega
    · rintro rfl; simp
  simp only [h]

/-- **The turn back**: the electric sectors add up to the untwisted partition function. -/
theorem sunZel_sum (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T] :
    ∑ e : Fin N, sunZel N L β P c T e = sunZ N L β P T := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold sunZel
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_cos_sectors]
  rw [Finset.sum_eq_single (0 : ZMod N)]
  · simp only [↓reduceIte, sunZtw_zero]; field_simp
  · intro k _ hk; simp only [hk, ↓reduceIte, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The base sector**: `N Z_el(0)` is the sum of all twisted partition functions. -/
theorem sunZel_zero (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T] :
    (N : ℝ) * sunZel N L β P c T 0 = ∑ k : ZMod N, sunZtw N L β P c T k := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  unfold sunZel
  simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_mul, zero_div, Real.cos_zero, one_mul]
  field_simp

/-- **The hand-over over all `N` sectors**: for every `N ≥ 2`, if the electric sectors are positive, then some nontrivial twist free
energy or some nontrivial electric free energy of the SU(N) Wilson box is at least `log (1 + √N)`. -/
theorem sun_handover_full_turn [Fact (1 < N)] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T]
    (hel : ∀ e : Fin N, 0 < sunZel N L β P c T e) :
    (∃ k : ZMod N, k ≠ 0 ∧ Real.log (1 + √(N : ℝ)) ≤ twistF (sunZ N L β P T) (sunZtw N L β P c T k)) ∨
      (∃ e : Fin N, e ≠ 0 ∧
        Real.log (1 + √(N : ℝ)) ≤ Real.log (sunZel N L β P c T 0 / sunZel N L β P c T e)) := by
  have hN2 : 2 ≤ N := (Fact.out : 1 < N)
  have h := Arsenal.FullTurn.full_turn_balance_log (ZMod.card N) (Fintype.card_fin N) hN2 (0 : ZMod N) (0 : Fin N)
    (fun k => sunZtw N L β P c T k) (fun e => sunZel N L β P c T e) (fun k => sunZtw_pos N L β P c T k) hel
    (by rw [sunZel_sum, sunZtw_zero]) (sunZel_zero N L β P c T)
  rcases h with ⟨k, hk, hle⟩ | ⟨e, he, hle⟩
  · refine Or.inl ⟨k, hk, ?_⟩
    have : twistF (sunZ N L β P T) (sunZtw N L β P c T k) = Real.log (sunZ N L β P T / sunZtw N L β P c T k) := by
      rw [twistF, ← Real.log_inv, inv_div]
    rw [this, ← sunZtw_zero N L β P c T]
    exact hle
  · exact Or.inr ⟨e, he, hle⟩

/-- **The hand-over along a path**: if the electric sectors are positive, the mean twist free energy over the `N - 1` nontrivial
sectors, or the mean electric free energy over them, is at least `log (1 + √N)`. -/
theorem sun_handover_full_turn_mean [Fact (1 < N)] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ)
    [NeZero T] (hel : ∀ e : Fin N, 0 < sunZel N L β P c T e) :
    Real.log (1 + √(N : ℝ)) ≤
        (∑ k ∈ Finset.univ.erase (0 : ZMod N), twistF (sunZ N L β P T) (sunZtw N L β P c T k)) / ((N : ℝ) - 1) ∨
      Real.log (1 + √(N : ℝ)) ≤
        (∑ e ∈ Finset.univ.erase (0 : Fin N), Real.log (sunZel N L β P c T 0 / sunZel N L β P c T e)) / ((N : ℝ) - 1) := by
  have hN2 : 2 ≤ N := (Fact.out : 1 < N)
  have h := Arsenal.FullTurn.full_turn_balance_mean (ZMod.card N) (Fintype.card_fin N) hN2 (0 : ZMod N) (0 : Fin N)
    (fun k => sunZtw N L β P c T k) (fun e => sunZel N L β P c T e) (fun k => sunZtw_pos N L β P c T k) hel
    (by rw [sunZel_sum, sunZtw_zero]) (sunZel_zero N L β P c T)
  have htw : ∀ k, twistF (sunZ N L β P T) (sunZtw N L β P c T k)
      = Real.log (sunZtw N L β P c T 0 / sunZtw N L β P c T k) := by
    intro k
    rw [twistF, ← Real.log_inv, inv_div, sunZtw_zero]
  simp_rw [htw]
  exact h

/-- **For `N = 2` the electric sectors are positive**: they are `(Z ± Z_tw) / 2`, and `0 < Z_tw < Z` (`sunZtw_pos`, `sunZtw_lt`). So
the `N = 2` rate holds with no hypothesis beyond `β ≠ 0` and an even time extent. -/
theorem sunZel_pos_two [Fact (1 < 2)] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ}
    [NeZero T] (hT : Even T) (e : Fin 2) : 0 < sunZel 2 L β P c T e := by
  have hpos := sunZtw_pos 2 L β P c T 1
  have hlt := sunZtw_lt 2 L hβ P c hT (k := (1 : ZMod 2)) (by decide)
  have h0 := sunZtw_zero 2 L β P c T
  have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  have hv0 : ((ZMod.val (0 : ZMod 2) : ℕ) : ℝ) = 0 := by simp
  have hv1 : ((ZMod.val (1 : ZMod 2) : ℕ) : ℝ) = 1 := by simp [ZMod.val_one]
  have hcpi : Real.cos (2 * Real.pi * 1 * 1 / 2) = -1 := by
    rw [show 2 * Real.pi * 1 * 1 / 2 = Real.pi by ring, Real.cos_pi]
  unfold sunZel
  rw [huniv, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1), hv0, hv1, h0]
  fin_cases e
  · simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Real.cos_zero, one_mul]
    have := sunZ_pos 2 L β P T
    positivity
  · simp only [Nat.cast_one, mul_zero, zero_div, Real.cos_zero, one_mul]
    have := sunZ_pos 2 L β P T
    norm_num
    linarith

end ProofPhase.General
