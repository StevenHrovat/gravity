/-
Round 4, attempt 4 (r4-minting), 2026-11-21. Released under Apache 2.0.

# The DMP side of the minting conservation law (restated; a toy, no Yang–Mills in it)

Note: `docs/mass-gap/weak-coupling/attempts/r4-minting/NOTE.md`, section 1.

`evidence/Dmp/` is a separate Lean project, so the DMP objects used here are restated over the reals:
- `configStep`: T4 ("the trust configuration ... is fixed by both halves at the minting and changed only by a majority of trust", with
  T5's majority in both halves and T24b's lockstep): a minted value changes only on an act both halves sign, in either direction.
- `standingStep`: T24 (`evidence/Dmp/Standing.lean`, `update`): a standing is tightened on one witness, loosened only with both.
- `res`: the wave clock (`evidence/Dmp/R1Wave.lean`, `wvLayerBy`): layer `n` ticks once per `b^n` root ticks, so its resolution is
  derived from the root's, `k_n = k_0 / b^n`; no layer has a clock of its own.
- the act identity, its floor and 3s1t (`evidence/Dmp/Reach.lean`: `mg_reach_existence_floor`, `mg_space_time_certificate`).

What is proved:
1. `config_conserved`, `minted_value_every_layer`: a minted value is the same at every layer, as long as no act on the chain carries both
   signatures (no reminting): conservation derived from the root, not assumed per layer.
2. `standing_never_rises`, `standing_layers_only_tighten`, `standing_can_drop_to_zero`: a value governed by T24 only tightens across
   layers (one-sided), and one witness alone can drive it to zero at the first layer: no conservation, no floor.
3. `act_identity_every_layer`, `space_time_every_layer`: if the root's act obeys the act identity with the minted quantum and each layer
   step carries the act exactly to the coarser grid (one step rule, the same at every step), the act identity holds at every layer with
   the minted quantum, and 3s1t holds at every layer.
4. `floor_every_layer_of_minting`: `Reach.mg_reach_floor_every_layer` with its per-layer hypotheses ("the same Q and R at every layer")
   replaced by: the minted Q at the root, the exact step, and a reach that only tightens (one-sided suffices for the reach).
5. `frozen_no_floor`: read across scales instead of across resolutions (the same quantum for acts of every extent), the law is light's:
   the existence falls below every floor (`mg_no_reach_no_floor` in real form).
-/

import Mathlib

namespace Attempts.R4.Minting

noncomputable section

/-! ## 1. Minted values versus standings -/

/-- An act on a recorded value: the proposed new value and which halves signed it. -/
structure Act where
  new : ℝ
  w1 : Bool
  w2 : Bool

/-- An act both halves signed (the only kind that can change a minted value: a reminting-type act). -/
def Act.both (a : Act) : Prop := a.w1 = true ∧ a.w2 = true

/-- T4: a minted value changes only on an act both halves sign, in either direction. -/
def configStep (old : ℝ) (a : Act) : ℝ := if a.w1 && a.w2 then a.new else old

/-- T24: a standing is tightened (lowered) on one witness; loosening needs both. -/
def standingStep (old : ℝ) (a : Act) : ℝ :=
  if a.new ≤ old then (if a.w1 || a.w2 then a.new else old) else (if a.w1 && a.w2 then a.new else old)

/-- A sequence of acts applied to a minted value. -/
def runConfig : ℝ → List Act → ℝ
  | v, [] => v
  | v, a :: as => runConfig (configStep v a) as

/-- A sequence of acts applied to a standing. -/
def runStanding : ℝ → List Act → ℝ
  | v, [] => v
  | v, a :: as => runStanding (standingStep v a) as

theorem configStep_fixed (v : ℝ) (a : Act) (h : ¬ a.both) : configStep v a = v := by
  unfold configStep
  unfold Act.both at h
  cases h1 : a.w1 <;> cases h2 : a.w2 <;> simp_all

/-- **A minted value is conserved** along any sequence of acts none of which both halves signed. -/
theorem config_conserved (v : ℝ) (as : List Act) (h : ∀ a ∈ as, ¬ a.both) : runConfig v as = v := by
  induction as generalizing v with
  | nil => rfl
  | cons a as ih =>
    simp only [runConfig]
    rw [configStep_fixed v a (h a List.mem_cons_self)]
    exact ih v (fun b hb => h b (List.mem_cons_of_mem a hb))

theorem standingStep_le (v : ℝ) (a : Act) (h : ¬ a.both) : standingStep v a ≤ v := by
  unfold standingStep
  split_ifs <;> simp_all [Act.both]

/-- **A standing only tightens** along acts none of which both halves signed (one-sided). -/
theorem standing_never_rises (v : ℝ) (as : List Act) (h : ∀ a ∈ as, ¬ a.both) : runStanding v as ≤ v := by
  induction as generalizing v with
  | nil => exact le_refl v
  | cons a as ih =>
    simp only [runStanding]
    exact le_trans (ih _ (fun b hb => h b (List.mem_cons_of_mem a hb))) (standingStep_le v a (h a List.mem_cons_self))

/-- The value at every layer of a chain: the root holds the minted value, layer `n + 1` is layer `n` after the acts recorded there. -/
def layerValue (run : ℝ → List Act → ℝ) (Q : ℝ) (acts : ℕ → List Act) : ℕ → ℝ
  | 0 => Q
  | n + 1 => run (layerValue run Q acts n) (acts (n + 1))

/-- **Conservation across layers, derived from the minting.** With no act on the chain signed by both halves, every layer holds the
minted value. The hypothesis is one property of the chain (no reminting), not one hypothesis per layer. -/
theorem minted_value_every_layer (Q : ℝ) (acts : ℕ → List Act) (h : ∀ n, ∀ a ∈ acts n, ¬ a.both) :
    ∀ n, layerValue runConfig Q acts n = Q := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [layerValue]
    rw [config_conserved _ _ (h (n + 1)), ih]

/-- **A standing across layers is only monotone**: each layer is at most its parent (sub-layers only tighten). -/
theorem standing_layers_only_tighten (Q : ℝ) (acts : ℕ → List Act) (h : ∀ n, ∀ a ∈ acts n, ¬ a.both) (n : ℕ) :
    layerValue runStanding Q acts (n + 1) ≤ layerValue runStanding Q acts n ∧ layerValue runStanding Q acts n ≤ Q := by
  have step : ∀ m, layerValue runStanding Q acts (m + 1) ≤ layerValue runStanding Q acts m := fun m =>
    standing_never_rises _ _ (h (m + 1))
  refine ⟨step n, ?_⟩
  induction n with
  | zero => exact le_refl Q
  | succ m ih => exact le_trans (step m) ih

/-- **One witness can drop a standing to zero at the first layer**: with the quantum governed like a standing, no floor survives. -/
theorem standing_can_drop_to_zero (Q : ℝ) (hQ : 0 ≤ Q) :
    (∀ a ∈ [Act.mk 0 true false], ¬ a.both) ∧
      ∀ n, 1 ≤ n → layerValue runStanding Q (fun _ => [Act.mk 0 true false]) n = 0 := by
  refine ⟨fun a ha => ?_, fun n hn => ?_⟩
  · simp only [List.mem_singleton] at ha
    subst ha
    simp [Act.both]
  · induction n with
    | zero => omega
    | succ m ih =>
      simp only [layerValue, runStanding, standingStep]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp [layerValue, hQ]
      · rw [ih hm]
        simp

/-! ## 2. The act identity at every layer, derived from the root -/

/-- The wave clock: layer `n` ticks once per `b^n` root ticks, so its resolution (ticks per unit length) is `k₀ / bⁿ`. -/
def res (k0 b : ℝ) (n : ℕ) : ℝ := k0 / b ^ n

theorem res_succ (k0 b : ℝ) (n : ℕ) : res k0 b (n + 1) = res k0 b n / b := by
  unfold res
  rw [pow_succ, div_div]

theorem res_pos {k0 b : ℝ} (hk0 : 0 < k0) (hb : 0 < b) (n : ℕ) : 0 < res k0 b n :=
  div_pos hk0 (pow_pos hb n)

/-- **The act identity at every layer with the minted quantum.** The root's act obeys `x₀ · e₀ = Q · k₀²`; one step rule, the same at
every step, carries the act exactly to the next coarser grid (existence and extent in grid units both divided by the clock ratio `b`).
Then `xₙ · eₙ = Q · kₙ²` at every layer. -/
theorem act_identity_every_layer {Q k0 b : ℝ} (hb : b ≠ 0) (x e : ℕ → ℝ) (hroot : x 0 * e 0 = Q * k0 ^ 2)
    (hx : ∀ n, x (n + 1) = x n / b) (he : ∀ n, e (n + 1) = e n / b) : ∀ n, x n * e n = Q * res k0 b n ^ 2 := by
  intro n
  induction n with
  | zero => simp [res, hroot]
  | succ n ih =>
    rw [hx, he, res_succ]
    have h1 : x n / b * (e n / b) = (x n * e n) / b ^ 2 := by ring
    rw [h1, ih]
    field_simp

/-- **3s1t at every layer.** With the space and the time certificate both carried from the root, extent and time to live agree at every
layer where the existence is not zero (`Reach.mg_space_time_certificate`, layer by layer). -/
theorem space_time_every_layer {Q k0 b : ℝ} (hb : b ≠ 0) (x e τ : ℕ → ℝ) (hroot : x 0 * e 0 = Q * k0 ^ 2)
    (hroot' : x 0 * τ 0 = Q * k0 ^ 2) (hx : ∀ n, x (n + 1) = x n / b) (he : ∀ n, e (n + 1) = e n / b)
    (hτ : ∀ n, τ (n + 1) = τ n / b) (n : ℕ) (hxn : x n ≠ 0) : e n = τ n := by
  have h1 := act_identity_every_layer hb x e hroot hx he n
  have h2 := act_identity_every_layer hb x τ hroot' hx hτ n
  exact mul_left_cancel₀ hxn (h1.trans h2.symm)

/-- **The floor at every layer, from the minting.** `Reach.mg_reach_floor_every_layer` assumed the same quantum and the same reach at
every layer. Here: the minted quantum at the root and the exact step (two-sided) give the act identity at every layer; the reach only
has to tighten (`Rₙ ≤ R`, one-sided, "a sub-layer only tightens"). Then `Q · kₙ ≤ xₙ · R` at every layer. -/
theorem floor_every_layer_of_minting {Q k0 b R : ℝ} (hQ : 0 ≤ Q) (hk0 : 0 < k0) (hb : 0 < b) (x e Rn : ℕ → ℝ)
    (hroot : x 0 * e 0 = Q * k0 ^ 2) (hx : ∀ n, x (n + 1) = x n / b) (he : ∀ n, e (n + 1) = e n / b) (he0 : 0 < e 0)
    (hreach : ∀ n, e n ≤ Rn n * res k0 b n) (htight : ∀ n, Rn n ≤ R) : ∀ n, Q * res k0 b n ≤ x n * R := by
  intro n
  have hk := res_pos hk0 hb n
  have hid := act_identity_every_layer hb.ne' x e hroot hx he n
  have hen : 0 < e n := by
    induction n with
    | zero => exact he0
    | succ m ih => rw [he]; exact div_pos (ih (res_pos hk0 hb m) (act_identity_every_layer hb.ne' x e hroot hx he m)) hb
  have hxn : 0 ≤ x n := by
    by_contra hneg
    push Not at hneg
    have : x n * e n < 0 := mul_neg_of_neg_of_pos hneg hen
    have : 0 ≤ Q * res k0 b n ^ 2 := mul_nonneg hQ (sq_nonneg _)
    linarith
  have hreach' : e n ≤ R * res k0 b n :=
    le_trans (hreach n) (mul_le_mul_of_nonneg_right (htight n) hk.le)
  have h3 : Q * res k0 b n * res k0 b n ≤ x n * R * res k0 b n := by
    calc Q * res k0 b n * res k0 b n = x n * e n := by rw [hid]; ring
      _ ≤ x n * (R * res k0 b n) := mul_le_mul_of_nonneg_left hreach' hxn
      _ = x n * R * res k0 b n := by ring
  exact le_of_mul_le_mul_right h3 hk

/-! ## 3. The same law read across scales is light's -/

/-- **The quantum conserved across extents gives no floor.** If acts of every extent `L > 0` carry the same quantum (`E(L) · L = Q`, the
act number frozen across scales, as for the free photon, `z = 2πα`), the existence falls below every proposed floor. -/
theorem frozen_no_floor (Q : ℝ) (E : ℝ → ℝ) (hz : ∀ L, 0 < L → E L * L = Q) : ∀ ε, 0 < ε → ∃ L, 0 < L ∧ E L < ε := by
  intro ε hε
  have hL : 0 < |Q| / ε + 1 := by positivity
  refine ⟨|Q| / ε + 1, hL, ?_⟩
  have hE : E (|Q| / ε + 1) = Q / (|Q| / ε + 1) := eq_div_of_mul_eq hL.ne' (hz _ hL)
  rw [hE, div_lt_iff₀ hL]
  have h1 : ε * (|Q| / ε + 1) = |Q| + ε := by field_simp
  rw [h1]
  linarith [le_abs_self Q]

end

end Attempts.R4.Minting
