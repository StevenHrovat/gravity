/-
The owner's correction (2026-10-27): "You tried a scalar field, not a vector field. In QG it is a vector over time and space and in DMP it is
the trust and refresh rate of that trust. In both times it is the space spanned and direction that give the vector meaning."

So the field is retried as that vector: at every standing, its trust (freshness) and its refresh rate, over the grant graph (space) and the
ticks (time), pointing along the grant chain toward the pair. What the vector adds, and is proven here, in its favour:

1. **The rates are coupled, through the budget.** Every refresh draws on the one budget of checks per window (Physics.lean's `Schedule`),
   so the refresh rate of one standing is bounded by what every other standing leaves (`rates_share_the_budget`): the vector field is coupled
   where the scalar potential was not. The coupling is a conservation law (the rates sum to at most the budget), not a force between pairs.
2. **A horizon depth falls out.** A tree of fan-out b has at least b^D standings at depth D; keeping them all live in one window needs at
   least b^D refreshes, so b^D ≤ r·W (`horizon_depth_bound`): the depth the pair can span grows only logarithmically with its budget. That is
   the vector field's version of the capacity bound and the nearest thing in DMP to a radius.

And what the vector does not change, each a theorem:

3. **The field's law is configuration.** The demand a standing must meet and the window it lives in are functions of the parameters of T9
   (κ, λ, w₀, e_min), chosen at the minting inside an interval; the axioms' laws do not see them (`Field.n1_laws_hold`). So two mintings
   span two different vector fields over the same graph (`field_law_is_configuration`), and no field equation can be a theorem: gravity's
   law is one law with one constant, DMP's is a parameter.
4. **The field has compact support.** A standing is a vector; a contained item has no standing and so no vector (`no_vector_outside`): the
   space DMP's field spans is exactly the inside, and it ends at the horizon. A gravitational field has no edge: for every distance some mass
   is felt there (`gravity_has_no_edge`), and in general relativity the horizon is not where the field stops. The space spanned, which the
   owner says gives the vector its meaning, is the one thing the two fields do not share.
5. **Bell is unchanged.** A vector-valued, time-indexed hidden state (the whole history of freshness and rate) is still a hidden state, and a
   verdict read from it at a tick with a local judge is still a local deterministic outcome: the CHSH bound holds for histories exactly as
   for evidence (`history_gate_obeys_chsh`). The direction and the span of a vector do not make an outcome non-local.
6. **Clausius is unchanged** (NoGo.lean, `clausius_fails`): the drop per entry is the refreshed standing's mass times staleness whether the
   field is read as a scalar or as a vector; the rate adds a time axis, not a temperature.
-/
import Dmp.Physics
import Dmp.Stitch
import Dmp.NoGo

namespace Dmp

/-! ## 1. The rates are coupled through the budget -/

/-- Over a window, the refreshes of two different standings together never exceed the budget left after the boundary work: one standing's
    rate is bounded by what every other standing leaves. -/
theorem count_two_le_length (i j : Nat) (hij : i ≠ j) : ∀ l : List Nat, l.count i + l.count j ≤ l.length := by
  intro l
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : x = i
    · subst hx
      have hj : x ≠ j := hij
      simp [hj]
      omega
    · by_cases hy : x = j
      · subst hy
        simp [hx]
        omega
      · simp [hx, hy]
        omega

theorem rates_share_the_budget (s : Schedule r W) (i j : Nat) (hij : i ≠ j) :
    (s.touchedUpTo W).count i + (s.touchedUpTo W).count j + s.servedUpTo W ≤ r * W := by
  have h1 := count_two_le_length i j hij (s.touchedUpTo W)
  have h2 := s.budget_upTo W (Nat.le_refl W)
  omega

/-! ## 2. A horizon depth falls out -/

/-- With at least b^D standings all kept live in one window and nothing served outward, b^D ≤ r·W: the depth the pair spans grows only
    logarithmically with its budget (the nearest thing in DMP to a radius, and a different law from Schwarzschild's, which is linear in the mass). -/
theorem horizon_depth_bound (s : Schedule r W) (b D n : Nat) (hn : b ^ D ≤ n) (hall : ∀ i, i < n → i ∈ s.touchedUpTo W)
    (hserved : s.servedUpTo W = 0) : b ^ D ≤ r * W := by
  have h1 := all_mem_length n _ hall
  have h2 := s.touched_le_budget hserved
  omega

/-! ## 3. The field's law is configuration -/

/-- Two parameter vectors, both inside T9's intervals, give two different demands at the same depth: the vector field's magnitude law is
    an input of the minting, never a theorem of the axioms. -/
theorem field_law_is_configuration : ∃ π π' : Params, demand π 4 1 ≠ demand π' 4 1 :=
  ⟨⟨330, 100, 500, 100, 100, 1⟩, ⟨330, 100, 1000, 100, 100, 1⟩, by decide⟩

/-! ## 4. The field has compact support -/

/-- The vector at an item: its trust (the admission's evidence) and the rate it was refreshed at; none when the item is contained. -/
def vectorOf (adm : Option Evidence) (rate : Nat) (t : Nat) : Option (Evidence × Nat) :=
  if containedAt adm t then none else
    match adm with
    | some a => some (a, rate)
    | none => none

/-- Outside the inside there is no vector, whatever the rate: the field ends at the horizon. -/
theorem no_vector_outside (adm : Option Evidence) (rate t : Nat) (h : containedAt adm t = true) : vectorOf adm rate t = none := by
  simp [vectorOf, h]

/-- A gravitational field has no edge: at every distance some mass is felt (the toy magnitude M / r², in whole units). -/
theorem gravity_has_no_edge : ∀ dist : Nat, 0 < dist → ∃ M : Nat, 1 ≤ M / (dist * dist) := by
  intro dist hd
  refine ⟨dist * dist, ?_⟩
  have : 0 < dist * dist := Nat.mul_pos hd hd
  rw [Nat.div_self this]
  exact Nat.le_refl 1

/-! ## 5. Bell is unchanged by a vector-valued, time-indexed state -/

/-- Two gates reading a history (the field over time) at a tick: each outcome is a function of the history and the local judge. -/
def historyGateModel (judgeA judgeB : Bool → Evidence → Verdict) (t : Nat) : LocalModel (Nat → Evidence × Evidence) :=
  { A := fun s h => decide (guard (judgeA s) (h t).1 t = .pass)
    B := fun s h => decide (guard (judgeB s) (h t).2 t = .pass) }

theorem history_gate_obeys_chsh (judgeA judgeB : Bool → Evidence → Verdict) (t : Nat) (hs : List (Nat → Evidence × Evidence)) :
    -2 * (hs.length : Int) ≤ (historyGateModel judgeA judgeB t).ssum hs ∧
      (historyGateModel judgeA judgeB t).ssum hs ≤ 2 * (hs.length : Int) :=
  chsh_bound _ hs

end Dmp
