/-
What the physics pass needed (docs/physics.md): two small theorems in DMP's own objects.

1. **The capacity bound.** A Duality's witnesses verify standings live (Axiom 2) and serve acts across the boundary; both draw on one
   budget of checks per tick. A standing that is not verified within its validity lapses (Axiom 2: "a standing is evidence with a
   validity"; T2: a lapse is not an act against it) and from then on passes nothing (`Gate.stale_never_passes`, `lapsed_never_ok` below),
   so the item it admitted is contained where it lies (T37). The theorem is a pigeonhole: over a window of `W` ticks with a budget of
   `r` checks per tick, the standings kept live plus the boundary acts served never exceed `r * W`; when the declared standings exceed
   what the budget leaves after the boundary work, one of them is never refreshed in the window. This is the owner's IT instance
   (2026-10-27 02:21Z: a cluster that serves more I/O "can actively maintain less clients with the same number of nodes") as a theorem,
   and the only place in DMP where the balance of Axiom 1 (trust ageing against live verification) has a number.

2. **The content-free readout.** A record entry is its time and three verdicts and nothing else (Axiom 3: "counts always, content by a
   grant"; T31: an outside reader learns of the inside only its size, its staleness and its rotation interval). `Entry.ext` says that two
   entries that agree on those four fields are the same entry: there is no field a content could hide in. This is the shape of the
   no-hair theorem (Israel 1967, Carter 1971, Robinson 1975: a stationary black hole shows the outside exactly mass, spin and charge)
   in DMP's objects, and it holds by the type, the way `Config.relayout_never_votes` holds by `rfl`.

**Prior art.** The bound is the pigeonhole principle (Dirichlet 1834), applied as a verification budget; the shape is a capacity budget
of the kind Shannon's channel capacity (1948) and Carnot's efficiency (1824) have, except that this one is attained (a schedule that
refreshes every standing once per window exists whenever `n + served ≤ r * W`). Nothing here is invented beyond the counting.
-/
import Dmp.Field
import Dmp.Record

namespace Dmp

/-! ## 1. The capacity bound -/

/-- What the witnesses of a Duality do in one tick: verify a standing live (refresh it, Axiom 2), or serve an act across the boundary. -/
inductive Work where
  | refresh (i : Nat)
  | boundary
  deriving DecidableEq, Repr

/-- The standings a tick's work refreshed. -/
def refreshed (w : List Work) : List Nat :=
  w.filterMap fun a => match a with
    | .refresh i => some i
    | .boundary => none

/-- The boundary acts a tick's work served. -/
def boundaryCount : List Work → Nat
  | [] => 0
  | .refresh _ :: as => boundaryCount as
  | .boundary :: as => boundaryCount as + 1

/-- Every piece of work is one or the other: refreshes plus boundary acts are the tick's work. -/
theorem refreshed_add_boundary (w : List Work) : (refreshed w).length + boundaryCount w = w.length := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    cases a <;> simp only [refreshed, List.filterMap_cons, boundaryCount, List.length_cons] at ih ⊢ <;> omega

/-- A schedule: the work of each tick of a window of `W` ticks, never more than the budget `r` per tick. -/
structure Schedule (r W : Nat) where
  work : Nat → List Work
  budget : ∀ t, t < W → (work t).length ≤ r

/-- The standings refreshed at least once in the first `t` ticks (with repetition; only membership matters). -/
def Schedule.touchedUpTo (s : Schedule r W) : Nat → List Nat
  | 0 => []
  | t + 1 => s.touchedUpTo t ++ refreshed (s.work t)

/-- The boundary acts served in the first `t` ticks. -/
def Schedule.servedUpTo (s : Schedule r W) : Nat → Nat
  | 0 => 0
  | t + 1 => s.servedUpTo t + boundaryCount (s.work t)

/-- The budget over the window: standings refreshed plus boundary acts served never exceed `r` per tick, so never `r * t` over `t` ticks. -/
theorem Schedule.budget_upTo (s : Schedule r W) : ∀ t, t ≤ W → (s.touchedUpTo t).length + s.servedUpTo t ≤ r * t := by
  intro t
  induction t with
  | zero => intro _; simp [Schedule.touchedUpTo, Schedule.servedUpTo]
  | succ t ih =>
    intro ht
    have h1 := ih (Nat.le_of_succ_le ht)
    have h2 := s.budget t (Nat.lt_of_succ_le ht)
    have h3 := refreshed_add_boundary (s.work t)
    simp only [Schedule.touchedUpTo, Schedule.servedUpTo, List.length_append]
    rw [Nat.mul_succ]
    omega

/-- A standing refreshed at some tick of the window is among the touched. -/
theorem Schedule.mem_touchedUpTo (s : Schedule r W) (i : Nat) : ∀ u t, t < u → i ∈ refreshed (s.work t) → i ∈ s.touchedUpTo u := by
  intro u
  induction u with
  | zero => intro t ht; exact absurd ht (Nat.not_lt_zero t)
  | succ u ih =>
    intro t ht hmem
    simp only [Schedule.touchedUpTo, List.mem_append]
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with
    | inl h => exact Or.inl (ih t h hmem)
    | inr h => exact Or.inr (h ▸ hmem)

/-- Pigeonhole, the counting half: a list that holds every number below `n` has at least `n` entries. -/
theorem all_mem_length (n : Nat) : ∀ l : List Nat, (∀ i, i < n → i ∈ l) → n ≤ l.length := by
  induction n with
  | zero => intro l _; exact Nat.zero_le _
  | succ n ih =>
    intro l h
    have hn : n ∈ l := h n (Nat.lt_succ_self n)
    have h' : ∀ i, i < n → i ∈ l.erase n :=
      fun i hi => (List.mem_erase_of_ne (Nat.ne_of_lt hi)).mpr (h i (Nat.lt_succ_of_lt hi))
    have hle := ih (l.erase n) h'
    rw [List.length_erase_of_mem hn] at hle
    have hpos : 0 < l.length := List.length_pos_of_mem hn
    omega

/-- Pigeonhole: a list shorter than `n` misses some number below `n`. -/
theorem pigeonhole (n : Nat) (l : List Nat) (h : l.length < n) : ∃ i, i < n ∧ i ∉ l := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ i, i < n → i ∈ l := by
    intro i hi
    apply Classical.byContradiction
    intro hni
    exact hno ⟨i, hi, hni⟩
  have := all_mem_length n l hall
  omega

/-- **The capacity bound.** With `n` standings declared and the budget of the window spent beyond what they need (`r * W` is less than the
    standings plus the boundary acts served), some standing is never refreshed in the window: it lapses, and the item it admitted is
    contained (T37). Clients plus boundary I/O never exceed the budget. -/
theorem Schedule.some_standing_lapses (s : Schedule r W) (n : Nat) (h : r * W < n + s.servedUpTo W) :
    ∃ i, i < n ∧ ∀ t, t < W → i ∉ refreshed (s.work t) := by
  have hb := s.budget_upTo W (Nat.le_refl W)
  have hl : (s.touchedUpTo W).length < n := by omega
  obtain ⟨i, hi, hni⟩ := pigeonhole n _ hl
  exact ⟨i, hi, fun t ht hmem => hni (s.mem_touchedUpTo i W t ht hmem)⟩

/-- The counts-only case (the Schwarzschild case of docs/physics.md): with nothing served across the boundary, up to `r * W` standings
    are kept live. -/
theorem Schedule.touched_le_budget (s : Schedule r W) (hserved : s.servedUpTo W = 0) : (s.touchedUpTo W).length ≤ r * W := by
  have := s.budget_upTo W (Nat.le_refl W)
  omega

/-- The extremal case: a window whose whole budget went to the boundary keeps no standing live. -/
theorem Schedule.extremal_keeps_nothing (s : Schedule r W) (hserved : s.servedUpTo W = r * W) : (s.touchedUpTo W).length = 0 := by
  have := s.budget_upTo W (Nat.le_refl W)
  omega

/-- A lapsed standing is no evidence at the point of use, whatever its judge would say (K2). -/
theorem lapsed_never_ok (e : Evidence) (t : Nat) (h : e.validUntil ≤ t) : e.ok t = false := by
  unfold Evidence.ok
  have : Nat.blt t e.validUntil = false := by
    cases hb : Nat.blt t e.validUntil
    · rfl
    · exfalso
      rw [Nat.blt_eq] at hb
      omega
  simp [this]

/-! ## 2. The content-free readout -/

/-- A record entry is its time and three verdicts and nothing else: two entries that agree on those are the same entry. There is no
    field a content could hide in (Axiom 3, T31: counts, never content). -/
theorem Entry.ext (e e' : Entry) (ht : e.t = e'.t) (h1 : e.v1 = e'.v1) (h2 : e.v2 = e'.v2) (ho : e.outcome = e'.outcome) : e = e' := by
  cases e; cases e'; simp_all

end Dmp
