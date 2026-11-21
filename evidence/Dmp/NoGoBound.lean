/-
The owner's restatement (2026-10-27), after "You are doing the wrong thing": "QG is an extension of the two axiom system that prescribes
existence alone as proof of existence, where that is replaced by the only allowable replacement, a vector consisting of one vector that
bounds a space which can contain a field, and another, which gives change in the field a direction. Those two things, given initial
settings, Planck's constant, G and c, is able to solve the field part of the duality, which also contains a hierarchical information
space, which, with our settings, pushes the bounds faster than the field they project allows the force transmitting particles to catch
up, to also extend the field, which carries them, as they go. So the growth of bounds, in our case, slows down, and should be completely
modelable."

So this file models the extension itself, not DMP's objects: a bound of the existence space, a field inside it that the force carriers
extend toward the bound at their speed `c`, and a push on the bound by the information inside that acts only where the field has arrived
(the push is projected through the field, the owner's words). Nothing of DMP enters; the model is the owner's sentence and three numbers:
the carriers' speed, the push, and, in section 2, a capacity.

What the kernel decides (docs/qg-attempt.md section 4.10):

1. **The bound slows to the carriers' speed and never below it.** The bound never gets further ahead of the field than one push
   (`bound_within_one_push`), the field advances at most `c` per tick (`field_speed_le_carriers`), so the bound advances at most
   `c · t + push` over `t` ticks (`bound_speed_le_carriers`). The owner's "slows down" is a slowing from faster than the carriers to the
   carriers' speed. And it never stops: while the information pushes and the carriers move, the field reaches the bound again and the bound
   moves again (`bound_never_stops`).
2. **To slow to zero the bound needs a capacity, and the capacity is the cosmological constant.** With a cap `K` on the bound, the push acting
   only while the bound stays within it, the bound never exceeds `K` (`capacity_stops_the_bound`) and the growth ends there
   (`growth_ends_at_capacity`). In the universe the bound that the force carriers cannot catch up with is the cosmic event horizon; its
   growth does slow to zero, and the radius it freezes at is c · sqrt(3/Λ) (de Sitter; Gibbons and Hawking 1977). Its capacity in
   information is the horizon area over 4 ℓ_P², which is where ħ and G enter. `K` is Λ, and Λ is an input of this model as of every other
   (Weinberg 1989): ħ, G and c fix the Planck scale, and Λ is 10⁻¹²² of it.
3. **The same Λ makes the distances inside accelerate.** The horizon freezes because the recession speed at the horizon reaches c, and that is
   the acceleration of section 4.7 seen from the edge: dr/dt = H · r − c goes to zero exactly as H · r goes to c. "The growth of bounds slows
   down" and "the expansion accelerates" are one fact, and neither is derived from the duality; both are derived from Λ. (Section 4.7 read
   "expansion" as the distances inside and said the slowing is false; for the horizon it is true, and this section says so.)

The physics this lands on has names: the de Sitter horizon and its thermodynamics (Gibbons and Hawking 1977), the information bound on a
horizon (Bekenstein 1981; Bousso 1999), and the expansion of space as the quest for holographic equipartition between the bulk and the
boundary degrees of freedom (Padmanabhan 2012), which derives the Friedmann equation from the owner's picture with ħ, G and c as inputs and
the de Sitter state as the end. What that programme does not have is what quantum gravity would be: the microscopic degrees of freedom
whose count is the capacity. The owner's extension names them ("a hierarchical information space") and does not give them, and the change
the direction vector gives is a definite function of the field, so the gate of section 4.2 (the CHSH bound) stands over this model too.
-/

namespace Dmp

/-! ## 1. The bound and the field front -/

/-- The owner's extension, discretised: the bound of the existence space and the front of the field the carriers have extended inside it. -/
structure Front where
  bound : Nat
  field : Nat

/-- One tick: the carriers extend the field by `c`, never past the bound; the information pushes the bound by `push` only where the field has
    reached it. -/
def stepFront (c push : Nat) (s : Front) : Front :=
  let field' := if s.field + c ≤ s.bound then s.field + c else s.bound
  { bound := if field' = s.bound then s.bound + push else s.bound, field := field' }

theorem stepFront_field (c push : Nat) (s : Front) :
    (stepFront c push s).field = if s.field + c ≤ s.bound then s.field + c else s.bound := rfl

theorem stepFront_bound (c push : Nat) (s : Front) :
    (stepFront c push s).bound = if (stepFront c push s).field = s.bound then s.bound + push else s.bound := rfl

/-- The front after `t` ticks. -/
def runFront (c push : Nat) (s : Front) : Nat → Front
  | 0 => s
  | t + 1 => stepFront c push (runFront c push s t)

theorem runFront_add (c push : Nat) (s : Front) (t : Nat) : ∀ u, runFront c push s (t + u) = runFront c push (runFront c push s t) u := by
  intro u
  induction u with
  | zero => rfl
  | succ u ih =>
    show stepFront c push (runFront c push s (t + u)) = stepFront c push (runFront c push (runFront c push s t) u)
    rw [ih]

theorem runFront_shift (c push : Nat) (s : Front) : ∀ t, runFront c push s (t + 1) = runFront c push (stepFront c push s) t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    show stepFront c push (runFront c push s (t + 1)) = stepFront c push (runFront c push (stepFront c push s) t)
    rw [ih]

/-- The field advances at most `c` per tick: the carriers' speed. -/
theorem field_speed_le_carriers (c push : Nat) (s : Front) : (stepFront c push s).field ≤ s.field + c := by
  rw [stepFront_field]
  split <;> omega

/-- Over `t` ticks the field advances at most `c · t`. -/
theorem field_run_le (c push : Nat) (s : Front) : ∀ t, (runFront c push s t).field ≤ s.field + c * t := by
  intro t
  induction t with
  | zero => simp [runFront]
  | succ t ih =>
    simp only [runFront]
    have := field_speed_le_carriers c push (runFront c push s t)
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- The bound never gets further ahead of the field than one push. -/
theorem bound_within_one_push (c push : Nat) (s : Front) (h : s.bound ≤ s.field + push) :
    (stepFront c push s).bound ≤ (stepFront c push s).field + push := by
  rw [stepFront_bound, stepFront_field]
  by_cases h1 : s.field + c ≤ s.bound
  · by_cases h2 : s.field + c = s.bound
    · simp [h2]
    · simp [h1, h2]
      omega
  · simp [h1]

theorem bound_run_within_one_push (c push : Nat) (s : Front) (h : s.bound ≤ s.field + push) :
    ∀ t, (runFront c push s t).bound ≤ (runFront c push s t).field + push := by
  intro t
  induction t with
  | zero => simpa [runFront] using h
  | succ t ih => exact bound_within_one_push c push _ ih

/-- The bound advances at most `c · t + push` over `t` ticks: at the carriers' speed, plus one push. The owner's "slows down" is a slowing to
    the carriers' speed. -/
theorem bound_speed_le_carriers (c push : Nat) (s : Front) (h : s.bound ≤ s.field + push) (t : Nat) :
    (runFront c push s t).bound ≤ s.field + c * t + push := by
  have h1 := bound_run_within_one_push c push s h t
  have h2 := field_run_le c push s t
  omega

/-- While the information pushes and the carriers move, the field reaches the bound within the gap's worth of ticks and the bound moves. -/
theorem bound_reached (c push : Nat) (hc : 1 ≤ c) (hp : 1 ≤ push) :
    ∀ g, ∀ s : Front, s.bound - s.field ≤ g → ∃ t', 0 < t' ∧ s.bound < (runFront c push s t').bound := by
  intro g
  induction g with
  | zero =>
    intro s hs
    refine ⟨1, Nat.zero_lt_one, ?_⟩
    show s.bound < (stepFront c push s).bound
    rw [stepFront_bound, stepFront_field]
    have h1 : ¬ (s.field + c ≤ s.bound) := by omega
    simp [h1]
    omega
  | succ g ih =>
    intro s hs
    by_cases h1 : s.field + c ≤ s.bound
    · by_cases h2 : s.field + c = s.bound
      · refine ⟨1, Nat.zero_lt_one, ?_⟩
        show s.bound < (stepFront c push s).bound
        rw [stepFront_bound, stepFront_field]
        simp [h2]
        omega
      · have hf : (stepFront c push s).field = s.field + c := by rw [stepFront_field]; simp [h1]
        have hb : (stepFront c push s).bound = s.bound := by rw [stepFront_bound, hf]; simp [h2]
        have hg : (stepFront c push s).bound - (stepFront c push s).field ≤ g := by rw [hf, hb]; omega
        obtain ⟨t', ht', hlt⟩ := ih (stepFront c push s) hg
        refine ⟨t' + 1, Nat.succ_pos _, ?_⟩
        rw [runFront_shift, ← hb]
        exact hlt
    · refine ⟨1, Nat.zero_lt_one, ?_⟩
      show s.bound < (stepFront c push s).bound
      rw [stepFront_bound, stepFront_field]
      simp [h1]
      omega

/-- The bound never stops: after any tick there is a later tick at which it is further out. Without a capacity the growth never ends; it
    only slows to the carriers' speed. -/
theorem bound_never_stops (c push : Nat) (hc : 1 ≤ c) (hp : 1 ≤ push) (s : Front) :
    ∀ t, ∃ t', t < t' ∧ (runFront c push s t).bound < (runFront c push s t').bound := by
  intro t
  obtain ⟨u, hu, hlt⟩ := bound_reached c push hc hp _ (runFront c push s t) (Nat.le_refl _)
  refine ⟨t + u, by omega, ?_⟩
  rw [runFront_add]
  exact hlt

/-! ## 2. The capacity -/

/-- The extension with a capacity: the push acts only while the bound stays within `K`, the horizon's information capacity. -/
def stepCapped (c push K : Nat) (s : Front) : Front :=
  let field' := if s.field + c ≤ s.bound then s.field + c else s.bound
  { bound := if field' = s.bound ∧ s.bound + push ≤ K then s.bound + push else s.bound, field := field' }

theorem stepCapped_bound (c push K : Nat) (s : Front) :
    (stepCapped c push K s).bound =
      if (stepCapped c push K s).field = s.bound ∧ s.bound + push ≤ K then s.bound + push else s.bound := rfl

def runCapped (c push K : Nat) (s : Front) : Nat → Front
  | 0 => s
  | t + 1 => stepCapped c push K (runCapped c push K s t)

/-- With a capacity the bound never exceeds it, from any start within it. -/
theorem capacity_stops_the_bound (c push K : Nat) (s : Front) (h : s.bound ≤ K) : ∀ t, (runCapped c push K s t).bound ≤ K := by
  intro t
  induction t with
  | zero => simpa [runCapped] using h
  | succ t ih =>
    show (stepCapped c push K (runCapped c push K s t)).bound ≤ K
    rw [stepCapped_bound]
    split
    · rename_i hh
      exact hh.2
    · exact ih

/-- Once the next push would exceed the capacity, the bound no longer moves: the growth ends. -/
theorem growth_ends_at_capacity (c push K : Nat) (s : Front) (h : K < s.bound + push) : (stepCapped c push K s).bound = s.bound := by
  rw [stepCapped_bound]
  split
  · rename_i hh
    exact absurd hh.2 (by omega)
  · rfl

end Dmp
