/-
The owner's solution (2026-10-27), after the finding that the axioms give the expansion no cause: "While the existence space is able to
grow simply by the vectors that define it being raised, the information needed to cause that expansion still has to observe the rate
limit of the scalar giving direction, while travelling through the field spanned by the boundary vector. Try to disprove that." Tried, as
asked.

Instantiated in DMP's objects (docs/qg-attempt.md section 4.9): the existence space is the set of standings inside the boundary; a vector
is raised when a standing is granted or widened; the scalar giving direction is the budget of checks per tick, whose spending order the
field fixes (T26: refresh before a lapse, heaviest and stalest first); and travelling through the field is the outward propagation of the
pair's acts, one layer per verification round (T26; the wave clock of R1Wave.lean, the rounds of R2Stable.lean).

What the kernel decides:

1. **Raising a vector is a requested act, and the axioms contain no requester.** Widening a standing needs both witnesses
   (`loosening_needs_both` in Standing.lean, T16); the gate performs nothing without a request (`no_request_no_act`), and the acts performed
   never exceed the requests made (`growth_le_requests`). So "simply by the vectors being raised" moves the cause of the expansion from the
   declaration to whatever raises the vectors, and the axioms name no such thing: what asks for growth is still configuration (T9).
2. **The rate limit is a theorem, and it forbids acceleration.** Every window has the same ceiling on its served acts
   (`growth_never_accelerates`), so the growth over k windows is at most linear in k (`growth_at_most_linear`), and a history whose
   increments keep growing exceeds the ceiling by window r·W + 1 at the latest (`accelerating_breaks_the_limit`). The owner's second half is
   right and was already proven (`growth_capped_by_budget` in NoGoCosmo.lean); taken seriously it makes the boundary coast at a constant
   rate at most, a universe with deceleration parameter zero, while the measured one is about −0.53 (`todays_expansion_accelerates`).
3. **Travelling through the field delays the growth and never adds to it.** A growth that reaches the boundary only after D rounds and is
   rate-limited after that is bounded by the same line, shifted by D (`travel_delays_never_adds`): the propagation is a delay, not a cause
   and not an acceleration. In DMP the delay is bounded too: the field has a horizon depth (`horizon_depth_bound` in NoGoVector.lean), so
   every standing is reached in a bounded number of rounds.
4. **Expansion is paid with maintenance, and the ratio never settles.** What a window keeps live is at most the budget less its growth
   (`growth_costs_maintenance`; at full growth nothing is kept live, `Schedule.extremal_keeps_nothing` in Physics.lean), and with any positive
   growth per window the leftover over the bounded live set grows without bound (`no_stationary_ratio_under_growth`): the mechanism has a
   stationary ratio only at zero growth. ΛCDM's ratio of dark energy to matter grows without bound too (as a³), so this is no contradiction
   in direction; it says that today's 2.17 is a moment in both and a prediction in neither.

Nothing here is invented: 1 is T16 and the gate; 2 and 3 are arithmetic on a bounded increment; 4 is the pigeonhole bound read over time.
-/
import Dmp.Record
import Dmp.NoGoCosmo

namespace Dmp

/-! ## 1. Raising a vector is a requested act -/

/-- No request, no act: with nothing in front of the gate the state is unchanged. Growth of the existence space is performed acts, and each
    one answers a request from outside the axioms. -/
theorem no_request_no_act (j1 j2 : Evidence → Verdict) (s : State) : run j1 j2 s [] = s := rfl

/-- The acts performed never exceed the requests made: the existence space grows by at most what it is asked to grow by. -/
theorem growth_le_requests (j1 j2 : Evidence → Verdict) (rs : List Request) :
    ∀ s : State, (run j1 j2 s rs).performed ≤ s.performed + rs.length := by
  induction rs with
  | nil => intro s; simp [run]
  | cons r rs ih =>
    intro s
    simp only [run, List.length_cons]
    have h1 := ih (step j1 j2 s r)
    have h2 : (step j1 j2 s r).performed ≤ s.performed + 1 := by
      simp only [step]
      split <;> omega
    omega

/-! ## 2. The rate limit forbids acceleration -/

/-- Every window has the same ceiling on the acts it serves: the increments of the growth are bounded by one constant, window after window. -/
theorem growth_never_accelerates (r W : Nat) (windows : Nat → Schedule r W) : ∀ k, (windows k).servedUpTo W ≤ r * W := by
  intro k
  have := (windows k).budget_upTo W (Nat.le_refl W)
  omega

/-- A growth whose increments are bounded by `c` is at most linear: after `k` windows it is within `k · c` of where it began. -/
theorem growth_at_most_linear (c : Nat) (N : Nat → Nat) (h : ∀ k, N (k + 1) ≤ N k + c) : ∀ k, N k ≤ N 0 + k * c := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have := h k
    rw [Nat.add_mul, Nat.one_mul]
    omega

/-- A history whose increments keep growing (each window grows more than the last) exceeds any fixed ceiling, and the budget's by window
    r·W + 1 at the latest. -/
theorem accelerating_breaks_the_limit (r W : Nat) (d : Nat → Nat) (h : ∀ k, d k < d (k + 1)) : ∃ k, r * W < d k := by
  have hk : ∀ k, k ≤ d k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => exact Nat.lt_of_le_of_lt ih (h k)
  exact ⟨r * W + 1, by have := hk (r * W + 1); omega⟩

/-! ## 3. Travelling through the field -/

/-- A growth that reaches the boundary only after `D` rounds (nothing changes before) and is rate-limited after that lies under the same
    line shifted by `D`: the travel through the field is a delay, never an addition and never an acceleration. -/
theorem travel_delays_never_adds (c D : Nat) (N : Nat → Nat) (h0 : ∀ k, k < D → N (k + 1) = N k) (h : ∀ k, N (k + 1) ≤ N k + c) :
    ∀ k, N k ≤ N 0 + (k - D) * c := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    cases Nat.lt_or_ge k D with
    | inl hk =>
      rw [h0 k hk]
      have e1 : k - D = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hk)
      have e2 : k + 1 - D = 0 := Nat.sub_eq_zero_of_le hk
      rw [e1] at ih
      rw [e2]
      exact ih
    | inr hk =>
      have := h k
      have e : k + 1 - D = (k - D) + 1 := by omega
      rw [e, Nat.add_mul, Nat.one_mul]
      omega

/-! ## 4. Expansion is paid with maintenance -/

/-- What a window keeps live is at most the budget less what it spent on growth. -/
theorem growth_costs_maintenance (r W : Nat) (s : Schedule r W) : (s.touchedUpTo W).length ≤ r * W - s.servedUpTo W := by
  have := s.budget_upTo W (Nat.le_refl W)
  omega

/-- With any positive growth per window, the leftover over a bounded live set grows without bound: there is no stationary ratio except at
    zero growth. -/
theorem no_stationary_ratio_under_growth (N0 g budget : Nat) (hg : 1 ≤ g) : ∀ M, ∃ k, M < leftover (N0 + k * g) budget := by
  intro M
  refine ⟨M + budget + 1, ?_⟩
  unfold leftover
  have h1 := Nat.mul_le_mul_left (M + budget + 1) hg
  rw [Nat.mul_one] at h1
  omega

end Dmp
