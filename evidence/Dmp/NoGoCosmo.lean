/-
The owner's cosmological reading (2026-10-27): DMP's stable configuration is an information black hole, a boundary that never moves and
leaks only what it cannot contain; our universe has no perfect part arrangement, so its boundary expands while the information inside
cannot catch up; the leftover expansion over what gravity holds back should be the ratio of dark energy to dark matter, and the universe,
existing and stable, must be consistent with the two-axiom system.

Instantiated in DMP's objects (docs/qg-attempt.md section 4.6): the perfect arrangement is a declared boundary the budget fully holds
(potential zero, `Field.phi_zero_of_all_fresh`; nothing leaves but counts, T24); the imperfect one is a declaration of N standings beyond the
budget r·W, of which one is never refreshed (`Physics.Schedule.some_standing_lapses`); "what gravity holds back" is the budget; the
"leftover expansion" is N − r·W; the ratio of the two is the owner's dark energy over dark matter.

What the kernel then decides:

1. **Every ratio is a configuration.** For every value q there is a declaration whose leftover over held is q (`every_ratio_is_a_configuration`);
   today's Ω_Λ/Ω_m ≈ 2.17 is attained (`todays_ratio_is_attained`), and so is 0 and so is a million. The axioms fix the budget's role and
   nothing about N, which both halves fix at the minting (T9): a system consistent with every ratio predicts none.
2. **The scaling is an input.** The leftover grows exactly as the declaration grows (`leftover_grows_with_declaration`): declare as the
   volume and the ratio scales as the volume, which is ΛCDM's a³; declare otherwise and it scales otherwise. The exponent is put in, not out.
3. **The branching gap is not a number.** A tree of fan-out 3 against the binary optimum has a node ratio that changes with depth
   (`branching_ratio_not_constant`: 3/2 at depth 1, 9/4 at depth 2), so "fewer than three branches per part" yields no constant ratio.
4. **Existence is not stability, and instability is consistent with the axioms.** A declaration beyond the budget exists under the axioms as
   modelled and has a standing that lapses (`unstable_configuration_exists`): the axioms allow the unstable configuration, so "it exists,
   therefore it is stable, therefore it is consistent" proves nothing in either direction. T26 states the stability condition separately
   (the witnesses verify at least as often as standings age), and the owner's universe, by his own description, violates it.

Nothing here is invented: 1 and 2 are the cosmological-constant problem in DMP's clothing (Λ's value and its scaling are inputs in ΛCDM
too, Weinberg 1989); 3 is arithmetic; 4 is the definition of stability in T26.

Two later claims of the same day, tried in the same objects (sections 2 and 3 below):

**"By the axioms the expansion should slow down as the information that drives it cannot catch up. Which it does, to my knowledge."**
The expansion is the growth of the leftover over the windows. The axioms fix no history of it: every history, slowing, constant or
accelerating, is a declaration history (`every_history_is_a_configuration`). What the axioms do fix is a ceiling: a minting is an act the
pair serves (T2, the words), so the standings minted in a window never exceed the budget left after the live checks (`growth_capped_by_budget`), a
constant cap, lowered by nothing. "The information cannot catch up" is true in DMP and is the capacity bound: at most r·W standings are
live, the rest lapse; but a lapse acts on nothing (T7), so it does not slow the declaration. And the observation is the other way: the
expansion of the universe accelerates today (Riess et al. 1998, Perlmutter et al. 1999; with Planck 2018's Ω_m = 0.315 and Ω_Λ = 0.685 the
deceleration parameter q₀ = Ω_m/2 − Ω_Λ is negative, `todays_expansion_accelerates`), after decelerating until redshift about 0.63
(`acceleration_began_at_redshift_point_six`). The Hubble rate H falls toward a constant in every such model; the scale factor's growth
accelerates, and that is what "slows down" would have to deny.

**"Also explains quantum tunneling: the vector field decided, reordered its part."** A part moves only by a reorganisation both witnesses
signed (`R1Lens.lean`), and the layout law computes one layout per signed state (`ms_one_layout`), so "the field decided" names a
decided, unique move. A part moves exactly when both signed and the epoch is ahead (`moved_iff_signed_and_forward`); the outcome is stay
or move and nothing between (`move_is_all_or_nothing`); whether it moves is blind to how far (`moving_is_blind_to_distance`). Tunnelling
(Gamow 1928; Gurney and Condon 1928) is a transmission probability strictly between zero and one that falls with the barrier's width, through
a region the particle cannot classically be in. DMP has no such region: a refused move is not made at all (`ln_one_witness_never_moves`,
`ms_refused_never_moves`), a made move was not refused, and every request is recorded (`run_records_all`). A decided move through an open
gate is not a crossing of a closed one. The CHSH bound of `NoGo.lean` stands over all of it.
-/
import Dmp.Physics
import Dmp.R1Lens

namespace Dmp

/-- The leftover: declared standings beyond what the budget holds. -/
def leftover (N budget : Nat) : Nat := N - budget

/-- A declaration attains the ratio q (in thousandths) when its leftover times 1000 is q times what is held. -/
def attainsRatio (N budget q : Nat) : Prop := 0 < budget ∧ leftover N budget * 1000 = q * budget

/-- Every ratio is attained by some declaration over some budget: the axioms fix none. -/
theorem every_ratio_is_a_configuration (q : Nat) : ∃ N budget, attainsRatio N budget q :=
  ⟨1000 + q, 1000, by decide, by simp [leftover]⟩

/-- Today's ratio of dark energy to all matter (Planck 2018: 0.685 over 0.315, about 2.17) is attained, like every other. -/
theorem todays_ratio_is_attained : ∃ N budget, attainsRatio N budget 2170 := every_ratio_is_a_configuration 2170

/-- So is the ratio to dark matter alone (0.685 over about 0.265, about 2.6). -/
theorem todays_ratio_to_dark_matter_is_attained : ∃ N budget, attainsRatio N budget 2590 := every_ratio_is_a_configuration 2590

theorem zero_ratio_is_attained : ∃ N budget, attainsRatio N budget 0 := every_ratio_is_a_configuration 0

theorem any_ratio_is_attained : ∃ N budget, attainsRatio N budget 1000000 := every_ratio_is_a_configuration 1000000

/-- The leftover grows exactly as the declaration grows: its scaling in time is the declaration's, an input. -/
theorem leftover_grows_with_declaration (N N' budget : Nat) (h : N ≤ N') : leftover N budget ≤ leftover N' budget :=
  Nat.sub_le_sub_right h budget

/-- Nodes at depth D of a tree of fan-out b. The ratio of a 3-tree to the binary optimum changes with depth: no constant comes out. -/
theorem branching_ratio_not_constant : 3 ^ 1 * 2 ^ 2 ≠ 3 ^ 2 * 2 ^ 1 := by decide

/-- A declaration beyond the budget exists under the axioms as modelled (any schedule admits it) and has a standing that lapses: existence
    is not stability, and the unstable configuration is consistent with the axioms. -/
theorem unstable_configuration_exists (r W : Nat) (s : Schedule r W) : ∃ N, r * W < N ∧ ∃ i, i < N ∧ ∀ t, t < W → i ∉ refreshed (s.work t) :=
  ⟨r * W + 1, Nat.lt_succ_self _, s.some_standing_lapses (r * W + 1) (by omega)⟩

/-! ## 2. The expansion slows (the owner, 2026-10-27) -/

/-- Any history of the leftover is a configuration: for every function `f` of the windows there is a declaration history whose leftover at
    every window is `f`. A history that slows, one that accelerates and a constant one are all attained; the axioms predict none. -/
theorem every_history_is_a_configuration (budget : Nat) (f : Nat → Nat) : ∃ N : Nat → Nat, ∀ t, leftover (N t) budget = f t :=
  ⟨fun t => f t + budget, fun t => by simp [leftover]⟩

/-- The growth of the boundary in a window is served work: a minting is an act the pair performs (T2, the words), so the standings minted in a window
    never exceed the budget left after the live checks, and never the budget. The rate has a ceiling, a constant; nothing in the axioms
    lowers it over time. -/
theorem growth_capped_by_budget (r W : Nat) (s : Schedule r W) :
    s.servedUpTo W ≤ r * W - (s.touchedUpTo W).length ∧ s.servedUpTo W ≤ r * W := by
  have := s.budget_upTo W (Nat.le_refl W)
  omega

/-- The observation's arithmetic, on record for the comparison and derived from nothing here: in a flat ΛCDM universe the deceleration
    parameter is q₀ = Ω_m/2 − Ω_Λ, and with Planck 2018's Ω_m = 0.315 and Ω_Λ = 0.685 (thousandths) it is negative: today's expansion
    accelerates (Riess et al. 1998, Perlmutter et al. 1999). -/
theorem todays_expansion_accelerates : 315 < 2 * 685 := by decide

/-- Where the acceleration began: (1 + z)³ = 2Ω_Λ/Ω_m at the turn, and 2 · 685 / 315 lies between 1.632³ and 1.633³, so the expansion
    decelerated until redshift about 0.63 and has accelerated since. -/
theorem acceleration_began_at_redshift_point_six :
    1632 ^ 3 * 315 < 2 * 685 * 1000 ^ 3 ∧ 2 * 685 * 1000 ^ 3 < 1633 ^ 3 * 315 := by decide

/-! ## 3. Tunnelling (the owner, 2026-10-27) -/

/-- A part moves exactly when both witnesses signed the reorganisation and it is ahead of the part's epoch: whether it moves is a function
    of the signatures and the epoch. -/
theorem moved_iff_signed_and_forward (n : LnNode) (m : LnMove) :
    lnAccept n m ≠ n ↔ (m.sig1 = true ∧ m.sig2 = true ∧ n.epoch < m.epoch) := by
  constructor
  · intro hne
    apply Classical.byContradiction
    intro h
    apply hne
    simp [lnAccept, h]
  · intro h hEq
    rw [ln_signed_moves n m h.1 h.2.1 h.2.2] at hEq
    have he : m.epoch = n.epoch := congrArg LnNode.epoch hEq
    have := h.2.2
    omega

/-- All or nothing: a reorganisation leaves the part where it is or puts it exactly where it says. There is no third outcome, so there is no
    probability strictly between zero and one of a crossing. -/
theorem move_is_all_or_nothing (n : LnNode) (m : LnMove) :
    lnAccept n m = n ∨ lnAccept n m = { epoch := m.epoch, layer := m.layer } := by
  by_cases h : m.sig1 = true ∧ m.sig2 = true ∧ n.epoch < m.epoch
  · exact Or.inr (ln_signed_moves n m h.1 h.2.1 h.2.2)
  · exact Or.inl (by simp [lnAccept, h])

/-- Whether a part moves is blind to how far it moves: two reorganisations with the same signatures and epoch and different layers both move
    the part or neither does. A tunnelling probability falls with the barrier's width; the gate sees no width. -/
theorem moving_is_blind_to_distance (n : LnNode) (m m' : LnMove) (hs1 : m.sig1 = m'.sig1) (hs2 : m.sig2 = m'.sig2)
    (he : m.epoch = m'.epoch) : (lnAccept n m ≠ n) ↔ (lnAccept n m' ≠ n) := by
  rw [moved_iff_signed_and_forward, moved_iff_signed_and_forward, hs1, hs2, he]

end Dmp
