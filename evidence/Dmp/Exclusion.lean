/-
PR12 (proposal): exclusion and inclusion by voting share.

This file states the PROPOSED wording of constitution T39, drafted from the owner's rule of 2026-10-26 21:42Z and 21:43Z in the draft
pull request "Constitution T39: exclusion and inclusion by voting share" on the dmp repository. Gravity vendors DMP by pin
(../vendor/dmp, DMP 0.9.6), and a pin is never moved by a proposal: the vendored DMP does not contain T39 yet, and nothing here is DMP
0.9.6 text. The file is restated against the pinned DMP and the pin moved with tools/pin.sh only when the owner approves the dmp pull
request.

The owner's words (2026-10-26 21:42Z): "The simple majority of one side of a DoT, but never while being the simple majority of the DoT,
in which case it must logically work to restore balance above all, can initiate exclusion. An inclusion must be approved by two sides
DoT, who can, as they would have to restore balance above all, also not vote with a simple majority which also holds the total simple
majority." The measure (21:43Z): "It is about is percentage of the voting share, whichever value that happens to be."

Model. Shares are natural numbers, whole weights as the minting configures them (T4; the default gives every White Key holder one equal
share, so a share is a seat, T5). A percentage with fractions is this model scaled: every comparison below is homogeneous, so
multiplying all shares by a common factor changes nothing. "More than half" is `2 * c > s`, "at most half" is `2 * c ≤ s + t`, so no
division is needed and a tie sits on the allowed side: exactly half of the DoT is not a simple majority (question Q1 of the brief,
drafted as the reading states it — only "more than half" is barred).

Re-reading Standing.lean (T24) against this rule: `loosening_needs_both` keeps its truth, and `loosening_still_needs_both` below is its
share form — an inclusion still needs both sides; `one_witness_never_loosens`, `one_witness_tightens` and `self_correction_on_one` keep
their truth for a witness's own standing levels (T24's first sentence), which are not voting shares; Standing.lean states no fixed key
count, so no theorem there is touched by the replacement of the fixed "two".

Prior art this file stands on: the quorum reading of Layer.lean (Malkhi and Reiter, "Byzantine Quorum Systems", Distributed Computing
11, 1998; credited in docs/acknowledgements.md) is the shape behind the cap — a qualifying coalition must stay within half of the whole,
the same no-majority-across-the-pair bound that keeps two disjoint approvals from spanning the DoT. Nothing here is invented beyond
that reading and the owner's rule.

What this file proves:

1. The two predicates of T39: when a coalition of one side may initiate an exclusion, and when both sides approve an inclusion (the
   existential form of the approval is the owner's decision of 2026-10-26, question Q2 of the brief: an approval stands when the
   smallest approving coalition within the yes votes qualifies).
2. A coalition holding the whole-DoT majority never initiates an exclusion; exactly half does not count as holding it.
3. The worked examples of the brief, proved and not assumed: equal shares (three of one per side, T = 6: any two voters of one side),
   a 70/30 split (a 40 share on the 70-side initiates, all 70 is barred), one dominant voter (60 against 10 on its own side: nobody on
   that side initiates), and the general reason — a minority side's coalitions can never reach the cap.
4. An inclusion needs both sides, more agreement never voids an approval (Q2), and one voter alone never carries an approval — so the
   fixed "two signatures from two different keys" of IM version 1 stays a lower bound under the share rule.
5. Equal shares count shares as seat counts (T5's numbers), and the floors of T3a: at two seats per side an inclusion needs all four,
   and after a loss to 2 + 1 none can pass until the stand-in refills the seat (T6 keeps a stand-in per seat, so the blocked state is
   not where inclusions are asked).
-/

import Dmp.Standing

namespace Dmp

/-! ## The sides and their shares -/

/-- The two sides (the halves, the witnesses) of a Duality of Trust. -/
inductive Side | A | B

/-- The other side of the pair. -/
def Side.other : Side → Side
  | .A => .B
  | .B => .A

theorem Side.other_other (h : Side) : h.other.other = h := by
  cases h <;> rfl

/-- The voting shares of a DoT: each side's total share, whatever the configuration gives (T4). The default is one equal share per
    White Key holder, so a share is a seat (T5). -/
structure Shares where
  sideA : Nat
  sideB : Nat

/-- A side's total share. -/
def Shares.side (v : Shares) : Side → Nat
  | .A => v.sideA
  | .B => v.sideB

/-- The whole DoT's total share: both sides. -/
def Shares.total (v : Shares) : Nat := v.sideA + v.sideB

/-! ## The two predicates of T39 (proposed) -/

/-- T39 (proposed), exclusion: a coalition of one side with share `c` may initiate an exclusion when it holds more than half of its
    side's total share and at most half of the whole DoT's. A coalition that holds the total majority works to restore balance above
    all and does not extend its reach. Exactly half of the DoT is not a simple majority and stays allowed (Q1). -/
def canInitiateExclusion (v : Shares) (h : Side) (c : Nat) : Prop :=
  2 * c > v.side h ∧ 2 * c ≤ v.side h + v.side h.other

/-- T39 (proposed), one side's approval of an inclusion: the side's yes votes carry some qualifying coalition — more than half of the
    side's total share, at most half of the DoT's. The existential is the owner's decision of 2026-10-26 (Q2): the cap is on the
    smallest approving coalition within the yes votes, so extra yes votes never void an approval. -/
def sideApproves (v : Shares) (h : Side) (yes : Nat) : Prop :=
  ∃ c, c ≤ yes ∧ 2 * c > v.side h ∧ 2 * c ≤ v.side h + v.side h.other

/-- T39 (proposed): an inclusion is approved when both sides approve. -/
def inclusionApproved (v : Shares) (yesA yesB : Nat) : Prop :=
  sideApproves v .A yesA ∧ sideApproves v .B yesB

/-! ## The rule and its edge -/

/-- A coalition holding the whole-DoT majority never initiates an exclusion: it must work to restore balance above all. -/
theorem total_majority_never_initiates (v : Shares) (h : Side) (c : Nat) (hc : 2 * c > v.side h + v.side h.other) :
    ¬ canInitiateExclusion v h c := by
  unfold canInitiateExclusion
  omega

/-- Exactly half of the DoT is not a simple majority: a side majority holding exactly half may still initiate (Q1, drafted as the
    reading states it). -/
theorem exactly_half_still_initiates (v : Shares) (h : Side) (c : Nat)
    (hmaj : 2 * c > v.side h) (hcap : 2 * c = v.side h + v.side h.other) :
    canInitiateExclusion v h c :=
  ⟨hmaj, by omega⟩

/-- A side majority at most half of the DoT does initiate an exclusion: the rule is satisfiable exactly as the owner stated it. -/
theorem side_majority_initiates (v : Shares) (h : Side) (c : Nat)
    (hmaj : 2 * c > v.side h) (hcap : 2 * c ≤ v.side h + v.side h.other) :
    canInitiateExclusion v h c :=
  ⟨hmaj, hcap⟩

/-- On the minority side no coalition can reach the cap: every coalition of the smaller side that is a side majority automatically
    stays within half of the DoT (the brief's reason for the 70/30 and dominant-voter rows). -/
theorem minority_side_coalitions_never_reach_the_cap (v : Shares) (c : Nat)
    (hle : v.side .B ≤ v.side .A) (hc : c ≤ v.side .B) (hmaj : 2 * c > v.side .B) :
    canInitiateExclusion v .B c := by
  simp only [canInitiateExclusion, Shares.side, Side.other] at hle hc ⊢
  exact ⟨hmaj, by omega⟩

/-! ## Inclusion -/

/-- T24's direction in shares: an inclusion is a loosening and needs both sides (Standing.lean's `loosening_needs_both`, re-read
    against T39). -/
theorem loosening_still_needs_both (v : Shares) (ya yb : Nat) (hap : inclusionApproved v ya yb) :
    sideApproves v .A ya ∧ sideApproves v .B yb := hap

/-- With one side's approval missing there is no inclusion. -/
theorem inclusion_without_both_is_none (v : Shares) (ya yb : Nat) (h : ¬ sideApproves v .B yb) :
    ¬ inclusionApproved v ya yb := fun hin => h hin.2

/-- Q2, the owner's decision of 2026-10-26: more agreement never voids an approval. The cap is on the smallest approving coalition
    within the yes votes, so extra yes votes cannot turn an approval invalid. -/
theorem more_agreement_never_voids (v : Shares) (h : Side) (yes extra : Nat) (hap : sideApproves v h yes) :
    sideApproves v h (yes + extra) := by
  unfold sideApproves at hap ⊢
  obtain ⟨c, hc1, hc2, hc3⟩ := hap
  exact ⟨c, by omega, hc2, hc3⟩

/-- An approving side always carries at least one voter's share: a share of zero is never more than half of a side. -/
theorem approval_has_a_voter (v : Shares) (h : Side) (yes : Nat) (hap : sideApproves v h yes) :
    ∃ c, 0 < c ∧ c ≤ yes := by
  unfold sideApproves at hap
  obtain ⟨c, hc1, hc2, _⟩ := hap
  exact ⟨c, by omega, hc1⟩

/-- An inclusion is carried by voters of both sides, so never by one key alone: the fixed "two signatures from two different keys" of
    IM version 1 (04-im.md, "Orders and the White Key") stays a lower bound under the share rule. -/
theorem inclusion_carries_two_sides (v : Shares) (ya yb : Nat) (hap : inclusionApproved v ya yb) :
    (∃ ca, 0 < ca ∧ ca ≤ ya) ∧ (∃ cb, 0 < cb ∧ cb ≤ yb) :=
  ⟨approval_has_a_voter v .A ya hap.1, approval_has_a_voter v .B yb hap.2⟩

/-! ## The worked examples of the brief -/

/-- **Equal shares.** Three voters of 1 on each side (T = 6): any two voters of one side may initiate an exclusion — 2 > 1.5 and
    2 ≤ 3. -/
theorem equal_shares_two_voters_initiate : canInitiateExclusion ⟨3, 3⟩ .A 2 := by
  simp [canInitiateExclusion, Shares.side, Side.other] <;> omega

/-- The same on the other side: the rule does not prefer a half. -/
theorem equal_shares_two_voters_initiate_other_side : canInitiateExclusion ⟨3, 3⟩ .B 2 := by
  simp [canInitiateExclusion, Shares.side, Side.other] <;> omega

/-- Equal shares count shares as seat counts: a coalition of `n` equal seats holds share `n`, which is how the rule gives back T5's
    numbers at the default. -/
theorem equal_shares_are_seat_counts (n : Nat) : List.sum (List.replicate n 1) = n := by
  simp

/-- **A 70/30 split.** On the 70-side a coalition of 40 initiates: above 35 (the side's half) and at most 50 (the DoT's half). -/
theorem seventy_thirty_forty_initiates : canInitiateExclusion ⟨70, 30⟩ .A 40 := by
  simp [canInitiateExclusion, Shares.side, Side.other] <;> omega

/-- All of the 70-side is the total majority (70 > 50) and is barred: it must restore balance above all. -/
theorem seventy_thirty_whole_side_barred : ¬ canInitiateExclusion ⟨70, 30⟩ .A 70 := by
  simp [canInitiateExclusion, Shares.side, Side.other] <;> omega

/-- On the 30-side a coalition of 20 initiates (the instance of `minority_side_coalitions_never_reach_the_cap`). -/
theorem seventy_thirty_twenty_initiates : canInitiateExclusion ⟨70, 30⟩ .B 20 := by
  simp [canInitiateExclusion, Shares.side, Side.other] <;> omega

/-- **One dominant voter.** Side A holds one voter of 60 and one of 10, side B totals 30 (T = 100): nobody on side A may initiate.
    The voter of 60 holds the total majority (60 > 50) and must restore balance above all. -/
theorem dominant_voter_barred : ¬ canInitiateExclusion ⟨70, 30⟩ .A 60 := by
  simp [canInitiateExclusion, Shares.side, Side.other] <;> omega

/-- The voter of 10 is not a majority of its side either (10 ≤ 35), and no coalition of the two (70) escapes the cap. -/
theorem dominant_side_small_voter_barred : ¬ canInitiateExclusion ⟨70, 30⟩ .A 10 := by
  simp [canInitiateExclusion, Shares.side, Side.other] <;> omega

theorem dominant_side_whole_side_barred : ¬ canInitiateExclusion ⟨70, 30⟩ .A 70 :=
  seventy_thirty_whole_side_barred

/-- On side B any coalition above 15 initiates — the instance of the minority-side theorem. -/
theorem dominant_side_other_side_qualifies : canInitiateExclusion ⟨70, 30⟩ .B 20 := by
  simp [canInitiateExclusion, Shares.side, Side.other] <;> omega

/-! ## The floors (T3a, question Q6) -/

/-- At the floor, two seats of 1 per side (T = 4): the inclusion is approved by all four seats, each side's pair staying at exactly
    half of the DoT, which the cap allows. -/
theorem floor_inclusion_needs_all_four : inclusionApproved ⟨2, 2⟩ 2 2 := by
  simp only [inclusionApproved, sideApproves, Shares.side, Side.other]
  exact ⟨⟨2, by omega, by omega⟩, ⟨2, by omega, by omega⟩⟩

/-- One seat of the floor pair is not an approval: a single voter is never a side majority at equal shares with two seats per side
    (the seat-count reading of R1Mass.lean's "one seat is never a seat majority once there are two seats"). -/
theorem floor_one_seat_never_approves (v : Shares) (h : Side) (yes : Nat)
    (hfloor : v.side h = 2) (hequal : yes ≤ 1) : ¬ sideApproves v h yes := by
  unfold sideApproves
  rintro ⟨c, hc1, hc2, -⟩
  omega

/-- After a single loss at the floor one side is down to its last seat (2 + 1, T = 3): the surviving pair holds the total majority
    (2 > 1.5) and no share of its sits between its half and the cap, so no approval of that side exists and no inclusion can pass.
    The state does not last: T6 takes the stand-in to the empty seat at once, and T3a keeps one onboarded stand-in per seat, so the
    restore-balance work of T39 is the stand-in's, not a vote's. -/
theorem floor_after_a_loss_blocks_inclusion (ya yb : Nat) : ¬ inclusionApproved ⟨2, 1⟩ ya yb := by
  simp only [inclusionApproved, sideApproves, Shares.side, Side.other]
  rintro ⟨⟨c, -, hc2, hc3⟩, -⟩
  omega

end Dmp
