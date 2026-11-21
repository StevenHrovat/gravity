import Dmp.Field
import Dmp.Recipe

/-!
# The mass gap, in DMP's own words

The owner, 2026-11-20: an explanation and proof "for the mass gap in the DMP system", the brand new existence proof of Yang-Mills as
the occasion (`docs/mass-gap/README.md`). In physics, a theory has a **mass gap** when every excitation of its vacuum costs at least a
fixed positive amount `Δ` of energy, however large the system and however fine the grid it is computed on. DMP has its own words for
the three ingredients, all in T32 (the trust field): a **mass** (one plus the members that derive through a member), an **energy** (the
potential, mass times shortfall summed over members, zero exactly in the balanced state, the vacuum) and a **grid** (freshness, counted
in thousandths, the resolution of the clock). T3a adds the **floor**: the smallest cluster that can stand on its own.

What this file proves about DMP, and only about DMP:

1. Mass is a count, and it is never below one (T32).
2. The potential has a gap of one quantum, **uniform in the size of the boundary**: any imbalance anywhere costs at least one quantum,
   and for every size there is a state costing exactly one (the gap is tight and the same in every volume).
3. **Refinement closes the potential's gap**: on a clock of resolution `R` the quantum is `1/R` of a whole standing, so for every bound
   there is an imbalanced state lighter than it. In the continuum limit of its clock, DMP's energy is **gapless**, like light; only
   the counted mass keeps its gap, because a count does not refine. This is the shape of the physics problem: on a grid a gap is
   free, and the whole question is whether it survives the grid being made finer.
4. The intensive readout (the temperature) has no uniform gap: one stale quantum in a large boundary reads as almost nothing.
5. The floor: the smallest cluster that still answers after any single loss, by a majority that one wrong node cannot form, has three
   nodes (T3a, derived, not configured), and a well-formed recipe never holds a smaller singularity.
6. The stability margin `μ` (Gravity's constant) is a gap in time: with verification faster than ageing every staleness returns to
   zero within a bounded number of rounds, per member and so whatever the boundary's size; with verification only as fast as ageing
   (`μ = 0`) a staleness never returns. That is the dynamical meaning of a gap (the rate of return to balance).

Every statement is about DMP's model. None of it is a statement about Yang-Mills theory; how far each one transfers, and the test
every transfer has to pass, is `docs/mass-gap/README.md` and `Dmp/Gauge.lean`.
-/

namespace Dmp

/-! ## 1. Mass is a count, never below one -/

/-- T32: a member's mass is one plus the number of members that derive through it. -/
def memberMass (derived : Nat) : Nat := 1 + derived

theorem mg_mass_at_least_one (derived : Nat) : 1 ≤ memberMass derived := by
  unfold memberMass; omega

/-- Held standings whose parts are members: each carries mass at least one (T32). -/
def AllMembers (l : List Held) : Prop := ∀ x ∈ l, 1 ≤ x.mass

/-! ## 2. The potential's gap: one quantum, uniform in the size of the boundary -/

/-- One stale member alone costs at least its mass times its shortfall, whatever else the boundary holds. -/
theorem mg_member_term_le_phi (l : List Held) (x : Held) (hx : x ∈ l) : x.mass * (1000 - x.fresh) ≤ phi l := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons h hs ih =>
    simp only [phi]
    cases List.mem_cons.mp hx with
    | inl he => subst he; omega
    | inr ht => have := ih ht; omega

/-- **The gap.** In a boundary of members, any member short of full freshness makes the potential at least one quantum, wherever it
    sits and however many members the boundary holds: the bound does not mention the boundary's size. -/
theorem mg_gap_uniform (l : List Held) (hm : AllMembers l) (hs : ∃ x ∈ l, x.fresh < 1000) : 1 ≤ phi l := by
  obtain ⟨x, hx, hf⟩ := hs
  have h1 := mg_member_term_le_phi l x hx
  have h2 : 1 ≤ x.mass := hm x hx
  have h3 : 1 ≤ 1000 - x.fresh := by omega
  have h4 : 1 * 1 ≤ x.mass * (1000 - x.fresh) := Nat.mul_le_mul h2 h3
  omega

/-- The vacuum: in a boundary of members whose freshness never exceeds full, the potential is zero exactly when every standing is
    fully fresh (the balanced state, `Φ = 0` of T32). -/
theorem mg_vacuum_iff (l : List Held) (hm : AllMembers l) (hle : ∀ x ∈ l, x.fresh ≤ 1000) :
    phi l = 0 ↔ ∀ x ∈ l, x.fresh = 1000 := by
  constructor
  · intro h0 x hx
    have := hle x hx
    apply Classical.byContradiction
    intro hne
    have := mg_gap_uniform l hm ⟨x, hx, by omega⟩
    omega
  · exact phi_zero_of_all_fresh l

/-- A balanced boundary of `n` members, each of mass one. -/
def balanced (n : Nat) : List Held := List.replicate n { mass := 1, fresh := 1000 }

theorem phi_balanced (n : Nat) : phi (balanced n) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [balanced, List.replicate_succ, phi] at *; omega

/-- **The gap is tight, and the same in every volume**: for every size there is a boundary of members, imbalanced by one quantum in
    one member, whose potential is exactly one. -/
theorem mg_gap_tight (n : Nat) : ∃ l : List Held, l.length = n + 1 ∧ AllMembers l ∧ (∃ x ∈ l, x.fresh < 1000) ∧ phi l = 1 := by
  refine ⟨{ mass := 1, fresh := 999 } :: balanced n, ?_, ?_, ⟨_, List.mem_cons_self, by decide⟩, ?_⟩
  · simp [balanced]
  · intro x hx
    cases List.mem_cons.mp hx with
    | inl h => subst h; decide
    | inr h => simp [balanced, List.mem_replicate] at h; rw [h.2]; exact Nat.le_refl _
  · simp only [phi, phi_balanced]

/-! ## 3. Refinement closes the potential's gap -/

/-- The potential on a clock of resolution `R`: freshness counted in `R`-ths, shortfall `R - fresh`. Thousandths are `R = 1000`. -/
def phiAt (R : Nat) : List Held → Nat
  | [] => 0
  | h :: hs => h.mass * (R - h.fresh) + phiAt R hs

theorem phiAt_thousandths (l : List Held) : phiAt 1000 l = phi l := by
  induction l with
  | nil => rfl
  | cons h hs ih => simp only [phiAt, phi, ih]

/-- On every clock the gap is one quantum (the counting argument of §2 at resolution `R`). -/
theorem mg_gap_at (R : Nat) (l : List Held) (hm : AllMembers l) (hs : ∃ x ∈ l, x.fresh < R) : 1 ≤ phiAt R l := by
  obtain ⟨x, hx, hf⟩ := hs
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons h hs ih =>
    simp only [phiAt]
    cases List.mem_cons.mp hx with
    | inl he =>
      subst he
      have h2 : 1 ≤ x.mass := hm x List.mem_cons_self
      have h4 : 1 * 1 ≤ x.mass * (R - x.fresh) := Nat.mul_le_mul h2 (by omega)
      omega
    | inr ht =>
      have := ih (fun y hy => hm y (List.mem_cons_of_mem _ hy)) ht
      omega

/-- **But the quantum is `1/R` of a whole standing.** For every bound `1/N` there is a clock and an imbalanced boundary of members
    whose potential, measured in whole standings (`phiAt R l / R`), is below `1/N`. In the continuum limit of its clock DMP's energy has
    no gap: the gap of §2 is an artefact of counting in thousandths. -/
theorem mg_refinement_closes_potential_gap (N : Nat) :
    ∃ R l, AllMembers l ∧ (∃ x ∈ l, x.fresh < R) ∧ phiAt R l * N < R := by
  refine ⟨N + 1, [{ mass := 1, fresh := N }], ?_, ⟨_, List.mem_cons_self, by simp⟩, ?_⟩
  · intro x hx; simp at hx; rw [hx]; exact Nat.le_refl _
  · simp [phiAt]

/-- **The counted mass keeps its gap under every refinement**: whatever the clock, the lightest member still weighs one. Mass is not
    measured on the clock; it is a count of the grant graph. -/
theorem mg_mass_gap_survives_refinement (R : Nat) (l : List Held) (hm : AllMembers l) (hs : ∃ x ∈ l, x.fresh < R) :
    ∃ x ∈ l, x.fresh < R ∧ 1 ≤ x.mass := by
  obtain ⟨x, hx, hf⟩ := hs
  exact ⟨x, hx, hf, hm x hx⟩

/-! ## 4. The temperature has no uniform gap -/

/-- The total mass of a boundary. -/
def massSum : List Held → Nat
  | [] => 0
  | h :: hs => h.mass + massSum hs

theorem massSum_balanced (n : Nat) : massSum (balanced n) = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [balanced, List.replicate_succ, massSum] at *; omega

/-- The temperature (T32's one-number readout, mass-weighted staleness, `phi / (1000 · massSum)`) of a boundary with one stale quantum
    falls below any bound `1/N` once the boundary is large enough: the average forgets a single imbalance. -/
theorem mg_temperature_no_uniform_gap (N : Nat) :
    ∃ l, AllMembers l ∧ (∃ x ∈ l, x.fresh < 1000) ∧ phi l * N < 1000 * massSum l := by
  refine ⟨{ mass := 1, fresh := 999 } :: balanced N, ?_, ⟨_, List.mem_cons_self, by decide⟩, ?_⟩
  · intro x hx
    cases List.mem_cons.mp hx with
    | inl h => subst h; decide
    | inr h => simp [balanced, List.mem_replicate] at h; rw [h.2]; exact Nat.le_refl _
  · simp only [phi, massSum, phi_balanced, massSum_balanced]; omega

/-! ## 5. The floor: the smallest cluster that stands on its own -/

/-- A majority of `n` nodes: more than half. -/
def majority (n : Nat) : Nat := n / 2 + 1

/-- T3a's premise: a half answers by a majority of its nodes. It must still answer after any single loss, and one wrong node must not
    be able to speak for it. -/
def standsAlone (n : Nat) : Prop := majority n ≤ n - 1 ∧ 1 < majority n

/-- **The floor is three, derived**: a cluster stands alone exactly when it has at least three nodes. -/
theorem mg_cluster_floor (n : Nat) : standsAlone n ↔ 3 ≤ n := by
  unfold standsAlone majority; omega

/-- No smaller cluster stands: one node and two nodes fall over (the owner's notes on dmp#25: "Meson: two node cluster, so no
    failover"). -/
theorem mg_below_floor_falls (n : Nat) (h : n < 3) : ¬ standsAlone n := by
  rw [mg_cluster_floor]; omega

/-- A well-formed recipe never holds a singularity below the floor. -/
theorem mg_recipe_respects_floor (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (i : Nat) (hi : i < r.n)
    (hk : (r.line i).kind = .singularity) : standsAlone (r.line i).cluster :=
  (mg_cluster_floor _).mpr ((hwf i hi).2.1 hk)

/-! ## 6. The stability margin is a gap in time -/

/-- One verification round for one member's staleness (in quanta): ageing adds `age`, the witnesses' verification removes `verify`. -/
def round (age verify s : Nat) : Nat := s + age - verify

/-- `n` rounds. -/
def rounds (age verify : Nat) : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => rounds age verify n (round age verify s)

/-- With verification faster than ageing (`μ > 0`), every round removes at least the margin `verify - age`: after `n` rounds a
    staleness `s` is at most `s - n · margin`. -/
theorem mg_rounds_le (age verify : Nat) (h : age < verify) (n s : Nat) :
    rounds age verify n s ≤ s - n * (verify - age) := by
  induction n generalizing s with
  | zero => simp [rounds]
  | succ k ih =>
    simp only [rounds]
    have h1 := ih (round age verify s)
    have h2 : round age verify s ≤ s - (verify - age) := by unfold round; omega
    rw [Nat.succ_mul]
    generalize k * (verify - age) = t at *
    omega

/-- **Gap in time.** With `μ > 0` every staleness `s` is back to zero after `s` rounds at the latest (after `s / margin` rounds,
    rounded up, by `mg_rounds_le`); the bound is per member, so it holds whatever the boundary's size. -/
theorem mg_returns_to_balance (age verify s : Nat) (h : age < verify) : rounds age verify s s = 0 := by
  have h1 := mg_rounds_le age verify h s s
  have h2 : s * 1 ≤ s * (verify - age) := Nat.mul_le_mul_left s (by omega)
  generalize s * (verify - age) = t at *
  omega

/-- **No gap at `μ = 0`.** With verification exactly as fast as ageing a staleness never returns: the marginal case, the analogue of a
    massless field. -/
theorem mg_marginal_never_returns (age s n : Nat) : rounds age age n s = s := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih => simp only [rounds, round]; rw [show s + age - age = s by omega]; exact ih s

end Dmp
