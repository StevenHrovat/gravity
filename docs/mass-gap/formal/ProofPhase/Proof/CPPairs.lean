/-
P vs NP, the edge: pairs of derived lines in cutting planes, what they cost and what they create (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/CP-DUALITY.md`, section 5.
-/

import ProofPhase.Proof.CPDuality

/-!
# Pairs of derived lines in cutting planes

**1. Additive pairs cross for free** (`fan_iff`, `fan_sum`, `fan_cheap`). The line
`r·x₁ + Σ_{y ∈ R} y ≥ r` is the sum of the `r` clauses `x₁ + y ≥ 1`, built by additions only. It is equivalent to their
conjunction (one line names the whole region), it is sensitive to all `r + 1` of its variables, and it is forced true
by one fixed variable and false by two. So combining lines pairwise by addition crosses a region without paying in
either certificate channel.

**2. A refutation needs a creative pair** (`creative_pair`, `refutation_needs_pair`). CP derivations are formalized
over integer lines (`CPD`: axioms, addition, positive scaling, division with rounding). If some fractional point
satisfies every axiom and every axiom has a coefficient `±1` (true for clauses, and the all-1/2 point satisfies every
clause of width at least 2, `half_clause`), then every derivation of a line that fails at the point contains a
rounding step whose premise holds at the point and whose result does not. That premise is **not a positive multiple of
a single axiom** (`round_single`: rounding a multiple of a line with a unit coefficient creates nothing). So the first
genuinely new line is a rounding of a combination of at least two lines: a creative pair. Additions and scalings
alone never leave the point's half-space (`holds_add`, `holds_scale`).

**New here:** everything in this file.
-/

namespace ProofPhase.Proof.Edge

variable {α : Type*} [DecidableEq α]

/-! ### 1. The fan: one additive line names a region -/

/-- The CP line `r·x₁ + Σ_{y ∈ R} y ≥ r`, `r = |R|`: the sum of the clauses `x₁ + y ≥ 1`, `y ∈ R`. -/
def fan (x₁ : α) (R : Finset α) (a : α → Bool) : Prop :=
  R.card ≤ (if a x₁ = true then R.card else 0) + (R.filter fun y => a y = true).card

omit [DecidableEq α] in
/-- **The fan is the sum of its clauses**, as linear forms. -/
theorem fan_sum (x₁ : α) (R : Finset α) (a : α → Bool) :
    (if a x₁ = true then R.card else 0) + (R.filter fun y => a y = true).card =
      ∑ y ∈ R, ((if a x₁ = true then 1 else 0) + (if a y = true then 1 else 0)) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_boole]
  split_ifs <;> simp

omit [DecidableEq α] in
/-- **One line names the region exactly**: the fan holds iff every clause `x₁ ∨ y`, `y ∈ R`, holds. -/
theorem fan_iff {x₁ : α} {R : Finset α} (a : α → Bool) : fan x₁ R a ↔ ∀ y ∈ R, a x₁ = true ∨ a y = true := by
  unfold fan
  constructor
  · intro h y hy
    by_cases hx : a x₁ = true
    · exact Or.inl hx
    · right
      have hx' : a x₁ = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, ite_false, zero_add] at h
      have heq := Finset.eq_of_subset_of_card_le (Finset.filter_subset (fun y => a y = true) R) h
      have hy' : y ∈ R.filter fun y => a y = true := by rw [heq]; exact hy
      exact (Finset.mem_filter.mp hy').2
  · intro h
    by_cases hx : a x₁ = true
    · simp only [hx, ite_true]
      omega
    · have hall : ∀ y ∈ R, a y = true := fun y hy => (h y hy).resolve_left hx
      rw [filter_all hall]
      omega

/-- **The fan is cheap in both channels and sensitive to everything.** -/
theorem fan_cheap {x₁ : α} {R : Finset α} (h1R : x₁ ∉ R) (hR : R.Nonempty) :
    ForcesTrue (fan x₁ R) {x₁} (fun _ => true) ∧
    (∀ y ∈ R, ForcesFalse (fan x₁ R) {x₁, y} (fun _ => false)) ∧
    (∀ x ∈ insert x₁ R, ∃ a, ¬ fan x₁ R a ∧ fan x₁ R (ProofPhase.Proof.flip x a)) := by
  have hfl : ∀ (x z : α) (a : α → Bool), z ≠ x → ProofPhase.Proof.flip x a z = a z := fun x z a h => by
    simp [ProofPhase.Proof.flip, h]
  have hfs : ∀ (x : α) (a : α → Bool), ProofPhase.Proof.flip x a x = !a x := fun x a => by
    simp [ProofPhase.Proof.flip]
  refine ⟨fun a ha => (fan_iff a).mpr fun y _ => Or.inl (ha x₁ (by simp)), fun y hy a ha hf => ?_, fun x hx => ?_⟩
  · rcases (fan_iff a).mp hf y hy with h | h
    · rw [ha x₁ (by simp)] at h; exact Bool.false_ne_true h
    · rw [ha y (by simp)] at h; exact Bool.false_ne_true h
  · obtain ⟨y₀, hy₀⟩ := hR
    rcases Finset.mem_insert.mp hx with rfl | hyR
    · refine ⟨fun _ => false, fun hf => ?_, (fan_iff _).mpr fun y _ => Or.inl (by rw [hfs]; rfl)⟩
      rcases (fan_iff _).mp hf y₀ hy₀ with h | h <;> exact Bool.false_ne_true h
    · let a : α → Bool := fun z => decide (z ≠ x ∧ z ≠ x₁)
      have hxx : x ≠ x₁ := fun e => h1R (e ▸ hyR)
      refine ⟨a, fun hf => ?_, (fan_iff _).mpr fun z hz => Or.inr ?_⟩
      · rcases (fan_iff a).mp hf x hyR with h | h <;> simp [a] at h
      · have hz1 : z ≠ x₁ := fun e => h1R (e ▸ hz)
        by_cases hzx : z = x
        · rw [hzx, hfs]; simp [a]
        · rw [hfl x z a hzx]; simp [a, hzx, hz1]

/-! ### 2. CP derivations and the creative pair -/

/-- A CP line: integer coefficients and a right-hand side, read `Σ_{i ∈ V} c i · x i ≥ b`. -/
abbrev CPLine (β : Type*) := (β → ℤ) × ℤ

variable (V : Finset α)

/-- The line holds at the (fractional) point `p`. -/
def HoldsAt (p : α → ℚ) (L : CPLine α) : Prop := (L.2 : ℚ) ≤ ∑ i ∈ V, (L.1 i : ℚ) * p i

/-- Addition of two lines. -/
def addL (L₁ L₂ : CPLine α) : CPLine α := (fun i => L₁.1 i + L₂.1 i, L₁.2 + L₂.2)

/-- Scaling by a natural number. -/
def scaleL (c : ℕ) (L : CPLine α) : CPLine α := (fun i => c * L.1 i, c * L.2)

/-- Division by `d` with rounding up of the right-hand side (`⌈b / d⌉ = -⌊-b / d⌋`). -/
def roundL (d : ℕ) (L : CPLine α) : CPLine α := (fun i => L.1 i / d, -((-L.2) / d))

/-- Cutting-planes derivations from the axioms `Ax`, over the variables `V`. -/
inductive CPD (Ax : Set (CPLine α)) : CPLine α → Prop
  | ax {L : CPLine α} : L ∈ Ax → CPD Ax L
  | add {L₁ L₂ : CPLine α} : CPD Ax L₁ → CPD Ax L₂ → CPD Ax (addL L₁ L₂)
  | scale {L : CPLine α} (c : ℕ) : 0 < c → CPD Ax L → CPD Ax (scaleL c L)
  | round {L : CPLine α} (d : ℕ) : 0 < d → (∀ i ∈ V, (d : ℤ) ∣ L.1 i) → CPD Ax L → CPD Ax (roundL d L)

variable {V}

omit [DecidableEq α] in
/-- **Addition stays in the half-space of the point.** -/
theorem holds_add {p : α → ℚ} {L₁ L₂ : CPLine α} (h₁ : HoldsAt V p L₁) (h₂ : HoldsAt V p L₂) :
    HoldsAt V p (addL L₁ L₂) := by
  unfold HoldsAt addL at *
  push_cast
  simp only [add_mul, Finset.sum_add_distrib]
  linarith

omit [DecidableEq α] in
/-- **Scaling stays in the half-space of the point.** -/
theorem holds_scale {p : α → ℚ} {L : CPLine α} (c : ℕ) (h : HoldsAt V p L) : HoldsAt V p (scaleL c L) := by
  unfold HoldsAt scaleL at *
  push_cast
  simp only [mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h (by positivity)

omit [DecidableEq α] in
/-- **Rounding a multiple of one line with a unit coefficient creates nothing.** -/
theorem round_single {p : α → ℚ} {A : CPLine α} {j : α} (hj : j ∈ V) (hunit : A.1 j = 1 ∨ A.1 j = -1) {c d : ℕ}
    (hc : 0 < c) (hd : 0 < d) (hdiv : ∀ i ∈ V, (d : ℤ) ∣ (scaleL c A).1 i) (hA : HoldsAt V p A) :
    HoldsAt V p (roundL d (scaleL c A)) := by
  have hdc : (d : ℤ) ∣ c := by
    have := hdiv j hj
    simp only [scaleL] at this
    rcases hunit with h | h <;> rw [h] at this
    · simpa using this
    · simpa using this
  obtain ⟨t, ht⟩ := hdc
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have ht0 : (0 : ℤ) ≤ t := by
    have : (0 : ℤ) < d * t := by rw [← ht]; exact_mod_cast hc
    nlinarith [show (0 : ℤ) < d by exact_mod_cast hd]
  have hcoef : ∀ i, (c : ℤ) * A.1 i / d = t * A.1 i := fun i => by
    rw [ht, mul_assoc, Int.mul_ediv_cancel_left _ hd0]
  have hrhs : -(-((c : ℤ) * A.2) / d) = t * A.2 := by
    rw [ht, show -((d : ℤ) * t * A.2) = d * (-(t * A.2)) by ring, Int.mul_ediv_cancel_left _ hd0]
    ring
  unfold HoldsAt roundL scaleL at *
  simp only [hcoef, hrhs]
  push_cast
  simp only [mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hA (by exact_mod_cast ht0)

omit [DecidableEq α] in
/-- **The creative pair.** Let a fractional point `p` satisfy every axiom, each axiom having a coefficient `±1`. Then
every derivation of a line that fails at `p` contains a rounding step whose premise `L₀` holds at `p`, whose result
fails at `p`, and whose premise is not a positive multiple of a single axiom. -/
theorem creative_pair {Ax : Set (CPLine α)} {p : α → ℚ} (hAx : ∀ A ∈ Ax, HoldsAt V p A)
    (hunit : ∀ A ∈ Ax, ∃ j ∈ V, A.1 j = 1 ∨ A.1 j = -1) {L : CPLine α} (h : CPD V Ax L) :
    ¬ HoldsAt V p L → ∃ (L₀ : CPLine α) (d : ℕ), CPD V Ax L₀ ∧ 0 < d ∧ (∀ i ∈ V, (d : ℤ) ∣ L₀.1 i) ∧ HoldsAt V p L₀ ∧
      ¬ HoldsAt V p (roundL d L₀) ∧ ¬ ∃ A ∈ Ax, ∃ c : ℕ, 0 < c ∧ L₀ = scaleL c A := by
  induction h with
  | ax hA => exact fun hL => absurd (hAx _ hA) hL
  | @add L₁ L₂ _ _ ih1 ih2 =>
    intro hL
    by_cases hh1 : HoldsAt V p L₁
    · exact ih2 fun hh2 => hL (holds_add hh1 hh2)
    · exact ih1 hh1
  | @scale L c _ _ ih =>
    intro hL
    exact ih fun hh => hL (holds_scale c hh)
  | @round L d hd hdiv hD ih =>
    intro hL
    by_cases hh : HoldsAt V p L
    · refine ⟨L, d, hD, hd, hdiv, hh, hL, ?_⟩
      rintro ⟨A, hA, c, hc, rfl⟩
      obtain ⟨j, hj, hu⟩ := hunit A hA
      exact hL (round_single hj hu hc hd hdiv (hAx A hA))
    · exact ih hh

omit [DecidableEq α] in
/-- **Every CP refutation needs a creative pair** when the axioms have a common fractional solution. -/
theorem refutation_needs_pair {Ax : Set (CPLine α)} {p : α → ℚ} (hAx : ∀ A ∈ Ax, HoldsAt V p A)
    (hunit : ∀ A ∈ Ax, ∃ j ∈ V, A.1 j = 1 ∨ A.1 j = -1) (h : CPD V Ax (fun _ => 0, 1)) :
    ∃ (L₀ : CPLine α) (d : ℕ), CPD V Ax L₀ ∧ 0 < d ∧ (∀ i ∈ V, (d : ℤ) ∣ L₀.1 i) ∧ HoldsAt V p L₀ ∧
      ¬ HoldsAt V p (roundL d L₀) ∧ ¬ ∃ A ∈ Ax, ∃ c : ℕ, 0 < c ∧ L₀ = scaleL c A :=
  creative_pair hAx hunit h (by simp [HoldsAt])

end ProofPhase.Proof.Edge
