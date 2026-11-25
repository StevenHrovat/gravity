/-
P vs NP, the edge: two channels for cutting-planes lines, a duality floor and where it fails (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/CP-DUALITY.md`.
-/

import ProofPhase.Proof.Edge

/-!
# Two channels for cutting-planes lines

**1. The certificate duality for unit thresholds.** A line can be made true by fixing some variables (a 1-certificate,
the restriction channel: what a restriction must hit to kill it) and made false by fixing others (a 0-certificate, the
width channel: what a falsifying assignment must name). For the unit threshold `thr B k` ("at least `k` of `B`"):
* forcing it true needs at least `k` fixed variables (`thr_true_card`), and `k` suffice (`thr_true_cert`);
* forcing it false needs at least `|B| − k + 1` (`thr_false_card`), and that many suffice (`thr_false_cert`);
* so the two channels sum to `|B| + 1` (`thr_duality`): **every unit-threshold line pays at least `(|B| + 1)/2` in
  one of the two**. A clause (`k = 1`) pays in width, a majority pays in resistance to restriction.

**2. Weighted lines evade it** (`two_cheap`). The CP line `r·x₁ + r·x₂ + Σ_{y ∈ R} y ≥ 2r` is sensitive to every one
of its `r + 2` variables, yet it is forced true by fixing two variables and forced false by fixing two. So no
single-line certificate measure gives a duality floor for general CP lines.

**3. The positivity template runs through the additive rules and stops at rounding** (`half_clause`,
`half_breaks_rounding`). The all-1/2 point satisfies every clause of width at least 2 as a linear inequality, and
every sum of satisfied inequalities. The rounding (division) rule is sound on 0/1 points but fails there: from
`x + y ≥ 1` and `(1 − x) + y ≥ 1` it derives `y ≥ 1`, false at the point.

**4. Pairs: shared existence, not shared possibility** (`split_unsat_iff`, `interpolant_separates`). For a formula
split as `A(x, y) ∧ B(x, z)`, unsatisfiability is exactly the disjointness of the two boundary laws `∃ y, A x y` and
`∃ z, B x z`. Each is a separator. This is the object that feasible interpolation charges.

**New here:** everything in this file.
-/

namespace ProofPhase.Proof.Edge

variable {α : Type*} [DecidableEq α]

/-- `D` with values `ρ` forces `L` true. -/
def ForcesTrue (L : (α → Bool) → Prop) (D : Finset α) (ρ : α → Bool) : Prop := ∀ a, (∀ x ∈ D, a x = ρ x) → L a

/-- `D` with values `ρ` forces `L` false. -/
def ForcesFalse (L : (α → Bool) → Prop) (D : Finset α) (ρ : α → Bool) : Prop := ∀ a, (∀ x ∈ D, a x = ρ x) → ¬ L a

/-! ### 1. The certificate duality for unit thresholds -/

theorem thr_true_card {B D : Finset α} {k : ℕ} {ρ : α → Bool} (h : ForcesTrue (thr B k) D ρ) : k ≤ D.card := by
  by_contra hlt
  obtain ⟨a, ha, hna⟩ := thr_survives (k := k) B D (by omega) ρ
  exact hna (h a ha)

theorem thr_false_card {B D : Finset α} {k : ℕ} {ρ : α → Bool} (h : ForcesFalse (thr B k) D ρ) :
    B.card + 1 ≤ k + D.card := by
  let a : α → Bool := fun x => if x ∈ D then ρ x else true
  have hsub : B \ D ⊆ B.filter fun x => a x = true := by
    intro x hx
    obtain ⟨hxB, hxD⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_filter.mpr ⟨hxB, by simp [a, hxD]⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.le_card_sdiff D B
  have hna := h a (fun x hx => by simp [a, hx])
  simp only [thr, not_le] at hna
  omega

omit [DecidableEq α] in
theorem thr_true_cert {B : Finset α} {k : ℕ} (hk : k ≤ B.card) :
    ∃ D ρ, D.card = k ∧ ForcesTrue (thr B k) D ρ := by
  obtain ⟨D, hDB, hDc⟩ := Finset.exists_subset_card_eq hk
  refine ⟨D, fun _ => true, hDc, fun a ha => ?_⟩
  have hsub : D ⊆ B.filter fun x => a x = true := fun x hx => Finset.mem_filter.mpr ⟨hDB hx, ha x hx⟩
  have := Finset.card_le_card hsub
  simp only [thr]
  omega

theorem thr_false_cert {B : Finset α} {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ B.card) :
    ∃ D ρ, D.card = B.card + 1 - k ∧ ForcesFalse (thr B k) D ρ := by
  obtain ⟨D, hDB, hDc⟩ := Finset.exists_subset_card_eq (show B.card + 1 - k ≤ B.card by omega)
  refine ⟨D, fun _ => false, hDc, fun a ha => ?_⟩
  have hsub : (B.filter fun x => a x = true) ⊆ B \ D := by
    intro x hx
    obtain ⟨hxB, hxa⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_sdiff.mpr ⟨hxB, fun hxD => ?_⟩
    rw [ha x hxD] at hxa
    exact Bool.false_ne_true hxa
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_sdiff_of_subset hDB
  simp only [thr, not_le]
  omega

/-- **The duality floor for unit thresholds.** Every true-forcing and every false-forcing partial assignment of
`thr B k` together fix at least `|B| + 1` variables, so one of them fixes at least `(|B| + 1) / 2`; and certificates of
sizes `k` and `|B| + 1 − k` exist. -/
theorem thr_duality {B : Finset α} {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ B.card) :
    (∀ D ρ D' ρ', ForcesTrue (thr B k) D ρ → ForcesFalse (thr B k) D' ρ' → B.card + 1 ≤ D.card + D'.card) ∧
    (∃ D ρ D' ρ', D.card + D'.card = B.card + 1 ∧ ForcesTrue (thr B k) D ρ ∧ ForcesFalse (thr B k) D' ρ') := by
  refine ⟨fun D ρ D' ρ' h1 h2 => ?_, ?_⟩
  · have := thr_true_card h1
    have := thr_false_card h2
    omega
  · obtain ⟨D, ρ, hD, h1⟩ := thr_true_cert hk
    obtain ⟨D', ρ', hD', h2⟩ := thr_false_cert hk1 hk
    exact ⟨D, ρ, D', ρ', by omega, h1, h2⟩

/-! ### 2. Weighted lines evade the duality -/

/-- The CP line `r·x₁ + r·x₂ + Σ_{y ∈ R} y ≥ 2r`, with `r = |R|`. -/
def wline (x₁ x₂ : α) (R : Finset α) (a : α → Bool) : Prop :=
  2 * R.card ≤ (if a x₁ then R.card else 0) + (if a x₂ then R.card else 0) + (R.filter fun y => a y = true).card

theorem filter_all_but {R : Finset α} {y : α} {a : α → Bool} (hy : y ∈ R) (hay : a y = false)
    (hrest : ∀ z ∈ R, z ≠ y → a z = true) : (R.filter fun z => a z = true).card + 1 = R.card := by
  have : (R.filter fun z => a z = true) = R.erase y := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hz, hza⟩
      exact ⟨fun e => by rw [e, hay] at hza; exact Bool.false_ne_true hza, hz⟩
    · rintro ⟨hzy, hz⟩
      exact ⟨hz, hrest z hz hzy⟩
  rw [this, Finset.card_erase_of_mem hy]
  have := Finset.card_pos.mpr ⟨y, hy⟩
  omega

omit [DecidableEq α] in
theorem filter_all {R : Finset α} {a : α → Bool} (h : ∀ z ∈ R, a z = true) :
    (R.filter fun z => a z = true).card = R.card := by
  rw [Finset.filter_true_of_mem h]

/-- **Two cheap certificates, full sensitivity.** The weighted line is forced true by two fixed variables, forced
false by two fixed variables, and sensitive to each of its `|R| + 2` variables. -/
theorem two_cheap {x₁ x₂ : α} {R : Finset α} (h12 : x₁ ≠ x₂) (h1R : x₁ ∉ R) (h2R : x₂ ∉ R) (hR : R.Nonempty) :
    ForcesTrue (wline x₁ x₂ R) {x₁, x₂} (fun _ => true) ∧
    (∀ y ∈ R, ForcesFalse (wline x₁ x₂ R) {x₁, y} (fun _ => false)) ∧
    (∀ x ∈ insert x₁ (insert x₂ R), ∃ a, ¬ wline x₁ x₂ R a ∧ wline x₁ x₂ R (ProofPhase.Proof.flip x a)) := by
  have hr := Finset.card_pos.mpr hR
  refine ⟨fun a ha => ?_, fun y hy a ha => ?_, fun x hx => ?_⟩
  · have h1 := ha x₁ (by simp)
    have h2 := ha x₂ (by simp)
    simp only [wline, h1, h2, ite_true]
    omega
  · have h1 := ha x₁ (by simp)
    have hya := ha y (by simp)
    have hsub : (R.filter fun z => a z = true) ⊆ R.erase y := by
      intro z hz
      obtain ⟨hzR, hza⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_erase.mpr ⟨fun e => by rw [e, hya] at hza; exact Bool.false_ne_true hza, hzR⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hy] at hc
    simp only [wline, h1, Bool.false_eq_true, ite_false, not_le]
    split_ifs <;> omega
  · obtain ⟨y₀, hy₀⟩ := hR
    have hfl : ∀ (x z : α) (a : α → Bool), z ≠ x → ProofPhase.Proof.flip x a z = a z := fun x z a h => by
      simp [ProofPhase.Proof.flip, h]
    have hfs : ∀ (x : α) (a : α → Bool), ProofPhase.Proof.flip x a x = !a x := fun x a => by
      simp [ProofPhase.Proof.flip]
    have hnR : ∀ {u z : α}, u ∉ R → z ∈ R → z ≠ u := fun hu hz e => hu (e ▸ hz)
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · -- `x₁`: false, `x₂` true, all of `R` but `y₀` true
      let a : α → Bool := fun z => if z = x then false else if z = y₀ then false else true
      have ha1 : a x = false := by simp [a]
      have ha2 : a x₂ = true := by simp [a, Ne.symm h12, hnR h2R hy₀ |>.symm]
      have hc : (R.filter fun z => a z = true).card + 1 = R.card :=
        filter_all_but hy₀ (by simp [a, hnR h1R hy₀]) (fun z hz hzy => by simp [a, hnR h1R hz, hzy])
      have hc' : (R.filter fun z => ProofPhase.Proof.flip x a z = true) = R.filter fun z => a z = true :=
        Finset.filter_congr fun z hz => by rw [hfl x z a (hnR h1R hz)]
      refine ⟨a, ?_, ?_⟩
      · simp only [wline, ha1, ha2, Bool.false_eq_true, ite_false, ite_true, not_le]
        omega
      · simp only [wline, hfs, ha1, hfl x x₂ a (Ne.symm h12), ha2, Bool.not_false, ite_true, hc']
        omega
    rcases Finset.mem_insert.mp hx' with rfl | hyR
    · -- `x₂`: false, `x₁` true, all of `R` but `y₀` true
      let a : α → Bool := fun z => if z = x then false else if z = y₀ then false else true
      have ha2 : a x = false := by simp [a]
      have ha1 : a x₁ = true := by simp [a, h12, hnR h1R hy₀ |>.symm]
      have hc : (R.filter fun z => a z = true).card + 1 = R.card :=
        filter_all_but hy₀ (by simp [a, hnR h2R hy₀]) (fun z hz hzy => by simp [a, hnR h2R hz, hzy])
      have hc' : (R.filter fun z => ProofPhase.Proof.flip x a z = true) = R.filter fun z => a z = true :=
        Finset.filter_congr fun z hz => by rw [hfl x z a (hnR h2R hz)]
      refine ⟨a, ?_, ?_⟩
      · simp only [wline, ha1, ha2, Bool.false_eq_true, ite_false, ite_true, not_le]
        omega
      · simp only [wline, hfs, ha2, hfl x x₁ a h12, ha1, Bool.not_false, ite_true, hc']
        omega
    · -- `y ∈ R`: `x₁` true, `x₂` false, all of `R` but `y` true
      let a : α → Bool := fun z => if z = x₂ then false else if z = x then false else true
      have ha1 : a x₁ = true := by simp [a, h12, (hnR h1R hyR).symm]
      have ha2 : a x₂ = false := by simp [a]
      have hc : (R.filter fun z => a z = true).card + 1 = R.card :=
        filter_all_but hyR (by simp [a, hnR h2R hyR]) (fun z hz hzy => by simp [a, hnR h2R hz, hzy])
      have hall : ∀ z ∈ R, ProofPhase.Proof.flip x a z = true := fun z hz => by
        by_cases hzx : z = x
        · rw [hzx, hfs]; simp [a, hnR h2R hyR]
        · rw [hfl x z a hzx]; simp [a, hnR h2R hz, hzx]
      have hx1 : x₁ ≠ x := (hnR h1R hyR).symm
      have hx2 : x₂ ≠ x := (hnR h2R hyR).symm
      refine ⟨a, ?_, ?_⟩
      · simp only [wline, ha1, ha2, Bool.false_eq_true, ite_false, ite_true, not_le]
        omega
      · simp only [wline, hfl x x₁ a hx1, hfl x x₂ a hx2, ha1, ha2, Bool.false_eq_true, ite_false, ite_true,
          filter_all hall]
        omega

/-! ### 3. The positivity template: it runs through addition and stops at rounding -/

/-- The value of a clause, read as the linear inequality `Σ literals ≥ 1`, at a fractional point. -/
def lpVal (p : α → ℚ) (C : Clause α) : ℚ := ∑ l ∈ C, if l.2 then p l.1 else 1 - p l.1

omit [DecidableEq α] in
/-- **The all-1/2 point satisfies every clause of width at least 2.** -/
theorem half_clause {C : Clause α} (hC : 2 ≤ C.card) : 1 ≤ lpVal (fun _ => (1 / 2 : ℚ)) C := by
  unfold lpVal
  have h : ∀ l ∈ C, (if l.2 then (1 / 2 : ℚ) else 1 - 1 / 2) = 1 / 2 := fun l _ => by split_ifs <;> norm_num
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  have : (2 : ℚ) ≤ C.card := by exact_mod_cast hC
  linarith

/-- **Rounding breaks it.** At the point `x = y = 1/2` the clauses `x + y ≥ 1` and `(1 − x) + y ≥ 1` hold, and so
does their sum `2y ≥ 1`; dividing by 2 and rounding gives `y ≥ 1`, which fails at the point although it holds at every
0/1 point satisfying both clauses. -/
theorem half_breaks_rounding :
    ((1 : ℚ) / 2 + 1 / 2 ≥ 1) ∧ ((1 - (1 : ℚ) / 2) + 1 / 2 ≥ 1) ∧ (2 * ((1 : ℚ) / 2) ≥ 1) ∧ ¬ ((1 : ℚ) / 2 ≥ 1) ∧
    (∀ x y : Bool, (x || y) = true → (!x || y) = true → y = true) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  decide

/-! ### 4. Pairs: shared existence, not shared possibility -/

/-- **A split formula is unsatisfiable exactly when its two boundary laws are disjoint.** -/
theorem split_unsat_iff {X Y Z : Type*} (A : X → Y → Prop) (B : X → Z → Prop) :
    (∀ x y z, ¬ (A x y ∧ B x z)) ↔ ∀ x, ¬ ((∃ y, A x y) ∧ ∃ z, B x z) := by
  constructor
  · rintro h x ⟨⟨y, hy⟩, z, hz⟩
    exact h x y z ⟨hy, hz⟩
  · intro h x y z ⟨hy, hz⟩
    exact h x ⟨⟨y, hy⟩, z, hz⟩

/-- **The boundary law of either side separates.** It contains the `A`-side law and misses the `B`-side law. -/
theorem interpolant_separates {X Y Z : Type*} (A : X → Y → Prop) (B : X → Z → Prop)
    (h : ∀ x y z, ¬ (A x y ∧ B x z)) : ∀ x, (∃ y, A x y) → ¬ ∃ z, B x z :=
  fun x hA hB => (split_unsat_iff A B).mp h x ⟨hA, hB⟩

end ProofPhase.Proof.Edge
