/-
Proof phase, cycle 4, workstream 2 (c4b-seg1): the Moebius calculus on the subset lattice with anchored exponential
weights (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c4b-seg1/NOTE.md`.
-/

import Mathlib

/-!
# Moebius coefficients, majorants and anchored weighted norms

For a function `h` on the finite subsets of a type `V`, its **Moebius coefficients** are
`mob h A = ∑_{Y ⊆ A} (-1)^{|A \ Y|} h Y`; then `h Y = ∑_{A ⊆ Y} mob h A` (`sum_mob`), and the coefficients are unique
(`mob_eq_of`). A function of a set is **local in the Moebius sense** when its coefficients live on small sets: this is
the form in which the cluster expansion delivers the log of a polymer partition function (`ProofPhase.Seg1.KP`).

This file is the algebra behind the Kotecky–Preiss theorem of `KP.lean`. Everything is elementary and group-blind
(mark D, except the two series lemmas, which are standard analysis).

* `mob_mul`: the coefficients of a pointwise product are the "union convolution" of the coefficients.
* `mob_shift`: `Y ↦ h (Y \ E)` has the coefficients of `h` on the sets disjoint from `E`, and zero elsewhere.
* `mob_insert`: `mob h (insert y A) = mob (Y ↦ h (insert y Y) - h Y) A` for `y ∉ A`.
* **Majorants.** Functions may depend on a configuration `ω : Ω`; `MajBy D h c` says `|mob (h ω) A| ≤ c A` for all `ω`
  and all `A ⊆ D`: a configuration-uniform (sup-norm) bound on every coefficient.
* **Anchored weighted norms.** For a weight `σ` on finite sets and an anchor set `K`,
  `wnorm σ K D c = ∑_{A ⊆ D} c A · exp (σ (A ∪ K))`. If `σ` is subadditive on overlapping unions (`glue`), then
  `wnorm σ K D (conv c₁ c₂) ≤ wnorm σ K D c₁ · wnorm σ {b} D c₂` for every `b ∈ K` (`wnorm_conv_le`): the weighted norms
  form a Banach-algebra-like family in which a factor anchored at a point `b` of the anchor set costs only its own norm.
  This is where exponential tails in the diameter come from without any counting of connected sets.
* `MajBy.tsum`: majorants pass through pointwise convergent series (used for `(1 + u)⁻¹` and `log (1 + u)`).
-/

open Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Seg1

variable {V : Type*} [DecidableEq V]

/-! ## Moebius coefficients -/

/-- The Moebius coefficients on the subset lattice. -/
def mob (h : Finset V → ℝ) (A : Finset V) : ℝ :=
  ∑ Y ∈ A.powerset, (-1 : ℝ) ^ (A \ Y).card * h Y

theorem mob_congr {h h' : Finset V → ℝ} {A : Finset V} (hh : ∀ Y ⊆ A, h Y = h' Y) : mob h A = mob h' A :=
  sum_congr rfl fun Y hY => by rw [hh Y (mem_powerset.1 hY)]

theorem mob_empty (h : Finset V → ℝ) : mob h ∅ = h ∅ := by simp [mob]

theorem card_insert_sdiff {y : V} {A Y : Finset V} (hy : y ∉ A) (hY : Y ⊆ A) :
    (insert y A \ Y).card = (A \ Y).card + 1 := by
  have hyY : y ∉ Y := fun h => hy (hY h)
  have e : insert y A \ Y = insert y (A \ Y) := by
    ext x; simp only [mem_sdiff, mem_insert]; constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (h1 | ⟨h1, h2⟩)
      · subst h1; exact ⟨Or.inl rfl, hyY⟩
      · exact ⟨Or.inr h1, h2⟩
  rw [e, card_insert_of_notMem (fun h => hy (mem_sdiff.1 h).1)]

theorem insert_sdiff_insert_eq {y : V} {A Y : Finset V} (hy : y ∉ A) : insert y A \ insert y Y = A \ Y := by
  ext x; simp only [mem_sdiff, mem_insert, not_or]; constructor
  · rintro ⟨h1 | h1, h2, h3⟩
    · exact absurd h1 h2
    · exact ⟨h1, h3⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Or.inr h1, fun h => hy (h ▸ h1), h2⟩

/-- Moebius coefficients at `insert y A` are those of the `y`-difference at `A`. -/
theorem mob_insert {h : Finset V → ℝ} {y : V} {A : Finset V} (hy : y ∉ A) :
    mob h (insert y A) = mob (fun B => h (insert y B) - h B) A := by
  unfold mob
  rw [sum_powerset_insert hy, ← sum_add_distrib]
  refine sum_congr rfl fun Y hY => ?_
  have hYA := mem_powerset.1 hY
  rw [card_insert_sdiff hy hYA, insert_sdiff_insert_eq hy, pow_succ]
  ring

/-- **Moebius inversion**: `h Y = ∑_{A ⊆ Y} mob h A`. -/
theorem sum_mob (h : Finset V → ℝ) (Y : Finset V) : ∑ A ∈ Y.powerset, mob h A = h Y := by
  induction Y using Finset.induction_on generalizing h with
  | empty => simp [mob_empty]
  | insert y Y hy ih =>
    rw [sum_powerset_insert hy, ih]
    have : ∑ A ∈ Y.powerset, mob h (insert y A) = ∑ A ∈ Y.powerset, mob (fun B => h (insert y B) - h B) A :=
      sum_congr rfl fun A hA => mob_insert fun h' => hy (mem_powerset.1 hA h')
    rw [this, ih (fun B => h (insert y B) - h B)]
    ring

/-- **Uniqueness of the coefficients**: if `h = ∑_{B ⊆ ·} c B` on the subsets of `A`, then `mob h A = c A`. -/
theorem mob_eq_of {h c : Finset V → ℝ} {A : Finset V} (hh : ∀ Y ⊆ A, h Y = ∑ B ∈ Y.powerset, c B) :
    mob h A = c A := by
  rw [mob_congr hh]
  clear hh h
  induction A using Finset.induction_on generalizing c with
  | empty => simp [mob_empty]
  | insert y A hy ih =>
    rw [mob_insert hy]
    have : mob (fun B => ∑ B' ∈ (insert y B).powerset, c B' - ∑ B' ∈ B.powerset, c B') A =
        mob (fun B => ∑ B' ∈ B.powerset, c (insert y B')) A := by
      refine mob_congr fun B hB => ?_
      rw [sum_powerset_insert fun h' => hy (hB h')]
      ring
    rw [this, ih]

theorem mob_add (h₁ h₂ : Finset V → ℝ) (A : Finset V) :
    mob (fun Y => h₁ Y + h₂ Y) A = mob h₁ A + mob h₂ A := by
  unfold mob; rw [← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring

theorem mob_const_mul (a : ℝ) (h : Finset V → ℝ) (A : Finset V) : mob (fun Y => a * h Y) A = a * mob h A := by
  unfold mob; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring

theorem mob_neg (h : Finset V → ℝ) (A : Finset V) : mob (fun Y => - h Y) A = - mob h A := by
  have := mob_const_mul (-1) h A; simp only [neg_one_mul] at this; exact this

theorem mob_sum {ι : Type*} (s : Finset ι) (f : ι → Finset V → ℝ) (A : Finset V) :
    mob (fun Y => ∑ i ∈ s, f i Y) A = ∑ i ∈ s, mob (f i) A := by
  unfold mob; simp_rw [mul_sum]; exact sum_comm

/-- The coefficients of a constant. -/
theorem mob_const (a : ℝ) (A : Finset V) : mob (fun _ => a) A = if A = ∅ then a else 0 :=
  mob_eq_of (c := fun B => if B = ∅ then a else 0) fun Y _ => by simp [sum_ite_eq']

/-- The up-set indicator of `B`. -/
def upS (B Y : Finset V) : ℝ := if B ⊆ Y then 1 else 0

theorem mob_upS (B A : Finset V) : mob (upS B) A = if A = B then 1 else 0 :=
  mob_eq_of (c := fun A' => if A' = B then 1 else 0) fun Y _ => by simp [upS, sum_ite_eq', mem_powerset]

/-- The pairs of subsets of `A` whose union is `A`. -/
def pairs (A : Finset V) : Finset (Finset V × Finset V) :=
  (A.powerset ×ˢ A.powerset).filter fun p => p.1 ∪ p.2 = A

theorem mem_pairs {A : Finset V} {p : Finset V × Finset V} : p ∈ pairs A ↔ p.1 ∪ p.2 = A := by
  unfold pairs
  simp only [mem_filter, mem_product, mem_powerset]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨⟨h ▸ subset_union_left, h ▸ subset_union_right⟩, h⟩

/-- Regrouping a sum over pairs of subsets of `D` by their union. -/
theorem sum_pairs (D : Finset V) (f : Finset V × Finset V → ℝ) :
    ∑ A ∈ D.powerset, ∑ p ∈ pairs A, f p = ∑ p ∈ D.powerset ×ˢ D.powerset, f p := by
  rw [← sum_fiberwise_of_maps_to (s := D.powerset ×ˢ D.powerset) (t := D.powerset) (g := fun p => p.1 ∪ p.2)]
  · refine sum_congr rfl fun A hA => sum_congr ?_ fun _ _ => rfl
    ext p
    rw [mem_pairs, mem_filter, mem_product, mem_powerset, mem_powerset]
    have hAD := mem_powerset.1 hA
    constructor
    · intro h; exact ⟨⟨fun x hx => hAD (h ▸ mem_union_left _ hx), fun x hx => hAD (h ▸ mem_union_right _ hx)⟩, h⟩
    · exact fun h => h.2
  · intro p hp
    rw [mem_product, mem_powerset, mem_powerset] at hp
    exact mem_powerset.2 (union_subset hp.1 hp.2)

/-- **Coefficients of a product**: the union convolution of the coefficients. -/
theorem mob_mul (h₁ h₂ : Finset V → ℝ) (A : Finset V) :
    mob (fun Y => h₁ Y * h₂ Y) A = ∑ p ∈ pairs A, mob h₁ p.1 * mob h₂ p.2 := by
  refine mob_eq_of (c := fun B => ∑ p ∈ pairs B, mob h₁ p.1 * mob h₂ p.2) fun Y _ => ?_
  rw [← sum_mob h₁ Y, ← sum_mob h₂ Y, sum_mul_sum, ← sum_product', sum_pairs Y (fun p => mob h₁ p.1 * mob h₂ p.2)]

/-- **Coefficients of a shift**: `Y ↦ h (Y \ E)` keeps the coefficients on sets disjoint from `E`. -/
theorem mob_shift (h : Finset V → ℝ) (E A : Finset V) :
    mob (fun Y => h (Y \ E)) A = if Disjoint A E then mob h A else 0 := by
  refine mob_eq_of (c := fun B => if Disjoint B E then mob h B else 0) fun Y _ => ?_
  rw [← sum_mob h (Y \ E), ← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext B; simp only [mem_powerset, mem_filter, subset_sdiff]

/-- Coefficients of a product with an up-set indicator vanish off the up-set. -/
theorem mob_upS_mul_eq_zero (B : Finset V) (h : Finset V → ℝ) {A : Finset V} (hA : ¬ B ⊆ A) :
    mob (fun Y => upS B Y * h Y) A = 0 := by
  rw [mob_mul]
  refine sum_eq_zero fun p hp => ?_
  rw [mob_upS]
  have hp' := mem_pairs.1 hp
  have : p.1 ≠ B := fun e => hA (e ▸ hp' ▸ subset_union_left)
  simp [this]

/-! ## Majorants and anchored weighted norms -/

variable {Ω : Type*}

/-- `c` majorises the Moebius coefficients of `h` on the subsets of `D`, uniformly in the configuration. -/
def MajBy (D : Finset V) (h : Ω → Finset V → ℝ) (c : Finset V → ℝ) : Prop :=
  ∀ ω, ∀ A ∈ D.powerset, |mob (h ω) A| ≤ c A

theorem MajBy.congr {D : Finset V} {h h' : Ω → Finset V → ℝ} {c : Finset V → ℝ} (hc : MajBy D h c)
    (hh : ∀ ω, ∀ Y ⊆ D, h ω Y = h' ω Y) : MajBy D h' c := fun ω A hA => by
  rw [← mob_congr fun Y hY => hh ω Y (hY.trans (mem_powerset.1 hA))]; exact hc ω A hA

theorem MajBy.mono {D : Finset V} {h : Ω → Finset V → ℝ} {c c' : Finset V → ℝ} (hc : MajBy D h c)
    (hcc : ∀ A ∈ D.powerset, c A ≤ c' A) : MajBy D h c' := fun ω A hA => (hc ω A hA).trans (hcc A hA)

/-- The union convolution of two majorants. -/
def conv (c₁ c₂ : Finset V → ℝ) (A : Finset V) : ℝ := ∑ p ∈ pairs A, c₁ p.1 * c₂ p.2

theorem conv_nonneg {c₁ c₂ : Finset V → ℝ} (h₁ : ∀ A, 0 ≤ c₁ A) (h₂ : ∀ A, 0 ≤ c₂ A) (A : Finset V) :
    0 ≤ conv c₁ c₂ A := sum_nonneg fun _ _ => mul_nonneg (h₁ _) (h₂ _)

theorem MajBy.mul {D : Finset V} {h₁ h₂ : Ω → Finset V → ℝ} {c₁ c₂ : Finset V → ℝ} (m₁ : MajBy D h₁ c₁)
    (m₂ : MajBy D h₂ c₂) : MajBy D (fun ω Y => h₁ ω Y * h₂ ω Y) (conv c₁ c₂) := by
  intro ω A hA
  rw [mob_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp => ?_)
  have hp' := mem_pairs.1 hp
  have hAD := mem_powerset.1 hA
  have h1 : p.1 ∈ D.powerset := mem_powerset.2 ((hp' ▸ subset_union_left).trans hAD)
  have h2 : p.2 ∈ D.powerset := mem_powerset.2 ((hp' ▸ subset_union_right).trans hAD)
  rw [abs_mul]
  exact mul_le_mul (m₁ ω _ h1) (m₂ ω _ h2) (abs_nonneg _) ((abs_nonneg _).trans (m₁ ω _ h1))

theorem MajBy.add {D : Finset V} {h₁ h₂ : Ω → Finset V → ℝ} {c₁ c₂ : Finset V → ℝ} (m₁ : MajBy D h₁ c₁)
    (m₂ : MajBy D h₂ c₂) : MajBy D (fun ω Y => h₁ ω Y + h₂ ω Y) (fun A => c₁ A + c₂ A) := fun ω A hA => by
  rw [mob_add]; exact (abs_add_le _ _).trans (add_le_add (m₁ ω A hA) (m₂ ω A hA))

theorem MajBy.const_mul {D : Finset V} {h : Ω → Finset V → ℝ} {c : Finset V → ℝ} (m : MajBy D h c)
    {a : Ω → ℝ} {ā : ℝ} (ha : ∀ ω, |a ω| ≤ ā) : MajBy D (fun ω Y => a ω * h ω Y) (fun A => ā * c A) :=
  fun ω A hA => by
    rw [mob_const_mul, abs_mul]
    exact mul_le_mul (ha ω) (m ω A hA) (abs_nonneg _) ((abs_nonneg _).trans (ha ω))

theorem MajBy.neg {D : Finset V} {h : Ω → Finset V → ℝ} {c : Finset V → ℝ} (m : MajBy D h c) :
    MajBy D (fun ω Y => - h ω Y) c := fun ω A hA => by rw [mob_neg, abs_neg]; exact m ω A hA

theorem MajBy.sum {ι : Type*} (s : Finset ι) {D : Finset V} {f : ι → Ω → Finset V → ℝ} {c : ι → Finset V → ℝ}
    (m : ∀ i ∈ s, MajBy D (f i) (c i)) :
    MajBy D (fun ω Y => ∑ i ∈ s, f i ω Y) (fun A => ∑ i ∈ s, c i A) := fun ω A hA => by
  rw [mob_sum]; exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => m i hi ω A hA)

theorem majBy_shift {D E : Finset V} {g : Ω → Finset V → ℝ} {c : Finset V → ℝ} (m : MajBy (D \ E) g c) :
    MajBy D (fun ω Y => g ω (Y \ E)) (fun A => if Disjoint A E then c A else 0) := by
  intro ω A hA
  dsimp only
  rw [mob_shift]
  split_ifs with h
  · exact m ω A (mem_powerset.2 (subset_sdiff.2 ⟨mem_powerset.1 hA, h⟩))
  · simp

/-- The majorant of the constant `1`. -/
def unitM (A : Finset V) : ℝ := if A = ∅ then 1 else 0

theorem unitM_nonneg (A : Finset V) : 0 ≤ unitM A := by unfold unitM; split_ifs <;> norm_num

theorem majBy_one (D : Finset V) : MajBy D (fun (_ : Ω) _ => (1 : ℝ)) unitM := fun _ A _ => by
  rw [mob_const]; unfold unitM; split_ifs <;> simp

/-- The majorant of the up-set indicator of `{b}`. -/
def deltaM (b : V) (A : Finset V) : ℝ := if A = {b} then 1 else 0

theorem deltaM_nonneg (b : V) (A : Finset V) : 0 ≤ deltaM b A := by unfold deltaM; split_ifs <;> norm_num

theorem majBy_upS (D : Finset V) (b : V) : MajBy D (fun (_ : Ω) => upS {b}) (deltaM b) := fun _ A _ => by
  rw [mob_upS]; unfold deltaM; split_ifs <;> simp

/-- Powers of a majorant under the union convolution. -/
def cpow (c : Finset V → ℝ) : ℕ → Finset V → ℝ
  | 0 => unitM
  | n + 1 => conv (cpow c n) c

theorem cpow_nonneg {c : Finset V → ℝ} (hc : ∀ A, 0 ≤ c A) (n : ℕ) (A : Finset V) : 0 ≤ cpow c n A := by
  induction n generalizing A with
  | zero => exact unitM_nonneg A
  | succ n ih => exact conv_nonneg ih hc A

theorem MajBy.pow {D : Finset V} {h : Ω → Finset V → ℝ} {c : Finset V → ℝ} (m : MajBy D h c) (n : ℕ) :
    MajBy D (fun ω Y => h ω Y ^ n) (cpow c n) := by
  induction n with
  | zero => simp only [pow_zero]; exact majBy_one D
  | succ n ih => simp only [pow_succ]; exact ih.mul m

section Weight

variable (σ : Finset V → ℝ)

/-- The anchored weighted norm of a majorant. -/
def wnorm (K D : Finset V) (c : Finset V → ℝ) : ℝ := ∑ A ∈ D.powerset, c A * Real.exp (σ (A ∪ K))

/-- **Admissible weights**: nonnegative on nonempty sets, zero on singletons, subadditive on overlapping unions.
Examples: `λ · diam` for a pseudometric, `|S| - 1`, and their sums (`Envelope.lean`). -/
structure Weight : Prop where
  nonneg : ∀ S : Finset V, S.Nonempty → 0 ≤ σ S
  single : ∀ v : V, σ {v} = 0
  glue : ∀ S T : Finset V, (S ∩ T).Nonempty → σ (S ∪ T) ≤ σ S + σ T

variable {σ}

theorem wnorm_nonneg {K D : Finset V} {c : Finset V → ℝ} (hc : ∀ A, 0 ≤ c A) : 0 ≤ wnorm σ K D c :=
  sum_nonneg fun A _ => mul_nonneg (hc A) (Real.exp_pos _).le

theorem wnorm_add (K D : Finset V) (c₁ c₂ : Finset V → ℝ) :
    wnorm σ K D (fun A => c₁ A + c₂ A) = wnorm σ K D c₁ + wnorm σ K D c₂ := by
  unfold wnorm; rw [← sum_add_distrib]; exact sum_congr rfl fun _ _ => by ring

theorem wnorm_const_mul (K D : Finset V) (a : ℝ) (c : Finset V → ℝ) :
    wnorm σ K D (fun A => a * c A) = a * wnorm σ K D c := by
  unfold wnorm; rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring

theorem wnorm_sum {ι : Type*} (s : Finset ι) (K D : Finset V) (c : ι → Finset V → ℝ) :
    wnorm σ K D (fun A => ∑ i ∈ s, c i A) = ∑ i ∈ s, wnorm σ K D (c i) := by
  unfold wnorm; simp_rw [sum_mul]; exact sum_comm

theorem wnorm_mono {K D : Finset V} {c c' : Finset V → ℝ} (h : ∀ A ∈ D.powerset, c A ≤ c' A) :
    wnorm σ K D c ≤ wnorm σ K D c' :=
  sum_le_sum fun A hA => mul_le_mul_of_nonneg_right (h A hA) (Real.exp_pos _).le

theorem wnorm_unitM (K D : Finset V) : wnorm σ K D unitM = Real.exp (σ K) := by
  unfold wnorm unitM
  rw [sum_eq_single (∅ : Finset V)]
  · simp
  · intro A _ hA; simp [hA]
  · intro h; exact absurd (empty_mem_powerset D) h

theorem wnorm_deltaM (hσ : Weight σ) {b : V} {D : Finset V} (hb : b ∈ D) : wnorm σ {b} D (deltaM b) = 1 := by
  unfold wnorm deltaM
  rw [sum_eq_single ({b} : Finset V)]
  · simp [hσ.single]
  · intro A _ hA; simp [hA]
  · intro h; exact absurd (mem_powerset.2 (singleton_subset_iff.2 hb)) h

/-- **The gluing inequality** (S, elementary): a factor anchored at a point `b` of the anchor set `K` costs only its
own norm. -/
theorem wnorm_conv_le (hσ : Weight σ) {K D : Finset V} {b : V} (hb : b ∈ K) {c₁ c₂ : Finset V → ℝ}
    (h₁ : ∀ A, 0 ≤ c₁ A) (h₂ : ∀ A, 0 ≤ c₂ A) :
    wnorm σ K D (conv c₁ c₂) ≤ wnorm σ K D c₁ * wnorm σ {b} D c₂ := by
  unfold wnorm conv
  calc ∑ A ∈ D.powerset, (∑ p ∈ pairs A, c₁ p.1 * c₂ p.2) * Real.exp (σ (A ∪ K))
      = ∑ A ∈ D.powerset, ∑ p ∈ pairs A, c₁ p.1 * c₂ p.2 * Real.exp (σ ((p.1 ∪ p.2) ∪ K)) := by
        refine sum_congr rfl fun A _ => ?_
        rw [sum_mul]
        exact sum_congr rfl fun p hp => by rw [mem_pairs.1 hp]
    _ = ∑ p ∈ D.powerset ×ˢ D.powerset, c₁ p.1 * c₂ p.2 * Real.exp (σ ((p.1 ∪ p.2) ∪ K)) := sum_pairs D _
    _ ≤ ∑ p ∈ D.powerset ×ˢ D.powerset, c₁ p.1 * Real.exp (σ (p.1 ∪ K)) * (c₂ p.2 * Real.exp (σ (p.2 ∪ {b}))) := by
      refine sum_le_sum fun p _ => ?_
      have e : (p.1 ∪ p.2) ∪ K = (p.1 ∪ K) ∪ (p.2 ∪ {b}) := by
        ext x; simp only [mem_union, mem_singleton]; constructor
        · rintro ((h | h) | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl (Or.inr h)
        · rintro ((h | h) | (h | h))
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
          · exact Or.inl (Or.inr h)
          · exact Or.inr (h ▸ hb)
      have hov : ((p.1 ∪ K) ∩ (p.2 ∪ {b})).Nonempty :=
        ⟨b, mem_inter.2 ⟨mem_union_right _ hb, mem_union_right _ (mem_singleton_self b)⟩⟩
      have hg := hσ.glue _ _ hov
      rw [e]
      have hexp : Real.exp (σ ((p.1 ∪ K) ∪ (p.2 ∪ {b}))) ≤
          Real.exp (σ (p.1 ∪ K)) * Real.exp (σ (p.2 ∪ {b})) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.2 hg
      have := mul_nonneg (h₁ p.1) (h₂ p.2)
      calc c₁ p.1 * c₂ p.2 * Real.exp (σ ((p.1 ∪ K) ∪ (p.2 ∪ {b})))
          ≤ c₁ p.1 * c₂ p.2 * (Real.exp (σ (p.1 ∪ K)) * Real.exp (σ (p.2 ∪ {b}))) :=
            mul_le_mul_of_nonneg_left hexp this
        _ = c₁ p.1 * Real.exp (σ (p.1 ∪ K)) * (c₂ p.2 * Real.exp (σ (p.2 ∪ {b}))) := by ring
    _ = (∑ A ∈ D.powerset, c₁ A * Real.exp (σ (A ∪ K))) * ∑ A ∈ D.powerset, c₂ A * Real.exp (σ (A ∪ {b})) := by
      rw [sum_mul_sum, ← sum_product']

theorem wnorm_cpow_le (hσ : Weight σ) {D : Finset V} {y : V} {c : Finset V → ℝ} (hc : ∀ A, 0 ≤ c A) (n : ℕ) :
    wnorm σ {y} D (cpow c n) ≤ wnorm σ {y} D c ^ n := by
  induction n with
  | zero => simp [cpow, wnorm_unitM, hσ.single]
  | succ n ih =>
    calc wnorm σ {y} D (cpow c (n + 1)) ≤ wnorm σ {y} D (cpow c n) * wnorm σ {y} D c :=
          wnorm_conv_le hσ (mem_singleton_self y) (cpow_nonneg hc n) hc
      _ ≤ wnorm σ {y} D c ^ n * wnorm σ {y} D c :=
          mul_le_mul_of_nonneg_right ih (wnorm_nonneg hc)
      _ = _ := by rw [pow_succ]

theorem wnorm_shift (K D E : Finset V) (c : Finset V → ℝ) :
    wnorm σ K D (fun A => if Disjoint A E then c A else 0) = wnorm σ K (D \ E) c := by
  unfold wnorm
  rw [show (D \ E).powerset = D.powerset.filter (fun A => Disjoint A E) by
    ext A; simp only [mem_powerset, mem_filter, subset_sdiff], sum_filter]
  exact sum_congr rfl fun A _ => by by_cases h : Disjoint A E <;> simp [h]

/-- **Changing the anchor** from a point `y` to `insert y C` costs nothing for majorants supported on the up-set of
`C`. -/
theorem wnorm_trunc_le {y : V} {C K D : Finset V} (hK : K = insert y C) {c : Finset V → ℝ}
    (hc0 : ∀ A, 0 ≤ c A) : wnorm σ {y} D (fun A => if C ⊆ A then c A else 0) ≤ wnorm σ K D c := by
  unfold wnorm
  refine sum_le_sum fun A _ => ?_
  dsimp only
  split_ifs with h
  · have e : A ∪ {y} = A ∪ K := by
      rw [hK]; ext x; simp only [mem_union, mem_singleton, mem_insert]
      constructor
      · rintro (hx | hx)
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)
      · rintro (hx | hx | hx)
        · exact Or.inl hx
        · exact Or.inr hx
        · exact Or.inl (h hx)
    rw [e]
  · rw [zero_mul]; exact mul_nonneg (hc0 A) (Real.exp_pos _).le

/-- Pointwise values are bounded by the norm of a majorant (anchor nonempty). -/
theorem abs_le_wnorm (hσ : Weight σ) {K D : Finset V} (hK : K.Nonempty) {h : Ω → Finset V → ℝ}
    {c : Finset V → ℝ} (hc0 : ∀ A, 0 ≤ c A) (m : MajBy D h c) (ω : Ω) {Y : Finset V} (hY : Y ⊆ D) :
    |h ω Y| ≤ wnorm σ K D c := by
  rw [← sum_mob (h ω) Y]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ A ∈ Y.powerset, |mob (h ω) A| ≤ ∑ A ∈ Y.powerset, c A :=
        sum_le_sum fun A hA => m ω A (mem_powerset.2 ((mem_powerset.1 hA).trans hY))
    _ ≤ ∑ A ∈ D.powerset, c A := sum_le_sum_of_subset_of_nonneg (powerset_mono.2 hY) fun A _ _ => hc0 A
    _ ≤ wnorm σ K D c := sum_le_sum fun A _ => by
        have h0 : 0 ≤ σ (A ∪ K) := hσ.nonneg _ (hK.mono subset_union_right)
        have : 1 ≤ Real.exp (σ (A ∪ K)) := Real.one_le_exp h0
        nlinarith [hc0 A]

/-- **Majorants pass through series** (standard analysis): if `h = ∑ₙ fₙ` pointwise on the subsets of `D`, each `fₙ`
is majorised by `cₙ ≥ 0`, and the norms `wnorm (cₙ) ≤ tₙ` are summable, then `∑' cₙ` majorises `h` and its norm is
`≤ ∑' tₙ`. -/
theorem MajBy.tsum (hσ : Weight σ) {K D : Finset V} (hK : K.Nonempty) {f : ℕ → Ω → Finset V → ℝ}
    {h : Ω → Finset V → ℝ} {c : ℕ → Finset V → ℝ} {t : ℕ → ℝ} (hc0 : ∀ n A, 0 ≤ c n A)
    (m : ∀ n, MajBy D (f n) (c n)) (hf : ∀ ω, ∀ Y ⊆ D, HasSum (fun n => f n ω Y) (h ω Y))
    (ht : ∀ n, wnorm σ K D (c n) ≤ t n) (hts : Summable t) :
    MajBy D h (fun A => ∑' n, c n A) ∧ wnorm σ K D (fun A => ∑' n, c n A) ≤ ∑' n, t n := by
  -- summability of every coefficient majorant
  have hcA : ∀ A ∈ D.powerset, Summable fun n => c n A := by
    intro A hA
    refine Summable.of_nonneg_of_le (fun n => hc0 n A) (fun n => ?_) hts
    have h0 : 0 ≤ σ (A ∪ K) := hσ.nonneg _ (hK.mono subset_union_right)
    calc c n A ≤ c n A * Real.exp (σ (A ∪ K)) := le_mul_of_one_le_right (hc0 n A) (Real.one_le_exp h0)
      _ ≤ wnorm σ K D (c n) :=
          single_le_sum (f := fun A => c n A * Real.exp (σ (A ∪ K))) (fun B _ => mul_nonneg (hc0 n B)
            (Real.exp_pos _).le) hA
      _ ≤ t n := ht n
  refine ⟨fun ω A hA => ?_, ?_⟩
  · have hS : HasSum (fun n => mob (f n ω) A) (mob (h ω) A) := by
      unfold mob
      exact hasSum_sum fun Y hY =>
        (hf ω Y ((mem_powerset.1 hY).trans (mem_powerset.1 hA))).mul_left _
    have hcs := (hcA A hA).hasSum
    have hle : ∀ n, |mob (f n ω) A| ≤ c n A := fun n => m n ω A hA
    rw [abs_le]
    constructor
    · have := hasSum_le (fun n => (neg_le_of_abs_le (hle n))) hcs.neg hS
      linarith
    · exact hasSum_le (fun n => le_of_abs_le (hle n)) hS hcs
  · unfold wnorm
    have e : ∑ A ∈ D.powerset, (∑' n, c n A) * Real.exp (σ (A ∪ K)) =
        ∑' n, ∑ A ∈ D.powerset, c n A * Real.exp (σ (A ∪ K)) := by
      rw [Summable.tsum_finsetSum fun A hA => (hcA A hA).mul_right _]
      exact sum_congr rfl fun A _ => (tsum_mul_right).symm
    rw [e]
    have hsw : Summable fun n => ∑ A ∈ D.powerset, c n A * Real.exp (σ (A ∪ K)) :=
      summable_sum fun A hA => (hcA A hA).mul_right _
    exact Summable.tsum_le_tsum (fun n => ht n) hsw hts

end Weight

end ProofPhase.Seg1
