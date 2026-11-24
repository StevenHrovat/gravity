/-
Proof phase, ScaleHyp kit, module 4: counting, generic and on the torus (2026-11-23). Released under Apache 2.0.

Pack: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/PACK-SCALEHYP.md`, item (e).
Note: `docs/mass-gap/weak-coupling/proof-phase/scalehyp/NOTE.md`.
-/

import ProofPhase.OneBox.CouplingDS

/-!
# Counting: the `hcount` input of `ScaleHyp.ofBlockBounds`

`hcount` asks, for every site `z`,
`Σ_{b good, z ∉ B b} Σ_{y ∈ B b} w b z e^{λ d(z, y)} ≤ M c(z)`, with `c` the coverage.

* `hcount_of_range` (generic): if `0 ≤ w ≤ W₀`, `|B b| ≤ V`, `w b z ≠ 0` only when every `y ∈ B b` is within `D` of
  `z` (finite range plus block diameter), and the number of blocks with `w b z ≠ 0` is at most `A c(z)` (multiplicity),
  then `hcount` holds with `M = A V W₀ e^{λ D}`.
* **The torus** `(ZMod N)^d` with the lattice (graph, `ℓ¹`) distance `tdist`, built from `ZMod.valMinAbs`:
  `tdist_self`, `tdist_triangle`.
* **The box family** of all translates `b + K` of the side-`ℓ` box `K = {0, ..., ℓ - 1}^d`, indexed by `b` in the
  torus: `coverage_boxes` (every site is covered `|K|` times), `card_boxes`, `tdist_boxes_le` (diameter `≤ d ℓ`),
  and `card_near_le` (at most `(2R + 1)^d |K|` boxes come within distance `R` of a site).
* `torus_hcount`: `hcount` for the box family with `w = nearW` (`1` if the box comes within `R` of `z`, else `0`)
  and `M = (2R + 1)^d |K| e^{λ (R + d ℓ)}`. With `κ b z ≤ ε nearW b z` (the influence vanishes beyond the range `R`
  and is at most `ε`), `ScaleHyp.ofBlockBounds` then gets `γ = ε M`.

The composite boxes `W(K)` with multiplicity `n_W` (`UV-TV.md` 22.3) fit the generic lemma with `A = n_W`-type
constants; their geometry depends on the cluster configuration and stays on paper.
-/

open Finset ProofPhase.OneBox

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.ScaleHypKit

/-! ### Generic counting -/

section Generic

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

/-- **`hcount` from finite range, block size and multiplicity.** -/
theorem hcount_of_range (B : β → Finset ι) (good : Finset β) (dist : ι → ι → ℝ) (w : β → ι → ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) {W₀ V D A : ℝ} (hW₀ : 0 ≤ W₀) (hV : 0 ≤ V) (hw : ∀ b z, w b z ≤ W₀)
    (hcard : ∀ b, ((B b).card : ℝ) ≤ V)
    (hrange : ∀ b z, w b z ≠ 0 → ∀ y ∈ B b, dist z y ≤ D)
    (hmult : ∀ z, ((univ.filter fun b => w b z ≠ 0).card : ℝ) ≤ A * coverage B z) (z : ι) :
    ∑ b ∈ good.filter (fun b => z ∉ B b), ∑ y ∈ B b, w b z * Real.exp (lam * dist z y) ≤
      A * V * W₀ * Real.exp (lam * D) * coverage B z := by
  set c := V * W₀ * Real.exp (lam * D) with hcdef
  have hc : 0 ≤ c := by positivity
  have hinner : ∀ b, ∑ y ∈ B b, w b z * Real.exp (lam * dist z y) ≤ if w b z ≠ 0 then c else 0 := by
    intro b
    split_ifs with h
    · calc ∑ y ∈ B b, w b z * Real.exp (lam * dist z y)
          ≤ ∑ _y ∈ B b, W₀ * Real.exp (lam * D) := by
            refine sum_le_sum fun y hy => mul_le_mul (hw b z) ?_ (Real.exp_pos _).le hW₀
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hrange b z h y hy) hlam)
        _ = (B b).card * (W₀ * Real.exp (lam * D)) := by rw [sum_const, nsmul_eq_mul]
        _ ≤ V * (W₀ * Real.exp (lam * D)) := mul_le_mul_of_nonneg_right (hcard b) (by positivity)
        _ = c := by rw [hcdef]; ring
    · push Not at h
      simp [h]
  calc ∑ b ∈ good.filter (fun b => z ∉ B b), ∑ y ∈ B b, w b z * Real.exp (lam * dist z y)
      ≤ ∑ b ∈ good.filter (fun b => z ∉ B b), (if w b z ≠ 0 then c else 0) := sum_le_sum fun b _ => hinner b
    _ ≤ ∑ b, (if w b z ≠ 0 then c else 0) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun b _ _ => by split_ifs <;> simp [hc]
    _ = (univ.filter fun b => w b z ≠ 0).card * c := by rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ A * coverage B z * c := mul_le_mul_of_nonneg_right (hmult z) hc
    _ = A * V * W₀ * Real.exp (lam * D) * coverage B z := by rw [hcdef]; ring

end Generic

/-! ### The torus and its lattice distance -/

section Torus

variable {d N : ℕ} [NeZero N]

/-- The torus `(ZMod N)^d`. -/
abbrev Torus (d N : ℕ) := Fin d → ZMod N

/-- The lattice (graph, `ℓ¹`) distance on the torus. -/
def tdist (x y : Torus d N) : ℝ := ∑ i, ((x i - y i).valMinAbs.natAbs : ℝ)

theorem natAbs_valMinAbs_add_le (a b : ZMod N) :
    (a + b).valMinAbs.natAbs ≤ a.valMinAbs.natAbs + b.valMinAbs.natAbs := by
  have he : (((a + b).valMinAbs : ℤ) : ZMod N) = ((a.valMinAbs + b.valMinAbs : ℤ) : ZMod N) := by
    simp
  exact (ZMod.natAbs_min_of_le_div_two N _ _ he (ZMod.natAbs_valMinAbs_le _)).trans (Int.natAbs_add_le _ _)

theorem tdist_self (x : Torus d N) : tdist x x = 0 := by simp [tdist, ZMod.valMinAbs_zero]

theorem tdist_triangle (x y z : Torus d N) : tdist x z ≤ tdist x y + tdist y z := by
  simp only [tdist, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  have h := natAbs_valMinAbs_add_le (x i - y i) (y i - z i)
  rw [sub_add_sub_cancel] at h
  exact_mod_cast h

/-- If `a, b` are casts of integers `a', b'` with `|a' - b'| ≤ m`, the torus distance of `a, b` is at most `m`. -/
theorem natAbs_valMinAbs_sub_le_of_cast (a' b' : ℤ) {m : ℕ} (h : (a' - b').natAbs ≤ m) :
    (((a' : ZMod N) - (b' : ZMod N))).valMinAbs.natAbs ≤ m := by
  have he : (((((a' : ZMod N) - (b' : ZMod N))).valMinAbs : ℤ) : ZMod N) = ((a' - b' : ℤ) : ZMod N) := by
    simp
  exact (ZMod.natAbs_min_of_le_div_two N _ _ he (ZMod.natAbs_valMinAbs_le _)).trans h

/-! ### The box family -/

/-- The offsets of the side-`ℓ` box, `{0, ..., ℓ - 1}^d`. -/
def offsets (d N ℓ : ℕ) : Finset (Torus d N) :=
  Fintype.piFinset fun _ => (range ℓ).image (fun n : ℕ => (n : ZMod N))

/-- The box `b + K`. -/
def boxes (ℓ : ℕ) (b : Torus d N) : Finset (Torus d N) := (offsets d N ℓ).image (b + ·)

theorem mem_boxes {ℓ : ℕ} {b y : Torus d N} : y ∈ boxes ℓ b ↔ y - b ∈ offsets d N ℓ := by
  simp only [boxes, mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩; simpa using hk
  · intro h; exact ⟨y - b, h, by abel⟩

theorem card_boxes (ℓ : ℕ) (b : Torus d N) : (boxes ℓ b).card = (offsets d N ℓ).card :=
  card_image_of_injective _ (add_right_injective b)

/-- **Every site is covered `|K|` times.** -/
theorem coverage_boxes (ℓ : ℕ) (z : Torus d N) : coverage (boxes (d := d) (N := N) ℓ) z = (offsets d N ℓ).card := by
  have h : (univ.filter fun b => z ∈ boxes ℓ b) = (offsets d N ℓ).image (fun k => z - k) := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_boxes, mem_image]
    constructor
    · intro hb; exact ⟨z - b, hb, by abel⟩
    · rintro ⟨k, hk, rfl⟩; simpa using hk
  rw [coverage, h, card_image_of_injective _ (sub_right_injective)]

theorem offsets_nonempty {ℓ : ℕ} (hℓ : 0 < ℓ) : (offsets d N ℓ).Nonempty :=
  ⟨0, Fintype.mem_piFinset.mpr fun _ => mem_image.mpr ⟨0, mem_range.mpr hℓ, Nat.cast_zero⟩⟩

/-- Two offsets are at distance at most `d ℓ`. -/
theorem tdist_offsets_le {ℓ : ℕ} {k k' : Torus d N} (hk : k ∈ offsets d N ℓ) (hk' : k' ∈ offsets d N ℓ) :
    tdist k k' ≤ d * ℓ := by
  have hi : ∀ i, ((k i - k' i).valMinAbs.natAbs : ℝ) ≤ ℓ := by
    intro i
    obtain ⟨a, ha, hai⟩ := mem_image.mp (Fintype.mem_piFinset.mp hk i)
    obtain ⟨b, hb, hbi⟩ := mem_image.mp (Fintype.mem_piFinset.mp hk' i)
    have ha' := mem_range.mp ha
    have hb' := mem_range.mp hb
    have hab : ((a : ℤ) - (b : ℤ)).natAbs ≤ ℓ := by omega
    have h := natAbs_valMinAbs_sub_le_of_cast (N := N) (a : ℤ) (b : ℤ) hab
    rw [← hai, ← hbi]
    push_cast at h ⊢
    exact_mod_cast h
  calc tdist k k' ≤ ∑ _i : Fin d, (ℓ : ℝ) := sum_le_sum fun i _ => hi i
    _ = d * ℓ := by simp

/-- **The diameter of a box** is at most `d ℓ`. -/
theorem tdist_boxes_le {ℓ : ℕ} {b y y' : Torus d N} (hy : y ∈ boxes ℓ b) (hy' : y' ∈ boxes ℓ b) :
    tdist y y' ≤ d * ℓ := by
  have h := tdist_offsets_le (mem_boxes.mp hy) (mem_boxes.mp hy')
  simpa [tdist, sub_sub_sub_cancel_right] using h

/-- The sites within distance `R` of `z`. -/
def ball (z : Torus d N) (R : ℕ) : Finset (Torus d N) := univ.filter fun y => tdist z y ≤ R

theorem card_ball_le (z : Torus d N) (R : ℕ) : (ball z R).card ≤ (2 * R + 1) ^ d := by
  have hsub : ball z R ⊆ Fintype.piFinset fun i => (Icc (-(R : ℤ)) R).image (fun t : ℤ => z i + (t : ZMod N)) := by
    intro y hy
    have hy' : tdist z y ≤ R := (mem_filter.mp hy).2
    refine Fintype.mem_piFinset.mpr fun i => mem_image.mpr ?_
    have hle : ((z i - y i).valMinAbs.natAbs : ℝ) ≤ R :=
      (single_le_sum (f := fun j => ((z j - y j).valMinAbs.natAbs : ℝ)) (fun j _ => Nat.cast_nonneg _)
        (mem_univ i)).trans hy'
    have hle' : (z i - y i).valMinAbs.natAbs ≤ R := by exact_mod_cast hle
    refine ⟨-(z i - y i).valMinAbs, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    push_cast
    ring
  calc (ball z R).card ≤ _ := card_le_card hsub
    _ = ∏ i, ((Icc (-(R : ℤ)) R).image (fun t : ℤ => z i + (t : ZMod N))).card := Fintype.card_piFinset _
    _ ≤ ∏ _i : Fin d, (2 * R + 1) := by
        gcongr with i _
        refine card_image_le.trans ?_
        rw [Int.card_Icc]
        omega
    _ = (2 * R + 1) ^ d := by simp

open Classical in
/-- The range weight: `1` if the box `b + K` comes within distance `R` of `z`, else `0`. -/
def nearW (ℓ R : ℕ) (b z : Torus d N) : ℝ := if ∃ y ∈ boxes ℓ b, tdist z y ≤ R then 1 else 0

/-- **At most `(2R + 1)^d |K|` boxes come within distance `R` of a site.** -/
theorem card_near_le (ℓ R : ℕ) (z : Torus d N) :
    (univ.filter fun b => nearW ℓ R b z ≠ 0).card ≤ (2 * R + 1) ^ d * (offsets d N ℓ).card := by
  have hsub : (univ.filter fun b => nearW ℓ R b z ≠ 0) ⊆ (ball z R ×ˢ offsets d N ℓ).image (fun p => p.1 - p.2) := by
    intro b hb
    have hb' : nearW ℓ R b z ≠ 0 := (mem_filter.mp hb).2
    simp only [nearW, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hb'
    obtain ⟨y, hy, hyz⟩ := hb'
    refine mem_image.mpr ⟨(y, y - b), mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _, hyz⟩, mem_boxes.mp hy⟩, ?_⟩
    simp
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (ball z R ×ˢ offsets d N ℓ).card := card_image_le
    _ = (ball z R).card * (offsets d N ℓ).card := card_product _ _
    _ ≤ (2 * R + 1) ^ d * (offsets d N ℓ).card := Nat.mul_le_mul_right _ (card_ball_le z R)

/-- **`hcount` on the torus** for the box family and the range weight `nearW`. -/
theorem torus_hcount (ℓ R : ℕ) (good : Finset (Torus d N)) {lam : ℝ} (hlam : 0 ≤ lam) (z : Torus d N) :
    ∑ b ∈ good.filter (fun b => z ∉ boxes ℓ b), ∑ y ∈ boxes ℓ b, nearW ℓ R b z * Real.exp (lam * tdist z y) ≤
      (2 * R + 1 : ℝ) ^ d * (offsets d N ℓ).card * Real.exp (lam * (R + d * ℓ)) * coverage (boxes ℓ) z := by
  have h := hcount_of_range (boxes ℓ) good tdist (nearW ℓ R) hlam (W₀ := 1) (V := (offsets d N ℓ).card)
    (D := R + d * ℓ) (A := (2 * R + 1 : ℝ) ^ d) zero_le_one (Nat.cast_nonneg _)
    (fun b z => by unfold nearW; split_ifs <;> norm_num)
    (fun b => by rw [card_boxes])
    (fun b z hw y hy => by
      simp only [nearW, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hw
      obtain ⟨y₀, hy₀, hzy₀⟩ := hw
      calc tdist z y ≤ tdist z y₀ + tdist y₀ y := tdist_triangle _ _ _
        _ ≤ R + d * ℓ := add_le_add hzy₀ (tdist_boxes_le hy₀ hy))
    (fun z => by
      rw [coverage_boxes]
      exact_mod_cast card_near_le ℓ R z) z
  simpa [mul_one] using h

end Torus

end ProofPhase.ScaleHypKit
