/-
Proof phase, generalisation phase 1: the counting layer in the lattice dimension `d` (2026-11-23).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`.
-/

import OneScale.LinkDist

/-!
# Counting in dimension `d`

In the Lean proof `d = 4` enters only as lattice counting (`GENERALISE-AUDIT.md`, finding 1). This file proves the
`d`-versions of those counting facts; the old `d = 4` statements are re-derived from them in
`ProofPhase.General.Instances`.

* `card_filter_siteDist_le_one`: at most `3 ^ d` sites within distance `1` of the origin.
* `card_le_of_siteDist`: a set of links of `ℓ^∞` diameter `≤ r` has at most `d * (2r + 1) ^ d` elements.
* `poly_exp_le`, `poly_exp_bound`: the tail sum `(1 + x)^d e^{-2ax} ≤ (d!/a^d) e^a e^{-ax}`.
-/

open Finset OneScale.LinkDist

open scoped Classical

noncomputable section

namespace ProofPhase.General

/-! ## The polynomial-times-exponential tail -/

/-- **The `d`-dimensional growth tail.** `(1 + x)^d e^{-2ax} ≤ (d!/a^d) e^a e^{-ax}`; the old `d = 4` bound has the
constant `24 = 4!`. -/
theorem poly_exp_le (d : ℕ) {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    (1 + x) ^ d * Real.exp (-(2 * a * x)) ≤
      (Nat.factorial d : ℝ) / a ^ d * Real.exp a * Real.exp (-(a * x)) := by
  have h := Real.pow_div_factorial_le_exp (a * (1 + x)) (by positivity) d
  have hf : (0 : ℝ) < (Nat.factorial d : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have ha' : (0 : ℝ) < a ^ d := by positivity
  have h4 : (1 + x) ^ d ≤ Real.exp (a * (1 + x)) * ((Nat.factorial d : ℝ) / a ^ d) := by
    calc (1 + x) ^ d = (a * (1 + x)) ^ d / (Nat.factorial d : ℝ) * ((Nat.factorial d : ℝ) / a ^ d) := by
          rw [mul_pow]; field_simp
      _ ≤ Real.exp (a * (1 + x)) * ((Nat.factorial d : ℝ) / a ^ d) := by gcongr
  calc (1 + x) ^ d * Real.exp (-(2 * a * x))
      ≤ Real.exp (a * (1 + x)) * ((Nat.factorial d : ℝ) / a ^ d) * Real.exp (-(2 * a * x)) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = (Nat.factorial d : ℝ) / a ^ d * (Real.exp (a * (1 + x)) * Real.exp (-(2 * a * x))) := by ring
    _ = (Nat.factorial d : ℝ) / a ^ d * Real.exp a * Real.exp (-(a * x)) := by
        rw [mul_assoc ((Nat.factorial d : ℝ) / a ^ d) (Real.exp a), ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-- **A bounded form of the same tail**: `(1 + x)^d e^{-rx} ≤ d! e^r / r^d` for `x ≥ 0`. -/
theorem poly_exp_bound (d : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → (1 + x) ^ d * Real.exp (-(r * x)) ≤ C := by
  refine ⟨(Nat.factorial d : ℝ) * Real.exp r / r ^ d, by positivity, fun x hx => ?_⟩
  have h := Real.pow_div_factorial_le_exp (x := r * (1 + x)) (by positivity) d
  have hf : (0 : ℝ) < (Nat.factorial d : ℝ) := by exact_mod_cast Nat.factorial_pos d
  rw [mul_pow, div_le_iff₀ hf] at h
  have hsplit : Real.exp (r * (1 + x)) = Real.exp r * Real.exp (r * x) := by rw [← Real.exp_add]; ring_nf
  have hinv : Real.exp (r * x) * Real.exp (-(r * x)) = 1 := by rw [← Real.exp_add]; simp
  rw [hsplit] at h
  rw [le_div_iff₀ (by positivity)]
  have he := Real.exp_pos (-(r * x))
  calc (1 + x) ^ d * Real.exp (-(r * x)) * r ^ d = (r ^ d * (1 + x) ^ d) * Real.exp (-(r * x)) := by ring
    _ ≤ (Real.exp r * Real.exp (r * x) * (Nat.factorial d : ℝ)) * Real.exp (-(r * x)) :=
        mul_le_mul_of_nonneg_right h he.le
    _ = (Nat.factorial d : ℝ) * Real.exp r * (Real.exp (r * x) * Real.exp (-(r * x))) := by ring
    _ = (Nat.factorial d : ℝ) * Real.exp r := by rw [hinv, mul_one]

/-! ## Counting sites and links -/

section Sites

variable {d N : ℕ} [NeZero N]

/-- A residue at cyclic distance `≤ 1` from `0` is `0`, `1` or `-1`. -/
theorem eq_of_cyc_le_one {a : ZMod N} (h : cyc a ≤ 1) : a = 0 ∨ a = 1 ∨ a = -1 := by
  rw [cyc_eq_min] at h
  have hlt := ZMod.val_lt a
  have ha : ((a.val : ℕ) : ZMod N) = a := ZMod.natCast_zmod_val a
  rcases min_le_iff.1 h with h1 | h1
  · rcases (by omega : a.val = 0 ∨ a.val = 1) with hv | hv
    · left; rw [← ha, hv]; simp
    · right; left; rw [← ha, hv]; simp
  · right; right
    have h3 : a.val = N - 1 := by omega
    rw [← ha, h3, Nat.cast_sub (by omega : 1 ≤ N)]
    simp

/-- **Neighbours**: at most `3 ^ d` sites are within distance `1` of the origin. -/
theorem card_near_le :
    (univ.filter (fun u : FinLatticeSites d N => siteDist u 0 ≤ 1)).card ≤ 3 ^ d := by
  let g : (Fin d → Fin 3) → FinLatticeSites d N := fun v i => ![(0 : ZMod N), 1, -1] (v i)
  have hsub : univ.filter (fun u : FinLatticeSites d N => siteDist u 0 ≤ 1) ⊆ univ.image g := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    have : ∀ i, ∃ j : Fin 3, ![(0 : ZMod N), 1, -1] j = u i := by
      intro i
      have hi : cyc (u i - (0 : FinLatticeSites d N) i) ≤ 1 := (cyc_le_siteDist _ _ i).trans hu
      simp only [Pi.zero_apply, sub_zero] at hi
      rcases eq_of_cyc_le_one hi with h | h | h
      · exact ⟨0, by simp [h]⟩
      · exact ⟨1, by simp [h]⟩
      · exact ⟨2, by simp [h]⟩
    choose v hv using this
    exact mem_image.2 ⟨v, mem_univ _, funext hv⟩
  calc _ ≤ (univ.image g).card := card_le_card hsub
    _ ≤ (univ : Finset (Fin d → Fin 3)).card := card_image_le
    _ = 3 ^ d := by simp

/-- **Boxes**: a set of links whose base sites are pairwise at `ℓ^∞` cyclic distance `≤ r` has at most
`d (2r + 1)^d` elements (independent of the torus). -/
theorem card_le_of_siteDist {A : Finset (LatticeLink d N)} {r : ℕ}
    (h : ∀ e ∈ A, ∀ e' ∈ A, siteDist e.site e'.site ≤ r) : A.card ≤ d * (2 * r + 1) ^ d := by
  rcases A.eq_empty_or_nonempty with hA | ⟨e₀, he₀⟩
  · simp [hA]
  set S : Finset ((Fin d → ℤ) × Fin d) :=
    Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) r) ×ˢ Finset.univ with hS
  have hsub : A ⊆ S.image (fun p => (⟨fun i => e₀.site i + ((p.1 i : ℤ) : ZMod N), p.2⟩ : LatticeLink d N)) := by
    intro e he
    refine Finset.mem_image.2 ⟨(fun i => (e.site i - e₀.site i).valMinAbs, e.dir), ?_, ?_⟩
    · refine Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun i => ?_, Finset.mem_univ _⟩
      have h1 : cyc (e.site i - e₀.site i) ≤ r := (cyc_le_siteDist _ _ i).trans (h e he e₀ he₀)
      have h2 : |(e.site i - e₀.site i).valMinAbs| ≤ (r : ℤ) := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast h1
      exact Finset.mem_Icc.2 (abs_le.1 h2)
    · obtain ⟨site, dir⟩ := e
      show LatticeLink.mk _ _ = LatticeLink.mk site dir
      congr 1
      funext i
      simp only [ZMod.coe_valMinAbs]
      ring
  have hI : (Finset.Icc (-(r : ℤ)) r).card = 2 * r + 1 := by rw [Int.card_Icc]; omega
  calc A.card ≤ (S.image _).card := Finset.card_le_card hsub
    _ ≤ S.card := Finset.card_image_le
    _ = d * (2 * r + 1) ^ d := by
      rw [hS, Finset.card_product, Fintype.card_piFinset, Finset.card_univ, Fintype.card_fin]
      simp only [hI, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      ring

end Sites

end ProofPhase.General
