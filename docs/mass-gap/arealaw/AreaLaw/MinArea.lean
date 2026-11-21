/-
Minimal area (area-law project, step P5 of BLUEPRINT.md, 2026-11-21). Released under Apache 2.0.

# A plaquette set closing a rectangle mod 2 has at least the minimal area

Project to the (μ, ν) torus. Summing the parity condition over all μ-links (resp. ν-links) above one cell, plaquettes in other planes
cancel in pairs and the (μ, ν)-plaquettes give `cellPar (i, j) + cellPar (i, j - 1)` (resp. `(i - 1, j)`); the rectangle gives the same
for the indicator of its R × T cells (`strip`). So the `defect` (cell parity plus indicator) is invariant under both unit shifts, hence
constant on the torus, and the cells of odd parity are either the rectangle's cells or their complement. Each such cell holds a
plaquette of `O`.

## Main results

- `rect_parity_area_of_le`: the bound for `R, T ≤ N`, `[NeZero N]`.
- `rect_parity_area`: the statement used by the assembly (`1 ≤ R, T`, `R, T < N`).
-/

import AreaLaw.CentreSymmetry

noncomputable section

open Finset

namespace MinArea

variable {d N : ℕ}

theorem z2_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> decide

theorem z2_two : (2 : ZMod 2) = 0 := by decide

/-! ## Counting steps whose link satisfies a predicate, mod 2 -/

/-- Number of steps of `L` whose link satisfies `Q`, mod 2. -/
def cnt (Q : LatticeLink d N → Prop) [DecidablePred Q] (L : List (PathStep d N)) : ZMod 2 :=
  ((L.countP (fun s => Q s.link) : ℕ) : ZMod 2)

theorem cnt_nil (Q : LatticeLink d N → Prop) [DecidablePred Q] : cnt Q ([] : List (PathStep d N)) = 0 := by
  simp [cnt]

theorem cnt_cons (Q : LatticeLink d N → Prop) [DecidablePred Q] (s : PathStep d N) (L : List (PathStep d N)) :
    cnt Q (s :: L) = (if Q s.link then 1 else 0) + cnt Q L := by
  simp only [cnt, List.countP_cons]
  split_ifs <;> simp_all [add_comm]

theorem cnt_append (Q : LatticeLink d N → Prop) [DecidablePred Q] (L M : List (PathStep d N)) :
    cnt Q (L ++ M) = cnt Q L + cnt Q M := by
  simp [cnt, List.countP_append]

theorem cnt_straightFwd (Q : LatticeLink d N → Prop) [DecidablePred Q] (μ : Fin d) (k : ℕ) :
    ∀ y : FinLatticeSites d N,
      cnt Q (straightFwd y μ k) = ∑ m ∈ range k, if Q ⟨siteShiftN y μ m, μ⟩ then 1 else 0 := by
  induction k with
  | zero => intro y; simp [straightFwd, cnt_nil]
  | succ k ih =>
    intro y
    rw [straightFwd, cnt_cons, ih, Finset.sum_range_succ']
    simp only [siteShiftN_succ', siteShiftN_zero]
    ring

theorem cnt_straightBwd (Q : LatticeLink d N → Prop) [DecidablePred Q] (μ : Fin d) (k : ℕ) :
    ∀ y : FinLatticeSites d N,
      cnt Q (straightBwd y μ k) = ∑ m ∈ range k, if Q ⟨siteShiftN y μ m, μ⟩ then 1 else 0 := by
  induction k with
  | zero => intro y; simp [straightBwd, cnt_nil]
  | succ k ih =>
    intro y
    rw [straightBwd, cnt_append, ih, cnt_cons, cnt_nil, Finset.sum_range_succ']
    simp only [siteShiftN_succ', siteShiftN_zero]
    ring

theorem cnt_rectPath (Q : LatticeLink d N → Prop) [DecidablePred Q] (x : FinLatticeSites d N) (μ ν : Fin d)
    (R T : ℕ) :
    cnt Q (rectPath x μ ν R T) =
      (∑ m ∈ range R, if Q ⟨siteShiftN x μ m, μ⟩ then 1 else 0) +
      (∑ m ∈ range T, if Q ⟨siteShiftN (siteShiftN x μ R) ν m, ν⟩ then 1 else 0) +
      (∑ m ∈ range R, if Q ⟨siteShiftN (siteShiftN x ν T) μ m, μ⟩ then 1 else 0) +
      (∑ m ∈ range T, if Q ⟨siteShiftN x ν m, ν⟩ then 1 else 0) := by
  simp only [rectPath, cnt_append, cnt_straightFwd, cnt_straightBwd]

theorem cnt_plaquettePath (Q : LatticeLink d N → Prop) [DecidablePred Q] (p : LatticePlaquette d N) :
    cnt Q (plaquettePath p) =
      (if Q (p.boundaryLinks 0) then 1 else 0) + (if Q (p.boundaryLinks 1) then 1 else 0) +
      (if Q (p.boundaryLinks 2) then 1 else 0) + (if Q (p.boundaryLinks 3) then 1 else 0) := by
  simp only [plaquettePath, cnt_cons, cnt_nil]
  ring

/-! ## Summing the parity condition over a fibre of links -/

theorem sum_visits_fibre (F : Finset (FinLatticeSites d N)) (ρ : Fin d) (L : List (PathStep d N)) :
    ∑ y ∈ F, visits ⟨y, ρ⟩ L = L.countP (fun s => s.link.dir = ρ ∧ s.link.site ∈ F) := by
  induction L with
  | nil => simp [visits]
  | cons s L ih =>
    simp only [visits, List.countP_cons] at ih ⊢
    rw [Finset.sum_add_distrib, ih]
    congr 1
    obtain ⟨⟨z, σ⟩, f⟩ := s
    by_cases hσ : σ = ρ
    · subst hσ; simp [Finset.sum_ite_eq]
    · simp [hσ]

theorem fibre_parity (C : List (PathStep d N)) (O : Finset (LatticePlaquette d N))
    (hpar : ∀ ℓ : LatticeLink d N, Even (visits ℓ C + plaqVisits ℓ O))
    (ρ : Fin d) (F : Finset (FinLatticeSites d N)) :
    cnt (fun ℓ => ℓ.dir = ρ ∧ ℓ.site ∈ F) C +
      ∑ p ∈ O, cnt (fun ℓ => ℓ.dir = ρ ∧ ℓ.site ∈ F) (plaquettePath p) = 0 := by
  have h : ((∑ y ∈ F, (visits ⟨y, ρ⟩ C + plaqVisits ⟨y, ρ⟩ O) : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_sum]
    exact Finset.sum_eq_zero fun y _ => ZMod.natCast_eq_zero_iff_even.mpr (hpar _)
  have e1 : ∑ y ∈ F, plaqVisits ⟨y, ρ⟩ O =
      ∑ p ∈ O, (plaquettePath p).countP (fun s => s.link.dir = ρ ∧ s.link.site ∈ F) := by
    simp only [plaqVisits]
    rw [Finset.sum_comm]
    simp only [sum_visits_fibre]
  rw [Finset.sum_add_distrib, sum_visits_fibre, e1] at h
  simpa [cnt, Nat.cast_sum] using h

/-! ## The (μ, ν)-projection -/

/-- Sites over the cell `(i, j)` of the (μ, ν) torus. -/
def fibre [NeZero N] (μ ν : Fin d) (i j : ZMod N) : Finset (FinLatticeSites d N) :=
  univ.filter (fun y => y μ = i ∧ y ν = j)

theorem mem_fibre [NeZero N] {μ ν : Fin d} {i j : ZMod N} {y : FinLatticeSites d N} :
    y ∈ fibre μ ν i j ↔ y μ = i ∧ y ν = j := by
  simp [fibre]

/-- Parity of the number of (μ, ν)-plaquettes of `O` over the cell `(i, j)`. -/
def cellPar (O : Finset (LatticePlaquette d N)) (μ ν : Fin d) (i j : ZMod N) : ZMod 2 :=
  ((O.filter (fun p => p.dir1 = μ ∧ p.dir2 = ν ∧ p.site μ = i ∧ p.site ν = j)).card : ZMod 2)

theorem cnt_plaq_mu [NeZero N] {μ ν : Fin d} (hμν : μ < ν) (i j : ZMod N) (p : LatticePlaquette d N) :
    cnt (fun ℓ => ℓ.dir = μ ∧ ℓ.site ∈ fibre μ ν i j) (plaquettePath p) =
      (if p.dir1 = μ ∧ p.dir2 = ν ∧ p.site μ = i ∧ p.site ν = j then 1 else 0) +
      (if p.dir1 = μ ∧ p.dir2 = ν ∧ p.site μ = i ∧ p.site ν = j - 1 then 1 else 0) := by
  obtain ⟨s, a, b, hab⟩ := p
  rw [cnt_plaquettePath]
  simp only [LatticePlaquette.boundaryLinks, mem_fibre, siteShift, Function.update_apply, eq_sub_iff_add_eq]
  have hνμ : ν ≠ μ := ne_of_gt hμν
  by_cases ha : a = μ
  · subst ha
    have hba : b ≠ a := ne_of_gt hab
    by_cases hb : b = ν
    · subst hb
      simp [hba, Ne.symm hba]
    · simp [hba, Ne.symm hba, hb, Ne.symm hb, z2_add_self]
  · by_cases hb : b = μ
    · subst hb
      have haν : a ≠ ν := fun h => absurd (h ▸ hab) (not_lt.mpr hμν.le)
      simp [ha, Ne.symm ha, Ne.symm haν, z2_add_self]
    · simp [ha, hb]

theorem cnt_plaq_nu [NeZero N] {μ ν : Fin d} (hμν : μ < ν) (i j : ZMod N) (p : LatticePlaquette d N) :
    cnt (fun ℓ => ℓ.dir = ν ∧ ℓ.site ∈ fibre μ ν i j) (plaquettePath p) =
      (if p.dir1 = μ ∧ p.dir2 = ν ∧ p.site μ = i ∧ p.site ν = j then 1 else 0) +
      (if p.dir1 = μ ∧ p.dir2 = ν ∧ p.site μ = i - 1 ∧ p.site ν = j then 1 else 0) := by
  obtain ⟨s, a, b, hab⟩ := p
  rw [cnt_plaquettePath]
  simp only [LatticePlaquette.boundaryLinks, mem_fibre, siteShift, Function.update_apply, eq_sub_iff_add_eq]
  have hνμ : ν ≠ μ := ne_of_gt hμν
  by_cases hb : b = ν
  · subst hb
    have hab' : a ≠ b := ne_of_lt hab
    by_cases ha : a = μ
    · subst ha
      simp [hab', Ne.symm hab']
      split_ifs <;> simp_all
    · simp [hab', Ne.symm hab', ha, Ne.symm ha, z2_add_self]
  · by_cases ha : a = ν
    · subst ha
      have hbμ : b ≠ μ := fun h => absurd (h ▸ hab) (not_lt.mpr hμν.le)
      simp [hb, Ne.symm hb, Ne.symm hbμ, hνμ, z2_add_self]
    · simp [ha, hb]

/-! ## Strips: the projection of the rectangle -/

/-- Number of `m < K` with `a + m = i`, mod 2. -/
def strip (a : ZMod N) (K : ℕ) (i : ZMod N) : ZMod 2 :=
  ∑ m ∈ range K, if a + (m : ZMod N) = i then 1 else 0

theorem strip_telescope (a : ZMod N) (K : ℕ) (j : ZMod N) :
    strip a K j + strip a K (j - 1) = (if a = j then 1 else 0) + (if a + (K : ZMod N) = j then 1 else 0) := by
  induction K with
  | zero => simp [strip, z2_add_self]
  | succ K ih =>
    simp only [strip, Finset.sum_range_succ] at ih ⊢
    have e : (a + (K : ZMod N) = j - 1) ↔ (a + ((K + 1 : ℕ) : ZMod N) = j) := by
      push_cast; rw [eq_sub_iff_add_eq, add_assoc]
    simp only [e]
    linear_combination ih + z2_add_self (if a + (K : ZMod N) = j then (1 : ZMod 2) else 0)

theorem strip_inj (a : ZMod N) {K : ℕ} (hK : K ≤ N) :
    Set.InjOn (fun m : ℕ => a + (m : ZMod N)) ↑(range K) := by
  intro m hm m' hm' h
  simp only [coe_range, Set.mem_Iio] at hm hm'
  have h' : (m : ZMod N) = m' := add_left_cancel h
  rw [ZMod.natCast_eq_natCast_iff'] at h'
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'

/-- The cells of a strip. -/
def stripSet (a : ZMod N) (K : ℕ) : Finset (ZMod N) := (range K).image (fun m : ℕ => a + (m : ZMod N))

theorem strip_eq (a : ZMod N) {K : ℕ} (hK : K ≤ N) (i : ZMod N) :
    strip a K i = if i ∈ stripSet a K then 1 else 0 := by
  have := Finset.sum_image (f := fun k => if k = i then (1 : ZMod 2) else 0) (strip_inj a hK)
  rw [Finset.sum_ite_eq'] at this
  rw [strip, stripSet, this]

theorem card_stripSet (a : ZMod N) {K : ℕ} (hK : K ≤ N) : (stripSet a K).card = K := by
  rw [stripSet, Finset.card_image_of_injOn (strip_inj a hK), card_range]

/-! ## What the rectangle visits over a cell -/

theorem card_filter_and_const {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (Q : Prop) [Decidable Q] :
    ((s.filter (fun a => P a ∧ Q)).card : ZMod 2) = if Q then ((s.filter P).card : ZMod 2) else 0 := by
  by_cases hQ : Q <;> simp [hQ]

theorem card_filter_const_and {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] (Q : Prop) [Decidable Q] :
    ((s.filter (fun a => Q ∧ P a)).card : ZMod 2) = if Q then ((s.filter P).card : ZMod 2) else 0 := by
  by_cases hQ : Q <;> simp [hQ]

theorem cnt_rect_mu [NeZero N] (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) (R T : ℕ) (i j : ZMod N) :
    cnt (fun ℓ => ℓ.dir = μ ∧ ℓ.site ∈ fibre μ ν i j) (rectPath x μ ν R T) =
      strip (x μ) R i * ((if x ν = j then 1 else 0) + (if x ν + (T : ZMod N) = j then 1 else 0)) := by
  rw [cnt_rectPath]
  simp [mem_fibre, siteShiftN, hμν, Ne.symm hμν, strip, mul_add]
  simp only [card_filter_and_const]

theorem cnt_rect_nu [NeZero N] (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) (R T : ℕ) (i j : ZMod N) :
    cnt (fun ℓ => ℓ.dir = ν ∧ ℓ.site ∈ fibre μ ν i j) (rectPath x μ ν R T) =
      ((if x μ = i then 1 else 0) + (if x μ + (R : ZMod N) = i then 1 else 0)) * strip (x ν) T j := by
  rw [cnt_rectPath]
  simp [mem_fibre, siteShiftN, hμν, Ne.symm hμν, strip, add_mul]
  simp only [card_filter_const_and]
  ring

/-- The defect: cell parity plus the indicator of the rectangle's cells. -/
def defect (x : FinLatticeSites d N) (μ ν : Fin d) (R T : ℕ) (O : Finset (LatticePlaquette d N)) (i j : ZMod N) :
    ZMod 2 :=
  cellPar O μ ν i j + strip (x μ) R i * strip (x ν) T j

theorem defect_def (x : FinLatticeSites d N) (μ ν : Fin d) (R T : ℕ) (O : Finset (LatticePlaquette d N)) (i j : ZMod N) :
    defect x μ ν R T O i j = cellPar O μ ν i j + strip (x μ) R i * strip (x ν) T j := rfl

/-! ## The cell equations -/

section CellEquations

variable [NeZero N] (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ < ν) (R T : ℕ)
  (O : Finset (LatticePlaquette d N))
  (hpar : ∀ ℓ : LatticeLink d N, Even (visits ℓ (rectPath x μ ν R T) + plaqVisits ℓ O))
include hμν hpar

/-- Summing the parity condition over the μ-links above the cell `(i, j)`. -/
theorem cell_eq_mu (i j : ZMod N) :
    strip (x μ) R i * (strip (x ν) T j + strip (x ν) T (j - 1)) + cellPar O μ ν i j + cellPar O μ ν i (j - 1) = 0 := by
  have h := fibre_parity _ O hpar μ (fibre μ ν i j)
  rw [cnt_rect_mu x hμν.ne, Finset.sum_congr rfl (fun p _ => cnt_plaq_mu hμν i j p), Finset.sum_add_distrib,
    Finset.sum_boole, Finset.sum_boole] at h
  rw [strip_telescope]
  simpa [cellPar, add_assoc] using h

/-- Summing the parity condition over the ν-links above the cell `(i, j)`. -/
theorem cell_eq_nu (i j : ZMod N) :
    (strip (x μ) R i + strip (x μ) R (i - 1)) * strip (x ν) T j + cellPar O μ ν i j + cellPar O μ ν (i - 1) j = 0 := by
  have h := fibre_parity _ O hpar ν (fibre μ ν i j)
  rw [cnt_rect_nu x hμν.ne, Finset.sum_congr rfl (fun p _ => cnt_plaq_nu hμν i j p), Finset.sum_add_distrib,
    Finset.sum_boole, Finset.sum_boole] at h
  rw [strip_telescope]
  simpa [cellPar, add_assoc] using h

theorem defect_succ_nu (i j : ZMod N) : defect x μ ν R T O i (j + 1) = defect x μ ν R T O i j := by
  have h := cell_eq_mu x hμν R T O hpar i (j + 1)
  rw [add_sub_cancel_right] at h
  simp only [defect_def]
  linear_combination h - (cellPar O μ ν i j + strip (x μ) R i * strip (x ν) T j) * z2_two

theorem defect_succ_mu (i j : ZMod N) : defect x μ ν R T O (i + 1) j = defect x μ ν R T O i j := by
  have h := cell_eq_nu x hμν R T O hpar (i + 1) j
  rw [add_sub_cancel_right] at h
  simp only [defect_def]
  linear_combination h - (cellPar O μ ν i j + strip (x μ) R i * strip (x ν) T j) * z2_two

end CellEquations

/-- On the cycle `ZMod N` a function invariant under `+1` is constant. -/
theorem const_of_succ [NeZero N] {α : Type*} (f : ZMod N → α) (hf : ∀ t, f (t + 1) = f t) (t : ZMod N) :
    f t = f 0 := by
  rw [← ZMod.natCast_zmod_val t]
  generalize t.val = n
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, hf, ih]

/-! ## Counting -/

/-- Each cell of odd parity holds at least one (μ, ν)-plaquette of `O`. -/
theorem card_cells_le [NeZero N] (O : Finset (LatticePlaquette d N)) (μ ν : Fin d) :
    (univ.filter (fun c : ZMod N × ZMod N => cellPar O μ ν c.1 c.2 = 1)).card ≤
      (O.filter (fun p => p.dir1 = μ ∧ p.dir2 = ν)).card := by
  rw [Finset.card_filter, Finset.card_eq_sum_card_fiberwise (s := O.filter (fun p => p.dir1 = μ ∧ p.dir2 = ν))
    (f := fun p => (p.site μ, p.site ν)) (t := univ) (fun _ _ => by simp)]
  apply Finset.sum_le_sum
  intro c _
  split_ifs with h
  · rw [Nat.one_le_iff_ne_zero]
    intro h0
    have e : (O.filter (fun p => p.dir1 = μ ∧ p.dir2 = ν)).filter (fun p => (p.site μ, p.site ν) = c) =
        O.filter (fun p => p.dir1 = μ ∧ p.dir2 = ν ∧ p.site μ = c.1 ∧ p.site ν = c.2) := by
      ext p; simp [Prod.ext_iff, and_assoc]
    rw [e] at h0
    simp [cellPar, h0] at h
  · exact Nat.zero_le _

end MinArea

open MinArea in
/-- **Minimal area (P5), general form.** If the plaquette set `O` closes the rectangle `rectPath x μ ν R T` mod 2, with
    `R, T ≤ N`, then `O` holds at least `min (R T) (N² − R T)` plaquettes in the plane (μ, ν). -/
theorem rect_parity_area_of_le {d N : ℕ} [NeZero N] (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ < ν) (R T : ℕ)
    (hRN : R ≤ N) (hTN : T ≤ N) (O : Finset (LatticePlaquette d N))
    (hpar : ∀ ℓ : LatticeLink d N, Even (visits ℓ (rectPath x μ ν R T) + plaqVisits ℓ O)) :
    min (R * T) (N * N - R * T) ≤ (O.filter (fun p => p.dir1 = μ ∧ p.dir2 = ν)).card := by
  have hc := card_cells_le O μ ν
  have hD : ∀ i j, defect x μ ν R T O i j = defect x μ ν R T O 0 0 := by
    intro i j
    rw [const_of_succ (fun j => defect x μ ν R T O i j)
        (fun t => defect_succ_nu x hμν R T O hpar i t) j,
      const_of_succ (fun i => defect x μ ν R T O i 0)
        (fun t => defect_succ_mu x hμν R T O hpar t 0) i]
  have hA : ∀ i j, cellPar O μ ν i j = defect x μ ν R T O 0 0 +
      (if i ∈ stripSet (x μ) R then 1 else 0) * (if j ∈ stripSet (x ν) T then 1 else 0) := by
    intro i j
    rw [← hD i j, ← strip_eq (x μ) hRN i, ← strip_eq (x ν) hTN j, defect_def]
    rw [add_assoc, z2_add_self, add_zero]
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (defect x μ ν R T O 0 0) with h0 | h1
  · have e : univ.filter (fun c : ZMod N × ZMod N => cellPar O μ ν c.1 c.2 = 1) =
        stripSet (x μ) R ×ˢ stripSet (x ν) T := by
      ext c
      simp only [mem_filter, mem_univ, true_and, mem_product, hA, h0, zero_add]
      split_ifs <;> simp_all
    rw [e, card_product, card_stripSet _ hRN, card_stripSet _ hTN] at hc
    exact le_trans (min_le_left _ _) hc
  · have e : univ.filter (fun c : ZMod N × ZMod N => cellPar O μ ν c.1 c.2 = 1) =
        (stripSet (x μ) R ×ˢ stripSet (x ν) T)ᶜ := by
      ext c
      simp only [mem_filter, mem_univ, true_and, mem_compl, mem_product, hA, h1]
      split_ifs <;> simp_all
    rw [e, card_compl, card_product, card_stripSet _ hRN, card_stripSet _ hTN, Fintype.card_prod,
      ZMod.card] at hc
    exact le_trans (min_le_right _ _) hc

set_option linter.unusedVariables false in
/-- **Minimal area (P5).** If the plaquette set `O` closes the rectangle `rectPath x μ ν R T` mod 2, then `O` holds at least
    `min (R T) (N² − R T)` plaquettes in the plane (μ, ν). (The bounds `1 ≤ R, T` are not needed; see
    `rect_parity_area_of_le`.) -/
theorem rect_parity_area {d N : ℕ} (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < N) (hTN : T < N)
    (O : Finset (LatticePlaquette d N))
    (hpar : ∀ ℓ : LatticeLink d N, Even (visits ℓ (rectPath x μ ν R T) + plaqVisits ℓ O)) :
    min (R * T) (N * N - R * T) ≤ (O.filter (fun p => p.dir1 = μ ∧ p.dir2 = ν)).card := by
  have : NeZero N := ⟨by omega⟩
  exact rect_parity_area_of_le x hμν R T hRN.le hTN.le O hpar

-- #print axioms rect_parity_area  -- checked: [propext, Classical.choice, Quot.sound]
