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

end MinArea
