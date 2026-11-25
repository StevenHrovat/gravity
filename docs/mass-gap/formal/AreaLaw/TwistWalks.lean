/-
Walks in a lattice layer, loop erasure and walk counts, for the centre-twist area law (area-law project, 2026-11-21).
Released under Apache 2.0.

Idea of the centre-twist area law as in B. G. Srivats, fisher-lorentz-formalization (`Confinement/AreaLaw.lean`) and
Osterwalder–Seiler 1978; this file is written independently, in this project's framework.

# Contents

* Abstract walks (`walkEnd`, `walkLabels`) for a step map and a labelling of steps, and **loop erasure** (`exists_nodup_walk`): if
  equal labels force the later step to end at an endpoint of the earlier one, every walk can be shortened to one with distinct
  labels, the same ends and labels among the old ones.
* Walks in the layer orthogonal to a direction `ν`: a move is a direction `ρ ≠ ν` and a sign (`Move`, `2 (d − 1)` of them); a move
  from `y` crosses the plaquette in the plane `(ν, ρ)` whose two `ν`-links start at `y` and at the next site (`mlab`). Loop erasure
  applies (`mlab_eq`); the `ν`-coordinate is constant; the `μ`-displacement is at most the length (`walkEnd_apply_disp`,
  `abs_sum_mdisp_le`), so a walk joining two sites `R` apart in direction `μ` on `ℤ/Nℤ` has length at least `min(R, N − R)`
  (`min_le_natAbs_of_cast_eq`).
* Counting: `listsUpTo` (all lists of length at most `k`) and `∑_{|l| ≥ r} p^{|l|} ≤ q^r / (1 − q)`, `q = |moves| · p`
  (`sum_listsUpTo_le`); the superset sum over survivors (`sum_surv_le`).
-/

import AreaLaw.Clustering

open Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace AreaLaw.Twist

/-! ## Abstract walks and loop erasure -/

section Abstract

variable {S M P : Type*} (step : S → M → S) (lab : S → M → P)

/-- Where a walk ends. -/
def walkEnd : S → List M → S
  | y, [] => y
  | y, m :: ms => walkEnd (step y m) ms

/-- The labels of the steps of a walk. -/
def walkLabels : S → List M → List P
  | _, [] => []
  | y, m :: ms => lab y m :: walkLabels (step y m) ms

theorem walkEnd_append (y : S) (a b : List M) : walkEnd step y (a ++ b) = walkEnd step (walkEnd step y a) b := by
  induction a generalizing y with
  | nil => rfl
  | cons m a ih => exact ih (step y m)

theorem walkLabels_append (y : S) (a b : List M) :
    walkLabels step lab y (a ++ b) = walkLabels step lab y a ++ walkLabels step lab (walkEnd step y a) b := by
  induction a generalizing y with
  | nil => rfl
  | cons m a ih => simp only [List.cons_append, walkLabels, ih, walkEnd]

theorem length_walkLabels (y : S) (ms : List M) : (walkLabels step lab y ms).length = ms.length := by
  induction ms generalizing y with
  | nil => rfl
  | cons m ms ih => simp [walkLabels, ih]

theorem exists_split_of_mem_walkLabels {x : P} : ∀ (y : S) (ms : List M), x ∈ walkLabels step lab y ms →
    ∃ a m b, ms = a ++ m :: b ∧ lab (walkEnd step y a) m = x
  | y, [], h => by simp [walkLabels] at h
  | y, m :: ms, h => by
    rcases List.mem_cons.mp h with h | h
    · exact ⟨[], m, ms, rfl, h.symm⟩
    · obtain ⟨a, m', b, rfl, hx⟩ := exists_split_of_mem_walkLabels (step y m) ms h
      exact ⟨m :: a, m', b, rfl, hx⟩

/-- **Loop erasure.** If equal labels force the later step to end at an endpoint of the earlier one, every walk has a shortcut
    with distinct labels, the same ends, and labels among the old ones. -/
theorem exists_nodup_walk
    (hlab : ∀ y m y' m', lab y m = lab y' m' → step y' m' = y ∨ step y' m' = step y m) :
    ∀ (ms : List M) (y : S), ∃ ms', walkEnd step y ms' = walkEnd step y ms ∧ (walkLabels step lab y ms').Nodup ∧
      ∀ x ∈ walkLabels step lab y ms', x ∈ walkLabels step lab y ms
  | [], y => ⟨[], rfl, List.nodup_nil, fun _ h => h⟩
  | m :: ms, y => by
    obtain ⟨ms'', he, hnd, hsub⟩ := exists_nodup_walk hlab ms (step y m)
    by_cases hmem : lab y m ∈ walkLabels step lab (step y m) ms''
    · obtain ⟨a, m', b, rfl, hx⟩ := exists_split_of_mem_walkLabels step lab (step y m) ms'' hmem
      have hsplit : walkLabels step lab (step y m) (a ++ m' :: b) =
          walkLabels step lab (step y m) a ++ lab y m ::
            walkLabels step lab (step (walkEnd step (step y m) a) m') b := by
        rw [walkLabels_append, walkLabels, hx]
      have hend : walkEnd step (step y m) (a ++ m' :: b) = walkEnd step (step (walkEnd step (step y m) a) m') b := by
        rw [walkEnd_append]; rfl
      generalize walkEnd step (step y m) a = y' at hsplit hend hx
      rw [hsplit] at hnd hsub
      rw [hend] at he
      have hnd2 : (lab y m :: walkLabels step lab (step y' m') b).Nodup := hnd.sublist (List.sublist_append_right _ _)
      have hL2 : ∀ x ∈ walkLabels step lab (step y' m') b, x ∈ walkLabels step lab y (m :: ms) := fun x hx2 =>
        List.mem_cons_of_mem _ (hsub x (List.mem_append_right _ (List.mem_cons_of_mem _ hx2)))
      rcases hlab y m y' m' hx.symm with h | h
      · have e1 : walkEnd step y b = walkEnd step (step y' m') b := by rw [h]
        have e2 : walkLabels step lab y b = walkLabels step lab (step y' m') b := by rw [h]
        refine ⟨b, e1.trans he, ?_, ?_⟩
        · rw [e2]; exact (List.nodup_cons.mp hnd2).2
        · rw [e2]; exact hL2
      · have e1 : walkEnd step (step y m) b = walkEnd step (step y' m') b := by rw [h]
        have e2 : walkLabels step lab (step y m) b = walkLabels step lab (step y' m') b := by rw [h]
        refine ⟨m :: b, e1.trans he, ?_, ?_⟩
        · show (lab y m :: walkLabels step lab (step y m) b).Nodup
          rw [e2]; exact hnd2
        · intro x hx2
          rcases List.mem_cons.mp hx2 with hx3 | hx3
          · rw [hx3]; exact List.mem_cons_self
          · rw [e2] at hx3; exact hL2 x hx3
    · refine ⟨m :: ms'', he, List.nodup_cons.mpr ⟨hmem, hnd⟩, fun x hx2 => ?_⟩
      rcases List.mem_cons.mp hx2 with hx3 | hx3
      · rw [hx3]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub x hx3)

end Abstract

/-! ## Walks in a layer -/

section Layer

variable {d N : ℕ}

/-- A move in the layer orthogonal to `ν`: a direction `ρ ≠ ν` and a sign. -/
abbrev Move (d : ℕ) (ν : Fin d) := {ρ : Fin d // ρ ≠ ν} × Bool

theorem card_move (ν : Fin d) : Fintype.card (Move d ν) = 2 * (d - 1) := by
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_subtype, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, mul_comm]

/-- One move: `y ± ρ̂`. -/
def mstep {ν : Fin d} (y : FinLatticeSites d N) (m : Move d ν) : FinLatticeSites d N :=
  Function.update y m.1.1 (y m.1.1 + if m.2 then 1 else -1)

/-- The plaquette at `s` in the plane `(ν, ρ)`, directions in increasing order. -/
def mkPlaq (s : FinLatticeSites d N) (ν ρ : Fin d) (h : ρ ≠ ν) : LatticePlaquette d N :=
  if h' : ν < ρ then ⟨s, ν, ρ, h'⟩ else ⟨s, ρ, ν, lt_of_le_of_ne (not_lt.mp h') h⟩

/-- The base site of the plaquette a move crosses: `y` for `+ρ̂`, `y − ρ̂` for `−ρ̂`. -/
def mbase {ν : Fin d} (y : FinLatticeSites d N) (m : Move d ν) : FinLatticeSites d N := if m.2 then y else mstep y m

/-- The plaquette a move crosses: its two `ν`-links start at `y` and at `mstep y m`. -/
def mlab {ν : Fin d} (y : FinLatticeSites d N) (m : Move d ν) : LatticePlaquette d N := mkPlaq (mbase y m) ν m.1.1 m.1.2

theorem mkPlaq_site (s : FinLatticeSites d N) (ν ρ : Fin d) (h : ρ ≠ ν) : (mkPlaq s ν ρ h).site = s := by
  unfold mkPlaq; split_ifs <;> rfl

theorem mkPlaq_inj {s s' : FinLatticeSites d N} {ν ρ ρ' : Fin d} {h : ρ ≠ ν} {h' : ρ' ≠ ν}
    (e : mkPlaq s ν ρ h = mkPlaq s' ν ρ' h') : s = s' ∧ ρ = ρ' := by
  unfold mkPlaq at e
  split_ifs at e <;> simp only [LatticePlaquette.mk.injEq] at e <;> simp_all

theorem mkPlaq_of_lt (s : FinLatticeSites d N) {ν ρ : Fin d} (h : ρ ≠ ν) (hlt : ν < ρ) :
    mkPlaq s ν ρ h = ⟨s, ν, ρ, hlt⟩ := by
  unfold mkPlaq; rw [dif_pos hlt]

theorem mkPlaq_of_gt (s : FinLatticeSites d N) {ν ρ : Fin d} (h : ρ ≠ ν) (hlt : ρ < ν) :
    mkPlaq s ν ρ h = ⟨s, ρ, ν, hlt⟩ := by
  unfold mkPlaq; rw [dif_neg (not_lt.mpr hlt.le)]

theorem mstep_true {ν : Fin d} (y : FinLatticeSites d N) (ρ : {ρ : Fin d // ρ ≠ ν}) :
    mstep y (ρ, true) = siteShift d N y ρ.1 := by
  simp [mstep, siteShift]

theorem siteShift_mstep_false {ν : Fin d} (y : FinLatticeSites d N) (ρ : {ρ : Fin d // ρ ≠ ν}) :
    siteShift d N (mstep y (ρ, false)) ρ.1 = y := by
  simp [mstep, siteShift]

theorem mstep_false_siteShift {ν : Fin d} (y : FinLatticeSites d N) (ρ : {ρ : Fin d // ρ ≠ ν}) :
    mstep (siteShift d N y ρ.1) (ρ, false) = y := by
  simp [mstep, siteShift]

/-- The two ends of a move are the two `ν`-link sites of the plaquette it crosses. -/
theorem mlab_ends {ν : Fin d} (y : FinLatticeSites d N) (m : Move d ν) :
    (y = mbase y m ∧ mstep y m = siteShift d N (mbase y m) m.1.1) ∨
      (y = siteShift d N (mbase y m) m.1.1 ∧ mstep y m = mbase y m) := by
  obtain ⟨ρ, b⟩ := m
  cases b
  · right; exact ⟨(siteShift_mstep_false y ρ).symm, rfl⟩
  · left; exact ⟨rfl, mstep_true y ρ⟩

/-- Equal plaquettes: the later move ends at an end of the earlier one (the hypothesis of loop erasure). -/
theorem mlab_eq {ν : Fin d} (y : FinLatticeSites d N) (m : Move d ν) (y' : FinLatticeSites d N) (m' : Move d ν)
    (e : mlab y m = mlab y' m') : mstep y' m' = y ∨ mstep y' m' = mstep y m := by
  obtain ⟨hs, hρ⟩ := mkPlaq_inj e
  have hsh : siteShift d N (mbase y m) m.1.1 = siteShift d N (mbase y' m') m'.1.1 := by rw [hs, hρ]
  rcases mlab_ends y m with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases mlab_ends y' m' with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · right; rw [h4, h2, hsh]
  · left; rw [h4, ← hs, ← h1]
  · left; rw [h4, ← hsh, ← h1]
  · right; rw [h4, h2, hs]

/-! ### The `ν`-coordinate is constant -/

theorem mstep_apply_self {ν : Fin d} (y : FinLatticeSites d N) (m : Move d ν) : mstep y m ν = y ν :=
  Function.update_of_ne (Ne.symm m.1.2) _ _

theorem mlab_site_apply {ν : Fin d} (y : FinLatticeSites d N) (m : Move d ν) : (mlab y m).site ν = y ν := by
  unfold mlab; rw [mkPlaq_site]; unfold mbase; split_ifs
  · rfl
  · exact mstep_apply_self y m

theorem walkEnd_apply_self {ν : Fin d} (y : FinLatticeSites d N) (ms : List (Move d ν)) :
    walkEnd mstep y ms ν = y ν := by
  induction ms generalizing y with
  | nil => rfl
  | cons m ms ih => exact (ih (mstep y m)).trans (mstep_apply_self y m)

theorem walkLabels_site {ν : Fin d} (y : FinLatticeSites d N) (ms : List (Move d ν)) :
    ∀ p ∈ walkLabels mstep mlab y ms, p.site ν = y ν := by
  induction ms generalizing y with
  | nil => simp [walkLabels]
  | cons m ms ih =>
    intro p hp
    rcases List.mem_cons.mp hp with h | h
    · rw [h]; exact mlab_site_apply y m
    · exact (ih (mstep y m) p h).trans (mstep_apply_self y m)

/-! ### Displacement in another direction -/

/-- The change of the `μ`-coordinate under a move. -/
def mdisp {ν : Fin d} (μ : Fin d) (m : Move d ν) : ℤ := if m.1.1 = μ then (if m.2 then 1 else -1) else 0

theorem abs_mdisp_le {ν : Fin d} (μ : Fin d) (m : Move d ν) : |mdisp μ m| ≤ 1 := by
  unfold mdisp; split_ifs <;> simp

theorem mstep_apply_disp {ν : Fin d} (μ : Fin d) (y : FinLatticeSites d N) (m : Move d ν) :
    mstep y m μ = y μ + (mdisp μ m : ZMod N) := by
  unfold mstep mdisp
  by_cases h : m.1.1 = μ
  · subst h; cases m.2 <;> simp
  · rw [Function.update_of_ne (Ne.symm h), if_neg h]; simp

theorem walkEnd_apply_disp {ν : Fin d} (μ : Fin d) (y : FinLatticeSites d N) (ms : List (Move d ν)) :
    walkEnd mstep y ms μ = y μ + (((ms.map (mdisp μ)).sum : ℤ) : ZMod N) := by
  induction ms generalizing y with
  | nil => simp [walkEnd]
  | cons m ms ih =>
    show walkEnd mstep (mstep y m) ms μ = _
    rw [ih, mstep_apply_disp]; push_cast [List.map_cons, List.sum_cons]; ring

theorem abs_sum_mdisp_le {ν : Fin d} (μ : Fin d) (ms : List (Move d ν)) : |(ms.map (mdisp μ)).sum| ≤ ms.length := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith [abs_add_le (mdisp μ m) (ms.map (mdisp μ)).sum, abs_mdisp_le μ m]

/-- **Distance on `ℤ/Nℤ`.** An integer congruent to `R` modulo `N`, `R < N`, has absolute value at least `min(R, N − R)`. -/
theorem min_le_natAbs_of_cast_eq {R : ℕ} (hR : R < N) {k : ℤ} (h : (k : ZMod N) = (R : ZMod N)) :
    min R (N - R) ≤ k.natAbs := by
  rw [← Int.cast_natCast, ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨t, ht⟩ := h
  rw [min_le_iff]
  zify [hR.le]
  rcases lt_trichotomy t 0 with h0 | h0 | h0
  · left
    have : (N : ℤ) * t ≤ -N := by nlinarith
    rcases abs_cases k with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rw [hk] <;> omega
  · left; subst h0
    rcases abs_cases k with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rw [hk] <;> omega
  · right
    have : (N : ℤ) * t ≥ N := by nlinarith
    rcases abs_cases k with ⟨hk, _⟩ | ⟨hk, _⟩ <;> rw [hk] <;> omega

end Layer

/-! ## Counting -/

section Count

variable (α : Type*) [Fintype α] [DecidableEq α]

/-- All lists of length at most `k`. -/
def listsUpTo : ℕ → Finset (List α)
  | 0 => {[]}
  | k + 1 => insert [] ((univ ×ˢ listsUpTo k).image (fun x : α × List α => x.1 :: x.2))

theorem mem_listsUpTo : ∀ (k : ℕ) (l : List α), l.length ≤ k → l ∈ listsUpTo α k
  | 0, l, h => by rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]; simp [listsUpTo]
  | k + 1, [], _ => by simp [listsUpTo]
  | k + 1, a :: l, h => by
    rw [listsUpTo]
    refine mem_insert_of_mem (mem_image.mpr ⟨(a, l), mem_product.mpr ⟨mem_univ _, mem_listsUpTo k l ?_⟩, rfl⟩)
    simp only [List.length_cons] at h; omega

/-- **The walk count.** `∑_{l, |l| ≥ r} p^{|l|} ≤ q^r / (1 − q)` over lists of length at most `k`, `q = |α| p < 1`. -/
theorem sum_listsUpTo_le {p : ℝ} (hp : 0 ≤ p) (hq : (Fintype.card α : ℝ) * p < 1) :
    ∀ (k r : ℕ), ∑ l ∈ listsUpTo α k, (if r ≤ l.length then p ^ l.length else 0) ≤
      ((Fintype.card α : ℝ) * p) ^ r / (1 - (Fintype.card α : ℝ) * p) := by
  set q := (Fintype.card α : ℝ) * p with hqdef
  have hq0 : 0 ≤ q := by positivity
  have h1q : 0 < 1 - q := by linarith
  intro k
  induction k with
  | zero =>
    intro r
    simp only [listsUpTo, sum_singleton, List.length_nil, pow_zero]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · rw [if_pos le_rfl, pow_zero, le_div_iff₀ h1q]; linarith
    · rw [if_neg (by omega)]; positivity
  | succ k ih =>
    intro r
    have hnot : ([] : List α) ∉ (univ ×ˢ listsUpTo α k).image (fun x : α × List α => x.1 :: x.2) := by simp
    rw [listsUpTo, sum_insert hnot,
      sum_image (fun x _ y _ h => Prod.ext (List.cons.inj h).1 (List.cons.inj h).2), sum_product]
    have hinner : ∀ (a : α) (l : List α), (if r ≤ (a :: l).length then p ^ (a :: l).length else 0) =
        p * (if r - 1 ≤ l.length then p ^ l.length else 0) := by
      intro a l
      simp only [List.length_cons]
      by_cases h1 : r ≤ l.length + 1
      · rw [if_pos h1, if_pos (by omega), pow_succ]; ring
      · rw [if_neg h1, if_neg (by omega), mul_zero]
    have hsum : ∑ a : α, ∑ l ∈ listsUpTo α k, (if r ≤ (a :: l).length then p ^ (a :: l).length else 0) =
        q * ∑ l ∈ listsUpTo α k, (if r - 1 ≤ l.length then p ^ l.length else 0) := by
      simp_rw [hinner, ← mul_sum]
      rw [sum_const, card_univ, nsmul_eq_mul, hqdef]; ring
    simp only at hsum ⊢
    rw [hsum]
    have ih' := ih (r - 1)
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp only [List.length_nil, le_refl, if_true, pow_zero, Nat.zero_sub] at ih' ⊢
      rw [le_div_iff₀ h1q]
      have := mul_le_mul_of_nonneg_left ih' hq0
      rw [le_div_iff₀ h1q] at ih'
      nlinarith
    · rw [if_neg (by simp; omega), zero_add]
      calc q * ∑ l ∈ listsUpTo α k, (if r - 1 ≤ l.length then p ^ l.length else 0)
          ≤ q * (q ^ (r - 1) / (1 - q)) := mul_le_mul_of_nonneg_left ih' hq0
        _ = q ^ r / (1 - q) := by
          rw [← mul_div_assoc, ← pow_succ']; congr 2; omega

/-- A filtered version: walks of length at least `r`. -/
theorem sum_filter_listsUpTo_le {p : ℝ} (hp : 0 ≤ p) (hq : (Fintype.card α : ℝ) * p < 1) (k r : ℕ)
    (Q : List α → Prop) [DecidablePred Q] (hQ : ∀ l, Q l → r ≤ l.length) :
    ∑ l ∈ (listsUpTo α k).filter Q, p ^ l.length ≤
      ((Fintype.card α : ℝ) * p) ^ r / (1 - (Fintype.card α : ℝ) * p) := by
  refine le_trans ?_ (sum_listsUpTo_le α hp hq k r)
  rw [sum_filter]
  refine sum_le_sum fun l _ => ?_
  by_cases h : Q l
  · rw [if_pos h, if_pos (hQ l h)]
  · rw [if_neg h]; split_ifs <;> positivity

end Count

/-! ## Survivors and supersets -/

/-- **The superset sum over survivors.** If every surviving `A` contains a witness `X i`, `i ∈ W`, and `0 ≤ h ≤ p (1 + h)`, then
    `∑_{A survives} ∏_A h ≤ (∑_{i ∈ W} p^{|X i|}) ∏ (1 + h)`. -/
theorem sum_surv_le {V ι : Type*} [Fintype V] [DecidableEq V] (h : V → ℝ) {p : ℝ} (h0 : ∀ v, 0 ≤ h v)
    (hle : ∀ v, h v ≤ p * (1 + h v)) (Surv : Finset V → Prop) [DecidablePred Surv] (W : Finset ι) (X : ι → Finset V)
    (hw : ∀ A, Surv A → ∃ i ∈ W, X i ⊆ A) :
    ∑ A ∈ (univ : Finset V).powerset.filter Surv, ∏ v ∈ A, h v ≤ (∑ i ∈ W, p ^ (X i).card) * ∏ v, (1 + h v) := by
  classical
  have hI : ∀ A : Finset V, 0 ≤ ∏ v ∈ A, h v := fun A => prod_nonneg fun v _ => h0 v
  have hite : ∀ (A : Finset V) (i : ι), 0 ≤ (if X i ⊆ A then ∏ v ∈ A, h v else 0) := fun A i => by
    split_ifs <;> [exact hI A; exact le_rfl]
  calc ∑ A ∈ (univ : Finset V).powerset.filter Surv, ∏ v ∈ A, h v
      ≤ ∑ A ∈ (univ : Finset V).powerset.filter Surv, ∑ i ∈ W, (if X i ⊆ A then ∏ v ∈ A, h v else 0) := by
        refine sum_le_sum fun A hA => ?_
        obtain ⟨i, hi, hXA⟩ := hw A (mem_filter.mp hA).2
        calc ∏ v ∈ A, h v = (if X i ⊆ A then ∏ v ∈ A, h v else 0) := by rw [if_pos hXA]
          _ ≤ _ := single_le_sum (f := fun i => if X i ⊆ A then ∏ v ∈ A, h v else 0) (fun i _ => hite A i) hi
    _ ≤ ∑ A ∈ (univ : Finset V).powerset, ∑ i ∈ W, (if X i ⊆ A then ∏ v ∈ A, h v else 0) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun A _ _ => sum_nonneg fun i _ => hite A i
    _ = ∑ i ∈ W, ∑ A ∈ (univ : Finset V).powerset, (if X i ⊆ A then ∏ v ∈ A, h v else 0) := sum_comm
    _ = ∑ i ∈ W, ∑ A ∈ (univ : Finset V).powerset.filter (fun A => X i ⊆ A), ∏ v ∈ A, h v :=
        sum_congr rfl fun i _ => by rw [sum_filter]
    _ ≤ ∑ i ∈ W, p ^ (X i).card * ∏ v, (1 + h v) := by
        refine sum_le_sum fun i _ => ?_
        convert AreaLaw.Clustering.sum_superset_le h h0 hle (X i)
    _ = _ := by rw [sum_mul]

end AreaLaw.Twist
