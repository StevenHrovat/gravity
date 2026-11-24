/-
Proof phase, cycle 8, workstream 1 (c8a-saturation): the 't Hooft twist sheet on the periodic lattice, how it moves, when a
configuration lets it be moved away, and the count of the configurations that pin it (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c8a-saturation/NOTE.md`, section 3.
-/

import AreaLaw.TwistAreaLaw

/-!
# The twist sheet: geometry and counting

Fix two directions `μ ≠ ν` and a value `a` of the `μ`-coordinate. The **twist sheet at layer `c`** is the set of plaquettes in
the plane `(μ, ν)` based at the sites with `x_ν = c`, `x_μ = a` (`IsSheet`): one plaquette for each value of the other
`d − 2` coordinates, i.e. a closed surface of the dual lattice wrapping the torus in the remaining directions. Multiplying its
plaquette holonomies by a central involution `z` is the 't Hooft twist in the plane `(μ, ν)`.

* **The sheet moves for free** (`tcount_move`): multiplying the `μ`-links at `x_μ = a`, `x_ν = c + 1` by `z` changes the twist
  count of every plaquette by the difference of the sheet indicators of layers `c + 1` and `c`, up to sign. So the twisted
  weight with the sheet at layer `c` is a change of variables of the one with the sheet at layer `c + 1`.
* **A configuration of plaquettes `A` lets the sheet go at layer `c`** unless it pins it there (`SurvLayer`): unless, inside
  layer `c`, some site just above the sheet reaches a site just below it by moves across plaquettes of `A` that are not sheet
  plaquettes, with the sheet plaquettes at both ends in `A`. If not, multiplying the `ν`-links of the layer that start in the
  reached set by `z` makes every plaquette of `A` see the sheet an even number of times (`tcount_cancel`).
* **A pinning walk is long** (`length_ge_of_cross`): it must go around the torus in direction `μ`, so it has at least `N − 1`
  steps (a lifted-coordinate argument).
* **The count** (`sum_surv_sheet_le`): if every layer is pinned, `A` contains `N` disjoint pinning loops, each of at least `N`
  plaquettes (`N²` in total: the area of the sheet). With `0 ≤ h ≤ p (1 + h)` and `q = 2(d − 1) p < 1`:
  `∑_{A pins every layer} ∏_A h ≤ (V p q^{N−1}/(1 − q))^N ∏ (1 + h)`, `V` the number of sites.

This is the energy–entropy (Peierls) balance in the form the proof uses: each pinning plaquette costs a factor `p` (energy), each
step of a pinning walk has `2(d − 1)` continuations (entropy), and `q < 1` is "energy beats entropy" for the pinning surfaces,
which is the same as "entropy beats energy" for the twist sheet (NOTE, section 2).
-/

open Finset AreaLaw.Twist

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Saturation

variable {d N : ℕ}

/-! ## 1. The sheet -/

section Sheet

variable (μ ν : Fin d) (a : ZMod N) [NeZero N]

/-- The plaquette lies in the plane `(μ, ν)`. -/
def InPlane (p : LatticePlaquette d N) : Prop := (p.dir1 = μ ∧ p.dir2 = ν) ∨ (p.dir1 = ν ∧ p.dir2 = μ)

/-- **The twist sheet at layer `c`**: plaquettes in the plane `(μ, ν)` based at `x_ν = c`, `x_μ = a`. -/
def IsSheet (c : ZMod N) (p : LatticePlaquette d N) : Prop := InPlane μ ν p ∧ p.site ν = c ∧ p.site μ = a

/-- The sheet indicator as an exponent of the twist. -/
def sheetE (c : ZMod N) (p : LatticePlaquette d N) : ℤ := if IsSheet μ ν a c p then 1 else 0

variable {μ ν}

/-- The move `+μ̂` in the layer orthogonal to `ν`. -/
def muPlus (hμν : μ ≠ ν) : Move d ν := (⟨μ, hμν⟩, true)

theorem inPlane_mkPlaq (hμν : μ ≠ ν) (s : FinLatticeSites d N) (ρ : Fin d) (h : ρ ≠ ν) :
    InPlane μ ν (mkPlaq s ν ρ h) ↔ ρ = μ := by
  unfold mkPlaq
  split_ifs with h'
  · show (ν = μ ∧ ρ = ν) ∨ (ν = ν ∧ ρ = μ) ↔ ρ = μ
    constructor
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact absurd h1.symm hμν
      · exact h2
    · intro hρ; exact Or.inr ⟨rfl, hρ⟩
  · show (ρ = μ ∧ ν = ν) ∨ (ρ = ν ∧ ν = μ) ↔ ρ = μ
    constructor
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact h1
      · exact absurd h1 h
    · intro hρ; exact Or.inl ⟨hρ, rfl⟩

/-- A move crosses a sheet plaquette iff it goes in direction `μ` and its plaquette is based on the sheet. -/
theorem isSheet_mlab (hμν : μ ≠ ν) (c : ZMod N) (y : FinLatticeSites d N) (m : Move d ν) :
    IsSheet μ ν a c (mlab y m) ↔ m.1.1 = μ ∧ mbase y m ν = c ∧ mbase y m μ = a := by
  unfold IsSheet
  rw [show mlab y m = mkPlaq (mbase y m) ν m.1.1 m.1.2 from rfl, inPlane_mkPlaq hμν, mkPlaq_site]

theorem isSheet_muPlus (hμν : μ ≠ ν) (c : ZMod N) (y : FinLatticeSites d N) :
    IsSheet μ ν a c (mlab y (muPlus hμν)) ↔ y ν = c ∧ y μ = a := by
  rw [isSheet_mlab a hμν]
  simp [muPlus, mbase]

/-! ## 2. The sheet moves for free -/

/-- The `μ`-links at `x_μ = a`, `x_ν = c + 1`: multiplying them by `z` moves the sheet from layer `c` to layer `c + 1`. -/
def moveLinks (μ ν : Fin d) (a c : ZMod N) : Finset (LatticeLink d N) :=
  univ.filter (fun l : LatticeLink d N => l.dir = μ ∧ l.site μ = a ∧ l.site ν = c + 1)

theorem siteShift_apply_ne' (s : FinLatticeSites d N) {α β : Fin d} (h : α ≠ β) : siteShift d N s α β = s β := by
  simp [siteShift, Function.update_of_ne (Ne.symm h)]

theorem siteShift_apply_self' (s : FinLatticeSites d N) (α : Fin d) : siteShift d N s α α = s α + 1 := by
  simp [siteShift]

/-- **The move.** The twist count of every plaquette under `moveLinks c` is `± (sheetE (c+1) − sheetE c)`. -/
theorem tcount_move (hμν : μ ≠ ν) (c : ZMod N) (p : LatticePlaquette d N) :
    tcount (moveLinks μ ν a c) (plaquettePath p) = sheetE μ ν a (c + 1) p - sheetE μ ν a c p ∨
      tcount (moveLinks μ ν a c) (plaquettePath p) = sheetE μ ν a c p - sheetE μ ν a (c + 1) p := by
  rw [tcount_plaquettePath]
  obtain ⟨s, α, β, hab⟩ := p
  have hαβ : α ≠ β := ne_of_lt hab
  simp only [LatticePlaquette.boundaryLinks, moveLinks, mem_filter, mem_univ, true_and, sheetE, IsSheet, InPlane]
  by_cases hαμ : α = μ
  · subst hαμ
    have hβα : β ≠ α := Ne.symm hαβ
    by_cases hβν : β = ν
    · subst hβν
      simp only [siteShift_apply_ne' s hαβ, siteShift_apply_ne' s hβα, siteShift_apply_self' s β]
      left
      have e1 : (s β + 1 = c + 1) ↔ s β = c := add_left_inj 1
      by_cases h1 : s α = a <;> by_cases h2 : s β = c + 1 <;> by_cases h3 : s β = c <;>
        simp [h1, h2, h3, e1, hαβ, hβα]
    · rw [siteShift_apply_ne' s hβα, siteShift_apply_ne' s hβν]
      left
      have hn1 : ¬ (α = ν ∧ β = α) := fun h => hβα h.2
      simp [hβα, hβν, hn1]
  · by_cases hβμ : β = μ
    · subst hβμ
      by_cases hαν : α = ν
      · subst hαν
        rw [siteShift_apply_ne' s hαβ, siteShift_apply_self' s α]
        right
        have e1 : (s α + 1 = c + 1) ↔ s α = c := add_left_inj 1
        by_cases h1 : s β = a <;> by_cases h2 : s α = c + 1 <;> by_cases h3 : s α = c <;>
          simp [h1, h2, h3, e1, hαβ, Ne.symm hαβ]
      · rw [siteShift_apply_ne' s hαβ, siteShift_apply_ne' s hαν]
        left
        simp [hαμ, hαν]
    · left
      simp [hαμ, hβμ]

/-! ## 3. Letting the sheet go -/

variable (μ ν)

/-- A move from `y` to `y'` across a plaquette of `A` that is not a sheet plaquette of layer `c`. -/
def Allowed (c : ZMod N) (A : Finset (LatticePlaquette d N)) (y y' : FinLatticeSites d N) : Prop :=
  ∃ m : Move d ν, mstep y m = y' ∧ mlab y m ∈ A ∧ ¬ IsSheet μ ν a c (mlab y m)

variable {μ ν}

/-- The sites reached from just above a sheet plaquette of `A` by allowed moves. -/
def Reach (hμν : μ ≠ ν) (c : ZMod N) (A : Finset (LatticePlaquette d N)) (y : FinLatticeSites d N) : Prop :=
  ∃ y', y' ν = c ∧ y' μ = a ∧ mlab y' (muPlus hμν) ∈ A ∧
    Relation.ReflTransGen (Allowed μ ν a c A) (siteShift d N y' μ) y

/-- **`A` pins the sheet at layer `c`**: a site just below a sheet plaquette of `A` is reached. -/
def SurvLayer (hμν : μ ≠ ν) (c : ZMod N) (A : Finset (LatticePlaquette d N)) : Prop :=
  ∃ y, Reach a hμν c A y ∧ y μ = a ∧ mlab y (muPlus hμν) ∈ A

/-- The `ν`-links starting at the reached sites. -/
def cancelLinks (hμν : μ ≠ ν) (c : ZMod N) (A : Finset (LatticePlaquette d N)) : Finset (LatticeLink d N) :=
  univ.filter (fun l : LatticeLink d N => l.dir = ν ∧ Reach a hμν c A l.site)

theorem reach_tail {hμν : μ ≠ ν} {c : ZMod N} {A : Finset (LatticePlaquette d N)} {y y' : FinLatticeSites d N}
    (h : Reach a hμν c A y) (e : Allowed μ ν a c A y y') : Reach a hμν c A y' := by
  obtain ⟨y0, h1, h2, h3, h4⟩ := h
  exact ⟨y0, h1, h2, h3, h4.tail e⟩

/-- Across a non-sheet plaquette of `A` the reached set does not change. -/
theorem reach_iff_of_mem {hμν : μ ≠ ν} {c : ZMod N} {A : Finset (LatticePlaquette d N)} (y : FinLatticeSites d N)
    (ρ : {ρ : Fin d // ρ ≠ ν}) (hA : mlab y (ρ, true) ∈ A) (hns : ¬ IsSheet μ ν a c (mlab y (ρ, true))) :
    Reach a hμν c A y ↔ Reach a hμν c A (siteShift d N y ρ.1) := by
  have hlab : mlab (siteShift d N y ρ.1) (ρ, false) = mlab y (ρ, true) := by
    simp only [mlab, mbase, Bool.false_eq_true, ↓reduceIte, mstep_false_siteShift]
  have e1 : Allowed μ ν a c A y (siteShift d N y ρ.1) := ⟨(ρ, true), mstep_true y ρ, hA, hns⟩
  have e2 : Allowed μ ν a c A (siteShift d N y ρ.1) y :=
    ⟨(ρ, false), mstep_false_siteShift y ρ, by rw [hlab]; exact hA, by rw [hlab]; exact hns⟩
  exact ⟨fun h => reach_tail a h e1, fun h => reach_tail a h e2⟩

/-- **Letting the sheet go.** If `A` does not pin the sheet at layer `c`, every plaquette of `A` sees the sheet plus the
    `ν`-link twist `cancelLinks c A` an even number of times. -/
theorem tcount_cancel (hμν : μ ≠ ν) (c : ZMod N) (A : Finset (LatticePlaquette d N)) (hA : ¬ SurvLayer a hμν c A)
    (p : LatticePlaquette d N) (hp : p ∈ A) :
    Even (sheetE μ ν a c p + tcount (cancelLinks a hμν c A) (plaquettePath p)) := by
  rw [tcount_plaquettePath]
  obtain ⟨s, α, β, hab⟩ := p
  have hαβ : α ≠ β := ne_of_lt hab
  simp only [LatticePlaquette.boundaryLinks, cancelLinks, mem_filter, mem_univ, true_and]
  by_cases hαν : α = ν
  · subst hαν
    have hβ : β ≠ α := Ne.symm hαβ
    have hpl : mlab s ((⟨β, hβ⟩ : {ρ : Fin d // ρ ≠ α}), true) = ⟨s, α, β, hab⟩ := by
      simp only [mlab, mbase, ↓reduceIte]; exact mkPlaq_of_lt s hβ hab
    by_cases hsh : IsSheet μ α a c ⟨s, α, β, hab⟩
    · have hsh' := hsh
      rw [← hpl, isSheet_mlab a hμν] at hsh'
      obtain ⟨hβμ, hsν, hsμ⟩ := hsh'
      simp only [mbase, ↓reduceIte] at hβμ hsν hsμ
      subst hβμ
      have hpl' : mlab s (muPlus hμν) = ⟨s, α, β, hab⟩ := hpl
      have hRup : Reach a hμν c A (siteShift d N s β) :=
        ⟨s, hsν, hsμ, by rw [hpl']; exact hp, Relation.ReflTransGen.refl⟩
      have hRs : ¬ Reach a hμν c A s := fun h => hA ⟨s, h, hsμ, by rw [hpl']; exact hp⟩
      simp [sheetE, hsh, hRs, hRup, hβ]
    · have hkey := reach_iff_of_mem (hμν := hμν) a s ⟨β, hβ⟩ (by rw [hpl]; exact hp) (by rw [hpl]; exact hsh)
      simp only at hkey
      rcases em (Reach a hμν c A s) with h1 | h1
      · simp [sheetE, hsh, h1, hkey.mp h1, hβ]
      · simp [sheetE, hsh, h1, mt hkey.mpr h1, hβ]
  · by_cases hβν : β = ν
    · subst hβν
      have hpl : mlab s ((⟨α, hαν⟩ : {ρ : Fin d // ρ ≠ β}), true) = ⟨s, α, β, hab⟩ := by
        simp only [mlab, mbase, ↓reduceIte]; exact mkPlaq_of_gt s hαν hab
      by_cases hsh : IsSheet μ β a c ⟨s, α, β, hab⟩
      · have hsh' := hsh
        rw [← hpl, isSheet_mlab a hμν] at hsh'
        obtain ⟨hαμ, hsν, hsμ⟩ := hsh'
        simp only [mbase, ↓reduceIte] at hαμ hsν hsμ
        subst hαμ
        have hpl' : mlab s (muPlus hμν) = ⟨s, α, β, hab⟩ := hpl
        have hRup : Reach a hμν c A (siteShift d N s α) :=
          ⟨s, hsν, hsμ, by rw [hpl']; exact hp, Relation.ReflTransGen.refl⟩
        have hRs : ¬ Reach a hμν c A s := fun h => hA ⟨s, h, hsμ, by rw [hpl']; exact hp⟩
        simp [sheetE, hsh, hRs, hRup, hαν]
      · have hkey := reach_iff_of_mem (hμν := hμν) a s ⟨α, hαν⟩ (by rw [hpl]; exact hp) (by rw [hpl]; exact hsh)
        simp only at hkey
        rcases em (Reach a hμν c A s) with h1 | h1
        · simp [sheetE, hsh, h1, hkey.mp h1, hαν]
        · simp [sheetE, hsh, h1, mt hkey.mpr h1, hαν]
    · have hns : ¬ IsSheet μ ν a c ⟨s, α, β, hab⟩ := by
        rintro ⟨hpl, -, -⟩
        rcases hpl with ⟨-, h2⟩ | ⟨h1, -⟩
        · exact hβν h2
        · exact hαν h1
      simp [sheetE, hns, hαν, hβν]

/-! ## 4. A pinning walk goes around the torus -/

/-- The height above the sheet, lifted: `(x_μ − (a + 1)).val ∈ [0, N)`. -/
def height (μ : Fin d) (a : ZMod N) (y : FinLatticeSites d N) : ℕ := (y μ - (a + 1)).val

theorem val_neg_one' (hN : 1 < N) : (-1 : ZMod N).val = N - 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [ZMod.val_neg_one]; omega

/-- One allowed step changes the lifted height by the displacement. -/
theorem height_mstep (hN : 1 < N) (hμν : μ ≠ ν) (c : ZMod N) (y : FinLatticeSites d N) (hyν : y ν = c) (m : Move d ν)
    (hns : ¬ IsSheet μ ν a c (mlab y m)) :
    (height μ a (mstep y m) : ℤ) = height μ a y + mdisp μ m := by
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (1 < N) := ⟨hN⟩
  rw [isSheet_mlab a hμν] at hns
  unfold height
  rw [mstep_apply_disp]
  set t := y μ - (a + 1) with ht
  obtain ⟨⟨ρ, hρ⟩, b⟩ := m
  by_cases hρμ : ρ = μ
  · subst hρμ
    cases b
    · -- the move `−μ̂`
      have hmd : mdisp ρ ((⟨ρ, hρ⟩ : {ρ' : Fin d // ρ' ≠ ν}), false) = -1 := by simp [mdisp]
      rw [hmd]
      have hbase : mbase y ((⟨ρ, hρ⟩ : {ρ' : Fin d // ρ' ≠ ν}), false) = mstep y (⟨ρ, hρ⟩, false) := rfl
      have hmν : mstep y ((⟨ρ, hρ⟩ : {ρ' : Fin d // ρ' ≠ ν}), false) ν = c := (mstep_apply_self y _).trans hyν
      have hmμ : mstep y ((⟨ρ, hρ⟩ : {ρ' : Fin d // ρ' ≠ ν}), false) ρ = y ρ - 1 := by
        rw [mstep_apply_disp, hmd]; push_cast; ring
      have ht0 : t ≠ 0 := by
        intro h0
        apply hns
        refine ⟨rfl, by rw [hbase]; exact hmν, ?_⟩
        rw [hbase, hmμ]
        have : y ρ = a + 1 := by rw [ht] at h0; exact sub_eq_zero.mp h0
        rw [this]; ring
      have hv0 : t.val ≠ 0 := fun h => ht0 ((ZMod.val_eq_zero t).mp h)
      have hv1 : (1 : ZMod N).val ≤ t.val := by rw [ZMod.val_one]; omega
      have e : y ρ + ((-1 : ℤ) : ZMod N) - (a + 1) = t - 1 := by rw [ht]; push_cast; ring
      rw [e, ZMod.val_sub hv1, ZMod.val_one]
      push_cast [Nat.one_le_iff_ne_zero.mpr hv0]
      ring
    · -- the move `+μ̂`
      have hmd : mdisp ρ ((⟨ρ, hρ⟩ : {ρ' : Fin d // ρ' ≠ ν}), true) = 1 := by simp [mdisp]
      rw [hmd]
      have htm : t ≠ -1 := by
        intro h1
        apply hns
        refine ⟨rfl, hyν, ?_⟩
        show y ρ = a
        have : y ρ - (a + 1) = -1 := h1
        linear_combination this
      have hvlt : t.val + (1 : ZMod N).val < N := by
        rw [ZMod.val_one]
        have h1 := ZMod.val_lt t
        have h2 : t.val ≠ N - 1 := by
          intro h
          apply htm
          apply ZMod.val_injective N
          rw [h, val_neg_one' hN]
        omega
      have e : y ρ + ((1 : ℤ) : ZMod N) - (a + 1) = t + 1 := by rw [ht]; push_cast; ring
      rw [e, ZMod.val_add_of_lt hvlt, ZMod.val_one]
      push_cast; ring
  · have hmd : mdisp μ ((⟨ρ, hρ⟩ : {ρ' : Fin d // ρ' ≠ ν}), b) = 0 := by simp [mdisp, hρμ]
    rw [hmd]; simp only [Int.cast_zero, add_zero, ht]

/-- Along an allowed walk in layer `c` the lifted height changes by the total displacement. -/
theorem height_walkEnd (hN : 1 < N) (hμν : μ ≠ ν) (c : ZMod N) :
    ∀ (ms : List (Move d ν)) (y : FinLatticeSites d N), y ν = c →
      (∀ l ∈ walkLabels mstep mlab y ms, ¬ IsSheet μ ν a c l) →
      (height μ a (walkEnd mstep y ms) : ℤ) = height μ a y + (ms.map (mdisp μ)).sum
  | [], y, _, _ => by simp [walkEnd]
  | m :: ms, y, hy, hns => by
    have h1 : ¬ IsSheet μ ν a c (mlab y m) := hns _ List.mem_cons_self
    have h2 : ∀ l ∈ walkLabels mstep mlab (mstep y m) ms, ¬ IsSheet μ ν a c l :=
      fun l hl => hns l (List.mem_cons_of_mem _ hl)
    have h3 := height_walkEnd hN hμν c ms (mstep y m) ((mstep_apply_self y m).trans hy) h2
    show (height μ a (walkEnd mstep (mstep y m) ms) : ℤ) = _
    rw [h3, height_mstep a hN hμν c y hy m h1, List.map_cons, List.sum_cons]
    ring

/-- **A pinning walk is long.** An allowed walk in layer `c` from just above the sheet (`x_μ = a + 1`) to its lower side
    (`x_μ = a`) has at least `N − 1` steps. -/
theorem length_ge_of_cross (hN : 1 < N) (hμν : μ ≠ ν) (c : ZMod N) (y0 : FinLatticeSites d N) (hy0ν : y0 ν = c)
    (hy0μ : y0 μ = a + 1) (ms : List (Move d ν)) (hns : ∀ l ∈ walkLabels mstep mlab y0 ms, ¬ IsSheet μ ν a c l)
    (hend : walkEnd mstep y0 ms μ = a) : N - 1 ≤ ms.length := by
  have h := height_walkEnd a hN hμν c ms y0 hy0ν hns
  have h0 : height μ a y0 = 0 := by simp [height, hy0μ]
  have hE : height μ a (walkEnd mstep y0 ms) = N - 1 := by
    unfold height; rw [hend, show a - (a + 1) = (-1 : ZMod N) by ring, val_neg_one' hN]
  rw [h0, hE, Nat.cast_zero, zero_add] at h
  have hb := abs_sum_mdisp_le μ ms
  have : ((N - 1 : ℕ) : ℤ) ≤ ms.length := by
    rw [h]; exact (le_abs_self _).trans hb
  exact_mod_cast this

/-! ## 5. The count -/

/-- The witnesses of layer `c`: a start `y'` on the sheet's lower side and a loop-erased allowed walk from `y' + μ̂` to the
    lower side. -/
def walkW (hμν : μ ≠ ν) (c : ZMod N) : Finset (FinLatticeSites d N × List (Move d ν)) :=
  (univ ×ˢ listsUpTo (Move d ν) (Fintype.card (LatticePlaquette d N))).filter (fun i =>
    i.1 ν = c ∧ i.1 μ = a ∧ (walkLabels mstep mlab (siteShift d N i.1 μ) i.2).Nodup ∧
    (∀ l ∈ walkLabels mstep mlab (siteShift d N i.1 μ) i.2, ¬ IsSheet μ ν a c l) ∧
    walkEnd mstep (siteShift d N i.1 μ) i.2 μ = a)

/-- The plaquettes of a witness: the walk's plaquettes and the sheet plaquette at its end. -/
def walkX (hμν : μ ≠ ν) (i : FinLatticeSites d N × List (Move d ν)) : Finset (LatticePlaquette d N) :=
  insert (mlab (walkEnd mstep (siteShift d N i.1 μ) i.2) (muPlus hμν))
    (walkLabels mstep mlab (siteShift d N i.1 μ) i.2).toFinset

theorem walkX_site (hμν : μ ≠ ν) (c : ZMod N) {i : FinLatticeSites d N × List (Move d ν)} (hi : i ∈ walkW a hμν c)
    (p : LatticePlaquette d N) (hp : p ∈ walkX hμν i) : p.site ν = c := by
  have hc : i.1 ν = c := (mem_filter.mp hi).2.1
  have hsν : siteShift d N i.1 μ ν = c := by rw [siteShift_apply_ne' _ hμν, hc]
  rcases mem_insert.mp hp with h | h
  · rw [h, mlab_site_apply, walkEnd_apply_self, hsν]
  · rw [walkLabels_site _ _ p (List.mem_toFinset.mp h), hsν]

theorem card_walkX (hμν : μ ≠ ν) (c : ZMod N) {i : FinLatticeSites d N × List (Move d ν)} (hi : i ∈ walkW a hμν c) :
    (walkX hμν i).card = i.2.length + 1 := by
  obtain ⟨-, hc, ha, hnd, hns, hend⟩ := mem_filter.mp hi
  have hsν : siteShift d N i.1 μ ν = c := by rw [siteShift_apply_ne' _ hμν, hc]
  have hsh : IsSheet μ ν a c (mlab (walkEnd mstep (siteShift d N i.1 μ) i.2) (muPlus hμν)) :=
    (isSheet_muPlus a hμν c _).mpr ⟨by rw [walkEnd_apply_self, hsν], hend⟩
  have hnot : mlab (walkEnd mstep (siteShift d N i.1 μ) i.2) (muPlus hμν) ∉
      (walkLabels mstep mlab (siteShift d N i.1 μ) i.2).toFinset :=
    fun h => hns _ (List.mem_toFinset.mp h) hsh
  unfold walkX
  rw [card_insert_of_notMem hnot, List.toFinset_card_of_nodup hnd, length_walkLabels]

/-- A pinned layer has a witness inside `A`. -/
theorem exists_witness (hμν : μ ≠ ν) (c : ZMod N) (A : Finset (LatticePlaquette d N)) (h : SurvLayer a hμν c A) :
    ∃ i ∈ walkW a hμν c, walkX hμν i ⊆ A := by
  obtain ⟨y, ⟨y', hy'ν, hy'μ, hy'A, hreach⟩, hyμ, hyA⟩ := h
  have hwalk : ∀ {u v : FinLatticeSites d N}, Relation.ReflTransGen (Allowed μ ν a c A) u v →
      ∃ ms : List (Move d ν), walkEnd mstep u ms = v ∧
        ∀ l ∈ walkLabels mstep mlab u ms, l ∈ A ∧ ¬ IsSheet μ ν a c l := by
    intro u v huv
    induction huv with
    | refl => exact ⟨[], rfl, by simp [walkLabels]⟩
    | tail _ hbc ih =>
      obtain ⟨ms, he, hl⟩ := ih
      obtain ⟨m, hm, hA, hns⟩ := hbc
      refine ⟨ms ++ [m], by rw [walkEnd_append, he]; exact hm, fun l hl' => ?_⟩
      rw [walkLabels_append, he, List.mem_append] at hl'
      rcases hl' with hl' | hl'
      · exact hl l hl'
      · simp only [walkLabels, List.mem_singleton] at hl'; rw [hl']; exact ⟨hA, hns⟩
  obtain ⟨ms, he, hl⟩ := hwalk hreach
  obtain ⟨ms', he', hnd, hsub⟩ :=
    exists_nodup_walk mstep mlab (fun y m y' m' e => mlab_eq y m y' m' e) ms (siteShift d N y' μ)
  have hend : walkEnd mstep (siteShift d N y' μ) ms' = y := he'.trans he
  refine ⟨(y', ms'), mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, mem_listsUpTo _ _ _ ?_⟩, hy'ν, hy'μ, hnd,
    fun l hl' => (hl l (hsub l hl')).2, by rw [hend]; exact hyμ⟩, ?_⟩
  · rw [← length_walkLabels mstep mlab (siteShift d N y' μ) ms']
    exact hnd.length_le_card
  · intro p hp
    rcases mem_insert.mp hp with h | h
    · simp only at h; rw [h, hend]; exact hyA
    · exact (hl p (hsub p (List.mem_toFinset.mp h))).1

/-- The per-layer sum: `∑_{witnesses} p^{|X|} ≤ V p q^{N−1}/(1 − q)`. -/
theorem sum_walkW_le (hN : 1 < N) (hμν : μ ≠ ν) (c : ZMod N) {pr : ℝ} (hpr0 : 0 ≤ pr)
    (hq : (Fintype.card (Move d ν) : ℝ) * pr < 1) :
    ∑ i ∈ walkW a hμν c, pr ^ (walkX hμν i).card ≤
      Fintype.card (FinLatticeSites d N) * pr *
        (((Fintype.card (Move d ν) : ℝ) * pr) ^ (N - 1) / (1 - (Fintype.card (Move d ν) : ℝ) * pr)) := by
  set L := listsUpTo (Move d ν) (Fintype.card (LatticePlaquette d N))
  set φ : List (Move d ν) → ℝ := fun ms => if N - 1 ≤ ms.length then pr ^ ms.length else 0 with hφ
  have hφ0 : ∀ ms, 0 ≤ φ ms := fun ms => by simp only [hφ]; split_ifs <;> positivity
  have hterm : ∀ i ∈ walkW a hμν c, pr ^ (walkX hμν i).card = pr * φ i.2 := by
    intro i hi
    obtain ⟨-, hc, ha, hnd, hns, hend⟩ := mem_filter.mp hi
    have hlen := length_ge_of_cross a hN hμν c (siteShift d N i.1 μ) (by rw [siteShift_apply_ne' _ hμν, hc])
      (by rw [siteShift_apply_self', ha]) i.2 hns hend
    rw [card_walkX a hμν c hi]; simp only [hφ, if_pos hlen, pow_succ]; ring
  calc ∑ i ∈ walkW a hμν c, pr ^ (walkX hμν i).card
      = ∑ i ∈ walkW a hμν c, pr * φ i.2 := sum_congr rfl hterm
    _ ≤ ∑ i ∈ (univ : Finset (FinLatticeSites d N)) ×ˢ L, pr * φ i.2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ => mul_nonneg hpr0 (hφ0 _)
    _ = ∑ _y : FinLatticeSites d N, ∑ ms ∈ L, pr * φ ms := sum_product _ _ _
    _ = Fintype.card (FinLatticeSites d N) * pr * ∑ ms ∈ L, φ ms := by
        rw [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]; ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left (sum_listsUpTo_le (Move d ν) hpr0 hq _ _) (by positivity)

/-- `A` pins the sheet in every layer. -/
def SurvAll (hμν : μ ≠ ν) (A : Finset (LatticePlaquette d N)) : Prop := ∀ c : ZMod N, SurvLayer a hμν c A

/-- **The count over configurations that pin the sheet in every layer.** With `0 ≤ h ≤ p (1 + h)` and
    `q = |moves| · p < 1`: `∑_{A pins every layer} ∏_A h ≤ (V p q^{N−1}/(1 − q))^N ∏ (1 + h)`. -/
theorem sum_surv_sheet_le (hN : 1 < N) (hμν : μ ≠ ν) (h : LatticePlaquette d N → ℝ) {pr : ℝ} (hpr0 : 0 ≤ pr)
    (hq : (Fintype.card (Move d ν) : ℝ) * pr < 1) (h0 : ∀ p, 0 ≤ h p) (hle : ∀ p, h p ≤ pr * (1 + h p)) :
    ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter (SurvAll a hμν), ∏ p ∈ A, h p ≤
      (Fintype.card (FinLatticeSites d N) * pr *
        (((Fintype.card (Move d ν) : ℝ) * pr) ^ (N - 1) / (1 - (Fintype.card (Move d ν) : ℝ) * pr))) ^ N *
        ∏ p, (1 + h p) := by
  set b := Fintype.card (FinLatticeSites d N) * pr *
    (((Fintype.card (Move d ν) : ℝ) * pr) ^ (N - 1) / (1 - (Fintype.card (Move d ν) : ℝ) * pr)) with hb
  set W := Fintype.piFinset (fun c : ZMod N => walkW a hμν c)
  set X : (ZMod N → FinLatticeSites d N × List (Move d ν)) → Finset (LatticePlaquette d N) :=
    fun i => univ.biUnion (fun c => walkX hμν (i c)) with hX
  have hw : ∀ A, SurvAll a hμν A → ∃ i ∈ W, X i ⊆ A := by
    intro A hA
    have hex := fun c => exists_witness a hμν c A (hA c)
    choose i hi hsub using hex
    refine ⟨i, Fintype.mem_piFinset.mpr hi, fun p hp => ?_⟩
    obtain ⟨c, -, hpc⟩ := mem_biUnion.mp hp
    exact hsub c hpc
  have hcard : ∀ i ∈ W, (X i).card = ∑ c, (walkX hμν (i c)).card := by
    intro i hi
    rw [card_biUnion]
    intro c _ c' _ hcc'
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    have e1 := walkX_site a hμν c (Fintype.mem_piFinset.mp hi c) p hp
    have e2 := walkX_site a hμν c' (Fintype.mem_piFinset.mp hi c') p hp'
    exact hcc' (e1.symm.trans e2)
  have hB : ∑ i ∈ W, pr ^ (X i).card ≤ b ^ N := by
    calc ∑ i ∈ W, pr ^ (X i).card
        = ∑ i ∈ W, ∏ c, pr ^ (walkX hμν (i c)).card :=
          sum_congr rfl fun i hi => by rw [hcard i hi, prod_pow_eq_pow_sum]
      _ = ∏ c, ∑ i ∈ walkW a hμν c, pr ^ (walkX hμν i).card :=
          (prod_univ_sum (fun c => walkW a hμν c) (fun _ i => pr ^ (walkX hμν i).card)).symm
      _ ≤ ∏ _c : ZMod N, b :=
          prod_le_prod₀ (fun c _ => sum_nonneg fun _ _ => pow_nonneg hpr0 _) fun c _ =>
            sum_walkW_le a hN hμν c hpr0 hq
      _ = b ^ N := by rw [prod_const, card_univ, ZMod.card]
  have hmain := sum_surv_le h h0 hle (SurvAll a hμν) W X hw
  exact hmain.trans (mul_le_mul_of_nonneg_right hB (prod_nonneg fun p _ => by linarith [h0 p]))

end Sheet

end ProofPhase.Saturation
