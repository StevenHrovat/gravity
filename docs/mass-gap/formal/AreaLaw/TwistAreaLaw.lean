/-
The area law by the centre twist, for SU(n) (every n ≥ 2), U(n) and any compact group with a nontrivial central element
(area-law project, 2026-11-21). Released under Apache 2.0.

Idea as in B. G. Srivats, fisher-lorentz-formalization (`Confinement/AreaLaw.lean`, README "The proof"), and Osterwalder–Seiler
1978; the proof here is written independently, in this project's framework (`AreaLaw.Lattice`, `WilsonLoop`, `productHaar`,
`TwistVanish`, `TwistWalks`).

# Statement

`G` a compact group (Haar probability measure, left invariant), a continuous representation with `‖tr‖ ≤ n`, a central `z` with
`rep z = ω I`, `ω ≠ 1`. Wilson action `β Re tr U_p` (any sign of `β`) on the periodic lattice `(ℤ/Nℤ)^d`, the `R × T` rectangle `C`
in the plane `(μ, ν)` (`R < N`, `T ≤ N`), the complex Wilson loop `W_C = tr rep(U_C)`:

  |⟨W_C⟩| ≤ n · (q^{min(R, N−R)} / (1 − q))^T = n · q^{T·min(R, N−R)} · (1 − q)^{−T},   q = 2 (d − 1) (1 − e^{−2n|β|}) < 1.

So `|⟨W_C⟩| ≤ n e^{−σ · area} e^{κ T}` with `σ = log(1/q)`, `κ = log(1/(1 − q))` (`wilson_area_law_twist`; real part:
`wilson_area_law_twist_re`). No cluster expansion is used; the window `q < 1` is `|β| < log((2d − 2)/(2d − 3)) / (2n)`, for
`d = 4`: `|β| < log(6/5) / (2n)`, i.e. `|β| < 0.0456` for SU(2) and `|β| < 0.0304` for SU(3) (this `β` multiplies `Re tr U_p`; in
the usual normalisation `β_std = n β`, the window is `β_std < log(6/5)/2 ≈ 0.0912` for every `n`).

# Proof

1. Each plaquette weight is `e^{−n|β|} (1 + h_p)`, `0 ≤ h_p ≤ p (1 + h_p)`, `p = 1 − e^{−2n|β|}` (`twistH`). Expand `∏ (1 + h_p)`
   over plaquette sets `A`.
2. **Slabs.** For each of the `T` layers `j` of `ν`-links crossed by the loop, let `D` be the set of sites of that layer reachable from
   the loop's right side by moves across plaquettes of `A` (`EdgeA`). If `D` does not contain the left side, multiply the `ν`-links
   of the layer starting in `D` by `z`: every plaquette of `A` has twist count `0` (`plaq_tcount_zero`) and the loop has twist count
   `1` (`tcount_rect`), so the term vanishes (`twist_term_vanish`).
3. **Counting.** A surviving `A` contains, in each layer, a walk with distinct plaquettes from the right side to the left side (loop
   erasure); it has at least `min(R, N − R)` steps, and the layers are disjoint. `∑_{A ⊇ X} ∏_A h ≤ p^{|X|} ∏ (1 + h)` and the
   walk count (`2 (d − 1)` moves per step) give the bound (`sum_surv_rect_le`).

Strong coupling only; known physics (Osterwalder–Seiler 1978); an independent formalisation. Nothing about weak coupling or the
continuum limit.
-/

import AreaLaw.ConcreteSUn
import AreaLaw.TwistVanish
import AreaLaw.TwistWalks

open scoped Classical

open Finset MeasureTheory AreaLaw.Assembly AreaLaw.Clustering AreaLaw.Concrete AreaLaw.ConcreteSUn

set_option linter.unusedSectionVars false

noncomputable section

namespace AreaLaw.Twist

/-! ## 1. Geometry of the rectangle and the slabs -/

section Geometry

variable {d N : ℕ}

/-- A move from `y` to `y'` across a plaquette of `A`. -/
def EdgeA (ν : Fin d) (A : Finset (LatticePlaquette d N)) (y y' : FinLatticeSites d N) : Prop :=
  ∃ m : Move d ν, mstep y m = y' ∧ mlab y m ∈ A

/-- The right side of the rectangle in layer `j`: `x + R μ̂ + j ν̂`. -/
def rsite (x : FinLatticeSites d N) (μ ν : Fin d) (R j : ℕ) : FinLatticeSites d N := siteShiftN (siteShiftN x μ R) ν j

/-- The left side of the rectangle in layer `j`: `x + j ν̂`. -/
def lsite (x : FinLatticeSites d N) (ν : Fin d) (j : ℕ) : FinLatticeSites d N := siteShiftN x ν j

/-- `A` survives every slab: in each layer the right side reaches the left side across plaquettes of `A`. -/
def RectSurv (x : FinLatticeSites d N) (μ ν : Fin d) (R T : ℕ) (A : Finset (LatticePlaquette d N)) : Prop :=
  ∀ j : Fin T, Relation.ReflTransGen (EdgeA ν A) (rsite x μ ν R j) (lsite x ν j)

theorem siteShiftN_apply_self (y : FinLatticeSites d N) (ν : Fin d) (i : ℕ) : siteShiftN y ν i ν = y ν + i := by
  simp [siteShiftN]

theorem siteShiftN_apply_ne (y : FinLatticeSites d N) {μ ν : Fin d} (h : μ ≠ ν) (k : ℕ) : siteShiftN y μ k ν = y ν := by
  simp [siteShiftN, Function.update_of_ne (Ne.symm h)]

theorem natCast_inj_of_lt {i j : ℕ} (hi : i < N) (hj : j < N) (h : (i : ZMod N) = (j : ZMod N)) : i = j := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

theorem reach_apply_self {ν : Fin d} {A : Finset (LatticePlaquette d N)} {a b : FinLatticeSites d N}
    (h : Relation.ReflTransGen (EdgeA ν A) a b) : b ν = a ν := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    obtain ⟨m, hm, -⟩ := hbc
    rw [← hm, mstep_apply_self]; exact ih

theorem tcount_plaquettePath (S : Finset (LatticeLink d N)) (p : LatticePlaquette d N) :
    tcount S (plaquettePath p) = (if p.boundaryLinks 0 ∈ S then 1 else 0) + (if p.boundaryLinks 1 ∈ S then 1 else 0)
      - (if p.boundaryLinks 2 ∈ S then 1 else 0) - (if p.boundaryLinks 3 ∈ S then 1 else 0) := by
  simp only [plaquettePath, tcount, stepCount, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> norm_num

/-- **Plaquettes of `A` do not see the twist.** If the predicate `Q` on sites is unchanged across every plaquette of `A` lying in a
    plane `(ν, ρ)`, the twist of the `ν`-links starting in `Q` leaves every plaquette of `A` unchanged. -/
theorem plaq_tcount_zero [Fintype (LatticeLink d N)] (ν : Fin d) (Q : FinLatticeSites d N → Prop)
    (A : Finset (LatticePlaquette d N))
    (hQ : ∀ y (ρ : {ρ : Fin d // ρ ≠ ν}), mlab y (ρ, true) ∈ A → (Q y ↔ Q (siteShift d N y ρ.1)))
    (p : LatticePlaquette d N) (hp : p ∈ A) :
    tcount (univ.filter (fun l : LatticeLink d N => l.dir = ν ∧ Q l.site)) (plaquettePath p) = 0 := by
  rw [tcount_plaquettePath]
  obtain ⟨s, a, b, hab⟩ := p
  simp only [LatticePlaquette.boundaryLinks, mem_filter, mem_univ, true_and]
  by_cases ha : a = ν
  · subst ha
    have hb : b ≠ a := ne_of_gt hab
    have hpl : mlab s ((⟨b, hb⟩ : {ρ : Fin d // ρ ≠ a}), true) = ⟨s, a, b, hab⟩ := by
      simp only [mlab, mbase, ↓reduceIte]; exact mkPlaq_of_lt s hb hab
    have key := hQ s ⟨b, hb⟩ (by rw [hpl]; exact hp)
    rcases em (Q s) with h1 | h1
    · simp [hb, h1, key.mp h1]
    · simp [hb, h1, mt key.mpr h1]
  · by_cases hb : b = ν
    · subst hb
      have hpl : mlab s ((⟨a, ha⟩ : {ρ : Fin d // ρ ≠ b}), true) = ⟨s, a, b, hab⟩ := by
        simp only [mlab, mbase, ↓reduceIte]; exact mkPlaq_of_gt s ha hab
      have key := hQ s ⟨a, ha⟩ (by rw [hpl]; exact hp)
      rcases em (Q s) with h1 | h1
      · simp [ha, h1, key.mp h1]
      · simp [ha, h1, mt key.mpr h1]
    · simp [ha, hb]

theorem mem_straightFwd_dir (μ : Fin d) :
    ∀ (k : ℕ) (y : FinLatticeSites d N) (s : PathStep d N), s ∈ straightFwd y μ k → s.link.dir = μ
  | 0, y, s, h => by simp [straightFwd] at h
  | k + 1, y, s, h => by
    simp only [straightFwd, List.mem_cons] at h
    rcases h with h | h
    · rw [h]
    · exact mem_straightFwd_dir μ k _ s h

theorem mem_straightBwd_dir (μ : Fin d) :
    ∀ (k : ℕ) (y : FinLatticeSites d N) (s : PathStep d N), s ∈ straightBwd y μ k → s.link.dir = μ
  | 0, y, s, h => by simp [straightBwd] at h
  | k + 1, y, s, h => by
    simp only [straightBwd, List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · exact mem_straightBwd_dir μ k _ s h
    · rw [h]

theorem tcount_straightFwd (S : Finset (LatticeLink d N)) (ν : Fin d) : ∀ (k : ℕ) (y : FinLatticeSites d N),
    tcount S (straightFwd y ν k) = ∑ i ∈ range k, (if (⟨siteShiftN y ν i, ν⟩ : LatticeLink d N) ∈ S then 1 else 0)
  | 0, y => by simp [straightFwd, tcount]
  | k + 1, y => by
    rw [straightFwd, tcount_cons, tcount_straightFwd S ν k, sum_range_succ']
    simp only [stepCount, ↓reduceIte, siteShiftN_zero, siteShiftN_succ']
    ring

theorem tcount_straightBwd (S : Finset (LatticeLink d N)) (ν : Fin d) : ∀ (k : ℕ) (y : FinLatticeSites d N),
    tcount S (straightBwd y ν k) = -∑ i ∈ range k, (if (⟨siteShiftN y ν i, ν⟩ : LatticeLink d N) ∈ S then 1 else 0)
  | 0, y => by simp [straightBwd, tcount]
  | k + 1, y => by
    rw [straightBwd, tcount_append, tcount_straightBwd S ν k, sum_range_succ']
    simp only [tcount, stepCount, Bool.false_eq_true, ↓reduceIte, siteShiftN_zero, siteShiftN_succ']
    split_ifs <;> ring

/-- **The loop sees the twist once.** If `Q` holds only in layer `j` of the `ν`-links, holds at the right side and fails at the left
    side, the rectangle passes the twisted links with signed count `1`. -/
theorem tcount_rect [Fintype (LatticeLink d N)] (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) (R T : ℕ)
    (hT : T ≤ N) (j : ℕ) (hj : j < T) (Q : FinLatticeSites d N → Prop) (hQν : ∀ y, Q y → y ν = x ν + j)
    (hr : Q (rsite x μ ν R j)) (hl : ¬ Q (lsite x ν j)) :
    tcount (univ.filter (fun l : LatticeLink d N => l.dir = ν ∧ Q l.site)) (rectPath x μ ν R T) = 1 := by
  set S := univ.filter (fun l : LatticeLink d N => l.dir = ν ∧ Q l.site) with hS
  have hnotμ : ∀ s : PathStep d N, s.link.dir = μ → s.link ∉ S := fun s hs hm => by
    rw [hS, mem_filter] at hm; exact hμν (hs.symm.trans hm.2.1)
  have hmemν : ∀ y : FinLatticeSites d N, ((⟨y, ν⟩ : LatticeLink d N) ∈ S ↔ Q y) := fun y => by simp [hS]
  have honly : ∀ y : FinLatticeSites d N, y ν = x ν → ∀ i, i < T → Q (siteShiftN y ν i) → i = j := by
    intro y hy i hi hQ
    have h1 := hQν _ hQ
    rw [siteShiftN_apply_self, hy] at h1
    exact natCast_inj_of_lt (by omega) (by omega) (add_left_cancel h1)
  have e1 : ∑ i ∈ range T, (if (⟨siteShiftN (siteShiftN x μ R) ν i, ν⟩ : LatticeLink d N) ∈ S then (1 : ℤ) else 0) = 1 := by
    rw [sum_eq_single j]
    · exact ite_eq_left ((hmemν (siteShiftN (siteShiftN x μ R) ν j)).mpr hr)
    · intro i hi hij
      rw [ite_eq_right]
      exact fun hm => hij (honly _ (siteShiftN_apply_ne x hμν R) i (mem_range.mp hi) ((hmemν _).mp hm))
    · intro hj'; exact absurd (mem_range.mpr hj) hj'
  have e2 : ∑ i ∈ range T, (if (⟨siteShiftN x ν i, ν⟩ : LatticeLink d N) ∈ S then (1 : ℤ) else 0) = 0 := by
    refine sum_eq_zero fun i hi => ?_
    rw [ite_eq_right]
    intro hm
    have hQ := (hmemν _).mp hm
    have := honly x rfl i (mem_range.mp hi) hQ
    subst this
    exact hl hQ
  unfold rectPath
  rw [tcount_append, tcount_append, tcount_append,
    tcount_eq_zero_of_forall S _ (fun s hs => hnotμ s (mem_straightFwd_dir μ R x s hs)),
    tcount_eq_zero_of_forall S _ (fun s hs => hnotμ s (mem_straightBwd_dir μ R _ s hs)),
    tcount_straightFwd, tcount_straightBwd, e1, e2]
  norm_num

/-! ## 2. Walks in the slabs and the count -/

theorem walk_of_reach {ν : Fin d} {A : Finset (LatticePlaquette d N)} {a b : FinLatticeSites d N}
    (h : Relation.ReflTransGen (EdgeA ν A) a b) :
    ∃ ms : List (Move d ν), walkEnd mstep a ms = b ∧ ∀ p ∈ walkLabels mstep mlab a ms, p ∈ A := by
  induction h with
  | refl => exact ⟨[], rfl, by simp [walkLabels]⟩
  | tail _ hbc ih =>
    obtain ⟨ms, he, hl⟩ := ih
    obtain ⟨m, hm, hA⟩ := hbc
    refine ⟨ms ++ [m], by rw [walkEnd_append, he]; exact hm, fun p hp => ?_⟩
    rw [walkLabels_append, he, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hl p hp
    · simp only [walkLabels, List.mem_singleton] at hp; rw [hp]; exact hA

/-- Walks from `a` to `b` with distinct plaquettes (so of length at most the number of plaquettes). -/
def goodWalks [Fintype (LatticePlaquette d N)] (ν : Fin d) (a b : FinLatticeSites d N) : Finset (List (Move d ν)) :=
  (listsUpTo (Move d ν) (Fintype.card (LatticePlaquette d N))).filter
    (fun ms => walkEnd mstep a ms = b ∧ (walkLabels mstep mlab a ms).Nodup)

theorem good_of_reach [Fintype (LatticePlaquette d N)] {ν : Fin d} {A : Finset (LatticePlaquette d N)}
    {a b : FinLatticeSites d N} (h : Relation.ReflTransGen (EdgeA ν A) a b) :
    ∃ ms ∈ goodWalks ν a b, ∀ p ∈ walkLabels mstep mlab a ms, p ∈ A := by
  obtain ⟨ms, he, hl⟩ := walk_of_reach h
  obtain ⟨ms', he', hnd, hsub⟩ := exists_nodup_walk mstep mlab (fun y m y' m' e => mlab_eq y m y' m' e) ms a
  refine ⟨ms', mem_filter.mpr ⟨mem_listsUpTo _ _ _ ?_, he'.trans he, hnd⟩, fun p hp => hl p (hsub p hp)⟩
  rw [← length_walkLabels mstep mlab a ms']
  exact hnd.length_le_card

/-- A walk in a slab from the right side to the left side has at least `min(R, N − R)` steps. -/
theorem length_ge_of_walk (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) {R : ℕ} (hR : R < N) (j : ℕ)
    (ms : List (Move d ν)) (he : walkEnd mstep (rsite x μ ν R j) ms = lsite x ν j) : min R (N - R) ≤ ms.length := by
  have h1 := walkEnd_apply_disp μ (rsite x μ ν R j) ms
  rw [he] at h1
  have hl : lsite x ν j μ = x μ := siteShiftN_apply_ne x (Ne.symm hμν) j
  have hr : rsite x μ ν R j μ = x μ + R := by
    simp only [rsite, siteShiftN_apply_ne _ (Ne.symm hμν), siteShiftN_apply_self]
  rw [hl, hr] at h1
  set k := (ms.map (mdisp μ)).sum
  have hk : ((-k : ℤ) : ZMod N) = (R : ZMod N) := by push_cast; linear_combination h1
  have h2 := min_le_natAbs_of_cast_eq hR hk
  rw [Int.natAbs_neg] at h2
  have h4 : (k.natAbs : ℤ) ≤ ms.length := by rw [Int.natCast_natAbs]; exact abs_sum_mdisp_le μ ms
  exact h2.trans (by exact_mod_cast h4)

theorem walkLabels_rsite_site (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) (R j : ℕ) (ms : List (Move d ν)) :
    ∀ p ∈ walkLabels mstep mlab (rsite x μ ν R j) ms, p.site ν = x ν + j := fun p hp => by
  rw [walkLabels_site _ ms p hp]
  simp only [rsite, siteShiftN_apply_self, siteShiftN_apply_ne _ hμν]

/-- **The count over survivors.** With `0 ≤ h ≤ p (1 + h)` and `q = 2 (d − 1) p < 1`:
    `∑_{A survives} ∏_A h ≤ (q^{min(R, N−R)} / (1 − q))^T ∏ (1 + h)`. -/
theorem sum_surv_rect_le [NeZero N] (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) {R T : ℕ} (hR : R < N)
    (hT : T ≤ N) (h : LatticePlaquette d N → ℝ) {pr : ℝ} (hpr0 : 0 ≤ pr)
    (hq : (Fintype.card (Move d ν) : ℝ) * pr < 1) (h0 : ∀ p, 0 ≤ h p) (hle : ∀ p, h p ≤ pr * (1 + h p)) :
    ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter (RectSurv x μ ν R T), ∏ p ∈ A, h p ≤
      (((Fintype.card (Move d ν) : ℝ) * pr) ^ (min R (N - R)) / (1 - (Fintype.card (Move d ν) : ℝ) * pr)) ^ T *
        ∏ p, (1 + h p) := by
  set q := (Fintype.card (Move d ν) : ℝ) * pr with hqdef
  set good : Fin T → Finset (List (Move d ν)) := fun j => goodWalks ν (rsite x μ ν R j) (lsite x ν j) with hgooddef
  set X : (Fin T → List (Move d ν)) → Finset (LatticePlaquette d N) :=
    fun ms => univ.biUnion (fun j : Fin T => (walkLabels mstep mlab (rsite x μ ν R j) (ms j)).toFinset) with hX
  have hw : ∀ A, RectSurv x μ ν R T A → ∃ ms ∈ Fintype.piFinset good, X ms ⊆ A := by
    intro A hA
    have hex := fun j => good_of_reach (hA j)
    choose ms hms hsub using hex
    refine ⟨ms, Fintype.mem_piFinset.mpr hms, fun p hp => ?_⟩
    obtain ⟨j, -, hpj⟩ := mem_biUnion.mp hp
    exact hsub j p (List.mem_toFinset.mp hpj)
  have hcard : ∀ ms ∈ Fintype.piFinset good, (X ms).card = ∑ j, (ms j).length := by
    intro ms hms
    rw [card_biUnion]
    · refine sum_congr rfl fun j _ => ?_
      rw [List.toFinset_card_of_nodup (mem_filter.mp (Fintype.mem_piFinset.mp hms j)).2.2, length_walkLabels]
    · intro j _ j' _ hjj'
      rw [Function.onFun, Finset.disjoint_left]
      intro p hp hp'
      have e1 := walkLabels_rsite_site x hμν R j (ms j) p (List.mem_toFinset.mp hp)
      have e2 := walkLabels_rsite_site x hμν R j' (ms j') p (List.mem_toFinset.mp hp')
      have hj1 := j.2
      have hj2 := j'.2
      exact hjj' (Fin.ext (natCast_inj_of_lt (by omega) (by omega) (add_left_cancel (e1.symm.trans e2))))
  have hgood : ∀ j, ∑ ms ∈ good j, pr ^ ms.length ≤ q ^ (min R (N - R)) / (1 - q) := fun j =>
    sum_filter_listsUpTo_le (Move d ν) hpr0 hq _ _ _ (fun ms hms => length_ge_of_walk x hμν hR j ms hms.1)
  have hB : ∑ ms ∈ Fintype.piFinset good, pr ^ (X ms).card ≤ (q ^ (min R (N - R)) / (1 - q)) ^ T := by
    calc ∑ ms ∈ Fintype.piFinset good, pr ^ (X ms).card
        = ∑ ms ∈ Fintype.piFinset good, ∏ j, pr ^ (ms j).length :=
          sum_congr rfl fun ms hms => by rw [hcard ms hms, prod_pow_eq_pow_sum]
      _ = ∏ j, ∑ ms ∈ good j, pr ^ ms.length := (prod_univ_sum good (fun _ ms => pr ^ ms.length)).symm
      _ ≤ ∏ _j : Fin T, q ^ (min R (N - R)) / (1 - q) :=
          prod_le_prod₀ (fun j _ => sum_nonneg fun _ _ => pow_nonneg hpr0 _) fun j _ => hgood j
      _ = _ := by rw [prod_const, card_univ, Fintype.card_fin]
  have hmain := sum_surv_le h h0 hle (RectSurv x μ ν R T) (Fintype.piFinset good) X hw
  exact hmain.trans (mul_le_mul_of_nonneg_right hB (prod_nonneg fun p _ => by linarith [h0 p]))

end Geometry

/-! ## 3. The analytic bound -/

section Analytic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n] {d N : ℕ}

/-- The plaquette weight minus one, normalised to be `≥ 0`: `e^{β x_p + n|β|} − 1`. -/
def twistH (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (p : LatticePlaquette d N) (U : GaugeConnection G d N) : ℝ :=
  Real.exp (β * xp n p U + n * |β|) - 1

variable (hbd : ∀ g : G, |gaugeReTr G n g| ≤ n)

include hbd in
theorem twistH_expo (β : ℝ) (p : LatticePlaquette d N) (U : GaugeConnection G d N) :
    0 ≤ β * xp n p U + n * |β| ∧ β * xp n p U + n * |β| ≤ 2 * n * |β| := by
  have h : |β * xp n p U| ≤ n * |β| := by
    rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hbd _) (abs_nonneg β)
  have h' := abs_le.mp h
  constructor <;> linarith [h'.1, h'.2]

include hbd in
theorem twistH_nonneg (β : ℝ) (p : LatticePlaquette d N) (U : GaugeConnection G d N) : 0 ≤ twistH n β p U := by
  unfold twistH; linarith [Real.one_le_exp (twistH_expo hbd β p U).1]

include hbd in
theorem twistH_le (β : ℝ) (p : LatticePlaquette d N) (U : GaugeConnection G d N) :
    twistH n β p U ≤ Real.exp (2 * n * |β|) - 1 := by
  unfold twistH; linarith [Real.exp_le_exp.mpr (twistH_expo hbd β p U).2]

include hbd in
/-- `h ≤ p (1 + h)` with `p = 1 − e^{−2n|β|}`. -/
theorem twistH_le_mul (β : ℝ) (p : LatticePlaquette d N) (U : GaugeConnection G d N) :
    twistH n β p U ≤ (1 - Real.exp (-(2 * n * |β|))) * (1 + twistH n β p U) := by
  unfold twistH
  set s := β * xp n p U + n * |β|
  have hs := (twistH_expo hbd β p U).2
  have h1 : Real.exp s * Real.exp (-(2 * n * |β|)) ≤ 1 := by
    rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith)
  nlinarith

theorem one_add_twistH (β : ℝ) (p : LatticePlaquette d N) (U : GaugeConnection G d N) :
    1 + twistH n β p U = Real.exp (n * |β|) * Real.exp (β * xp n p U) := by
  unfold twistH
  rw [add_sub_cancel, ← Real.exp_add]
  congr 1; ring

theorem prod_one_add_twistH [Fintype (LatticePlaquette d N)] (β : ℝ) (U : GaugeConnection G d N) :
    ∏ p, (1 + twistH n β p U) = Real.exp (n * |β|) ^ Fintype.card (LatticePlaquette d N) * wW n β U := by
  simp_rw [one_add_twistH]
  rw [prod_mul_distrib, prod_const, card_univ]
  rfl

theorem measurable_wilsonLoopC (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (C : List (PathStep d N)) :
    Measurable (wilsonLoopC (G := G) n C) := by
  have : Continuous (gaugeTrace G n) := hc.matrix_trace
  exact this.measurable.comp (measurable_pathHol C)

variable [HasHaarProbability G] [NeZero N]

omit hbd in
/-- **The analytic bound.** If every term with `A` not surviving vanishes, and the surviving sum is at most `B ∏ (1 + h)` pointwise,
    then the partition function is positive and `|⟨W_C⟩| ≤ n B`. -/
theorem twist_bound_of_comb (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (hbdC : ∀ g : G, ‖gaugeTrace G n g‖ ≤ n) (β : ℝ) (C : List (PathStep d N))
    (Surv : Finset (LatticePlaquette d N) → Prop) [DecidablePred Surv] (B : ℝ)
    (hvan : ∀ A, ¬ Surv A →
      ∫ U, wilsonLoopC n C U * ((∏ p ∈ A, twistH n β p U : ℝ) : ℂ) ∂(productHaar G d N) = 0)
    (hcomb : ∀ U : GaugeConnection G d N, ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter Surv,
      ∏ p ∈ A, twistH n β p U ≤ B * ∏ p, (1 + twistH n β p U)) :
    0 < ∫ U, wW n β U ∂(productHaar G d N) ∧
    ‖(∫ U, wilsonLoopC n C U * (wW n β U : ℂ) ∂(productHaar G d N)) /
      ((∫ U, wW n β U ∂(productHaar G d N) : ℝ) : ℂ)‖ ≤ n * B := by
  have hbd : ∀ g : G, |gaugeReTr G n g| ≤ n := fun g => (Complex.abs_re_le_norm _).trans (hbdC g)
  have hmeas := measurable_xp (d := d) (N := N) hc
  set μ := productHaar G d N with hμ
  set c := Fintype.card (LatticePlaquette d N) with hc'
  set E := Real.exp (n * |β|) ^ c with hE
  have hE0 : 0 < E := by positivity
  set M := Real.exp (2 * n * |β|) - 1 with hM
  have mW := measurable_wilsonLoopC (d := d) (N := N) hc C
  have mh : ∀ p, Measurable (twistH (G := G) n β p) := fun p =>
    (((hmeas p).const_mul β).add_const _).exp.sub_const 1
  have mprod : ∀ A : Finset (LatticePlaquette d N), Measurable fun U : GaugeConnection G d N => ∏ p ∈ A, twistH n β p U :=
    fun A => Finset.measurable_prod _ fun p _ => mh p
  have hprod0 : ∀ (A : Finset (LatticePlaquette d N)) (U : GaugeConnection G d N), 0 ≤ ∏ p ∈ A, twistH n β p U :=
    fun A U => prod_nonneg fun p _ => twistH_nonneg hbd β p U
  have hprodM : ∀ (A : Finset (LatticePlaquette d N)) (U : GaugeConnection G d N), ∏ p ∈ A, twistH n β p U ≤ M ^ A.card :=
    fun A U => by
      rw [← prod_const]; exact prod_le_prod₀ (fun p _ => twistH_nonneg hbd β p U) (fun p _ => twistH_le hbd β p U)
  have intA : ∀ A : Finset (LatticePlaquette d N), Integrable (fun U => ∏ p ∈ A, twistH n β p U) μ := fun A =>
    Integrable.of_bound (mprod A).aestronglyMeasurable (M ^ A.card) (Filter.Eventually.of_forall fun U => by
      rw [Real.norm_of_nonneg (hprod0 A U)]; exact hprodM A U)
  set F : Finset (LatticePlaquette d N) → GaugeConnection G d N → ℂ :=
    fun A U => wilsonLoopC n C U * ((∏ p ∈ A, twistH n β p U : ℝ) : ℂ) with hF
  have mF : ∀ A, Measurable (F A) := fun A => mW.mul (Complex.measurable_ofReal.comp (mprod A))
  have hFb : ∀ A U, ‖F A U‖ ≤ n * ∏ p ∈ A, twistH n β p U := fun A U => by
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hprod0 A U)]
    exact mul_le_mul_of_nonneg_right (hbdC _) (hprod0 A U)
  have intF : ∀ A, Integrable (F A) μ := fun A =>
    Integrable.of_bound (mF A).aestronglyMeasurable (n * M ^ A.card) (Filter.Eventually.of_forall fun U =>
      (hFb A U).trans (mul_le_mul_of_nonneg_left (hprodM A U) (Nat.cast_nonneg n)))
  have hTb : ∀ A, ‖∫ U, F A U ∂μ‖ ≤ n * ∫ U, ∏ p ∈ A, twistH n β p U ∂μ := fun A => by
    rw [← integral_const_mul]
    exact norm_integral_le_of_norm_le ((intA A).const_mul _) (Filter.Eventually.of_forall (hFb A))
  have hexp : ∀ U, wilsonLoopC n C U * (((∏ p, (1 + twistH n β p U)) : ℝ) : ℂ) =
      ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset, F A U := fun U => by
    rw [prod_one_add, Complex.ofReal_sum, mul_sum]
  have hW : ∀ U : GaugeConnection G d N, (((∏ p, (1 + twistH n β p U)) : ℝ) : ℂ) = (E : ℂ) * (wW n β U : ℂ) :=
    fun U => by rw [prod_one_add_twistH β U, Complex.ofReal_mul]
  have hWb := wW_bounds hbd (d := d) (N := N) β
  have mWw : Measurable (wW (G := G) (d := d) (N := N) n β) := measurable_wW hmeas β
  have hW0 : ∀ U, 0 ≤ wW n β U := fun U => (pow_nonneg (Real.exp_pos _).le _).trans (hWb U).1
  have iW : Integrable (wW (G := G) (d := d) (N := N) n β) μ :=
    Integrable.of_bound mWw.aestronglyMeasurable (Real.exp (n * |β|) ^ c) (Filter.Eventually.of_forall fun U => by
      rw [Real.norm_of_nonneg (hW0 U)]; exact (hWb U).2)
  set Z := ∫ U, wW n β U ∂μ with hZ
  have hZ0 : 0 < Z := by
    have h1 : ∫ _U, Real.exp (-(n * |β|)) ^ c ∂μ ≤ Z := integral_mono (integrable_const _) iW fun U => (hWb U).1
    have h2 : ∫ _U, Real.exp (-(n * |β|)) ^ c ∂μ = Real.exp (-(n * |β|)) ^ c := by simp
    have h3 : 0 < Real.exp (-(n * |β|)) ^ c := by positivity
    linarith
  set Num := ∫ U, wilsonLoopC n C U * (wW n β U : ℂ) ∂μ with hNum
  have hNumE : (E : ℂ) * Num = ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset, ∫ U, F A U ∂μ := by
    rw [hNum, ← integral_const_mul, ← integral_finsetSum _ fun A _ => intF A]
    congr 1; funext U; rw [← hexp U, hW U]; ring
  have hD : ∀ U : GaugeConnection G d N,
      ∏ p, (1 + twistH n β p U) = ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset, ∏ p ∈ A, twistH n β p U :=
    fun U => prod_one_add _
  have intD : Integrable (fun U => ∏ p, (1 + twistH n β p U)) μ := by
    simp_rw [hD]; exact integrable_finsetSum _ fun A _ => intA A
  have hden : ∫ U, ∏ p, (1 + twistH n β p U) ∂μ = E * Z := by
    simp_rw [prod_one_add_twistH β]; rw [integral_const_mul]
  have hsumI : ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter Surv,
      ∫ U, ∏ p ∈ A, twistH n β p U ∂μ ≤ B * (E * Z) := by
    rw [← integral_finsetSum _ fun A _ => intA A, ← hden, ← integral_const_mul]
    exact integral_mono (integrable_finsetSum _ fun A _ => intA A) (intD.const_mul B) hcomb
  have hmain : E * ‖Num‖ ≤ n * (B * (E * Z)) := by
    have h1 : ‖(E : ℂ) * Num‖ = E * ‖Num‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hE0.le]
    rw [← h1, hNumE]
    calc ‖∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset, ∫ U, F A U ∂μ‖
        ≤ ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset, ‖∫ U, F A U ∂μ‖ := norm_sum_le _ _
      _ ≤ ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset,
            (if Surv A then n * ∫ U, ∏ p ∈ A, twistH n β p U ∂μ else 0) := by
          refine sum_le_sum fun A _ => ?_
          split_ifs with h
          · exact hTb A
          · rw [show ∫ U, F A U ∂μ = 0 from hvan A h, norm_zero]
      _ = n * ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter Surv,
            ∫ U, ∏ p ∈ A, twistH n β p U ∂μ := by
          rw [← sum_filter, mul_sum]
      _ ≤ n * (B * (E * Z)) := mul_le_mul_of_nonneg_left hsumI (Nat.cast_nonneg n)
  refine ⟨hZ0, ?_⟩
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hZ0.le, div_le_iff₀ hZ0]
  have h2 : E * ‖Num‖ ≤ E * (n * B * Z) := by
    calc E * ‖Num‖ ≤ n * (B * (E * Z)) := hmain
      _ = E * (n * B * Z) := by ring
  exact le_of_mul_le_mul_left h2 hE0

end Analytic

/-! ## 4. The area law by the centre twist -/

/-- The per-plaquette ratio `q = 2 (d − 1) (1 − e^{−2n|β|})` of the centre-twist area law. -/
def twistQ (d n : ℕ) (β : ℝ) : ℝ := 2 * ((d : ℝ) - 1) * (1 - Real.exp (-(2 * n * |β|)))

section Main

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n] {d N : ℕ}

/-- **The area law by the centre twist** (any compact group with a left-invariant Haar probability measure, a continuous
    representation with `‖tr‖ ≤ n`, a central `z` with `rep z = ω I`, `ω ≠ 1`). For `q = 2 (d − 1) (1 − e^{−2n|β|}) < 1`, on
    `(ℤ/Nℤ)^d`, for the `R × T` rectangle in the plane `(μ, ν)` with `R < N`, `T ≤ N`: the partition function is positive and the
    complex Wilson loop satisfies `|⟨tr U_C⟩| ≤ n (q^{min(R, N−R)} / (1 − q))^T = n q^{T min(R, N−R)} (1 − q)^{−T}`. -/
theorem wilson_area_law_twist [HasHaarProbability G] [(haarG G).IsMulLeftInvariant] [NeZero N]
    (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (hbdC : ∀ g : G, ‖gaugeTrace G n g‖ ≤ n)
    (z : G) (hz : ∀ g : G, Commute z g) {ω : ℂ} (hrep : HasGaugeTrace.rep (G := G) (n := n) z = ω • 1) (hω : ω ≠ 1)
    {β : ℝ} (hq : twistQ d n β < 1)
    (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) (R T : ℕ) (hR : R < N) (hT : T ≤ N) :
    0 < ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N) ∧
    ‖(∫ U, wilsonLoopC n (rectPath x μ ν R T) U *
          ((∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) : ℝ) : ℂ) ∂(productHaar G d N)) /
      ((∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N) : ℝ) : ℂ)‖ ≤
      n * (twistQ d n β ^ (min R (N - R)) / (1 - twistQ d n β)) ^ T := by
  have hbd : ∀ g : G, |gaugeReTr G n g| ≤ n := fun g => (Complex.abs_re_le_norm _).trans (hbdC g)
  set pr := 1 - Real.exp (-(2 * n * |β|)) with hpr
  have hpr0 : 0 ≤ pr := by
    have : Real.exp (-(2 * n * |β|)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : (0 : ℝ) ≤ 2 * n * |β| := by positivity
      linarith)
    linarith
  have hcardq : (Fintype.card (Move d ν) : ℝ) * pr = twistQ d n β := by
    have hd : 1 ≤ d := Fin.pos ν
    rw [card_move]; push_cast [Nat.cast_sub hd]; unfold twistQ; ring
  have hq' : (Fintype.card (Move d ν) : ℝ) * pr < 1 := hcardq ▸ hq
  have hzm := measurePreserving_mul_left (haarG G) z
  have hzm' := measurePreserving_mul_left (haarG G) z⁻¹
  have hvan : ∀ A, ¬ RectSurv x μ ν R T A →
      ∫ U, wilsonLoopC n (rectPath x μ ν R T) U * ((∏ p ∈ A, twistH n β p U : ℝ) : ℂ) ∂(productHaar G d N) = 0 := by
    intro A hA
    simp only [RectSurv, not_forall] at hA
    obtain ⟨j, hj⟩ := hA
    set Q := Relation.ReflTransGen (EdgeA ν A) (rsite x μ ν R j) with hQdef
    have hQ : ∀ y (ρ : {ρ : Fin d // ρ ≠ ν}), mlab y (ρ, true) ∈ A → (Q y ↔ Q (siteShift d N y ρ.1)) := by
      intro y ρ hyA
      have e1 : EdgeA ν A y (siteShift d N y ρ.1) := ⟨(ρ, true), mstep_true y ρ, hyA⟩
      have hlab : mlab (siteShift d N y ρ.1) (ρ, false) = mlab y (ρ, true) := by
        simp only [mlab, mbase, Bool.false_eq_true, ↓reduceIte, mstep_false_siteShift]
      have e2 : EdgeA ν A (siteShift d N y ρ.1) y := ⟨(ρ, false), mstep_false_siteShift y ρ, by rw [hlab]; exact hyA⟩
      exact ⟨fun h => h.tail e1, fun h => h.tail e2⟩
    have hQν : ∀ y, Q y → y ν = x ν + (j : ℕ) := fun y hy => by
      rw [reach_apply_self hy]
      simp only [rsite, siteShiftN_apply_self, siteShiftN_apply_ne _ hμν]
    have hcount := tcount_rect x hμν R T hT j j.2 Q hQν Relation.ReflTransGen.refl hj
    have hplaq := fun p hp => plaq_tcount_zero ν Q A hQ p hp
    have h := twist_term_vanish z hz hrep hω hzm hzm' _ _ hcount A hplaq
      (fun _ g => ((Real.exp (β * gaugeReTr G n g + n * |β|) - 1 : ℝ) : ℂ))
    rw [← h]
    congr 1; funext U
    rw [Complex.ofReal_prod]
    rfl
  have hcomb : ∀ U : GaugeConnection G d N,
      ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter (RectSurv x μ ν R T), ∏ p ∈ A, twistH n β p U ≤
        (((Fintype.card (Move d ν) : ℝ) * pr) ^ (min R (N - R)) / (1 - (Fintype.card (Move d ν) : ℝ) * pr)) ^ T *
          ∏ p, (1 + twistH n β p U) := fun U =>
    sum_surv_rect_le x hμν hR hT (fun p => twistH n β p U) hpr0 hq' (fun p => twistH_nonneg hbd β p U)
      (fun p => twistH_le_mul hbd β p U)
  have h := twist_bound_of_comb hc hbdC β (rectPath x μ ν R T) (RectSurv x μ ν R T) _ hvan hcomb
  rw [hcardq] at h
  exact h

/-- **The area law by the centre twist, real part** (the observable `Re tr U_C` of `Assembly`/`Concrete`): same hypotheses and
    bound as `wilson_area_law_twist`. -/
theorem wilson_area_law_twist_re [HasHaarProbability G] [(haarG G).IsMulLeftInvariant] [NeZero N]
    (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (hbdC : ∀ g : G, ‖gaugeTrace G n g‖ ≤ n)
    (z : G) (hz : ∀ g : G, Commute z g) {ω : ℂ} (hrep : HasGaugeTrace.rep (G := G) (n := n) z = ω • 1) (hω : ω ≠ 1)
    {β : ℝ} (hq : twistQ d n β < 1)
    (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) (R T : ℕ) (hR : R < N) (hT : T ≤ N) :
    0 < ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N) ∧
    |(∫ U, wilsonLoop n (rectPath x μ ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N)) /
      (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N))| ≤
      n * (twistQ d n β ^ (min R (N - R)) / (1 - twistQ d n β)) ^ T := by
  obtain ⟨h0, h1⟩ := wilson_area_law_twist hc hbdC z hz hrep hω hq x hμν R T hR hT
  refine ⟨h0, le_trans (le_of_eq ?_) ((Complex.abs_re_le_norm _).trans h1)⟩
  have hbd : ∀ g : G, |gaugeReTr G n g| ≤ n := fun g => (Complex.abs_re_le_norm _).trans (hbdC g)
  set μP := productHaar G d N
  set w : GaugeConnection G d N → ℝ := fun U => ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
    with hw
  have hWb := wW_bounds hbd (d := d) (N := N) β
  have mWw : Measurable w := measurable_wW (measurable_xp hc) β
  have mW := measurable_wilsonLoopC (d := d) (N := N) hc (rectPath x μ ν R T)
  have hint : Integrable (fun U => wilsonLoopC n (rectPath x μ ν R T) U * (w U : ℂ)) μP :=
    Integrable.of_bound (mW.mul (Complex.measurable_ofReal.comp mWw)).aestronglyMeasurable
      (n * Real.exp (n * |β|) ^ Fintype.card (LatticePlaquette d N)) (Filter.Eventually.of_forall fun U => by
        have hw0 : 0 ≤ w U := (pow_nonneg (Real.exp_pos _).le _).trans (hWb U).1
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
        exact mul_le_mul (hbdC _) (hWb U).2 hw0 (Nat.cast_nonneg n))
  have hre := integral_re hint
  simp only [RCLike.re_to_complex, Complex.re_mul_ofReal] at hre
  rw [Complex.div_ofReal_re, ← hre]
  rfl

end Main

/-! ## 5. SU(n), SU(3), SU(2), U(n) -/

variable {d N : ℕ}

/-- **The area law for SU(n) lattice gauge theory by the `Z_n` centre twist**, every `n ≥ 2` (centre `e^{2πi/n} I`). For
    `q = 2 (d − 1) (1 − e^{−2n|β|}) < 1` and the `R × T` rectangle (`R < N`, `T ≤ N`):
    `|⟨tr U_C⟩| ≤ n (q^{min(R, N−R)} / (1 − q))^T`. -/
theorem wilson_area_law_twist_SUn [NeZero N] {n : ℕ} (hn : 2 ≤ n) {β : ℝ} (hq : twistQ d n β < 1)
    (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) (R T : ℕ) (hR : R < N) (hT : T ≤ N) :
    0 < ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar (SUn n) d N) ∧
    ‖(∫ U, wilsonLoopC n (rectPath x μ ν R T) U *
          ((∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) : ℝ) : ℂ) ∂(productHaar (SUn n) d N)) /
      ((∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar (SUn n) d N) : ℝ) : ℂ)‖ ≤
      n * (twistQ d n β ^ (min R (N - R)) / (1 - twistQ d n β)) ^ T :=
  wilson_area_law_twist (G := SUn n) (continuous_rep_SUn n) (norm_trace_SUn_le n) (centreSUn n) (centreSUn_central n)
    (rep_centreSUn n) (omegaN_ne_one hn) hq x hμν R T hR hT

/-- **The area law for SU(3) lattice gauge theory** (the gauge group of the strong force) by the `Z_3` centre twist: for
    `q = 2 (d − 1) (1 − e^{−6|β|}) < 1`, `|⟨tr U_C⟩| ≤ 3 (q^{min(R, N−R)} / (1 − q))^T`. For `d = 4` the window is
    `|β| < log(6/5)/6 ≈ 0.0304`. -/
theorem wilson_area_law_twist_SU3 [NeZero N] {β : ℝ} (hq : twistQ d 3 β < 1)
    (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) (R T : ℕ) (hR : R < N) (hT : T ≤ N) :
    0 < ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 3 p U) ∂(productHaar (SUn 3) d N) ∧
    ‖(∫ U, wilsonLoopC 3 (rectPath x μ ν R T) U *
          ((∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 3 p U) : ℝ) : ℂ) ∂(productHaar (SUn 3) d N)) /
      ((∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 3 p U) ∂(productHaar (SUn 3) d N) : ℝ) : ℂ)‖ ≤
      3 * (twistQ d 3 β ^ (min R (N - R)) / (1 - twistQ d 3 β)) ^ T := by
  have h := wilson_area_law_twist_SUn (n := 3) (by norm_num) hq x hμν R T hR hT
  exact_mod_cast h

/-- **The area law for SU(2) lattice gauge theory** by the centre twist (`z = −I`): for `q = 2 (d − 1) (1 − e^{−4|β|}) < 1`,
    `|⟨tr U_C⟩| ≤ 2 (q^{min(R, N−R)} / (1 − q))^T`. For `d = 4` the window is `|β| < log(6/5)/4 ≈ 0.0456`. -/
theorem wilson_area_law_twist_SU2 [NeZero N] {β : ℝ} (hq : twistQ d 2 β < 1)
    (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) (R T : ℕ) (hR : R < N) (hT : T ≤ N) :
    0 < ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar (SUn 2) d N) ∧
    ‖(∫ U, wilsonLoopC 2 (rectPath x μ ν R T) U *
          ((∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) : ℝ) : ℂ) ∂(productHaar (SUn 2) d N)) /
      ((∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar (SUn 2) d N) : ℝ) : ℂ)‖ ≤
      2 * (twistQ d 2 β ^ (min R (N - R)) / (1 - twistQ d 2 β)) ^ T := by
  have h := wilson_area_law_twist_SUn (n := 2) (by norm_num) hq x hμν R T hR hT
  exact_mod_cast h

/-- **The area law for U(n) lattice gauge theory** (including U(1)) by the centre twist (`z = −I`, `ω = −1`): for
    `q = 2 (d − 1) (1 − e^{−2n|β|}) < 1`, `|⟨tr U_C⟩| ≤ n (q^{min(R, N−R)} / (1 − q))^T`. -/
theorem wilson_area_law_twist_Un [NeZero N] (n : ℕ) {β : ℝ} (hq : twistQ d n β < 1)
    (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) (R T : ℕ) (hR : R < N) (hT : T ≤ N) :
    0 < ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar (Un n) d N) ∧
    ‖(∫ U, wilsonLoopC n (rectPath x μ ν R T) U *
          ((∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) : ℝ) : ℂ) ∂(productHaar (Un n) d N)) /
      ((∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar (Un n) d N) : ℝ) : ℂ)‖ ≤
      n * (twistQ d n β ^ (min R (N - R)) / (1 - twistQ d n β)) ^ T := by
  have hz : ∀ g : Un n, Commute (negOneUn n) g :=
    fun g => Subtype.ext (show (-1 : Matrix (Fin n) (Fin n) ℂ) * g.val = g.val * -1 by simp)
  have hrep : HasGaugeTrace.rep (G := Un n) (n := n) (negOneUn n) = (-1 : ℂ) • 1 := by
    show (-1 : Matrix (Fin n) (Fin n) ℂ) = (-1 : ℂ) • 1
    simp
  exact wilson_area_law_twist (G := Un n) continuous_subtype_val (fun g => norm_trace_le_of_unitary g.2) (negOneUn n) hz
    hrep (by norm_num) hq x hμν R T hR hT

end AreaLaw.Twist
