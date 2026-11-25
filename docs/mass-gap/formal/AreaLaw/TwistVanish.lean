/-
The centre twist and the vanishing of twisted terms (area-law project, 2026-11-21). Released under Apache 2.0.

Idea of the centre-twist area law as in B. G. Srivats, fisher-lorentz-formalization (`Confinement/AreaLaw.lean`, README "The proof")
and Osterwalder–Seiler 1978; written independently here, in this project's framework (`AreaLaw.Lattice`, `WilsonLoop`, `productHaar`).

# The twist

Let `z` be a central element of the gauge group with `rep z = ω · I`, `ω ≠ 1`. Multiplying the links of a set `S` by `z`
(`twistAt z S`) multiplies the holonomy of a path by `z^k`, `k` the signed number of its steps through `S` (`tcount`, forward `+1`,
backward `−1`): `pathHol_twistAt`. It preserves the product Haar measure (left invariance), changes a plaquette holonomy only when
`tcount S (plaquettePath p) ≠ 0`, and multiplies the complex Wilson loop `tr rep(U_C)` by `ω` when `tcount S C = 1`.

`twist_term_vanish`: if every plaquette of `A` has twist count `0` and the loop has twist count `1`, then
`∫ tr rep(U_C) · ∏_{p ∈ A} F_p(U_p) = 0` for any functions `F_p` of the plaquette holonomies.
-/

import AreaLaw.Clustering

open Finset MeasureTheory

noncomputable section

namespace AreaLaw.Twist

variable {G : Type*} [Group G] {d N : ℕ}

/-! ## Twisting a set of links -/

/-- Multiply every link of `S` by `z`. -/
def twistAt (z : G) (S : Finset (LatticeLink d N)) (U : GaugeConnection G d N) : GaugeConnection G d N :=
  fun l => if l ∈ S then z * U l else U l

/-- The signed passage of one step through `S`: `+1` forward, `−1` backward, `0` if its link is not in `S`. -/
def stepCount (S : Finset (LatticeLink d N)) (s : PathStep d N) : ℤ :=
  if s.link ∈ S then (if s.fwd then 1 else -1) else 0

/-- The signed number of passages of a path through `S`. -/
def tcount (S : Finset (LatticeLink d N)) : List (PathStep d N) → ℤ
  | [] => 0
  | s :: rest => stepCount S s + tcount S rest

theorem tcount_nil (S : Finset (LatticeLink d N)) : tcount S [] = 0 := rfl

theorem tcount_cons (S : Finset (LatticeLink d N)) (s : PathStep d N) (rest : List (PathStep d N)) :
    tcount S (s :: rest) = stepCount S s + tcount S rest := rfl

theorem tcount_append (S : Finset (LatticeLink d N)) (p q : List (PathStep d N)) :
    tcount S (p ++ q) = tcount S p + tcount S q := by
  induction p with
  | nil => simp [tcount]
  | cons s rest ih => simp [tcount, ih, add_assoc]

/-- A path none of whose links lies in `S` has twist count `0`. -/
theorem tcount_eq_zero_of_forall (S : Finset (LatticeLink d N)) :
    ∀ p : List (PathStep d N), (∀ s ∈ p, s.link ∉ S) → tcount S p = 0
  | [], _ => rfl
  | s :: rest, h => by
    rw [tcount_cons, tcount_eq_zero_of_forall S rest (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    simp [stepCount, h s List.mem_cons_self]

section Algebra

variable (z : G) (hz : ∀ g : G, Commute z g)
include hz

theorem hol_twistAt (S : Finset (LatticeLink d N)) (U : GaugeConnection G d N) (s : PathStep d N) :
    s.hol (twistAt z S U) = z ^ stepCount S s * s.hol U := by
  obtain ⟨l, f⟩ := s
  by_cases hl : l ∈ S
  · cases f
    · simp only [PathStep.hol, twistAt, hl, ite_true, stepCount, Bool.false_eq_true, ite_false, zpow_neg, zpow_one]
      rw [mul_inv_rev]
      exact ((hz (U l)).inv_inv).eq.symm
    · simp [PathStep.hol, twistAt, hl, stepCount]
  · simp [PathStep.hol, twistAt, hl, stepCount]

/-- **The twist multiplies a path's holonomy by `z` to the power of its signed passages through `S`.** -/
theorem pathHol_twistAt (S : Finset (LatticeLink d N)) (U : GaugeConnection G d N) :
    ∀ p : List (PathStep d N), pathHol (twistAt z S U) p = z ^ tcount S p * pathHol U p
  | [] => by simp [pathHol, tcount]
  | s :: rest => by
    rw [pathHol, hol_twistAt z hz, pathHol_twistAt S U rest, pathHol, tcount_cons, zpow_add]
    have hc : Commute (z ^ tcount S rest) (s.hol U) := (hz _).zpow_left _
    calc z ^ stepCount S s * s.hol U * (z ^ tcount S rest * pathHol U rest)
        = z ^ stepCount S s * (s.hol U * z ^ tcount S rest) * pathHol U rest := by simp only [mul_assoc]
      _ = z ^ stepCount S s * (z ^ tcount S rest * s.hol U) * pathHol U rest := by rw [hc.eq]
      _ = z ^ stepCount S s * z ^ tcount S rest * (s.hol U * pathHol U rest) := by simp only [mul_assoc]

theorem plaquetteHolonomy_twistAt (S : Finset (LatticeLink d N)) (U : GaugeConnection G d N) (p : LatticePlaquette d N) :
    plaquetteHolonomy (twistAt z S U) p = z ^ tcount S (plaquettePath p) * plaquetteHolonomy U p := by
  rw [← plaquettePath_hol, pathHol_twistAt z hz, plaquettePath_hol]

/-- A plaquette with twist count `0` does not see the twist. -/
theorem plaquetteHolonomy_twistAt_of_zero (S : Finset (LatticeLink d N)) (U : GaugeConnection G d N)
    {p : LatticePlaquette d N} (hp : tcount S (plaquettePath p) = 0) :
    plaquetteHolonomy (twistAt z S U) p = plaquetteHolonomy U p := by
  rw [plaquetteHolonomy_twistAt z hz, hp, zpow_zero, one_mul]

end Algebra

theorem twistAt_inv (z : G) (S : Finset (LatticeLink d N)) (U : GaugeConnection G d N) :
    twistAt z⁻¹ S (twistAt z S U) = U := by
  funext l; by_cases hl : l ∈ S <;> simp [twistAt, hl]

theorem twistAt_inv' (z : G) (S : Finset (LatticeLink d N)) (U : GaugeConnection G d N) :
    twistAt z S (twistAt z⁻¹ S U) = U := by
  funext l; by_cases hl : l ∈ S <;> simp [twistAt, hl]

/-! ## The complex Wilson loop -/

variable {n : ℕ} [HasGaugeTrace G n]

/-- The complex Wilson loop `tr rep(U_C)`. Its real part is `wilsonLoop`. -/
def wilsonLoopC (n : ℕ) [HasGaugeTrace G n] (C : List (PathStep d N)) (U : GaugeConnection G d N) : ℂ :=
  gaugeTrace G n (pathHol U C)

theorem re_wilsonLoopC (C : List (PathStep d N)) (U : GaugeConnection G d N) :
    (wilsonLoopC n C U).re = wilsonLoop n C U := rfl

theorem gaugeTrace_central_mul {z : G} {ω : ℂ} (hrep : HasGaugeTrace.rep (G := G) (n := n) z = ω • 1) (g : G) :
    gaugeTrace G n (z * g) = ω * gaugeTrace G n g := by
  simp [gaugeTrace, map_mul, hrep, Matrix.trace_smul]

/-! ## The twist preserves the product Haar measure -/

section Measure

variable [MeasurableSpace G] [HasHaarProbability G] [Fintype (LatticeLink d N)]

theorem measurePreserving_twistAt (z : G) (hzm : MeasurePreserving (z * ·) (haarG G) (haarG G))
    (S : Finset (LatticeLink d N)) :
    MeasurePreserving (twistAt (d := d) (N := N) z S) (productHaar G d N) (productHaar G d N) := by
  have h : ∀ l : LatticeLink d N, MeasurePreserving (if l ∈ S then (z * ·) else id) (haarG G) (haarG G) := by
    intro l; split_ifs
    · exact hzm
    · exact MeasurePreserving.id _
  have hpi := measurePreserving_pi (fun _ : LatticeLink d N => haarG G) (fun _ => haarG G) h
  have hfun : (twistAt (d := d) (N := N) z S) = fun U l => (if l ∈ S then (z * ·) else id) (U l) := by
    funext U l; by_cases hl : l ∈ S <;> simp [twistAt, hl]
  rw [hfun]; exact hpi

/-- **The twist lemma (MG3, formal version).** Let `z` be central with `rep z = ω I`, `ω ≠ 1`, and left multiplication by `z^{±1}`
    preserve the link measure. If the loop `C` passes the twisted links `S` once (signed count `1`) while every plaquette of `A`
    passes them a net zero times, then `∫ tr rep(U_C) · ∏_{p ∈ A} F_p(U_p) = 0`. This is the formal version of the project's
    finding MG3: the twist is invisible to every local (plaquette) check and visible only around the large loop. -/
theorem twist_term_vanish (z : G) (hz : ∀ g : G, Commute z g) {ω : ℂ}
    (hrep : HasGaugeTrace.rep (G := G) (n := n) z = ω • 1) (hω : ω ≠ 1)
    (hzm : MeasurePreserving (z * ·) (haarG G) (haarG G)) (hzm' : MeasurePreserving (z⁻¹ * ·) (haarG G) (haarG G))
    (S : Finset (LatticeLink d N)) (C : List (PathStep d N)) (hC : tcount S C = 1)
    (A : Finset (LatticePlaquette d N)) (hA : ∀ p ∈ A, tcount S (plaquettePath p) = 0)
    (F : LatticePlaquette d N → G → ℂ) :
    ∫ U, wilsonLoopC n C U * ∏ p ∈ A, F p (plaquetteHolonomy U p) ∂(productHaar G d N) = 0 := by
  set Φ : GaugeConnection G d N → ℂ := fun U => wilsonLoopC n C U * ∏ p ∈ A, F p (plaquetteHolonomy U p) with hΦ
  have hmp := measurePreserving_twistAt z hzm S
  have hmp' := measurePreserving_twistAt z⁻¹ hzm' S
  let e : GaugeConnection G d N ≃ᵐ GaugeConnection G d N :=
    { toFun := twistAt z S
      invFun := twistAt z⁻¹ S
      left_inv := twistAt_inv z S
      right_inv := twistAt_inv' z S
      measurable_toFun := hmp.measurable
      measurable_invFun := hmp'.measurable }
  have h1 : ∫ U, Φ (twistAt z S U) ∂(productHaar G d N) = ∫ U, Φ U ∂(productHaar G d N) :=
    hmp.integral_comp' (f := e) Φ
  have h2 : ∀ U, Φ (twistAt z S U) = ω * Φ U := by
    intro U
    simp only [hΦ, wilsonLoopC]
    rw [pathHol_twistAt z hz, hC, zpow_one, gaugeTrace_central_mul hrep]
    rw [prod_congr rfl fun p hp => by rw [plaquetteHolonomy_twistAt_of_zero z hz S U (hA p hp)]]
    ring
  simp_rw [h2] at h1
  rw [integral_const_mul] at h1
  have h3 : (ω - 1) * ∫ U, Φ U ∂(productHaar G d N) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hω)

end Measure

end AreaLaw.Twist
