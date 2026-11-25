/-
Centre symmetry and the parity selection rule for Wilson loops (area-law project, 2026-11-21).
Released under Apache 2.0.

# Centre symmetry: only closed surfaces mod 2 survive

Let `z` be a central element of the gauge group with `z * z = 1` that acts as `-1` in the gauge representation (for SU(2): `z = -1`).
Multiplying one link `ℓ` by `z` ("flipping" it) multiplies the holonomy of every path by `z` once per visit to `ℓ`, so Re Tr of a closed
path changes sign once per visit. The product Haar measure is unchanged by the flip (when the single-link Haar measure is invariant under
left multiplication by `z`). Hence an integrand that changes sign under the flip integrates to zero.

The selection rule (`integral_parity_eq_zero`): a Wilson loop `C`, multiplied by functions of a set `O` of plaquettes that are odd under
`x ↦ -x` and by any functions of the plaquettes that are even, integrates to zero against the product Haar measure unless, for every link,
the number of times `C` visits it plus the number of plaquettes of `O` that contain it is even, i.e. unless `O` and `C` together form a
closed surface mod 2. This is the step of the strong-coupling area law that forces the minimal spanning area.
-/

import AreaLaw.WilsonLoop

open MeasureTheory

noncomputable section

variable {G : Type*} [Group G] {d N : ℕ}

/-! ## Flipping one link -/

/-- Multiply the link `ℓ` by `z`. -/
def flipAt (z : G) (ℓ : LatticeLink d N) (U : GaugeConnection G d N) : GaugeConnection G d N :=
  Function.update U ℓ (z * U ℓ)

/-- How often a path visits the link `ℓ` (in either direction). -/
def visits (ℓ : LatticeLink d N) (p : List (PathStep d N)) : ℕ := p.countP (fun s => s.link = ℓ)

section Algebra

variable (z : G) (hz : ∀ g : G, Commute z g) (hzz : z * z = 1)
include hz hzz

theorem PathStep.hol_flipAt (ℓ : LatticeLink d N) (U : GaugeConnection G d N) (s : PathStep d N) :
    s.hol (flipAt z ℓ U) = z ^ (if s.link = ℓ then 1 else 0) * s.hol U := by
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  obtain ⟨l, f⟩ := s
  by_cases hl : l = ℓ
  · subst hl
    cases f
    · simp only [PathStep.hol, flipAt, Function.update_self, if_true, pow_one, Bool.false_eq_true, if_false]
      rw [mul_inv_rev, hzinv]
      exact ((hz (U l)⁻¹).eq).symm
    · simp [PathStep.hol, flipAt]
  · simp [PathStep.hol, flipAt, Function.update_of_ne hl, hl]

/-- **Flipping a link multiplies a path's holonomy by `z` once per visit.** -/
theorem pathHol_flipAt (ℓ : LatticeLink d N) (U : GaugeConnection G d N) :
    ∀ p : List (PathStep d N), pathHol (flipAt z ℓ U) p = z ^ visits ℓ p * pathHol U p
  | [] => by simp [pathHol, visits]
  | s :: rest => by
    have hc : Commute (z ^ visits ℓ rest) (s.hol U) := (hz _).pow_left _
    have hv : visits ℓ (s :: rest) = visits ℓ rest + (if s.link = ℓ then 1 else 0) := by
      simp [visits, List.countP_cons]
    rw [pathHol, PathStep.hol_flipAt z hz hzz, pathHol_flipAt ℓ U rest, pathHol, hv, pow_add]
    calc z ^ (if s.link = ℓ then 1 else 0) * s.hol U * (z ^ visits ℓ rest * pathHol U rest)
        = z ^ (if s.link = ℓ then 1 else 0) * (s.hol U * z ^ visits ℓ rest) * pathHol U rest := by
          simp only [mul_assoc]
      _ = z ^ (if s.link = ℓ then 1 else 0) * (z ^ visits ℓ rest * s.hol U) * pathHol U rest := by rw [hc.eq]
      _ = (z ^ (if s.link = ℓ then 1 else 0) * z ^ visits ℓ rest) * (s.hol U * pathHol U rest) := by
          simp only [mul_assoc]
      _ = (z ^ visits ℓ rest * z ^ (if s.link = ℓ then 1 else 0)) * (s.hol U * pathHol U rest) := by
          rw [pow_mul_comm]

end Algebra

section Trace

variable {n : ℕ} [HasGaugeTrace G n] (z : G) (hrep : HasGaugeTrace.rep (G := G) (n := n) z = -1)
include hrep

/-- In the gauge representation `z` acts as `-1`, so Re Tr picks up a sign per power of `z`. -/
theorem gaugeReTr_zpow_mul (k : ℕ) (g : G) : gaugeReTr G n (z ^ k * g) = (-1) ^ k * gaugeReTr G n g := by
  simp only [gaugeReTr, gaugeTrace, map_mul, map_pow, hrep]
  rw [neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;>
    simp [h, neg_one_pow_eq_pow_mod_two (R := ℝ) (n := k), Matrix.trace_neg]

end Trace

/-! ## The flip preserves the product Haar measure -/

section Measure

variable [MeasurableSpace G] [HasHaarProbability G] [Fintype (LatticeLink d N)]

theorem flipAt_eq_pi (z : G) (ℓ : LatticeLink d N) (U : GaugeConnection G d N) :
    flipAt z ℓ U = fun l => (if l = ℓ then (z * ·) else id) (U l) := by
  funext l; by_cases h : l = ℓ
  · subst h; simp [flipAt]
  · simp [flipAt, Function.update_of_ne h, h]

/-- **The flip preserves the product Haar measure**, if left multiplication by `z` preserves the single-link Haar measure. -/
theorem measurePreserving_flipAt (z : G) (hzm : MeasurePreserving (z * ·) (haarG G) (haarG G)) (ℓ : LatticeLink d N) :
    MeasurePreserving (flipAt (d := d) (N := N) z ℓ) (productHaar G d N) (productHaar G d N) := by
  have h : ∀ l : LatticeLink d N, MeasurePreserving (if l = ℓ then (z * ·) else id) (haarG G) (haarG G) := by
    intro l; split_ifs
    · exact hzm
    · exact MeasurePreserving.id _
  have hpi := measurePreserving_pi (fun _ : LatticeLink d N => haarG G) (fun _ => haarG G) h
  have hfun : (flipAt (d := d) (N := N) z ℓ) = fun U l => (if l = ℓ then (z * ·) else id) (U l) := by
    funext U; exact flipAt_eq_pi z ℓ U
  rw [hfun]; exact hpi

/-- **Odd integrands vanish.** If an integrand changes sign when one link is flipped, its integral is zero. -/
theorem integral_eq_zero_of_flip_odd (z : G) (hzz : z * z = 1) (hzm : MeasurePreserving (z * ·) (haarG G) (haarG G))
    (ℓ : LatticeLink d N) (F : GaugeConnection G d N → ℝ) (hF : ∀ U, F (flipAt z ℓ U) = -F U) :
    ∫ U, F U ∂(productHaar G d N) = 0 := by
  have hinv : Function.Involutive (flipAt (d := d) (N := N) z ℓ) := by
    intro U; funext l; by_cases h : l = ℓ
    · subst h; simp [flipAt, ← mul_assoc, hzz]
    · simp [flipAt, Function.update_of_ne h]
  have hmp := measurePreserving_flipAt z hzm ℓ
  let e : GaugeConnection G d N ≃ᵐ GaugeConnection G d N :=
    { toEquiv := hinv.toPerm _, measurable_toFun := hmp.measurable, measurable_invFun := hmp.measurable }
  have h1 : ∫ U, F (flipAt z ℓ U) ∂(productHaar G d N) = ∫ U, F U ∂(productHaar G d N) :=
    hmp.integral_comp' (f := e) F
  simp only [hF, integral_neg] at h1
  linarith

/-! ## The parity selection rule -/

variable {n : ℕ} [HasGaugeTrace G n]

/-- How many plaquettes of `O` contain the link `ℓ` (counted along their boundaries). -/
def plaqVisits (ℓ : LatticeLink d N) (O : Finset (LatticePlaquette d N)) : ℕ :=
  ∑ p ∈ O, visits ℓ (plaquettePath p)

/-- **The selection rule.** A Wilson loop times odd functions of the plaquettes in `O` times even functions of all plaquettes in `P`
    integrates to zero unless every link is visited an even number of times by the loop and the boundaries of `O` together: only closed
    surfaces mod 2 survive. -/
theorem integral_parity_eq_zero (z : G) (hz : ∀ g : G, Commute z g) (hzz : z * z = 1)
    (hrep : HasGaugeTrace.rep (G := G) (n := n) z = -1) (hzm : MeasurePreserving (z * ·) (haarG G) (haarG G))
    (C : List (PathStep d N)) (O P : Finset (LatticePlaquette d N)) (t w : ℝ → ℝ)
    (ht : ∀ x, t (-x) = -t x) (hw : ∀ x, w (-x) = w x)
    (ℓ : LatticeLink d N) (hodd : Odd (visits ℓ C + plaqVisits ℓ O)) :
    ∫ U, wilsonLoop n C U * (∏ p ∈ O, t (gaugeReTr G n (plaquetteHolonomy U p))) *
      (∏ p ∈ P, w (gaugeReTr G n (plaquetteHolonomy U p))) ∂(productHaar G d N) = 0 := by
  apply integral_eq_zero_of_flip_odd z hzz hzm ℓ
  intro U
  -- every plaquette picks up the sign (-1)^(visits), the loop too
  have hplaq : ∀ p, gaugeReTr G n (plaquetteHolonomy (flipAt z ℓ U) p) =
      (-1) ^ visits ℓ (plaquettePath p) * gaugeReTr G n (plaquetteHolonomy U p) := by
    intro p
    rw [← plaquettePath_hol, pathHol_flipAt z hz hzz, gaugeReTr_zpow_mul z hrep, plaquettePath_hol]
  have hodd_t : ∀ (k : ℕ) (x : ℝ), t ((-1) ^ k * x) = (-1) ^ k * t x := by
    intro k x; rcases Nat.even_or_odd k with he | ho
    · simp [he.neg_one_pow]
    · simp [ho.neg_one_pow, ht]
  have heven_w : ∀ (k : ℕ) (x : ℝ), w ((-1) ^ k * x) = w x := by
    intro k x; rcases Nat.even_or_odd k with he | ho
    · simp [he.neg_one_pow]
    · simp [ho.neg_one_pow, hw]
  simp only [wilsonLoop, pathHol_flipAt z hz hzz, gaugeReTr_zpow_mul z hrep, hplaq, hodd_t, heven_w]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have : (-1 : ℝ) ^ visits ℓ C * (-1) ^ plaqVisits ℓ O = -1 := by
    rw [← pow_add]; exact hodd.neg_one_pow
  simp only [plaqVisits] at this
  linear_combination (gaugeReTr G n (pathHol U C) * (∏ p ∈ O, t (gaugeReTr G n (plaquetteHolonomy U p))) *
    ∏ p ∈ P, w (gaugeReTr G n (plaquetteHolonomy U p))) * this

end Measure

end
