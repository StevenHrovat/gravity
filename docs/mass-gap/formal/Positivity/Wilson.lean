/-
Reflection positivity of the Wilson lattice gauge measure, site reflection (positivity project, 2026-11-21). Released under
Apache 2.0.

Osterwalder and Seiler proved reflection positivity of the Wilson action in 1978 (Ann. Phys. 110, 440); this file is an
independent formalisation of the site-reflection case on the periodic lattice.

# The Wilson measure is reflection positive (site reflection)

Lattice (ℤ/Nℤ)^d, `N` even, direction `0` is time, reflection `t ↦ −t` fixing the slices `t = 0` and `t = N/2`
(`Positivity.Reflection`). The Wilson weight is `e^{−S(U)} = ∏_p exp(β Re tr U_p)` (any real `β`).

1. The plaquettes split into positive, fixed and negative ones; the negative ones are the mirrors of the positive ones, and
   `Re tr U_{mirror q}(U) = Re tr U_q(Θ U)`. Hence `e^{−S(U)} = A(U) · A(Θ U) · B(U)` with
   `A = ∏_{positive p} exp(β Re tr U_p)` (a function of the closed positive half) and
   `B = ∏_{fixed p} exp(β Re tr U_p)` (a function of the fixed slices) (`wilson_weight_factor`).
2. By `Positivity.Product`, for every bounded measurable `F` depending only on the links of the closed positive half
   `0 ≤ t ≤ N/2`: `∫ F · (F ∘ Θ) · e^{−S} d(productHaar) ≥ 0` (`wilson_rp`), also normalised (`wilson_rp_normalized`),
   the form is symmetric (`wilson_rp_symm`), satisfies Cauchy–Schwarz (`wilson_rp_cs`), and its Gram matrices are positive
   semi-definite (`wilson_rp_gram`).

Hypotheses on the gauge group: a topological group with Borel structure (second countable), a continuous unitary matrix
representation, and a single-link probability measure that is invariant under inversion (Haar measure on a compact group,
`Positivity.Concrete`). Left invariance is not needed for positivity.
-/

import Positivity.Reflection

open MeasureTheory Finset
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Positivity

open AreaLaw.Concrete

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] {n : ℕ} [HasGaugeTrace G n]

/-- The weight of the positive plaquettes. -/
def posWeight (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (U : GaugeConnection G d N) : ℝ :=
  ∏ p ∈ (univ : Finset (LatticePlaquette d N)).filter IsPosPlaq, Real.exp (β * xp n p U)

/-- The weight of the plaquettes in the fixed slices. -/
def fixWeight (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (U : GaugeConnection G d N) : ℝ :=
  ∏ p ∈ (univ : Finset (LatticePlaquette d N)).filter IsFixedPlaq, Real.exp (β * xp n p U)

/-- **The factorisation of the Wilson weight**: `e^{−S(U)} = A(U) · A(Θ U) · B(U)`. -/
theorem wilson_weight_factor (hN : Even N) (hinv : ∀ g : G, gaugeReTr G n g⁻¹ = gaugeReTr G n g) (β : ℝ)
    (U : GaugeConnection G d N) :
    ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) =
      posWeight n β U * posWeight n β (thetaConn U) * fixWeight n β U := by
  rw [← prod_filter_mul_prod_filter_not univ IsPosPlaq,
    ← prod_filter_mul_prod_filter_not ((univ : Finset (LatticePlaquette d N)).filter (fun p => ¬IsPosPlaq p))
      IsFixedPlaq]
  have hfix : ((univ : Finset (LatticePlaquette d N)).filter (fun p => ¬IsPosPlaq p)).filter IsFixedPlaq =
      univ.filter IsFixedPlaq := by
    ext p
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    intro hf hp
    exact not_fixedPlaq_of_pos hp hf
  have hneg : ∏ p ∈ ((univ : Finset (LatticePlaquette d N)).filter (fun p => ¬IsPosPlaq p)).filter
      (fun p => ¬IsFixedPlaq p), Real.exp (β * xp n p U) = posWeight n β (thetaConn U) := by
    unfold posWeight
    simp_rw [xp_thetaConn hinv]
    symm
    refine prod_nbij' mirrorPlaq mirrorPlaq (fun q hq => ?_) (fun p hp => ?_) (fun q _ => mirrorPlaq_involutive q)
      (fun p _ => mirrorPlaq_involutive p) (fun q _ => rfl)
    · simp only [mem_filter, mem_univ, true_and] at hq ⊢
      exact ⟨(plaq_pos_mirror hN hq).2, (plaq_pos_mirror hN hq).1⟩
    · simp only [mem_filter, mem_univ, true_and] at hp ⊢
      exact plaq_neg_mirror hN hp.2 hp.1
  rw [hfix, hneg]
  unfold posWeight fixWeight
  ring

theorem posWeight_depPos (hN : Even N) (β : ℝ) : DepPos (linkSplit hN) (posWeight (G := G) (d := d) (N := N) n β) := by
  apply depPos_of_linkDep hN
  intro U V h
  unfold posWeight
  refine prod_congr rfl fun p hp => ?_
  simp only [mem_filter, mem_univ, true_and] at hp
  have hl : ∀ i, U (p.boundaryLinks i) = V (p.boundaryLinks i) := fun i =>
    h _ (by simp only [posHalfLinks, mem_filter, mem_univ, true_and]; exact plaq_pos_links hN hp i)
  simp only [xp, plaquetteHolonomy, hl]

theorem fixWeight_depFix (hN : Even N) (β : ℝ) : DepFix (linkSplit hN) (fixWeight (G := G) (d := d) (N := N) n β) := by
  intro U V h
  unfold fixWeight
  refine prod_congr rfl fun p hp => ?_
  simp only [mem_filter, mem_univ, true_and] at hp
  have hl : ∀ i, U (p.boundaryLinks i) = V (p.boundaryLinks i) := fun i => h ⟨_, plaq_fixed_links hp i⟩
  simp only [xp, plaquetteHolonomy, hl]

section Measure

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem measurable_expxp (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ) (p : LatticePlaquette d N) :
    Measurable (fun U : GaugeConnection G d N => Real.exp (β * xp n p U)) :=
  Real.measurable_exp.comp ((measurable_xp hc p).const_mul β)

theorem isBdd_expxp (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ) (β : ℝ)
    (p : LatticePlaquette d N) : IsBdd (fun U : GaugeConnection G d N => Real.exp (β * xp n p U)) := by
  refine ⟨Real.exp (|β| * n), fun U => ?_⟩
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.mpr ?_
  have hx : |xp n p U| ≤ n := abs_re_trace_le_of_unitary (hU _)
  calc β * xp n p U ≤ |β * xp n p U| := le_abs_self _
    _ = |β| * |xp n p U| := abs_mul _ _
    _ ≤ |β| * n := mul_le_mul_of_nonneg_left hx (abs_nonneg _)

theorem measurable_wilsonWeight (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (β : ℝ)
    (s : Finset (LatticePlaquette d N)) :
    Measurable (fun U : GaugeConnection G d N => ∏ p ∈ s, Real.exp (β * xp n p U)) :=
  Finset.measurable_prod s (fun p _ => measurable_expxp hc β p)

theorem isBdd_wilsonWeight (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (β : ℝ) (s : Finset (LatticePlaquette d N)) :
    IsBdd (fun U : GaugeConnection G d N => ∏ p ∈ s, Real.exp (β * xp n p U)) :=
  IsBdd.prod s (fun p => isBdd_expxp hU β p)

variable [HasHaarProbability G] [(haarG G).IsInvInvariant]

theorem linkTwist_measurePreserving (l : LatticeLink d N) :
    MeasurePreserving (linkTwist (G := G) l) (haarG G) (haarG G) := by
  unfold linkTwist
  split_ifs
  · exact Measure.measurePreserving_inv _
  · exact MeasurePreserving.id _

theorem measurable_thetaConn : Measurable (thetaConn (G := G) (d := d) (N := N)) :=
  measurePreserving_thetaConn.measurable

variable (hN : Even N) (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
include hN hc hU

/-- Rewriting the reflected integrand through the factorisation of the weight. -/
theorem wilson_integrand_eq (β : ℝ) (F F' : GaugeConnection G d N → ℝ) (U : GaugeConnection G d N) :
    F U * F' (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) =
      (F U * posWeight n β U) * (F' (thetaConn U) * posWeight n β (thetaConn U)) * fixWeight n β U := by
  rw [wilson_weight_factor hN (gaugeReTr_inv_of_unitary hU) β U]; ring

/-- Reflection positivity, with the boundedness hypothesis as `IsBdd`. -/
theorem wilson_rp_of_isBdd (β : ℝ) {F : GaugeConnection G d N → ℝ} (hF : LinkDep F (posHalfLinks d N))
    (mF : Measurable F) (bF : IsBdd F) :
    0 ≤ ∫ U, F U * F (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
      ∂(productHaar G d N) := by
  simp_rw [wilson_integrand_eq hN hc hU β F F]
  have : Nonempty G := ⟨1⟩
  exact config_rp (haarG G) (fun x => linkTwist_measurePreserving x.1) (isReflection_thetaConn hN)
    ((depPos_of_linkDep hN hF).mul (posWeight_depPos hN β)) (fixWeight_depFix hN β)
    (mF.mul (measurable_wilsonWeight hc β _)) (measurable_wilsonWeight hc β _)
    (bF.mul (isBdd_wilsonWeight hU β _)) (isBdd_wilsonWeight hU β _)
    (fun U => prod_nonneg fun p _ => (Real.exp_pos _).le)

/-- **Reflection positivity of the Wilson measure (site reflection).** For every bounded measurable `F` depending only on
    the links of the closed positive half `0 ≤ t ≤ N/2` (the fixed slices included) and every real `β`:
    `∫ F · (F ∘ Θ) · ∏_p exp(β Re tr U_p) d(productHaar) ≥ 0`. -/
theorem wilson_rp (β : ℝ) {F : GaugeConnection G d N → ℝ} (hF : LinkDep F (posHalfLinks d N))
    (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
      ∂(productHaar G d N) :=
  wilson_rp_of_isBdd hN hc hU β hF mF (IsBdd.of_abs bF)

/-- **Reflection positivity, normalised:** `⟨F · (F ∘ Θ)⟩_β ≥ 0` for the Wilson expectation. -/
theorem wilson_rp_normalized (β : ℝ) {F : GaugeConnection G d N → ℝ} (hF : LinkDep F (posHalfLinks d N))
    (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ (∫ U, F U * F (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
          ∂(productHaar G d N)) /
      ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N) :=
  div_nonneg (wilson_rp hN hc hU β hF mF bF)
    (integral_nonneg fun U => prod_nonneg fun p _ => (Real.exp_pos _).le)

/-- **Symmetry of the reflected form.** -/
theorem wilson_rp_symm (β : ℝ) {F F' : GaugeConnection G d N → ℝ} (hF : LinkDep F (posHalfLinks d N))
    (hF' : LinkDep F' (posHalfLinks d N)) (mF : Measurable F) (mF' : Measurable F') (bF : IsBdd F)
    (bF' : IsBdd F') :
    ∫ U, F U * F' (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
        ∂(productHaar G d N) =
      ∫ U, F' U * F (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
        ∂(productHaar G d N) := by
  simp_rw [wilson_integrand_eq hN hc hU β]
  have : Nonempty G := ⟨1⟩
  exact config_symm (haarG G) (fun x => linkTwist_measurePreserving x.1) (isReflection_thetaConn hN)
    ((depPos_of_linkDep hN hF).mul (posWeight_depPos hN β)) ((depPos_of_linkDep hN hF').mul (posWeight_depPos hN β))
    (fixWeight_depFix hN β) (mF.mul (measurable_wilsonWeight hc β _)) (mF'.mul (measurable_wilsonWeight hc β _))
    (measurable_wilsonWeight hc β _) (bF.mul (isBdd_wilsonWeight hU β _)) (bF'.mul (isBdd_wilsonWeight hU β _))
    (isBdd_wilsonWeight hU β _)

/-- The admissible observables: bounded measurable functions of the closed positive half. -/
def PosObs (d N : ℕ) [NeZero d] [NeZero N] (G : Type*) [Group G] [MeasurableSpace G]
    (F : GaugeConnection G d N → ℝ) : Prop :=
  LinkDep F (posHalfLinks d N) ∧ Measurable F ∧ IsBdd F

omit hN hc hU in
theorem posObs_zero : PosObs d N G 0 :=
  ⟨fun _ _ _ => rfl, measurable_const, IsBdd.const 0⟩

omit hN hc hU in
theorem posObs_add {F F' : GaugeConnection G d N → ℝ} (hF : PosObs d N G F) (hF' : PosObs d N G F') :
    PosObs d N G (F + F') :=
  ⟨fun U V h => by simp only [Pi.add_apply, hF.1 U V h, hF'.1 U V h], hF.2.1.add hF'.2.1, hF.2.2.add hF'.2.2⟩

omit hN hc hU in
theorem posObs_smul (t : ℝ) {F : GaugeConnection G d N → ℝ} (hF : PosObs d N G F) : PosObs d N G (t • F) :=
  ⟨fun U V h => by simp only [Pi.smul_apply, hF.1 U V h], hF.2.1.const_smul t, hF.2.2.const_mul t⟩

theorem posObs_integrable (β : ℝ) {F F' : GaugeConnection G d N → ℝ} (hF : PosObs d N G F)
    (hF' : PosObs d N G F') :
    Integrable (fun U => F U * F' (thetaConn U) *
      ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)) (productHaar G d N) :=
  IsBdd.integrable ((hF.2.2.mul (hF'.2.2.comp thetaConn)).mul (isBdd_wilsonWeight hU β _))
    ((hF.2.1.mul (hF'.2.1.comp measurable_thetaConn)).mul (measurable_wilsonWeight hc β _)).aestronglyMeasurable

/-- **Gram positivity.** For bounded measurable `F₁, …, F_k` of the closed positive half, the matrix
    `[∫ Fᵢ · (Fⱼ ∘ Θ) · e^{−S}]` is positive semi-definite. -/
theorem wilson_rp_gram (β : ℝ) {ι : Type*} (s : Finset ι) (Fs : ι → GaugeConnection G d N → ℝ)
    (hFs : ∀ i ∈ s, LinkDep (Fs i) (posHalfLinks d N) ∧ Measurable (Fs i) ∧ ∃ M, ∀ U, |Fs i U| ≤ M) (z : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, z i * z j *
      ∫ U, Fs i U * Fs j (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
        ∂(productHaar G d N) :=
  gram_of_rp thetaConn _ (PosObs d N G) posObs_zero (fun _ _ => posObs_add) (fun t _ => posObs_smul t)
    (fun _ _ hF hF' => posObs_integrable hN hc hU β hF hF')
    (fun _ hF => wilson_rp_of_isBdd hN hc hU β hF.1 hF.2.1 hF.2.2) s Fs
    (fun i hi => ⟨(hFs i hi).1, (hFs i hi).2.1, IsBdd.of_abs (hFs i hi).2.2⟩) z

/-- **Cauchy–Schwarz for the reflected form:**
    `|∫ F · (F' ∘ Θ) e^{−S}|² ≤ (∫ F · (F ∘ Θ) e^{−S}) (∫ F' · (F' ∘ Θ) e^{−S})`. -/
theorem wilson_rp_cs (β : ℝ) {F F' : GaugeConnection G d N → ℝ} (hF : LinkDep F (posHalfLinks d N))
    (hF' : LinkDep F' (posHalfLinks d N)) (mF : Measurable F) (mF' : Measurable F') (bF : ∃ M, ∀ U, |F U| ≤ M)
    (bF' : ∃ M, ∀ U, |F' U| ≤ M) :
    |∫ U, F U * F' (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
        ∂(productHaar G d N)| ^ 2 ≤
      (∫ U, F U * F (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
        ∂(productHaar G d N)) *
      ∫ U, F' U * F' (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
        ∂(productHaar G d N) :=
  cs_of_rp thetaConn _ (PosObs d N G) posObs_zero (fun _ _ => posObs_add) (fun t _ => posObs_smul t)
    (fun _ _ hF hF' => posObs_integrable hN hc hU β hF hF')
    (fun _ hF => wilson_rp_of_isBdd hN hc hU β hF.1 hF.2.1 hF.2.2)
    (fun _ _ hF hF' => wilson_rp_symm hN hc hU β hF.1 hF'.1 hF.2.1 hF'.2.1 hF.2.2 hF'.2.2)
    ⟨hF, mF, IsBdd.of_abs bF⟩ ⟨hF', mF', IsBdd.of_abs bF'⟩

end Measure

end Positivity
