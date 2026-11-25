/-
Reflection positivity for every plaquette weight that is a function of `Re tr U_p` (positivity project, 2026-11-21).
Released under Apache 2.0.

# Site reflection for a general plaquette weight

The proof of `wilson_rp` (`Positivity.Wilson`) uses only that the weight factors over plaquettes, that each plaquette lies in
one closed half, and that mirrored plaquettes have the same `Re tr`. So the same proof works for the weight
`∏_p φ(Re tr U_p)` for any measurable `φ ≥ 0`. We only need `φ` to be bounded on `[-n, n]`, the range of `Re tr` of a
unitary `n × n` matrix, so `φ = exp (β ·)` is covered (`wilson_rp_of_general`, the old theorem as a corollary).

* `rp_plaquette_weight`: `∫ F · (F ∘ Θ) · ∏_p φ(xp p U) d(productHaar) ≥ 0`.
* `rp_plaquette_weight_gram`: the Gram matrices of the reflected form are positive semi-definite.
-/

import Positivity.Wilson
import Positivity.LinkWilson

open MeasureTheory Finset
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Positivity

open AreaLaw.Concrete

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] {n : ℕ} [HasGaugeTrace G n]

/-- The weight of the positive plaquettes, plaquette weight `φ`. -/
def posWeightφ (n : ℕ) [HasGaugeTrace G n] (φ : ℝ → ℝ) (U : GaugeConnection G d N) : ℝ :=
  ∏ p ∈ (univ : Finset (LatticePlaquette d N)).filter IsPosPlaq, φ (xp n p U)

/-- The weight of the plaquettes in the fixed slices, plaquette weight `φ`. -/
def fixWeightφ (n : ℕ) [HasGaugeTrace G n] (φ : ℝ → ℝ) (U : GaugeConnection G d N) : ℝ :=
  ∏ p ∈ (univ : Finset (LatticePlaquette d N)).filter IsFixedPlaq, φ (xp n p U)

/-- **Factorisation of any plaquette weight**: `∏_p φ(Re tr U_p) = A(U) · A(Θ U) · B(U)`. -/
theorem plaquette_weight_factor (hN : Even N) (hinv : ∀ g : G, gaugeReTr G n g⁻¹ = gaugeReTr G n g) (φ : ℝ → ℝ)
    (U : GaugeConnection G d N) :
    ∏ p ∈ (univ : Finset (LatticePlaquette d N)), φ (xp n p U) =
      posWeightφ n φ U * posWeightφ n φ (thetaConn U) * fixWeightφ n φ U := by
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
      (fun p => ¬IsFixedPlaq p), φ (xp n p U) = posWeightφ n φ (thetaConn U) := by
    unfold posWeightφ
    simp_rw [xp_thetaConn hinv]
    symm
    refine prod_nbij' mirrorPlaq mirrorPlaq (fun q hq => ?_) (fun p hp => ?_) (fun q _ => mirrorPlaq_involutive q)
      (fun p _ => mirrorPlaq_involutive p) (fun q _ => rfl)
    · simp only [mem_filter, mem_univ, true_and] at hq ⊢
      exact ⟨(plaq_pos_mirror hN hq).2, (plaq_pos_mirror hN hq).1⟩
    · simp only [mem_filter, mem_univ, true_and] at hp ⊢
      exact plaq_neg_mirror hN hp.2 hp.1
  rw [hfix, hneg]
  unfold posWeightφ fixWeightφ
  ring

theorem posWeightφ_depPos (hN : Even N) (φ : ℝ → ℝ) :
    DepPos (linkSplit hN) (posWeightφ (G := G) (d := d) (N := N) n φ) := by
  apply depPos_of_linkDep hN
  intro U V h
  unfold posWeightφ
  refine prod_congr rfl fun p hp => ?_
  simp only [mem_filter, mem_univ, true_and] at hp
  have hl : ∀ i, U (p.boundaryLinks i) = V (p.boundaryLinks i) := fun i =>
    h _ (by simp only [posHalfLinks, mem_filter, mem_univ, true_and]; exact plaq_pos_links hN hp i)
  simp only [xp, plaquetteHolonomy, hl]

theorem fixWeightφ_depFix (hN : Even N) (φ : ℝ → ℝ) :
    DepFix (linkSplit hN) (fixWeightφ (G := G) (d := d) (N := N) n φ) := by
  intro U V h
  unfold fixWeightφ
  refine prod_congr rfl fun p hp => ?_
  simp only [mem_filter, mem_univ, true_and] at hp
  have hl : ∀ i, U (p.boundaryLinks i) = V (p.boundaryLinks i) := fun i => h ⟨_, plaq_fixed_links hp i⟩
  simp only [xp, plaquetteHolonomy, hl]

/-- The hypothesis on a plaquette weight: measurable, and nonnegative and bounded on `[-n, n]`. -/
structure PlaqWeight (n : ℕ) (φ : ℝ → ℝ) : Prop where
  meas : Measurable φ
  nonneg : ∀ x : ℝ, |x| ≤ n → 0 ≤ φ x
  bdd : ∃ M : ℝ, ∀ x : ℝ, |x| ≤ n → |φ x| ≤ M

section Measure

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

section Bounds

variable (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
include hU

theorem xp_abs_le (p : LatticePlaquette d N) (U : GaugeConnection G d N) : |xp n p U| ≤ n :=
  abs_re_trace_le_of_unitary (hU _)

theorem isBdd_phi_xp {φ : ℝ → ℝ} (hφ : PlaqWeight n φ) (p : LatticePlaquette d N) :
    IsBdd (fun U : GaugeConnection G d N => φ (xp n p U)) := by
  obtain ⟨M, hM⟩ := hφ.bdd
  exact ⟨M, fun U => by
    rw [Real.norm_eq_abs]; exact hM _ (xp_abs_le hU p U)⟩

theorem isBdd_phi_prod {φ : ℝ → ℝ} (hφ : PlaqWeight n φ) (s : Finset (LatticePlaquette d N)) :
    IsBdd (fun U : GaugeConnection G d N => ∏ p ∈ s, φ (xp n p U)) :=
  IsBdd.prod s (fun p => isBdd_phi_xp hU hφ p)

theorem phi_prod_nonneg {φ : ℝ → ℝ} (hφ : PlaqWeight n φ) (s : Finset (LatticePlaquette d N))
    (U : GaugeConnection G d N) : 0 ≤ ∏ p ∈ s, φ (xp n p U) :=
  prod_nonneg fun p _ => hφ.nonneg _ (xp_abs_le hU p U)

end Bounds

theorem measurable_phi_prod (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) {φ : ℝ → ℝ}
    (hφ : PlaqWeight n φ) (s : Finset (LatticePlaquette d N)) :
    Measurable (fun U : GaugeConnection G d N => ∏ p ∈ s, φ (xp n p U)) :=
  Finset.measurable_prod s (fun p _ => hφ.meas.comp (measurable_xp hc p))

variable [HasHaarProbability G] [(haarG G).IsInvInvariant]

variable (hN : Even N) (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
include hN hc hU

theorem plaquette_integrand_eq {φ : ℝ → ℝ} (F F' : GaugeConnection G d N → ℝ) (U : GaugeConnection G d N) :
    F U * F' (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), φ (xp n p U) =
      (F U * posWeightφ n φ U) * (F' (thetaConn U) * posWeightφ n φ (thetaConn U)) * fixWeightφ n φ U := by
  rw [plaquette_weight_factor hN (gaugeReTr_inv_of_unitary hU) φ U]; ring

theorem rp_plaquette_weight_of_isBdd {φ : ℝ → ℝ} (hφ : PlaqWeight n φ) {F : GaugeConnection G d N → ℝ}
    (hF : LinkDep F (posHalfLinks d N)) (mF : Measurable F) (bF : IsBdd F) :
    0 ≤ ∫ U, F U * F (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), φ (xp n p U)
      ∂(productHaar G d N) := by
  simp_rw [plaquette_integrand_eq hN hc hU (φ := φ) F F]
  have : Nonempty G := ⟨1⟩
  exact config_rp (haarG G) (fun x => linkTwist_measurePreserving x.1) (isReflection_thetaConn hN)
    ((depPos_of_linkDep hN hF).mul (posWeightφ_depPos hN φ)) (fixWeightφ_depFix hN φ)
    (mF.mul (measurable_phi_prod hc hφ _)) (measurable_phi_prod hc hφ _)
    (bF.mul (isBdd_phi_prod hU hφ _)) (isBdd_phi_prod hU hφ _)
    (fun U => phi_prod_nonneg hU hφ _ U)

/-- **Reflection positivity for any plaquette weight that is a function of `Re tr U_p` (site reflection).**
    For every measurable `φ ≥ 0` (bounded on `[-n, n]`, which is all that matters for `n × n` unitary holonomies) and
    every bounded measurable `F` depending only on the links of the closed positive half:
    `∫ F · (F ∘ Θ) · ∏_p φ(Re tr U_p) d(productHaar) ≥ 0`. -/
theorem rp_plaquette_weight {φ : ℝ → ℝ} (hφ : PlaqWeight n φ) {F : GaugeConnection G d N → ℝ}
    (hF : LinkDep F (posHalfLinks d N)) (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), φ (xp n p U)
      ∂(productHaar G d N) :=
  rp_plaquette_weight_of_isBdd hN hc hU hφ hF mF (IsBdd.of_abs bF)

omit hN in
theorem posObs_integrable_φ {φ : ℝ → ℝ} (hφ : PlaqWeight n φ) {F F' : GaugeConnection G d N → ℝ}
    (hF : PosObs d N G F) (hF' : PosObs d N G F') :
    Integrable (fun U => F U * F' (thetaConn U) *
      ∏ p ∈ (univ : Finset (LatticePlaquette d N)), φ (xp n p U)) (productHaar G d N) :=
  IsBdd.integrable ((hF.2.2.mul (hF'.2.2.comp thetaConn)).mul (isBdd_phi_prod hU hφ _))
    ((hF.2.1.mul (hF'.2.1.comp measurable_thetaConn)).mul (measurable_phi_prod hc hφ _)).aestronglyMeasurable

/-- **Gram positivity for a general plaquette weight.** -/
theorem rp_plaquette_weight_gram {φ : ℝ → ℝ} (hφ : PlaqWeight n φ) {ι : Type*} (s : Finset ι)
    (Fs : ι → GaugeConnection G d N → ℝ)
    (hFs : ∀ i ∈ s, LinkDep (Fs i) (posHalfLinks d N) ∧ Measurable (Fs i) ∧ ∃ M, ∀ U, |Fs i U| ≤ M) (z : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, z i * z j *
      ∫ U, Fs i U * Fs j (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), φ (xp n p U)
        ∂(productHaar G d N) :=
  gram_of_rp thetaConn _ (PosObs d N G) posObs_zero (fun _ _ => posObs_add) (fun t _ => posObs_smul t)
    (fun _ _ hF hF' => posObs_integrable_φ hc hU hφ hF hF')
    (fun _ hF => rp_plaquette_weight_of_isBdd hN hc hU hφ hF.1 hF.2.1 hF.2.2) s Fs
    (fun i hi => ⟨(hFs i hi).1, (hFs i hi).2.1, IsBdd.of_abs (hFs i hi).2.2⟩) z

omit hN hc hU in
/-- The Wilson weight `exp (β ·)` is a plaquette weight. -/
theorem plaqWeight_exp (β : ℝ) : PlaqWeight n (fun x => Real.exp (β * x)) where
  meas := Real.measurable_exp.comp (measurable_const.mul measurable_id)
  nonneg := fun x _ => (Real.exp_pos _).le
  bdd := ⟨Real.exp (|β| * n), fun x hx => by
    rw [abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc β * x ≤ |β * x| := le_abs_self _
      _ = |β| * |x| := abs_mul _ _
      _ ≤ |β| * n := mul_le_mul_of_nonneg_left hx (abs_nonneg _)⟩

/-- **`wilson_rp` as the special case `φ = exp (β ·)`** of `rp_plaquette_weight`. -/
theorem wilson_rp_of_general (β : ℝ) {F : GaugeConnection G d N → ℝ} (hF : LinkDep F (posHalfLinks d N))
    (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaConn U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
      ∂(productHaar G d N) :=
  rp_plaquette_weight hN hc hU (plaqWeight_exp β) hF mF bF

end Measure


/-! ## Link reflection: crossing plaquettes pure exponential, the others arbitrary

The link-reflection proof (`wilson_rp_link`) needs the crossing plaquettes to carry a positive-definite kernel in
`(P, Θ P)`: `exp (β ⟨P, Θ P⟩)` with `β ≥ 0` is one. A general `φ(Re tr (P (Θ P)⁻¹))` is not (an indicator is not, in
general), and we do not know whether link-reflection positivity holds for such weights. What does go through is the mixed
weight below: pure exponential `exp (β Re tr U_p)` (with `β ≥ 0`) on the crossing plaquettes, an arbitrary plaquette weight
`ψ` on all the others. -/

/-- The mixed plaquette weight: `exp (β x)` on crossing plaquettes, `ψ x` on the others. -/
def mixedWeight (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (ψ : ℝ → ℝ) (p : LatticePlaquette d N) (U : GaugeConnection G d N) :
    ℝ :=
  if IsCrossPL p then Real.exp (β * xp n p U) else ψ (xp n p U)

/-- The weight of the positive plaquettes of the link reflection, plaquette weight `ψ`. -/
def posWeightLψ (n : ℕ) [HasGaugeTrace G n] (ψ : ℝ → ℝ) (U : GaugeConnection G d N) : ℝ :=
  ∏ p ∈ (univ : Finset (LatticePlaquette d N)).filter IsPosPL, ψ (xp n p U)

theorem posWeightLψ_linkDep (hN : Even N) (ψ : ℝ → ℝ) :
    LinkDep (posWeightLψ (G := G) (d := d) (N := N) n ψ) (posLinksL d N) := by
  intro U V h
  unfold posWeightLψ
  refine prod_congr rfl fun p hp => ?_
  simp only [mem_filter, mem_univ, true_and] at hp
  have hl : ∀ i, U (p.boundaryLinks i) = V (p.boundaryLinks i) := fun i =>
    h _ (by simp only [posLinksL, mem_filter, mem_univ, true_and]; exact posPL_links hN hp i)
  simp only [xp, plaquetteHolonomy, hl]

section MeasureL

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem measurable_mixedWeight (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) {ψ : ℝ → ℝ}
    (hψ : PlaqWeight n ψ) (β : ℝ) :
    Measurable (fun U : GaugeConnection G d N =>
      ∏ p ∈ (univ : Finset (LatticePlaquette d N)), mixedWeight n β ψ p U) := by
  refine Finset.measurable_prod _ (fun p _ => ?_)
  unfold mixedWeight
  by_cases h : IsCrossPL p
  · simp only [h, ite_true]
    exact measurable_expxp hc β p
  · simp only [h, ite_false]
    exact hψ.meas.comp (measurable_xp hc p)

variable [HasHaarProbability G] [(haarG G).IsInvInvariant] [(haarG G).IsMulRightInvariant]
  [(haarG G).IsMulLeftInvariant]

variable (hN : Even N) (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
include hN hc hU

/-- The mixed weight on the extended space. -/
theorem mixed_weight_factor_ext (β : ℝ) (ψ : ℝ → ℝ) (ω : ExtIdx d N → G) :
    ∏ p ∈ (univ : Finset (LatticePlaquette d N)), mixedWeight n β ψ p (recombine ω) =
      posWeightLψ n ψ (recombine ω) * posWeightLψ n ψ (recombine (thetaExt ω)) *
        Real.exp (β * ∑ j, crossFeat n j ω * crossFeat n j (thetaExt ω)) := by
  have hinv := gaugeReTr_inv_of_unitary hU
  rw [← prod_filter_mul_prod_filter_not univ IsPosPL,
    ← prod_filter_mul_prod_filter_not ((univ : Finset (LatticePlaquette d N)).filter (fun p => ¬IsPosPL p))
      IsCrossPL]
  have hcr : ((univ : Finset (LatticePlaquette d N)).filter (fun p => ¬IsPosPL p)).filter IsCrossPL =
      univ.filter IsCrossPL := by
    ext p
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    intro hc hp
    exact not_crossPL_of_posPL hp hc
  have hpos : ∏ p ∈ (univ : Finset (LatticePlaquette d N)).filter IsPosPL, mixedWeight n β ψ p (recombine ω) =
      posWeightLψ n ψ (recombine ω) := by
    unfold posWeightLψ
    refine prod_congr rfl fun p hp => ?_
    simp only [mem_filter, mem_univ, true_and] at hp
    simp [mixedWeight, not_crossPL_of_posPL hp]
  have hneg : ∏ p ∈ ((univ : Finset (LatticePlaquette d N)).filter (fun p => ¬IsPosPL p)).filter
      (fun p => ¬IsCrossPL p), mixedWeight n β ψ p (recombine ω) = posWeightLψ n ψ (recombine (thetaExt ω)) := by
    unfold posWeightLψ
    have e : ∀ p ∈ ((univ : Finset (LatticePlaquette d N)).filter (fun p => ¬IsPosPL p)).filter
        (fun p => ¬IsCrossPL p), mixedWeight n β ψ p (recombine ω) = ψ (xp n p (recombine ω)) := by
      intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      simp [mixedWeight, hp.2]
    rw [prod_congr rfl e]
    simp_rw [recombine_thetaExt hN, xp_thetaL hinv]
    symm
    refine prod_nbij' mirrorPL mirrorPL (fun q hq => ?_) (fun p hp => ?_) (fun q _ => mirrorPL_involutive q)
      (fun p _ => mirrorPL_involutive p) (fun q _ => rfl)
    · simp only [mem_filter, mem_univ, true_and] at hq ⊢
      exact ⟨(posPL_mirror hN hq).1, (posPL_mirror hN hq).2⟩
    · simp only [mem_filter, mem_univ, true_and] at hp ⊢
      exact negPL_mirror hN hp.1 hp.2
  have hcross : ∏ p ∈ (univ : Finset (LatticePlaquette d N)).filter IsCrossPL, mixedWeight n β ψ p (recombine ω) =
      Real.exp (β * ∑ j, crossFeat n j ω * crossFeat n j (thetaExt ω)) := by
    rw [← sum_cross_xp hN hU, Finset.mul_sum, Real.exp_sum]
    refine prod_congr rfl fun p hp => ?_
    simp only [mem_filter, mem_univ, true_and] at hp
    simp [mixedWeight, hp]
  rw [hcr, hneg, hcross, hpos]
  ring

/-- **Link-reflection positivity for the mixed weight** (`β ≥ 0`): pure exponential `exp (β Re tr U_p)` on the crossing
    plaquettes, an arbitrary plaquette weight `ψ` (measurable, `≥ 0`, bounded on `[-n, n]`) on all other plaquettes. For
    `F` bounded measurable depending on the links of the open positive half:
    `∫ F · (F ∘ Θ) · ∏_p w_p d(productHaar) ≥ 0` for the link reflection `Θ`. -/
theorem rp_plaquette_weight_link {β : ℝ} (hβ : 0 ≤ β) {ψ : ℝ → ℝ} (hψ : PlaqWeight n ψ)
    {F : GaugeConnection G d N → ℝ} (hF : LinkDep F (posLinksL d N))
    (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaL U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), mixedWeight n β ψ p U
      ∂(productHaar G d N) := by
  have : Nonempty G := ⟨1⟩
  have mW := measurable_mixedWeight hc hψ β (d := d) (N := N)
  have mWp : Measurable (fun U : GaugeConnection G d N => posWeightLψ n ψ U) :=
    Finset.measurable_prod _ (fun p _ => hψ.meas.comp (measurable_xp hc p))
  rw [← integral_comp_of_measurePreserving measurePreserving_recombine
    (g := fun U => F U * F (thetaL U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), mixedWeight n β ψ p U)
    ((mF.mul (mF.comp measurable_thetaL)).mul mW).aestronglyMeasurable]
  have key : ∀ ω : ExtIdx d N → G,
      F (recombine ω) * F (thetaL (recombine ω)) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d N)), mixedWeight n β ψ p (recombine ω) =
      (F (recombine ω) * posWeightLψ n ψ (recombine ω)) *
        (F (recombine (thetaExt ω)) * posWeightLψ n ψ (recombine (thetaExt ω))) * (fun _ => (1 : ℝ)) ω *
          Real.exp (β * ∑ j, crossFeat n j ω * crossFeat n j (thetaExt ω)) := by
    intro ω
    rw [mixed_weight_factor_ext hN hc hU β ψ ω, ← recombine_thetaExt hN]
    ring
  simp_rw [key]
  have hrec : Measurable (recombine (G := G) (d := d) (N := N)) := measurePreserving_recombine.measurable
  have bPos : IsBdd (fun U : GaugeConnection G d N => posWeightLψ n ψ U) :=
    isBdd_phi_prod hU hψ _
  exact config_rp_kernel (haarG G) (fun x => by
      rcases x with x | c
      · exact linkTwist_measurePreserving x.1
      · exact MeasurePreserving.id _)
    (isReflection_thetaExt hN)
    (F := fun ω => F (recombine ω) * posWeightLψ n ψ (recombine ω)) (B := fun _ => 1)
    ((depPos_comp_recombine hN hF).mul (depPos_comp_recombine hN (posWeightLψ_linkDep hN ψ)))
    (fun _ _ _ => rfl) ((mF.comp hrec).mul (mWp.comp hrec)) measurable_const
    (((IsBdd.of_abs bF).comp _).mul (bPos.comp _)) (IsBdd.const 1)
    (fun _ => zero_le_one) (crossFeat_depPos hN) (measurable_crossFeat hc) (isBdd_crossFeat hU) hβ

end MeasureL

end Positivity
