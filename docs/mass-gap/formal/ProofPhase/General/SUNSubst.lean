/-
Proof phase, generalisation phase 2: the `GaugeSubst` instance of SU(N), its agreement with the SU(2) instance, and
the strong-coupling area law for SU(N) with `N` even (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 2.
-/

import ProofPhase.General.Centre
import ProofPhase.General.Projection
import ProofPhase.General.Combined
import ProofPhase.General.Filter
import ProofPhase.General.Torus

/-!
# SU(N) as an instance of `GaugeSubst`, and the agreement with SU(2)

`instGaugeSubstSUN N` (for `N ≥ 2`, given as `[Fact (2 ≤ N)]`): the cost distance `geodSUN`, the centre `Z_N`
(the range of `centreHom`) and the polar projection `projSUN`. Every field is proved.

**Agreement with the SU(2) instance of phase 1 (`instGaugeSubstSU2`), at `N = 2`.**
* The Prop-valued instances coincide (`GaugeGroupBase`, `GaugeRep`: proof irrelevance).
* The cost distances are equal (`geodSUN_two`).
* The centres are equal as sets: `range (centreHom 2) = {1, negOneSU2}` (`range_centreHom_two`).
* The projections agree on `SU(2)`, where both are the identity (`projSUN_two_eq_on_SU2`). They are **different maps off
  SU(2)** (`RouteA.projSU2` rescales by `|det A|^{-1/2}` and falls back to `1`; `projSUN` is the polar factor with a
  phase correction), and the package only uses the identity on the group.
* The mixture area law of phase 1 for SU(2) is re-derived from the SU(N) one at `N = 2`
  (`su2_area_law_of_mixture_SUN`, same type as `su2_area_law_of_mixture_general`).

**The area law for SU(N), `N` even.** `-I ∈ SU(N)` exactly when `N` is even; then `wilson_area_law_explicit` applies with
`z = -I` and gives the strong-coupling area law for SU(N), the bound of `wilson_area_law_SU2` with `2` replaced by `N`
(`wilson_area_law_SUN_even`). For odd `N` the order-two centre does not exist; the argument there needs the `Z_N` layer
(phase 3).
-/

open MeasureTheory Finset AreaLaw.Concrete

open scoped Classical

noncomputable section

namespace ProofPhase.General

section Subst

variable (N : ℕ) [NeZero N] [Fact (2 ≤ N)]

/-- **SU(N), `N ≥ 2`, as an instance of the `subst` layer.** -/
instance instGaugeSubstSUN : GaugeSubst (SUN N) N where
  geodDist := geodSUN N
  geodDist_nonneg := geodSUN_nonneg
  geodDist_pos := exists_geodSUN_pos (Fact.out)
  centre := Set.range (centreHom N)
  one_mem_centre := ⟨1, map_one _⟩
  centre_central := by
    rintro _ ⟨ζ, rfl⟩ g
    exact centreHom_central ζ g
  centre_scalar := by
    rintro _ ⟨ζ, rfl⟩
    exact ⟨((ζ : ℂˣ) : ℂ), centreHom_rep ζ⟩
  proj := projSUN N
  proj_rep g := projSUN_coe g

end Subst

/-! ## Agreement with the SU(2) instance at `N = 2` -/

section Two

/-- The `GaugeGroupBase` instances agree (a proposition). -/
example : instGaugeGroupBaseSUN 2 = instGaugeGroupBaseSU2 := rfl

/-- The `GaugeRep` instances agree (a proposition). -/
example : instGaugeRepSUN 2 = instGaugeRepSU2 := rfl

/-- The `N = 2` cost distance of the SU(N) instance is the one of the SU(2) instance. -/
theorem geodDist_two :
    (@instGaugeSubstSUN 2 _ ⟨le_refl 2⟩).geodDist = instGaugeSubstSU2.geodDist := geodSUN_two

/-- The centre `Z_2` of SU(2) is `{1, -1}`. -/
theorem range_centreHom_two : Set.range (centreHom 2) = ({1, negOneSU2} : Set (SUN 2)) := by
  ext g
  constructor
  · rintro ⟨ζ, rfl⟩
    have h := rootsOfUnity_pow ζ
    have h' : ((ζ : ℂˣ) : ℂ) * ((ζ : ℂˣ) : ℂ) = 1 := by rw [← sq]; exact h
    rcases mul_self_eq_one_iff.1 h' with h1 | h1
    · left
      have : ζ = 1 := Subtype.ext (Units.ext h1)
      rw [this, map_one]
    · right
      rw [← centreElt_two_neg_one]
      exact Subtype.ext (by simp [centreHom_val, h1])
  · rintro (rfl | rfl)
    · exact ⟨1, map_one _⟩
    · refine ⟨⟨-1, by rw [mem_rootsOfUnity]; ext; simp⟩, ?_⟩
      rw [← centreElt_two_neg_one]
      exact Subtype.ext (by simp [centreHom_val])

/-- The centres of the two instances agree. -/
theorem centre_two :
    (@instGaugeSubstSUN 2 _ ⟨le_refl 2⟩).centre = instGaugeSubstSU2.centre := range_centreHom_two

/-- The two projections agree on SU(2), where both are the identity. -/
theorem projSUN_two_eq_on_SU2 (g : SU2) :
    projSUN 2 (g : Matrix (Fin 2) (Fin 2) ℂ) = ProofPhase.RouteA.projSU2 (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [projSUN_coe g, ProofPhase.RouteA.projSU2_coe g]

end Two

/-! ## The mixture area law and the strong-coupling area law for SU(N) -/

section AreaLaw

open AreaLaw.Assembly ProofPhase.Centre

variable {d M : ℕ} [NeZero M]

/-- **The mixture area law for SU(N)**: `area_law_of_mixture` at `G = SUN N`, `n = N`, `B = M = N`. -/
theorem area_law_of_mixture_SUN (N : ℕ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → LatticePlaquette d M → ℝ) (w : Ω → ℝ) (hw : ∀ v, |w v| ≤ N) (hr : ∀ v p, |r v p| ≤ N)
    {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.exp (N * β) - 1 ≤ 1 / (4 * Real.exp (16 * d + 1) * (16 * d + 1) ^ 4))
    (x : FinLatticeSites d M) {μ' ν : Fin d} (hμν : μ' < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < M) (hTN : T < M)
    (hmix : (∫ U, wilsonLoop N (rectPath x μ' ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d M)), Real.exp (β * xp N p U) ∂(productHaar (SUN N) d M)) /
        (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d M)), Real.exp (β * xp N p U) ∂(productHaar (SUN N) d M)) =
        ∫ v, w v * corr plaqSupp (fun p => β * r v p) (pathSupp (rectPath x μ' ν R T)) ∂μ) :
    |(∫ U, wilsonLoop N (rectPath x μ' ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d M)), Real.exp (β * xp N p U) ∂(productHaar (SUN N) d M)) /
        (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d M)), Real.exp (β * xp N p U) ∂(productHaar (SUN N) d M))| ≤
      N * Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp (N * β) - 1)) ^ (min (R * T) (M * M - R * T)) :=
  area_law_of_mixture (G := SUN N) (n := N) μ r w (M := N) (B := N) (Nat.cast_nonneg N) (Nat.cast_nonneg N) hw hr hβ
    hsmall x hμν R T hR hT hRN hTN hmix

/-- **`su2_area_law_of_mixture_general` re-derived from the SU(N) version at `N = 2`** (same statement). -/
theorem su2_area_law_of_mixture_SUN {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → LatticePlaquette d M → ℝ) (w : Ω → ℝ) (hw : ∀ v, |w v| ≤ 2) (hr : ∀ v p, |r v p| ≤ 2)
    {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.exp (2 * β) - 1 ≤ 1 / (4 * Real.exp (16 * d + 1) * (16 * d + 1) ^ 4))
    (x : FinLatticeSites d M) {μ' ν : Fin d} (hμν : μ' < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < M) (hTN : T < M)
    (hmix : (∫ U, wilsonLoop 2 (rectPath x μ' ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d M)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d M)) /
        (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d M)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d M)) =
        ∫ v, w v * corr plaqSupp (fun p => β * r v p) (pathSupp (rectPath x μ' ν R T)) ∂μ) :
    |(∫ U, wilsonLoop 2 (rectPath x μ' ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d M)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d M)) /
        (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d M)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d M))| ≤
      2 * Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp (2 * β) - 1)) ^ (min (R * T) (M * M - R * T)) := by
  have h := area_law_of_mixture_SUN 2 μ r w (by exact_mod_cast hw) (by exact_mod_cast hr) hβ
    (by exact_mod_cast hsmall) x hμν R T hR hT hRN hTN (by exact_mod_cast hmix)
  exact_mod_cast h

/-- **The strong-coupling area law for SU(N), `N` even** (Wilson action, periodic lattice `(ℤ/M)^d`, `R × T` loop):
the partition function is nonzero and, for `e^{Nβ} − 1 ≤ 1/(4 e^{16d+1}(16d+1)⁴)`,
`|⟨W_{R×T}⟩| ≤ N e^{2·4d·2(R+T)} (√(e^{16d+1}(e^{Nβ} − 1)))^{min(RT, M² − RT)}`. The centre element used is `−I`, which
lies in SU(N) exactly when `N` is even. -/
theorem wilson_area_law_SUN_even (N : ℕ) [NeZero N] (hN : Even N) {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.exp (N * β) - 1 ≤ 1 / (4 * Real.exp (16 * d + 1) * (16 * d + 1) ^ 4))
    (x : FinLatticeSites d M) {μ ν : Fin d} (hμν : μ < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < M) (hTN : T < M) :
    ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d M)), Real.exp (β * xp N p U) ∂(productHaar (SUN N) d M) ≠ 0 ∧
    |(∫ U, wilsonLoop N (rectPath x μ ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d M)), Real.exp (β * xp N p U) ∂(productHaar (SUN N) d M)) /
      (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d M)), Real.exp (β * xp N p U) ∂(productHaar (SUN N) d M))| ≤
      N * Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp (N * β) - 1)) ^ (min (R * T) (M * M - R * T)) := by
  have hpow : (-1 : ℂ) ^ N = 1 := Even.neg_one_pow hN
  set z : SUN N := centreElt N (-1) hpow with hz
  have hc : Continuous (HasGaugeTrace.rep (G := SUN N) (n := N)) := continuous_subtype_val
  have hbd : ∀ g : SUN N, |gaugeReTr (SUN N) N g| ≤ N := fun g => abs_gaugeReTr_le g
  have hzc : ∀ g : SUN N, Commute z g := fun g => centreElt_central (-1) hpow g
  have hzz : z * z = 1 := Subtype.ext (by simp [hz])
  have hrep : HasGaugeTrace.rep (G := SUN N) (n := N) z = -1 := by
    show ((-1 : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) = -1
    simp
  exact wilson_area_law_explicit hc hbd z hzc hzz hrep hβ hsmall x hμν R T hR hT hRN hTN

end AreaLaw


/-! ## The generic layer of phase 1 at SU(N)

The generic theorems of phase 1 apply to `SUN N` as they stand, because `GaugeGroupBase (SUN N)` and `GaugeRep (SUN N) N`
are instances. Two examples, for every `N` and every dimension `d`. -/

section GenericAtSUN


/-- Smoother stability gives part (c) of the transfer for the Wilson measure of SU(N), any `N`, any `d`. -/
theorem condDecouple_of_smootherStable_SUN (N d : ℕ) [NeZero N] [NeZero d] {T : Tuning}
    {B : BlockingFamily (SUN N) d T} {Sep : SepPred d T} (h : SmootherStable (G := SUN N) N B Sep) :
    CondDecouple (G := SUN N) N B Sep :=
  condDecouple_of_smootherStable N h

/-- The one-box criterion gives the W₁ gap for laws on `GaugeConnection (SUN N) d (M j)`, with the cost distance
`geodSUN`. -/
theorem lawGapBddW_of_oneBoxLaw_SUN (N d : ℕ) [NeZero d] {M : ℕ → ℕ} [∀ j, NeZero (M j)]
    {ρ : ℕ → ∀ j, Measure (GaugeConnection (SUN N) d (M j))} {lam : ℝ} (hlam : 0 ≤ lam)
    (hρ : ∀ k j, IsProbabilityMeasure (ρ k j)) (h : OneBoxLaw ρ lam) :
    LawGapBddW (geodSUN N) ρ lam := by
  have : Nonempty (SUN N) := ⟨1⟩
  exact lawGapBddW_of_oneBoxLaw hlam hρ h

end GenericAtSUN
end ProofPhase.General
