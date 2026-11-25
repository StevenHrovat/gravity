/-
Proof phase, cycle 7, workstream b (c7b-centre): the Z2 lattice gauge group as an instance of the area-law project's
gauge-group interface, and the Z2 Wilson expectation as an Ising correlation (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c7b-centre/NOTE.md`, section 2.
-/

import AreaLaw.Concrete
import ProofPhase.Centre.Comparison

/-!
# Z2 gauge theory in the area-law project's interface

* `Z2`: the group of order two (a structure around `Bool`, so no other instance can interfere), with the discrete topology,
  the discrete Borel structure, the one-dimensional representation `g ↦ ±1` (`HasGaugeTrace Z2 1`, centre element
  `z = Z2.neg` with `rep z = -1`), and its normalised Haar measure (uniform: each point `1/2`, `haarG_singleton`).
* `wilson_area_law_Z2`: the repo's strong-coupling area law (`AreaLaw.Concrete.wilson_area_law_explicit`) for `G = Z2`,
  `n = 1`: for `e^β - 1 ≤ 1/(4 e^{16d+1}(16d+1)^4)`,
  `|⟨W_{R×T}⟩| ≤ e^{2·4d·2(R+T)} (√(e^{16d+1}(e^β - 1)))^{min(RT, N²-RT)}`.
* `integral_productHaar_Z2`: `∫ F d(productHaar Z2 d N) = 2^{-|links|} ∑_σ F(σ)`.
* `wilsonRatio_Z2_eq_corr`: the Z2 Wilson expectation (ratio of integrals of the repo) is the Ising correlation
  `corr plaqSupp (fun _ => β) (pathSupp C)` of `ProofPhase.Centre.Ginibre`, with one interaction per plaquette whose
  support is its four boundary links, and `pathSupp C` the multiset of links of the path.

Claim level: proved in Lean (the group interface, the integral formula, the identification); the area law is the repo's.
-/

open Finset MeasureTheory

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Centre

/-! ## The group Z2 -/

/-- The group of order two. -/
structure Z2 where
  val : Bool
  deriving DecidableEq

namespace Z2

instance : Group Z2 where
  mul a b := ⟨xor a.val b.val⟩
  one := ⟨false⟩
  inv a := a
  mul_assoc a b c := by cases a with | mk a => cases b with | mk b => cases c with | mk c => cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a with | mk a => cases a <;> rfl
  mul_one a := by cases a with | mk a => cases a <;> rfl
  inv_mul_cancel a := by cases a with | mk a => cases a <;> rfl

theorem mul_val (a b : Z2) : (a * b).val = xor a.val b.val := rfl

theorem one_val : (1 : Z2).val = false := rfl

theorem inv_eq (a : Z2) : a⁻¹ = a := rfl

theorem ext' {a b : Z2} (h : a.val = b.val) : a = b := by cases a; cases b; simp_all

/-- The non-trivial element (`-1`). -/
def neg : Z2 := ⟨true⟩

theorem comm (a b : Z2) : a * b = b * a := ext' (by rw [mul_val, mul_val, Bool.xor_comm])

instance : Fintype Z2 :=
  Fintype.ofEquiv Bool ⟨fun b => ⟨b⟩, Z2.val, fun _ => rfl, fun a => by cases a; rfl⟩

instance : TopologicalSpace Z2 := ⊥
instance : DiscreteTopology Z2 := ⟨rfl⟩
instance : IsTopologicalGroup Z2 := inferInstance
instance : MeasurableSpace Z2 := ⊤
instance : DiscreteMeasurableSpace Z2 := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass Z2 := inferInstance
instance : BorelSpace Z2 := ⟨by
  rw [borel_eq_top_of_discrete]; rfl⟩
instance : SecondCountableTopology Z2 := inferInstance
instance : CompactSpace Z2 := inferInstance

/-- The one-dimensional representation `g ↦ ±1`. -/
def rep : Z2 →* Matrix (Fin 1) (Fin 1) ℂ where
  toFun g := Matrix.of fun _ _ => (((ProofPhase.Centre.sgn g.val : ℝ)) : ℂ)
  map_one' := by
    ext i j; fin_cases i; fin_cases j; simp [one_val, ProofPhase.Centre.sgn]
  map_mul' a b := by
    ext i j; fin_cases i; fin_cases j
    simp only [Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_one, mul_val]
    rw [← Complex.ofReal_mul]; congr 1
    rw [ProofPhase.Centre.sgn_xor]

instance : HasGaugeTrace Z2 1 := ⟨rep⟩

instance : HasHaarProbability Z2 := AreaLaw.Concrete.haarProbability Z2

instance : (haarG Z2).IsMulLeftInvariant := by
  show (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts Z2)).IsMulLeftInvariant; infer_instance

theorem gaugeReTr_eq (g : Z2) : gaugeReTr Z2 1 g = ProofPhase.Centre.sgn g.val := by
  simp [gaugeReTr, gaugeTrace, HasGaugeTrace.rep, rep, Matrix.trace, Fin.sum_univ_one]

theorem rep_neg : HasGaugeTrace.rep (G := Z2) (n := 1) neg = -1 := by
  ext i j; fin_cases i; fin_cases j; simp [HasGaugeTrace.rep, rep, neg, ProofPhase.Centre.sgn]

end Z2

/-! ## The area law of the repo for Z2 -/

section AreaLaw

open AreaLaw.Assembly AreaLaw.Concrete

variable {d N : ℕ}

/-- **The strong-coupling area law for Z2 lattice gauge theory** (the repo's `wilson_area_law_explicit` for `G = Z2`, `n = 1`;
Wilson action `exp (β ∑_p ±1)`, periodic lattice, `R × T` loop). -/
theorem wilson_area_law_Z2 [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.exp β - 1 ≤ 1 / (4 * Real.exp (16 * d + 1) * (16 * d + 1) ^ 4))
    (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < N) (hTN : T < N) :
    |(∫ U, wilsonLoop 1 (rectPath x μ ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 1 p U) ∂(productHaar Z2 d N)) /
      (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 1 p U) ∂(productHaar Z2 d N))| ≤
      Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp β - 1)) ^ (min (R * T) (N * N - R * T)) := by
  have hc : Continuous (HasGaugeTrace.rep (G := Z2) (n := 1)) := continuous_of_discreteTopology
  have hbd : ∀ g : Z2, |gaugeReTr Z2 1 g| ≤ (1 : ℕ) := fun g => by
    rw [Z2.gaugeReTr_eq]; rcases ProofPhase.Centre.sgn_eq g.val with h | h <;> rw [h] <;> norm_num
  have hz : ∀ g : Z2, Commute Z2.neg g := fun g => Z2.comm _ _
  have hzz : Z2.neg * Z2.neg = 1 := Z2.ext' (by simp [Z2.mul_val, Z2.neg, Z2.one_val])
  have hs : Real.exp ((1 : ℕ) * β) - 1 ≤ 1 / (4 * Real.exp (16 * d + 1) * (16 * d + 1) ^ 4) := by
    simpa using hsmall
  have h := (wilson_area_law_explicit hc hbd Z2.neg hz hzz Z2.rep_neg hβ hs x hμν R T hR hT hRN hTN).2
  simpa using h

end AreaLaw

/-! ## The Z2 Wilson expectation is an Ising correlation -/

section Bridge

open AreaLaw.Assembly AreaLaw.Concrete

variable {d N : ℕ} [NeZero N]

/-- The Z2 connection of a spin configuration. -/
def toConn (σ : LatticeLink d N → Bool) : GaugeConnection Z2 d N := fun l => ⟨σ l⟩

/-- Support (as a multiset of links) of the plaquette interaction: the four boundary links. -/
def plaqSupp (p : LatticePlaquette d N) : Multiset (LatticeLink d N) :=
  (Finset.univ : Finset (Fin 4)).val.map p.boundaryLinks

/-- The multiset of links a path traverses (with multiplicity). -/
def pathSupp (C : List (PathStep d N)) : Multiset (LatticeLink d N) := (C.map PathStep.link : List (LatticeLink d N))

/-- `Z2` as `Bool`. -/
def equivBool : Z2 ≃ Bool := ⟨Z2.val, fun b => ⟨b⟩, fun a => by cases a; rfl, fun _ => rfl⟩

theorem card_Z2 : Fintype.card Z2 = 2 := by rw [Fintype.card_congr equivBool]; rfl

theorem haar_singleton (g : Z2) : (haarG Z2).real {g} = 1 / 2 := by
  have hinv : ∀ h : Z2, (haarG Z2) {h} = (haarG Z2) {1} := by
    intro h
    have := measure_preimage_mul (haarG Z2) h ({1} : Set Z2)
    have e : (fun x : Z2 => h * x) ⁻¹' {1} = {h} := by
      ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        have h1 := congrArg Z2.val hx
        rw [Z2.mul_val, Z2.one_val] at h1
        apply Z2.ext'
        revert h1; cases h.val <;> cases x.val <;> simp
      · rintro rfl; exact Z2.ext' (by simp [Z2.mul_val, Z2.one_val])
    rw [e] at this; exact this
  have hsum : ∑ x : Z2, (haarG Z2).real {x} = 1 := by
    have := sum_measure_singleton (μ := haarG Z2) (s := (Finset.univ : Finset Z2))
    simp only [Finset.coe_univ, measure_univ] at this
    simp only [Measure.real]
    rw [← ENNReal.toReal_sum (fun x _ => measure_ne_top _ _), this]; simp
  have hall : ∀ h : Z2, (haarG Z2).real {h} = (haarG Z2).real {1} := fun h => by simp only [Measure.real, hinv h]
  have h2 : ∑ x : Z2, (haarG Z2).real {x} = 2 * (haarG Z2).real {1} := by
    simp_rw [hall]; rw [Finset.sum_const, Finset.card_univ, card_Z2]; simp
  rw [hall g]; linarith

theorem integral_productHaar_Z2 (F : GaugeConnection Z2 d N → ℝ) :
    ∫ U, F U ∂(productHaar Z2 d N) =
      (1 / 2 : ℝ) ^ Fintype.card (LatticeLink d N) * ∑ σ : LatticeLink d N → Bool, F (toConn σ) := by
  unfold productHaar
  rw [integral_fintype Integrable.of_finite]
  have hs : ∀ x : GaugeConnection Z2 d N,
      (Measure.pi (fun _ : LatticeLink d N => haarG Z2)).real {x} = (1 / 2 : ℝ) ^ Fintype.card (LatticeLink d N) := by
    intro x
    simp only [Measure.real, Measure.pi_singleton]
    rw [ENNReal.toReal_prod]
    have hh : ∀ l, ((haarG Z2) {x l}).toReal = 1 / 2 := fun l => haar_singleton (x l)
    simp only [hh]
    simp
  simp_rw [hs, smul_eq_mul, ← Finset.mul_sum]
  congr 1
  exact (Fintype.sum_equiv (Equiv.piCongrRight fun _ => equivBool.symm) _ _ (fun σ => rfl)).symm


theorem mono_plaqSupp (σ : LatticeLink d N → Bool) (p : LatticePlaquette d N) :
    ProofPhase.Centre.mono σ (plaqSupp p) =
      sgn (σ (p.boundaryLinks 0)) * sgn (σ (p.boundaryLinks 1)) * sgn (σ (p.boundaryLinks 2)) *
        sgn (σ (p.boundaryLinks 3)) := by
  unfold ProofPhase.Centre.mono plaqSupp
  rw [Multiset.map_map]
  have := Fin.prod_univ_four (fun j => sgn (σ (p.boundaryLinks j)))
  exact this

theorem xp_Z2 (σ : LatticeLink d N → Bool) (p : LatticePlaquette d N) :
    xp 1 p (toConn σ) = ProofPhase.Centre.mono σ (plaqSupp p) := by
  rw [mono_plaqSupp]
  unfold xp
  rw [Z2.gaugeReTr_eq]
  simp only [plaquetteHolonomy, toConn, Z2.mul_val, Z2.inv_eq, sgn_xor]

theorem gaugeReTr_mul_Z2 (a b : Z2) : gaugeReTr Z2 1 (a * b) = gaugeReTr Z2 1 a * gaugeReTr Z2 1 b := by
  simp only [Z2.gaugeReTr_eq, Z2.mul_val, sgn_xor]

theorem wilsonLoop_Z2 (σ : LatticeLink d N → Bool) (C : List (PathStep d N)) :
    wilsonLoop 1 C (toConn σ) = ProofPhase.Centre.mono σ (pathSupp C) := by
  induction C with
  | nil =>
    simp [wilsonLoop, pathHol, pathSupp, ProofPhase.Centre.mono, gaugeReTr, gaugeTrace, map_one]
  | cons s rest ih =>
    have h1 : wilsonLoop 1 (s :: rest) (toConn σ) = gaugeReTr Z2 1 (s.hol (toConn σ)) * wilsonLoop 1 rest (toConn σ) := by
      unfold wilsonLoop; rw [pathHol, gaugeReTr_mul_Z2]
    have h2 : gaugeReTr Z2 1 (s.hol (toConn σ)) = sgn (σ s.link) := by
      unfold PathStep.hol
      cases s.fwd <;> simp [Z2.gaugeReTr_eq, toConn, Z2.inv_eq]
    have h3 : ProofPhase.Centre.mono σ (pathSupp (s :: rest)) = sgn (σ s.link) * ProofPhase.Centre.mono σ (pathSupp rest) := by
      simp [ProofPhase.Centre.mono, pathSupp]
    rw [h1, h2, ih, h3]

/-- **The Z2 Wilson expectation of the repo is an Ising correlation**: one interaction per plaquette, support its four
boundary links, coupling `β`; the loop `C` is the monomial of its links. -/
theorem wilsonRatio_Z2_eq_corr (β : ℝ) (C : List (PathStep d N)) :
    (∫ U, wilsonLoop 1 C U * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 1 p U)
        ∂(productHaar Z2 d N)) /
      (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 1 p U) ∂(productHaar Z2 d N)) =
    corr plaqSupp (fun _ => β) (pathSupp C) := by
  have hE : ∀ σ : LatticeLink d N → Bool,
      ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 1 p (toConn σ)) =
        Real.exp (energy plaqSupp (fun _ => β) σ) := by
    intro σ
    rw [energy, Real.exp_sum]
    exact Finset.prod_congr rfl (fun p _ => by rw [xp_Z2])
  rw [integral_productHaar_Z2, integral_productHaar_Z2]
  simp_rw [hE, wilsonLoop_Z2]
  unfold corr num Zf
  have hc : ((1 / 2 : ℝ) ^ Fintype.card (LatticeLink d N)) ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ hc]

end Bridge

end ProofPhase.Centre
