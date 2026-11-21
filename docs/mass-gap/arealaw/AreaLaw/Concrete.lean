/-
Concrete instances of the area law (area-law project, 2026-11-21). Released under Apache 2.0.

# Discharging the hypotheses of `wilson_area_law_rect`

1. `Fintype` instances for links and plaquettes of the periodic lattice (`[NeZero N]`).
2. The degree bound `(plaqGraph d N).degree p ≤ 16 d` (`plaqGraph_degree_le`): a link lies in at most `4 d` plaquettes
   (one of 4 boundary slots, one free direction; the site is then determined), and a neighbour shares one of the 4 links.
3. The perimeter bounds `(loopPlaqs C).card ≤ 4 d · (pathLinks C).card` and `(pathLinks (rectPath …)).card ≤ 2 (R + T)`.
4. The concrete gauge groups SU(2) and U(n) with Borel structure, normalised Haar measure, the defining representation and
   the centre element `z = -1`; the final area laws `wilson_area_law_SU2`, `wilson_area_law_Un`.

The compactness argument for the unitary group follows the idea of `mrdouglasny/lgt` (Copyright (c) 2026 Michael R. Douglas,
Apache 2.0, `LGT/GaugeField/UnitaryGroup.lean`): the unitary matrices are a closed subset of the product of closed unit balls.
-/

import AreaLaw.Assembly

open Finset MeasureTheory

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace AreaLaw.Concrete

open AreaLaw.Assembly

variable {d N : ℕ}

/-! ## 1. Finiteness of links and plaquettes -/

/-- Links are pairs (site, direction). -/
def linkEquiv (d N : ℕ) : LatticeLink d N ≃ FinLatticeSites d N × Fin d where
  toFun l := (l.site, l.dir)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeLatticeLink [NeZero N] : Fintype (LatticeLink d N) := Fintype.ofEquiv _ (linkEquiv d N).symm

/-- Plaquettes are pairs (site, ordered pair of directions). -/
def plaqEquiv (d N : ℕ) : LatticePlaquette d N ≃ FinLatticeSites d N × {p : Fin d × Fin d // p.1 < p.2} where
  toFun p := (p.site, ⟨(p.dir1, p.dir2), p.h_lt⟩)
  invFun q := ⟨q.1, q.2.1.1, q.2.1.2, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeLatticePlaquette [NeZero N] : Fintype (LatticePlaquette d N) :=
  Fintype.ofEquiv _ (plaqEquiv d N).symm

/-! ## 2. The degree of the plaquette graph -/

theorem siteShift_injective (μ : Fin d) : Function.Injective (fun x : FinLatticeSites d N => siteShift d N x μ) := by
  intro x y h
  funext i
  have h' := congrFun h i
  by_cases hi : i = μ
  · subst hi; simpa [siteShift] using h'
  · simpa [siteShift, Function.update_of_ne hi] using h'

theorem plaq_ext {p q : LatticePlaquette d N} (hs : p.site = q.site) (h1 : p.dir1 = q.dir1) (h2 : p.dir2 = q.dir2) :
    p = q := by
  cases p; cases q; simp_all

variable [Fintype (LatticePlaquette d N)]

/-- The plaquettes having the link `l` in boundary slot `i`. -/
def plaqsAtSlot (l : LatticeLink d N) (i : Fin 4) : Finset (LatticePlaquette d N) :=
  univ.filter (fun q => q.boundaryLinks i = l)

/-- The direction of a plaquette that is not the direction of its `i`-th boundary link. -/
def otherDir (i : Fin 4) (q : LatticePlaquette d N) : Fin d := if i = 0 ∨ i = 2 then q.dir2 else q.dir1

theorem card_plaqsAtSlot_le (l : LatticeLink d N) (i : Fin 4) : (plaqsAtSlot l i).card ≤ d := by
  have h : (plaqsAtSlot l i).card ≤ (univ : Finset (Fin d)).card := by
    refine card_le_card_of_injOn (otherDir i) (fun _ _ => mem_univ _) ?_
    intro q hq q' hq' he
    simp only [plaqsAtSlot, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hq hq'
    rw [← hq'] at hq
    fin_cases i <;>
      simp only [LatticePlaquette.boundaryLinks, LatticeLink.mk.injEq, otherDir] at hq he <;> simp at he
    · exact plaq_ext hq.1 hq.2 he
    · rw [he] at hq; exact plaq_ext (siteShift_injective _ hq.1) he hq.2
    · rw [he] at hq; exact plaq_ext (siteShift_injective _ hq.1) hq.2 he
    · exact plaq_ext hq.1 he hq.2
  simpa using h

/-- The plaquettes containing the link `l`. -/
def plaqsAt (l : LatticeLink d N) : Finset (LatticePlaquette d N) := univ.filter (fun q => l ∈ plaqLinks q)

theorem plaqsAt_subset (l : LatticeLink d N) : plaqsAt l ⊆ univ.biUnion (plaqsAtSlot l) := by
  intro q hq
  simp only [plaqsAt, plaqLinks, mem_filter, mem_univ, true_and, mem_image] at hq
  obtain ⟨i, hi⟩ := hq
  exact mem_biUnion.mpr ⟨i, mem_univ _, by simp [plaqsAtSlot, hi]⟩

/-- **A link lies in at most `4 d` plaquettes.** -/
theorem card_plaqsAt_le (l : LatticeLink d N) : (plaqsAt l).card ≤ 4 * d := by
  calc (plaqsAt l).card ≤ (univ.biUnion (plaqsAtSlot l)).card := card_le_card (plaqsAt_subset l)
    _ ≤ ∑ i : Fin 4, (plaqsAtSlot l i).card := card_biUnion_le
    _ ≤ ∑ _i : Fin 4, d := sum_le_sum (fun i _ => card_plaqsAtSlot_le l i)
    _ = 4 * d := by simp

theorem card_plaqLinks_le (p : LatticePlaquette d N) : (plaqLinks p).card ≤ 4 := by
  unfold plaqLinks; simpa using (card_image_le (s := (univ : Finset (Fin 4))) (f := p.boundaryLinks))

/-- Sum of `plaqsAt` over a set of links. -/
theorem card_biUnion_plaqsAt_le (S : Finset (LatticeLink d N)) : (S.biUnion plaqsAt).card ≤ 4 * d * S.card := by
  calc (S.biUnion plaqsAt).card ≤ ∑ l ∈ S, (plaqsAt l).card := card_biUnion_le
    _ ≤ ∑ _l ∈ S, 4 * d := sum_le_sum (fun l _ => card_plaqsAt_le l)
    _ = 4 * d * S.card := by rw [sum_const, smul_eq_mul, mul_comm]

/-- **The degree bound.** Every plaquette has at most `16 d` neighbours in the plaquette graph. -/
theorem plaqGraph_degree_le (p : LatticePlaquette d N) : (plaqGraph d N).degree p ≤ 16 * d := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : (plaqGraph d N).neighborFinset p ⊆ (plaqLinks p).biUnion plaqsAt := by
    intro q hq
    rw [SimpleGraph.mem_neighborFinset] at hq
    obtain ⟨l, hl⟩ := hq.2
    rw [mem_inter] at hl
    exact mem_biUnion.mpr ⟨l, hl.1, by simp [plaqsAt, hl.2]⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ 4 * d * (plaqLinks p).card := card_biUnion_plaqsAt_le _
    _ ≤ 4 * d * 4 := Nat.mul_le_mul_left _ (card_plaqLinks_le p)
    _ = 16 * d := by ring

/-! ## 3. Perimeter bounds -/

/-- **Plaquettes touching a path.** At most `4 d` per link of the path. -/
theorem card_loopPlaqs_le (C : List (PathStep d N)) : (loopPlaqs C).card ≤ 4 * d * (pathLinks C).card := by
  refine le_trans (card_le_card ?_) (card_biUnion_plaqsAt_le (pathLinks C))
  intro q hq
  simp only [loopPlaqs, mem_filter, mem_univ, true_and] at hq
  obtain ⟨l, hl⟩ := hq
  rw [mem_inter] at hl
  exact mem_biUnion.mpr ⟨l, hl.2, by simp [plaqsAt, hl.1]⟩

theorem card_pathLinks_le_length (C : List (PathStep d N)) : (pathLinks C).card ≤ C.length := by
  unfold pathLinks
  exact (List.toFinset_card_le _).trans (by simp)

theorem length_straightFwd (x : FinLatticeSites d N) (μ : Fin d) (k : ℕ) : (straightFwd x μ k).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [straightFwd, ih]

theorem length_straightBwd (x : FinLatticeSites d N) (μ : Fin d) (k : ℕ) : (straightBwd x μ k).length = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => simp [straightBwd, ih]

theorem length_rectPath (x : FinLatticeSites d N) (μ ν : Fin d) (R T : ℕ) :
    (rectPath x μ ν R T).length = 2 * (R + T) := by
  simp [rectPath, length_straightFwd, length_straightBwd]; ring

/-- **The rectangle visits at most `2 (R + T)` links.** -/
theorem card_pathLinks_rect_le (x : FinLatticeSites d N) (μ ν : Fin d) (R T : ℕ) :
    (pathLinks (rectPath x μ ν R T)).card ≤ 2 * (R + T) :=
  (card_pathLinks_le_length _).trans (length_rectPath x μ ν R T).le

/-- **The rectangle touches at most `8 d (R + T)` plaquettes.** -/
theorem card_loopPlaqs_rect_le (x : FinLatticeSites d N) (μ ν : Fin d) (R T : ℕ) :
    (loopPlaqs (rectPath x μ ν R T)).card ≤ 4 * d * (2 * (R + T)) :=
  (card_loopPlaqs_le _).trans (Nat.mul_le_mul_left _ (card_pathLinks_rect_le x μ ν R T))

/-! ## 4. Compact gauge groups: measurability, Haar probability, the explicit area law -/

section Generic

open Topology TopologicalSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n]

theorem continuous_gaugeReTr (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) : Continuous (gaugeReTr G n) := by
  unfold gaugeReTr gaugeTrace
  exact Complex.continuous_re.comp hc.matrix_trace

theorem measurable_xp (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (p : LatticePlaquette d N) :
    Measurable (xp (G := G) n p) := by
  show Measurable fun U : GaugeConnection G d N => gaugeReTr G n (U (p.boundaryLinks 0) * U (p.boundaryLinks 1) *
    (U (p.boundaryLinks 2))⁻¹ * (U (p.boundaryLinks 3))⁻¹)
  exact (continuous_gaugeReTr hc).measurable.comp
    ((((measurable_pi_apply (p.boundaryLinks 0)).mul (measurable_pi_apply (p.boundaryLinks 1))).mul
      (measurable_pi_apply (p.boundaryLinks 2)).inv).mul (measurable_pi_apply (p.boundaryLinks 3)).inv)

theorem measurable_pathHol (C : List (PathStep d N)) : Measurable (fun U : GaugeConnection G d N => pathHol U C) := by
  induction C with
  | nil => exact measurable_const
  | cons s rest ih =>
    have hs : Measurable (fun U : GaugeConnection G d N => s.hol U) := by
      by_cases h : s.fwd
      · simp only [PathStep.hol, h, ite_true]; exact measurable_pi_apply _
      · simp only [PathStep.hol, h]; exact (measurable_pi_apply _).inv
    exact hs.mul ih

theorem measurable_wilsonLoop (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (C : List (PathStep d N)) :
    Measurable (wilsonLoop (G := G) n C) :=
  (continuous_gaugeReTr hc).measurable.comp (measurable_pathHol C)

end Generic

section Haar

open TopologicalSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem isProbabilityMeasure_haarMeasure_top :
    IsProbabilityMeasure (Measure.haarMeasure (⊤ : PositiveCompacts G)) := by
  constructor
  have h := Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts G))
  rwa [PositiveCompacts.coe_top] at h

/-- Haar measure on a compact group, normalised to total mass 1. -/
abbrev haarProbability (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] : HasHaarProbability G :=
  ⟨Measure.haarMeasure ⊤, isProbabilityMeasure_haarMeasure_top⟩

end Haar

section Explicit

open TopologicalSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n]

/-- **The explicit area law on a gauge group with a left-invariant probability measure.** `16 d` bounds the degree of the
    plaquette graph and `8 d (R + T)` the number of plaquettes touching the loop. -/
theorem wilson_area_law_explicit [NeZero N] [HasHaarProbability G] [(haarG G).IsMulLeftInvariant]
    (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (hbd : ∀ g : G, |gaugeReTr G n g| ≤ n)
    (z : G) (hz : ∀ g : G, Commute z g) (hzz : z * z = 1) (hrep : HasGaugeTrace.rep (G := G) (n := n) z = -1)
    {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.exp (n * β) - 1 ≤ 1 / (4 * Real.exp (16 * d + 1) * (16 * d + 1) ^ 4))
    (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < N) (hTN : T < N) :
    ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N) ≠ 0 ∧
    |(∫ U, wilsonLoop n (rectPath x μ ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N)) /
      (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N))| ≤
      n * Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp (n * β) - 1)) ^ (min (R * T) (N * N - R * T)) := by
  have hzm : MeasurePreserving (z * ·) (haarG G) (haarG G) := measurePreserving_mul_left (haarG G) z
  have hsmall' : Real.exp (n * β) - 1 ≤
      1 / (4 * Real.exp (((16 * d : ℕ) : ℝ) + 1) * (((16 * d : ℕ) : ℝ) + 1) ^ 4) := by
    push_cast; exact hsmall
  obtain ⟨h1, h2⟩ := wilson_area_law_rect hbd (measurable_xp hc) z hz hzz hrep hzm hβ x hμν R T hR hT hRN hTN
    (measurable_wilsonLoop hc _) (Δ := 16 * d) plaqGraph_degree_le hsmall'
  refine ⟨h1, h2.trans ?_⟩
  push_cast
  have hcard : ((loopPlaqs (rectPath x μ ν R T)).card : ℝ) ≤ 4 * d * (2 * (R + T)) := by
    exact_mod_cast card_loopPlaqs_rect_le x μ ν R T
  gcongr

end Explicit

/-! ### Unitary matrices -/

instance instSecondCountableMatrix {m : Type*} [Countable m] :
    SecondCountableTopology (Matrix m m ℂ) := inferInstanceAs (SecondCountableTopology (m → m → ℂ))

/-- |Re tr A| ≤ n for a unitary n × n matrix (its entries have modulus ≤ 1). -/
theorem abs_re_trace_le_of_unitary {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    |A.trace.re| ≤ n := by
  calc |A.trace.re| ≤ ‖A.trace‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ‖A i i‖ := by unfold Matrix.trace; exact norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := sum_le_sum (fun i _ => entry_norm_bound_of_unitary hA i i)
    _ = n := by simp

/-- The unitary matrices lie in the compact box of matrices with entries of modulus ≤ 1, and form a closed set. -/
theorem isCompact_unitaryGroup (n : ℕ) : IsCompact (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hbox : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) :
      Set (Matrix (Fin n) (Fin n) ℂ)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall 0 1))
  have hcl : IsClosed (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := isClosed_unitary
  refine hbox.of_isClosed_subset hcl ?_
  intro A hA
  simp only [Set.mem_pi, Set.mem_univ, forall_const, mem_closedBall_zero_iff]
  exact fun i j => entry_norm_bound_of_unitary hA i j

/-! ### SU(2) -/

/-- SU(2), with the topology and the (Borel) measurable structure inherited from the 2 × 2 complex matrices. -/
abbrev SU2 : Type := Matrix.specialUnitaryGroup (Fin 2) ℂ

instance : IsTopologicalGroup SU2 where
  continuous_mul := by
    apply continuous_induced_rng.2
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply continuous_induced_rng.2
    exact continuous_subtype_val.star

theorem isCompact_SU2 : IsCompact (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine (isCompact_unitaryGroup 2).of_isClosed_subset ?_
    (fun A hA => (Matrix.mem_specialUnitaryGroup_iff.mp hA).1)
  have hcl : IsClosed (Matrix.unitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) := isClosed_unitary
  have hdet : IsClosed {A : Matrix (Fin 2) (Fin 2) ℂ | A.det = 1} :=
    isClosed_eq continuous_id.matrix_det continuous_const
  convert hcl.inter hdet using 1
  ext A
  simp only [SetLike.mem_coe, Matrix.mem_specialUnitaryGroup_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]

instance : CompactSpace SU2 := isCompact_iff_compactSpace.mp isCompact_SU2

instance : SecondCountableTopology SU2 :=
  inferInstanceAs (SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)))

/-- The defining representation SU(2) ⊆ M₂(ℂ). -/
instance : HasGaugeTrace SU2 2 := ⟨(Matrix.specialUnitaryGroup (Fin 2) ℂ).subtype⟩

/-- Haar measure on SU(2), normalised to a probability measure. -/
instance : HasHaarProbability SU2 := haarProbability SU2

instance : (haarG SU2).IsMulLeftInvariant := by
  show (Measure.haarMeasure ⊤).IsMulLeftInvariant; infer_instance

/-- The centre element −I of SU(2) (det(−I) = 1). -/
def negOneSU2 : SU2 :=
  ⟨-1, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨by simp [Matrix.mem_unitaryGroup_iff], by simp [Matrix.det_neg]⟩⟩

/-- **The area law for SU(2) lattice gauge theory** (Wilson action, periodic lattice (ℤ/Nℤ)^d, R × T loop in the plane
    (μ, ν)). The partition function is nonzero, and for `e^{2β} − 1 ≤ 1 / (4 e^{16d+1} (16d+1)⁴)`:
    `|⟨W_{R×T}⟩| ≤ 2 e^{2 · 4d · 2(R+T)} (√(e^{16d+1} (e^{2β} − 1)))^{min(RT, N² − RT)}`. -/
theorem wilson_area_law_SU2 [NeZero N] {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.exp (2 * β) - 1 ≤ 1 / (4 * Real.exp (16 * d + 1) * (16 * d + 1) ^ 4))
    (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < N) (hTN : T < N) :
    ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d N) ≠ 0 ∧
    |(∫ U, wilsonLoop 2 (rectPath x μ ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d N)) /
      (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d N))| ≤
      2 * Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp (2 * β) - 1)) ^ (min (R * T) (N * N - R * T)) := by
  have hc : Continuous (HasGaugeTrace.rep (G := SU2) (n := 2)) := continuous_subtype_val
  have hbd : ∀ g : SU2, |gaugeReTr SU2 2 g| ≤ (2 : ℕ) :=
    fun g => abs_re_trace_le_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
  have hz : ∀ g : SU2, Commute negOneSU2 g :=
    fun g => Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * g.val = g.val * -1 by simp)
  have hzz : negOneSU2 * negOneSU2 = 1 :=
    Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * -1 = 1 by simp)
  have hrep : HasGaugeTrace.rep (G := SU2) (n := 2) negOneSU2 = -1 := rfl
  have h := wilson_area_law_explicit hc hbd negOneSU2 hz hzz hrep hβ (by exact_mod_cast hsmall) x hμν R T hR hT hRN hTN
  exact_mod_cast h

/-! ### U(n) -/

/-- U(n), with the topology and the (Borel) measurable structure inherited from the n × n complex matrices. -/
abbrev Un (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

instance (n : ℕ) : CompactSpace (Un n) := isCompact_iff_compactSpace.mp (isCompact_unitaryGroup n)

instance (n : ℕ) : SecondCountableTopology (Un n) :=
  inferInstanceAs (SecondCountableTopology (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)))

/-- The defining representation U(n) ⊆ Mₙ(ℂ). -/
instance (n : ℕ) : HasGaugeTrace (Un n) n := ⟨(Matrix.unitaryGroup (Fin n) ℂ).subtype⟩

/-- Haar measure on U(n), normalised to a probability measure. -/
instance (n : ℕ) : HasHaarProbability (Un n) := haarProbability (Un n)

instance (n : ℕ) : (haarG (Un n)).IsMulLeftInvariant := by
  show (Measure.haarMeasure ⊤).IsMulLeftInvariant; infer_instance

/-- The centre element −I of U(n). -/
def negOneUn (n : ℕ) : Un n := ⟨-1, by simp [Matrix.mem_unitaryGroup_iff]⟩

/-- **The area law for U(n) lattice gauge theory** (Wilson action, periodic lattice (ℤ/Nℤ)^d, R × T loop in the plane
    (μ, ν)). The partition function is nonzero, and for `e^{nβ} − 1 ≤ 1 / (4 e^{16d+1} (16d+1)⁴)`:
    `|⟨W_{R×T}⟩| ≤ n e^{2 · 4d · 2(R+T)} (√(e^{16d+1} (e^{nβ} − 1)))^{min(RT, N² − RT)}`. -/
theorem wilson_area_law_Un [NeZero N] (n : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : Real.exp (n * β) - 1 ≤ 1 / (4 * Real.exp (16 * d + 1) * (16 * d + 1) ^ 4))
    (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < N) (hTN : T < N) :
    ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar (Un n) d N) ≠ 0 ∧
    |(∫ U, wilsonLoop n (rectPath x μ ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar (Un n) d N)) /
      (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar (Un n) d N))| ≤
      n * Real.exp (2 * (4 * d * (2 * (R + T)))) *
        Real.sqrt (Real.exp (16 * d + 1) * (Real.exp (n * β) - 1)) ^ (min (R * T) (N * N - R * T)) := by
  have hc : Continuous (HasGaugeTrace.rep (G := Un n) (n := n)) := continuous_subtype_val
  have hbd : ∀ g : Un n, |gaugeReTr (Un n) n g| ≤ n := fun g => abs_re_trace_le_of_unitary g.2
  have hz : ∀ g : Un n, Commute (negOneUn n) g :=
    fun g => Subtype.ext (show (-1 : Matrix (Fin n) (Fin n) ℂ) * g.val = g.val * -1 by simp)
  have hzz : negOneUn n * negOneUn n = 1 :=
    Subtype.ext (show (-1 : Matrix (Fin n) (Fin n) ℂ) * -1 = 1 by simp)
  have hrep : HasGaugeTrace.rep (G := Un n) (n := n) (negOneUn n) = -1 := rfl
  exact wilson_area_law_explicit hc hbd (negOneUn n) hz hzz hrep hβ hsmall x hμν R T hR hT hRN hTN

-- #print axioms wilson_area_law_SU2  -- [propext, Classical.choice, Quot.sound]
-- #print axioms wilson_area_law_Un  -- [propext, Classical.choice, Quot.sound]

end AreaLaw.Concrete
