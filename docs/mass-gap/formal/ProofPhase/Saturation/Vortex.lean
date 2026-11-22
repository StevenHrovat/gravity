/-
Proof phase, cycle 8, workstream 1 (c8a-saturation): saturation of the centre-vortex sheet at the area rate, for every compact
group with a central involution, whenever one plaquette's worst-case action oscillation is below the entropy threshold
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c8a-saturation/NOTE.md`, sections 2 and 3.
-/

import ProofPhase.Saturation.Sheet
import ProofPhase.Flip.Floor

/-!
# Vortex saturation from an energy–entropy balance

Setting: a compact group `G` (left-invariant Haar probability), a central `z` with `z² = 1` (for SU(2): `−1`), measurable
plaquette actions `f_p : G → ℝ`, **one per plaquette** (inhomogeneous couplings, background fields), all with **oscillation
at most `E`** (`F₀ ≤ f_p ≤ F₀ + E`), the periodic lattice `(ℤ/Nℤ)^d`, and the partition functions

  `Z = ∫ ∏_p e^{f_p(U_p)}`,   `Z_tw = ∫ ∏_p e^{f_p(z^{[p ∈ sheet]} U_p)}`   (the 't Hooft twist in the plane `(μ, ν)`).

The bound below depends on the actions only through `E`: it is uniform over every field that enters the weights.

**Theorem** (`vortex_saturation`). With `p = 1 − e^{−E}` and `q = 2(d − 1) p < 1`:

  `|Z − Z_tw| ≤ B (Z + Z_tw)`,   `B = (N^d p q^{N−1}/(1 − q))^N`,

so the flip probability `P = Z_tw/(Z + Z_tw)` satisfies `|1 − 2P| ≤ B` (`flip_saturation`): **`P → ½` at the area rate**
(`B ≈ q^{N²}` up to `e^{O(N log N)}`), the Tomboulis–Yaffe form `½ − P ≤ e^{−ρ L²}` with `ρ` close to `log(1/q)`.

**Proof.** Write `e^{f} = e^{F₀}(1 + h)` with `0 ≤ h ≤ p(1 + h)` (this is where the oscillation enters: it bounds `h`
**pointwise, for every configuration**), expand both products over plaquette sets `A`, and compare term by term. A term whose
`A` does not pin the sheet in some layer is the same in `Z` and `Z_tw`: move the sheet to that layer (`tcount_move`) and let it go
there (`tcount_cancel`), each a change of variables `U ↦ twistAt z S U` that preserves the product Haar measure. The terms that
pin the sheet in every layer are counted by `sum_surv_sheet_le`.

**What it is.** The strong-coupling vortex free energy (Muenster 1981; Tomboulis–Yaffe 1985 consume it), here as a group-blind
energy–entropy theorem: the energy is the worst-case cost `E` of a plaquette, the entropy `2(d − 1)` continuations per step. It
holds for Z₂, SU(2), U(1) and the finite groups alike in its window, which is correct: all of them confine at strong coupling.
For the Wilson action `β Re tr`, `E = 2n|β|` (`wilson_vortex_saturation`).
-/

open Finset MeasureTheory AreaLaw.Twist

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Saturation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {d N : ℕ} [NeZero N]

/-! ## 1. Objects -/

/-- The twisted plaquette holonomy: `z^{[p ∈ sheet c]} U_p`. -/
def twHol (z : G) (μ ν : Fin d) (a c : ZMod N) (U : GaugeConnection G d N) (p : LatticePlaquette d N) : G :=
  z ^ sheetE μ ν a c p * plaquetteHolonomy U p

variable (d N) in
/-- The partition function of the plaquette action `f`. -/
def Zf [HasHaarProbability G] (f : LatticePlaquette d N → G → ℝ) : ℝ :=
  ∫ U, ∏ p, Real.exp (f p (plaquetteHolonomy U p)) ∂(productHaar G d N)

variable (d N) in
/-- The twisted partition function: the sheet at layer `c` of the plane `(μ, ν)` carries the twist `z`. -/
def Ztw [HasHaarProbability G] (f : LatticePlaquette d N → G → ℝ) (z : G) (μ ν : Fin d) (a c : ZMod N) : ℝ :=
  ∫ U, ∏ p, Real.exp (f p (twHol z μ ν a c U p)) ∂(productHaar G d N)

/-- The single-plaquette activity `p = 1 − e^{−E}`. -/
def satP (E : ℝ) : ℝ := 1 - Real.exp (-E)

/-- The energy–entropy ratio `q = 2(d − 1)(1 − e^{−E})`. -/
def satQ (d : ℕ) (E : ℝ) : ℝ := 2 * ((d : ℝ) - 1) * satP E

/-- The saturation bound `B = (N^d p q^{N−1}/(1 − q))^N`. -/
def satB (d N : ℕ) (E : ℝ) : ℝ := ((N : ℝ) ^ d * satP E * (satQ d E ^ (N - 1) / (1 - satQ d E))) ^ N

/-! ## 2. Algebra of the central involution -/

theorem zpow_eq_of_even_sub {z : G} (hzz : z * z = 1) {k l : ℤ} (h : Even (k - l)) : z ^ k = z ^ l := by
  obtain ⟨r, hr⟩ := h
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzz
  have : z ^ (k - l) = 1 := by rw [hr, ← two_mul, zpow_mul, h2, one_zpow]
  calc z ^ k = z ^ (k - l) * z ^ l := by rw [← zpow_add, sub_add_cancel]
    _ = z ^ l := by rw [this, one_mul]

/-- **The sheet moves for free**, pointwise: twisting by `moveLinks c` turns the twist at layer `c` into the twist at `c + 1`. -/
theorem twHol_move {z : G} (hz : ∀ g : G, Commute z g) (hzz : z * z = 1) {μ ν : Fin d} (hμν : μ ≠ ν) (a c : ZMod N)
    (U : GaugeConnection G d N) (p : LatticePlaquette d N) :
    twHol z μ ν a c (twistAt z (moveLinks μ ν a c) U) p = twHol z μ ν a (c + 1) U p := by
  unfold twHol
  rw [plaquetteHolonomy_twistAt z hz, ← mul_assoc, ← zpow_add]
  congr 1
  apply zpow_eq_of_even_sub hzz
  rcases tcount_move a hμν c p with h | h <;> rw [h]
  · exact ⟨0, by ring⟩
  · exact ⟨sheetE μ ν a c p - sheetE μ ν a (c + 1) p, by ring⟩

/-- **The sheet lets go**, pointwise on the plaquettes of `A`, when `A` does not pin it at layer `c`. -/
theorem twHol_cancel {z : G} (hz : ∀ g : G, Commute z g) (hzz : z * z = 1) {μ ν : Fin d} (hμν : μ ≠ ν) (a c : ZMod N)
    (A : Finset (LatticePlaquette d N)) (hA : ¬ SurvLayer a hμν c A) (U : GaugeConnection G d N)
    (p : LatticePlaquette d N) (hp : p ∈ A) :
    twHol z μ ν a c (twistAt z (cancelLinks a hμν c A) U) p = plaquetteHolonomy U p := by
  unfold twHol
  rw [plaquetteHolonomy_twistAt z hz, ← mul_assoc, ← zpow_add]
  have h := zpow_eq_of_even_sub hzz (k := sheetE μ ν a c p + tcount (cancelLinks a hμν c A) (plaquettePath p)) (l := 0)
    (by rw [sub_zero]; exact tcount_cancel a hμν c A hA p hp)
  rw [h, zpow_zero, one_mul]

/-! ## 3. Measurability and the expansion -/

theorem measurable_hol (p : LatticePlaquette d N) :
    Measurable (fun U : GaugeConnection G d N => plaquetteHolonomy U p) := by
  show Measurable fun U : GaugeConnection G d N => U (p.boundaryLinks 0) * U (p.boundaryLinks 1) *
    (U (p.boundaryLinks 2))⁻¹ * (U (p.boundaryLinks 3))⁻¹
  exact (((measurable_pi_apply (p.boundaryLinks 0)).mul (measurable_pi_apply (p.boundaryLinks 1))).mul
    (measurable_pi_apply (p.boundaryLinks 2)).inv).mul (measurable_pi_apply (p.boundaryLinks 3)).inv

theorem measurable_twHol (z : G) (μ ν : Fin d) (a c : ZMod N) (p : LatticePlaquette d N) :
    Measurable (fun U : GaugeConnection G d N => twHol z μ ν a c U p) :=
  (measurable_hol p).const_mul _

/-- The normalised plaquette activity `h = e^{f − F₀} − 1`. -/
def actH (f : G → ℝ) (F0 : ℝ) (g : G) : ℝ := Real.exp (f g - F0) - 1

section Activity

variable {f : G → ℝ} {F0 E : ℝ} (hlo : ∀ g, F0 ≤ f g) (hhi : ∀ g, f g ≤ F0 + E)
include hlo

theorem actH_nonneg (g : G) : 0 ≤ actH f F0 g := by
  unfold actH; linarith [Real.one_le_exp (sub_nonneg.mpr (hlo g))]

include hhi in
theorem actH_le (g : G) : actH f F0 g ≤ Real.exp E - 1 := by
  unfold actH; have := Real.exp_le_exp.mpr (show f g - F0 ≤ E by linarith [hhi g]); linarith

include hhi in
/-- `h ≤ p (1 + h)`, `p = 1 − e^{−E}`: the worst-case oscillation bounds the activity pointwise. -/
theorem actH_le_mul (g : G) : actH f F0 g ≤ satP E * (1 + actH f F0 g) := by
  unfold actH satP
  set s := f g - F0
  have hs : s ≤ E := by simp only [s]; linarith [hhi g]
  have h1 : Real.exp s * Real.exp (-E) ≤ 1 := by
    rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith)
  nlinarith

end Activity

theorem one_add_actH (f : G → ℝ) (F0 : ℝ) (g : G) : 1 + actH f F0 g = Real.exp (-F0) * Real.exp (f g) := by
  unfold actH; rw [add_sub_cancel, ← Real.exp_add]; congr 1; ring

/-! ## 4. The comparison -/

section Main

variable [HasHaarProbability G] [(haarG G).IsMulLeftInvariant]

/-- The `A`-term of the expansion for a holonomy family `H`. -/
def termI (f : LatticePlaquette d N → G → ℝ) (F0 : ℝ) (H : GaugeConnection G d N → LatticePlaquette d N → G)
    (A : Finset (LatticePlaquette d N)) : ℝ :=
  ∫ U, ∏ p ∈ A, actH (f p) F0 (H U p) ∂(productHaar G d N)

/-- Terms are equal under a change of variables `U ↦ twistAt z S U` that maps one family to the other on `A`. -/
theorem termI_eq_of_twist {f : LatticePlaquette d N → G → ℝ} {F0 : ℝ} (z : G) (S : Finset (LatticeLink d N))
    {H1 H2 : GaugeConnection G d N → LatticePlaquette d N → G} (A : Finset (LatticePlaquette d N))
    (hH : ∀ U, ∀ p ∈ A, H1 (twistAt z S U) p = H2 U p) : termI f F0 H1 A = termI f F0 H2 A := by
  have hzm := measurePreserving_mul_left (haarG G) z
  have hzm' := measurePreserving_mul_left (haarG G) z⁻¹
  have hmp := measurePreserving_twistAt z hzm S
  have hmp' := measurePreserving_twistAt z⁻¹ hzm' S
  let e : GaugeConnection G d N ≃ᵐ GaugeConnection G d N :=
    { toFun := twistAt z S
      invFun := twistAt z⁻¹ S
      left_inv := twistAt_inv z S
      right_inv := twistAt_inv' z S
      measurable_toFun := hmp.measurable
      measurable_invFun := hmp'.measurable }
  set Φ : GaugeConnection G d N → ℝ := fun U => ∏ p ∈ A, actH (f p) F0 (H1 U p)
  have h1 : ∫ U, Φ (twistAt z S U) ∂(productHaar G d N) = ∫ U, Φ U ∂(productHaar G d N) :=
    hmp.integral_comp' (f := e) Φ
  unfold termI
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  exact (prod_congr rfl fun p hp => by rw [hH U p hp]).symm

variable {z : G} (hz : ∀ g : G, Commute z g) (hzz : z * z = 1) {μ ν : Fin d} (hμν : μ ≠ ν) (a : ZMod N)
include hz hzz hμν

theorem termI_tw_succ (f : LatticePlaquette d N → G → ℝ) (F0 : ℝ) (c : ZMod N) (A : Finset (LatticePlaquette d N)) :
    termI f F0 (twHol z μ ν a c) A = termI f F0 (twHol z μ ν a (c + 1)) A :=
  termI_eq_of_twist z (moveLinks μ ν a c) A fun U p _ => twHol_move hz hzz hμν a c U p

theorem termI_tw_add (f : LatticePlaquette d N → G → ℝ) (F0 : ℝ) (c : ZMod N) (A : Finset (LatticePlaquette d N)) :
    ∀ k : ℕ, termI f F0 (twHol z μ ν a c) A = termI f F0 (twHol z μ ν a (c + (k : ZMod N))) A
  | 0 => by simp
  | k + 1 => by
    rw [termI_tw_add f F0 c A k, termI_tw_succ hz hzz hμν a f F0 (c + (k : ZMod N)) A]
    congr 2; push_cast; ring

/-- The twisted terms do not depend on the layer of the sheet. -/
theorem termI_tw_layer (f : LatticePlaquette d N → G → ℝ) (F0 : ℝ) (c c' : ZMod N) (A : Finset (LatticePlaquette d N)) :
    termI f F0 (twHol z μ ν a c) A = termI f F0 (twHol z μ ν a c') A := by
  rw [termI_tw_add hz hzz hμν a f F0 c A (c' - c).val, ZMod.natCast_zmod_val, add_sub_cancel]

/-- **Terms that do not pin the sheet in every layer cancel.** -/
theorem termI_tw_eq (f : LatticePlaquette d N → G → ℝ) (F0 : ℝ) (c : ZMod N) (A : Finset (LatticePlaquette d N)) (hA : ¬ SurvAll a hμν A) :
    termI f F0 (twHol z μ ν a c) A = termI f F0 (fun U p => plaquetteHolonomy U p) A := by
  obtain ⟨c', hc'⟩ := not_forall.mp hA
  rw [termI_tw_layer hz hzz hμν a f F0 c c' A]
  exact termI_eq_of_twist z (cancelLinks a hμν c' A) A fun U p hp => twHol_cancel hz hzz hμν a c' A hc' U p hp

omit hz hzz hμν in
/-- The expansion of a partition function and the bound on the pinning terms, for any measurable holonomy family. -/
theorem expand_bound {f : LatticePlaquette d N → G → ℝ} (hf : ∀ p, Measurable (f p)) {F0 E : ℝ}
    (hlo : ∀ p g, F0 ≤ f p g) (hhi : ∀ p g, f p g ≤ F0 + E)
    {H : GaugeConnection G d N → LatticePlaquette d N → G} (hH : ∀ p, Measurable fun U => H U p)
    (Surv : Finset (LatticePlaquette d N) → Prop) {B : ℝ}
    (hcomb : ∀ U, ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter Surv, ∏ p ∈ A, actH (f p) F0 (H U p) ≤
      B * ∏ p, (1 + actH (f p) F0 (H U p))) :
    0 < ∫ U, ∏ p, Real.exp (f p (H U p)) ∂(productHaar G d N) ∧
    Real.exp (-F0) ^ Fintype.card (LatticePlaquette d N) * ∫ U, ∏ p, Real.exp (f p (H U p)) ∂(productHaar G d N) =
      ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset, termI f F0 H A ∧
    (∀ A, 0 ≤ termI f F0 H A) ∧
    ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter Surv, termI f F0 H A ≤
      B * (Real.exp (-F0) ^ Fintype.card (LatticePlaquette d N) *
        ∫ U, ∏ p, Real.exp (f p (H U p)) ∂(productHaar G d N)) := by
  set μP := productHaar G d N
  set K := Real.exp (-F0) ^ Fintype.card (LatticePlaquette d N) with hK
  have mh : ∀ p, Measurable fun U => actH (f p) F0 (H U p) := fun p =>
    ((((hf p).comp (hH p)).sub_const F0).exp).sub_const 1
  have mprod : ∀ A : Finset (LatticePlaquette d N), Measurable fun U => ∏ p ∈ A, actH (f p) F0 (H U p) :=
    fun A => Finset.measurable_prod _ fun p _ => mh p
  have h0 : ∀ (A : Finset (LatticePlaquette d N)) U, 0 ≤ ∏ p ∈ A, actH (f p) F0 (H U p) :=
    fun A U => prod_nonneg fun p _ => actH_nonneg (hlo p) _
  have hM : ∀ (A : Finset (LatticePlaquette d N)) U, ∏ p ∈ A, actH (f p) F0 (H U p) ≤ (Real.exp E - 1) ^ A.card :=
    fun A U => by
      rw [← prod_const]; exact prod_le_prod₀ (fun p _ => actH_nonneg (hlo p) _) (fun p _ => actH_le (hlo p) (hhi p) _)
  have intA : ∀ A : Finset (LatticePlaquette d N), Integrable (fun U => ∏ p ∈ A, actH (f p) F0 (H U p)) μP := fun A =>
    Integrable.of_bound (mprod A).aestronglyMeasurable ((Real.exp E - 1) ^ A.card) (Filter.Eventually.of_forall fun U => by
      rw [Real.norm_of_nonneg (h0 A U)]; exact hM A U)
  have hD : ∀ U, ∏ p, (1 + actH (f p) F0 (H U p)) =
      ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset, ∏ p ∈ A, actH (f p) F0 (H U p) := fun U => prod_one_add _
  have hW : ∀ U, ∏ p, (1 + actH (f p) F0 (H U p)) = K * ∏ p, Real.exp (f p (H U p)) := fun U => by
    simp_rw [one_add_actH]; rw [prod_mul_distrib, prod_const, card_univ]
  have intD : Integrable (fun U => ∏ p, (1 + actH (f p) F0 (H U p))) μP := by
    simp_rw [hD]; exact integrable_finsetSum _ fun A _ => intA A
  have hexpand : K * ∫ U, ∏ p, Real.exp (f p (H U p)) ∂μP =
      ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset, termI f F0 H A := by
    unfold termI
    rw [← integral_const_mul, ← integral_finsetSum _ fun A _ => intA A]
    congr 1; funext U; rw [← hW U, hD U]
  have hK0 : 0 < K := by positivity
  refine ⟨?_, hexpand, fun A => integral_nonneg fun U => h0 A U, ?_⟩
  · -- positivity: the empty set contributes `1`
    have hge : ∀ U, (1 : ℝ) ≤ ∏ p, (1 + actH (f p) F0 (H U p)) := fun U =>
      one_le_prod₀ fun p _ => by linarith [actH_nonneg (hlo p) (H U p)]
    have h1 : (1 : ℝ) ≤ ∫ U, ∏ p, (1 + actH (f p) F0 (H U p)) ∂μP := by
      have := integral_mono (integrable_const (1 : ℝ)) intD hge
      simpa using this
    have h2 : ∫ U, ∏ p, (1 + actH (f p) F0 (H U p)) ∂μP = K * ∫ U, ∏ p, Real.exp (f p (H U p)) ∂μP := by
      rw [← integral_const_mul]; congr 1; funext U; exact hW U
    rw [h2] at h1
    by_contra hneg
    have hle : ∫ U, ∏ p, Real.exp (f p (H U p)) ∂μP ≤ 0 := not_lt.mp hneg
    nlinarith
  · have hsum : ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter Surv, termI f F0 H A =
        ∫ U, ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter Surv, ∏ p ∈ A, actH (f p) F0 (H U p) ∂μP := by
      unfold termI; rw [integral_finsetSum _ fun A _ => intA A]
    rw [hsum]
    calc ∫ U, ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter Surv, ∏ p ∈ A, actH (f p) F0 (H U p) ∂μP
        ≤ ∫ U, B * ∏ p, (1 + actH (f p) F0 (H U p)) ∂μP :=
          integral_mono (integrable_finsetSum _ fun A _ => intA A) (intD.const_mul B) hcomb
      _ = B * (K * ∫ U, ∏ p, Real.exp (f p (H U p)) ∂μP) := by
          rw [integral_const_mul]; congr 1; rw [← integral_const_mul]
          exact integral_congr_ae (Filter.Eventually.of_forall hW)

/-- **Vortex saturation from an energy–entropy balance** (S). For a central involution `z`, a measurable plaquette action
    of oscillation at most `E` and `q = 2(d − 1)(1 − e^{−E}) < 1`, on `(ℤ/Nℤ)^d`, `N ≥ 2`, any directions `μ ≠ ν`, slice `a`,
    layer `c`: both partition functions are positive and `|Z − Z_tw| ≤ B (Z + Z_tw)`, `B = (N^d p q^{N−1}/(1 − q))^N`. -/
theorem vortex_saturation (f : LatticePlaquette d N → G → ℝ) (hf : ∀ p, Measurable (f p)) {F0 E : ℝ}
    (hlo : ∀ p g, F0 ≤ f p g) (hhi : ∀ p g, f p g ≤ F0 + E) (hN : 1 < N) (c : ZMod N) (hq : satQ d E < 1) :
    0 < Zf d N f ∧ 0 < Ztw d N f z μ ν a c ∧
      |Zf d N f - Ztw d N f z μ ν a c| ≤ satB d N E * (Zf d N f + Ztw d N f z μ ν a c) := by
  have hE : 0 ≤ E := by linarith [hlo (mkPlaq 0 ν μ hμν) 1, hhi (mkPlaq 0 ν μ hμν) 1]
  have hpr0 : 0 ≤ satP E := by
    unfold satP; linarith [Real.exp_le_one_iff.mpr (show -E ≤ 0 by linarith)]
  have hd : 1 ≤ d := Fin.pos ν
  have hcardM : (Fintype.card (Move d ν) : ℝ) * satP E = satQ d E := by
    rw [card_move]; push_cast [Nat.cast_sub hd]; unfold satQ; ring
  have hq' : (Fintype.card (Move d ν) : ℝ) * satP E < 1 := hcardM ▸ hq
  have hcardV : (Fintype.card (FinLatticeSites d N) : ℝ) = (N : ℝ) ^ d := by
    simp [FinLatticeSites, Fintype.card_fun, ZMod.card]
  have hB : (Fintype.card (FinLatticeSites d N) * satP E *
      (((Fintype.card (Move d ν) : ℝ) * satP E) ^ (N - 1) / (1 - (Fintype.card (Move d ν) : ℝ) * satP E))) ^ N =
      satB d N E := by
    rw [hcardM, hcardV]; rfl
  have hcomb : ∀ (H : GaugeConnection G d N → LatticePlaquette d N → G) U,
      ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter (SurvAll a hμν), ∏ p ∈ A, actH (f p) F0 (H U p) ≤
        satB d N E * ∏ p, (1 + actH (f p) F0 (H U p)) := fun H U => by
    rw [← hB]
    exact sum_surv_sheet_le a hN hμν (fun p => actH (f p) F0 (H U p)) hpr0 hq' (fun p => actH_nonneg (hlo p) _)
      (fun p => actH_le_mul (hlo p) (hhi p) _)
  obtain ⟨hZ0, hZe, hZn, hZb⟩ := expand_bound hf hlo hhi (H := fun U p => plaquetteHolonomy U p) measurable_hol
    (SurvAll a hμν) (hcomb _)
  obtain ⟨hT0, hTe, hTn, hTb⟩ := expand_bound hf hlo hhi (H := twHol z μ ν a c) (measurable_twHol z μ ν a c)
    (SurvAll a hμν) (hcomb _)
  refine ⟨hZ0, hT0, ?_⟩
  set K := Real.exp (-F0) ^ Fintype.card (LatticePlaquette d N) with hK
  have hK0 : 0 < K := by positivity
  set P := (univ : Finset (LatticePlaquette d N)).powerset
  have hsplit : ∀ g : Finset (LatticePlaquette d N) → ℝ,
      ∑ A ∈ P, g A = ∑ A ∈ P.filter (SurvAll a hμν), g A + ∑ A ∈ P.filter (fun A => ¬ SurvAll a hμν A), g A :=
    fun g => (sum_filter_add_sum_filter_not P _ g).symm
  have hdiff : K * (Zf d N f - Ztw d N f z μ ν a c) =
      ∑ A ∈ P.filter (SurvAll a hμν), (termI f F0 (fun U p => plaquetteHolonomy U p) A -
        termI f F0 (twHol z μ ν a c) A) := by
    have e1 : K * Zf d N f = ∑ A ∈ P, termI f F0 (fun U p => plaquetteHolonomy U p) A := hZe
    have e2 : K * Ztw d N f z μ ν a c = ∑ A ∈ P, termI f F0 (twHol z μ ν a c) A := hTe
    have hnot : ∑ A ∈ P.filter (fun A => ¬ SurvAll a hμν A), termI f F0 (fun U p => plaquetteHolonomy U p) A =
        ∑ A ∈ P.filter (fun A => ¬ SurvAll a hμν A), termI f F0 (twHol z μ ν a c) A :=
      sum_congr rfl fun A hA => (termI_tw_eq hz hzz hμν a f F0 c A (mem_filter.mp hA).2).symm
    rw [mul_sub, e1, e2, hsplit (termI f F0 (fun U p => plaquetteHolonomy U p)), hsplit (termI f F0 (twHol z μ ν a c)),
      hnot, sum_sub_distrib]
    ring
  have habs : K * |Zf d N f - Ztw d N f z μ ν a c| ≤ K * (satB d N E * (Zf d N f + Ztw d N f z μ ν a c)) := by
    rw [← abs_of_pos hK0, ← abs_mul, abs_of_pos hK0, hdiff]
    calc |∑ A ∈ P.filter (SurvAll a hμν), (termI f F0 (fun U p => plaquetteHolonomy U p) A -
          termI f F0 (twHol z μ ν a c) A)|
        ≤ ∑ A ∈ P.filter (SurvAll a hμν), |termI f F0 (fun U p => plaquetteHolonomy U p) A -
            termI f F0 (twHol z μ ν a c) A| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ A ∈ P.filter (SurvAll a hμν), (termI f F0 (fun U p => plaquetteHolonomy U p) A +
            termI f F0 (twHol z μ ν a c) A) := by
          refine sum_le_sum fun A _ => ?_
          rw [abs_le]; constructor <;> linarith [hZn A, hTn A]
      _ = ∑ A ∈ P.filter (SurvAll a hμν), termI f F0 (fun U p => plaquetteHolonomy U p) A +
            ∑ A ∈ P.filter (SurvAll a hμν), termI f F0 (twHol z μ ν a c) A := sum_add_distrib
      _ ≤ satB d N E * (K * Zf d N f) + satB d N E * (K * Ztw d N f z μ ν a c) := add_le_add hZb hTb
      _ = K * (satB d N E * (Zf d N f + Ztw d N f z μ ν a c)) := by ring
  exact le_of_mul_le_mul_left habs hK0

/-- **Flip saturation** (S): the flip probability `P = Z_tw/(Z_tw + Z)` of c6a satisfies `|1 − 2P| ≤ B`. -/
theorem flip_saturation (f : LatticePlaquette d N → G → ℝ) (hf : ∀ p, Measurable (f p)) {F0 E : ℝ}
    (hlo : ∀ p g, F0 ≤ f p g) (hhi : ∀ p g, f p g ≤ F0 + E) (hN : 1 < N) (c : ZMod N) (hq : satQ d E < 1) :
    |1 - 2 * ProofPhase.Flip.flipP (Zf d N f) (Ztw d N f z μ ν a c)| ≤ satB d N E := by
  obtain ⟨hZ, hT, hb⟩ := vortex_saturation hz hzz hμν a f hf hlo hhi hN c hq
  rw [ProofPhase.Flip.one_sub_two_flipP (by linarith), abs_div, abs_of_pos (by linarith : 0 < Zf d N f + _),
    div_le_iff₀ (by linarith)]
  exact hb

end Main

end ProofPhase.Saturation
