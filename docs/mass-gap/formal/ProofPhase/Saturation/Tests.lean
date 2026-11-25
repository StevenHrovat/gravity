/-
Proof phase, cycle 8, workstream 1 (c8a-saturation): the Wilson-action instances of vortex saturation (Z₂, SU(2), U(1)) and
the formal unit tests (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c8a-saturation/NOTE.md`, sections 3 and 6.
-/

import ProofPhase.Saturation.EnergyEntropy
import ProofPhase.Centre.Z2Wilson

/-!
# Instances and unit tests

* `wilson_vortex_saturation`: the Wilson action `β Re tr` of any compact group with a central involution, `E = 2n|β|`; the
  window is `twistQ d n β < 1` (the repo's centre-twist area-law window), i.e. `2n|β| < log(K/(K − 1))` (`wilson_window`).
* `z2_vortex_saturation`, `su2_vortex_saturation`, `u1_vortex_saturation`: Z₂ (`|β| < log(6/5)/2` in `d = 4`), SU(2)
  (`|β| < log(6/5)/4`, the repo's `SU2` and `negOneSU2`), compact U(1) (confines at strong coupling, correctly).
* Unit tests:
  - **weak coupling** (`not_window_weak`): for `2n|β| ≥ log(K/(K − 1))` the hypothesis fails, for every group: the theorem is
    silent on deconfined Z₂, on 2I at weak coupling, on the U(1) photon. Silence is the correct verdict for all three.
  - **no centre layer** (`ztw_trivial`, `flipP_trivial`, `real_no_central_involution`): the twist by the trivial element is the
    identity, `P = ½` exactly in every phase (the photon's Coulomb phase included); the non-compact photon has no other central
    involution. So `P = ½` by itself carries no information; the content needs `z ≠ 1`.
  - **mixture** (`mixture_saturation`): saturation of each component gives saturation of the mixture (with the same `B`), while
    the one-box criterion fails for two coexisting phases (c7c): saturation must not imply the gap, and does not.
  - **product** (`flipP_product`): if the twist acts on one factor only (SU(2)×U(1), twist `(−1, 1)`), the flip probability is
    that of the factor: saturated by SU(2), blind to the photon, which keeps the product gapless (c7c, `not_fineOneBox_...`).
-/

open Finset MeasureTheory AreaLaw.Twist AreaLaw.Concrete AreaLaw.ConcreteSUn ProofPhase.Flip

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Saturation

variable {d N : ℕ} [NeZero N]

/-! ## 1. The Wilson action -/

section Wilson

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] [(haarG G).IsMulLeftInvariant] {n : ℕ} [HasGaugeTrace G n]

variable (G) in
/-- The Wilson plaquette action `β Re tr`, the same at every plaquette. -/
def wilsonAct (n : ℕ) [HasGaugeTrace G n] (β : ℝ) : LatticePlaquette d N → G → ℝ := fun _ g => β * gaugeReTr G n g

theorem satQ_wilson (n : ℕ) (β : ℝ) : satQ d (2 * n * |β|) = twistQ d n β := rfl

/-- **Vortex saturation for the Wilson action** (S): `E = 2n|β|`, window `twistQ d n β < 1`. -/
theorem wilson_vortex_saturation (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (hbd : ∀ g : G, |gaugeReTr G n g| ≤ n) {z : G} (hz : ∀ g : G, Commute z g) (hzz : z * z = 1)
    {μ ν : Fin d} (hμν : μ ≠ ν) (a c : ZMod N) {β : ℝ} (hN : 1 < N) (hq : twistQ d n β < 1) :
    0 < Zf d N (wilsonAct G n β) ∧ 0 < Ztw d N (wilsonAct G n β) z μ ν a c ∧
      |1 - 2 * flipP (Zf d N (wilsonAct G n β)) (Ztw d N (wilsonAct G n β) z μ ν a c)| ≤ satB d N (2 * n * |β|) := by
  have hf : ∀ _ : LatticePlaquette d N, Measurable (fun g : G => β * gaugeReTr G n g) :=
    fun _ => (continuous_gaugeReTr hc).measurable.const_mul β
  have hab : ∀ g : G, |β * gaugeReTr G n g| ≤ n * |β| := fun g => by
    rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hbd g) (abs_nonneg β)
  have hlo : ∀ (_ : LatticePlaquette d N) (g : G), -(n * |β|) ≤ β * gaugeReTr G n g := fun _ g => (abs_le.mp (hab g)).1
  have hhi : ∀ (_ : LatticePlaquette d N) (g : G), β * gaugeReTr G n g ≤ -(n * |β|) + 2 * n * |β| := fun _ g => by
    linarith [(abs_le.mp (hab g)).2]
  have hq' : satQ d (2 * n * |β|) < 1 := hq
  obtain ⟨h1, h2, -⟩ := vortex_saturation hz hzz hμν a _ hf hlo hhi hN c hq'
  exact ⟨h1, h2, flip_saturation hz hzz hμν a _ hf hlo hhi hN c hq'⟩

/-- The window in cost form: `twistQ d n β < 1 ⇔ 2n|β| < log(K/(K − 1))`, `K = 2(d − 1)`. -/
theorem wilson_window (hd : 2 ≤ d) (n : ℕ) (β : ℝ) :
    twistQ d n β < 1 ↔ 2 * n * |β| < Real.log (2 * ((d : ℝ) - 1) / (2 * ((d : ℝ) - 1) - 1)) := by
  rw [← satQ_wilson]; exact satQ_lt_one_iff hd _

/-- **Unit test, weak coupling: the theorem is silent** once one plaquette's worst-case cost reaches the entropy threshold. -/
theorem not_window_weak (hd : 2 ≤ d) {E : ℝ} (hE : Real.log (2 * ((d : ℝ) - 1) / (2 * ((d : ℝ) - 1) - 1)) ≤ E) :
    ¬ satQ d E < 1 := by
  rw [satQ_lt_one_iff hd]; exact not_lt.mpr hE

end Wilson

/-! ## 2. Z₂, SU(2), U(1) -/

open ProofPhase.Centre in
/-- **Z₂ gauge theory, confined (strong coupling)**: the vortex sheet saturates at the area rate. In `d = 4` the window is
    `|β| < log(6/5)/2 ≈ 0.091` (`β` multiplies `±1`); the transition is at `β ≈ 0.44`, so this is deep in the confined phase. -/
theorem z2_vortex_saturation {μ ν : Fin d} (hμν : μ ≠ ν) (a c : ZMod N) {β : ℝ} (hN : 1 < N) (hq : twistQ d 1 β < 1) :
    |1 - 2 * flipP (Zf d N (wilsonAct Z2 1 β)) (Ztw d N (wilsonAct Z2 1 β) Z2.neg μ ν a c)|
      ≤ satB d N (2 * (1 : ℕ) * |β|) := by
  have hc : Continuous (HasGaugeTrace.rep (G := Z2) (n := 1)) := continuous_of_discreteTopology
  have hbd : ∀ g : Z2, |gaugeReTr Z2 1 g| ≤ (1 : ℕ) := fun g => by
    rw [Z2.gaugeReTr_eq]; rcases ProofPhase.Centre.sgn_eq g.val with h | h <;> rw [h] <;> norm_num
  have hz : ∀ g : Z2, Commute Z2.neg g := fun g => Z2.comm _ _
  have hzz : Z2.neg * Z2.neg = 1 := Z2.ext' (by simp [Z2.mul_val, Z2.neg, Z2.one_val])
  exact (wilson_vortex_saturation hc hbd hz hzz hμν a c hN hq).2.2

/-- **SU(2), strong coupling** (the repo's `SU2`, centre `−I`): window `|β| < log(6/5)/4 ≈ 0.046` in `d = 4` (`β` multiplies
    `Re tr`; `β_std = 2β < 0.091`). -/
theorem su2_vortex_saturation {μ ν : Fin d} (hμν : μ ≠ ν) (a c : ZMod N) {β : ℝ} (hN : 1 < N) (hq : twistQ d 2 β < 1) :
    |1 - 2 * flipP (Zf d N (wilsonAct SU2 2 β))
        (Ztw d N (wilsonAct SU2 2 β) negOneSU2 μ ν a c)| ≤ satB d N (2 * (2 : ℕ) * |β|) := by
  have hc : Continuous (HasGaugeTrace.rep (G := SU2) (n := 2)) := continuous_subtype_val
  have hbd : ∀ g : SU2, |gaugeReTr SU2 2 g| ≤ (2 : ℕ) :=
    fun g => abs_re_trace_le_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
  have hz : ∀ g : SU2, Commute negOneSU2 g :=
    fun g => Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * g.val = g.val * -1 by simp)
  have hzz : negOneSU2 * negOneSU2 = 1 :=
    Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * -1 = 1 by simp)
  exact (wilson_vortex_saturation hc hbd hz hzz hμν a c hN hq).2.2

/-- **Compact U(1), strong coupling**: saturates too (U(1) confines at strong coupling); its Coulomb phase lies outside the
    window (`not_window_weak`). -/
theorem u1_vortex_saturation {μ ν : Fin d} (hμν : μ ≠ ν) (a c : ZMod N) {β : ℝ} (hN : 1 < N) (hq : twistQ d 1 β < 1) :
    |1 - 2 * flipP (Zf d N (wilsonAct (Un 1) 1 β))
        (Ztw d N (wilsonAct (Un 1) 1 β) (negOneUn 1) μ ν a c)| ≤ satB d N (2 * (1 : ℕ) * |β|) := by
  have hc : Continuous (HasGaugeTrace.rep (G := Un 1) (n := 1)) := continuous_subtype_val
  have hbd : ∀ g : Un 1, |gaugeReTr (Un 1) 1 g| ≤ (1 : ℕ) := fun g => abs_re_trace_le_of_unitary g.2
  have hz : ∀ g : Un 1, Commute (negOneUn 1) g :=
    fun g => Subtype.ext (show (-1 : Matrix (Fin 1) (Fin 1) ℂ) * g.val = g.val * -1 by simp)
  have hzz : negOneUn 1 * negOneUn 1 = 1 :=
    Subtype.ext (show (-1 : Matrix (Fin 1) (Fin 1) ℂ) * -1 = 1 by simp)
  exact (wilson_vortex_saturation hc hbd hz hzz hμν a c hN hq).2.2

open ProofPhase.Centre in
/-- **Quenched centre saturation: Z₂ with an arbitrary coupling field** (S). For any plaquette couplings `J_p` with
    `|J_p| ≤ J̄` (any signs; for example the effective centre couplings `J_p(V)` of one fixed adjoint background `V` in the
    plaquette representation of c7b) the bound holds with `E = 2J̄`, **uniformly in the field**: the sup-norm activity makes
    the energy–entropy balance worst-case over everything that enters the weights. -/
theorem z2_background_saturation {μ ν : Fin d} (hμν : μ ≠ ν) (a c : ZMod N) (J : LatticePlaquette d N → ℝ) {Jbar : ℝ}
    (hJ : ∀ p, |J p| ≤ Jbar) (hN : 1 < N) (hq : satQ d (2 * Jbar) < 1) :
    |1 - 2 * flipP (Zf d N (fun p (g : Z2) => J p * gaugeReTr Z2 1 g))
        (Ztw d N (fun p (g : Z2) => J p * gaugeReTr Z2 1 g) Z2.neg μ ν a c)| ≤ satB d N (2 * Jbar) := by
  have hz : ∀ g : Z2, Commute Z2.neg g := fun g => Z2.comm _ _
  have hzz : Z2.neg * Z2.neg = 1 := Z2.ext' (by simp [Z2.mul_val, Z2.neg, Z2.one_val])
  have hbd : ∀ g : Z2, |gaugeReTr Z2 1 g| ≤ 1 := fun g => by
    rw [Z2.gaugeReTr_eq]; rcases ProofPhase.Centre.sgn_eq g.val with h | h <;> rw [h] <;> norm_num
  have hab : ∀ p (g : Z2), |J p * gaugeReTr Z2 1 g| ≤ Jbar := fun p g => by
    rw [abs_mul]
    calc |J p| * |gaugeReTr Z2 1 g| ≤ Jbar * 1 :=
          mul_le_mul (hJ p) (hbd g) (abs_nonneg _) ((abs_nonneg _).trans (hJ p))
      _ = Jbar := mul_one _
  have hf : ∀ p, Measurable (fun g : Z2 => J p * gaugeReTr Z2 1 g) := fun p => Measurable.of_discrete
  exact flip_saturation hz hzz hμν a _ hf (F0 := -Jbar) (E := 2 * Jbar) (fun p g => (abs_le.mp (hab p g)).1)
    (fun p g => by linarith [(abs_le.mp (hab p g)).2]) hN c hq

/-! ## 3. Unit tests: no centre layer, mixture, product -/

section Trivial

variable {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G]

/-- The twist by the trivial element is no twist. -/
theorem ztw_trivial (f : LatticePlaquette d N → G → ℝ) (μ ν : Fin d) (a c : ZMod N) : Ztw d N f 1 μ ν a c = Zf d N f := by
  simp [Ztw, Zf, twHol]

/-- **Unit test, no centre layer**: with the trivial twist `P = ½` exactly, in every phase. -/
theorem flipP_trivial {Z : ℝ} (hZ : Z ≠ 0) : flipP Z Z = 1 / 2 := by
  unfold flipP; field_simp; ring

/-- The non-compact photon (`ℝ`) has no central involution but the identity. -/
theorem real_no_central_involution (z : Multiplicative ℝ) (h : z * z = 1) : z = 1 := by
  have h' : Multiplicative.toAdd z + Multiplicative.toAdd z = 0 := by
    rw [← toAdd_mul, h, toAdd_one]
  have : Multiplicative.toAdd z = 0 := by linarith
  rw [← ofAdd_toAdd z, this, ofAdd_zero]

end Trivial

/-- **Unit test, mixture**: saturation of the components gives saturation of the mixture, with the same bound. -/
theorem mixture_saturation {Z₁ Z₂ T₁ T₂ B : ℝ} (h₁ : |Z₁ - T₁| ≤ B * (Z₁ + T₁)) (h₂ : |Z₂ - T₂| ≤ B * (Z₂ + T₂)) :
    |(Z₁ + Z₂) - (T₁ + T₂)| ≤ B * ((Z₁ + Z₂) + (T₁ + T₂)) := by
  calc |(Z₁ + Z₂) - (T₁ + T₂)| = |(Z₁ - T₁) + (Z₂ - T₂)| := by ring_nf
    _ ≤ |Z₁ - T₁| + |Z₂ - T₂| := abs_add_le _ _
    _ ≤ B * (Z₁ + T₁) + B * (Z₂ + T₂) := add_le_add h₁ h₂
    _ = B * ((Z₁ + Z₂) + (T₁ + T₂)) := by ring

/-- **Unit test, product**: a twist acting on one factor sees only that factor. -/
theorem flipP_product {Z T W : ℝ} (hW : W ≠ 0) : flipP (Z * W) (T * W) = flipP Z T := by
  unfold flipP
  rw [show T * W + Z * W = (T + Z) * W by ring, mul_div_mul_right _ _ hW]

end ProofPhase.Saturation
