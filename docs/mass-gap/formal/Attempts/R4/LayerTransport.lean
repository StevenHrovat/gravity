/-
Round 4, attempt r4-layer, 2026-11-21. Released under Apache 2.0.

# The act is conserved per layer: exact transport of the flux sector under a centre-respecting blocking; T38 in full

Note: `docs/mass-gap/weak-coupling/attempts/r4-layer/NOTE.md`, sections 2 and 3.

**Transport (section 1).** A blocking is a measurable map `B` from fine to coarse configurations (a random blocking is a
deterministic one on the fine configurations together with the noise variables). It *respects the centre* if `B ∘ Ω̂_f = Ω̂_c ∘ B`.
The blocked layer of a fine ensemble `μ` is its image `B_* μ`; "the blocked action" is, by definition, `−log` of the density of
`B_* μ` (one image per fine ensemble: periodic, twisted, or one electric-flux sector).
Proved:
* `sector_partition_conserved`, `act_conserved_per_layer`: the sector partition functions are conserved, `Z_e(coarse) = Z_e(fine)`,
  hence the electric free energy `F_e = −log(Z₁/Z₀)` and the act number `z = L·F_e/T` are conserved when lengths are measured in
  the layer's own units (`L ↦ L/b`, `T ↦ T/b`): **the act is conserved per layer**.
* `map_centre_invariant`, `correlator_conserved`, `lift_charged`: the blocked layer inherits the centre symmetry; coarse correlators
  are fine correlators of the lifted observables; a coarse state of centre charge `ε` lifts to a fine state of the same charge. So
  the coarse flux sector is a subspace of the fine flux sector (`lift_mem_sec`).
* `blocked_flux_decay`: for a blocking that does not change the time step, the correlators of lifted coarse flux states decay at
  least like the fine flux sector, `e^{−E_e n}` relative to the fine vacuum growth. This half is one-sided: the rate a coarse
  observer sees is `≥ E_e`, with equality exactly when the coarse flux states overlap the fine flux ground state (not formalised).

**T38 in full (section 2), finite configuration spaces.** The fine layer is reflection positive in the form of
`Positivity.Abstract` (weight `v(p) w(p,a) w(p,b)` on plane × positive half × reflected negative half). A blocking that *gates
the coarse plane through the fine plane* (the coarse plane variables `c` are drawn from the fine plane `p` alone, `K₀(p, c)`; the
coarse positive variables `y` from the fine plane, the fine positive half and `c`, `K₊(p, a, c, y)`; the negative ones by the same
kernel from the mirror) produces a coarse layer that is reflection positive for **every** coarse observable `F(c, y)` of the closed
coarse positive half, the coarse plane included (`layer_rp`, `coarseForm_eq`). This extends `Attempts.R3.DmpHost.gated_rp`, which
covered only observables of the open positive half. The condition cannot be dropped: `straddle_breaks_rp` is an explicit RP fine
layer and a reflection-covariant blocking whose coarse plane variable is drawn from both halves, with a negative coarse RP form.
-/

import Attempts.R4.LayerSector

open MeasureTheory

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.R4.Layer

/-! ## 1. Transport -/

section Transport

variable {Ωf Ωc : Type*} [MeasurableSpace Ωf] [MeasurableSpace Ωc]

/-- `ψ` has centre charge `ε` under the map `σ`. -/
def IsCharged (σ : Ωc → Ωc) (ε : ℝ) (ψ : Ωc → ℝ) : Prop := ∀ x, ψ (σ x) = ε * ψ x

/-- **A centre-respecting blocking preserves the centre charge:** a coarse state of charge `ε` lifts to a fine state of charge `ε`. -/
theorem lift_charged {B : Ωf → Ωc} {σf : Ωf → Ωf} {σc : Ωc → Ωc} (hB : ∀ x, B (σf x) = σc (B x)) {ε : ℝ} {ψ : Ωc → ℝ}
    (hψ : IsCharged σc ε ψ) : ∀ x, ψ (B (σf x)) = ε * ψ (B x) := fun x => by rw [hB, hψ]

/-- **The blocked layer inherits the centre symmetry.** -/
theorem map_centre_invariant {B : Ωf → Ωc} (hBm : Measurable B) {σf : Ωf → Ωf} {σc : Ωc → Ωc} (hσf : Measurable σf)
    (hσc : Measurable σc) (hB : ∀ x, B (σf x) = σc (B x)) {μ : Measure Ωf} (hμ : μ.map σf = μ) :
    (μ.map B).map σc = μ.map B := by
  rw [Measure.map_map hσc hBm]
  have : σc ∘ B = B ∘ σf := funext fun x => (hB x).symm
  rw [this, ← Measure.map_map hBm hσf, hμ]

/-- **Coarse correlators are fine correlators of the lifted observables.** -/
theorem correlator_conserved {B : Ωf → Ωc} (hBm : Measurable B) (μ : Measure Ωf) {F G : Ωc → ℝ}
    (hF : Measurable F) (hG : Measurable G) :
    ∫ y, F y * G y ∂(μ.map B) = ∫ x, F (B x) * G (B x) ∂μ :=
  integral_map hBm.aemeasurable (hF.mul hG).aestronglyMeasurable

/-- The partition function `Z = μ(Ω)` (as a real number). -/
def partition (μ : Measure Ωf) : ℝ := (μ Set.univ).toReal

theorem partition_map {B : Ωf → Ωc} (hBm : Measurable B) (μ : Measure Ωf) : partition (μ.map B) = partition μ := by
  unfold partition; rw [Measure.map_apply hBm MeasurableSet.univ, Set.preimage_univ]

/-- The electric-flux partition functions from the periodic and the twisted ensembles: `Z_e = (Z + ε Z_tw)/2`. -/
def sectorPartition (μ μtw : Measure Ωf) (ε : ℝ) : ℝ := (partition μ + ε * partition μtw) / 2

/-- **The sector partition functions are conserved by blocking.** -/
theorem sector_partition_conserved {B : Ωf → Ωc} (hBm : Measurable B) (μ μtw : Measure Ωf) (ε : ℝ) :
    sectorPartition (μ.map B) (μtw.map B) ε = sectorPartition μ μtw ε := by
  unfold sectorPartition; rw [partition_map hBm, partition_map hBm]

/-- The act number `z = L · F_e / T`, `F_e = −log(Z₁/Z₀)` (for a long box `F_e ≈ E_e T`, so `z ≈ E_e L`). -/
def actNumber (L T : ℝ) (μ μtw : Measure Ωf) : ℝ :=
  L * (-Real.log (sectorPartition μ μtw (-1) / sectorPartition μ μtw 1)) / T

/-- **The act is conserved per layer.** A blocking by the factor `b` maps the box of side `L` and time extent `T` (fine units) to
    the box of side `L/b` and time extent `T/b` (coarse units). The flux sector partition functions are carried over unchanged, so
    the electric free energy and the act number are the same on both layers:
    `z(L/b, T/b; blocked layer) = z(L, T; fine layer)`, the scout's `z(2L; S) = z(L; S_eff)` for `b = 2`.
    What is conserved is the pair of sector partition functions (equivalently `Z` and `Z_tw`); the blocked layer is the image of the
    fine ensembles, and nothing here compares it with the fine action on the same box. -/
theorem act_conserved_per_layer {B : Ωf → Ωc} (hBm : Measurable B) (μ μtw : Measure Ωf) {b : ℝ} (hb : b ≠ 0) (L T : ℝ) :
    actNumber (L / b) (T / b) (μ.map B) (μtw.map B) = actNumber L T μ μtw := by
  unfold actNumber
  rw [sector_partition_conserved hBm, sector_partition_conserved hBm, div_mul_eq_mul_div, div_div_div_cancel_right₀ hb]

/-- **The coarse flux sector lies in the fine flux sector.** For the fine transfer operator with centre symmetry `c` and a
    measurable centre-respecting blocking `B` (`B ∘ Ω̂_f = Ω̂_c ∘ B`), the lift `ψ ∘ B` of a bounded measurable coarse state of
    charge `ε` is a fine sector state of charge `ε`. -/
theorem lift_mem_sec {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν] {k : TKernel X}
    (c : CentreSym ν k) {B : X → Ωc} (hBm : Measurable B) {σc : Ωc → Ωc} (hB : ∀ x, B (c.σ x) = σc (B x)) {ε : ℝ}
    {ψ : Ωc → ℝ} (hψm : Measurable ψ) (hψb : ∃ M, ∀ y, |ψ y| ≤ M) (hψ : IsCharged σc ε ψ) :
    Sec c (fun _ => True) ε (fun x => ψ (B x)) := by
  refine ⟨⟨hψm.comp hBm, hψb.imp fun M hM x => hM _⟩, trivial, fun x => ?_⟩
  exact lift_charged hB hψ x

/-- **One-sided half of the transport (blocking in space, time step unchanged):** correlators of lifted coarse flux states decay at
    least like the fine flux sector, `(∫ φ · Tⁿ(ψ ∘ B))² ≤ (lamVac^n e^{−E_e n})² ‖φ‖² ‖ψ ∘ B‖²` with the fine `E_e`. -/
theorem blocked_flux_decay {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν] {k : TKernel X}
    (c : CentreSym ν k) {B : X → Ωc} (hBm : Measurable B) {σc : Ωc → Ωc} (hB : ∀ x, B (c.σ x) = σc (B x))
    {ψ : Ωc → ℝ} (hψm : Measurable ψ) (hψb : ∃ M, ∀ y, |ψ y| ≤ M) (hψ : IsCharged σc (-1) ψ)
    {φ : X → ℝ} (hφ : BM φ) (n : ℕ) :
    (∫ x, φ x * (top ν k)^[n] (fun x => ψ (B x)) x ∂ν) ^ 2 ≤
      ((lamVac c (fun _ => True)) ^ n * Real.exp (-(fluxEnergy c (fun _ => True) * n))) ^ 2 * nrm ν φ *
        nrm ν (fun x => ψ (B x)) :=
  flux_correlator_decay c _ (fun _ _ => trivial) (fun _ _ _ => trivial) hφ (lift_mem_sec c hBm hB hψm hψb hψ) n

end Transport

/-! ## 2. T38 in full: reflection positivity of a blocked layer, coarse plane included -/

section T38

variable {P A C Y : Type*} [Fintype P] [Fintype A] [Fintype C] [Fintype Y]

/-- The coarse reflection form `Σ_{fine} W(p, a, b) Σ_{coarse} K(c, y, y' | p, a, b) F(c, y) F(c, y')`, where the fine weight is
    `v(p) w(p, a) w(p, b)` (fine plane `p`, positive half `a`, reflected negative half `b`), the coarse plane variable is drawn by
    `K₀(p, ·)` and the coarse positive (negative) variable by `K₊(p, a, c, ·)` (`K₊(p, b, c, ·)`). -/
def coarseForm (v : P → ℝ) (w : P → A → ℝ) (K0 : P → C → ℝ) (Kp : P → A → C → Y → ℝ) (F : C → Y → ℝ) : ℝ :=
  ∑ p, ∑ a, ∑ b, ∑ c, ∑ y, ∑ y', v p * w p a * w p b * K0 p c * Kp p a c y * Kp p b c y' * (F c y * F c y')

/-- The coarse form is a sum of squares weighted by `v K₀`. -/
theorem coarseForm_eq (v : P → ℝ) (w : P → A → ℝ) (K0 : P → C → ℝ) (Kp : P → A → C → Y → ℝ) (F : C → Y → ℝ) :
    coarseForm v w K0 Kp F = ∑ p, ∑ c, v p * K0 p c * (∑ a, ∑ y, w p a * Kp p a c y * F c y) ^ 2 := by
  unfold coarseForm
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  ring

/-- **T38 in full (every blocked layer has its own Duality).** A blocking that gates the coarse plane through the fine plane gives a
    reflection-positive coarse layer for every observable of the closed coarse positive half, coarse plane variables included. -/
theorem layer_rp (v : P → ℝ) (w : P → A → ℝ) (K0 : P → C → ℝ) (Kp : P → A → C → Y → ℝ) (F : C → Y → ℝ)
    (hv : ∀ p, 0 ≤ v p) (hK0 : ∀ p c, 0 ≤ K0 p c) : 0 ≤ coarseForm v w K0 Kp F := by
  rw [coarseForm_eq]
  exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun c _ =>
    mul_nonneg (mul_nonneg (hv p) (hK0 p c)) (sq_nonneg _)

end T38

/-! ### The obstruction: a coarse plane variable drawn from both halves (toy) -/

section Straddle

/-- Toy fine layer: each half carries `(b, Y) ∈ Bool × Bool` with weight `1` if `b = Y`, else `0`; no plane variable. -/
def toyW (q : Bool × Bool) : ℝ := if q.1 = q.2 then 1 else 0

/-- The toy fine layer is reflection positive: `Σ_{a,b} w(a) w(b) Φ(b) Φ(a) = (Σ_a w(a) Φ(a))² ≥ 0`. -/
theorem straddle_fine_rp (Φ : Bool × Bool → ℝ) : 0 ≤ ∑ qa, ∑ qb, toyW qa * toyW qb * (Φ qb * Φ qa) := by
  have e : ∑ qa, ∑ qb, toyW qa * toyW qb * (Φ qb * Φ qa) = (∑ q, toyW q * Φ q) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun qa _ => Finset.sum_congr rfl fun qb _ => by ring
  rw [e]; exact sq_nonneg _

/-- A coarse observable of the closed positive half: it reads the coarse plane variable `c` and the coarse positive variable `y`. -/
def toyF (c y : Bool) : ℝ := if c then 0 else (if y then 1 else -1)

/-- **A straddling blocking destroys reflection positivity.** The coarse plane variable `c = [b̃ = b]` is drawn symmetrically from
    both halves (so the blocking commutes with the reflection), the coarse positive variable is `Y`, the negative one `Ỹ`. The coarse
    reflection form of `toyF` is `−2 < 0`. -/
theorem straddle_breaks_rp :
    ∑ qa : Bool × Bool, ∑ qb : Bool × Bool,
      toyW qa * toyW qb * (toyF (decide (qa.1 = qb.1)) qb.2 * toyF (decide (qa.1 = qb.1)) qa.2) = -2 := by
  simp [Fintype.sum_prod_type, toyW, toyF]
  norm_num

end Straddle

end Attempts.R4.Layer
