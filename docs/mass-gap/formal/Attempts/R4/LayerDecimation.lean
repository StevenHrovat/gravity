/-
Round 4, attempt r4-layer, 2026-11-21. Released under Apache 2.0.

# The decimation blocking of lattice gauge theory: gauge, centre and reflection covariant; T38 and flux transport with SU(2) inside

Note: `docs/mass-gap/weak-coupling/attempts/r4-layer/NOTE.md`, sections 2 and 3.

The blocking by the factor 2 that keeps, for every coarse link `(x, μ)` of `(ℤ/Mℤ)^d`, the product of the two fine links of
`(ℤ/2Mℤ)^d` that run along it:

  `(D U)(x, μ) = U(2x, μ) · U(2x + e_μ, μ)`.

All other fine links are integrated out (they do not enter `D U`). This is the simplest gauge-covariant blocking; it is the
"flat/slab" blocking of the note, the one blocking that keeps site reflection positivity in every direction.

Proved, for every group `G` (SU(2) in the corollaries):
* `decimate_gauge`: gauge covariance, `D(g · U) = (g ∘ 2·) · D U`.
* `decimate_centreFlip`: centre covariance, `D(Ω̂_f U) = Ω̂_c(D U)` for 't Hooft's centre transformation of the last row (fine row
  `2M − 1`, coarse row `M − 1`).
* `decimate_thetaConn`: reflection covariance, `D(Θ_f U) = Θ_c(D U)` for the site reflection `t ↦ −t`.
* `linkDep_decimate`: a coarse observable of the closed coarse positive half lifts to a fine observable of the closed fine positive
  half (`M` even).
* `decimated_wilson_rp`, `decimated_wilson_rp_SU2`: **T38 for the blocked Yang–Mills layer**: the image of the Wilson measure under
  `D` is reflection positive for every bounded measurable coarse observable of the closed coarse positive half.
* `su2_decimated_flux_decay`: on the spatial slice, the lift of a coarse flux-sector state is a fine flux-sector state of the SU(2)
  Wilson transfer operator, so its correlators decay at least like `e^{−E_e n}` (the one-sided half of the transport, with SU(2)
  inside).
-/

import Attempts.R4.LayerKernel
import Attempts.R4.LayerTransport

open MeasureTheory Finset AreaLaw.Concrete AreaLaw.Twist Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.R4.Layer

variable {M : ℕ} [NeZero M]

instance instNeZeroTwoMul : NeZero (2 * M) := ⟨by have := NeZero.ne M; omega⟩

/-! ## The doubling map on sites -/

/-- `a ↦ 2a`, from `ℤ/Mℤ` to `ℤ/2Mℤ`. -/
def dbl (a : ZMod M) : ZMod (2 * M) := ((2 * a.val : ℕ) : ZMod (2 * M))

theorem dbl_add (a b : ZMod M) : dbl (a + b) = dbl a + dbl b := by
  unfold dbl
  have h : (2 * ((a.val + b.val) % M) : ℕ) = (2 * (a.val + b.val)) % (2 * M) := (Nat.mul_mod_mul_left 2 _ _).symm
  rw [ZMod.val_add, h, ZMod.natCast_mod]; push_cast; ring

theorem dbl_zero : dbl (0 : ZMod M) = 0 := by simp [dbl]

theorem dbl_one : dbl (1 : ZMod M) = 2 := by
  unfold dbl
  have h : (2 * (1 % M) : ℕ) = (2 * 1) % (2 * M) := (Nat.mul_mod_mul_left 2 _ _).symm
  rw [ZMod.val_one_eq_one_mod, h, ZMod.natCast_mod]; push_cast; ring

theorem dbl_neg (a : ZMod M) : dbl (-a) = -dbl a := by
  have h := dbl_add a (-a)
  rw [add_neg_cancel, dbl_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem val_dbl (a : ZMod M) : (dbl a).val = 2 * a.val := by
  unfold dbl
  exact ZMod.val_cast_of_lt (by have := ZMod.val_lt a; omega)

theorem val_dbl_add_one (a : ZMod M) : (dbl a + 1).val = 2 * a.val + 1 := by
  have e : dbl a + 1 = ((2 * a.val + 1 : ℕ) : ZMod (2 * M)) := by unfold dbl; push_cast; ring
  rw [e]; exact ZMod.val_cast_of_lt (by have := ZMod.val_lt a; omega)

variable {d : ℕ}

/-- The fine site `2x` of a coarse site `x`. -/
def fineSite (x : FinLatticeSites d M) : FinLatticeSites d (2 * M) := fun μ => dbl (x μ)

theorem fineSite_siteShift (x : FinLatticeSites d M) (μ : Fin d) :
    siteShift d (2 * M) (siteShift d (2 * M) (fineSite x) μ) μ = fineSite (siteShift d M x μ) := by
  funext ν
  simp only [siteShift, fineSite, Function.update_apply]
  split_ifs with h
  · subst h; rw [dbl_add, dbl_one]; ring
  · rfl

/-! ## The decimation -/

variable {G : Type*} [Group G]

/-- The fine links along the coarse link `(x, μ)`. -/
def firstLink (l : LatticeLink d M) : LatticeLink d (2 * M) := ⟨fineSite l.site, l.dir⟩

def secondLink (l : LatticeLink d M) : LatticeLink d (2 * M) := ⟨siteShift d (2 * M) (fineSite l.site) l.dir, l.dir⟩

/-- **The decimation blocking** `(D U)(x, μ) = U(2x, μ) U(2x + e_μ, μ)`. -/
def decimate (U : GaugeConnection G d (2 * M)) : GaugeConnection G d M := fun l => U (firstLink l) * U (secondLink l)

theorem measurable_decimate [MeasurableSpace G] [MeasurableMul₂ G] :
    Measurable (decimate (G := G) (d := d) (M := M)) :=
  measurable_pi_iff.mpr fun _ => (measurable_pi_apply _).mul (measurable_pi_apply _)

/-- **Gauge covariance.** -/
theorem decimate_gauge (g : GaugeTransform G d (2 * M)) (U : GaugeConnection G d (2 * M)) :
    decimate (gaugeTransformConnection g U) = gaugeTransformConnection (fun x => g (fineSite x)) (decimate U) := by
  funext l
  simp only [decimate, gaugeTransformConnection, firstLink, secondLink, LatticeLink.target]
  rw [fineSite_siteShift]
  group

/-! ## Centre covariance -/

variable [NeZero d]

theorem val_neg_one' (K : ℕ) [NeZero K] : ((-1 : ZMod K)).val = K - 1 := by
  have e : (-1 : ZMod K) = ((K - 1 : ℕ) : ZMod K) := by
    rw [Nat.cast_sub NeZero.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [e, ZMod.val_cast_of_lt (by have := NeZero.pos K; omega)]

theorem dbl_eq_neg_one_iff (a : ZMod M) : dbl a + 1 = -1 ↔ a = -1 := by
  constructor
  · intro h
    have h1 := congrArg ZMod.val h
    rw [val_dbl_add_one] at h1
    have hm : ((-1 : ZMod (2 * M))).val = 2 * M - 1 := val_neg_one' _
    have hm' : ((-1 : ZMod M)).val = M - 1 := val_neg_one' _
    apply ZMod.val_injective
    rw [hm']; rw [hm] at h1
    have := NeZero.ne M; omega
  · intro h; subst h
    rw [dbl_neg, dbl_one]; ring

theorem dbl_ne_neg_one (a : ZMod M) : dbl a ≠ -1 := by
  intro h
  have h1 := congrArg ZMod.val h
  rw [val_dbl, val_neg_one'] at h1
  have := NeZero.ne M; omega

theorem firstLink_not_mem_rowSet (μ₀ : Fin d) (l : LatticeLink d M) : firstLink l ∉ rowSet d (2 * M) μ₀ := by
  rw [mem_rowSet]; rintro ⟨-, h⟩; exact dbl_ne_neg_one _ h

theorem secondLink_mem_rowSet (μ₀ : Fin d) (l : LatticeLink d M) :
    secondLink l ∈ rowSet d (2 * M) μ₀ ↔ l ∈ rowSet d M μ₀ := by
  rw [mem_rowSet, mem_rowSet]
  simp only [secondLink]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    subst h1
    rw [siteShift, Function.update_self] at h2
    exact (dbl_eq_neg_one_iff _).mp h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    subst h1
    rw [siteShift, Function.update_self]
    exact (dbl_eq_neg_one_iff _).mpr h2

/-- **Centre covariance:** decimation commutes with 't Hooft's centre transformation of the last row,
    `D(Ω̂_f U) = Ω̂_c(D U)`. -/
theorem decimate_centreFlip {z : G} (hz : ∀ g : G, Commute z g) (μ₀ : Fin d) (U : GaugeConnection G d (2 * M)) :
    decimate (centreFlip z μ₀ U) = centreFlip z μ₀ (decimate U) := by
  funext l
  simp only [decimate, centreFlip, twistAt, firstLink_not_mem_rowSet μ₀ l, ↓reduceIte]
  by_cases h : l ∈ rowSet d M μ₀
  · simp only [(secondLink_mem_rowSet μ₀ l).mpr h, h, ↓reduceIte]
    rw [← mul_assoc, ← (hz _).eq, mul_assoc]
  · simp only [mt (secondLink_mem_rowSet μ₀ l).mp h, h, ↓reduceIte]

/-! ## Reflection covariance -/

theorem fineSite_update (x : FinLatticeSites d M) (v : ZMod M) :
    fineSite (Function.update x 0 v) = Function.update (fineSite x) 0 (dbl v) := by
  funext ν
  simp only [fineSite, Function.update_apply]
  split_ifs <;> rfl

theorem fineSite_reflSite (x : FinLatticeSites d M) : fineSite (reflSite x) = reflSite (fineSite x) := by
  unfold reflSite; rw [fineSite_update, dbl_neg]; rfl

theorem fineSite_tflipSite (x : FinLatticeSites d M) :
    fineSite (tflipSite x) = tflipSite (siteShift d (2 * M) (fineSite x) 0) := by
  funext ν
  simp only [tflipSite, siteShift, fineSite, Function.update_apply]
  split_ifs with h
  · rw [sub_eq_add_neg, dbl_add, dbl_neg, dbl_neg, dbl_one]; ring
  · rfl

theorem siteShift_fineSite_tflipSite (x : FinLatticeSites d M) :
    siteShift d (2 * M) (fineSite (tflipSite x)) 0 = tflipSite (fineSite x) := by
  funext ν
  simp only [tflipSite, siteShift, fineSite, Function.update_apply]
  split_ifs with h
  · rw [sub_eq_add_neg, dbl_add, dbl_neg, dbl_neg, dbl_one]; ring
  · rfl

/-- **Reflection covariance:** `D(Θ_f U) = Θ_c(D U)` for the site reflection `t ↦ −t` (temporal links reversed). -/
theorem decimate_thetaConn (U : GaugeConnection G d (2 * M)) : decimate (thetaConn U) = thetaConn (decimate U) := by
  funext l
  rcases l with ⟨x, μ⟩
  by_cases hμ : μ = 0
  · subst hμ
    simp only [decimate, thetaConn, mirrorLink, firstLink, secondLink, ↓reduceIte]
    rw [siteShift_fineSite_tflipSite, fineSite_tflipSite, mul_inv_rev]
  · simp only [decimate, thetaConn, mirrorLink, firstLink, secondLink, hμ, ↓reduceIte]
    rw [fineSite_reflSite, reflSite_siteShift _ hμ]

/-! ## The closed positive half lifts to the closed positive half -/

theorem mem_posHalfLinks_iff {K : ℕ} [NeZero K] (l : LatticeLink d K) :
    l ∈ posHalfLinks d K ↔ IsPosLink l ∨ IsFixedLink l := by
  simp [posHalfLinks]

theorem firstLink_mem (hM : Even M) {l : LatticeLink d M} (hl : l ∈ posHalfLinks d M) :
    firstLink l ∈ posHalfLinks d (2 * M) := by
  obtain ⟨k, hk⟩ := hM
  rw [mem_posHalfLinks_iff] at hl ⊢
  rcases l with ⟨x, μ⟩
  have hv : ((firstLink (⟨x, μ⟩ : LatticeLink d M)).site 0).val = 2 * (x 0).val := val_dbl _
  have hd : (firstLink (⟨x, μ⟩ : LatticeLink d M)).dir = μ := rfl
  unfold IsPosLink IsFixedLink at hl ⊢
  rw [hv, hd]
  dsimp only at hl
  omega

theorem secondLink_mem (hM : Even M) {l : LatticeLink d M} (hl : l ∈ posHalfLinks d M) :
    secondLink l ∈ posHalfLinks d (2 * M) := by
  obtain ⟨k, hk⟩ := hM
  rw [mem_posHalfLinks_iff] at hl ⊢
  rcases l with ⟨x, μ⟩
  have hd : (secondLink (⟨x, μ⟩ : LatticeLink d M)).dir = μ := rfl
  have hlt := ZMod.val_lt (x 0)
  unfold IsPosLink IsFixedLink at hl ⊢
  rw [hd]
  dsimp only at hl
  by_cases hμ : μ = 0
  · have hv : ((secondLink (⟨x, μ⟩ : LatticeLink d M)).site 0).val = 2 * (x 0).val + 1 := by
      show (siteShift d (2 * M) (fineSite x) μ 0).val = _
      rw [hμ, siteShift_zero_zero]; exact val_dbl_add_one _
    rw [hv]
    omega
  · have hv : ((secondLink (⟨x, μ⟩ : LatticeLink d M)).site 0).val = 2 * (x 0).val := by
      show (siteShift d (2 * M) (fineSite x) μ 0).val = _
      rw [siteShift_zero_of_ne _ hμ]; exact val_dbl _
    rw [hv]
    omega

/-- A coarse observable of the closed coarse positive half lifts to one of the closed fine positive half. -/
theorem linkDep_decimate (hM : Even M) {α : Type*} {F : GaugeConnection G d M → α} (hF : LinkDep F (posHalfLinks d M)) :
    LinkDep (fun U => F (decimate U)) (posHalfLinks d (2 * M)) := by
  intro U V hUV
  apply hF
  intro l hl
  show U (firstLink l) * U (secondLink l) = V (firstLink l) * V (secondLink l)
  rw [hUV _ (firstLink_mem hM hl), hUV _ (secondLink_mem hM hl)]

/-! ## T38 for the blocked Yang–Mills layer -/

section RP

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {n : ℕ} [HasGaugeTrace G n] [HasHaarProbability G] [(haarG G).IsInvInvariant]

/-- **T38 for the decimated Yang–Mills layer.** The image of the Wilson measure of `(ℤ/2Mℤ)^d` under the decimation is reflection
    positive for the coarse site reflection: for every bounded measurable coarse `F` of the closed coarse positive half
    `0 ≤ t ≤ M/2` (the coarse fixed slices included), `∫ (F ∘ D) · (F ∘ Θ_c ∘ D) · e^{−S_W} ≥ 0`. -/
theorem decimated_wilson_rp (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ) (hM : Even M) (β : ℝ)
    {F : GaugeConnection G d M → ℝ} (hF : LinkDep F (posHalfLinks d M)) (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) :
    0 ≤ ∫ U, F (decimate U) * F (thetaConn (decimate U)) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d (2 * M))), Real.exp (β * xp n p U) ∂(productHaar G d (2 * M)) := by
  simp_rw [← decimate_thetaConn]
  exact wilson_rp (even_two_mul M) hc hU β (linkDep_decimate hM hF) (mF.comp measurable_decimate)
    (bF.imp fun C h U => h _)

end RP

/-- **T38 for the decimated SU(2) layer.** -/
theorem decimated_wilson_rp_SU2 (hM : Even M) (β : ℝ) {F : GaugeConnection SU2 d M → ℝ}
    (hF : LinkDep F (posHalfLinks d M)) (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) :
    0 ≤ ∫ U, F (decimate U) * F (thetaConn (decimate U)) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d (2 * M))), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d (2 * M)) :=
  decimated_wilson_rp su2_hc su2_hU hM β hF mF bF

/-! ## The flux sector is carried to the blocked layer (spatial decimation of the slice, SU(2)) -/

/-- **The coarse flux sector lies in the fine flux sector of the SU(2) Wilson transfer operator**, and correlators of lifted coarse
    flux states decay at least like the fine `e^{−E_e n}` (one-sided: a coarse observer sees a rate `≥ E_e`). Here `d` is the
    spatial dimension of the slice and the decimation acts on the slice (time step unchanged). -/
theorem su2_decimated_flux_decay (β : ℝ) (μ₀ : Fin d) {ψ : GaugeConnection SU2 d M → ℝ} (hψm : Measurable ψ)
    (hψb : ∃ C, ∀ V, |ψ V| ≤ C) (hψ : IsCharged (centreFlip negOneSU2 μ₀) (-1) ψ)
    {φ : GaugeConnection SU2 d (2 * M) → ℝ} (hφ : BM φ) (m : ℕ) :
    (∫ x, φ x * (top (productHaar SU2 d (2 * M)) (wilsonTKernel (ds := d) (N := 2 * M) su2_hc su2_hU β))^[m]
        (fun x => ψ (decimate x)) x ∂(productHaar SU2 d (2 * M))) ^ 2 ≤
      ((lamVac (su2Centre (N := 2 * M) β μ₀) (fun _ => True)) ^ m *
          Real.exp (-(fluxEnergy (su2Centre (N := 2 * M) β μ₀) (fun _ => True) * m))) ^ 2 *
        nrm (productHaar SU2 d (2 * M)) φ * nrm (productHaar SU2 d (2 * M)) (fun x => ψ (decimate x)) :=
  blocked_flux_decay (su2Centre (N := 2 * M) β μ₀) measurable_decimate
    (fun x => decimate_centreFlip negOneSU2_central μ₀ x) hψm hψb hψ hφ m

end Attempts.R4.Layer
