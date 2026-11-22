/-
Proof phase, M1 task R11: a measurable-only blocking interface for the assembly. Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-r11/NOTE.md`.
-/

import ProofPhase.V4.Top

/-!
# Measurable blockings: the assembly without reflection symmetry or half-locality

`RPBlocking` carries a map, its measurability, a reflection-commutation `theta` and a half-locality `half`. The gap and
transfer statements of the assembly (`BlockGapBddW`, `BlockGapUnifW`, `ObsTransferPhysTW`) and the proof of the torus decay
use only the map and its measurability (the fields `theta`, `half` occur only in `blocked_wilson_rp` and in the constructions
that compose or noise blockings). Reflection positivity of the limit comes from the bare measure (`limitRP`).

This file states the same data for a bare `MeasBlocking` and proves the analogues of the top theorems, so that a blocking
which is measurable and deterministic but neither reflection-symmetric nor half-local can be plugged in.
Every statement for an `RPBlocking` family is the special case along `RPBlocking.toMeas` (the `Iff.rfl` lemmas below).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift OneScale.CubeChain Positivity ProofPhase.Existence ProofPhase.RouteA ProofPhase.Torus
  ProofPhase.H1 ProofPhase.Certified ProofPhase.V3 ProofPhase.V4

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Interface

/-- **A measurable blocking** from `(ℤ/Nℤ)^d` to `(ℤ/Mℤ)^d`: a measurable map of connections, nothing else. -/
structure MeasBlocking (G : Type*) [Group G] [MeasurableSpace G] (d N M : ℕ) [NeZero d] [NeZero N] [NeZero M] where
  B : GaugeConnection G d N → GaugeConnection G d M
  meas : Measurable B

/-- Forget reflection symmetry and half-locality. -/
def _root_.ProofPhase.RPBlocking.toMeas {G : Type*} [Group G] [MeasurableSpace G] {d N M : ℕ} [NeZero d] [NeZero N]
    [NeZero M] (P : RPBlocking G d N M) : MeasBlocking G d N M := ⟨P.B, P.meas⟩

/-- A measurable blocking family: at every level and volume a measurable map of the fine torus onto the coarse one. -/
abbrev MeasBlockingFamily (T : Tuning) := ∀ k j, MeasBlocking SU2 4 (T.side k j) (coarseSide j)

/-- Forget the reflection structure of a whole family. -/
def blockingFamilyToMeas {T : Tuning} (B : BlockingFamily T) : MeasBlockingFamily T := fun k j => (B k j).toMeas

/-- The blocked law at level `k`, volume `j`: the image of the SU(2) Wilson measure. -/
def measBlockedLaw (T : Tuning) (B : MeasBlockingFamily T) (k j : ℕ) : Measure (GaugeConnection SU2 4 (coarseSide j)) :=
  (T.ym k j).map (B k j).B

/-- `BlockGapUnifW` for a measurable family (same statement). -/
def MeasBlockGapUnifW (T : Tuning) (B : MeasBlockingFamily T) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
    (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg R : ℝ),
    BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → LipBound geodSU2 g (fun _ => Lg) →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
        (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
      C * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R))

/-- `BlockGapBddW` for a measurable family (same statement). -/
def MeasBlockGapBddW (T : Tuning) (B : MeasBlockingFamily T) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
    (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg R : ℝ),
    Measurable f → Measurable g → (∀ V, |f V| ≤ 1) → (∀ V, |g V| ≤ 1) → DepOn f A → DepOn g Sg →
    OscBound f vf → 0 ≤ Lg → LipBound geodSU2 g (fun _ => Lg) → 0 ≤ R →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
        (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
      C * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(lam * R))

/-- `ObsTransferPhysTW` for a measurable family (same statement). -/
def MeasObsTransferPhysTW (T : Tuning) (B : MeasBlockingFamily T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ), 0 ≤ D →
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e') →
    ∃ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink 4 (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ 4) ∧
      LipBound geodSU2 g (fun _ => K) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U - f ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U - g ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(T.ym k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U ∂(T.ym k j)|
        ≤ c * Real.exp (-(m * D))

/-! ## Compatibility: the `RPBlocking` statements are the special case -/

theorem measBlockGapBddW_toMeas_iff {T : Tuning} (B : BlockingFamily T) (lam : ℝ) :
    MeasBlockGapBddW T (blockingFamilyToMeas B) lam ↔ BlockGapBddW T B lam := Iff.rfl

theorem measBlockGapUnifW_toMeas_iff {T : Tuning} (B : BlockingFamily T) (lam : ℝ) :
    MeasBlockGapUnifW T (blockingFamilyToMeas B) lam ↔ BlockGapUnifW T B lam := Iff.rfl

theorem measObsTransferPhysTW_toMeas_iff {T : Tuning} (B : BlockingFamily T) :
    MeasObsTransferPhysTW T (blockingFamilyToMeas B) ↔ ObsTransferPhysTW T B := Iff.rfl

theorem measBlockedLaw_toMeas {T : Tuning} (B : BlockingFamily T) (k j : ℕ) :
    measBlockedLaw T (blockingFamilyToMeas B) k j = blockedLaw T B k j := rfl

/-! ## The gap statements -/

/-- The homogeneous block gap implies the bounded one, for a measurable family. -/
theorem measBlockGapBddW_of_unifW {T : Tuning} {B : MeasBlockingFamily T} {lam : ℝ}
    (h : MeasBlockGapUnifW T B lam) : MeasBlockGapBddW T B lam := by
  obtain ⟨C, hC, k₀, H⟩ := h
  refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip _ hR => ?_⟩
  exact (H k hk j f g A Sg vf Lg R ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩ hfA hgS hvf hLg hlip hR).trans
    (homog_le_bdd hC (sum_osc_nonneg hvf A) hLg (Real.exp_pos _).le)

/-- **The v4 cut with the bounded infrared input, for a measurable blocking family** (the proof of
`V4.torusDecayLoc_of_blockGapBddW`, which uses `B` only through the map and its measurability). -/
theorem measTorusDecayLoc_of_blockGapBddW {T : Tuning} (B : MeasBlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    (hB : MeasBlockGapBddW T B lam) (h3 : MeasObsTransferPhysTW T B) : TorusDecayLoc T.toV := by
  obtain ⟨C, hC, k₀, hgap⟩ := hB
  obtain ⟨m, hm, htrP⟩ := h3
  have hL1 := T.L₁_pos
  set a := lam / 4
  have ha : 0 < a := by positivity
  set m' := min (lam / (4 * T.L₁)) m
  have hm' : 0 < m' := lt_min (by positivity) hm
  refine ⟨m', hm', fun s R => ?_⟩
  obtain ⟨c, K, hc, hK, k₁, htr⟩ := htrP (R + T.L₁)
  refine ⟨max k₀ k₁, C * (1 + 2 * K) * (1 + K) * (24 / a ^ 4 * Real.exp a) + 5 * c, by positivity,
    fun k hk Vb j O hO n hn => ?_⟩
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hk₁ : k₁ ≤ k := (le_max_right _ _).trans hk
  obtain ⟨hdA, hdB, -, -, -⟩ := slab_transfer_data T O hn
  have hsepT := slab_time_sep T O hn
  have hak := T.a_pos k
  have haL : T.a k ≤ T.L₁ := div_le_self hL1.le (by exact_mod_cast T.ℓ_pos k)
  have eA : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j))))
      (R + T.L₁) := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    rw [linkDist_shiftLink]
    have : T.a k * linkDist l l' ≤ R := hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
    linarith
  have eB : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image mirrorLink) (R + T.L₁) := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    have h1 : T.a k * linkDist l l' ≤ R := hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
    have h2 := mul_le_mul_of_nonneg_left (linkDist_mirrorLink_le l l') hak.le
    nlinarith
  set D := (n : ℝ) * T.a k
  have hD : 0 ≤ D := by positivity
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, ⟨vf, hvf, hsv⟩, hlip, hsep', hEF, hEG, hdec⟩ :=
    htr k hk₁ j _ _ _ _ D hD ((O.meas k j).comp (measurable_tShift _))
      ((O.meas k j).comp measurePreserving_thetaConn.measurable) (fun U => O.bdd k j _) (fun U => O.bdd k j _)
      (gaugeInvariant_tShift (O.gauge k j) _) (gaugeInvariant_thetaConn (O.gauge k j)) hdA hdB eA eB hsepT
  have hx : 0 ≤ D / T.L₁ := by positivity
  -- the block covariance, by the bounded infrared input
  have hR' : ∀ x ∈ A', ∀ y ∈ B', D / (2 * T.L₁) ≤ linkDist x y := by
    intro x hx' y hy
    rw [div_le_iff₀ (by positivity)]
    have := hsep' x hx' y hy
    nlinarith
  have hblk := hgap k hk₀ j f g A' B' vf K (D / (2 * T.L₁)) mf mg bf bg dfA dgB hvf hK hlip (by positivity) hR'
  -- the transfer
  haveI := UV.ymProb T k j
  have htr' := cov_transfer (T.ym k j) (B k j).meas ((O.meas k j).comp (measurable_tShift _))
    ((O.meas k j).comp measurePreserving_thetaConn.measurable) (fun U => O.bdd k j _) (fun U => O.bdd k j _)
    mf mg bf bg hEF hEG hdec
  have hw : |T.wcorr k j (O.F k j) n| ≤
      C * (1 + ∑ a ∈ A', vf a) * (1 + K) * Real.exp (-(lam * (D / (2 * T.L₁)))) +
        5 * (c * Real.exp (-(m * D))) := by
    unfold Tuning.wcorr corr
    exact htr'.trans (by linarith)
  -- constants
  have hY1 : 1 ≤ (1 + D / T.L₁) ^ 4 := one_le_pow₀ (by linarith)
  have h1S : 1 + ∑ a ∈ A', vf a ≤ (1 + 2 * K) * (1 + D / T.L₁) ^ 4 := by nlinarith
  set Kc := C * (1 + 2 * K) * (1 + K) with hKcdef
  have hKc : 0 ≤ Kc := by positivity
  have hstep : C * (1 + ∑ a ∈ A', vf a) * (1 + K) ≤ Kc * (1 + D / T.L₁) ^ 4 := by
    have h1 := mul_le_mul_of_nonneg_left h1S hC
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 1 + K)
    calc C * (1 + ∑ a ∈ A', vf a) * (1 + K) ≤ C * ((1 + 2 * K) * (1 + D / T.L₁) ^ 4) * (1 + K) := h2
      _ = Kc * (1 + D / T.L₁) ^ 4 := by rw [hKcdef]; ring
  have hpoly := poly_exp_le ha hx
  have e1 : lam * (D / (2 * T.L₁)) = 2 * a * (D / T.L₁) := by simp only [a]; field_simp; ring
  have e2 : a * (D / T.L₁) = lam / (4 * T.L₁) * D := by simp only [a]; field_simp
  have hE1 : Real.exp (-(lam / (4 * T.L₁) * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (lam / (4 * T.L₁)) m])
  have hE2 : Real.exp (-(m * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (lam / (4 * T.L₁)) m])
  show |T.wcorr k j (O.F k j) n| ≤ _
  calc |T.wcorr k j (O.F k j) n|
      ≤ C * (1 + ∑ a ∈ A', vf a) * (1 + K) * Real.exp (-(lam * (D / (2 * T.L₁)))) +
          5 * (c * Real.exp (-(m * D))) := hw
    _ ≤ Kc * (1 + D / T.L₁) ^ 4 * Real.exp (-(2 * a * (D / T.L₁))) + 5 * c * Real.exp (-(m' * D)) := by
        rw [e1]
        have h5 : c * Real.exp (-(m * D)) ≤ c * Real.exp (-(m' * D)) := mul_le_mul_of_nonneg_left hE2 hc
        have h6 := mul_le_mul_of_nonneg_right hstep (Real.exp_pos (-(2 * a * (D / T.L₁)))).le
        linarith
    _ = Kc * ((1 + D / T.L₁) ^ 4 * Real.exp (-(2 * a * (D / T.L₁)))) + 5 * c * Real.exp (-(m' * D)) := by ring
    _ ≤ Kc * (24 / a ^ 4 * Real.exp a * Real.exp (-(a * (D / T.L₁)))) + 5 * c * Real.exp (-(m' * D)) := by
        gcongr
    _ = Kc * (24 / a ^ 4 * Real.exp a) * Real.exp (-(lam / (4 * T.L₁) * D)) + 5 * c * Real.exp (-(m' * D)) := by
        rw [e2]; ring
    _ ≤ Kc * (24 / a ^ 4 * Real.exp a) * Real.exp (-(m' * D)) + 5 * c * Real.exp (-(m' * D)) := by gcongr
    _ = (Kc * (24 / a ^ 4 * Real.exp a) + 5 * c) * Real.exp (-(m' * (n * T.a k))) := by ring


/-- **Assembly v4 for a measurable blocking family** (bounded infrared input): the conclusions of
`yang_mills_assembly_v4_bdd`, for a blocking that is only measurable. -/
theorem yang_mills_assembly_v4_bdd_meas {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (B : MeasBlockingFamily T)
    {lam : ℝ} (hlam : 0 < lam) (hIR : MeasBlockGapBddW T B lam) (hUV : MeasObsTransferPhysTW T B) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  have hT := measTorusDecayLoc_of_blockGapBddW B hlam hIR hUV
  obtain ⟨hVF, hMF⟩ := bothOrdersLoc_of_torusDecayLoc hL.tendsto_a hT
  exact ⟨hT, hVF, hMF, limitRP T, hN⟩

/-- **Assembly v4 for a measurable blocking family** (homogeneous infrared input). -/
theorem yang_mills_assembly_v4_meas {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (B : MeasBlockingFamily T)
    {lam : ℝ} (hlam : 0 < lam) (hIR : MeasBlockGapUnifW T B lam) (hUV : MeasObsTransferPhysTW T B) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T :=
  yang_mills_assembly_v4_bdd_meas hL hN B hlam (measBlockGapBddW_of_unifW hIR) hUV

/-- The open inputs of version 4 for a measurable blocking family. -/
structure MeasOpenInputsV4 (T : Tuning) : Prop where
  lcp : OnLCP' T
  nontrivial : NonTrivial T
  layers : ∃ (B : MeasBlockingFamily T) (lam : ℝ), 0 < lam ∧ MeasBlockGapBddW T B lam ∧ MeasObsTransferPhysTW T B

theorem yang_mills_assembly_v4_inputs_meas {T : Tuning} (P : MeasOpenInputsV4 T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  obtain ⟨B, lam, hlam, hIR, hUV⟩ := P.layers
  exact yang_mills_assembly_v4_bdd_meas P.lcp P.nontrivial B hlam hIR hUV

/-- The reflection-respecting inputs give the measurable ones. -/
theorem measOpenInputsV4_of_openInputsV4 {T : Tuning} (P : OpenInputsV4 T) : MeasOpenInputsV4 T := by
  obtain ⟨B, lam, hlam, hIR, hUV⟩ := P.layers
  exact ⟨P.lcp, P.nontrivial, blockingFamilyToMeas B, lam, hlam, hIR, hUV⟩

/-! ## Blockings through an intermediate state (for an encoded block state such as SO(3) x Z2) -/

/-- A blocking that goes through an intermediate block state `X` (any measurable space, e.g. an SO(3) field with a Z2
layer) and a measurable SU(2) encoding of that state. -/
def MeasBlocking.viaState {N M : ℕ} [NeZero N] [NeZero M] {X : Type*} [MeasurableSpace X]
    (φ : GaugeConnection SU2 4 N → X) (hφ : Measurable φ) (enc : X → GaugeConnection SU2 4 M)
    (henc : Measurable enc) : MeasBlocking SU2 4 N M := ⟨enc ∘ φ, henc.comp hφ⟩

/-- The blocked law of such a blocking is the encoding of the law of the block state. -/
theorem measBlockedLaw_viaState {N M : ℕ} [NeZero N] [NeZero M] {X : Type*} [MeasurableSpace X]
    (μ : Measure (GaugeConnection SU2 4 N)) (φ : GaugeConnection SU2 4 N → X) (hφ : Measurable φ)
    (enc : X → GaugeConnection SU2 4 M) (henc : Measurable enc) :
    μ.map (MeasBlocking.viaState φ hφ enc henc).B = (μ.map φ).map enc :=
  (Measure.map_map henc hφ).symm

end ProofPhase.Interface
