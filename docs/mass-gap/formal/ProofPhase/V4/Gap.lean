/-
Proof phase, cycle 5, workstream 1 (c5a-v4): the infrared interface of version 4 (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5a-v4/NOTE.md`.
-/

import ProofPhase.V3.W1Route
import ProofPhase.V4.LCP

/-!
# The infrared statement of version 4: the W₁ block gap, in two strengths, for any family of laws

Version 4 cuts the proof at `L_*` (the tuning's unit read as the end of segment 1) and keeps one infrared input: the W₁
block gap `V3.BlockGapUnifW T B λ`. This file states it for an arbitrary family of laws on tori (so the same statement can
be asked of the `L_*` theory and of its further blockings) and adds the weaker **bounded form**, which is exactly what the
torus decay consumes and what the recursion lemma (`ProofPhase.V4.Recursion`) produces.

* `LawGapW ρ λ` (homogeneous form, for laws `ρ k j` on tori of side `M j`): bounded `f` (oscillations `vf` on `A`) against
  geodesic-Lipschitz `g` (constant `Lg`) at link distance `≥ R`: `|Cov_ρ(f, g)| ≤ C (Σ_A vf) Lg e^{−λR}`.
  `blockGapUnifW_iff_lawGapW`: `BlockGapUnifW T B λ ↔ LawGapW (blockedLaw T B) λ`.
* `LevelDprimeWOn ρ λ`: v3's `LevelDprimeW` for any family of laws (`levelDprimeW_iff_on` is `Iff.rfl`);
  `lawGapW_of_levelDprimeWOn` (S, c3c's `decay_of_siteW`).
* `LawGapBddW ρ λ`, `BlockGapBddW T B λ` (**bounded form**): only `|f|, |g| ≤ 1` and `R ≥ 0`, bound
  `C (1 + Σ_A vf)(1 + Lg) e^{−λR}`. Implied by the homogeneous form (`blockGapBddW_of_unifW`).
* `torusDecayLoc_of_blockGapBddW` (S): `BlockGapBddW ∧ ObsTransferPhysTW ⇒ TorusDecayLoc`, the v3 cut with the weaker
  infrared input (same proof as `V3.torusDecayLoc_of_blockGapUnifW`, constant `C(1 + 2K)(1 + K)`).

**Claim level.** Both forms are decay statements for block observables of the Wilson measure: **gap strength**, named
as such (the photon fails them: power-law block correlations). They are the one infrared input of version 4.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift OneScale.CubeChain Positivity ProofPhase.Existence ProofPhase.RouteA ProofPhase.Torus
  ProofPhase.H1 ProofPhase.Certified ProofPhase.V3

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.V4

section Laws

variable {M : ℕ → ℕ} [∀ j, NeZero (M j)]

/-- **The W₁ gap of a family of laws** `ρ k j` on the tori `(ℤ/M_j)⁴`, homogeneous form, uniform in `k ≥ k₀` and `j`. -/
def LawGapW (ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection SU2 4 (M j) → ℝ) (A Sg : Finset (LatticeLink 4 (M j)))
    (vf : LatticeLink 4 (M j) → ℝ) (Lg R : ℝ),
    BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → LipBound geodSU2 g (fun _ => Lg) →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ V, f V * g V ∂(ρ k j) - (∫ V, f V ∂(ρ k j)) * ∫ V, g V ∂(ρ k j)| ≤
      C * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R))

/-- **The W₁ gap of a family of laws, bounded form**: `|f|, |g| ≤ 1`, `R ≥ 0`, bound `C (1 + Σ vf)(1 + Lg) e^{−λR}`. -/
def LawGapBddW (ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection SU2 4 (M j) → ℝ) (A Sg : Finset (LatticeLink 4 (M j)))
    (vf : LatticeLink 4 (M j) → ℝ) (Lg R : ℝ),
    Measurable f → Measurable g → (∀ V, |f V| ≤ 1) → (∀ V, |g V| ≤ 1) → DepOn f A → DepOn g Sg →
    OscBound f vf → 0 ≤ Lg → LipBound geodSU2 g (fun _ => Lg) → 0 ≤ R →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ V, f V * g V ∂(ρ k j) - (∫ V, f V ∂(ρ k j)) * ∫ V, g V ∂(ρ k j)| ≤
      C * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(lam * R))

/-- **D′ in W₁ form for any family of laws** (v3's `LevelDprimeW` with the blocked law replaced by `ρ k j`). -/
def LevelDprimeWOn (ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))) (lam : ℝ) : Prop :=
  ∃ γ D₁ : ℝ, 0 ≤ γ ∧ γ * Real.exp (lam * D₁) < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
    ∃ V : Finset (LatticeLink 4 (M j)) → GaugeConnection SU2 4 (M j) → ℝ,
    ρ k j = Attempts.R3.gibbsMeasure (haarG SU2) V ∧ Attempts.R3.Potential (fun A => A) V ∧
    ∃ kk : LatticeLink 4 (M j) → LatticeLink 4 (M j) → ℝ,
      SiteInfluenceW (haarG SU2) (fun A => A) V geodSU2 kk ∧
      (∀ z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (LatticeLink 4 (M j)))), kk i z ≤ γ) ∧
      (∀ i z, z ∉ ({i} : Finset (LatticeLink 4 (M j))) → kk i z ≠ 0 → linkDist z i ≤ D₁)

/-- Oscillation sums are nonnegative. -/
theorem sum_osc_nonneg {N : ℕ} [NeZero N] {f : GaugeConnection SU2 4 N → ℝ} {vf : LatticeLink 4 N → ℝ}
    (hvf : OscBound f vf) (A : Finset (LatticeLink 4 N)) : 0 ≤ ∑ a ∈ A, vf a :=
  Finset.sum_nonneg fun a _ => hvf.nonneg (fun _ => 1) a

/-- `C S L ≤ C (1 + S)(1 + L)` for nonnegative `C, S, L` (times a nonnegative factor). -/
theorem homog_le_bdd {C S L E : ℝ} (hC : 0 ≤ C) (hS : 0 ≤ S) (hL : 0 ≤ L) (hE : 0 ≤ E) :
    C * S * L * E ≤ C * (1 + S) * (1 + L) * E := by
  refine mul_le_mul_of_nonneg_right ?_ hE
  exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC) (by linarith) hL (mul_nonneg hC (by linarith))

/-- **D′ in W₁ form gives the W₁ gap** (S: c3c's `decay_of_siteW` on each law). -/
theorem lawGapW_of_levelDprimeWOn {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ}
    (hlam : 0 ≤ lam) (h : LevelDprimeWOn ρ lam) : LawGapW ρ lam := by
  obtain ⟨γ, D₁, hγ0, hρ, k₀, H⟩ := h
  refine ⟨Real.pi / (1 - γ * Real.exp (lam * D₁)), div_nonneg Real.pi_pos.le (by linarith), k₀,
    fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ?_⟩
  obtain ⟨V, hgibbs, hpot, kk, hk', hcol, hD₁⟩ := H k hk j
  have : Nonempty (LatticeLink 4 (M j)) := ⟨⟨fun _ => 0, 0⟩⟩
  rw [hgibbs]
  exact decay_of_siteW (haarG SU2) hpot geodSU2_nonneg geodSU2_le_pi hk' hγ0 hcol linkDist linkDist_self
    linkDist_triangle hD₁ hlam hρ hf hg hfA hgS hvf hLg hvg hR

/-- The homogeneous form implies the bounded form. -/
theorem lawGapBddW_of_lawGapW {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ}
    (h : LawGapW ρ lam) : LawGapBddW ρ lam := by
  obtain ⟨C, hC, k₀, H⟩ := h
  refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip _ hR => ?_⟩
  exact (H k hk j f g A Sg vf Lg R ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩ hfA hgS hvf hLg hlip hR).trans
    (homog_le_bdd hC (sum_osc_nonneg hvf A) hLg (Real.exp_pos _).le)

end Laws

/-! ## The blocked Yang–Mills laws -/

/-- **The W₁ block gap, bounded form** (version 4's infrared input in its weakest consumed form): for `|f|, |g| ≤ 1`,
`f` with oscillations `vf` on `A`, `g` geodesic-Lipschitz with constant `Lg` on `Sg`, coarse link distance `≥ R ≥ 0`,
`|Cov_{T.ym k j}(f ∘ B, g ∘ B)| ≤ C (1 + Σ_A vf)(1 + Lg) e^{−λR}`, uniformly in `k ≥ k₀` and `j`. -/
def BlockGapBddW (T : Tuning) (B : BlockingFamily T) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
    (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg R : ℝ),
    Measurable f → Measurable g → (∀ V, |f V| ≤ 1) → (∀ V, |g V| ≤ 1) → DepOn f A → DepOn g Sg →
    OscBound f vf → 0 ≤ Lg → LipBound geodSU2 g (fun _ => Lg) → 0 ≤ R →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
        (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
      C * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(lam * R))

/-- v3's `LevelDprimeW` is `LevelDprimeWOn` of the blocked laws (definitional). -/
theorem levelDprimeW_iff_on {T : Tuning} (B : BlockingFamily T) (lam : ℝ) :
    LevelDprimeW T B lam ↔ LevelDprimeWOn (M := coarseSide) (blockedLaw T B) lam := Iff.rfl

/-- `BlockGapUnifW` is `LawGapW` of the blocked laws. -/
theorem blockGapUnifW_iff_lawGapW {T : Tuning} (B : BlockingFamily T) (lam : ℝ) :
    BlockGapUnifW T B lam ↔ LawGapW (M := coarseSide) (blockedLaw T B) lam := by
  constructor
  · rintro ⟨C, hC, k₀, H⟩
    refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hlip hR => ?_⟩
    have := H k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hlip hR
    rw [Effective.cov_map (T.ym k j) (B k j).meas hf hg] at this
    exact this
  · rintro ⟨C, hC, k₀, H⟩
    refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hlip hR => ?_⟩
    rw [Effective.cov_map (T.ym k j) (B k j).meas hf hg]
    exact H k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hlip hR

/-- `BlockGapBddW` is `LawGapBddW` of the blocked laws. -/
theorem blockGapBddW_iff_lawGapBddW {T : Tuning} (B : BlockingFamily T) (lam : ℝ) :
    BlockGapBddW T B lam ↔ LawGapBddW (M := coarseSide) (blockedLaw T B) lam := by
  constructor
  · rintro ⟨C, hC, k₀, H⟩
    refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR => ?_⟩
    have := H k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR
    rw [Effective.cov_map (T.ym k j) (B k j).meas ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩] at this
    exact this
  · rintro ⟨C, hC, k₀, H⟩
    refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR => ?_⟩
    rw [Effective.cov_map (T.ym k j) (B k j).meas ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩]
    exact H k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR

/-- **The homogeneous block gap implies the bounded one.** -/
theorem blockGapBddW_of_unifW {T : Tuning} {B : BlockingFamily T} {lam : ℝ} (h : BlockGapUnifW T B lam) :
    BlockGapBddW T B lam :=
  (blockGapBddW_iff_lawGapBddW B lam).2 (lawGapBddW_of_lawGapW ((blockGapUnifW_iff_lawGapW B lam).1 h))

/-- **The v4 cut with the bounded infrared input** (S): `BlockGapBddW ∧ ObsTransferPhysTW ⇒ TorusDecayLoc`, physical
rate `min(λ/(4L), m)` with `L` the tuning's unit. -/
theorem torusDecayLoc_of_blockGapBddW {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    (hB : BlockGapBddW T B lam) (h3 : ObsTransferPhysTW T B) : TorusDecayLoc T.toV := by
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
  have := UV.ymProb T k j
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

end ProofPhase.V4
