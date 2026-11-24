/-
The rotation round: the instances of the marker test (Yang-Mills, Navier-Stokes, the half-turn of the plaquette layer)
(2026-11-24). Released under Apache 2.0.

Note: `docs/unified/ROTATION-API.md`.
-/

import ProofPhase.ETM.Rotation
import ProofPhase.Unified.YangMills
import ProofPhase.Unified.NavierStokesAPI
import ProofPhase.OneBox.Fine
import ProofPhase.Crossover.Dichotomy

/-!
# The rotation API: the instances

**Chain boxes (`chainSys`, `chainBox`).** States are the scales `k : ℕ`, the step is the next scale, the gate factor is a
given stream `f k ∈ [0, 1]`, the mass the running product (the ledger law holds at every floor `δ ≥ 0`). The marker is
the system's own claim at each scale. With the claim `inside` at every scale, DMP-complete from scale `k₀` is exactly
"every gate factor from `k₀` on is within the margin" (`chainBox_complete_iff`).

**Yang-Mills, the chain form of O1 (`o1Box`, `o1_iff_complete`).** Gate factor `min 1 e^{−Fe ω}` of the box in the outside
`ω`, floor `log μ` (the path entropy, `μ ≥ 1`), claim `inside`. Then O1 (`YMOneBox Fe μ`) holds **exactly** when some
margin makes every chain of outsides DMP-complete. Both directions are proved: the general class carries exactly O1.

**Yang-Mills, the Wilson measure (`ymBox`, `fineOneBox_iff_complete`).** For a fixed box geometry (`Geo`: cells, `λ`, `D₀`,
`n_max`, start level `k₀`, uniform in level and volume), the gate factor at level `k` is the best one-box ratio
`γ` for which the level-`k` criterion holds in every volume (`ymFac`, an infimum; `1` when no `γ < 1` works). Then
`FineOneBox T` holds exactly when for some valid geometry and margin `θ < 1` the box is DMP-complete from `k₀`. Both
directions are proved. The converse needs the geometry fixed across levels; that uniformity is part of `FineOneBox` and of
the box, and it is exactly the shared-gate content (note, section 4).

**Navier-Stokes (`nsBox`, `ns_not_complete`).** Gate factor at dyadic scale `k`: the energy-only transfer bound
`K 2^{5k/2}` over the viscous cost `ν 4^k`, clipped to `[0, 1]`; claim `inside` (regular at every scale). By VII.3.4b
(`dyadic_supercritical`) the transfer overtakes the cost at some scale, where the gate reads `r136a1`: the marker is wrong
there, for every `ν, K > 0` and every margin `θ < 1`. Model level, as VII.3.4b.

**The half-turn of the plaquette layer (`crossoverGate`).** A box `R` of plaquettes, a closed `ℤ/2` layer `τ`: the flux
read from inside (`τ` restricted to `R`) and after the half-turn (restricted to the complement) agree
(`cob_restrict_eq_cob_restrict_compl`), so every verdict read from the outside is the verdict read from inside.

**`rotation_round`** collects the theorems. No axioms beyond the standard ones; no open step is assumed.
-/

open Finset
open Arsenal.Rotation (Marker)
open Arsenal.Rotation.Box (Gate)

noncomputable section

namespace ProofPhase.ETM

open Box

/-! ## 1. Chain boxes -/

/-- **A chain of scales**: states `ℕ`, step the next scale, gate factor `f`, mass the running product of the factors;
the ledger law holds at every floor `δ ≥ 0`. -/
def chainSys (f : ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) : RunSys.{0} δ where
  X := ℕ
  step := Nat.succ
  fac := f
  mass i := ∏ j ∈ range i, f j
  fac_nonneg := hf0
  fac_le_one := hf1
  mass_nonneg i := prod_nonneg fun j _ => hf0 j
  pays i := by
    show (∏ j ∈ range (i + 1), f j) ≤ Real.exp δ * f i * ∏ j ∈ range i, f j
    rw [prod_range_succ]
    have hp : 0 ≤ ∏ j ∈ range i, f j := prod_nonneg fun j _ => hf0 j
    have h := mul_le_mul_of_nonneg_right (Real.one_le_exp hδ) (mul_nonneg hp (hf0 i))
    nlinarith [h]

theorem chainSys_iter (f : ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (k n : ℕ) :
    (chainSys f hf0 hf1 hδ).step^[n] k = k + n :=
  Nat.succ_iterate k n

/-- **A chain box**: the chain of scales with a margin and the system's claim at each scale. -/
def chainBox (f : ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (θ : ℝ)
    (hθ : Real.exp δ * θ < 1) (claim : ℕ → Marker) : Box.{0} δ :=
  ⟨chainSys f hf0 hf1 hδ, θ, hθ, claim⟩

/-- **A chain box claiming `inside` at every scale is DMP-complete from `k` exactly when every gate factor from `k` on
is within the margin.** -/
theorem chainBox_complete_iff (f : ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (θ : ℝ)
    (hθ : Real.exp δ * θ < 1) (k : ℕ) :
    (chainBox f hf0 hf1 hδ θ hθ fun _ => .inside).DMPComplete k ↔ ∀ n, f (k + n) ≤ θ := by
  refine forall_congr' fun n => ?_
  show Marker.inside = (if f ((chainSys f hf0 hf1 hδ).step^[n] k) ≤ θ then Marker.inside else Marker.r136a1) ↔ _
  rw [chainSys_iter]
  by_cases h : f (k + n) ≤ θ
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, iff_false]
    exact fun e => Marker.noConfusion e

/-! ## 2. Yang-Mills, the chain form of O1 -/

section O1

variable {Ω : Type*}

/-- The gate factor of the box in the outside `ω n`: `min 1 e^{−Fe}`. -/
def o1Fac (Fe : Ω → ℝ) (ω : ℕ → Ω) (n : ℕ) : ℝ := min 1 (Real.exp (-Fe (ω n)))

theorem o1Fac_nonneg (Fe : Ω → ℝ) (ω : ℕ → Ω) (n : ℕ) : 0 ≤ o1Fac Fe ω n :=
  le_min zero_le_one (Real.exp_pos _).le

theorem o1Fac_le_one (Fe : Ω → ℝ) (ω : ℕ → Ω) (n : ℕ) : o1Fac Fe ω n ≤ 1 := min_le_left _ _

/-- **The O1 box** along a chain of outsides `ω`: floor `log μ` (path entropy), margin `θ` with `μ θ < 1`, claim
`inside` at every box. -/
def o1Box (Fe : Ω → ℝ) {μ : ℝ} (hμ : 1 ≤ μ) (θ : ℝ) (hθ : Real.exp (Real.log μ) * θ < 1) (ω : ℕ → Ω) :
    Box.{0} (Real.log μ) :=
  chainBox (o1Fac Fe ω) (o1Fac_nonneg Fe ω) (o1Fac_le_one Fe ω) (Real.log_nonneg hμ) θ hθ fun _ => .inside

/-- **The general class carries exactly O1** (chain form). O1 holds exactly when some margin makes every chain of
outsides DMP-complete. -/
theorem o1_iff_complete (Fe : Ω → ℝ) {μ : ℝ} (hμ : 1 ≤ μ) :
    Unified.YMOneBox Fe μ ↔
      ∃ θ, ∃ hθ : Real.exp (Real.log μ) * θ < 1, ∀ ω : ℕ → Ω, (o1Box Fe hμ θ hθ ω).DMPComplete (0 : ℕ) := by
  have hμ0 : 0 < μ := lt_of_lt_of_le one_pos hμ
  rw [Unified.ymOneBox_iff_tube hμ0]
  constructor
  · rintro ⟨κ, hκ, hFe⟩
    refine ⟨Real.exp (-κ), by rwa [Real.exp_log hμ0], fun ω => ?_⟩
    refine (chainBox_complete_iff _ _ _ _ _ _ 0).2 fun n => ?_
    exact (min_le_right _ _).trans (Real.exp_le_exp.2 (neg_le_neg (hFe _)))
  · rintro ⟨θ, hθ, H⟩
    rw [Real.exp_log hμ0] at hθ
    set θ' := max θ (1 / (2 * μ)) with hθ'
    have hθ'0 : 0 < θ' := lt_max_of_lt_right (by positivity)
    have hμθ' : μ * θ' < 1 := by
      rw [hθ', mul_max_of_nonneg _ _ hμ0.le]
      refine max_lt hθ ?_
      rw [show μ * (1 / (2 * μ)) = 1 / 2 by field_simp]
      norm_num
    have hθ'1 : θ' < 1 := lt_of_le_of_lt (le_mul_of_one_le_left hθ'0.le hμ) hμθ'
    refine ⟨-Real.log θ', by rwa [neg_neg, Real.exp_log hθ'0], fun ω₀ => ?_⟩
    have h := (chainBox_complete_iff _ _ _ _ _ _ 0).1 (H fun _ => ω₀) 0
    have hle : min 1 (Real.exp (-Fe ω₀)) ≤ θ' := h.trans (le_max_left _ _)
    have he : Real.exp (-Fe ω₀) ≤ θ' := by
      rcases min_le_iff.1 hle with h1 | h1
      · exact absurd h1 (not_le.2 hθ'1)
      · exact h1
    have := Real.exp_le_exp.1 (he.trans_eq (Real.exp_log hθ'0).symm)
    linarith

end O1

/-! ## 3. Yang-Mills, the Wilson measure: `FineOneBox` -/

section Fine

open MeasureTheory Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity ProofPhase.Torus ProofPhase.V3 ProofPhase.V4 ProofPhase.RouteA ProofPhase.OneBox

/-- **The box geometry**, uniform in level and volume: the cells, the cell constants `c₀, c₁`, the rate `λ`, the box
diameter `D₀`, the box size `n_max`, and the start level `k₀`. -/
structure Geo (T : Tuning) where
  cell : ∀ k j, LatticeLink 4 (T.side k j) → LatticeLink 4 (coarseSide j)
  c₀ : ℝ
  c₁ : ℝ
  lam : ℝ
  D₀ : ℝ
  nmax : ℕ
  k₀ : ℕ

/-- A geometry is valid when its cells have physical size `L₁` and the rate is positive. -/
def Geo.Valid {T : Tuning} (g : Geo T) : Prop := CellGeometry T g.cell g.c₀ g.c₁ ∧ 0 < g.lam

open scoped Classical in
/-- **The level-`k` criterion with ratio `γ`**: the body of `FineOneBox` at one level, in every volume. -/
def LevelBox (T : Tuning) (g : Geo T) (γ : ℝ) (k : ℕ) : Prop :=
  ∀ j, ∃ (Λ₀ : Finset (FinLatticeSites 4 (coarseSide j))) (κ : FinLatticeSites 4 (coarseSide j) → ℝ)
      (P : BlockSpec ((T.ym k j).map (cellLift (g.cell k j) (1 : SU2))) (FinLatticeSites 4 (coarseSide j))),
      1 ≤ Λ₀.card ∧ Λ₀.card ≤ g.nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ g.D₀) ∧
      (∀ t, P.block t = boxBlock Λ₀ t) ∧
      (∀ t, SpecCovariant (liftAct (g.cell k j) (gaugeAct (T.side k j))) (P.spec t)) ∧
      (∀ t z, z ∉ P.block t →
        IsInfluenceBoundOn (ActAdm (liftAct (g.cell k j) (gaugeAct (T.side k j))) (P.block t)) (P.block t)
          (P.spec t) z (κ (z.site - t))) ∧
      OneBoxSum κ (boxReach Λ₀) Λ₀ g.lam γ

/-- **`FineOneBox` is a geometry, a ratio `γ < 1`, and the level criterion at every level from `k₀`.** -/
theorem fineOneBox_iff (T : Tuning) :
    FineOneBox T ↔ ∃ g : Geo T, g.Valid ∧ ∃ γ, 0 ≤ γ ∧ γ < 1 ∧ ∀ k, g.k₀ ≤ k → LevelBox T g γ k := by
  constructor
  · rintro ⟨cell, c₀, c₁, hg, lam, γ, D₀, nmax, hl, h0, h1, k₀, H⟩
    exact ⟨⟨cell, c₀, c₁, lam, D₀, nmax, k₀⟩, ⟨hg, hl⟩, γ, h0, h1, H⟩
  · rintro ⟨g, ⟨hg, hl⟩, γ, h0, h1, H⟩
    exact ⟨g.cell, g.c₀, g.c₁, hg, g.lam, γ, g.D₀, g.nmax, hl, h0, h1, g.k₀, H⟩

/-- The level criterion is monotone in the ratio. -/
theorem levelBox_mono {T : Tuning} {g : Geo T} {γ γ' : ℝ} (hγ : γ ≤ γ') {k : ℕ} (h : LevelBox T g γ k) :
    LevelBox T g γ' k := fun j => by
  obtain ⟨Λ₀, κ, P, h1, h2, h3, h4, h5, h6, h7⟩ := h j
  refine ⟨Λ₀, κ, P, h1, h2, h3, h4, h5, h6, ?_⟩
  unfold OneBoxSum at h7 ⊢
  exact h7.trans (mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg _))

open scoped Classical in
/-- **The gate factor at level `k`**: the best one-box ratio for which the level criterion holds (an infimum), `1` when
no ratio below `1` works. -/
def ymFac (T : Tuning) (g : Geo T) (k : ℕ) : ℝ :=
  if ∃ γ, 0 ≤ γ ∧ γ < 1 ∧ LevelBox T g γ k then sInf {γ | 0 ≤ γ ∧ LevelBox T g γ k} else 1

theorem ymFac_le {T : Tuning} {g : Geo T} {γ : ℝ} {k : ℕ} (h0 : 0 ≤ γ) (h1 : γ < 1) (hL : LevelBox T g γ k) :
    ymFac T g k ≤ γ := by
  have hex : ∃ γ, 0 ≤ γ ∧ γ < 1 ∧ LevelBox T g γ k := ⟨γ, h0, h1, hL⟩
  unfold ymFac
  simp only [hex, ↓reduceIte]
  exact csInf_le ⟨0, fun _ h => h.1⟩ ⟨h0, hL⟩

theorem ymFac_nonneg (T : Tuning) (g : Geo T) (k : ℕ) : 0 ≤ ymFac T g k := by
  unfold ymFac
  split_ifs
  · exact Real.sInf_nonneg fun _ h => h.1
  · exact zero_le_one

theorem ymFac_le_one (T : Tuning) (g : Geo T) (k : ℕ) : ymFac T g k ≤ 1 := by
  by_cases h : ∃ γ, 0 ≤ γ ∧ γ < 1 ∧ LevelBox T g γ k
  · obtain ⟨γ, h0, h1, hL⟩ := h
    exact (ymFac_le h0 h1 hL).trans h1.le
  · unfold ymFac
    simp only [h, ↓reduceIte, le_refl]

/-- Below the gate factor's value the criterion holds: any ratio above it (and at most `1`) works. -/
theorem levelBox_of_ymFac_lt {T : Tuning} {g : Geo T} {γ' : ℝ} {k : ℕ} (h : ymFac T g k < γ') (h1 : γ' ≤ 1) :
    LevelBox T g γ' k := by
  by_cases hex : ∃ γ, 0 ≤ γ ∧ γ < 1 ∧ LevelBox T g γ k
  · unfold ymFac at h
    simp only [hex, ↓reduceIte] at h
    obtain ⟨γ, h0, -, hL⟩ := hex
    obtain ⟨γ'', ⟨-, hL''⟩, hlt⟩ := exists_lt_of_csInf_lt (s := {γ | 0 ≤ γ ∧ LevelBox T g γ k}) ⟨γ, h0, hL⟩ h
    exact levelBox_mono hlt.le hL''
  · unfold ymFac at h
    simp only [hex, ↓reduceIte] at h
    linarith

/-- **The Yang-Mills box** of a geometry: the levels from `k₀` as scales, gate factor `ymFac`, floor `0`, margin `θ < 1`,
claim `inside` at every level. -/
def ymBox (T : Tuning) (g : Geo T) (θ : ℝ) (hθ : θ < 1) : Box.{0} 0 :=
  chainBox (ymFac T g) (ymFac_nonneg T g) (ymFac_le_one T g) le_rfl θ (by rwa [Real.exp_zero, one_mul])
    fun _ => .inside

/-- For a fixed geometry, DMP-complete from `k₀` for some margin is the level criterion with one ratio `γ < 1` at every
level from `k₀`. Both directions. -/
theorem ym_complete_iff (T : Tuning) (g : Geo T) :
    (∃ θ, ∃ hθ : θ < 1, (ymBox T g θ hθ).DMPComplete g.k₀) ↔
      ∃ γ, 0 ≤ γ ∧ γ < 1 ∧ ∀ k, g.k₀ ≤ k → LevelBox T g γ k := by
  constructor
  · rintro ⟨θ, hθ, h⟩
    have H := (chainBox_complete_iff _ _ _ _ _ _ _).1 h
    refine ⟨(max θ 0 + 1) / 2, by positivity, by linarith [max_lt hθ one_pos], fun k hk => ?_⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
    refine levelBox_of_ymFac_lt ?_ (by linarith [max_lt hθ one_pos])
    linarith [H n, le_max_left θ 0, max_lt hθ one_pos]
  · rintro ⟨γ, h0, h1, H⟩
    exact ⟨γ, h1, (chainBox_complete_iff _ _ _ _ _ _ _).2 fun n => ymFac_le h0 h1 (H _ (Nat.le_add_right _ _))⟩

/-- **`FineOneBox` is exactly DMP-completeness of the Yang-Mills box** for some valid geometry and margin. Both
directions: the general class carries exactly the one-box criterion. -/
theorem fineOneBox_iff_complete (T : Tuning) :
    FineOneBox T ↔ ∃ g : Geo T, g.Valid ∧ ∃ θ, ∃ hθ : θ < 1, (ymBox T g θ hθ).DMPComplete g.k₀ := by
  rw [fineOneBox_iff]
  exact exists_congr fun g => and_congr_right fun _ => (ym_complete_iff T g).symm

/-- **`FineOneBox` gives the correct marker at every scale**: at every level from `k₀` (every volume inside the level
criterion), the claim `inside` is the gate's verdict. -/
theorem fineOneBox_correct (T : Tuning) (h : FineOneBox T) :
    ∃ g : Geo T, g.Valid ∧ ∃ θ, ∃ hθ : θ < 1, ∀ k, g.k₀ ≤ k → (ymBox T g θ hθ).Correct k := by
  obtain ⟨g, hg, θ, hθ, hc⟩ := (fineOneBox_iff_complete T).1 h
  refine ⟨g, hg, θ, hθ, fun k hk => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  have := hc n
  rwa [show (ymBox T g θ hθ).S.step^[n] g.k₀ = g.k₀ + n from Nat.succ_iterate _ _] at this

/-- **DMP-complete Yang-Mills box ⇒ the one-box assembly**: with the line of constant physics and non-triviality (the
lower edge, conditional on III.64), decay, the gap in both orders of limits, reflection positivity. -/
theorem ym_assembly_of_complete {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T)
    (h : ∃ g : Geo T, g.Valid ∧ ∃ θ, ∃ hθ : θ < 1, (ymBox T g θ hθ).DMPComplete g.k₀) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T :=
  yang_mills_assembly_onebox hL hN ((fineOneBox_iff_complete T).2 h)

end Fine

/-! ## 4. Navier-Stokes: the wrong marker at some scale -/

/-- The gate factor at dyadic scale `k`: the energy-only transfer bound `K 2^{5k/2}` over the viscous cost `ν 4^k`,
clipped to `[0, 1]`. -/
def nsFac (ν K : ℝ) (k : ℕ) : ℝ := max 0 (min 1 (K * √2 ^ (5 * k) / (ν * 4 ^ k)))

theorem nsFac_nonneg (ν K : ℝ) (k : ℕ) : 0 ≤ nsFac ν K k := le_max_left _ _

theorem nsFac_le_one (ν K : ℝ) (k : ℕ) : nsFac ν K k ≤ 1 := max_le zero_le_one (min_le_left _ _)

/-- **The Navier-Stokes box**: dyadic scales, gate factor `nsFac`, floor `0`, margin `θ < 1`, claim `inside` at every
scale (regularity). -/
def nsBox (ν K θ : ℝ) (hθ : θ < 1) : Box.{0} 0 :=
  chainBox (nsFac ν K) (nsFac_nonneg ν K) (nsFac_le_one ν K) le_rfl θ (by rwa [Real.exp_zero, one_mul])
    fun _ => .inside

/-- At a scale where the transfer bound overtakes the viscous cost the gate factor is `1`. -/
theorem nsFac_eq_one {ν K : ℝ} (hν : 0 < ν) {k : ℕ} (hk : ν * 4 ^ k < K * √2 ^ (5 * k)) : nsFac ν K k = 1 := by
  have h1 : 1 ≤ K * √2 ^ (5 * k) / (ν * 4 ^ k) := (one_le_div (by positivity)).2 hk.le
  unfold nsFac
  rw [min_eq_left h1, max_eq_right zero_le_one]

/-- **Navier-Stokes: the gate reads `r136a1` at some scale** (from VII.3.4b, `dyadic_supercritical`), for every `ν, K > 0`
and every margin `θ < 1`. -/
theorem ns_gate_outside {ν K θ : ℝ} (hν : 0 < ν) (hK : 0 < K) (hθ : θ < 1) :
    ∃ k : ℕ, (nsBox ν K θ hθ).gate k = .r136a1 := by
  obtain ⟨k, hk⟩ := API.NavierStokes.dyadic_supercritical ν hK
  refine ⟨k, ((nsBox ν K θ hθ).gate_eq_r136a1_iff k).2 ?_⟩
  show θ < nsFac ν K k
  rw [nsFac_eq_one hν hk]
  exact hθ

/-- **Navier-Stokes: the marker `inside` is wrong at some scale**, so the box is not DMP-complete (from VII.3.4b; model
level: the transfer bound and the viscous cost are given as exponents). -/
theorem ns_wrong_marker {ν K θ : ℝ} (hν : 0 < ν) (hK : 0 < K) (hθ : θ < 1) :
    ∃ k : ℕ, ¬ (nsBox ν K θ hθ).Correct k := by
  obtain ⟨k, hk⟩ := ns_gate_outside hν hK hθ
  exact ⟨k, fun h => Marker.noConfusion (h.trans hk)⟩

theorem ns_not_complete {ν K θ : ℝ} (hν : 0 < ν) (hK : 0 < K) (hθ : θ < 1) :
    ¬ (nsBox ν K θ hθ).DMPComplete (0 : ℕ) := fun h => by
  obtain ⟨k, hk⟩ := API.NavierStokes.dyadic_supercritical ν hK
  have := (chainBox_complete_iff _ _ _ _ _ _ 0).1 h k
  rw [zero_add, nsFac_eq_one hν hk] at this
  linarith

/-! ## 5. The half-turn of the plaquette layer -/

section HalfTurn

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- **The plaquette gate at the cell `q`**: states are boxes `R` of plaquettes; the flux read from inside is the
coboundary of the closed layer `τ` restricted to `R`, the flux after the half-turn the one restricted to the complement.
The flux law is `cob_restrict_eq_cob_restrict_compl`. -/
def crossoverGate (inc : Q → Finset P) (τ : P → ZMod 2) (h : Crossover.Closed inc τ) (q : Q) :
    Gate (Finset P) (ZMod 2) where
  inner R := Crossover.cob inc (Crossover.restrictTo R τ) q
  outer R := Crossover.cob inc (Crossover.restrictTo Rᶜ τ) q
  flux R := (Crossover.cob_restrict_eq_cob_restrict_compl h R q).symm

/-- **The outside is read through the same gate**: any verdict on the flux read after the half-turn is the verdict read
from inside. -/
theorem crossover_halfTurn (inc : Q → Finset P) (τ : P → ZMod 2) (h : Crossover.Closed inc τ) (q : Q)
    (v : ZMod 2 → Marker) (R : Finset P) :
    v (Crossover.cob inc (Crossover.restrictTo Rᶜ τ) q) = v (Crossover.cob inc (Crossover.restrictTo R τ) q) :=
  (crossoverGate inc τ h q).halfTurn v R

end HalfTurn

/-! ## 6. The round in one statement -/

/-- **The rotation round.** (1) One-box certificate. (2) Scale certificate from III.64 (a named hypothesis). (3) The ETM is a
box whose DMP-completeness is undecidable over descriptions. (4) O1, chain form, is exactly DMP-completeness of the O1
boxes. (5) `FineOneBox` is exactly DMP-completeness of the Yang-Mills box for some valid geometry. (6) Navier-Stokes has
a wrong marker at some scale (model, VII.3.4b). -/
theorem rotation_round :
    (∀ (δ : ℝ) (B : Box.{0} δ) (x₀ : B.S.X), B.Correct x₀ → (∀ x, B.Correct x → B.Correct (B.S.step x)) →
      B.DMPComplete x₀) ∧
    (∀ (δ : ℝ) (B : Box.{0} δ) (x₀ : B.S.X) (ι : Type) (C : ι → Box.{0} δ) (x : ∀ j, (C j).S.X),
      B.DMPComplete x₀ → SharedGate B x₀ C x → ∀ j, (C j).DMPComplete (x j)) ∧
    (∀ n, ¬ ComputablePred fun c : Nat.Partrec.Code => etmBox.DMPComplete (start c n)) ∧
    (∀ (Ω : Type) (Fe : Ω → ℝ) (μ : ℝ) (hμ : 1 ≤ μ), Unified.YMOneBox Fe μ ↔
      ∃ θ, ∃ hθ : Real.exp (Real.log μ) * θ < 1, ∀ ω : ℕ → Ω, (o1Box Fe hμ θ hθ ω).DMPComplete (0 : ℕ)) ∧
    (∀ T : Tuning, ProofPhase.OneBox.FineOneBox T ↔
      ∃ g : Geo T, g.Valid ∧ ∃ θ, ∃ hθ : θ < 1, (ymBox T g θ hθ).DMPComplete g.k₀) ∧
    (∀ ν K θ : ℝ, 0 < ν → 0 < K → ∀ hθ : θ < 1, ¬ (nsBox ν K θ hθ).DMPComplete (0 : ℕ)) :=
  ⟨fun _ B _ h0 hs => B.onebox_certificate h0 hs, fun _ B _ _ C x hB h => scale_certificate B C x hB h,
    etmBox_complete_undecidable, fun _ Fe _ hμ => o1_iff_complete Fe hμ, fineOneBox_iff_complete,
    fun _ _ _ hν hK hθ => ns_not_complete hν hK hθ⟩

end ProofPhase.ETM
