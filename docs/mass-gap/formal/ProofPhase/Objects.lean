/-
Proof phase (round 5), the assembly: the concrete objects (2026-11-22). Released under Apache 2.0.

Map: `docs/mass-gap/weak-coupling/PROOF-BLUEPRINT.md`; field-by-field: `docs/mass-gap/weak-coupling/proof-phase/ASSEMBLY.md`.
-/

import OneScale
import Positivity
import Attempts.R4.LayerKernel
import ProofPhase.RouteB.FluxEnergy

/-!
# The objects of the assembly: SU(2) Yang–Mills on the 4D torus along a line of constant physics, and the mass gap

Everything here is a definition about the **real** lattice theory, built from the existing libraries:

* **Group.** `SU2 = Matrix.specialUnitaryGroup (Fin 2) ℂ` with its normalised Haar measure (`AreaLaw.Concrete`). The
  generic definitions (`wilsonWeight`, `wilsonMeasure`, `GaugeInvariant`) are stated for every compact group with a
  continuous unitary representation, as in `OneScale`; the line of constant physics, the observables and the gap are
  stated for SU(2) only. The Clay problem asks for every compact simple group: see `ASSEMBLY.md` (missing piece G).
* **Lattice and measure.** The periodic lattice `(ℤ/Nℤ)⁴` (`LatticeLink 4 N`), the Wilson weight `x ↦ e^{βx}` of
  `Re tr U_p`, and the normalised Wilson measure `wilsonMeasure G n β = gaugeMeasure n (wilsonWeight β)`
  (`OneScale.Gauge.gaugeMeasure`: `Z⁻¹ ∏_p e^{β Re tr U_p}` times the product Haar measure).
* **The family along a line of constant physics (`Tuning`).** Data: a physical length `L₁ > 0`, a resolution
  `ℓ_k ≥ 1` (lattice steps per length `L₁` at level `k`) and a bare coupling `β_k`. The lattice spacing is
  `a_k = L₁/ℓ_k` (so `L₁` is the physical unit). Volumes: at level `k` the torus `j` has side
  `side k j = 2(j+1)·ℓ_k`, i.e. physical side `2(j+1)·L₁`, even (reflection positivity needs it). The relation of the
  data to a physical scale is **not** part of the data: it is the open piece P6.6 (`OnLCP` in `Assembly.lean`), so that
  a mistuned or trivial family (e.g. `β_k = 0`, pure noise) is still a `Tuning` and can be shown to fail the hypotheses.
* **Observables.** `SlabObs T s V`: at every level `k` and volume `j`, a measurable gauge-invariant function of the
  field with `|F| ≤ 1`, depending only on the links of the time slab `[0, ⌈s/a_k⌉]` (physical thickness `s`) and on at
  most `V k` links (local). Slabs are the observables of reflection positivity; spatially they are arbitrary.
* **Correlation.** `wcorr T k j F n = Cov(F ∘ S_n, F ∘ Θ)` under the Wilson measure (`OneScale.TimeShift.corr`): the
  connected correlation of `F` translated by `n` lattice steps in time with its time reflection. Physical time `n·a_k`.
* **Limits.** `IsLimitPoint u h`: `h` is the limit of a subsequence of `u`. All gap statements are made for **every**
  limit point, so no convergence, uniqueness or identification of the limit is assumed anywhere.

## The mass gap (precise)

* `LatticeGap T` (what the chain delivers): there is `m > 0` such that for every slab thickness `s` and support bound
  `V`, from some level on, every infinite-volume limit point `h` (torus `j → ∞` at fixed level `k`) of the reflected
  correlation at lattice time `n` satisfies `|h| ≤ 2 e^{-m n a_k}`. Order of limits: volume first, then lattice spacing.
* **`MassGap T`** (the continuum statement): there is `m > 0` such that for every slab observable family, every physical
  time `τ ≥ 0`, every choice of infinite-volume limit points `h_k` at lattice time `⌊τ/a_k⌋` and every limit point `g`
  of `h_k` as `k → ∞`: `|g| ≤ 2 e^{-m τ}`. `LatticeGap` implies `MassGap` once `a_k → 0` (`massGap_of_latticeGap`).

**Neither vacuous nor stronger than the Clay gap.** Not vacuous: the correlations are bounded by `2` (`abs_wcorr_le`),
so limit points exist for every family, and the bound fails for any theory whose limit correlations decay slower than
exponentially (the free photon). Not stronger: the limit functional `F ↦ g` is reflection positive (`limitRP`, proved
below from lattice reflection positivity) and time-translation invariant, so it defines (Osterwalder–Schrader) a
Hilbert space with a transfer matrix `e^{-τH}`, `H ≥ 0`, and the reflected correlation is
`⟨Θ F Ω, e^{-τH}(1 − P_Ω) F Ω⟩`; if `H` has the spectral gap `Δ` on `Ω^⊥` (the Clay gap of the theory so defined), this is
at most `‖F‖² e^{-Δτ} ≤ e^{-Δτ}`, so `MassGap` holds with `m = Δ`. Conversely, `MassGap` with rate `m` says the
spectral measure of every slab vector `F Ω` on `Ω^⊥` gives no mass to `[0, m)` (`spectral_gap_of_decay`, proved below
for a finite measure on `[0, ∞)`), and slab vectors are dense in the OS Hilbert space, so the spectral gap is at least `m`.
So **`MassGap` is equivalent to the spectral gap of the reconstructed continuum theory, given the OS reconstruction of
the limit** (P6.5, standard once the limit is a state on a field algebra; see `ASSEMBLY.md`). It is a statement about
every limit point (no uniqueness), in the order volume first, then spacing; it does not by itself say that the limit is
non-trivial (P6.2) or Euclidean invariant (P6.4).

## Other objects

* `blocked_wilson_rp`: reflection positivity of the image of the Wilson measure under **any** measurable blocking that
  commutes with the time reflection and maps the closed positive half to the closed positive half (generalises
  `Attempts.R4.Layer.decimated_wilson_rp`, whose proof used only these two properties). With it, reflection positivity
  at every level is a property of the blocking, not an open piece (P1.6 for every such blocking).
* **The flux energy from the 4D measure** (cycle 2, replacing the transfer-operator definition in the assembly):
  `IsFluxLimitSU2 β L h` says `h` is a time limit (time extent `T → ∞` along a subsequence, spatial box `(ℤ/Lℤ)³` fixed)
  of the normalised correlation of the centre-odd Polyakov sum on the anisotropic SU(2) Wilson torus
  `ℤ/Tℤ × (ℤ/Lℤ)³` (`ProofPhase.RouteB.IsFluxLimit`, workstream 2); limits exist (`exists_fluxLimitSU2`); the act
  number of `h` is `actRate L h = L · fluxRate h` (`fluxRate h` = the limit of the effective masses, the exact decay rate
  of `h`, `RouteB.fluxEnergy_props`). No transfer operator, no Gauss-law projection, no `Z = tr(P_G Tⁿ)` is needed.
  Uniqueness of the time limit is not proved (Perron–Frobenius for the finite-box transfer matrix, standard), so the
  assembly states every flux condition **for every time limit**; when `h` vanishes from some time on, `fluxRate h` is a
  junk value, which can only make such a condition harder to satisfy.
* `gaugeInvQ`, `fluxE`, `actZ` (kept, no longer used by the assembly): the electric-flux energy of the SU(2)
  temporal-gauge transfer operator on Gauss-law states (`Attempts.R4.Layer.fluxEnergy`) and `z = L·E_e`; its
  identification with the 4D Wilson measure (`Z = tr(P_G Tⁿ)`) is not formalised.
* **Observables of bounded physical extent** (cycle 2): `SlabObs.Extent O R` says that at every level and volume any two
  links of the support of `O` are at physical distance `≤ R` (`a_k · linkDist ≤ R`); the number of fine links is not
  bounded. `MassGapLoc T` is `MassGap T` for these families (every `R`, one rate). It is implied by `MassGap`
  (`massGapLoc_of_massGap`) and is the form the Clay gap needs: the vectors `F Ω` of local observables of bounded extent
  are dense in the reconstructed Hilbert space (see `ASSEMBLY.md`).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase

/-! ## Generic objects (any compact group with a continuous unitary representation) -/

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] {n : ℕ} [HasGaugeTrace G n]

/-- The Wilson plaquette weight `x ↦ e^{β x}` (applied to `x = Re tr U_p`). -/
def wilsonWeight (β : ℝ) : ℝ → ℝ := fun x => Real.exp (β * x)

theorem posWeight_wilson (n : ℕ) (β : ℝ) : PosWeight n (wilsonWeight β) := posWeight_exp n β

/-- **The Wilson measure** on `(ℤ/Nℤ)^d` at bare coupling `β`: `Z⁻¹ ∏_p e^{β Re tr U_p}` times product Haar. -/
abbrev wilsonMeasure (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (d N : ℕ)
    [NeZero N] : Measure (GaugeConnection G d N) :=
  gaugeMeasure (d := d) (N := N) (G := G) n (wilsonWeight β)

/-- A function of the gauge field is **gauge invariant**. -/
def GaugeInvariant {d N : ℕ} (F : GaugeConnection G d N → ℝ) : Prop :=
  ∀ (g : GaugeTransform G d N) (U : GaugeConnection G d N), F (gaugeTransformConnection g U) = F U

end Generic

/-- `h` is a **limit point** of the real sequence `u`: the limit of some subsequence. -/
def IsLimitPoint (u : ℕ → ℝ) (h : ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 h)

theorem IsLimitPoint.le {u : ℕ → ℝ} {h B : ℝ} (hu : ∀ᶠ k in atTop, u k ≤ B) (hh : IsLimitPoint u h) : h ≤ B := by
  obtain ⟨φ, hφ, ht⟩ := hh
  exact le_of_tendsto ht (hφ.tendsto_atTop.eventually hu)

theorem IsLimitPoint.abs_le {u : ℕ → ℝ} {h B : ℝ} (hu : ∀ᶠ k in atTop, |u k| ≤ B) (hh : IsLimitPoint u h) :
    |h| ≤ B := by
  obtain ⟨φ, hφ, ht⟩ := hh
  exact le_of_tendsto ht.abs (hφ.tendsto_atTop.eventually hu)

/-! ## The family along a line of constant physics (data only) -/

/-- **A tuning**: physical unit `L₁ > 0`, resolution `ℓ_k ≥ 1` lattice steps per `L₁`, bare coupling `β_k`. The lattice
spacing is `a_k = L₁ / ℓ_k`. Whether the family lies on a line of constant physics is the open piece P6.6
(`ProofPhase.OnLCP`), not part of the data. -/
structure Tuning where
  L₁ : ℝ
  L₁_pos : 0 < L₁
  ℓ : ℕ → ℕ
  ℓ_pos : ∀ k, 0 < ℓ k
  β : ℕ → ℝ

namespace Tuning

variable (T : Tuning)

/-- The lattice spacing `a_k = L₁/ℓ_k`. -/
def a (k : ℕ) : ℝ := T.L₁ / T.ℓ k

theorem a_pos (k : ℕ) : 0 < T.a k := div_pos T.L₁_pos (by exact_mod_cast T.ℓ_pos k)

/-- The fine side of torus `j` at level `k`: `2(j+1)·ℓ_k` (physical side `2(j+1) L₁`). -/
def side (k j : ℕ) : ℕ := 2 * (j + 1) * T.ℓ k

instance (k j : ℕ) : NeZero (T.side k j) := ⟨by unfold side; have := T.ℓ_pos k; positivity⟩

theorem even_side (k j : ℕ) : Even (T.side k j) := by
  unfold side; rw [mul_assoc]; exact even_two_mul _

theorem le_side (k j : ℕ) : j ≤ T.side k j := by
  unfold side; have := T.ℓ_pos k; nlinarith

theorem tendsto_side (k : ℕ) : Tendsto (T.side k) atTop atTop :=
  tendsto_atTop_mono (T.le_side k) tendsto_id

/-- The slab of physical thickness `s` in lattice steps: `⌈s/a_k⌉`. -/
def thick (k : ℕ) (s : ℝ) : ℕ := ⌈s / T.a k⌉₊

/-- Physical time `τ` in lattice steps: `⌊τ/a_k⌋`. -/
def steps (k : ℕ) (τ : ℝ) : ℕ := ⌊τ / T.a k⌋₊

theorem steps_mul_ge (k : ℕ) {τ : ℝ} (_hτ : 0 ≤ τ) : τ - T.a k ≤ (T.steps k τ : ℝ) * T.a k := by
  have ha := T.a_pos k
  have h := Nat.lt_floor_add_one (τ / T.a k)
  have : τ / T.a k - 1 ≤ (T.steps k τ : ℝ) := by unfold steps; linarith
  have e : τ - T.a k = (τ / T.a k - 1) * T.a k := by field_simp
  rw [e]; exact mul_le_mul_of_nonneg_right this ha.le

/-- The SU(2) Wilson measure at level `k` on torus `j`. -/
abbrev ym (k j : ℕ) : Measure (GaugeConnection SU2 4 (T.side k j)) := wilsonMeasure SU2 2 (T.β k) 4 (T.side k j)

/-- The reflected connected correlation at level `k`, torus `j`, lattice time `n`: `Cov(F ∘ S_n, F ∘ Θ)`. -/
def wcorr (k j : ℕ) (F : GaugeConnection SU2 4 (T.side k j) → ℝ) (n : ℕ) : ℝ :=
  corr (d := 4) (N := T.side k j) (G := SU2) 2 (wilsonWeight (T.β k)) F n

end Tuning

/-! ## Observables -/

/-- **Slab observables** of physical thickness `s` with at most `V k` links at level `k`: for every level and volume a
measurable, gauge-invariant function of the SU(2) field with `|F| ≤ 1`, depending only on the time slab `[0, ⌈s/a_k⌉]`
and on a set of at most `V k` links. -/
structure SlabObs (T : Tuning) (s : ℝ) (V : ℕ → ℕ) where
  F : ∀ k j, GaugeConnection SU2 4 (T.side k j) → ℝ
  meas : ∀ k j, Measurable (F k j)
  bdd : ∀ k j U, |F k j U| ≤ 1
  gauge : ∀ k j, GaugeInvariant (F k j)
  slab : ∀ k j, DepOn (F k j) (timeSlab 0 (T.thick k s))
  supp : ∀ k j, Finset (LatticeLink 4 (T.side k j))
  supp_card : ∀ k j, (supp k j).card ≤ V k
  dep : ∀ k j, DepOn (F k j) (supp k j)

theorem SlabObs.bm {T : Tuning} {s : ℝ} {V : ℕ → ℕ} (O : SlabObs T s V) (k j : ℕ) : BM (O.F k j) :=
  ⟨O.meas k j, 1, O.bdd k j⟩

/-! ## The gap -/

/-- **Lattice-uniform gap** (volume first, then spacing): one physical rate `m > 0`; for every thickness `s` and support
bound `V`, from some level `k₀` on, every infinite-volume limit point of the reflected correlation at lattice time `n` is
at most `2 e^{-m n a_k}`. -/
def LatticeGap (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s : ℝ) (V : ℕ → ℕ), ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (O : SlabObs T s V) (n : ℕ) (h : ℝ),
    IsLimitPoint (fun j => T.wcorr k j (O.F k j) n) h → |h| ≤ 2 * Real.exp (-(m * (n * T.a k)))

/-- **The mass gap of the continuum limit** (precise form; see the module docstring for why it is neither vacuous nor
stronger than the Clay gap). One rate `m > 0`; for every slab observable family, every physical time `τ ≥ 0`, every
choice of infinite-volume limit points `h k` at lattice time `⌊τ/a_k⌋`, and every limit point `g` of `h` as `k → ∞`:
`|g| ≤ 2 e^{-m τ}`. -/
def MassGap (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s : ℝ) (V : ℕ → ℕ) (O : SlabObs T s V) (τ : ℝ), 0 ≤ τ → ∀ (h : ℕ → ℝ) (g : ℝ),
    (∀ k, IsLimitPoint (fun j => T.wcorr k j (O.F k j) (T.steps k τ)) (h k)) → IsLimitPoint h g →
      |g| ≤ 2 * Real.exp (-(m * τ))

/-- `LatticeGap` gives `MassGap` once the lattice spacing goes to zero. -/
theorem massGap_of_latticeGap {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : LatticeGap T) : MassGap T := by
  obtain ⟨m, hm, hgap⟩ := h
  refine ⟨m, hm, fun s V O τ hτ hk g hhk hg => ?_⟩
  obtain ⟨k₀, hk₀⟩ := hgap s V
  -- for `k ≥ k₀`: `|h k| ≤ 2 e^{-m (τ - a_k)}`
  have hb : ∀ k, k₀ ≤ k → |hk k| ≤ 2 * Real.exp (-(m * (τ - T.a k))) := by
    intro k hkk
    refine (hk₀ k hkk O _ _ (hhk k)).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
    have := T.steps_mul_ge k hτ
    nlinarith
  obtain ⟨φ, hφ, ht⟩ := hg
  have hlim : Tendsto (fun k => 2 * Real.exp (-(m * (τ - T.a (φ k))))) atTop (𝓝 (2 * Real.exp (-(m * τ)))) := by
    have h1 : Tendsto (fun k => T.a (φ k)) atTop (𝓝 0) := ha.comp hφ.tendsto_atTop
    have h2 : Tendsto (fun k => -(m * (τ - T.a (φ k)))) atTop (𝓝 (-(m * (τ - 0)))) :=
      ((tendsto_const_nhds.sub h1).const_mul m).neg
    rw [sub_zero] at h2
    exact (Real.continuous_exp.tendsto _ |>.comp h2).const_mul 2
  refine le_of_tendsto_of_tendsto ht.abs hlim ?_
  filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop k₀)] with k hk
  exact hb (φ k) hk

/-! ## Bounds and positivity at every level -/

section Level

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n] [HasHaarProbability G] [(haarG G).IsInvInvariant]

/-- A covariance of two functions bounded by one under a probability measure is at most `2`. -/
theorem abs_cov_le_two {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hf1 : ∀ x, |f x| ≤ 1) (hg1 : ∀ x, |g x| ≤ 1) :
    |∫ x, f x * g x ∂μ - (∫ x, f x ∂μ) * ∫ x, g x ∂μ| ≤ 2 := by
  have i1 : |∫ x, f x * g x ∂μ| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f x * g x) (C := 1)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]; nlinarith [hf1 x, hg1 x, abs_nonneg (f x), abs_nonneg (g x)])
    simpa using this
  have i2 : |∫ x, f x ∂μ| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := 1)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hf1 x)
    simpa using this
  have i3 : |∫ x, g x ∂μ| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := g) (C := 1)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hg1 x)
    simpa using this
  have i4 : |(∫ x, f x ∂μ) * ∫ x, g x ∂μ| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg (∫ x, f x ∂μ), abs_nonneg (∫ x, g x ∂μ)]
  calc _ ≤ |∫ x, f x * g x ∂μ| + |(∫ x, f x ∂μ) * ∫ x, g x ∂μ| := abs_sub _ _
    _ ≤ 2 := by linarith

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

include hc hU in
/-- The reflected correlation of a function bounded by one is at most `2` in absolute value. -/
theorem abs_corr_le_two {φ : ℝ → ℝ} (hφ : PosWeight n φ) {F : GaugeConnection G d N → ℝ} (hF : Measurable F)
    (hF1 : ∀ U, |F U| ≤ 1) (m : ℕ) : |corr n φ F m| ≤ 2 := by
  have := isProbabilityMeasure_gaugeMeasure (d := d) (N := N) hc hU hφ
  exact abs_cov_le_two _ (hF.comp (measurable_tShift _)) (hF.comp measurePreserving_thetaConn.measurable)
    (fun U => hF1 _) (fun U => hF1 _)

variable (hN : Even N)

include hc hU hN in
/-- **Reflection positivity at every level, normalised:** `∫ F · (F ∘ Θ) dμ_φ ≥ 0` for bounded measurable `F` of the
closed positive half, every weight in class (Φ) (Wilson at every `β`). -/
theorem rp_gaugeMeasure {φ : ℝ → ℝ} (hφ : PosWeight n φ) {F : GaugeConnection G d N → ℝ}
    (hF : LinkDep F (posHalfLinks d N)) (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaConn U) ∂(gaugeMeasure n φ) := by
  have hZ := partZ_pos (d := d) (N := N) hc hU hφ
  have e := rpForm_eq (d := d) (N := N) hc hU hφ F F
  have h0 : 0 ≤ TorusRP.rpForm n φ F F :=
    rp_plaquette_weight hN hc hU (plaqWeight_of_posWeight hφ) hF mF bF
  rw [e] at h0
  exact nonneg_of_mul_nonneg_right (by linarith) hZ

end Level

theorem Tuning.abs_wcorr_le (T : Tuning) (k j : ℕ) {F : GaugeConnection SU2 4 (T.side k j) → ℝ} (hF : Measurable F)
    (hF1 : ∀ U, |F U| ≤ 1) (n : ℕ) : |T.wcorr k j F n| ≤ 2 :=
  abs_corr_le_two (d := 4) continuous_subtype_val (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
    (posWeight_wilson 2 (T.β k)) hF hF1 n

/-- **Reflection positivity of every continuum limit point (the positivity half of P6.3, proved).** For every family
of bounded measurable functions of the closed positive half (`t ∈ [0, N/2]`), every choice of infinite-volume limit
points `h k` of the reflected forms `⟨F, Θ F⟩` at level `k`, and every limit point `g` of `h`: `g ≥ 0`. Proved from
lattice reflection positivity (`Positivity.rp_plaquette_weight`) at every level and closedness. -/
def LimitRP (T : Tuning) : Prop :=
  ∀ (F : ∀ k j, GaugeConnection SU2 4 (T.side k j) → ℝ),
    (∀ k j, LinkDep (F k j) (posHalfLinks 4 (T.side k j)) ∧ Measurable (F k j) ∧ ∃ M, ∀ U, |F k j U| ≤ M) →
    ∀ (h : ℕ → ℝ) (g : ℝ),
      (∀ k, IsLimitPoint (fun j => ∫ U, F k j U * F k j (thetaConn U) ∂(T.ym k j)) (h k)) → IsLimitPoint h g → 0 ≤ g

theorem IsLimitPoint.nonneg {u : ℕ → ℝ} {h : ℝ} (hu : ∀ k, 0 ≤ u k) (hh : IsLimitPoint u h) : 0 ≤ h := by
  obtain ⟨φ, _, ht⟩ := hh
  exact ge_of_tendsto' ht (fun k => hu (φ k))

theorem limitRP (T : Tuning) : LimitRP T := by
  intro F hF h g hh hg
  have hk : ∀ k, 0 ≤ h k := fun k =>
    (hh k).nonneg fun j => rp_gaugeMeasure (d := 4) (N := T.side k j) continuous_subtype_val
      (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (T.even_side k j) (posWeight_wilson 2 (T.β k))
      (hF k j).1 (hF k j).2.1 (hF k j).2.2
  exact hg.nonneg hk

/-! ## The spectral reading -/

/-- **The spectral reading of the gap.** If a finite measure `μ` on `ℝ` (the spectral measure of a vector for a
self-adjoint `H ≥ 0`, so `μ` lives on `[0, ∞)`) has Laplace transform decaying at rate `m`,
`∫ e^{-tλ} dμ(λ) ≤ C e^{-mt}` for all `t ≥ 0`, then `μ` gives no mass to `[0, m)`: the spectrum seen by that vector
starts at `m`. Applied to the vectors `(1 − P_Ω) F Ω` of the slab observables (dense in the OS Hilbert space) this turns
`MassGap` into the spectral gap. -/
theorem spectral_gap_of_decay (μ : Measure ℝ) [IsFiniteMeasure μ] (h0 : μ (Set.Iio 0) = 0) {C m : ℝ}
    (hdec : ∀ t : ℝ, 0 ≤ t → ∫ x, Real.exp (-(t * x)) ∂μ ≤ C * Real.exp (-(m * t))) :
    μ (Set.Iio m) = 0 := by
  have hae : ∀ᵐ x ∂μ, 0 ≤ x := by
    rw [ae_iff]
    have e : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
    rw [e]; exact h0
  have hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun x => Real.exp (-(t * x))) μ := by
    intro t ht
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [hae] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by nlinarith)
  -- the mass of `[0, m')` vanishes for every `m' < m`
  have hpiece : ∀ m' : ℝ, m' < m → μ (Set.Ico 0 m') = 0 := by
    intro m' hm'
    have hb : ∀ t : ℝ, 0 ≤ t → μ.real (Set.Ico 0 m') ≤ C * Real.exp (-((m - m') * t)) := by
      intro t ht
      have h1 : Real.exp (-(t * m')) * μ.real (Set.Ico 0 m') ≤ ∫ x in Set.Ico 0 m', Real.exp (-(t * x)) ∂μ :=
        setIntegral_ge_of_const_le_real measurableSet_Ico (measure_ne_top _ _)
          (fun x hx => Real.exp_le_exp.2 (by nlinarith [hx.2])) (hint t ht).integrableOn
      have h2 : ∫ x in Set.Ico 0 m', Real.exp (-(t * x)) ∂μ ≤ ∫ x, Real.exp (-(t * x)) ∂μ :=
        setIntegral_le_integral (hint t ht) (Eventually.of_forall fun x => (Real.exp_pos _).le)
      have h3 := (h1.trans h2).trans (hdec t ht)
      have e : C * Real.exp (-(m * t)) = Real.exp (-(t * m')) * (C * Real.exp (-((m - m') * t))) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      rw [e] at h3
      exact le_of_mul_le_mul_left h3 (Real.exp_pos _)
    have hlim : Tendsto (fun t : ℝ => C * Real.exp (-((m - m') * t))) atTop (𝓝 (C * 0)) := by
      refine tendsto_const_nhds.mul ?_
      have h1 : Tendsto (fun t : ℝ => (m - m') * t) atTop atTop :=
        Tendsto.const_mul_atTop (sub_pos.2 hm') tendsto_id
      exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
    rw [mul_zero] at hlim
    have hle : μ.real (Set.Ico 0 m') ≤ 0 :=
      ge_of_tendsto hlim ((eventually_ge_atTop 0).mono fun t ht => hb t ht)
    have h0' : μ.real (Set.Ico 0 m') = 0 := le_antisymm hle measureReal_nonneg
    rwa [measureReal_eq_zero_iff (measure_ne_top _ _)] at h0'
  -- `[0, m) = ⋃_i [0, m - 1/(i+1))`
  have hsub : Set.Iio m ⊆ Set.Iio 0 ∪ ⋃ i : ℕ, Set.Ico 0 (m - 1 / ((i : ℝ) + 1)) := by
    intro x hx
    rcases lt_or_ge x 0 with h | h
    · exact Or.inl h
    · obtain ⟨i, hi⟩ := exists_nat_one_div_lt (sub_pos.2 (Set.mem_Iio.1 hx))
      exact Or.inr (Set.mem_iUnion.2 ⟨i, h, by linarith⟩)
  refine measure_mono_null hsub (measure_union_null h0 (measure_iUnion_null fun i => hpiece _ ?_))
  have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
  linarith

/-! ## Reflection positivity of a blocked layer -/

section Blocked

variable {d M N : ℕ} [NeZero d] [NeZero M] [NeZero N]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n] [HasHaarProbability G] [(haarG G).IsInvInvariant]

/-- **A reflection-respecting blocking** from `(ℤ/Nℤ)^d` to `(ℤ/Mℤ)^d`: measurable, commuting with the site reflection
`Θ`, and reading only the closed positive half for coarse observables of the closed positive half. Decimation is one
(`Attempts.R4.Layer.decimate`); a blocking that averages freely inside each time slice and decimates in time is another
(not constructed here). -/
structure RPBlocking (G : Type*) [Group G] [MeasurableSpace G] (d N M : ℕ) [NeZero d] [NeZero N] [NeZero M] where
  B : GaugeConnection G d N → GaugeConnection G d M
  meas : Measurable B
  theta : ∀ U, B (thetaConn U) = thetaConn (B U)
  half : ∀ F : GaugeConnection G d M → ℝ, LinkDep F (posHalfLinks d M) →
    LinkDep (fun U => F (B U)) (posHalfLinks d N)

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

include hc hU in
/-- **T38 for every reflection-respecting blocking** (generalises `Attempts.R4.Layer.decimated_wilson_rp`): the image
of the Wilson measure on an even torus under `B` is reflection positive for every bounded measurable coarse observable
of the closed coarse positive half. -/
theorem blocked_wilson_rp (hN : Even N) (P : RPBlocking G d N M) (β : ℝ) {F : GaugeConnection G d M → ℝ}
    (hF : LinkDep F (posHalfLinks d M)) (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) :
    0 ≤ ∫ U, F (P.B U) * F (thetaConn (P.B U)) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N) := by
  simp_rw [← P.theta]
  exact wilson_rp hN hc hU β (P.half F hF) (mF.comp P.meas) (bF.imp fun C h U => h _)

end Blocked

/-! ## The flux sector (route W) -/

open Attempts.R4.Layer in
/-- Gauss's law on the spatial slice: a state is **gauge invariant**. Closed under `|·|`. -/
def gaugeInvQ {L : ℕ} (ψ : GaugeConnection SU2 3 L → ℝ) : Prop := GaugeInvariant ψ

theorem gaugeInvQ_abs {L : ℕ} (ψ : GaugeConnection SU2 3 L → ℝ) (h : gaugeInvQ ψ) : gaugeInvQ (fun x => |ψ x|) :=
  fun g U => by simp only [h g U]

open Attempts.R4.Layer in
/-- **The electric-flux energy** `E_e` (lattice units) of the SU(2) temporal-gauge Wilson transfer operator on the spatial
box `(ℤ/Lℤ)³` at bare coupling `β`, flux along the first axis, on **gauge-invariant (Gauss-law) states**. -/
def fluxE (β : ℝ) (L : ℕ) [NeZero L] : ℝ := fluxEnergy (su2Centre (ds := 3) (N := L) β 0) gaugeInvQ

/-- **The act number** `z = L · E_e` of the box of side `L` (dimensionless). -/
def actZ (β : ℝ) (L : ℕ) [NeZero L] : ℝ := L * fluxE β L

theorem fluxE_nonneg (β : ℝ) (L : ℕ) [NeZero L] : 0 ≤ fluxE β L :=
  Attempts.R4.Layer.su2_fluxEnergy_nonneg β 0 gaugeInvQ gaugeInvQ_abs

/-- The box of side `2^j ℓ_k` at level `k` (physical side `2^j L₁`). -/
def Tuning.box (T : Tuning) (k j : ℕ) : ℕ := 2 ^ j * T.ℓ k

instance (T : Tuning) (k j : ℕ) : NeZero (T.box k j) := ⟨by unfold Tuning.box; have := T.ℓ_pos k; positivity⟩

/-! ## The flux energy from the 4D measure (cycle 2) -/

/-- **`h` is a flux time limit** of the SU(2) Wilson measure at bare coupling `β` on `ℤ/Tℤ × (ℤ/Lℤ)³` (periodic spatial
box, no twist): a limit along a subsequence `T → ∞` of the normalised correlation `⟨Φ(a_t) Φ(a_0)⟩_T` of the
centre-odd Polyakov sum `Φ` (workstream 2, `ProofPhase.RouteB.IsFluxLimit`). -/
def IsFluxLimitSU2 (β : ℝ) (L : ℕ) [NeZero L] (h : ℕ → ℝ) : Prop :=
  RouteB.IsFluxLimit (G := SU2) (n := 2) L continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β ∅ h

/-- Flux time limits exist at every coupling and box size. -/
theorem exists_fluxLimitSU2 (β : ℝ) (L : ℕ) [NeZero L] : ∃ h, IsFluxLimitSU2 β L h :=
  RouteB.exists_fluxLimit (G := SU2) (n := 2) L _ _ β ∅

/-- **The act number of a flux time limit** of the box of side `L` (dimensionless): `z = L · E_e` with `E_e` the decay rate
`fluxRate h` of the centre-odd correlation (lattice units). -/
def actRate (L : ℕ) (h : ℕ → ℝ) : ℝ := L * RouteB.fluxRate h

/-! ## Observables of bounded physical extent (cycle 2) -/

/-- **A slab observable family of physical extent at most `R`**: at every level `k` and volume `j`, any two links of its
support are at physical distance `a_k · linkDist ≤ R`. The number of fine links is not restricted (it may grow like
`(R/a_k)⁴`); single-plaquette or other lattice-scale families have extent `→ 0` and are included. -/
def SlabObs.Extent {T : Tuning} {s : ℝ} {V : ℕ → ℕ} (O : SlabObs T s V) (R : ℝ) : Prop :=
  ∀ k j, ∀ e ∈ O.supp k j, ∀ e' ∈ O.supp k j, T.a k * linkDist e e' ≤ R

/-- **The mass gap for observables of bounded physical extent** (volume first, then spacing): `MassGap` restricted to
the families with `SlabObs.Extent O R` for some `R`; one rate `m` for all `R` and `s`. -/
def MassGapLoc (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s R : ℝ) (V : ℕ → ℕ) (O : SlabObs T s V), O.Extent R → ∀ (τ : ℝ), 0 ≤ τ →
    ∀ (h : ℕ → ℝ) (g : ℝ), (∀ k, IsLimitPoint (fun j => T.wcorr k j (O.F k j) (T.steps k τ)) (h k)) →
      IsLimitPoint h g → |g| ≤ 2 * Real.exp (-(m * τ))

/-- The full gap implies the gap for bounded physical extent (definitional). -/
theorem massGapLoc_of_massGap {T : Tuning} (h : MassGap T) : MassGapLoc T := by
  obtain ⟨m, hm, H⟩ := h
  exact ⟨m, hm, fun s _ V O _ τ hτ hk g hhk hg => H s V O τ hτ hk g hhk hg⟩

end ProofPhase
