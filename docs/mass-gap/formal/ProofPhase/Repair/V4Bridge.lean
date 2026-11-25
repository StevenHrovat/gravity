/-
Proof phase, cycle 5, workstream 3 (c5c-repair): the repaired W₁ inputs in the version-4 interface (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5c-repair/NOTE.md`, section 4.
-/

import ProofPhase.V4.Recursion
import ProofPhase.Repair.MulNoise

/-!
# The repairs, stated for any family of laws, landing on `LawGapBddW` / `BlockGapBddW`

Version 4 (c5a-v4) states the infrared input for an arbitrary family of laws `ρ k j` on tori of side `M j`
(`V4.LawGapW`, `V4.LawGapBddW`) and uses v3's finite-range `LevelDprimeWOn` inside strategy (a). This file gives the
weighted (no `D₁`) and general-support versions in that law-level form.

* **`LevelDprimeWwOn ρ λ`** (named hypothesis, open): weighted D′ for a family of laws. `levelDprimeWw_iff_on`
  (definitional): `LevelDprimeWw T B λ ↔ LevelDprimeWwOn (blockedLaw T B) λ`.
* **`lawGapW_of_levelDprimeWwOn`** (S) and **`lawGapBddW_of_levelDprimeWwOn`** (S): weighted D′ gives the W₁ gap of the
  family, both forms. **`blockGapBddW_of_levelDprimeWw`** (S): on the blocked laws, the v4 infrared input of record.
* `levelDprimeWwOn_of_levelDprimeWOn` (S): v4's finite-range `LevelDprimeWOn` is a special case.
* **`blockGapBddW_of_levelDprimeWwOn`** (S): strategy (a) of v4 (`V4.blockGapBddW_of_levelDprimeWOn`) with the
  weighted hypothesis at `L₁`: `LevelDprimeWwOn` of the `L₁` laws and `StageTwoW` give `BlockGapBddW` at `L_*`.
* `CloseWwOn`, **`levelDprimeWwOn_of_ref`** (S): the general-support reference pair, law-level.
* **`noisy_lawGapBddW`** (S): for a noisy blocking family, `LevelDprimeWwOn (noisyBlockedLaw NB)` gives
  `LawGapBddW (noisyBlockedLaw NB)`; `noisy_gibbs_clause` (S): with `KernelDensity` the Gibbs clause of
  `LevelDprimeWwOn` is met at every level and volume, so what remains of the hypothesis is the weighted column alone.

**Claim level.** All proved. Nothing here changes the strength of the infrared input; it removes clauses the true
blocked laws cannot meet.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.LinkDist ProofPhase.Certified
  ProofPhase.V3 ProofPhase.V4

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Repair

section Laws

variable {M : ℕ → ℕ} [∀ j, NeZero (M j)]

/-- **Weighted D′ for any family of laws** (no range clause): from some level on, in every volume, `ρ k j` is the Gibbs
measure of a bounded potential (any supports) whose single-link W₁ influences have weighted column sums `≤ γ < 1`. -/
def LevelDprimeWwOn (ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))) (lam : ℝ) : Prop :=
  ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
    ∃ V : Finset (LatticeLink 4 (M j)) → GaugeConnection SU2 4 (M j) → ℝ,
    ρ k j = Attempts.R3.gibbsMeasure (haarG SU2) V ∧ Attempts.R3.Potential (fun A => A) V ∧
    ∃ kk : LatticeLink 4 (M j) → LatticeLink 4 (M j) → ℝ,
      SiteInfluenceW (haarG SU2) (fun A => A) V geodSU2 kk ∧ WeightedColumnW kk linkDist lam γ

/-- **Weighted D′ gives the W₁ gap of the family** (S), constant `π/(1 − γ)`. -/
theorem lawGapW_of_levelDprimeWwOn {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ}
    (hlam : 0 ≤ lam) (h : LevelDprimeWwOn ρ lam) : LawGapW ρ lam := by
  obtain ⟨γ, hγ0, hγ1, k₀, H⟩ := h
  refine ⟨Real.pi / (1 - γ), div_nonneg Real.pi_pos.le (by linarith), k₀,
    fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ?_⟩
  obtain ⟨V, hgibbs, hpot, kk, hk', hcol⟩ := H k hk j
  have : Nonempty (LatticeLink 4 (M j)) := ⟨⟨fun _ => 0, 0⟩⟩
  rw [hgibbs]
  exact decay_of_siteWw (haarG SU2) hpot geodSU2_nonneg geodSU2_le_pi hk' linkDist linkDist_self
    linkDist_triangle hlam hγ0 hγ1 hcol hf hg hfA hgS hvf hLg hvg hR

/-- The bounded form (S). -/
theorem lawGapBddW_of_levelDprimeWwOn {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ}
    (hlam : 0 ≤ lam) (h : LevelDprimeWwOn ρ lam) : LawGapBddW ρ lam :=
  lawGapBddW_of_lawGapW (lawGapW_of_levelDprimeWwOn hlam h)

/-- **v4's finite-range `LevelDprimeWOn` is a special case** (S), with `γ' = γ e^{λ D₁}`. -/
theorem levelDprimeWwOn_of_levelDprimeWOn {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ}
    (hlam : 0 ≤ lam) (h : LevelDprimeWOn ρ lam) : LevelDprimeWwOn ρ lam := by
  obtain ⟨γ, D₁, hγ0, hρ, k₀, H⟩ := h
  refine ⟨γ * Real.exp (lam * D₁), mul_nonneg hγ0 (Real.exp_pos _).le, hρ, k₀, fun k hk j => ?_⟩
  obtain ⟨V, hgibbs, hpot, kk, hk', hcol, hD₁⟩ := H k hk j
  exact ⟨V, hgibbs, hpot, kk, hk',
    weightedColumn_le_of_range (siteInfluenceW_nonneg (haarG SU2) geodSU2_nonneg hk' exists_geodSU2_pos)
      linkDist hlam hcol hD₁⟩

/-- **Eventual W₁ closeness to a general-support reference action, for a family of laws** (named hypothesis). -/
def CloseWwOn (ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j)))
    (Vref : ∀ j, Finset (LatticeLink 4 (M j)) → GaugeConnection SU2 4 (M j) → ℝ) (lam ε₀ : ℝ) : Prop :=
  ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j, ∃ V : Finset (LatticeLink 4 (M j)) → GaugeConnection SU2 4 (M j) → ℝ,
    ρ k j = Attempts.R3.gibbsMeasure (haarG SU2) V ∧ Attempts.R3.Potential (fun A => A) V ∧
    ∃ δ : LatticeLink 4 (M j) → LatticeLink 4 (M j) → ℝ,
      (∀ i z, z ∉ ({i} : Finset (LatticeLink 4 (M j))) →
        OneScale.Effective.InfluenceDevW geodSU2 {i}
          (Attempts.R3.siteSpec (haarG SU2) (fun A => A) (Vref j) i)
          (Attempts.R3.siteSpec (haarG SU2) (fun A => A) V i) z (δ i z)) ∧
      WeightedColumnW δ linkDist lam ε₀

/-- **The repaired openness lemma, law level** (S): a reference action with weighted column `≤ γ` in every volume and
eventual closeness `≤ ε₀`, `γ + ε₀ < 1`, give `LevelDprimeWwOn`. -/
theorem levelDprimeWwOn_of_ref {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))}
    {Vref : ∀ j, Finset (LatticeLink 4 (M j)) → GaugeConnection SU2 4 (M j) → ℝ} {lam γ ε₀ : ℝ}
    (hγ0 : 0 ≤ γ) (hε0 : 0 ≤ ε₀) (h1 : γ + ε₀ < 1)
    (href : ∀ j, ∃ kk : LatticeLink 4 (M j) → LatticeLink 4 (M j) → ℝ,
      SiteInfluenceW (haarG SU2) (fun A => A) (Vref j) geodSU2 kk ∧ WeightedColumnW kk linkDist lam γ)
    (hclose : CloseWwOn ρ Vref lam ε₀) : LevelDprimeWwOn ρ lam := by
  obtain ⟨k₀, H⟩ := hclose
  refine ⟨γ + ε₀, by linarith, h1, k₀, fun k hk j => ?_⟩
  obtain ⟨V, hgibbs, hpot, δ, hdev, hcolδ⟩ := H k hk j
  obtain ⟨kL, hkL, hcolL⟩ := href j
  refine ⟨V, hgibbs, hpot, fun i z => kL i z + δ i z, fun i z hz => (hkL i z hz).of_devW (hdev i z hz), ?_⟩
  intro z
  have := add_le_add (hcolL z) (hcolδ z)
  simpa only [add_mul, sum_add_distrib] using this

end Laws

/-! ## On the blocked laws: the v4 infrared input -/

/-- `LevelDprimeWw` is `LevelDprimeWwOn` of the blocked laws (definitional). -/
theorem levelDprimeWw_iff_on {T : Tuning} (B : BlockingFamily T) (lam : ℝ) :
    LevelDprimeWw T B lam ↔ LevelDprimeWwOn (M := coarseSide) (blockedLaw T B) lam := Iff.rfl

/-- **Weighted D′ gives v4's infrared input of record** (S): `LevelDprimeWw T B λ ⇒ BlockGapBddW T B λ`. -/
theorem blockGapBddW_of_levelDprimeWw {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : LevelDprimeWw T B lam) : BlockGapBddW T B lam :=
  blockGapBddW_of_unifW (blockGapUnifW_of_levelDprimeWw B hlam h)

/-- **Strategy (a) of version 4 with the weighted hypothesis at `L₁`** (S): `LevelDprimeWwOn` of the `L₁` laws
`(ν k j).map (B₂ k j)` and `StageTwoW` give the bounded block gap at `L_*`. -/
theorem blockGapBddW_of_levelDprimeWwOn {M : ℕ → ℕ} [∀ j, NeZero (M j)] {T : Tuning} (B₁ : BlockingFamily T)
    (B₂ : ∀ k j : ℕ, GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j))
    (hB₂ : ∀ k j : ℕ, Measurable (B₂ k j)) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hD : LevelDprimeWwOn (fun k j => (blockedLaw T B₁ k j).map (B₂ k j)) lam₂)
    (hX : StageTwoW (blockedLaw T B₁) B₂ s) :
    ∃ lam : ℝ, 0 < lam ∧ BlockGapBddW T B₁ lam :=
  blockGapBddW_of_stageTwo B₁ B₂ hB₂ hs hlam₂ (lawGapBddW_of_levelDprimeWwOn hlam₂.le hD) hX

/-! ## Noisy blockings in the law-level form -/

variable {Y0 Yp : ℕ → Type} [∀ j, MeasurableSpace (Y0 j)] [∀ j, MeasurableSpace (Yp j)]

/-- **Noisy blockings plug into the law-level gap** (S): weighted D′ for the noisy blocked laws gives their W₁ gap in
the bounded form `LawGapBddW (noisyBlockedLaw NB)`. -/
theorem noisy_lawGapBddW {T : Tuning} (NB : NoisyBlockingFamily T Y0 Yp) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : LevelDprimeWwOn (M := coarseSide) (noisyBlockedLaw NB) lam) :
    LawGapBddW (M := coarseSide) (noisyBlockedLaw NB) lam :=
  lawGapBddW_of_levelDprimeWwOn hlam h

/-- **With a kernel density, the Gibbs clause is automatic** (S): only the weighted column remains to be shown; i.e.
if for every level and volume (from `k₀` on) every bounded potential representing the noisy blocked law has a weighted
column `≤ γ < 1`, then `LevelDprimeWwOn (noisyBlockedLaw NB) λ`. -/
theorem noisy_gibbs_clause {T : Tuning} (NB : NoisyBlockingFamily T Y0 Yp) {lam γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {k₀ : ℕ} (hK : ∀ k, k₀ ≤ k → ∀ j, KernelDensity NB k j)
    (hcol : ∀ k, k₀ ≤ k → ∀ j (V : CoarsePot j), Attempts.R3.Potential (fun A => A) V →
      noisyBlockedLaw NB k j = Attempts.R3.gibbsMeasure (haarG SU2) V →
      ∃ kk : LatticeLink 4 (coarseSide j) → LatticeLink 4 (coarseSide j) → ℝ,
        SiteInfluenceW (haarG SU2) (fun A => A) V geodSU2 kk ∧ WeightedColumnW kk linkDist lam γ) :
    LevelDprimeWwOn (M := coarseSide) (noisyBlockedLaw NB) lam := by
  refine ⟨γ, hγ0, hγ1, k₀, fun k hk j => ?_⟩
  obtain ⟨V, hpot, hgibbs⟩ := noisy_blockedLaw_gibbs NB k j (hK k hk j)
  exact ⟨V, hgibbs, hpot, hcol k hk j V hpot hgibbs⟩

/-- **The deterministic case agrees** (S): for the trivial-noise family of a `BlockingFamily`, the law-level gap of the
noisy blocked laws is `BlockGapBddW`. -/
theorem blockGapBddW_iff_noisy {T : Tuning} (B : BlockingFamily T) (lam : ℝ) :
    BlockGapBddW T B lam ↔ LawGapBddW (M := coarseSide) (noisyBlockedLaw (BlockingFamily.toNoisy B)) lam := by
  have e : noisyBlockedLaw (BlockingFamily.toNoisy B) = blockedLaw T B := by
    funext k j; exact blockedLaw_toNoisy B k j
  rw [e]
  exact blockGapBddW_iff_lawGapBddW B lam

end ProofPhase.Repair
