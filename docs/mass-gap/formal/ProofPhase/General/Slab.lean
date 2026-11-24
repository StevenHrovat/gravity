/-
Proof phase, generalisation phase 1c: the slab-observable layer over any gauge group and dimension (2026-11-24).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1c.
-/

import ProofPhase.General.Setting
import ProofPhase.Existence.Bridge
import ProofPhase.Torus.Local

/-!
# Slab observables, gaps and reflection positivity, over any gauge group and dimension

The observable layer of `Objects` for the Wilson measure of any `Gr` of the package in dimension `d` (representation
dimension `nr`): the reflected correlation `wcorr`, slab observables `SlabObs`, the gaps `LatticeGap`, `MassGap`,
`MassGapLoc` (and `massGap_of_latticeGap`, `massGapLoc_of_massGap`), `abs_wcorr_le`, reflection positivity of every
limit point `LimitRP`, `limitRP`. The correlation with a volume-dependent coupling is `vwcorr` (for a `VTuning`).
`timeSlab`, `thetaConn`, `IsLimitPoint` are already group-free.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase (IsLimitPoint)
open ProofPhase.Existence (VTuning)

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Slab

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] {d : ℕ} [NeZero d]

/-- The reflected connected correlation at level `k`, torus `j`, lattice time `n`: `Cov(F ∘ S_n, F ∘ Θ)`. -/
def wcorr (T : Tuning) (k j : ℕ) (F : GaugeConnection Gr d (T.side k j) → ℝ) (n : ℕ) : ℝ :=
  corr (d := d) (N := T.side k j) (G := Gr) nr (wilsonWeight (T.β k)) F n

/-- The same with the volume-dependent coupling of a `VTuning`. -/
def vwcorr (V : VTuning) (k j : ℕ) (F : GaugeConnection Gr d (V.T.side k j) → ℝ) (n : ℕ) : ℝ :=
  corr (d := d) (N := V.T.side k j) (G := Gr) nr (wilsonWeight (V.βv k j)) F n

theorem vwcorr_toV (T : Tuning) (k j : ℕ) (F : GaugeConnection Gr d (T.side k j) → ℝ) (n : ℕ) :
    vwcorr nr T.toV k j F n = wcorr nr T k j F n := rfl

structure SlabObs (Gr : Type*) [Group Gr] [MeasurableSpace Gr] (d : ℕ) [NeZero d] (T : Tuning) (s : ℝ) (V : ℕ → ℕ) where
  F : ∀ k j, GaugeConnection Gr d (T.side k j) → ℝ
  meas : ∀ k j, Measurable (F k j)
  bdd : ∀ k j U, |F k j U| ≤ 1
  gauge : ∀ k j, GaugeInvariant (F k j)
  slab : ∀ k j, DepOn (F k j) (timeSlab 0 (T.thick k s))
  supp : ∀ k j, Finset (LatticeLink d (T.side k j))
  supp_card : ∀ k j, (supp k j).card ≤ V k
  dep : ∀ k j, DepOn (F k j) (supp k j)

theorem SlabObs.bm {T : Tuning} {s : ℝ} {V : ℕ → ℕ} (O : SlabObs Gr d T s V) (k j : ℕ) : BM (O.F k j) :=
  ⟨O.meas k j, 1, O.bdd k j⟩

def SlabObs.Extent {T : Tuning} {s : ℝ} {V : ℕ → ℕ} (O : SlabObs Gr d T s V) (R : ℝ) : Prop :=
  ∀ k j, ∀ e ∈ O.supp k j, ∀ e' ∈ O.supp k j, T.a k * linkDist e e' ≤ R

section Explicit

variable (Gr) (d)

def LatticeGap (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s : ℝ) (V : ℕ → ℕ), ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (O : SlabObs Gr d T s V) (n : ℕ) (h : ℝ),
    IsLimitPoint (fun j => wcorr nr T k j (O.F k j) n) h → |h| ≤ 2 * Real.exp (-(m * (n * T.a k)))

def MassGap (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s : ℝ) (V : ℕ → ℕ) (O : SlabObs Gr d T s V) (τ : ℝ), 0 ≤ τ → ∀ (h : ℕ → ℝ) (g : ℝ),
    (∀ k, IsLimitPoint (fun j => wcorr nr T k j (O.F k j) (T.steps k τ)) (h k)) → IsLimitPoint h g →
      |g| ≤ 2 * Real.exp (-(m * τ))

/-- `LatticeGap` gives `MassGap` once the lattice spacing goes to zero. -/
theorem massGap_of_latticeGap {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : LatticeGap Gr nr d T) : MassGap Gr nr d T := by
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


def MassGapLoc (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s R : ℝ) (V : ℕ → ℕ) (O : SlabObs Gr d T s V), O.Extent R → ∀ (τ : ℝ), 0 ≤ τ →
    ∀ (h : ℕ → ℝ) (g : ℝ), (∀ k, IsLimitPoint (fun j => wcorr nr T k j (O.F k j) (T.steps k τ)) (h k)) →
      IsLimitPoint h g → |g| ≤ 2 * Real.exp (-(m * τ))

theorem massGapLoc_of_massGap {T : Tuning} (h : MassGap Gr nr d T) : MassGapLoc Gr nr d T := by
  obtain ⟨m, hm, H⟩ := h
  exact ⟨m, hm, fun s _ V O _ τ hτ hk g hhk hg => H s V O τ hτ hk g hhk hg⟩

end Explicit

section Explicit2

variable (Gr) (d)

def LimitRP (T : Tuning) : Prop :=
  ∀ (F : ∀ k j, GaugeConnection Gr d (T.side k j) → ℝ),
    (∀ k j, LinkDep (F k j) (posHalfLinks d (T.side k j)) ∧ Measurable (F k j) ∧ ∃ M, ∀ U, |F k j U| ≤ M) →
    ∀ (h : ℕ → ℝ) (g : ℝ),
      (∀ k, IsLimitPoint (fun j => ∫ U, F k j U * F k j (thetaConn U) ∂(ymLaw (G := Gr) nr d T k j)) (h k)) → IsLimitPoint h g → 0 ≤ g

variable [GaugeRep Gr nr]

theorem abs_wcorr_le (T : Tuning) (k j : ℕ) {F : GaugeConnection Gr d (T.side k j) → ℝ} (hF : Measurable F)
    (hF1 : ∀ U, |F U| ≤ 1) (n : ℕ) : |wcorr nr T k j F n| ≤ 2 :=
  abs_corr_le_two (d := d) GaugeRep.continuous_rep GaugeRep.unitary_rep
    (posWeight_wilson nr (T.β k)) hF hF1 n

theorem limitRP (T : Tuning) : LimitRP Gr nr d T := by
  intro F hF h g hh hg
  have hk : ∀ k, 0 ≤ h k := fun k =>
    (hh k).nonneg fun j => rp_gaugeMeasure (d := d) (N := T.side k j) GaugeRep.continuous_rep
      GaugeRep.unitary_rep (T.even_side k j) (posWeight_wilson nr (T.β k))
      (hF k j).1 (hF k j).2.1 (hF k j).2.2
  exact hg.nonneg hk

end Explicit2

end Slab

/-! ## The SU(2), `d = 4` instances -/

section Instance

variable {T : Tuning} {s : ℝ} {V : ℕ → ℕ}

/-- The old slab observables as generic ones (same fields). -/
def SlabObs.ofOld (O : ProofPhase.SlabObs T s V) : SlabObs SU2 4 T s V :=
  ⟨O.F, O.meas, O.bdd, O.gauge, O.slab, O.supp, O.supp_card, O.dep⟩

/-- The generic slab observables for `SU2`, `d = 4` as old ones. -/
def SlabObs.toOld (O : SlabObs SU2 4 T s V) : ProofPhase.SlabObs T s V :=
  ⟨O.F, O.meas, O.bdd, O.gauge, O.slab, O.supp, O.supp_card, O.dep⟩

theorem latticeGap_iff (T : Tuning) : ProofPhase.LatticeGap T ↔ LatticeGap SU2 2 4 T :=
  ⟨fun ⟨m, hm, H⟩ => ⟨m, hm, fun s V => by
      obtain ⟨k₀, hk⟩ := H s V
      exact ⟨k₀, fun k hk' O n h hh => hk k hk' O.toOld n h hh⟩⟩,
   fun ⟨m, hm, H⟩ => ⟨m, hm, fun s V => by
      obtain ⟨k₀, hk⟩ := H s V
      exact ⟨k₀, fun k hk' O n h hh => hk k hk' (SlabObs.ofOld O) n h hh⟩⟩⟩

theorem massGap_iff (T : Tuning) : ProofPhase.MassGap T ↔ MassGap SU2 2 4 T :=
  ⟨fun ⟨m, hm, H⟩ => ⟨m, hm, fun s V O τ hτ h g hh hg => H s V O.toOld τ hτ h g hh hg⟩,
   fun ⟨m, hm, H⟩ => ⟨m, hm, fun s V O τ hτ h g hh hg => H s V (SlabObs.ofOld O) τ hτ h g hh hg⟩⟩

theorem massGapLoc_iff (T : Tuning) : ProofPhase.MassGapLoc T ↔ MassGapLoc SU2 2 4 T :=
  ⟨fun ⟨m, hm, H⟩ => ⟨m, hm, fun s R V O hO τ hτ h g hh hg => H s R V O.toOld hO τ hτ h g hh hg⟩,
   fun ⟨m, hm, H⟩ => ⟨m, hm, fun s R V O hO τ hτ h g hh hg => H s R V (SlabObs.ofOld O) hO τ hτ h g hh hg⟩⟩

theorem limitRP_iff (T : Tuning) : ProofPhase.LimitRP T ↔ LimitRP SU2 2 4 T := Iff.rfl

/-- `ProofPhase.massGap_of_latticeGap` from the generic theorem. -/
theorem massGap_of_latticeGap_su2 {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : ProofPhase.LatticeGap T) :
    ProofPhase.MassGap T :=
  (massGap_iff T).2 (massGap_of_latticeGap SU2 2 4 ha ((latticeGap_iff T).1 h))

/-- `ProofPhase.massGapLoc_of_massGap` from the generic theorem. -/
theorem massGapLoc_of_massGap_su2 {T : Tuning} (h : ProofPhase.MassGap T) : ProofPhase.MassGapLoc T :=
  (massGapLoc_iff T).2 (massGapLoc_of_massGap SU2 2 4 ((massGap_iff T).1 h))

/-- `ProofPhase.Tuning.abs_wcorr_le` from the generic theorem. -/
theorem abs_wcorr_le_su2 (T : Tuning) (k j : ℕ) {F : GaugeConnection SU2 4 (T.side k j) → ℝ} (hF : Measurable F)
    (hF1 : ∀ U, |F U| ≤ 1) (n : ℕ) : |T.wcorr k j F n| ≤ 2 :=
  abs_wcorr_le SU2 2 4 T k j hF hF1 n

/-- `ProofPhase.limitRP` from the generic theorem. -/
theorem limitRP_su2 (T : Tuning) : ProofPhase.LimitRP T := limitRP SU2 2 4 T

example : @ProofPhase.Tuning.abs_wcorr_le = @abs_wcorr_le_su2 := rfl
example : @ProofPhase.limitRP = @limitRP_su2 := rfl

end Instance

end ProofPhase.General
