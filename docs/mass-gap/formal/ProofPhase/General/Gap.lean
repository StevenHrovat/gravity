/-
Proof phase, generalisation phase 1b: the W₁ laws and the recursion lemma over any gauge group and dimension
(2026-11-24). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1b.
-/

import ProofPhase.General.Setting
import ProofPhase.General.Torus
import ProofPhase.V4.Recursion

/-!
# The W₁ gap of laws, and the recursion lemma, over any gauge group and dimension

`V4/Gap` and `V4/Recursion` for the Wilson measure of any `Gr` of the package in dimension `d`, with the cost
distance of the Lipschitz class a parameter `cost : Gr → Gr → ℝ` (for SU(2): `geodSU2`; for SU(N): `geodSUN`; in the
package: `GaugeSubst.geodDist`). The theorems that use the Dobrushin-type decay (`lawGapW_of_levelDprimeWOn`) take the
two facts they use about the cost: `0 ≤ cost` and `cost ≤ P` (`P = π` for `geodSU2` and `geodSUN`). The polynomial
growth `(1 + R)^d` of the coarse oscillation sum and the tail constant `d!/r^d` replace `(1 + R)^4` and `24/r^4`
(`poly_exp_le` of phase 1). `LawGapBddW` is `ProofPhase.General.LawGapBddW` of `Torus.lean`.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase.Certified (SiteInfluenceW decay_of_siteW)
open ProofPhase.RouteA (cov_transfer)
open ProofPhase.V4 (homog_le_bdd)
open ProofPhase.UV

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section Gap

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  {d : ℕ} [NeZero d] (cost : Gr → Gr → ℝ) {M : ℕ → ℕ} [∀ j, NeZero (M j)]

/-- Oscillation sums are nonnegative. -/
theorem sum_osc_nonneg {N : ℕ} [NeZero N] {f : GaugeConnection Gr d N → ℝ} {vf : LatticeLink d N → ℝ}
    (hvf : OscBound f vf) (A : Finset (LatticeLink d N)) : 0 ≤ ∑ a ∈ A, vf a :=
  Finset.sum_nonneg fun a _ => hvf.nonneg (fun _ => 1) a

def LawGapW (ρ : ℕ → ∀ j, Measure (GaugeConnection Gr d (M j))) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection Gr d (M j) → ℝ) (A Sg : Finset (LatticeLink d (M j)))
    (vf : LatticeLink d (M j) → ℝ) (Lg R : ℝ),
    BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → LipBound cost g (fun _ => Lg) →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ V, f V * g V ∂(ρ k j) - (∫ V, f V ∂(ρ k j)) * ∫ V, g V ∂(ρ k j)| ≤
      C * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R))

def LevelDprimeWOn (ρ : ℕ → ∀ j, Measure (GaugeConnection Gr d (M j))) (lam : ℝ) : Prop :=
  ∃ γ D₁ : ℝ, 0 ≤ γ ∧ γ * Real.exp (lam * D₁) < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j,
    ∃ V : Finset (LatticeLink d (M j)) → GaugeConnection Gr d (M j) → ℝ,
    ρ k j = Attempts.R3.gibbsMeasure (haarG Gr) V ∧ Attempts.R3.Potential (fun A => A) V ∧
    ∃ kk : LatticeLink d (M j) → LatticeLink d (M j) → ℝ,
      SiteInfluenceW (haarG Gr) (fun A => A) V cost kk ∧
      (∀ z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (LatticeLink d (M j)))), kk i z ≤ γ) ∧
      (∀ i z, z ∉ ({i} : Finset (LatticeLink d (M j))) → kk i z ≠ 0 → linkDist z i ≤ D₁)

/-- **D′ in W₁ form gives the W₁ gap** (S: `decay_of_siteW` on each law), for a cost distance with `0 ≤ cost ≤ P`. -/
theorem lawGapW_of_levelDprimeWOn {P : ℝ} (hc0 : ∀ a b, 0 ≤ cost a b) (hP : ∀ a b, cost a b ≤ P)
    {ρ : ℕ → ∀ j, Measure (GaugeConnection Gr d (M j))} {lam : ℝ}
    (hlam : 0 ≤ lam) (h : LevelDprimeWOn cost ρ lam) : LawGapW cost ρ lam := by
  obtain ⟨γ, D₁, hγ0, hρ, k₀, H⟩ := h
  have hP0 : 0 ≤ P := (hc0 1 1).trans (hP 1 1)
  refine ⟨P / (1 - γ * Real.exp (lam * D₁)), div_nonneg hP0 (by linarith), k₀,
    fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ?_⟩
  obtain ⟨V, hgibbs, hpot, kk, hk', hcol, hD₁⟩ := H k hk j
  have : Nonempty (LatticeLink d (M j)) := ⟨⟨fun _ => 1, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩⟩
  rw [hgibbs]
  exact decay_of_siteW (haarG Gr) hpot hc0 hP hk' hγ0 hcol linkDist linkDist_self
    linkDist_triangle hD₁ hlam hρ hf hg hfA hgS hvf hLg hvg hR

/-- The homogeneous form implies the bounded form. -/
theorem lawGapBddW_of_lawGapW {ρ : ℕ → ∀ j, Measure (GaugeConnection Gr d (M j))} {lam : ℝ}
    (h : LawGapW cost ρ lam) : LawGapBddW cost ρ lam := by
  obtain ⟨C, hC, k₀, H⟩ := h
  refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip _ hR => ?_⟩
  exact (H k hk j f g A Sg vf Lg R ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩ hfA hgS hvf hLg hlip hR).trans
    (homog_le_bdd hC (sum_osc_nonneg hvf A) hLg (Real.exp_pos _).le)

end Gap

/-! ## The SU(2), `d = 4` instances -/

section Instance

variable {M : ℕ → ℕ} [∀ j, NeZero (M j)]

theorem lawGapW_iff {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ} :
    ProofPhase.V4.LawGapW ρ lam ↔ LawGapW ProofPhase.Certified.geodSU2 ρ lam := Iff.rfl

theorem levelDprimeWOn_iff {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ} :
    ProofPhase.V4.LevelDprimeWOn ρ lam ↔ LevelDprimeWOn ProofPhase.Certified.geodSU2 ρ lam := Iff.rfl

/-- `ProofPhase.V4.lawGapW_of_levelDprimeWOn` from the generic theorem (`P = π`). -/
theorem lawGapW_of_levelDprimeWOn_su2 {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ}
    (hlam : 0 ≤ lam) (h : ProofPhase.V4.LevelDprimeWOn ρ lam) : ProofPhase.V4.LawGapW ρ lam :=
  lawGapW_of_levelDprimeWOn ProofPhase.Certified.geodSU2 ProofPhase.Certified.geodSU2_nonneg
    ProofPhase.Certified.geodSU2_le_pi hlam h

/-- `ProofPhase.V4.lawGapBddW_of_lawGapW` from the generic theorem. -/
theorem lawGapBddW_of_lawGapW_su2 {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ}
    (h : ProofPhase.V4.LawGapW ρ lam) : ProofPhase.V4.LawGapBddW ρ lam :=
  lawGapBddW_of_lawGapW ProofPhase.Certified.geodSU2 h

example : @ProofPhase.V4.lawGapW_of_levelDprimeWOn = @lawGapW_of_levelDprimeWOn_su2 := rfl
example : @ProofPhase.V4.lawGapBddW_of_lawGapW = @lawGapBddW_of_lawGapW_su2 := rfl

end Instance

end ProofPhase.General
