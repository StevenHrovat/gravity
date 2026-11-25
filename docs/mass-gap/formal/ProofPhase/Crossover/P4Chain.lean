/-
Proof phase, crossover workstream, round 2 (c9a-crossover, W1): the crossover P4 as one named hypothesis `P4Star` at
M1's hand-over scale, and the chain from it to the assembly (2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/W1-CHAIN.md`.
-/

import ProofPhase.Crossover.Openness
import ProofPhase.OneBox.Fine
import ProofPhase.Interface.RandBlocking

/-!
# P4 as one named hypothesis, and the exact chain to the assembly

**Where M1 ends.** M1 hands over, at the stopping scale `L_*`, the law of the block state in Balaban's inductive form,
uniformly in the lattice spacing. In the assembly's language this is a statement about the block laws
`randBlockedLaw T B k j` of a randomized blocking family `B` (randomized because M1 gives swallowed coarse bonds an
independent Haar value): **from some level on, every block law lies in a class `C` of laws on the coarse tori**
(`M1HandOver T B C`, a named hypothesis; it bundles M1's law form at `L_*`, the interface encoding R11 of the block state
`(SO(3), closed Z2)` as a coarse configuration, and the threshold `a ≤ a₀(γ)`).

**What P4 must say.** `P4Star C λ` (named, **open**): every law of the class `C`, in every volume, satisfies the one-box
criterion with **one** set of constants (`γ < 1`, box size `≤ n_max`, diameter `≤ D₀`, rate `λ`). Two forms:
* `P4Star`: influences tested on all bounded functions of the box (the form the existing law route consumes);
* `P4StarInv`: influences tested only on gauge-invariant functions of the box with frozen boundary, with a gauge-covariant
  box specification (`ActAdm`, `SpecCovariant`, as in `FineOneBox`). Its influence clause is weaker; it adds covariance
  of the box specification (true for the DLR specification of a gauge-invariant law with Haar prior). Neither form
  implies the other as stated; the restricted one is the natural one for a gauge theory.

**The chain** (all S, i.e. Lean):
* `oneBoxLaw_of_p4Star`: `P4Star C λ ∧ M1HandOver T B C ⇒ OneBoxLaw (randBlockedLaw T B) λ`;
* `randBlockGapBddW_of_lawGapBddW`: `LawGapBddW` of the block laws `⇒ RandBlockGapBddW` (pushforward);
* **`yang_mills_assembly_p4Star`**: `OnLCP' ∧ NonTrivial ∧ P4Star C λ ∧ M1HandOver T B C ∧ RandObsTransferPhysTW T B ⇒`
  the v4 conclusions (through `lawGapBddW_of_oneBoxLaw` and `yang_mills_assembly_v4_bdd_rand`);
* restricted form: `lawGapBddWInv_of_oneBoxLawInv` (the one-box theorem with the real gauge action; decay for a
  gauge-invariant second observable), `randTorusDecayLoc_of_blockGapBddWInv` (the v4 cut, where the coarse approximant
  of the transfer is required to be gauge invariant: `RandObsTransferPhysTWInv`, which implies the old transfer,
  `randObsTransferPhysTW_of_inv`), and **`yang_mills_assembly_p4StarInv`**.

**Net form** (`p4StarInv_of_net`, S, with `Openness.lean`): `P4StarInv C λ` follows if every law of the class has a
gauge-covariant box specification that is `δ`-close (worst case over boundary conditions, `IsNearSpec`) to a reference
specification whose influences on a shell of positions are `κ̄`, with influences `≤ κ̄` off the shell directly (the
**tail clause**: quasi-locality, not supplied by closeness), the one-box sum for `κ̄` with `γ`, and the margin
`γ + 2δS/|Λ₀| ≤ γ₁ < 1`. The tail clause is where the content of (WL) sits.

**The other split** (section 5, S): `lawGapBddW_of_stageTwo` (version 4's recursion lemma for any family of `L_*` laws),
`randBlockGapBddW_of_stageTwo` and **`yang_mills_assembly_stageTwo`**: the landing (`LawGapBddW` of the `L₁` laws, strong
coupling) and stage two across the crossover (`V4.StageTwoW`: projection quasi-locality and conditional decoupling, the
Lean form of what (WL) must deliver) give the assembly over M1's hand-over without `P4Star`.

**Claim level.** Lean, standard axioms. Nothing about Yang–Mills is proved here beyond the existing assembly: `P4Star`,
`P4StarInv`, `M1HandOver`, the transfers (including the new `RandObsTransferPhysTWInv`) and `StageTwoW` are named
hypotheses. The value is that the dependency structure is now exact: P4 is one hypothesis on a class of laws at the place
where M1 ends. `L₁` enters only through the box size and diameter (`n_max`, `D₀`), which must scale like `L₁/L_*`.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift OneScale.CubeChain Positivity ProofPhase.Existence ProofPhase.RouteA ProofPhase.Torus
  ProofPhase.H1 ProofPhase.Certified ProofPhase.V3 ProofPhase.V4 ProofPhase.OneBox ProofPhase.Interface

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Crossover

/-! ## 1. Classes of laws at `L_*`, `P4Star`, M1's hand-over -/

/-- A class of laws on the `L_*` tori: for every volume `j` a set of measures on the coarse configurations. -/
abbrev LawClass : Type := ∀ j : ℕ, Set (Measure (GaugeConnection SU2 4 (coarseSide j)))

section Data

variable {N : ℕ} [NeZero N]

/-- **One box for one law, unrestricted influences** (the body of `OneBoxLaw`): a box `Λ₀` of `1 ≤ |Λ₀| ≤ n_max` sites,
diameter `≤ D₀`, a block specification of `ρ` whose blocks are the translates of `Λ₀`, influences `κ(u)` of the relative
outside position `u` tested on all bounded functions of the box, and the one-box sum with `λ, γ`. -/
def OneBoxData (ρ : Measure (GaugeConnection SU2 4 N)) (lam γ D₀ : ℝ) (nmax : ℕ) : Prop :=
  ∃ (Λ₀ : Finset (FinLatticeSites 4 N)) (κ : FinLatticeSites 4 N → ℝ) (P : BlockSpec ρ (FinLatticeSites 4 N)),
    1 ≤ Λ₀.card ∧ Λ₀.card ≤ nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) ∧
    (∀ t, P.block t = boxBlock Λ₀ t) ∧
    (∀ t z, z ∉ P.block t → IsInfluenceBound (P.block t) (P.spec t) z (κ (z.site - t))) ∧
    OneBoxSum κ (boxReach Λ₀) Λ₀ lam γ

/-- **One box for one law, gauge-restricted** (the form of `FineOneBox`): as `OneBoxData`, with a gauge-covariant
specification and influences tested only on gauge-invariant functions of the box with frozen boundary. -/
def OneBoxDataInv (ρ : Measure (GaugeConnection SU2 4 N)) (lam γ D₀ : ℝ) (nmax : ℕ) : Prop :=
  ∃ (Λ₀ : Finset (FinLatticeSites 4 N)) (κ : FinLatticeSites 4 N → ℝ) (P : BlockSpec ρ (FinLatticeSites 4 N)),
    1 ≤ Λ₀.card ∧ Λ₀.card ≤ nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) ∧
    (∀ t, P.block t = boxBlock Λ₀ t) ∧
    (∀ t, SpecCovariant (gaugeAct N) (P.spec t)) ∧
    (∀ t z, z ∉ P.block t →
      IsInfluenceBoundOn (ActAdm (gaugeAct N) (P.block t)) (P.block t) (P.spec t) z (κ (z.site - t))) ∧
    OneBoxSum κ (boxReach Λ₀) Λ₀ lam γ

end Data

/-- **`P4Star` (named, open: the crossover).** Every law of the class `C`, in every volume, satisfies the one-box
criterion (unrestricted influences) with one set of constants `γ < 1`, `D₀`, `n_max` and the rate `λ`. -/
def P4Star (C : LawClass) (lam : ℝ) : Prop :=
  ∃ (γ D₀ : ℝ) (nmax : ℕ), 0 ≤ γ ∧ γ < 1 ∧ ∀ j, ∀ ρ ∈ C j, OneBoxData ρ lam γ D₀ nmax

/-- **`P4StarInv` (named, open: the crossover, gauge-restricted form).** -/
def P4StarInv (C : LawClass) (lam : ℝ) : Prop :=
  ∃ (γ D₀ : ℝ) (nmax : ℕ), 0 ≤ γ ∧ γ < 1 ∧ ∀ j, ∀ ρ ∈ C j, OneBoxDataInv ρ lam γ D₀ nmax

/-- **M1's hand-over (named).** From some level on, in every volume, the `L_*` block law of the randomized blocking family
`B` lies in the class `C`. (For M1: `C` = laws of M1's inductive form at final coupling in `[γ', γ]` with constants `c`,
encoded as coarse configurations by the interface R11; the level threshold is `a ≤ a₀(γ)`.) -/
def M1HandOver (T : Tuning) (B : RandBlockingFamily T) (C : LawClass) : Prop :=
  ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j, randBlockedLaw T B k j ∈ C j

/-- A larger class is a stronger `P4Star`: it suffices to prove `P4Star` for any class containing M1's. -/
theorem p4Star_mono {C C' : LawClass} (h : ∀ j, C' j ⊆ C j) {lam : ℝ} (hP : P4Star C lam) : P4Star C' lam := by
  obtain ⟨γ, D₀, nmax, h0, h1, H⟩ := hP
  exact ⟨γ, D₀, nmax, h0, h1, fun j ρ hρ => H j ρ (h j hρ)⟩

theorem p4StarInv_mono {C C' : LawClass} (h : ∀ j, C' j ⊆ C j) {lam : ℝ} (hP : P4StarInv C lam) :
    P4StarInv C' lam := by
  obtain ⟨γ, D₀, nmax, h0, h1, H⟩ := hP
  exact ⟨γ, D₀, nmax, h0, h1, fun j ρ hρ => H j ρ (h j hρ)⟩

/-- M1's hand-over is monotone in the class. -/
theorem m1HandOver_mono {T : Tuning} {B : RandBlockingFamily T} {C C' : LawClass} (h : ∀ j, C' j ⊆ C j)
    (hM : M1HandOver T B C') : M1HandOver T B C := by
  obtain ⟨k₀, hk⟩ := hM
  exact ⟨k₀, fun k hkk j => h j (hk k hkk j)⟩

/-! ## 2. The unrestricted chain -/

theorem randBlockedLaw_prob (T : Tuning) (B : RandBlockingFamily T) (k j : ℕ) :
    IsProbabilityMeasure (randBlockedLaw T B k j) := by
  unfold randBlockedLaw
  exact (Measure.isProbabilityMeasure_map_iff (B k j).meas.aemeasurable).2 inferInstance

theorem integral_randBlockedLaw {T : Tuning} (B : RandBlockingFamily T) (k j : ℕ)
    {f : GaugeConnection SU2 4 (coarseSide j) → ℝ} (hf : Measurable f) :
    ∫ V, f V ∂(randBlockedLaw T B k j) = ∫ p, f ((B k j).B p) ∂(randJointLaw T B k j) := by
  unfold randBlockedLaw
  exact integral_map (B k j).meas.aemeasurable hf.aestronglyMeasurable

/-- **`P4Star` at M1's hand-over is the one-box criterion of the `L_*` block laws** (S). -/
theorem oneBoxLaw_of_p4Star {T : Tuning} {B : RandBlockingFamily T} {C : LawClass} {lam : ℝ}
    (hP : P4Star C lam) (hM : M1HandOver T B C) : OneBoxLaw (M := coarseSide) (randBlockedLaw T B) lam := by
  obtain ⟨γ, D₀, nmax, h0, h1, H⟩ := hP
  obtain ⟨k₀, hk⟩ := hM
  exact ⟨γ, D₀, nmax, h0, h1, k₀, fun k hkk j => H j _ (hk k hkk j)⟩

/-- **The law gap of the block laws is the block gap of the randomized blocking** (S, pushforward). -/
theorem randBlockGapBddW_of_lawGapBddW {T : Tuning} {B : RandBlockingFamily T} {lam : ℝ}
    (h : LawGapBddW (M := coarseSide) (randBlockedLaw T B) lam) : RandBlockGapBddW T B lam := by
  obtain ⟨C, hC, k₀, H⟩ := h
  refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR => ?_⟩
  have h0 := H k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR
  have e1 : ∫ V, f V * g V ∂(randBlockedLaw T B k j) =
      ∫ p, f ((B k j).B p) * g ((B k j).B p) ∂(randJointLaw T B k j) :=
    integral_randBlockedLaw B k j (mf.mul mg)
  have e2 := integral_randBlockedLaw B k j mf
  have e3 := integral_randBlockedLaw B k j mg
  rw [e1, e2, e3] at h0
  exact h0

/-- **`P4Star` and M1's hand-over give the v4 infrared input** (S). -/
theorem randBlockGapBddW_of_p4Star {T : Tuning} {B : RandBlockingFamily T} {C : LawClass} {lam : ℝ}
    (hlam : 0 ≤ lam) (hP : P4Star C lam) (hM : M1HandOver T B C) : RandBlockGapBddW T B lam :=
  randBlockGapBddW_of_lawGapBddW
    (lawGapBddW_of_oneBoxLaw hlam (fun k j => randBlockedLaw_prob T B k j) (oneBoxLaw_of_p4Star hP hM))

/-- **Assembly from `P4Star` at M1's hand-over** (S). Open inputs: the line of constant physics (weakened), non-triviality,
`P4Star C λ` (the crossover), M1's hand-over into `C` (M1 + interface R11), and the ultraviolet transfer for the
randomized blocking (M1's R10 + Lemma UV-TV). -/
theorem yang_mills_assembly_p4Star {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (B : RandBlockingFamily T)
    {C : LawClass} {lam : ℝ} (hlam : 0 < lam) (hP4 : P4Star C lam) (hM1 : M1HandOver T B C)
    (hUV : RandObsTransferPhysTW T B) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T :=
  yang_mills_assembly_v4_bdd_rand hL hN B hlam (randBlockGapBddW_of_p4Star hlam.le hP4 hM1) hUV

/-! ## 3. The gauge-restricted chain -/

section LawInv

variable {M : ℕ → ℕ} [∀ j, NeZero (M j)]

/-- **The one-box criterion for a family of laws, gauge-restricted.** -/
def OneBoxLawInv (ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))) (lam : ℝ) : Prop :=
  ∃ (γ D₀ : ℝ) (nmax : ℕ), 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j, OneBoxDataInv (ρ k j) lam γ D₀ nmax

/-- **The W₁ gap of a family of laws, bounded form, for a gauge-invariant second observable.** As `LawGapBddW`, with
`GaugeInvariant g` added. -/
def LawGapBddWInv (ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection SU2 4 (M j) → ℝ) (A Sg : Finset (LatticeLink 4 (M j)))
    (vf : LatticeLink 4 (M j) → ℝ) (Lg R : ℝ),
    Measurable f → Measurable g → (∀ V, |f V| ≤ 1) → (∀ V, |g V| ≤ 1) → GaugeInvariant g → DepOn f A → DepOn g Sg →
    OscBound f vf → 0 ≤ Lg → LipBound geodSU2 g (fun _ => Lg) → 0 ≤ R →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ V, f V * g V ∂(ρ k j) - (∫ V, f V ∂(ρ k j)) * ∫ V, g V ∂(ρ k j)| ≤
      C * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(lam * R))

/-- **One gauge-restricted box gives the W₁ gap for gauge-invariant second observables, in every volume** (S): the proof
of `lawGapBddW_of_oneBoxLaw` with the lattice gauge action in place of the trivial one. -/
theorem lawGapBddWInv_of_oneBoxLawInv {ρ : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (M j))} {lam : ℝ}
    (hlam : 0 ≤ lam) (hρ : ∀ k j, IsProbabilityMeasure (ρ k j)) (h : OneBoxLawInv ρ lam) : LawGapBddWInv ρ lam := by
  obtain ⟨γ, D₀, nmax, hγ0, hγ1, k₀, H⟩ := h
  have hg1 : 0 < 1 - γ := by linarith
  refine ⟨2 * (4 * nmax) * Real.exp (lam * D₀) / (1 - γ), by positivity, k₀,
    fun k hk j f g A Sg vf Lg R mf mg bf bg hgI hfA hgS hvf hLg _ hR0 hR => ?_⟩
  obtain ⟨Λ₀, κ, P, hΛ1, hΛn, hdiam, hblock, hcovar, hk, hsum⟩ := H k hk j
  have := hρ k j
  have : Nonempty (LatticeLink 4 (M j)) := ⟨⟨fun _ => 0, 0⟩⟩
  have hbox : IsBoxFamily P.block (fun t (x : LatticeLink 4 (M j)) => x.site - t) Λ₀ := by
    have := isBoxFamily_torus Λ₀
    exact ⟨this.bij, fun t x => by rw [hblock t]; exact this.mem t x⟩
  have hvg : OscBound g (fun _ => (2 : ℝ)) := fun V x s =>
    (abs_sub _ _).trans (by linarith [bg V, bg (Function.update V x s)])
  have hcov := abs_cov_le_of_oneBox (a := gaugeAct (M j)) P (fun t x => x.site - t) Λ₀ hbox hΛ1
    (measurable_gaugeAct (M j)) hcovar κ (boxReach Λ₀) (fun t z hz => hk t z hz) (b := 4 * nmax)
    (fun t => by rw [hblock t]; exact (card_boxBlock Λ₀ t).trans (by omega))
    linkDist linkDist_self linkDist_triangle (D₀ := D₀)
    (fun t => by rw [hblock t]; exact boxBlock_diam hdiam t)
    (fun t x y _ hy => by rw [hblock t] at hy; exact boxBlock_reach Λ₀ t x y hy) hlam hγ0 hγ1 hsum
    ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩ (actInv_of_gaugeInvariant hgI) hfA hgS hvf (by norm_num) hvg hR
  refine hcov.trans ?_
  have hS := sum_osc_nonneg hvf A
  have e1 : Real.exp (-(lam * (R - D₀))) = Real.exp (lam * D₀) * Real.exp (-(lam * R)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1]
  have hE := Real.exp_pos (lam * D₀)
  have hE' := Real.exp_pos (-(lam * R))
  have hn : ((4 * nmax : ℕ) : ℝ) = 4 * (nmax : ℝ) := by push_cast; ring
  rw [hn]
  have key : 4 * (nmax : ℝ) / (1 - γ) * (∑ x ∈ A, vf x) * 2 ≤
      2 * (4 * nmax) / (1 - γ) * (1 + ∑ a ∈ A, vf a) * (1 + Lg) := by
    have h0 : 0 ≤ 4 * (nmax : ℝ) / (1 - γ) := by positivity
    have h1 : (∑ x ∈ A, vf x) ≤ (1 + ∑ a ∈ A, vf a) * (1 + Lg) := by nlinarith
    calc 4 * (nmax : ℝ) / (1 - γ) * (∑ x ∈ A, vf x) * 2
        = 2 * (4 * nmax) / (1 - γ) * (∑ x ∈ A, vf x) := by ring
      _ ≤ 2 * (4 * nmax) / (1 - γ) * ((1 + ∑ a ∈ A, vf a) * (1 + Lg)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  calc 4 * (nmax : ℝ) / (1 - γ) * (∑ x ∈ A, vf x) * 2 * (Real.exp (lam * D₀) * Real.exp (-(lam * R)))
      = (4 * (nmax : ℝ) / (1 - γ) * (∑ x ∈ A, vf x) * 2) * Real.exp (lam * D₀) * Real.exp (-(lam * R)) := by ring
    _ ≤ (2 * (4 * nmax) / (1 - γ) * (1 + ∑ a ∈ A, vf a) * (1 + Lg)) * Real.exp (lam * D₀) *
          Real.exp (-(lam * R)) := by gcongr
    _ = 2 * (4 * nmax) * Real.exp (lam * D₀) / (1 - γ) * (1 + ∑ a ∈ A, vf a) * (1 + Lg) *
          Real.exp (-(lam * R)) := by ring

end LawInv

/-- **`P4StarInv` at M1's hand-over is the gauge-restricted one-box criterion of the `L_*` block laws** (S). -/
theorem oneBoxLawInv_of_p4StarInv {T : Tuning} {B : RandBlockingFamily T} {C : LawClass} {lam : ℝ}
    (hP : P4StarInv C lam) (hM : M1HandOver T B C) : OneBoxLawInv (M := coarseSide) (randBlockedLaw T B) lam := by
  obtain ⟨γ, D₀, nmax, h0, h1, H⟩ := hP
  obtain ⟨k₀, hk⟩ := hM
  exact ⟨γ, D₀, nmax, h0, h1, k₀, fun k hkk j => H j _ (hk k hkk j)⟩

/-- `RandBlockGapBddW` with a gauge-invariant second observable. -/
def RandBlockGapBddWInv (T : Tuning) (B : RandBlockingFamily T) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
    (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg R : ℝ),
    Measurable f → Measurable g → (∀ V, |f V| ≤ 1) → (∀ V, |g V| ≤ 1) → GaugeInvariant g → DepOn f A → DepOn g Sg →
    OscBound f vf → 0 ≤ Lg → LipBound geodSU2 g (fun _ => Lg) → 0 ≤ R →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ p, f ((B k j).B p) * g ((B k j).B p) ∂(randJointLaw T B k j) -
        (∫ p, f ((B k j).B p) ∂(randJointLaw T B k j)) * ∫ p, g ((B k j).B p) ∂(randJointLaw T B k j)| ≤
      C * (1 + ∑ a ∈ A, vf a) * (1 + Lg) * Real.exp (-(lam * R))

theorem randBlockGapBddWInv_of_lawGapBddWInv {T : Tuning} {B : RandBlockingFamily T} {lam : ℝ}
    (h : LawGapBddWInv (M := coarseSide) (randBlockedLaw T B) lam) : RandBlockGapBddWInv T B lam := by
  obtain ⟨C, hC, k₀, H⟩ := h
  refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R mf mg bf bg hgI hfA hgS hvf hLg hlip hR0 hR => ?_⟩
  have h0 := H k hk j f g A Sg vf Lg R mf mg bf bg hgI hfA hgS hvf hLg hlip hR0 hR
  have e1 : ∫ V, f V * g V ∂(randBlockedLaw T B k j) =
      ∫ p, f ((B k j).B p) * g ((B k j).B p) ∂(randJointLaw T B k j) :=
    integral_randBlockedLaw B k j (mf.mul mg)
  have e2 := integral_randBlockedLaw B k j mf
  have e3 := integral_randBlockedLaw B k j mg
  rw [e1, e2, e3] at h0
  exact h0

/-- **The transfer with a gauge-invariant coarse approximant.** `RandObsTransferPhysTW` with `GaugeInvariant g` added
for the approximant `g` of the (gauge-invariant) fine observable `G`. (Paper remark, not used: for a blocking that is
covariant in law under coarse gauge transformations, `E[G | block]` is gauge invariant, and averaging an approximant over
coarse gauge transformations keeps its bound and its Lipschitz constant, `geodSU2` being bi-invariant.) -/
def RandObsTransferPhysTWInv (T : Tuning) (B : RandBlockingFamily T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ), 0 ≤ D →
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e') →
    ∃ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink 4 (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ 4) ∧
      LipBound geodSU2 g (fun _ => K) ∧ GaugeInvariant g ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ p, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (randJointLaw T B k j) (fun q => F q.1) p -
          f ((B k j).B p)| ∂(randJointLaw T B k j) ≤ c * Real.exp (-(m * D)) ∧
      ∫ p, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (randJointLaw T B k j) (fun q => G q.1) p -
          g ((B k j).B p)| ∂(randJointLaw T B k j) ≤ c * Real.exp (-(m * D)) ∧
      |∫ p, F p.1 * G p.1 ∂(randJointLaw T B k j) -
          ∫ p, condExp (MeasurableSpace.comap (B k j).B inferInstance) (randJointLaw T B k j) (fun q => F q.1) p *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (randJointLaw T B k j) (fun q => G q.1) p
            ∂(randJointLaw T B k j)|
        ≤ c * Real.exp (-(m * D))

/-- The gauge-invariant transfer implies the old one (it only adds a conclusion). -/
theorem randObsTransferPhysTW_of_inv {T : Tuning} {B : RandBlockingFamily T} (h : RandObsTransferPhysTWInv T B) :
    RandObsTransferPhysTW T B := by
  obtain ⟨m, hm, H⟩ := h
  refine ⟨m, hm, fun R => ?_⟩
  obtain ⟨c, K, hc, hK, k₀, H'⟩ := H R
  refine ⟨c, K, hc, hK, k₀, fun k hk j F G A₀ B₀ D hD mF mG bF bG iF iG dF dG eF eG hsep => ?_⟩
  obtain ⟨f, g, A', B', mf, mg, bf, bg, df, dg, hv, hlip, -, hs, h1, h2, h3⟩ :=
    H' k hk j F G A₀ B₀ D hD mF mG bF bG iF iG dF dG eF eG hsep
  exact ⟨f, g, A', B', mf, mg, bf, bg, df, dg, hv, hlip, hs, h1, h2, h3⟩

/-- **The v4 cut with the gauge-restricted infrared input** (S). The proof of `randTorusDecayLoc_of_blockGapBddW`; the
block gap is only ever applied to the transfer's coarse approximant `g` of the gauge-invariant `G`, which
`RandObsTransferPhysTWInv` makes gauge invariant. -/
theorem randTorusDecayLoc_of_blockGapBddWInv {T : Tuning} (B : RandBlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    (hB : RandBlockGapBddWInv T B lam) (h3 : RandObsTransferPhysTWInv T B) : TorusDecayLoc T.toV := by
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
  have hFm := (O.meas k j).comp (measurable_tShift (G := SU2) (d := 4) (N := T.side k j) (n : ZMod (T.side k j)))
  have hGm := (O.meas k j).comp (measurePreserving_thetaConn (G := SU2) (d := 4) (N := T.side k j)).measurable
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, ⟨vf, hvf, hsv⟩, hlip, hgI, hsep', hEF, hEG, hdec⟩ :=
    htr k hk₁ j _ _ _ _ D hD hFm hGm (fun U => O.bdd k j _) (fun U => O.bdd k j _)
      (gaugeInvariant_tShift (O.gauge k j) _) (gaugeInvariant_thetaConn (O.gauge k j)) hdA hdB eA eB hsepT
  have hx : 0 ≤ D / T.L₁ := by positivity
  have hR' : ∀ x ∈ A', ∀ y ∈ B', D / (2 * T.L₁) ≤ linkDist x y := by
    intro x hx' y hy
    rw [div_le_iff₀ (by positivity)]
    have := hsep' x hx' y hy
    nlinarith
  have hblk := hgap k hk₀ j f g A' B' vf K (D / (2 * T.L₁)) mf mg bf bg hgI dfA dgB hvf hK hlip (by positivity) hR'
  have := UV.ymProb T k j
  have htr' := cov_transfer_rand (T.ym k j) (B k j).P (B k j).meas hFm hGm
    (fun p => O.bdd k j _) (fun p => O.bdd k j _) mf mg bf bg hEF hEG hdec
  have hw : |T.wcorr k j (O.F k j) n| ≤
      C * (1 + ∑ a ∈ A', vf a) * (1 + K) * Real.exp (-(lam * (D / (2 * T.L₁)))) +
        5 * (c * Real.exp (-(m * D))) := by
    unfold Tuning.wcorr corr
    exact htr'.trans (by linarith)
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
  have e1' : lam * (D / (2 * T.L₁)) = 2 * a * (D / T.L₁) := by simp only [a]; field_simp; ring
  have e2' : a * (D / T.L₁) = lam / (4 * T.L₁) * D := by simp only [a]; field_simp
  have hE1 : Real.exp (-(lam / (4 * T.L₁) * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (lam / (4 * T.L₁)) m])
  have hE2 : Real.exp (-(m * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (lam / (4 * T.L₁)) m])
  show |T.wcorr k j (O.F k j) n| ≤ _
  calc |T.wcorr k j (O.F k j) n|
      ≤ C * (1 + ∑ a ∈ A', vf a) * (1 + K) * Real.exp (-(lam * (D / (2 * T.L₁)))) +
          5 * (c * Real.exp (-(m * D))) := hw
    _ ≤ Kc * (1 + D / T.L₁) ^ 4 * Real.exp (-(2 * a * (D / T.L₁))) + 5 * c * Real.exp (-(m' * D)) := by
        rw [e1']
        have h5 : c * Real.exp (-(m * D)) ≤ c * Real.exp (-(m' * D)) := mul_le_mul_of_nonneg_left hE2 hc
        have h6 := mul_le_mul_of_nonneg_right hstep (Real.exp_pos (-(2 * a * (D / T.L₁)))).le
        linarith
    _ = Kc * ((1 + D / T.L₁) ^ 4 * Real.exp (-(2 * a * (D / T.L₁)))) + 5 * c * Real.exp (-(m' * D)) := by ring
    _ ≤ Kc * (24 / a ^ 4 * Real.exp a * Real.exp (-(a * (D / T.L₁)))) + 5 * c * Real.exp (-(m' * D)) := by
        gcongr
    _ = Kc * (24 / a ^ 4 * Real.exp a) * Real.exp (-(lam / (4 * T.L₁) * D)) + 5 * c * Real.exp (-(m' * D)) := by
        rw [e2']; ring
    _ ≤ Kc * (24 / a ^ 4 * Real.exp a) * Real.exp (-(m' * D)) + 5 * c * Real.exp (-(m' * D)) := by gcongr
    _ = (Kc * (24 / a ^ 4 * Real.exp a) + 5 * c) * Real.exp (-(m' * (n * T.a k))) := by ring

/-- **`P4StarInv` and M1's hand-over give the gauge-restricted infrared input** (S). -/
theorem randBlockGapBddWInv_of_p4StarInv {T : Tuning} {B : RandBlockingFamily T} {C : LawClass} {lam : ℝ}
    (hlam : 0 ≤ lam) (hP : P4StarInv C lam) (hM : M1HandOver T B C) : RandBlockGapBddWInv T B lam :=
  randBlockGapBddWInv_of_lawGapBddWInv
    (lawGapBddWInv_of_oneBoxLawInv hlam (fun k j => randBlockedLaw_prob T B k j) (oneBoxLawInv_of_p4StarInv hP hM))

/-- **Assembly from the gauge-restricted `P4StarInv` at M1's hand-over** (S). Open inputs: `OnLCP'`, `NonTrivial`,
`P4StarInv C λ` (the crossover), M1's hand-over into `C`, and the transfer with gauge-invariant coarse approximants. -/
theorem yang_mills_assembly_p4StarInv {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (B : RandBlockingFamily T)
    {C : LawClass} {lam : ℝ} (hlam : 0 < lam) (hP4 : P4StarInv C lam) (hM1 : M1HandOver T B C)
    (hUV : RandObsTransferPhysTWInv T B) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  have hT := randTorusDecayLoc_of_blockGapBddWInv B hlam (randBlockGapBddWInv_of_p4StarInv hlam.le hP4 hM1) hUV
  obtain ⟨hVF, hMF⟩ := bothOrdersLoc_of_torusDecayLoc hL.tendsto_a hT
  exact ⟨hT, hVF, hMF, limitRP T, hN⟩

/-! ## 4. The net form: what a reduction to a finite system must supply -/

section Net

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S]

/-- The unrestricted influence bound is the influence bound on the trivial class. -/
theorem isInfluenceBound_iff_on_true {B : Finset ι} {q : (ι → S) → Measure (ι → S)} {z : ι} {k : ℝ} :
    IsInfluenceBound B q z k ↔ IsInfluenceBoundOn (fun _ _ => True) B q z k :=
  ⟨isInfluenceBoundOn_of, fun h σ s F L hF hdep hosc => h σ s F L hF hdep trivial hosc⟩

/-- **Shell from closeness, outside the shell from the tail** (S). On positions where `p` holds, closeness `δ` to a
reference with influence `κ̄` gives `κ̄ + 2δ`; elsewhere the tail bound `κ̄` must be supplied directly. -/
theorem influence_net_or_tail {Adm : (ι → S) → ((ι → S) → ℝ) → Prop} {B : Finset ι}
    {q q' : (ι → S) → Measure (ι → S)} {z : ι} {kbar δ : ℝ} (p : Prop) [Decidable p]
    (hnet : p → IsInfluenceBoundOn Adm B q z kbar) (hnear : p → IsNearSpec B q q' δ)
    (htail : ¬ p → IsInfluenceBoundOn Adm B q' z kbar) :
    IsInfluenceBoundOn Adm B q' z (if p then kbar + 2 * δ else kbar) := by
  by_cases hp : p
  · simp only [hp, ↓reduceIte]; exact isInfluenceBoundOn_of_near (hnet hp) (hnear hp)
  · simp only [hp, ↓reduceIte]; exact htail hp

end Net

theorem oneBoxSum_mono {U : Type*} [Fintype U] [DecidableEq U] {κ Ehat : U → ℝ} {Λ₀ : Finset U} {lam γ γ' : ℝ}
    (h : OneBoxSum κ Ehat Λ₀ lam γ) (hγ : γ ≤ γ') : OneBoxSum κ Ehat Λ₀ lam γ' :=
  h.trans (mul_le_mul_of_nonneg_right hγ (Nat.cast_nonneg _))

/-- **`P4StarInv` from closeness to reference specifications plus a tail clause** (S). In every volume `j`: a box
`Λ₀ j`, reference influences `κ̄ j` with the one-box sum at `γ`, a shell `sh j` of relative positions of weighted size
`≤ S`, and the margin `γ + 2δS/|Λ₀ j| ≤ γ₁ < 1`. Every law of the class has a gauge-covariant block specification on the
translates of `Λ₀ j` such that, for every block `t`:
* its specification is `δ`-close, worst case over boundary conditions, to a reference specification `q t`;
* on the shell, the reference has influences `≤ κ̄`;
* **off the shell, the law's own specification has influences `≤ κ̄` (the tail clause).**
Then `P4StarInv C λ` with `γ₁`. Closeness does not control the tail: `IsNearSpec` costs `2δ` at **every** position, so a
volume-uniform criterion needs the tail clause, i.e. quasi-locality of the box laws in the boundary condition. That is
the content of (WL). -/
theorem p4StarInv_of_net {C : LawClass} {lam γ γ₁ D₀ δ S : ℝ} {nmax : ℕ} (hγ0 : 0 ≤ γ) (hγ₁ : γ₁ < 1)
    (hδ : 0 ≤ δ) (Λ₀ : ∀ j, Finset (FinLatticeSites 4 (coarseSide j)))
    (κbar : ∀ j, FinLatticeSites 4 (coarseSide j) → ℝ) (sh : ∀ j, Finset (FinLatticeSites 4 (coarseSide j)))
    (hΛ1 : ∀ j, 1 ≤ (Λ₀ j).card) (hΛn : ∀ j, (Λ₀ j).card ≤ nmax)
    (hdiam : ∀ j, ∀ u ∈ Λ₀ j, ∀ u' ∈ Λ₀ j, (siteDist u u' : ℝ) ≤ D₀)
    (hsum : ∀ j, OneBoxSum (κbar j) (boxReach (Λ₀ j)) (Λ₀ j) lam γ)
    (hS : ∀ j, ∑ u ∈ (univ.filter (fun u => u ∉ Λ₀ j)).filter (fun u => u ∈ sh j),
      Real.exp (lam * boxReach (Λ₀ j) u) ≤ S)
    (hmargin : ∀ j, γ + 2 * δ * S / (Λ₀ j).card ≤ γ₁)
    (hclass : ∀ j, ∀ ρ ∈ C j, ∃ (P : BlockSpec ρ (FinLatticeSites 4 (coarseSide j)))
        (q : FinLatticeSites 4 (coarseSide j) → GaugeConnection SU2 4 (coarseSide j) →
          Measure (GaugeConnection SU2 4 (coarseSide j))),
      (∀ t, P.block t = boxBlock (Λ₀ j) t) ∧
      (∀ t, SpecCovariant (gaugeAct (coarseSide j)) (P.spec t)) ∧
      (∀ t, IsNearSpec (P.block t) (q t) (P.spec t) δ) ∧
      (∀ t z, z ∉ P.block t → z.site - t ∈ sh j →
        IsInfluenceBoundOn (ActAdm (gaugeAct (coarseSide j)) (P.block t)) (P.block t) (q t) z
          (κbar j (z.site - t))) ∧
      (∀ t z, z ∉ P.block t → z.site - t ∉ sh j →
        IsInfluenceBoundOn (ActAdm (gaugeAct (coarseSide j)) (P.block t)) (P.block t) (P.spec t) z
          (κbar j (z.site - t)))) :
    P4StarInv C lam := by
  have hS0 : 0 ≤ S := (sum_nonneg fun u _ => (Real.exp_pos _).le).trans (hS 0)
  have h0 : 0 ≤ γ₁ := by
    have h1 := hmargin 0
    have h2 : 0 ≤ 2 * δ * S / ((Λ₀ 0).card : ℝ) := by positivity
    linarith
  refine ⟨γ₁, D₀, nmax, h0, hγ₁, fun j ρ hρ => ?_⟩
  obtain ⟨P, q, hblock, hcov, hnear, hnet, htail⟩ := hclass j ρ hρ
  refine ⟨Λ₀ j, fun u => if u ∈ sh j then κbar j u + 2 * δ else κbar j u, P, hΛ1 j, hΛn j, hdiam j, hblock, hcov,
    fun t z hz => ?_, ?_⟩
  · exact influence_net_or_tail (z.site - t ∈ sh j) (fun hp => hnet t z hz hp) (fun _ => hnear t)
      (fun hp => htail t z hz hp)
  · have hc : 0 < (Λ₀ j).card := by have := hΛ1 j; omega
    have h1 := oneBoxSum_of_near (κ := κbar j) (κ' := fun u => if u ∈ sh j then κbar j u + 2 * δ else κbar j u)
      (sh j) hδ hc (hsum j) (fun u hu => by simp [hu]) (fun u hu => by simp [hu]) (hS j)
    exact oneBoxSum_mono h1 (hmargin j)

/-! ## 5. The other split of P4: landing at `L₁` plus stage two

`P4Star` is one sufficient form of the crossover. The other is the recursion lemma of version 4, which splits P4 into
**the landing** (`LawGapBddW` of the `L₁` laws, the strong-coupling side) and **stage two** (`V4.StageTwoW`: quasi-locality
of the projections `E[f | B₂]` onto the `L₁` block field and conditional decoupling, with errors
`c (1 + Σvf)(1 + Lg) e^{−mR}`). Stage two is the precise Lean form of what the quenched conditional mass (WL) has to
deliver across the crossover (W1-CHAIN.md, section 3). -/

section StageTwo

variable {M : ℕ → ℕ} [∀ j, NeZero (M j)]

/-- **The recursion lemma for any family of `L_*` laws** (S): the proof of `V4.blockGapBddW_of_stageTwo`, with the
blocking of the Wilson measure removed (it was used only to identify the block covariance with a covariance of the
`L_*` law). -/
theorem lawGapBddW_of_stageTwo (ν : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (coarseSide j)))
    (hν : ∀ k j, IsProbabilityMeasure (ν k j))
    (B₂ : ℕ → ∀ j : ℕ, GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j))
    (hB₂ : ∀ k j : ℕ, Measurable (B₂ k j)) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hIR : LawGapBddW (fun k j => (ν k j).map (B₂ k j)) lam₂) (hX : StageTwoW ν B₂ s) :
    ∃ lam : ℝ, 0 < lam ∧ LawGapBddW (M := coarseSide) ν lam := by
  obtain ⟨C₂, hC₂, k₂, H2⟩ := hIR
  obtain ⟨m, c, K, hm, hc, hK, k₃, HX⟩ := hX
  set r := lam₂ / (4 * s)
  have hr : 0 < r := by positivity
  set lam := min r m
  have hlam : 0 < lam := lt_min hr hm
  refine ⟨lam, hlam, C₂ * (1 + K) ^ 2 * (24 / r ^ 4 * Real.exp r) + 5 * c, by positivity, max k₂ k₃,
    fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR => ?_⟩
  have hk₂ : k₂ ≤ k := (le_max_left _ _).trans hk
  have hk₃ : k₃ ≤ k := (le_max_right _ _).trans hk
  have hS : 0 ≤ ∑ a ∈ A, vf a := sum_osc_nonneg hvf A
  obtain ⟨f₂, g₂, A₂, S₂, v₂, L₂, mf₂, mg₂, bf₂, bg₂, hf₂A, hg₂S, hv₂, hsum₂, hL₂0, hL₂, hlip₂, hsep₂, hEF, hEG,
    hdec⟩ := HX k hk₃ j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR
  have := hν k j
  -- transfer to `L₁` on the `L_*` law
  have htr := cov_transfer (ν k j) (hB₂ k j) mf mg bf bg mf₂ mg₂ bf₂ bg₂ hEF hEG hdec
  rw [Effective.cov_map (ν k j) (hB₂ k j) ⟨mf₂, 1, bf₂⟩ ⟨mg₂, 1, bg₂⟩] at htr
  -- the `L₁` input
  have hsep' : ∀ x ∈ A₂, ∀ y ∈ S₂, R / (2 * s) ≤ linkDist x y := by
    intro x hx y hy
    rw [div_le_iff₀ (by positivity)]
    have := hsep₂ x hx y hy
    linarith
  have hir := H2 k hk₂ j f₂ g₂ A₂ S₂ v₂ L₂ (R / (2 * s)) mf₂ mg₂ bf₂ bg₂ hf₂A hg₂S hv₂ hL₂0 hlip₂ (by positivity) hsep'
  beta_reduce at hir
  -- constants
  set S := ∑ a ∈ A, vf a
  have hS4 : 1 ≤ (1 + R) ^ 4 := one_le_pow₀ (by linarith)
  have hP : 1 ≤ (1 + S) * (1 + R) ^ 4 := one_le_mul_of_one_le_of_one_le (by linarith) hS4
  have hv2 : 1 + ∑ a ∈ A₂, v₂ a ≤ (1 + K) * ((1 + S) * (1 + R) ^ 4) := by
    have e : K * (1 + S) * (1 + R) ^ 4 = K * ((1 + S) * (1 + R) ^ 4) := by ring
    have e' : (1 + K) * ((1 + S) * (1 + R) ^ 4) = (1 + S) * (1 + R) ^ 4 + K * ((1 + S) * (1 + R) ^ 4) := by ring
    linarith
  have hl2 : 1 + L₂ ≤ (1 + K) * (1 + Lg) := by
    have e' : (1 + K) * (1 + Lg) = 1 + Lg + K * (1 + Lg) := by ring
    linarith
  have hv2' : 0 ≤ 1 + ∑ a ∈ A₂, v₂ a := by have := sum_osc_nonneg hv₂ A₂; linarith
  have hprod : C₂ * (1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂) ≤
      C₂ * (1 + K) ^ 2 * (1 + S) * (1 + Lg) * (1 + R) ^ 4 := by
    have h1 : (1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂) ≤ ((1 + K) * ((1 + S) * (1 + R) ^ 4)) * ((1 + K) * (1 + Lg)) :=
      mul_le_mul hv2 hl2 (by linarith) (mul_nonneg (by linarith) (by linarith))
    calc C₂ * (1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂) = C₂ * ((1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂)) := by ring
      _ ≤ C₂ * (((1 + K) * ((1 + S) * (1 + R) ^ 4)) * ((1 + K) * (1 + Lg))) :=
          mul_le_mul_of_nonneg_left h1 hC₂
      _ = C₂ * (1 + K) ^ 2 * (1 + S) * (1 + Lg) * (1 + R) ^ 4 := by ring
  have e1 : lam₂ * (R / (2 * s)) = 2 * r * R := by simp only [r]; field_simp; ring
  have hpoly := poly_exp_le hr hR0
  have hE1 : Real.exp (-(r * R)) ≤ Real.exp (-(lam * R)) :=
    Real.exp_le_exp.mpr (by have := mul_le_mul_of_nonneg_right (min_le_left r m) hR0; linarith)
  have hE2 : Real.exp (-(m * R)) ≤ Real.exp (-(lam * R)) :=
    Real.exp_le_exp.mpr (by have := mul_le_mul_of_nonneg_right (min_le_right r m) hR0; linarith)
  set P := C₂ * (1 + K) ^ 2 * (1 + S) * (1 + Lg) with hPdef
  have hQ0 : 0 ≤ (1 + S) * (1 + Lg) := mul_nonneg (by linarith) (by linarith)
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    have : 0 ≤ C₂ * (1 + K) ^ 2 := mul_nonneg hC₂ (by positivity)
    have := mul_nonneg this hQ0
    calc (0 : ℝ) ≤ C₂ * (1 + K) ^ 2 * ((1 + S) * (1 + Lg)) := this
      _ = C₂ * (1 + K) ^ 2 * (1 + S) * (1 + Lg) := by ring
  calc _ ≤ |∫ x, f₂ x * g₂ x ∂((ν k j).map (B₂ k j)) -
          (∫ x, f₂ x ∂((ν k j).map (B₂ k j))) * ∫ x, g₂ x ∂((ν k j).map (B₂ k j))| +
          5 * (c * (1 + S) * (1 + Lg) * Real.exp (-(m * R))) := htr
    _ ≤ C₂ * (1 + ∑ a ∈ A₂, v₂ a) * (1 + L₂) * Real.exp (-(lam₂ * (R / (2 * s)))) +
          5 * (c * (1 + S) * (1 + Lg) * Real.exp (-(m * R))) := by linarith [hir]
    _ ≤ P * (1 + R) ^ 4 * Real.exp (-(2 * r * R)) +
          5 * c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) := by
        rw [e1]
        have h6 := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-(2 * r * R))).le
        have h7 : c * ((1 + S) * (1 + Lg)) * Real.exp (-(m * R)) ≤
            c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) :=
          mul_le_mul_of_nonneg_left hE2 (mul_nonneg hc hQ0)
        have e3 : c * (1 + S) * (1 + Lg) * Real.exp (-(m * R)) = c * ((1 + S) * (1 + Lg)) * Real.exp (-(m * R)) := by
          ring
        rw [hPdef]
        linarith [h6, h7, e3]
    _ = P * ((1 + R) ^ 4 * Real.exp (-(2 * r * R))) +
          5 * c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) := by ring
    _ ≤ P * (24 / r ^ 4 * Real.exp r * Real.exp (-(r * R))) +
          5 * c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) := by gcongr
    _ ≤ P * (24 / r ^ 4 * Real.exp r * Real.exp (-(lam * R))) +
          5 * c * ((1 + S) * (1 + Lg)) * Real.exp (-(lam * R)) := by gcongr
    _ = (C₂ * (1 + K) ^ 2 * (24 / r ^ 4 * Real.exp r) + 5 * c) * (1 + S) * (1 + Lg) * Real.exp (-(lam * R)) := by
        rw [hPdef]; ring

/-- **The other split of P4, for M1's randomized blocking** (S): the landing at `L₁` and stage two give the v4 infrared
input. -/
theorem randBlockGapBddW_of_stageTwo {T : Tuning} (B : RandBlockingFamily T)
    (B₂ : ℕ → ∀ j : ℕ, GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j))
    (hB₂ : ∀ k j : ℕ, Measurable (B₂ k j)) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hIR : LawGapBddW (fun k j => (randBlockedLaw T B k j).map (B₂ k j)) lam₂)
    (hX : StageTwoW (randBlockedLaw T B) B₂ s) : ∃ lam : ℝ, 0 < lam ∧ RandBlockGapBddW T B lam := by
  obtain ⟨lam, hlam, h⟩ :=
    lawGapBddW_of_stageTwo (randBlockedLaw T B) (randBlockedLaw_prob T B) B₂ hB₂ hs hlam₂ hIR hX
  exact ⟨lam, hlam, randBlockGapBddW_of_lawGapBddW h⟩

/-- **Assembly from the landing at `L₁` and stage two over M1's hand-over** (S). Open inputs: `OnLCP'`, `NonTrivial`,
the `L₁` law gap of the blocked hand-over laws (landing), stage two across the crossover (the content of (WL)), and the
ultraviolet transfer. -/
theorem yang_mills_assembly_stageTwo {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (B : RandBlockingFamily T)
    (B₂ : ℕ → ∀ j : ℕ, GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j))
    (hB₂ : ∀ k j : ℕ, Measurable (B₂ k j)) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hIR : LawGapBddW (fun k j => (randBlockedLaw T B k j).map (B₂ k j)) lam₂)
    (hX : StageTwoW (randBlockedLaw T B) B₂ s) (hUV : RandObsTransferPhysTW T B) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  obtain ⟨lam, hlam, h⟩ := randBlockGapBddW_of_stageTwo B B₂ hB₂ hs hlam₂ hIR hX
  exact yang_mills_assembly_v4_bdd_rand hL hN B hlam h hUV

end StageTwo

end ProofPhase.Crossover
