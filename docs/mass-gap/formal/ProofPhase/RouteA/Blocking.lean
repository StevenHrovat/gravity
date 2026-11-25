/-
Proof phase (round 5), workstream 1 (Route A): a good blocking (blueprint P1.8, free win 3), 2026-11-22.
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/ws1-routeA/NOTE.md`, section 2.
-/

import ProofPhase.Assembly
import Attempts.R4.LayerDecimation

/-!
# Slice smearing with time decimation: a reflection-positive blocking that is not a decimation

Reflection positivity is needed for the time reflection only, so a blocking may average freely **inside each time slice**
and over the **time strip** between two coarse slices, as long as the averaging pattern is symmetric under the strip's own
mirror. This file constructs such a blocking concretely for SU(2) and proves that it is reflection-respecting
(`RPBlocking`), so that `ProofPhase.blocked_wilson_rp` applies to it at every level.

**The step (`smearBlock w`, factor 2, all directions).** For the coarse link `(x, μ)` of `(ℤ/Mℤ)^d` with fine base site
`f = 2x` of `(ℤ/2Mℤ)^d`, sum the parallel transports along

* the straight path `f → f + 2e_μ` (the decimation path), and
* the staples `f → f ± e_ν → f ± e_ν + 2e_μ → f + 2e_μ` for every **spatial** direction `ν ≠ μ` (both signs),
  with weight `w ≥ 0`,

and project the sum (a real multiple of an SU(2) matrix) back to SU(2) by `A ↦ A / √|det A|` (`projSU2`). For a spatial
coarse link all paths lie in the fine time slice `t = 2x₀`; for a temporal coarse link all paths lie in the fine time strip
`[2x₀, 2x₀ + 2]`, and the staple family is mapped to itself by the strip's mirror combined with path reversal. With `w = 0`
it is the decimation of round 4 (`smearBlock_zero`).

**Proved here.**
* `walk_thetaConn`, `walk_rev`: transport along a path of the reflected field is transport along the mirrored path; the
  reversed path carries the inverse.
* `projSU2_star`: the projection commutes with `A ↦ A^†` (so with inversion), `projSU2_coe`: it fixes SU(2).
* `smearBlock_thetaConn`: **the step commutes with the time reflection**.
* `linkDep_smearBlock`: **a coarse observable of the closed coarse positive half lifts to the closed fine positive half**
  (coarse side even).
* `smearRP`: the step as an `RPBlocking`; `RPBlocking.comp`, `RPBlocking.cast`, `smearIter`: `n` steps
  (`2^n M → M`); `goodBlocking`: a `BlockingFamily` for every tuning with dyadic resolution `ℓ_k = 2^{n_k}`;
  `goodBlocking_rp`: **every blocked layer is reflection positive** (via `blocked_wilson_rp`).
* `smearBlock_zero`: `w = 0` is the decimation.

**Claim level.** Construction and the two geometric properties: concrete, elementary (substantive only in that they hold
for this non-decimation map). Reflection positivity itself is then `blocked_wilson_rp`, which holds for any map with the
two properties (definitional given them). **Not proved here:** that the iterated blocking has a non-trivial continuum limit
at fixed physical `L₁` (power counting in `NOTE.md` §2: slice smearing removes the linear self-energy divergence that makes
decimation converge to pure noise); gauge and centre covariance (exact off the null set where the path sum vanishes, on
paper in `NOTE.md`).
-/

open MeasureTheory Finset AreaLaw.Concrete Positivity Attempts.R4.Layer

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.RouteA

/-! ## Lattice paths -/

/-- A step of a lattice path: a direction and an orientation (`true`: forward along the link). -/
abbrev Step (d : ℕ) := Fin d × Bool

section Paths

variable {d N : ℕ}

/-- The site one step back in direction `ν`. -/
def stepBack (x : FinLatticeSites d N) (ν : Fin d) : FinLatticeSites d N := Function.update x ν (x ν - 1)

/-- The site after one step. -/
def nextSite (x : FinLatticeSites d N) : Step d → FinLatticeSites d N
  | (ν, true) => siteShift d N x ν
  | (ν, false) => stepBack x ν

/-- The link traversed by one step. -/
def stepLink (x : FinLatticeSites d N) : Step d → LatticeLink d N
  | (ν, true) => ⟨x, ν⟩
  | (ν, false) => ⟨stepBack x ν, ν⟩

/-- The parallel transport of one step (a backward step carries the inverse). -/
def stepVal {G : Type*} [Group G] (U : GaugeConnection G d N) (x : FinLatticeSites d N) : Step d → G
  | (ν, true) => U ⟨x, ν⟩
  | (ν, false) => (U ⟨stepBack x ν, ν⟩)⁻¹

/-- The parallel transport along a path from `x`. -/
def walk {G : Type*} [Group G] (U : GaugeConnection G d N) : FinLatticeSites d N → List (Step d) → G
  | _, [] => 1
  | x, s :: ss => stepVal U x s * walk U (nextSite x s) ss

/-- The links traversed by a path from `x`. -/
def walkLinks : FinLatticeSites d N → List (Step d) → List (LatticeLink d N)
  | _, [] => []
  | x, s :: ss => stepLink x s :: walkLinks (nextSite x s) ss

/-- The end point of a path from `x`. -/
def endSite : FinLatticeSites d N → List (Step d) → FinLatticeSites d N
  | x, [] => x
  | x, s :: ss => endSite (nextSite x s) ss

/-- A step reversed. -/
def flipS (s : Step d) : Step d := (s.1, !s.2)

/-- A path reversed. -/
def revPath (ss : List (Step d)) : List (Step d) := (ss.map flipS).reverse

theorem stepBack_siteShift (x : FinLatticeSites d N) (ν : Fin d) : stepBack (siteShift d N x ν) ν = x := by
  funext i
  simp only [stepBack, siteShift, Function.update_apply]
  split_ifs with h <;> simp_all

theorem siteShift_stepBack (x : FinLatticeSites d N) (ν : Fin d) : siteShift d N (stepBack x ν) ν = x := by
  funext i
  simp only [stepBack, siteShift, Function.update_apply]
  split_ifs with h <;> simp_all

theorem nextSite_flipS (x : FinLatticeSites d N) (s : Step d) : nextSite (nextSite x s) (flipS s) = x := by
  rcases s with ⟨ν, _ | _⟩
  · exact siteShift_stepBack x ν
  · exact stepBack_siteShift x ν

theorem stepVal_flipS {G : Type*} [Group G] (U : GaugeConnection G d N) (x : FinLatticeSites d N) (s : Step d) :
    stepVal U (nextSite x s) (flipS s) = (stepVal U x s)⁻¹ := by
  rcases s with ⟨ν, _ | _⟩
  · simp [stepVal, nextSite, flipS]
  · simp [stepVal, nextSite, flipS, stepBack_siteShift]

theorem walk_congr {G : Type*} [Group G] {U V : GaugeConnection G d N} {x : FinLatticeSites d N}
    {ss : List (Step d)} (h : ∀ l ∈ walkLinks x ss, U l = V l) : walk U x ss = walk V x ss := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    have h1 : stepVal U x s = stepVal V x s := by
      have := h _ List.mem_cons_self
      rcases s with ⟨ν, _ | _⟩
      · simp only [stepVal]; simp only [walkLinks, stepLink] at this; rw [this]
      · simp only [stepVal]; simp only [walkLinks, stepLink] at this; rw [this]
    simp only [walk]
    rw [h1, ih (fun l hl => h l (List.mem_cons_of_mem _ hl))]

theorem walk_append {G : Type*} [Group G] (U : GaugeConnection G d N) (x : FinLatticeSites d N)
    (ss tt : List (Step d)) : walk U x (ss ++ tt) = walk U x ss * walk U (endSite x ss) tt := by
  induction ss generalizing x with
  | nil => simp [walk, endSite]
  | cons s ss ih => simp only [List.cons_append, walk, endSite, ih, mul_assoc]

theorem endSite_append (x : FinLatticeSites d N) (ss tt : List (Step d)) :
    endSite x (ss ++ tt) = endSite (endSite x ss) tt := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih => exact ih _

theorem revPath_cons (s : Step d) (ss : List (Step d)) : revPath (s :: ss) = revPath ss ++ [flipS s] := by
  simp [revPath]

theorem endSite_rev (x : FinLatticeSites d N) (ss : List (Step d)) : endSite (endSite x ss) (revPath ss) = x := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    rw [revPath_cons, endSite_append]
    show endSite (endSite (endSite (nextSite x s) ss) (revPath ss)) [flipS s] = x
    rw [ih]
    exact nextSite_flipS x s

/-- **The reversed path carries the inverse transport.** -/
theorem walk_rev {G : Type*} [Group G] (U : GaugeConnection G d N) (x : FinLatticeSites d N) (ss : List (Step d)) :
    walk U (endSite x ss) (revPath ss) = (walk U x ss)⁻¹ := by
  induction ss generalizing x with
  | nil => simp [walk, endSite, revPath]
  | cons s ss ih =>
    rw [revPath_cons, walk_append]
    show walk U (endSite (nextSite x s) ss) (revPath ss) *
        walk U (endSite (endSite (nextSite x s) ss) (revPath ss)) [flipS s] = _
    rw [ih, endSite_rev]
    simp only [walk, mul_one, stepVal_flipS, mul_inv_rev]

/-! ### Paths under the time reflection -/

variable [NeZero d]

/-- The mirror of a step under `t ↦ −t`: temporal steps change orientation. -/
def flipT (s : Step d) : Step d := if s.1 = 0 then (s.1, !s.2) else s

theorem reflSite_stepBack (x : FinLatticeSites d N) {ν : Fin d} (hν : ν ≠ 0) :
    reflSite (stepBack x ν) = stepBack (reflSite x) ν := by
  funext i
  simp only [reflSite, stepBack, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem reflSite_stepBack_zero (x : FinLatticeSites d N) : reflSite (stepBack x 0) = siteShift d N (reflSite x) 0 := by
  funext i
  simp only [reflSite, stepBack, siteShift, Function.update_apply]
  split_ifs <;> simp_all; ring

theorem tflipSite_eq_stepBack (x : FinLatticeSites d N) : tflipSite x = stepBack (reflSite x) 0 := by
  funext i
  simp only [reflSite, stepBack, tflipSite, Function.update_apply]
  split_ifs <;> simp_all

theorem tflipSite_stepBack_zero (x : FinLatticeSites d N) : tflipSite (stepBack x 0) = reflSite x := by
  funext i
  simp only [reflSite, stepBack, tflipSite, Function.update_apply]
  split_ifs <;> simp_all

theorem stepVal_thetaConn {G : Type*} [Group G] (U : GaugeConnection G d N) (x : FinLatticeSites d N) (s : Step d) :
    stepVal (thetaConn U) x s = stepVal U (reflSite x) (flipT s) ∧
      reflSite (nextSite x s) = nextSite (reflSite x) (flipT s) := by
  rcases s with ⟨ν, _ | _⟩ <;> by_cases hν : ν = 0
  · subst hν
    refine ⟨?_, ?_⟩
    · simp [stepVal, flipT, thetaConn, mirrorLink, tflipSite_stepBack_zero]
    · simp [nextSite, flipT, reflSite_stepBack_zero]
  · refine ⟨?_, ?_⟩
    · simp [stepVal, flipT, thetaConn, mirrorLink, hν, reflSite_stepBack x hν]
    · simp [nextSite, flipT, hν, reflSite_stepBack x hν]
  · subst hν
    refine ⟨?_, ?_⟩
    · simp [stepVal, flipT, thetaConn, mirrorLink, tflipSite_eq_stepBack]
    · simp [nextSite, flipT, reflSite_siteShift_zero, tflipSite_eq_stepBack]
  · refine ⟨?_, ?_⟩
    · simp [stepVal, flipT, thetaConn, mirrorLink, hν]
    · simp [nextSite, flipT, hν, reflSite_siteShift x hν]

/-- **Transport of the reflected field along a path is transport along the mirrored path.** -/
theorem walk_thetaConn {G : Type*} [Group G] (U : GaugeConnection G d N) (x : FinLatticeSites d N)
    (ss : List (Step d)) : walk (thetaConn U) x ss = walk U (reflSite x) (ss.map flipT) := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih =>
    obtain ⟨h1, h2⟩ := stepVal_thetaConn U x s
    simp only [walk, List.map_cons, h1, ih, h2]

end Paths

/-! ## The smearing paths -/

section Smear

variable {d : ℕ}

/-- The straight path of two steps along `μ`. -/
def straight (μ : Fin d) : List (Step d) := [(μ, true), (μ, true)]

/-- The staple: one step along `±ν`, two along `μ`, one back along `ν`. -/
def staple (μ ν : Fin d) (b : Bool) : List (Step d) := [(ν, b), (μ, true), (μ, true), (ν, !b)]

variable [NeZero d]

/-- The smearing directions of a coarse link in direction `μ`: spatial and different from `μ`. -/
def transverse (μ : Fin d) : Finset (Fin d) := univ.filter fun ν => ν ≠ 0 ∧ ν ≠ μ

theorem mem_transverse {μ ν : Fin d} : ν ∈ transverse μ ↔ ν ≠ 0 ∧ ν ≠ μ := by simp [transverse]

/-! ## The projection onto SU(2) -/

/-- The normalisation `|det A|^{-1/2}`. -/
def nrmC (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (Real.sqrt ‖A.det‖)⁻¹

/-- `A / √|det A|` if that lies in SU(2) (it does for every nonzero real multiple of an SU(2) matrix), else `1`. -/
def projVal (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if ((nrmC A : ℂ) • A) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ then (nrmC A : ℂ) • A else 1

theorem projVal_mem (A : Matrix (Fin 2) (Fin 2) ℂ) : projVal A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  unfold projVal
  split_ifs with h
  · exact h
  · exact one_mem _

/-- **The projection onto SU(2).** -/
def projSU2 (A : Matrix (Fin 2) (Fin 2) ℂ) : SU2 := ⟨projVal A, projVal_mem A⟩

theorem nrmC_star (A : Matrix (Fin 2) (Fin 2) ℂ) : nrmC (star A) = nrmC A := by
  unfold nrmC
  rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, norm_star]

theorem star_mem_SU2_iff (B : Matrix (Fin 2) (Fin 2) ℂ) :
    star B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ ↔ B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_specialUnitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.det_conjTranspose, ← Matrix.star_eq_conjTranspose]
  have hu : star B ∈ Matrix.unitaryGroup (Fin 2) ℂ ↔ B ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_star, ← Matrix.mem_unitaryGroup_iff']
  rw [hu]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := congrArg star h2
    rwa [star_star, star_one] at this
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2, star_one]⟩

theorem smul_star (c : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) : (c : ℂ) • star A = star ((c : ℂ) • A) := by
  rw [star_smul, Complex.star_def, Complex.conj_ofReal]

/-- **The projection commutes with `A ↦ A^†`**, i.e. with inversion on SU(2). -/
theorem projSU2_star (A : Matrix (Fin 2) (Fin 2) ℂ) : projSU2 (star A) = (projSU2 A)⁻¹ := by
  apply Subtype.ext
  show projVal (star A) = star (projVal A)
  unfold projVal
  rw [nrmC_star, smul_star]
  by_cases h : ((nrmC A : ℂ) • A) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ
  · rw [ite_eq_left ((star_mem_SU2_iff _).mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ((star_mem_SU2_iff _).mp h')), ite_eq_right h, star_one]

/-- The projection fixes SU(2). -/
theorem projSU2_coe (g : SU2) : projSU2 (g : Matrix (Fin 2) (Fin 2) ℂ) = g := by
  apply Subtype.ext
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  have hc : nrmC (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by simp [nrmC, hdet]
  show projVal _ = _
  unfold projVal
  rw [hc]
  simp only [Complex.ofReal_one, one_smul]
  rw [ite_eq_left g.2]

theorem measurable_projSU2 : Measurable projSU2 := by
  have hc : Measurable nrmC := (Real.continuous_sqrt.comp (continuous_norm.comp
    (continuous_id.matrix_det))).measurable.inv
  have hs : Measurable fun A : Matrix (Fin 2) (Fin 2) ℂ => (nrmC A : ℂ) • A :=
    (Complex.continuous_ofReal.measurable.comp hc).smul measurable_id
  have hS : MeasurableSet (Matrix.specialUnitaryGroup (Fin 2) ℂ : Set (Matrix (Fin 2) (Fin 2) ℂ)) :=
    isCompact_SU2.isClosed.measurableSet
  have hv : Measurable projVal := Measurable.ite (hs hS) hs measurable_const
  exact hv.subtype_mk

/-! ## The smeared step -/

variable {M : ℕ} [NeZero M]

/-- The weighted sum of transports from `f` along the straight path and the staples of direction `μ`. -/
def smearSum {N : ℕ} (w : ℝ) (U : GaugeConnection SU2 d N) (f : FinLatticeSites d N) (μ : Fin d) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((walk U f (straight μ) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) +
    (w : ℂ) • ∑ ν ∈ transverse μ, ∑ b : Bool, ((walk U f (staple μ ν b) : SU2) : Matrix (Fin 2) (Fin 2) ℂ)

/-- **The slice-smeared, time-decimated blocking step** `(ℤ/2Mℤ)^d → (ℤ/Mℤ)^d`. -/
def smearBlock (w : ℝ) (U : GaugeConnection SU2 d (2 * M)) : GaugeConnection SU2 d M :=
  fun l => projSU2 (smearSum w U (fineSite l.site) l.dir)

/-- **`w = 0` is the decimation of round 4.** -/
theorem smearBlock_zero : smearBlock (d := d) (M := M) 0 = decimate := by
  funext U l
  simp only [smearBlock, smearSum, Complex.ofReal_zero, zero_smul, add_zero]
  rw [projSU2_coe]
  simp [walk, straight, stepVal, nextSite, decimate, firstLink, secondLink]

theorem continuous_walk {N : ℕ} (x : FinLatticeSites d N) (ss : List (Step d)) :
    Continuous fun U : GaugeConnection SU2 d N => walk U x ss := by
  induction ss generalizing x with
  | nil => exact continuous_const
  | cons s ss ih =>
    simp only [walk]
    refine Continuous.mul ?_ (ih _)
    rcases s with ⟨ν, _ | _⟩
    · exact (continuous_apply _).inv
    · exact continuous_apply _

theorem measurable_smearBlock (w : ℝ) : Measurable (smearBlock (d := d) (M := M) w) := by
  refine measurable_pi_iff.mpr fun l => measurable_projSU2.comp ?_
  have hc : ∀ ss : List (Step d), Continuous fun U : GaugeConnection SU2 d (2 * M) =>
      ((walk U (fineSite l.site) ss : SU2) : Matrix (Fin 2) (Fin 2) ℂ) :=
    fun ss => continuous_subtype_val.comp (continuous_walk _ ss)
  refine Continuous.measurable ?_
  have hs : Continuous fun U : GaugeConnection SU2 d (2 * M) => ∑ ν ∈ transverse l.dir, ∑ b : Bool,
      ((walk U (fineSite l.site) (staple l.dir ν b) : SU2) : Matrix (Fin 2) (Fin 2) ℂ) :=
    continuous_finsetSum _ fun ν _ => continuous_finsetSum _ fun b _ => hc _
  exact (hc _).add (hs.const_smul (w : ℂ))

/-! ### Reflection covariance -/

theorem map_flipT_straight {μ : Fin d} (hμ : μ ≠ 0) : (straight μ).map flipT = straight μ := by
  simp [straight, flipT, hμ]

theorem map_flipT_staple {μ ν : Fin d} (hμ : μ ≠ 0) (hν : ν ≠ 0) (b : Bool) :
    (staple μ ν b).map flipT = staple μ ν b := by
  simp [staple, flipT, hμ, hν]

theorem map_flipT_straight_zero : (straight (0 : Fin d)).map flipT = revPath (straight 0) := by
  simp [straight, flipT, revPath, flipS]

theorem map_flipT_staple_zero {ν : Fin d} (hν : ν ≠ 0) (b : Bool) :
    (staple 0 ν b).map flipT = revPath (staple 0 ν b) := by
  simp [staple, flipT, revPath, flipS, hν]

theorem endSite_straight_zero {N : ℕ} (y : FinLatticeSites d N) :
    endSite y (straight 0) = siteShift d N (siteShift d N y 0) 0 := by
  simp [straight, endSite, nextSite]

theorem endSite_staple_zero {N : ℕ} (y : FinLatticeSites d N) {ν : Fin d} (hν : ν ≠ 0) (b : Bool) :
    endSite y (staple 0 ν b) = siteShift d N (siteShift d N y 0) 0 := by
  have h0 : (0 : Fin d) ≠ ν := Ne.symm hν
  cases b <;>
  · funext i
    simp only [staple, endSite, nextSite, stepBack, siteShift, Bool.not_true, Bool.not_false, Function.update_apply]
    by_cases hi0 : i = 0
    · subst hi0; simp [h0]
    · by_cases hiν : i = ν
      · subst hiν; simp [hν]
      · simp [hi0, hiν]

/-- The temporal coarse link: transport of the reflected field from `2x` is the inverse transport from `2·tflip(x)`. -/
theorem walk_thetaConn_temporal (U : GaugeConnection SU2 d (2 * M)) (x : FinLatticeSites d M) {γ : List (Step d)}
    (hγ : γ.map flipT = revPath γ)
    (hend : endSite (fineSite (tflipSite x)) γ = siteShift d (2 * M) (siteShift d (2 * M) (fineSite (tflipSite x)) 0) 0) :
    ((walk (thetaConn U) (fineSite x) γ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      star ((walk U (fineSite (tflipSite x)) γ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [walk_thetaConn, hγ]
  have e : reflSite (fineSite x) = endSite (fineSite (tflipSite x)) γ := by
    rw [hend, siteShift_fineSite_tflipSite, siteShift_tflipSite_zero]
  rw [e, walk_rev]
  rfl

/-- **The smeared step commutes with the time reflection**: `B(Θ_f U) = Θ_c(B U)`. -/
theorem smearBlock_thetaConn (w : ℝ) (U : GaugeConnection SU2 d (2 * M)) :
    smearBlock w (thetaConn U) = thetaConn (smearBlock w U) := by
  funext l
  rcases l with ⟨x, μ⟩
  by_cases hμ : μ = 0
  · subst hμ
    simp only [smearBlock, thetaConn, mirrorLink, ↓reduceIte]
    rw [← projSU2_star]
    congr 1
    simp only [smearSum, star_add, star_sum, ← smul_star]
    congr 1
    · exact walk_thetaConn_temporal U x map_flipT_straight_zero (endSite_straight_zero _)
    · congr 1
      refine Finset.sum_congr rfl fun ν hν => Finset.sum_congr rfl fun b _ => ?_
      have hν0 := (mem_transverse.mp hν).1
      exact walk_thetaConn_temporal U x (map_flipT_staple_zero hν0 b) (endSite_staple_zero _ hν0 b)
  · simp only [smearBlock, thetaConn, mirrorLink, hμ, ↓reduceIte]
    congr 1
    simp only [smearSum, walk_thetaConn, fineSite_reflSite]
    congr 1
    · rw [map_flipT_straight hμ]
    · congr 1
      refine Finset.sum_congr rfl fun ν hν => Finset.sum_congr rfl fun b _ => ?_
      rw [map_flipT_staple hμ (mem_transverse.mp hν).1 b]

/-! ### The closed positive half lifts to the closed positive half -/

theorem mem_posHalf_spatial {K : ℕ} [NeZero K] {l : LatticeLink d K} (hd : l.dir ≠ 0) (ht : (l.site 0).val ≤ K / 2) :
    l ∈ posHalfLinks d K := by
  rw [mem_posHalfLinks_iff]
  unfold IsPosLink IsFixedLink
  rcases Nat.eq_zero_or_pos (l.site 0).val with h0 | h0
  · exact Or.inr ⟨hd, Or.inl h0⟩
  · rcases lt_or_eq_of_le ht with h1 | h1
    · exact Or.inl (Or.inl ⟨hd, h0, h1⟩)
    · exact Or.inr ⟨hd, Or.inr h1⟩

theorem mem_posHalf_temporal {K : ℕ} [NeZero K] {l : LatticeLink d K} (hd : l.dir = 0) (ht : (l.site 0).val < K / 2) :
    l ∈ posHalfLinks d K := by
  rw [mem_posHalfLinks_iff]
  exact Or.inl (Or.inr ⟨hd, ht⟩)

theorem val_dbl_add_two (a : ZMod M) (h : a.val + 1 < M) : (dbl a + 1 + 1).val = 2 * a.val + 2 := by
  have e : dbl a + 1 + 1 = ((2 * a.val + 2 : ℕ) : ZMod (2 * M)) := by unfold dbl; push_cast; ring
  rw [e]; exact ZMod.val_cast_of_lt (by omega)

theorem stepBack_zero_of_ne {N : ℕ} (x : FinLatticeSites d N) {ν : Fin d} (hν : ν ≠ 0) : stepBack x ν 0 = x 0 := by
  simp [stepBack, Function.update_of_ne (Ne.symm hν)]

theorem nextSite_zero_of_ne {N : ℕ} (x : FinLatticeSites d N) {ν : Fin d} (hν : ν ≠ 0) (b : Bool) :
    nextSite x (ν, b) 0 = x 0 := by
  cases b
  · exact stepBack_zero_of_ne x hν
  · exact siteShift_zero_of_ne x hν

theorem stepLink_zero_of_ne {N : ℕ} (x : FinLatticeSites d N) {ν : Fin d} (hν : ν ≠ 0) (b : Bool) :
    (stepLink x (ν, b)).site 0 = x 0 ∧ (stepLink x (ν, b)).dir = ν := by
  cases b
  · exact ⟨stepBack_zero_of_ne x hν, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- Every link of a smearing path of a coarse link of the closed coarse positive half lies in the closed fine positive
half (coarse side even). -/
theorem walkLinks_mem (hM : Even M) {x : FinLatticeSites d M} {μ : Fin d} (hl : (⟨x, μ⟩ : LatticeLink d M) ∈ posHalfLinks d M)
    {γ : List (Step d)} (hγ : γ = straight μ ∨ ∃ ν b, ν ∈ transverse μ ∧ γ = staple μ ν b) :
    ∀ e ∈ walkLinks (fineSite x) γ, e ∈ posHalfLinks d (2 * M) := by
  obtain ⟨k, hk⟩ := hM
  have hK : (2 * M) / 2 = M := by omega
  have hv := val_dbl (x 0)
  have hf0 : fineSite x 0 = dbl (x 0) := rfl
  rw [mem_posHalfLinks_iff] at hl
  unfold IsPosLink IsFixedLink at hl
  simp only at hl
  rcases hγ with rfl | ⟨ν, b, hν, rfl⟩
  · -- the straight path: the decimation links
    intro e he
    simp only [straight, walkLinks, stepLink, nextSite, List.mem_cons, List.not_mem_nil, or_false] at he
    have hl' : (⟨x, μ⟩ : LatticeLink d M) ∈ posHalfLinks d M := by
      rw [mem_posHalfLinks_iff]; unfold IsPosLink IsFixedLink; exact hl
    rcases he with rfl | rfl
    · exact firstLink_mem ⟨k, hk⟩ hl'
    · exact secondLink_mem ⟨k, hk⟩ hl'
  · obtain ⟨hν0, hνμ⟩ := mem_transverse.mp hν
    intro e he
    simp only [staple, walkLinks, List.mem_cons, List.not_mem_nil, or_false] at he
    set f1 := nextSite (fineSite x) (ν, b)
    have hf1 : f1 0 = dbl (x 0) := by
      show nextSite (fineSite x) (ν, b) 0 = _
      rw [nextSite_zero_of_ne _ hν0]; rfl
    by_cases hμ : μ = 0
    · subst hμ
      have hx : (x 0).val < M / 2 := by
        rcases hl with (⟨h, -⟩ | ⟨-, h⟩) | ⟨h, -⟩
        · exact absurd rfl h
        · exact h
        · exact absurd rfl h
      have h2 : (x 0).val + 1 < M := by omega
      have hs1 : nextSite f1 (0, true) 0 = dbl (x 0) + 1 := by
        show siteShift d (2 * M) f1 0 0 = _; rw [siteShift_zero_zero, hf1]
      have hs2 : nextSite (nextSite f1 (0, true)) (0, true) 0 = dbl (x 0) + 1 + 1 := by
        show siteShift d (2 * M) (nextSite f1 (0, true)) 0 0 = _; rw [siteShift_zero_zero, hs1]
      rcases he with rfl | rfl | rfl | rfl
      · obtain ⟨h1, h2'⟩ := stepLink_zero_of_ne (fineSite x) hν0 b
        refine mem_posHalf_spatial (by rw [h2']; exact hν0) ?_
        rw [h1, hf0, hv, hK]; omega
      · refine mem_posHalf_temporal rfl ?_
        show (f1 0).val < _
        rw [hf1, hv, hK]; omega
      · refine mem_posHalf_temporal rfl ?_
        show (nextSite f1 (0, true) 0).val < _
        rw [hs1, val_dbl_add_one, hK]; omega
      · obtain ⟨h1, h2'⟩ := stepLink_zero_of_ne (nextSite (nextSite f1 (0, true)) (0, true)) hν0 (!b)
        refine mem_posHalf_spatial (by rw [h2']; exact hν0) ?_
        rw [h1, hs2, val_dbl_add_two _ h2, hK]; omega
    · have hx : (x 0).val ≤ M / 2 := by
        rcases hl with (⟨-, -, h⟩ | ⟨h, -⟩) | ⟨-, h | h⟩
        · exact h.le
        · exact absurd h hμ
        · omega
        · omega
      have hs1 : nextSite f1 (μ, true) 0 = dbl (x 0) := by
        show siteShift d (2 * M) f1 μ 0 = _; rw [siteShift_zero_of_ne _ hμ, hf1]
      have hs2 : nextSite (nextSite f1 (μ, true)) (μ, true) 0 = dbl (x 0) := by
        show siteShift d (2 * M) (nextSite f1 (μ, true)) μ 0 = _; rw [siteShift_zero_of_ne _ hμ, hs1]
      have hsp : ∀ e : LatticeLink d (2 * M), e.dir ≠ 0 → e.site 0 = dbl (x 0) → e ∈ posHalfLinks d (2 * M) :=
        fun e hd ht => mem_posHalf_spatial hd (by rw [ht, hv, hK]; omega)
      rcases he with rfl | rfl | rfl | rfl
      · obtain ⟨h1, h2'⟩ := stepLink_zero_of_ne (fineSite x) hν0 b
        exact hsp _ (by rw [h2']; exact hν0) (by rw [h1]; rfl)
      · exact hsp _ hμ hf1
      · exact hsp _ hμ hs1
      · obtain ⟨h1, h2'⟩ := stepLink_zero_of_ne (nextSite (nextSite f1 (μ, true)) (μ, true)) hν0 (!b)
        exact hsp _ (by rw [h2']; exact hν0) (by rw [h1, hs2])

/-- **A coarse observable of the closed coarse positive half lifts to one of the closed fine positive half.** -/
theorem linkDep_smearBlock (hM : Even M) (w : ℝ) {α : Type*} {F : GaugeConnection SU2 d M → α}
    (hF : LinkDep F (posHalfLinks d M)) :
    LinkDep (fun U => F (smearBlock w U)) (posHalfLinks d (2 * M)) := by
  intro U V hUV
  apply hF
  intro l hl
  rcases l with ⟨x, μ⟩
  show projSU2 (smearSum w U (fineSite x) μ) = projSU2 (smearSum w V (fineSite x) μ)
  congr 1
  unfold smearSum
  have hw : ∀ γ, (γ = straight μ ∨ ∃ ν b, ν ∈ transverse μ ∧ γ = staple μ ν b) →
      walk U (fineSite x) γ = walk V (fineSite x) γ :=
    fun γ hγ => walk_congr fun e he => hUV e (walkLinks_mem hM hl hγ e he)
  rw [hw _ (Or.inl rfl)]
  congr 2
  refine Finset.sum_congr rfl fun ν hν => Finset.sum_congr rfl fun b _ => ?_
  rw [hw _ (Or.inr ⟨ν, b, hν, rfl⟩)]

/-- **The smeared step as a reflection-respecting blocking.** -/
def smearRP (w : ℝ) (hM : Even M) : RPBlocking SU2 d (2 * M) M where
  B := smearBlock w
  meas := measurable_smearBlock w
  theta := smearBlock_thetaConn w
  half := fun _ hF => linkDep_smearBlock hM w hF

end Smear

/-! ## Composition and iteration -/

section Iterate

variable {G : Type*} [Group G] [MeasurableSpace G] {d : ℕ} [NeZero d]

/-- The identity blocking. -/
def _root_.ProofPhase.RPBlocking.idRP (N : ℕ) [NeZero N] : RPBlocking G d N N where
  B := id
  meas := measurable_id
  theta := fun _ => rfl
  half := fun _ hF => hF

/-- **Composition of reflection-respecting blockings** is reflection-respecting. -/
def _root_.ProofPhase.RPBlocking.comp {N K M : ℕ} [NeZero N] [NeZero K] [NeZero M] (P : RPBlocking G d N K)
    (Q : RPBlocking G d K M) : RPBlocking G d N M where
  B := Q.B ∘ P.B
  meas := Q.meas.comp P.meas
  theta := fun U => by simp only [Function.comp, P.theta, Q.theta]
  half := fun F hF => P.half _ (Q.half F hF)

/-- Transport of a blocking along an equality of fine sides. -/
def _root_.ProofPhase.RPBlocking.cast {N N' M : ℕ} [NeZero N] [NeZero N'] [NeZero M] (h : N = N')
    (P : RPBlocking G d N M) : RPBlocking G d N' M := by
  subst h; exact P

instance neZero_pow_mul (n M : ℕ) [NeZero M] : NeZero (2 ^ n * M) :=
  ⟨Nat.mul_ne_zero (pow_ne_zero _ two_ne_zero) (NeZero.ne M)⟩

end Iterate

section Family

variable {d : ℕ} [NeZero d]

theorem even_pow_mul {M : ℕ} (hM : Even M) (n : ℕ) : Even (2 ^ n * M) := hM.mul_left _

/-- **`n` smeared steps**, `(ℤ/2ⁿMℤ)^d → (ℤ/Mℤ)^d` (coarse side `M` even). -/
def smearIter (w : ℝ) {M : ℕ} [NeZero M] (hM : Even M) : (n : ℕ) → RPBlocking SU2 d (2 ^ n * M) M
  | 0 => RPBlocking.cast (by rw [pow_zero, one_mul]) (RPBlocking.idRP M)
  | n + 1 => RPBlocking.cast (by rw [pow_succ]; ring)
      ((smearRP (M := 2 ^ n * M) w (even_pow_mul hM n)).comp (smearIter w hM n))

end Family

/-- The coarse side `2(j+1)` is even. -/
theorem even_coarseSide (j : ℕ) : Even (coarseSide j) := ⟨j + 1, by unfold coarseSide; ring⟩

/-- **The good blocking family** for a tuning with dyadic resolution `ℓ_k = 2^{n_k}`: at level `k`, `n_k` smeared steps
from the fine torus of side `2(j+1)ℓ_k` to the coarse torus of side `2(j+1)` (one coarse link per physical length `L₁`). -/
def goodBlocking (T : Tuning) (w : ℝ) (n : ℕ → ℕ) (hn : ∀ k, T.ℓ k = 2 ^ n k) : BlockingFamily T := fun k j =>
  RPBlocking.cast (by rw [Tuning.side, hn k, coarseSide]; ring) (smearIter (d := 4) w (even_coarseSide j) (n k))

/-- **Every layer of the good blocking is reflection positive** (P1.6 for this blocking, at every level and volume):
for every bounded measurable coarse observable `F` of the closed coarse positive half,
`∫ F(B U) F(Θ B U) e^{−S_W(U)} dHaar(U) ≥ 0`. -/
theorem goodBlocking_rp (T : Tuning) (w : ℝ) (n : ℕ → ℕ) (hn : ∀ k, T.ℓ k = 2 ^ n k) (k j : ℕ)
    {F : GaugeConnection SU2 4 (coarseSide j) → ℝ} (hF : LinkDep F (posHalfLinks 4 (coarseSide j)))
    (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) :
    0 ≤ ∫ U, F ((goodBlocking T w n hn k j).B U) * F (thetaConn ((goodBlocking T w n hn k j).B U)) *
        ∏ p ∈ (univ : Finset (LatticePlaquette 4 (T.side k j))), Real.exp (T.β k * xp 2 p U)
          ∂(productHaar SU2 4 (T.side k j)) :=
  blocked_wilson_rp continuous_subtype_val (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
    (T.even_side k j) (goodBlocking T w n hn k j) (T.β k) hF mF bF

end ProofPhase.RouteA
