/-
Wilson loops (area-law project, 2026-11-21; written first as a draft for `lgt`). Released under Apache 2.0.

# Wilson loops

Lattice paths as lists of oriented link steps, their holonomy, gauge covariance of open paths (the transformation acts only at the two
ends, by telescoping), gauge invariance of Wilson loops (closed paths, traced), the plaquette as the smallest Wilson loop, and the
rectangular R × T loops in any plane, the observables of the area law.

## Main results

- `pathHol_gauge_covariant`: a chain from x to y transforms as g(x) · hol · g(y)⁻¹.
- `wilsonLoop_gauge`: the traced holonomy of a closed chain is gauge-invariant.
- `plaquettePath_hol`, `plaquettePath_isLoop`: the boundary path of a plaquette is a closed chain with holonomy `plaquetteHolonomy`.
- `rectPath_isLoop`: the R × T rectangle in the plane (μ, ν), μ ≠ ν, is a closed chain.
-/

import AreaLaw.Lattice

noncomputable section

variable {d N : ℕ}

/-! ## Paths -/

/-- One step of a lattice path: a link, traversed forward (`fwd = true`, from its site to its target) or backward. -/
structure PathStep (d N : ℕ) where
  link : LatticeLink d N
  fwd : Bool
  deriving DecidableEq

/-- Where a step starts. -/
def PathStep.src (s : PathStep d N) : FinLatticeSites d N := if s.fwd then s.link.site else s.link.target

/-- Where a step ends. -/
def PathStep.tgt (s : PathStep d N) : FinLatticeSites d N := if s.fwd then s.link.target else s.link.site

/-- `PathChain x p y`: the steps of `p` follow each other from `x` to `y`. -/
def PathChain : FinLatticeSites d N → List (PathStep d N) → FinLatticeSites d N → Prop
  | x, [], y => x = y
  | x, s :: rest, y => s.src = x ∧ PathChain s.tgt rest y

/-- A closed path (a loop) based at `x`. -/
def IsLoop (x : FinLatticeSites d N) (p : List (PathStep d N)) : Prop := PathChain x p x

/-! ## Holonomy -/

variable {G : Type*} [Group G]

/-- The group element a step contributes: `U(l)` forward, `U(l)⁻¹` backward. -/
def PathStep.hol (U : GaugeConnection G d N) (s : PathStep d N) : G := if s.fwd then U s.link else (U s.link)⁻¹

/-- The holonomy (parallel transport) along a path: the ordered product of its steps. -/
def pathHol (U : GaugeConnection G d N) : List (PathStep d N) → G
  | [] => 1
  | s :: rest => s.hol U * pathHol U rest

theorem pathHol_append (U : GaugeConnection G d N) (p q : List (PathStep d N)) :
    pathHol U (p ++ q) = pathHol U p * pathHol U q := by
  induction p with
  | nil => simp [pathHol]
  | cons s rest ih => simp [pathHol, ih, mul_assoc]

/-- A gauge transformation acts on one step at its two ends. -/
theorem PathStep.hol_gauge (g : GaugeTransform G d N) (U : GaugeConnection G d N) (s : PathStep d N) :
    s.hol (gaugeTransformConnection g U) = g s.src * s.hol U * (g s.tgt)⁻¹ := by
  cases h : s.fwd <;> simp [PathStep.hol, PathStep.src, PathStep.tgt, gaugeTransformConnection, h, mul_assoc]

/-- **Gauge covariance of paths.** Along a chain from `x` to `y` the transformation telescopes: only its values at the two ends
    remain. -/
theorem pathHol_gauge_covariant (g : GaugeTransform G d N) (U : GaugeConnection G d N) :
    ∀ (p : List (PathStep d N)) (x y : FinLatticeSites d N), PathChain x p y →
      pathHol (gaugeTransformConnection g U) p = g x * pathHol U p * (g y)⁻¹
  | [], x, y, h => by simp only [PathChain] at h; subst h; simp [pathHol]
  | s :: rest, x, y, h => by
    obtain ⟨hs, hr⟩ := h
    rw [pathHol, PathStep.hol_gauge, pathHol_gauge_covariant g U rest s.tgt y hr, hs, pathHol]
    group

/-! ## Wilson loops -/

variable {n : ℕ} [HasGaugeTrace G n]

/-- The Wilson loop observable of a path: Re Tr of its holonomy (meaningful for closed paths). -/
def wilsonLoop (n : ℕ) [HasGaugeTrace G n] (p : List (PathStep d N)) (U : GaugeConnection G d N) : ℝ :=
  gaugeReTr G n (pathHol U p)

/-- Re Tr is invariant under conjugation (algebraic: no topology or measure needed). -/
theorem gaugeReTr_conj (g h : G) : gaugeReTr G n (g * h * g⁻¹) = gaugeReTr G n h := by
  simp only [gaugeReTr, gaugeTrace, map_mul]
  rw [Matrix.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]

/-- **Wilson loops are gauge-invariant.** -/
theorem wilsonLoop_gauge (x : FinLatticeSites d N) (p : List (PathStep d N)) (hp : IsLoop x p)
    (g : GaugeTransform G d N) (U : GaugeConnection G d N) :
    wilsonLoop n p (gaugeTransformConnection g U) = wilsonLoop n p U := by
  simp only [wilsonLoop]
  rw [pathHol_gauge_covariant g U p x x hp, gaugeReTr_conj]

/-! ## The plaquette is the smallest Wilson loop -/

/-- The counterclockwise boundary path of a plaquette. -/
def plaquettePath (p : LatticePlaquette d N) : List (PathStep d N) :=
  [⟨p.boundaryLinks 0, true⟩, ⟨p.boundaryLinks 1, true⟩, ⟨p.boundaryLinks 2, false⟩, ⟨p.boundaryLinks 3, false⟩]

theorem plaquettePath_hol (U : GaugeConnection G d N) (p : LatticePlaquette d N) :
    pathHol U (plaquettePath p) = plaquetteHolonomy U p := by
  simp [plaquettePath, pathHol, PathStep.hol, plaquetteHolonomy, mul_assoc]

theorem plaquettePath_isLoop (p : LatticePlaquette d N) : IsLoop p.site (plaquettePath p) := by
  have hc := siteShift_comm d N p.site p.dir1 p.dir2 (ne_of_lt p.h_lt)
  simp [IsLoop, PathChain, plaquettePath, PathStep.src, PathStep.tgt, LatticePlaquette.boundaryLinks, LatticeLink.target, hc]

/-! ## Rectangular loops -/

/-- The site `k` steps from `x` in direction `μ`. -/
def siteShiftN (x : FinLatticeSites d N) (μ : Fin d) (k : ℕ) : FinLatticeSites d N := Function.update x μ (x μ + k)

theorem siteShiftN_zero (x : FinLatticeSites d N) (μ : Fin d) : siteShiftN x μ 0 = x := by
  simp [siteShiftN]

theorem siteShiftN_succ (x : FinLatticeSites d N) (μ : Fin d) (k : ℕ) :
    siteShiftN x μ (k + 1) = siteShift d N (siteShiftN x μ k) μ := by
  ext i
  by_cases h : i = μ
  · subst h; simp [siteShiftN, siteShift, add_assoc]
  · simp [siteShiftN, siteShift, Function.update_of_ne h]

theorem siteShiftN_comm (x : FinLatticeSites d N) {μ ν : Fin d} (h : μ ≠ ν) (a b : ℕ) :
    siteShiftN (siteShiftN x μ a) ν b = siteShiftN (siteShiftN x ν b) μ a := by
  ext i
  by_cases hμ : i = μ
  · subst hμ; simp [siteShiftN, Function.update_of_ne h]
  · by_cases hν : i = ν
    · subst hν; simp [siteShiftN, Function.update_of_ne (Ne.symm h)]
    · simp [siteShiftN, Function.update_of_ne hμ, Function.update_of_ne hν]

/-- `k` forward steps in direction `μ` from `x`. -/
def straightFwd (x : FinLatticeSites d N) (μ : Fin d) : ℕ → List (PathStep d N)
  | 0 => []
  | k + 1 => ⟨⟨x, μ⟩, true⟩ :: straightFwd (siteShift d N x μ) μ k

/-- `k` backward steps in direction `μ` ending at `x` (the reverse of `straightFwd x μ k`). -/
def straightBwd (x : FinLatticeSites d N) (μ : Fin d) : ℕ → List (PathStep d N)
  | 0 => []
  | k + 1 => straightBwd (siteShift d N x μ) μ k ++ [⟨⟨x, μ⟩, false⟩]

theorem siteShiftN_succ' (x : FinLatticeSites d N) (μ : Fin d) (k : ℕ) :
    siteShiftN x μ (k + 1) = siteShiftN (siteShift d N x μ) μ k := by
  ext i
  by_cases h : i = μ
  · subst h; simp [siteShiftN, siteShift]; ring
  · simp [siteShiftN, siteShift, Function.update_of_ne h]

theorem pathChain_append {x y z : FinLatticeSites d N} {p q : List (PathStep d N)} (hp : PathChain x p y) (hq : PathChain y q z) :
    PathChain x (p ++ q) z := by
  induction p generalizing x with
  | nil => simp only [PathChain] at hp; subst hp; simpa using hq
  | cons s rest ih => exact ⟨hp.1, ih hp.2⟩

theorem straightFwd_pathChain (x : FinLatticeSites d N) (μ : Fin d) (k : ℕ) :
    PathChain x (straightFwd x μ k) (siteShiftN x μ k) := by
  induction k generalizing x with
  | zero => simp [straightFwd, PathChain, siteShiftN_zero]
  | succ k ih =>
    refine ⟨by simp [PathStep.src], ?_⟩
    simpa [PathStep.tgt, LatticeLink.target, siteShiftN_succ'] using ih (siteShift d N x μ)

theorem straightBwd_pathChain (x : FinLatticeSites d N) (μ : Fin d) (k : ℕ) :
    PathChain (siteShiftN x μ k) (straightBwd x μ k) x := by
  induction k generalizing x with
  | zero => simp [straightBwd, PathChain, siteShiftN_zero]
  | succ k ih =>
    rw [straightBwd, siteShiftN_succ']
    exact pathChain_append (ih (siteShift d N x μ)) ⟨by simp [PathStep.src, LatticeLink.target], by simp [PathChain, PathStep.tgt]⟩

/-- The R × T rectangle based at `x` in the plane (μ, ν): R steps along μ, T along ν, then back. -/
def rectPath (x : FinLatticeSites d N) (μ ν : Fin d) (R T : ℕ) : List (PathStep d N) :=
  straightFwd x μ R ++ straightFwd (siteShiftN x μ R) ν T ++ straightBwd (siteShiftN x ν T) μ R ++ straightBwd x ν T

/-- The rectangle is a closed chain. -/
theorem rectPath_isLoop (x : FinLatticeSites d N) {μ ν : Fin d} (h : μ ≠ ν) (R T : ℕ) : IsLoop x (rectPath x μ ν R T) := by
  have h1 := straightFwd_pathChain x μ R
  have h2 := straightFwd_pathChain (siteShiftN x μ R) ν T
  have h3 := straightBwd_pathChain (siteShiftN x ν T) μ R
  have h4 := straightBwd_pathChain x ν T
  rw [siteShiftN_comm x (Ne.symm h) T R] at h3
  exact pathChain_append (pathChain_append (pathChain_append h1 h2) h3) h4

/-- The rectangular Wilson loop is gauge-invariant. -/
theorem rectWilsonLoop_gauge (x : FinLatticeSites d N) {μ ν : Fin d} (h : μ ≠ ν) (R T : ℕ)
    (g : GaugeTransform G d N) (U : GaugeConnection G d N) :
    wilsonLoop n (rectPath x μ ν R T) (gaugeTransformConnection g U) = wilsonLoop n (rectPath x μ ν R T) U :=
  wilsonLoop_gauge x _ (rectPath_isLoop x h R T) g U

end
