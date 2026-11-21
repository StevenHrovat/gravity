/-
The lattice layer of the area-law project (2026-11-21). Released under Apache 2.0.

Definitions follow `mrdouglasny/lgt` (Copyright (c) 2026 Michael R. Douglas, Apache 2.0: `LGT/Lattice/CellComplex.lean`,
`LGT/GaugeField/Connection.lean`, `LGT/GaugeField/GaugeGroup.lean`, `LGT/MassGap/YMMeasure.lean`), restated here so that this project can
build on `scottnarmstrong/balaban-lean` (a newer Lean) without `lgt`'s dependencies. Same names, same conventions.
-/

import Mathlib

open MeasureTheory

noncomputable section

/-- Sites of the periodic lattice (ℤ/Nℤ)^d. -/
abbrev FinLatticeSites (d N : ℕ) := Fin d → ZMod N

variable (d N : ℕ)

/-- A link (oriented 1-cell): site + direction. -/
structure LatticeLink (d N : ℕ) where
  site : FinLatticeSites d N
  dir : Fin d
  deriving DecidableEq

/-- Shift a site by +1 in direction μ. -/
def siteShift (x : FinLatticeSites d N) (μ : Fin d) : FinLatticeSites d N :=
  Function.update x μ (x μ + 1)

theorem siteShift_comm (x : FinLatticeSites d N) (μ ν : Fin d) (h : μ ≠ ν) :
    siteShift d N (siteShift d N x μ) ν = siteShift d N (siteShift d N x ν) μ := by
  ext i
  simp only [siteShift, Function.update]
  split_ifs with h1 h2 h3 h4 <;> subst_eqs <;> simp_all

/-- Target of a link. -/
def LatticeLink.target {d N : ℕ} (l : LatticeLink d N) : FinLatticeSites d N := siteShift d N l.site l.dir

/-- A plaquette (oriented 2-cell): site + two ordered directions. -/
structure LatticePlaquette (d N : ℕ) where
  site : FinLatticeSites d N
  dir1 : Fin d
  dir2 : Fin d
  h_lt : dir1 < dir2
  deriving DecidableEq

/-- The four boundary links of a plaquette (counterclockwise; 2 and 3 traversed backward). -/
def LatticePlaquette.boundaryLinks {d N : ℕ} (p : LatticePlaquette d N) : Fin 4 → LatticeLink d N
  | 0 => ⟨p.site, p.dir1⟩
  | 1 => ⟨siteShift d N p.site p.dir1, p.dir2⟩
  | 2 => ⟨siteShift d N p.site p.dir2, p.dir1⟩
  | 3 => ⟨p.site, p.dir2⟩

/-- A gauge connection: a group element on every link. -/
abbrev GaugeConnection (G : Type*) (d N : ℕ) := LatticeLink d N → G

/-- A gauge transformation: a group element on every site. -/
abbrev GaugeTransform (G : Type*) (d N : ℕ) := FinLatticeSites d N → G

variable {G : Type*} [Group G] {d N}

/-- Holonomy around a plaquette: U(l₀) U(l₁) U(l₂)⁻¹ U(l₃)⁻¹. -/
def plaquetteHolonomy (U : GaugeConnection G d N) (p : LatticePlaquette d N) : G :=
  let l := p.boundaryLinks
  U (l 0) * U (l 1) * (U (l 2))⁻¹ * (U (l 3))⁻¹

/-- U'(link) = g(source) · U(link) · g(target)⁻¹. -/
def gaugeTransformConnection (g : GaugeTransform G d N) (U : GaugeConnection G d N) : GaugeConnection G d N :=
  fun l => g l.site * U l * (g l.target)⁻¹

/-- A matrix representation of the gauge group. -/
class HasGaugeTrace (G : Type*) (n : ℕ) [Group G] where
  rep : G →* Matrix (Fin n) (Fin n) ℂ

/-- Complex trace in the gauge representation. -/
def gaugeTrace (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n] (g : G) : ℂ :=
  Matrix.trace (HasGaugeTrace.rep (G := G) (n := n) g)

/-- Real part of the trace. -/
def gaugeReTr (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n] (g : G) : ℝ := (gaugeTrace G n g).re

/-- A probability measure on the gauge group, standing for its Haar measure (invariance properties are stated where they are used). -/
class HasHaarProbability (G : Type*) [MeasurableSpace G] where
  haar : Measure G
  isProb : IsProbabilityMeasure haar

attribute [instance] HasHaarProbability.isProb

/-- The single-link measure. -/
def haarG (G : Type*) [MeasurableSpace G] [HasHaarProbability G] : Measure G := HasHaarProbability.haar (G := G)

instance (G : Type*) [MeasurableSpace G] [HasHaarProbability G] : IsProbabilityMeasure (haarG G) := HasHaarProbability.isProb

/-- The product measure on connections. -/
def productHaar (G : Type*) [MeasurableSpace G] [HasHaarProbability G] (d N : ℕ) [Fintype (LatticeLink d N)] :
    Measure (GaugeConnection G d N) :=
  Measure.pi (fun _ : LatticeLink d N => haarG G)

end
