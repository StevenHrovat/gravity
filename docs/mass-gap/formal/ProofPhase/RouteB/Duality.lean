/-
Proof phase, workstream 2 (Route B): 't Hooft duality proper on the symmetric 4D box (P1.4′, 2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/ws2-routeB/NOTE.md`, section 3.
-/

import Positivity

/-!
# The lattice rotation exchanges the temporal and the spatial twist ('t Hooft duality on a symmetric box)

On the symmetric torus `(ℤ/Nℤ)⁴` (direction `0` is time) the twisted Wilson partition function
`twistZ β P = ∫ ∏_p e^{β s_p Re tr U_p} d(productHaar)`, `s_p = −1` on the plaquette set `P`, is defined for every set
`P` (a plaquette-dependent weight; `Positivity.PlaqWeight` is one function for all plaquettes).

* `permPlaq`, `xp_rotU`: a permutation `π` of the four coordinate axes acts on sites, links and plaquettes; pulling a
  connection back along it maps the holonomy of `p` to that of `π p` or its inverse, so `Re tr` is permuted.
* `twistZ_perm`: **`twistZ β P = twistZ β P'` whenever `π` maps `P` onto `P'`** (Haar is permutation invariant).
* `tHooft_rotation`: for `π = (0 2)(1 3)`, the **temporal twist** `P₀₁` (the `(0,1)`-plaquettes at `x₀ = x₁ = −1`, all
  `x₂, x₃`) and the **spatial (magnetic) twist** `P₂₃` (the `(2,3)`-plaquettes at `x₂ = x₃ = −1`, all `x₀, x₁`) have the
  same partition function.
* `electric_eq_magnetic`: hence the electric-flux ratio of the box, defined as the `Z₂` Fourier transform of the temporal
  twist, `(Z − Z₀₁)/(Z + Z₀₁)`, is the same function of the magnetic twist, `(Z − Z₂₃)/(Z + Z₂₃)`.

**Claim discipline.** `twistZ_perm` and `tHooft_rotation` are substantive but elementary (a symmetry of the lattice and of
Haar measure; true for every compact group and every `β`, including U(1), Z₂ and the finite subgroups); they need the
symmetric box (`T = L`), which is exactly the box of round 4's "inversion box". `electric_eq_magnetic` is `ring` once the
rotation is known. The identification of `(Z ∓ Z₀₁)/2` with the partition functions of the electric-flux sectors
`e₁ = 0, 1` of the transfer matrix (`Z₀₁ = tr(Ω̂₁ Tᴺ)`, `Ω̂₁` = the centre flip `ProofPhase.RouteB.flipA` of the
direction-1 links in one slice) is the standard transfer-matrix argument (`r3-monotone/NOTE.md`, B1), not formalised here.
With it, `tHooft_rotation` is 't Hooft's `F_e = dual(F_m)` on the symmetric box: P1.4′ of the blueprint.
-/

open MeasureTheory Finset Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.RouteB

variable {N : ℕ}

/-! ## Coordinate permutations -/

/-- The site with permuted coordinates: `(π · x)_{π i} = x_i`. -/
def permSite (π : Equiv.Perm (Fin 4)) (x : FinLatticeSites 4 N) : FinLatticeSites 4 N := fun i => x (π.symm i)

theorem permSite_symm (π : Equiv.Perm (Fin 4)) (x : FinLatticeSites 4 N) : permSite π.symm (permSite π x) = x := by
  funext i; simp [permSite]

theorem permSite_siteShift (π : Equiv.Perm (Fin 4)) (x : FinLatticeSites 4 N) (μ : Fin 4) :
    permSite π (siteShift 4 N x μ) = siteShift 4 N (permSite π x) (π μ) := by
  funext i
  simp only [permSite, siteShift, Function.update_apply]
  by_cases h : i = π μ
  · subst h; simp
  · have : π.symm i ≠ μ := fun h' => h (by rw [← h']; simp)
    simp [h, this]

/-- The permuted link. -/
def permLink (π : Equiv.Perm (Fin 4)) (l : LatticeLink 4 N) : LatticeLink 4 N := ⟨permSite π l.site, π l.dir⟩

/-- The link permutation as an equivalence. -/
def permLinkEquiv (π : Equiv.Perm (Fin 4)) : LatticeLink 4 N ≃ LatticeLink 4 N where
  toFun := permLink π
  invFun := permLink π.symm
  left_inv l := by rcases l with ⟨x, μ⟩; simp [permLink, permSite_symm]
  right_inv l := by
    rcases l with ⟨x, μ⟩
    have := permSite_symm (N := N) π.symm x
    simp only [Equiv.symm_symm] at this
    simp [permLink, this]

theorem lt_or_lt_perm (π : Equiv.Perm (Fin 4)) {a b : Fin 4} (h : a < b) : ¬π a < π b → π b < π a := fun h' =>
  lt_of_le_of_ne (not_lt.1 h') (π.injective.ne h.ne')

/-- The permuted plaquette (directions re-sorted). -/
def permPlaq (π : Equiv.Perm (Fin 4)) (p : LatticePlaquette 4 N) : LatticePlaquette 4 N :=
  if h : π p.dir1 < π p.dir2 then ⟨permSite π p.site, π p.dir1, π p.dir2, h⟩
  else ⟨permSite π p.site, π p.dir2, π p.dir1, lt_or_lt_perm π p.h_lt h⟩

theorem permPlaq_symm (π : Equiv.Perm (Fin 4)) (p : LatticePlaquette 4 N) : permPlaq π.symm (permPlaq π p) = p := by
  rcases p with ⟨x, a, b, hab⟩
  by_cases h : π a < π b
  · simp only [permPlaq, h, dite_true, Equiv.symm_apply_apply, hab, permSite_symm]
  · have h' : ¬ b < a := not_lt.2 hab.le
    simp only [permPlaq, h, dite_false, Equiv.symm_apply_apply, h', permSite_symm]

/-- The plaquette permutation as an equivalence. -/
def permPlaqEquiv (π : Equiv.Perm (Fin 4)) : LatticePlaquette 4 N ≃ LatticePlaquette 4 N where
  toFun := permPlaq π
  invFun := permPlaq π.symm
  left_inv p := permPlaq_symm π p
  right_inv p := by have := permPlaq_symm (N := N) π.symm p; simpa using this

variable {G : Type*} [Group G]

/-- The connection pulled back along the coordinate permutation. -/
def rotU (π : Equiv.Perm (Fin 4)) (U : GaugeConnection G 4 N) : GaugeConnection G 4 N := fun l => U (permLink π l)

variable {n : ℕ} [HasGaugeTrace G n]

theorem xp_rotU (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (π : Equiv.Perm (Fin 4)) (U : GaugeConnection G 4 N) (p : LatticePlaquette 4 N) :
    xp n p (rotU π U) = xp n (permPlaq π p) U := by
  rcases p with ⟨x, a, b, hab⟩
  unfold xp
  by_cases h : π a < π b
  · simp only [permPlaq, h, dite_true, plaquetteHolonomy, LatticePlaquette.boundaryLinks, rotU, permLink,
      permSite_siteShift]
  · simp only [permPlaq, h, dite_false]
    rw [← gaugeReTr_inv_of_unitary hU]
    congr 1
    simp only [plaquetteHolonomy, LatticePlaquette.boundaryLinks, rotU, permLink, permSite_siteShift]
    group

/-! ## Twisted partition functions -/

variable [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [HasHaarProbability G] [NeZero N]

/-- The sign of a plaquette for the twist set `P`. -/
def tsign (P : Finset (LatticePlaquette 4 N)) (p : LatticePlaquette 4 N) : ℝ := if p ∈ P then -1 else 1

/-- **The twisted Wilson partition function**: the plaquettes of `P` enter with `−β`. -/
def twistZ (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (P : Finset (LatticePlaquette 4 N)) : ℝ :=
  ∫ U, ∏ p, Real.exp (β * tsign P p * xp n p U) ∂(productHaar G 4 N)

/-- **Lattice symmetry of the twisted partition function**: a coordinate permutation that maps the twist set `P` onto
`P'` leaves the partition function unchanged. -/
theorem twistZ_perm (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (β : ℝ) (π : Equiv.Perm (Fin 4)) {P P' : Finset (LatticePlaquette 4 N)}
    (hP : ∀ p, permPlaq π p ∈ P' ↔ p ∈ P) : twistZ (G := G) n β P = twistZ (G := G) n β P' := by
  unfold twistZ
  have hmp : MeasurePreserving (rotU (G := G) (N := N) π) (productHaar G 4 N) (productHaar G 4 N) :=
    measurePreserving_reindex (haarG G) (permLinkEquiv π)
  have hpt : ∀ U : GaugeConnection G 4 N, ∏ p, Real.exp (β * tsign P p * xp n p (rotU π U)) = ∏ q, Real.exp (β * tsign P' q * xp n q U) := by
    intro U
    simp_rw [xp_rotU hU]
    have hs : ∀ p, tsign P p = tsign P' (permPlaq π p) := fun p => by simp only [tsign, hP p]
    simp_rw [hs]
    exact Equiv.prod_comp (permPlaqEquiv π) (fun q => Real.exp (β * tsign P' q * xp n q U))
  rw [← integral_comp_of_measurePreserving hmp (g := fun U : GaugeConnection G 4 N => ∏ q, Real.exp (β * tsign P q * xp n q U))]
  · exact integral_congr_ae (Filter.Eventually.of_forall fun U => hpt U)
  · exact (Finset.measurable_prod _ fun q _ =>
      Real.measurable_exp.comp (measurable_const.mul (AreaLaw.Concrete.measurable_xp hc q))).aestronglyMeasurable

/-! ## The temporal and the spatial twist -/

/-- The twist in the plane (μ, ν): the (μ, ν)-plaquettes at x_μ = x_ν = −1, all other coordinates free. -/
def twistPlane (μ ν : Fin 4) : Finset (LatticePlaquette 4 N) :=
  univ.filter fun p => p.dir1 = μ ∧ p.dir2 = ν ∧ p.site μ = -1 ∧ p.site ν = -1

/-- The lattice rotation (0 2)(1 3): time and the first spatial axis are exchanged with the other two axes. -/
def rot0213 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

theorem mem_twist_rot (p : LatticePlaquette 4 N) :
    permPlaq rot0213 p ∈ twistPlane 2 3 ↔ p ∈ twistPlane 0 1 := by
  rcases p with ⟨x, a, b, hab⟩
  have hs2 : rot0213.symm 2 = 0 := by decide
  have hs3 : rot0213.symm 3 = 1 := by decide
  have r0 : rot0213 0 = 2 := by decide
  have r1 : rot0213 1 = 3 := by decide
  simp only [twistPlane, mem_filter, mem_univ, true_and, permPlaq]
  split_ifs with h
  · simp only [permSite, hs2, hs3]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have ha : a = 0 := by have := congrArg rot0213.symm h1; simpa [hs2] using this
      have hb : b = 1 := by have := congrArg rot0213.symm h2; simpa [hs3] using this
      exact ⟨ha, hb, h3, h4⟩
    · rintro ⟨rfl, rfl, h3, h4⟩
      exact ⟨r0, r1, h3, h4⟩
  · constructor
    · rintro ⟨h1, h2, -, -⟩
      have hb : b = 0 := by have := congrArg rot0213.symm h1; simpa [hs2] using this
      have ha : a = 1 := by have := congrArg rot0213.symm h2; simpa [hs3] using this
      subst ha hb
      exact absurd hab (by decide)
    · rintro ⟨rfl, rfl, -, -⟩
      exact absurd (by rw [r0, r1]; decide) h

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

include hc hU in
/-- **'t Hooft duality on the symmetric box (P1.4′):** the temporal twist (plane (0,1), conjugate to electric flux
along axis 1) and the spatial twist (plane (2,3), magnetic flux along axis 1) have the same partition function. -/
theorem tHooft_rotation (β : ℝ) :
    twistZ (G := G) (N := N) n β (twistPlane 0 1) = twistZ (G := G) (N := N) n β (twistPlane 2 3) :=
  (twistZ_perm hc hU β rot0213 mem_twist_rot).symm.symm

include hc hU in
/-- **Electric = dual(magnetic)**: the electric-flux ratio Z_{e=1}/Z_{e=0} = (Z − Z₀₁)/(Z + Z₀₁) (the Z₂ Fourier
transform of the temporal twist) equals (Z − Z₂₃)/(Z + Z₂₃), the same function of the magnetic twist. -/
theorem electric_eq_magnetic (β : ℝ) :
    (twistZ (G := G) (N := N) n β ∅ - twistZ (G := G) (N := N) n β (twistPlane 0 1)) /
        (twistZ (G := G) (N := N) n β ∅ + twistZ (G := G) (N := N) n β (twistPlane 0 1)) =
      (twistZ (G := G) (N := N) n β ∅ - twistZ (G := G) (N := N) n β (twistPlane 2 3)) /
        (twistZ (G := G) (N := N) n β ∅ + twistZ (G := G) (N := N) n β (twistPlane 2 3)) := by
  rw [tHooft_rotation hc hU β]

end ProofPhase.RouteB
