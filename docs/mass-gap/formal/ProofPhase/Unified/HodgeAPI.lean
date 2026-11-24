/-
The form layer as one API: the Hodge instance, in the API's shape (2026-11-24).
Released under Apache 2.0.

Paper: `docs/unified/HODGE.md`, `docs/unified/API.md`. Mathlib-only core: `Unified/HodgeLinear.lean`.
-/

import ProofPhase.API
import ProofPhase.Unified.HodgeLinear

/-!
# Hodge through the API: input + structure + one named open step

The owner's reading: **describable implies exists**. On a smooth complex projective variety the rational `(p, p)` classes
are what cohomology can describe; the classes of algebraic cycles are what exists as geometry. The Hodge conjecture says
the first are among the second. Every content step sits in an `OpenStep` or `External` slot; nothing about the Hodge
conjecture is proved here.

* **The card** (`problem`): input = rational cohomology with its Hodge classes and its algebraic classes (`Input`); open
  step = `HodgeConjecture`; conclusion = Hodge classes and algebraic classes coincide (`hodge = alg`).
* **The positivity** (`PosInput`): the Hodge-Riemann relations (`External`; in the circle model of `HodgeLinear` they are
  `PolHS.hodge_pos`, linked by `hr_of_polHS`) make the polarisation positive definite on Hodge classes, hence on algebraic
  classes: Grothendieck's Hodge standard conjecture holds in characteristic 0 (`alg_pos`), numerical and homological
  equivalence agree on the algebraic classes (`num_eq_hom`), and the encoder bound holds (`alg_cs`).
* **The slot is not empty** (`DivisorInput.holds`): for divisors (`p = 1`) the open step is proved from Lefschetz (1,1)
  (the exponential sequence and the Hodge decomposition as `External` slots, the chase in Lean); hard Lefschetz carries
  it to curves (`CurveClassInput.holds`).
* **Describable must mean rational** (`integral_fails`): the integral version makes every torsion class algebraic, which
  Atiyah and Hirzebruch showed false.
* **The GRH column** (`weilCard`, `curveCard`): over a finite field the same positivity, the Hodge standard conjecture,
  would put the Frobenius eigenvalues on the circle `|μ|^2 = q^w`; for curves the open step is the Hodge index theorem
  on `C x C` (classical, `External`) and the conclusion is Weil's bound `|N - (q + 1)| ≤ 2 g sqrt q`.

Standard axioms only.
-/

noncomputable section

namespace ProofPhase.API.Hodge

open ProofPhase.Hodge

/-! ## 1. The card: describable implies exists -/

/-- **The well-defined input**: rational cohomology `V = H^{2p}(X, Q)` of a smooth complex projective variety `X` in a
degree `p`, its rational Hodge classes (the "describable" side: `H^{2p}(X, Q) ∩ H^{p,p}`), and the rational span of the
classes of algebraic cycles of codimension `p` (the "exists" side). The one fact taken from outside: the class of a
subvariety is a Hodge class. -/
structure Input where
  /-- `H^{2p}(X, Q)`. -/
  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℚ V]
  /-- The rational Hodge classes, of type `(p, p)`: the describable side. -/
  hodge : Submodule ℚ V
  /-- The rational span of the classes of algebraic cycles of codimension `p`: the side that exists. -/
  alg : Submodule ℚ V
  /-- The class of an algebraic cycle is a Hodge class. -/
  alg_le : External "the cycle class of a subvariety is a rational (p,p) class (classical)" (alg ≤ hodge)

attribute [instance] Input.acg Input.mod

/-- **The one open step: the Hodge conjecture** (Clay): every rational `(p, p)` class is a rational combination of
classes of algebraic cycles. Open for `p ≥ 2` in general. -/
def HodgeConjecture (i : Input) : Prop :=
  OpenStep "Hodge conjecture: every rational (p,p) class is a rational combination of classes of algebraic cycles"
    (i.hodge ≤ i.alg)

/-- **Hodge as a problem card.** Conclusion: the describable classes and the classes that exist coincide. -/
def problem : Problem where
  name := "Hodge: every rational (p,p) class is algebraic (describable implies exists)"
  Input := Input
  Open i := HodgeConjecture i
  Concl i := i.hodge = i.alg
  sources := ["the cycle class of a subvariety is a rational (p,p) class (classical)"]
  proved i h := le_antisymm h i.alg_le

/-! ## 2. The positivity: Hodge-Riemann on Hodge classes, hence on algebraic classes -/

/-- **The input with its polarisation**: a symmetric rational form `Q` on `V` (for a primitive piece: the cup product
with a power of an ample class, with the Lefschetz sign), and the **Hodge-Riemann bilinear relations** restricted to
rational Hodge classes, as an external theorem (Hodge theory). -/
structure PosInput where
  i : Input
  Q : LinearMap.BilinForm ℚ i.V
  symm : ∀ x y, Q x y = Q y x
  hr : External "Hodge-Riemann bilinear relations (Hodge theory): Q is positive definite on the rational Hodge classes"
    (∀ x ∈ i.hodge, x ≠ 0 → 0 < Q x x)

namespace PosInput

variable (P : PosInput)

/-- **Grothendieck's Hodge standard conjecture holds in characteristic 0**: the polarisation is positive definite on the
algebraic classes (they are Hodge classes, where Hodge-Riemann applies). -/
theorem alg_pos {x : P.i.V} (hx : x ∈ P.i.alg) (h0 : x ≠ 0) : 0 < P.Q x x := P.hr x (P.i.alg_le hx) h0

theorem alg_nonneg {x : P.i.V} (hx : x ∈ P.i.alg) : 0 ≤ P.Q x x := by
  by_cases h0 : x = 0
  · simp [h0]
  · exact (P.alg_pos hx h0).le

/-- **Numerical equivalence is homological equivalence on the algebraic classes**: an algebraic class orthogonal to every
algebraic class is zero (Grothendieck's conjecture D, in this piece, in characteristic 0). -/
theorem num_eq_hom {x : P.i.V} (hx : x ∈ P.i.alg) (h : ∀ y ∈ P.i.alg, P.Q x y = 0) : x = 0 := by
  by_contra h0
  exact (P.alg_pos hx h0).ne' (h x hx)

/-- **The encoder bound on algebraic classes** (Cauchy-Schwarz): `Q(x, y)^2 ≤ Q(x, x) Q(y, y)`. -/
theorem alg_cs {x y : P.i.V} (hx : x ∈ P.i.alg) (hy : y ∈ P.i.alg) : P.Q x y ^ 2 ≤ P.Q x x * P.Q y y :=
  cs_of_nonneg P.Q P.symm P.i.alg (fun _ hz => P.alg_nonneg hz) hx hy

end PosInput

/-- **Where the external Hodge-Riemann input comes from**: a real polarised Hodge structure (`PolHS`, the circle model)
whose rational points carry `Q` and whose Hodge classes contain the rational Hodge classes gives exactly the `hr` slot;
`PolHS.hodge_pos` is the proved positivity behind it. -/
theorem hr_of_polHS (i : Input) (Q : LinearMap.BilinForm ℚ i.V) {VR : Type} [AddCommGroup VR] [Module ℝ VR]
    (P : PolHS VR) (ι : i.V →+ VR) (hι : Function.Injective ι) (hQ : ∀ x y, (Q x y : ℝ) = P.Q (ι x) (ι y))
    (hH : ∀ x ∈ i.hodge, ι x ∈ P.hodge) : ∀ x ∈ i.hodge, x ≠ 0 → 0 < Q x x := by
  intro x hx h0
  have h1 : ι x ≠ 0 := fun h => h0 (hι (h.trans (map_zero ι).symm))
  have h2 := P.hodge_pos (hH x hx) h1
  rw [← hQ] at h2
  exact_mod_cast h2

/-! ## 3. The slot is not empty: divisors (Lefschetz (1,1)) and curves (hard Lefschetz) -/

/-- **The input for divisors** (`p = 1`): line bundles (on a projective `X`, divisor classes), `H^2(X, Z)`,
`H^2(X, O_X) = H^{0,2}`, `H^2(X, Q)`, the first Chern class, the map to `H^{0,2}`, the map to rational cohomology, and
the rational `(1,1)` classes. Three classical facts enter as `External` slots. -/
structure DivisorInput where
  Pic : Type
  H2Z : Type
  H02 : Type
  H2Q : Type
  [i₁ : AddCommGroup Pic]
  [i₂ : AddCommGroup H2Z]
  [i₃ : AddCommGroup H02]
  [i₄ : AddCommGroup H2Q]
  [i₅ : Module ℚ H2Q]
  c₁ : Pic →+ H2Z
  π : H2Z →+ H02
  ι : H2Z →+ H2Q
  /-- The rational `(1,1)` classes. -/
  hodge : Submodule ℚ H2Q
  /-- Exactness at `H^2(X, Z)` of the exponential sequence `0 → Z → O → O* → 0`. -/
  exact : External "exponential sequence: the kernel of H^2(X,Z) -> H^2(X,O) is the image of c1 (classical)"
    (∀ x, π x = 0 → x ∈ c₁.range)
  /-- A rational `(1,1)` class has an integral multiple with no `(0,2)` part (Hodge symmetry for real classes). -/
  hodge_int : External "Hodge decomposition: a rational (1,1) class has an integral multiple with zero (0,2) part"
    (∀ y ∈ hodge, ∃ n : ℕ, 0 < n ∧ ∃ x, ι x = n • y ∧ π x = 0)
  /-- The class of a divisor is a `(1,1)` class (and on projective `X` every line bundle is `O(D)`, Kodaira-Serre). -/
  div_hodge : External "c1 of a line bundle is a (1,1) class; on projective X every line bundle is O(D) (classical)"
    (Submodule.span ℚ (Set.range (ι.comp c₁)) ≤ hodge)

attribute [instance] DivisorInput.i₁ DivisorInput.i₂ DivisorInput.i₃ DivisorInput.i₄ DivisorInput.i₅

namespace DivisorInput

variable (D : DivisorInput)

/-- The divisor input as an input of the Hodge card: algebraic classes = the rational span of divisor classes. -/
def toInput : Input where
  V := D.H2Q
  hodge := D.hodge
  alg := Submodule.span ℚ (Set.range (D.ι.comp D.c₁))
  alg_le := D.div_hodge

/-- **The Hodge conjecture for divisors** (Lefschetz (1,1)): the open step of the card holds for `p = 1`. -/
theorem holds : problem.Open D.toInput := by
  intro y hy
  obtain ⟨n, hn, x, hxy, hπ⟩ := D.hodge_int y hy
  obtain ⟨L, rfl⟩ := lefschetz11 D.c₁ D.π D.exact hπ
  have h := rational_descent (D.ι.comp D.c₁) Set.univ hn (Set.mem_univ L) hxy
  rwa [Set.image_univ] at h

/-- **The card for divisors**: describable `(1,1)` classes and divisor classes coincide. -/
theorem card : D.hodge = Submodule.span ℚ (Set.range (D.ι.comp D.c₁)) := problem.holds D.toInput D.holds

end DivisorInput

/-- **The input for curves** (`p = n - 1`): the divisor input, `H^{2n-2}(X, Q)` with its Hodge classes and curve classes,
and hard Lefschetz `L^{n-2} : H^2(X, Q) ≅ H^{2n-2}(X, Q)` (cup with `n - 2` hyperplane classes). -/
structure CurveClassInput where
  D : DivisorInput
  H : Type
  [acg : AddCommGroup H]
  [mod : Module ℚ H]
  hodge : Submodule ℚ H
  alg : Submodule ℚ H
  alg_le : External "the class of a curve is a rational (n-1,n-1) class (classical)" (alg ≤ hodge)
  /-- Hard Lefschetz (classical, Hodge theory). -/
  L : D.H2Q ≃ₗ[ℚ] H
  hl_hodge : External "hard Lefschetz is an isomorphism of Hodge structures: its inverse keeps Hodge classes"
    (∀ y ∈ hodge, L.symm y ∈ D.hodge)
  hl_alg : External "a divisor cut with n-2 hyperplanes is a curve (classical)"
    (D.toInput.alg.map L.toLinearMap ≤ alg)

attribute [instance] CurveClassInput.acg CurveClassInput.mod

/-- The curve input as an input of the Hodge card. -/
def CurveClassInput.toInput (C : CurveClassInput) : Input where
  V := C.H
  hodge := C.hodge
  alg := C.alg
  alg_le := C.alg_le

/-- **The Hodge conjecture for curves** (degree `2n - 2`), from divisors by hard Lefschetz. -/
theorem CurveClassInput.holds (C : CurveClassInput) : problem.Open C.toInput :=
  transfer C.L C.hl_hodge C.hl_alg C.D.holds

/-! ## 4. Describable must mean rational: the integral version fails -/

/-- **The integral input**: `A = H^{2p}(X, Z)`, its image in rational cohomology, the rational Hodge classes, and the
classes of integral algebraic cycles. -/
structure IntegralInput where
  A : Type
  QV : Type
  [i₁ : AddCommGroup A]
  [i₂ : AddCommGroup QV]
  [i₃ : Module ℚ QV]
  ι : A →+ QV
  hodge : Submodule ℚ QV
  alg : Set A

attribute [instance] IntegralInput.i₁ IntegralInput.i₂ IntegralInput.i₃

/-- **The integral Hodge statement**: every integral class whose rational image is a Hodge class is the class of an
integral algebraic cycle. -/
def IntegralHodge (i : IntegralInput) : Prop := ∀ x, i.ι x ∈ i.hodge → x ∈ i.alg

/-- **The integral version fails** once there is a torsion class that is not algebraic (Atiyah-Hirzebruch 1962; Kollar
1992 gives non-torsion failures too). So "describable" must mean rational. -/
theorem integral_fails (i : IntegralInput)
    (ah : External "Atiyah-Hirzebruch 1962: a torsion class in H^4(X,Z) that is not algebraic"
      (∃ x : i.A, ∃ n : ℕ, 0 < n ∧ n • x = 0 ∧ x ∉ i.alg)) : ¬ IntegralHodge i := by
  intro hInt
  obtain ⟨x, n, hn, ht, hx⟩ := ah
  exact hx (integral_needs_torsion i.ι i.hodge i.alg hInt hn ht)

/-! ## 5. The GRH column: the same positivity over a finite field -/

/-- **The Weil input**: Frobenius `F` acting on weight-`w` cohomology (a complex vector space after a choice of
embedding), over `F_q`. -/
structure WeilInput where
  E : Type
  [acg : AddCommGroup E]
  [mod : Module ℂ E]
  F : Module.End ℂ E
  q : ℕ
  w : ℕ

attribute [instance] WeilInput.acg WeilInput.mod

/-- **The open step: the Hodge standard conjecture over `F_q`**, in the form the Riemann hypothesis needs: a
positive-definite Hermitian form on which Frobenius is a similitude of ratio `q^w`. Open in general (Grothendieck 1969);
for surfaces it is the Hodge index theorem (`curveCard`). -/
def StandardHodge (i : WeilInput) : Prop :=
  OpenStep "Hodge standard conjecture over F_q: a positive form on which Frobenius is a similitude of ratio q^w"
    (∃ S : i.E →ₗ⋆[ℂ] i.E →ₗ[ℂ] ℂ, (∀ x, x ≠ 0 → 0 < (S x x).re) ∧
      ∀ x y, S (i.F x) (i.F y) = (((i.q : ℝ) ^ i.w : ℝ) : ℂ) * S x y)

/-- **The positivity route to the Weil conjectures as a card**: the open step puts every Frobenius eigenvalue on the
circle `|μ|^2 = q^w`. Deligne proved the conclusion for `l`-adic cohomology in 1974 by another route; the positivity
route stays open. -/
def weilCard : Problem where
  name := "Weil conjectures, Riemann hypothesis part: positivity puts the Frobenius eigenvalues on |mu|^2 = q^w"
  Input := WeilInput
  Open := StandardHodge
  Concl i := ∀ μ : ℂ, i.F.HasEigenvalue μ → ‖μ‖ ^ 2 = (i.q : ℝ) ^ i.w
  sources := ["Deligne 1974 (Weil I): the conclusion for l-adic cohomology, proved without the open step"]
  proved i h := by
    obtain ⟨S, hpos, hF⟩ := h
    exact fun μ hμ => eigen_on_circle_form S hpos i.F hF hμ

/-- **The curve input**: the intersection form on `NS(C x C) ⊗ R` for a curve `C` of genus `g` over `F_q` with `N`
rational points, the fibre classes, the graph of Frobenius and the diagonal, with their intersection numbers (classical
intersection theory, one `External` slot). -/
structure CurveInput where
  W : Type
  [acg : AddCommGroup W]
  [mod : Module ℝ W]
  [fd : FiniteDimensional ℝ W]
  B : LinearMap.BilinForm ℝ W
  f₁ : W
  f₂ : W
  Γ : W
  Δ : W
  g : ℝ
  q : ℝ
  N : ℝ
  hg : 0 ≤ g
  hq : 0 < q
  geometry : External "intersection numbers on C x C (classical): f1^2 = f2^2 = 0, f1 f2 = 1, Gamma f1 = 1,
    Gamma f2 = q, Delta f1 = Delta f2 = 1, Gamma^2 = q(2-2g), Delta^2 = 2-2g, Gamma Delta = N"
    ((∀ x y, B x y = B y x) ∧ B f₁ f₁ = 0 ∧ B f₂ f₂ = 0 ∧ B f₁ f₂ = 1 ∧ B Γ f₁ = 1 ∧ B Γ f₂ = q ∧ B Δ f₁ = 1 ∧
      B Δ f₂ = 1 ∧ B Γ Γ = q * (2 - 2 * g) ∧ B Δ Δ = 2 - 2 * g ∧ B Γ Δ = N)

attribute [instance] CurveInput.acg CurveInput.mod CurveInput.fd

/-- **Curves over `F_q` as a card**: the open step (the Hodge standard conjecture for the surface `C x C`, i.e. the Hodge
index property at the ample class `f₁ + f₂`) gives Weil's bound. The slot is filled by the Hodge index theorem
(`curve_open`). -/
def curveCard : Problem where
  name := "Curves over F_q: the Hodge index property on C x C gives Weil's bound |N - (q + 1)| <= 2 g sqrt q"
  Input := CurveInput
  Open i := OpenStep "Hodge standard conjecture for the surface C x C: Hodge index at f1 + f2" (HodgeIndex i.B (i.f₁ + i.f₂))
  Concl i := |i.N - (i.q + 1)| ≤ 2 * i.g * Real.sqrt i.q
  sources := ["intersection numbers on C x C (classical)"]
  proved i h := by
    obtain ⟨hB, h11, h22, h12, hΓ1, hΓ2, hΔ1, hΔ2, hΓΓ, hΔΔ, hΓΔ⟩ := i.geometry
    exact weil_bound_abs i.B hB i.hg i.hq h11 h22 h12 h hΓ1 hΓ2 hΔ1 hΔ2 hΓΓ hΔΔ hΓΔ

/-- **The curve slot is filled by the Hodge index theorem** in its signature form (`NS(C x C) ⊗ R` has one positive
direction; Hodge 1937, Grothendieck 1958 in every characteristic): the open step of `curveCard` holds, and with it
Weil's bound. -/
theorem curve_open (i : CurveInput)
    (hit : External "Hodge index theorem on a surface: the intersection form has one positive direction"
      (sigPos (LinearMap.BilinMap.toQuadraticMap i.B) ≤ 1)) :
    curveCard.Open i ∧ curveCard.Concl i := by
  obtain ⟨hB, h11, h22, h12, -⟩ := i.geometry
  have hH : 0 < i.B (i.f₁ + i.f₂) (i.f₁ + i.f₂) := by
    have h21 : i.B i.f₂ i.f₁ = 1 := by rw [hB]; exact h12
    simp only [map_add, LinearMap.add_apply, h11, h22, h12, h21]
    norm_num
  have h := hodgeIndex_of_sigPos i.B hB hH hit
  exact ⟨h, curveCard.holds i h⟩

end ProofPhase.API.Hodge
