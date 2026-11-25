# Hodge: the last Millennium problem in the DMP API

Status: 2026-11-24. Puts the Hodge conjecture into the project as an instance of the DMP API (`API.md`), so that all seven
Millennium problems are covered by the framework. Answers the owner's request to add Hodge, which until now was mention-only:
`BLOWUP.md` section 10 ("Links found, not pursued") and the `PREP.md` entries "Describable => exists => positive", the
Frobenius / `C x C` reading of the GRH hand-over, and the scope decision that recorded the Hodge link (describable implies
exists; Hodge-Riemann positivity and Grothendieck's standard conjectures as the missing arithmetic Hodge index of GRH).

Files:
- Lean: `ProofPhase/Unified/HodgeLinear.lean` (22 declarations, namespace `ProofPhase.Hodge`): imports **Mathlib only**.
  The linear-algebra core that Mathlib can reach: Hodge-Riemann positivity on a polarised Hodge structure, the Hodge index
  theorem as linear algebra, Weil's bound for curves from it, positivity putting eigenvalues on a circle, and the
  Lefschetz (1,1) diagram chases.
- Lean: `ProofPhase/Unified/HodgeAPI.lean` (25 declarations, namespace `ProofPhase.API.Hodge`): the instance of the DMP
  API, with the Hodge card, the positivity, the divisor and curve cases, the integral failure, and the two cards of the GRH
  column.
- `hodge-axioms.sh`, `hodge-axioms.log`: both modules build with no warnings; all 47 declarations depend on the three
  standard axioms only (`propext`, `Classical.choice`, `Quot.sound`; two on fewer); no `sorry`.

Status marks as in `NAVIER-STOKES.md`: **[Lean]** (proved here, standard axioms), **[classical]** (standard mathematics,
recalled, not re-proved), **[external]** (a published or posted result, recorded, not checked here), **[reading]** (an
identification with DMP vocabulary, not a theorem), **[open]** (not proved by anyone), **[fails]** (false in this form).
"Recalled" means from memory of the literature, not re-checked in this round.

**Nothing in this note or in the Lean proves the Hodge conjecture, or any case of it that was not already known.** The
Lean proves the linear algebra and the diagram chases; the geometry (Hodge theory, the exponential sequence, hard
Lefschetz, intersection theory on a surface) enters as named `External` slots, and the Hodge conjecture itself is the
card's one `OpenStep`.

---

## 0. In plain words

**The question.** Take a smooth shape cut out by polynomial equations in complex projective space (a smooth projective
variety). Its cohomology describes it with numbers: holes of every dimension, and how they cross. Some cohomology classes
have a special form: rational, and of "type `(p, p)`" (balanced between holomorphic and antiholomorphic directions). Every
actual subvariety, a shape cut out by more equations, gives such a class. The Hodge conjecture says the converse: **every
rational `(p, p)` class comes from subvarieties** (a rational combination of their classes). In the owner's words:
**what can be described exists.**

**What is known.** For `p = 1` it is a theorem (Lefschetz, 1924): every such class in degree 2 comes from divisors
(hypersurfaces), and even with integer coefficients. By hard Lefschetz it then also holds for curves (degree `2n - 2`).
So every variety of dimension at most 3 is settled. Beyond that, only special families are known, mostly abelian
varieties (products of circles, algebraically).

**What fails.** Two natural strengthenings are false. With integer coefficients instead of rational ones (Atiyah and
Hirzebruch, 1962; Kollar, 1992). And on compact Kaehler manifolds that are not projective (Zucker; Voisin, 2002). So
"describable" must mean **rational, on a projective variety**; that is the care point of the owner's reading.

**The positivity.** On the Hodge classes a natural form is **positive definite**: the Hodge-Riemann bilinear relations,
a theorem of Hodge theory. Positivity on Hodge classes passes to algebraic classes, because they are Hodge classes. Over
the complex numbers that is Grothendieck's "Hodge standard conjecture", which is therefore a theorem there. **Over a finite
field the same positivity is open**, and it is exactly what would prove the Riemann hypothesis for varieties over finite
fields by the "system runs and certifies the line" route: a positive form on which Frobenius is a similitude puts every
Frobenius eigenvalue on a circle. For curves it is proved: the Hodge index theorem on the surface `C x C` gives Weil's
bound `|N - (q + 1)| <= 2 g sqrt q`. Deligne proved the general Riemann hypothesis over finite fields in 1974 by a different
route; the positivity route remains open. This is the same missing positivity as the GRH sign: an arithmetic Hodge index
theorem on "`Spec Z x Spec Z`" would be the GRH analogue of the Hodge index theorem on `C x C`.

**What the round built.** The Hodge card in the API's shape, input + proved structure + one named open step: the input
is rational cohomology with its Hodge classes (described) and its algebraic classes (existing); the open step is the
Hodge conjecture; the conclusion is "described = exists". Around it, everything Mathlib can reach was proved in Lean: the
positivity on Hodge classes of a polarised Hodge structure, its consequences for algebraic classes, the Hodge index
theorem as linear algebra (signature `(1, *)`), Weil's bound for curves derived from it, the eigenvalue-on-the-circle
statement, and the Lefschetz (1,1) chase. The card's slot is filled for divisors and curves, so it is not empty.

**What Mathlib has.** Almost none of the geometry: no complex manifolds beyond holomorphic functions, no Kaehler metrics,
no de Rham theorem, no Hodge decomposition, no cycle class map. It does have algebraic cycles on a scheme (new in 2026),
singular homology, sheaf cohomology, Kaehler differentials in the algebraic sense, and, importantly, the signature of a
quadratic form (Sylvester's law of inertia, also new in 2026), which the Hodge index statement here uses.

---

## 1. The statement and the state of the art

### 1.1 The Clay statement [classical]

Clay's official problem (Deligne's description): let `X` be a projective non-singular algebraic variety over `C`. A
**Hodge class** is a class in `H^{2p}(X, Q)` whose image in `H^{2p}(X, C)` lies in `H^{p,p}` of the Hodge decomposition
`H^k(X, C) = ⊕_{p+q=k} H^{p,q}`. The class `cl(Z)` of an algebraic subvariety `Z` of codimension `p` is a Hodge class.
**Hodge conjecture:** on a projective non-singular algebraic variety over `C`, every Hodge class is a rational linear
combination of classes `cl(Z)` of algebraic cycles.

In the Lean (`HodgeAPI.lean`): `Input` holds `V = H^{2p}(X, Q)`, the Hodge classes `hodge`, the rational span of cycle
classes `alg`, and the classical inclusion `alg ≤ hodge` (`External`). `HodgeConjecture i` is `hodge ≤ alg`, in the
`OpenStep` slot.

### 1.2 What is proved [classical; external where marked]

| case | result | status |
|---|---|---|
| `p = 1` (divisors) | **Lefschetz (1,1) theorem** (Lefschetz 1924; sheaf proof Kodaira-Spencer 1953): an integral class in `H^2(X, Z)` is of type `(1,1)` iff it is the first Chern class of a holomorphic line bundle; on projective `X` every line bundle is `O(D)` for a divisor `D`. So the Hodge conjecture holds for `p = 1`, even integrally. | classical |
| `p = n - 1` (curves) | Hard Lefschetz `L^{n-2} : H^2 → H^{2n-2}` is an isomorphism of Hodge structures and sends divisor classes to curve classes, so the rational Hodge conjecture holds in degree `2n - 2`. | classical |
| dimension `≤ 3` | follows from the two rows above (the only degrees with `(p, p)` classes are `p = 0, 1, n - 1, n`). | classical |
| abelian varieties whose Hodge ring is generated by divisor classes | the Hodge conjecture holds (every Hodge class is a product of divisor classes); this covers e.g. a very general abelian variety (Mattuck) and simple abelian varieties of prime dimension (Tankeev). Mumford's example and Weil's classes show not all abelian varieties are of this kind. | classical / external, recalled |
| abelian fourfolds of Weil type | Weil classes algebraic: discriminant 1 by Markman (2022; simpler proofs by Floccari-Fu and by van Geemen-Rapagnetta); for every abelian fourfold of Weil type by Markman, arXiv 2509.23403 (2025), which reports that the Hodge conjecture for abelian varieties of dimension at most 5 then follows (with Moonen-Zarhin). | external, abstracts read only, not checked |
| other families | e.g. cubic fourfolds (Zucker), uniruled fourfolds (Conte-Murre), some Fermat hypersurfaces (Shioda). | external, recalled |

In the Lean: the `p = 1` case is `DivisorInput.holds` (the exponential sequence, the Hodge decomposition of `H^2` and the
divisor interpretation as three `External` slots; the chase `lefschetz11` and the rational descent `rational_descent`
proved), and the `p = n - 1` case is `CurveClassInput.holds` (hard Lefschetz as `External`; the transfer proved).

### 1.3 What fails [external, recalled]

- **Integral coefficients** [fails]. The integral Hodge statement ("every integral class whose rational image is Hodge is
  algebraic") is false. Atiyah and Hirzebruch (1962) found torsion classes in `H^4(X, Z)` that are not algebraic
  (algebraic classes satisfy topological constraints, Steenrod operations / complex cobordism, which some torsion classes
  violate; Totaro 1997 gave the cobordism reading). Torsion classes are automatically "Hodge" (their rational image is
  `0`), so the integral version needs every torsion class to be algebraic: `integral_needs_torsion` [Lean], and with the
  Atiyah-Hirzebruch class as an `External`, `integral_fails` [Lean]. Kollar (1992) found non-torsion failures as well:
  integral classes on hypersurfaces that are not algebraic though a multiple is.
- **Non-projective Kaehler manifolds** [fails]. On a general complex torus there can be Hodge classes but too few analytic
  subvarieties (Zucker, 1977); Voisin (2002) showed that even with Chern classes of coherent sheaves (the natural
  Kaehler extension) the statement fails on some complex tori. Projectivity is part of the hypothesis, not a convenience.

### 1.4 The standard conjectures and positivity [classical; open where marked]

Grothendieck's **standard conjectures** (1969; Kleiman's account) for a Weil cohomology of a smooth projective variety:
- **B (Lefschetz type):** the inverse of hard Lefschetz is given by an algebraic correspondence. Known in characteristic 0
  for abelian varieties (Lieberman) and some other classes; implied by the Hodge conjecture in characteristic 0. [open in
  general]
- **C (Kunneth type):** the Kunneth projectors are algebraic. Over finite fields a consequence of the Weil conjectures
  (Katz-Messing 1974). [open over `C` in general; follows from B]
- **D:** numerical equivalence equals homological equivalence. [open in general]
- **Hodge type (I):** on primitive algebraic classes of codimension `p ≤ n/2` the form `(-1)^p ⟨x, L^{n-2p} x⟩` is
  positive definite.

The Hodge-type conjecture is the positivity. **In characteristic 0 it is a theorem**: the Hodge-Riemann bilinear
relations make the form definite on primitive Hodge classes, and algebraic classes are Hodge classes. The Lean makes this
step explicit: `PosInput.alg_pos` [Lean, with Hodge-Riemann as an `External`]; consequences `num_eq_hom` (D in this
piece) and `alg_cs` (the encoder bound). **In characteristic `p` it is open** except for surfaces, where it is the Hodge
index theorem (Hodge 1937; Segre; Grothendieck 1958 in every characteristic), and some further cases (e.g. Ancona 2021 for
abelian fourfolds) [external, recalled].

**The link to the Weil conjectures.** The Riemann hypothesis part of the Weil conjectures says that the Frobenius
eigenvalues on `H^w` have absolute value `q^{w/2}`. Weil proved it for curves (1948) through the Castelnuovo-Severi
inequality, which is the Hodge index theorem on `C x C` (Mattuck-Tate 1958; Grothendieck 1958). Grothendieck's plan: the
standard conjectures (B and Hodge type) give it for every smooth projective variety by the same positivity (Serre's
Kaehler analogue, 1960: a positive involution on the algebra of correspondences makes Frobenius divided by `q^{w/2}` an
isometry). **Deligne proved the Riemann hypothesis over finite fields in 1974 by another route** (Lefschetz pencils,
monodromy and Rankin's squaring trick), without the standard conjectures, which remain open. [classical]

In the Lean: `weil_bound`, `weil_bound_abs` [Lean] derive `(N - q - 1)^2 ≤ 4 g^2 q` from the intersection numbers on
`C x C` and the Hodge index property; `hodgeIndex_of_sigPos` [Lean] derives the Hodge index property from the signature
statement (one positive direction); `eigen_on_circle_form` [Lean] puts the eigenvalues of a similitude of a positive
Hermitian form on the circle `|μ|^2 = c`. The full Riemann hypothesis for a curve also needs the bound for every extension
`F_{q^n}` and the rationality of the zeta function [classical, not in the Lean].

### 1.5 What is open [open]

- The Hodge conjecture for `p ≥ 2` in general (first open case: `H^4` of fourfolds), including for general abelian
  varieties beyond the cases of 1.2.
- The standard conjectures B (in general), D, and the Hodge type in positive characteristic.
- Any positivity route to the Riemann hypothesis over finite fields beyond surfaces (Deligne's theorem is proved, the route
  is not), and the arithmetic analogue over `Z`.

---

## 2. What Mathlib v4.34.0 has

Searched in the Mathlib checkout the project builds against (v4.34.0). Expected very little; the result:

| needed for Hodge | in Mathlib v4.34.0 | where |
|---|---|---|
| complex manifolds | charted spaces over `C`, holomorphic (`MDifferentiable`) maps; only two theorems specific to complex manifolds (holomorphic functions on a compact one are constant); the file's TODO lists holomorphic bundles and sheaves as future work | `Geometry/Manifold/Complex.lean` |
| Kaehler metrics | **none** (`Kaehler` in Mathlib means Kaehler differentials `Ω[S/R]` of commutative algebra) | `RingTheory/Kaehler/` |
| Riemannian metrics | basic (`Geometry/Manifold/Riemannian/Basic.lean`, path length) | |
| differential forms, de Rham | exterior derivative of forms on a **normed space** (`extDeriv`, `d ∘ d = 0`); not on manifolds; no de Rham cohomology, no de Rham theorem | `Analysis/Calculus/DifferentialForm/` |
| singular (co)homology | singular homology functor, homotopy invariance, `H_0`; Eilenberg-Steenrod axioms as a structure; no cup product, no Poincare duality | `AlgebraicTopology/SingularHomology/`, `EilenbergSteenrod.lean` |
| sheaf cohomology | `Sheaf.H F n` on a site as Ext groups; Mayer-Vietoris | `CategoryTheory/Sites/SheafCohomology/` |
| l-adic cohomology | pro-etale `H^i(X, Z_l)` defined (2026) | `AlgebraicGeometry/Sites/ElladicCohomology.lean` |
| Hodge decomposition, Hodge structures | **none** (one bibliography mention of Deligne's Hodge II in `CategoryTheory/Filtration/Basic.lean`, filtered objects) | |
| algebraic cycles | **yes, new (2026)**: `AlgebraicCycle X R`, functions with locally finite support on a scheme, and their pushforward along quasi-compact maps; no rational equivalence, no Chow ring, no intersection product, no cycle class map | `AlgebraicGeometry/AlgebraicCycle/Basic.lean` |
| line bundles, divisors on schemes | Picard group of a commutative ring only (`RingTheory/PicardGroup.lean`); no Weil or Cartier divisors on schemes | |
| projective varieties | `Proj` of a graded ring, properness; smooth morphisms | `AlgebraicGeometry/ProjectiveSpectrum/`, `Morphisms/Smooth.lean` |
| Lefschetz theorems | none (only the model-theoretic "Lefschetz principle") | |
| quadratic forms, signature | **yes**: `sigPos`, `sigNeg`, Sylvester's law of inertia (2026), positive-definite forms, orthogonal complements, `isCompl_orthogonal_of_restrict_nondegenerate`, the quadratic discriminant | `LinearAlgebra/QuadraticForm/Signature.lean`, `BilinearForm/Orthogonal.lean`, `Algebra/QuadraticDiscriminant.lean` |
| eigenvalues | `Module.End.HasEigenvalue`, eigenvectors | `LinearAlgebra/Eigenspace/` |
| the circle | `Circle` (the API's `Phase`) | |

**A Mathlib-only foundation worth building for IM.** `HodgeLinear.lean` is that foundation for this round: it imports only
Mathlib and could move unchanged into the `im` repository's `form/` package (`API.md` section 7) as `Form.Hodge`. What it
holds, and what would extend it naturally:
- **built** [Lean]: polarised real Hodge structures of weight 0 in Deligne's circle form (`PolHS`), positivity and
  Cauchy-Schwarz on Hodge classes, the orthogonal splitting off of the Hodge classes; the Hodge index theorem from the
  signature, and the reversed Cauchy-Schwarz; Castelnuovo-Severi and Weil's bound; eigenvalues of similitudes; the
  Lefschetz (1,1) chase, rational descent, transfer along an isomorphism, the torsion obstruction.
- **next, reachable** (not built): the Lefschetz decomposition of a finite-dimensional `sl_2`-representation (hard
  Lefschetz as linear algebra: an `sl_2`-triple on a graded space gives `L^k : V_{-k} ≅ V_k` and the primitive
  decomposition); the Hodge-Riemann signature formula for a polarised Hodge structure of any weight (the signature of `Q`
  from the Hodge numbers); Hodge structures of weight `k` with the Hodge filtration; the finiteness of lattice Hodge
  classes of bounded norm (positivity plus discreteness).
- **far** (needs geometry Mathlib lacks): Kaehler manifolds, harmonic forms, the Hodge decomposition itself, the cycle class
  map, the exponential sequence on a complex manifold.

---

## 3. The API instance (`HodgeAPI.lean`)

### 3.1 The card: input + proved structure + one named open step

| | |
|---|---|
| input (`Input`) | `V = H^{2p}(X, Q)`; `hodge` = the rational `(p, p)` classes (the **describable** side); `alg` = the rational span of the classes of codimension-`p` algebraic cycles (the side that **exists**); `alg_le : External` (cycle classes are Hodge classes, classical) |
| open step (`HodgeConjecture`) | `OpenStep "Hodge conjecture: ..." (hodge ≤ alg)` [open] |
| conclusion | `hodge = alg`: described = exists [Lean from the open step] |
| sources | the cycle class is a Hodge class (classical) |

`problem.proved` is `le_antisymm`: the card adds no mathematics, it shows the shape. The content is all in the slot, as
for every card.

### 3.2 The positivity (the encoder bound) [Lean, Hodge-Riemann `External`]

`PosInput` adds a symmetric rational form `Q` (the polarisation on a primitive piece) and the Hodge-Riemann relations on
rational Hodge classes as an `External`. Proved:
- `alg_pos`: `Q` is positive definite on algebraic classes (the Hodge standard conjecture in characteristic 0);
- `num_eq_hom`: an algebraic class orthogonal to all algebraic classes is zero (conjecture D in this piece);
- `alg_cs`: `Q(x, y)^2 ≤ Q(x, x) Q(y, y)` on algebraic classes, the **encoder bound** (the same Cauchy-Schwarz that bounds
  the reflection coefficient in `Encoder`, `‖c‖ ≤ 1`).

Where the `External` comes from: `hr_of_polHS` [Lean] shows that a real polarised Hodge structure in the circle model
(`PolHS`) whose rational points carry `Q` gives exactly the `hr` slot; the positivity behind it is `PolHS.hodge_pos`
[Lean]: on a vector fixed by the circle the Weil operator is the identity, so `Q (C x) x > 0` becomes `Q x x > 0`. What
remains outside is the theorem of Hodge theory that the cohomology of `X` is such a structure.

### 3.3 The slot is not empty: divisors and curves [Lean, three plus two `External`]

- `DivisorInput` (`p = 1`): line bundles, `H^2(X, Z)`, `H^{0,2}`, `H^2(X, Q)`; `c₁`, the map `π` to `H^{0,2}`, the map
  `ι` to rational cohomology. `External`: exactness of the exponential sequence at `H^2(X, Z)`; a rational `(1,1)` class
  has an integral multiple with no `(0,2)` part; divisor classes are `(1,1)` and every line bundle on a projective `X` is
  `O(D)`. **`DivisorInput.holds : problem.Open D.toInput`** [Lean]: the Hodge conjecture's slot is filled for divisors,
  and `DivisorInput.card` gives described = exists there.
- `CurveClassInput` (`p = n - 1`): hard Lefschetz `L : H^2(X, Q) ≅ H^{2n-2}(X, Q)` with two `External` facts (its inverse
  keeps Hodge classes; it sends divisor classes to curve classes). **`CurveClassInput.holds`** [Lean] by `transfer`.

### 3.4 Describable must mean rational [Lean, Atiyah-Hirzebruch `External`]

`IntegralInput`, `IntegralHodge`; `integral_fails`: given a non-algebraic torsion class (Atiyah-Hirzebruch, `External`),
the integral statement is false. The reason is `integral_needs_torsion` (in `HodgeLinear`): torsion maps to `0` in rational
cohomology and `0` is a Hodge class.

### 3.5 The GRH column: the same positivity over a finite field

- `weilCard` (Problem): input = Frobenius `F` on weight-`w` cohomology over `F_q`; open step `StandardHodge` = a
  positive-definite Hermitian form on which `F` is a similitude of ratio `q^w` (the Hodge standard conjecture, in the form
  the Riemann hypothesis needs) [open]; conclusion: every eigenvalue has `|μ|^2 = q^w` [Lean from the open step,
  `eigen_on_circle_form`]. Source: Deligne 1974 proves the conclusion for `l`-adic cohomology by another route.
- `curveCard` (Problem): input = the intersection form on `NS(C x C) ⊗ R` with fibre classes, graph of Frobenius and
  diagonal and their intersection numbers (`External`, classical); open step = the Hodge index property at the ample class
  `f₁ + f₂`; conclusion = **Weil's bound `|N - (q + 1)| ≤ 2 g sqrt q`** [Lean from the open step].
- `curve_open` [Lean]: with the Hodge index theorem in its signature form (one positive direction, `External`: Hodge 1937,
  Grothendieck 1958) the open step holds (`hodgeIndex_of_sigPos`), and with it the bound. This is the column's proved
  instance: positivity runs the system and certifies the line, for curves.

The derivation in plain steps (all [Lean] in `HodgeLinear` section 3): put `D = aΓ + bΔ`; Castelnuovo-Severi (Hodge index
applied to `D - (D f₂) f₁ - (D f₁) f₂`, which is orthogonal to `f₁ + f₂`) gives `D^2 ≤ 2 (D f₁)(D f₂)`; with the
intersection numbers this is `g q a^2 - a b (N - q - 1) + g b^2 ≥ 0` for all real `a, b`; choosing `a = N - q - 1`,
`b = 2 g q` gives `(N - q - 1)^2 ≤ 4 g^2 q`.

---

## 4. The DMP reading

**"Describable implies exists", exactly** [reading on a classical statement]. The Hodge conjecture is the cleanest
instance of the owner's sentence among the seven problems: the describable objects are the rational `(p, p)` classes
(cohomology describes them); the existing objects are the algebraic cycles (geometry builds them); the conjecture is
`describable ⊆ exists`, the converse `exists ⊆ describable` being classical. In the API it is literally
`OpenStep (hodge ≤ alg)` with `alg ≤ hodge` as an `External`, and the card's conclusion is `hodge = alg`.

**Its exact counterpart in the project.** The `PREP.md` entry "Describable => exists => positive" anchored "describable
implies exists" in Goedel's completeness theorem (a consistent first-order theory has a model). The Hodge conjecture is the
geometric version, and it is not a logical triviality: here a description is a cohomology class with a Hodge-type
condition, and existence is an algebraic cycle; no completeness theorem bridges them, which is why it is open.

**The care point: describable must mean rational, on a projective variety** [classical, `integral_fails`]. Integral
"descriptions" include torsion classes, which every description of type `(p, p)` admits (their rational image is `0`) but
which need not exist as cycles (Atiyah-Hirzebruch); and on non-projective Kaehler manifolds descriptions outrun existence
(Zucker, Voisin). In DMP terms: a description counts only after tensoring with `Q` (torsion carries no "charge" a cycle
must match) and only on a space with an ample class (the polarisation that makes the positivity available). The owner's
sentence holds at most in that form, and in that form it is the open conjecture.

**Hodge types as charges on the G0 circle** [reading on a classical construction]. In Deligne's definition a real Hodge
structure is a representation of the Deligne torus; its circle part acts on `H^{p,q}` by `z^{p-q}`. So a Hodge type is a
charge on the circle, quantised by the API's `ChargeQuantisation` (`API.md` section 8: every continuous character of the
G0 circle is `z ↦ z^n`). The Hodge classes are the **neutral** rational vectors (charge 0, fixed by the circle): `PolHS.hodge`
is defined exactly so, with `h : Circle →* Module.End ℝ V` (`Circle` is the API's `Phase`). Described = neutral and
rational; exists = built from subvarieties.

**The shared positivity with the GRH column** [reading; the Lean steps are marked]. The "exists => positive" half of the
owner's sentence is, for Hodge, the Hodge-Riemann relations: on the described (Hodge) classes the polarisation is
positive [classical, `hodge_pos` Lean in the model], so on the existing (algebraic) classes too [`alg_pos` Lean]. Over `C`
that positivity is proved. Over `F_q` the same positivity is Grothendieck's Hodge standard conjecture [open], and it is
the positivity that would put Frobenius eigenvalues on the critical circle [`eigen_on_circle_form` Lean]; for curves the
Hodge index theorem on `C x C` supplies it and Weil's bound follows [`curve_open`, `weil_bound` Lean]. Over `Z` the
analogue would be a Hodge index theorem on "`Spec Z x Spec Z`", which does not exist; that missing positivity is exactly
the GRH card's `ScaleSign` slot (`API/GRH.lean`), with the explicit formula as the trace formula in place of the
Lefschetz fixed-point formula. The two columns have the same shape: **a positive form, a dynamics that is a similitude
of it, and the line as the consequence**. In GRH and in Hodge over `F_q` the positive form is the open step; over `C`, and
for curves over `F_q`, it is a theorem.

---

## 5. Status table

| item | status | where |
|---|---|---|
| Hodge conjecture (Clay) | open | `HodgeConjecture` (`OpenStep`) |
| card: open step gives described = exists | Lean | `problem` |
| cycle classes are Hodge classes | classical | `Input.alg_le` (`External`) |
| Hodge-Riemann positivity on Hodge classes of a polarised Hodge structure (circle model) | Lean | `PolHS.hodge_pos`, `hodge_cs`, `hodge_isCompl` |
| Hodge-Riemann relations for the cohomology of a projective manifold | classical | `PosInput.hr` (`External`), linked by `hr_of_polHS` (Lean) |
| Hodge standard conjecture in characteristic 0; D on algebraic classes; encoder bound | Lean from Hodge-Riemann | `alg_pos`, `num_eq_hom`, `alg_cs` |
| Lefschetz (1,1), rationally and integrally | classical; chase Lean | `lefschetz11`, `rational_descent`, `DivisorInput.holds` |
| curves via hard Lefschetz | classical; transfer Lean | `transfer`, `CurveClassInput.holds` |
| integral Hodge needs all torsion algebraic; integral version fails | Lean; Atiyah-Hirzebruch external | `integral_needs_torsion`, `integral_fails` |
| non-projective Kaehler version fails | external (Zucker, Voisin) | text only |
| abelian varieties, special families | classical / external | text only |
| Hodge index from signature `(1, *)`; reversed Cauchy-Schwarz | Lean | `hodgeIndex_of_sigPos`, `reverse_cs` |
| Castelnuovo-Severi; Weil's bound for curves | Lean from the Hodge index property and the intersection numbers | `castelnuovo_severi`, `weil_bound`, `weil_bound_abs`, `curveCard`, `curve_open` |
| Hodge index theorem on a surface | classical | `curve_open` (`External`) |
| positivity puts Frobenius eigenvalues on `|μ|^2 = q^w` | Lean from the open step | `eigen_on_circle`, `eigen_on_circle_form`, `weilCard` |
| Hodge standard conjecture over `F_q` | open (beyond surfaces and special cases) | `StandardHodge` (`OpenStep`) |
| Riemann hypothesis over `F_q` | classical (Deligne 1974, another route) | `weilCard.sources` |
| arithmetic Hodge index on "`Spec Z x Spec Z`" | open (no such object) | the GRH card's `ScaleSign` |
| DMP readings (describable = rational neutral; shared positivity) | reading | section 4 |

## 6. Files and checks

- `docs/mass-gap/formal/ProofPhase/Unified/HodgeLinear.lean`: Mathlib-only core (22 declarations).
- `docs/mass-gap/formal/ProofPhase/Unified/HodgeAPI.lean`: the API instance (25 declarations); placed under `Unified/`
  like `NavierStokesAPI.lean`, namespace already `ProofPhase.API.Hodge`, so it can move to `API/` unchanged.
- `docs/unified/hodge-axioms.sh`, `hodge-axioms.log`: build both, `#print axioms` on every declaration, source grep.
  Run in the WSL replay distro from the repository root: `bash docs/unified/hodge-axioms.sh > docs/unified/hodge-axioms.log 2>&1`
  (build folder `$FORMAL_DST`, default `~/formal-hodge`).
- Build one module: `FORMAL_DST=~/formal-hodge bash docs/mass-gap/formal/sync-build.sh ProofPhase.Unified.HodgeAPI`.
- Not touched: `API.md` (its section 4 table could gain a Hodge row), `BLOWUP.md` section 10 (Hodge is no longer
  "not pursued"), `Unified/All.lean`, the paper; left to the coordinator.
