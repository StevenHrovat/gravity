# Perelman on the form layer, and "Poincare for SU(N)" (ledger row VI.6.3j)

*Research round, 2026-11-24. Notes only: no paper edits, no Lean, nothing committed. Answers the owner's reading of 2026-11-24
(`docs/mass-gap/weak-coupling/PREP.md`, "Five answers", item 5): "Sounds like we can contribute by generalizing Perelman's approach
for DMP, I am sure we'll get a better construction from it." Builds on `BLOWUP.md` sections 6 and 7 (Perelman as a ledger, SU(N)
under Ricci flow) and on `docs/paper/OPEN-CLAIMS-CLOSURES.md` 2.3 (the surgery sketch for VI.6.3j), and does not repeat them.*

Marks as in the paper (Part I, I.0): **[classical]** known, with a reference; **[external]** published by others, read here, not
rebuilt; **[paper]** argued here in prose; **[reading]** a DMP reading; **[open]** not settled by anyone. "Recalled" means the
reference was not re-read this round.

## 0. The result in five lines

1. **VI.6.3j is settled, in both categories, and the open remainder "smooth N = 3" closes.** N = 2: true (Poincare). N = 3: true
   topologically *and* smoothly: every closed smooth manifold homotopy equivalent to SU(3) is diffeomorphic to it. This is a
   published theorem (X. Wang, Acta Math. Sinica 2021, Theorem 1.1 and Corollary 1.2). N >= 4: false topologically and smoothly.
2. **The earlier sketch is confirmed in all three parts**, with two gaps closed: N = 3 topological needed one more argument (why
   no differential spoils the count), and N >= 4 with N odd needed the obstruction to be adjusted without touching degree 8. Both
   are filled in section 2. Its hedge for smooth N = 3 ("depends on the inertia group") was the right reduction, and the inertia
   group turns out to contain the exotic 8-sphere.
3. **Perelman in form-layer terms** (section 1): the entropy and reduced volume are ledgers *at the floor* (zero cost). They buy a
   sign (no collapse), not a count. The count comes from two ledgers *above the floor*: volume per surgery, and the width's 4 pi per
   unit time. Surgery is a **typed** excision, not an R136a1: what is cut keeps its type, and the record rebuilds the manifold.
4. **What a DMP-generalised Perelman adds for SU(N): nothing new about the answer**, which is classical-complete. Two things are
   still worth having. One is a clean criterion: "rigid exactly when nothing is free below the top cell". The other is a
   falsifiability check: any "better construction" must fail for N >= 4, because the statement is false there.
5. **For the Navier-Stokes card the template is useful.** It names exactly what NS lacks against Perelman: a catalogue of what
   reaches the boundary, a quantum per act that does not shrink with scale (Caffarelli-Kohn-Nirenberg gives one that does), and a
   canonical continuation (VI.5.3).

No solution of any open problem is claimed. The SU(N) answer is classical mathematics (one published theorem, plus a standard
surgery computation written out here).

---

## 1. Perelman's construction in the form layer's terms

The form layer (Part II, II.11): a *running system* has states, a step, an encoder factor, a mass, and the ledger law
`mass(step x) <= e^delta fac(x) mass(x)`. In the additive form, step i adds at least `c_i - delta` to a global quantity G
(`Unified/Ledger.lean`, `Accrues`, `accrue`). With a cost above the floor, settling takes an explicit number of steps
(`reaches_of_contracting`, `balanceBound`). At the floor, no procedure decides it for all content (`etm_edge`). Both sides are
**[Lean]**.

### 1.1 The dictionary

| Form layer | Perelman (Ricci flow with surgery on a closed 3-manifold) | Mark |
|---|---|---|
| states | Riemannian metrics on M, plus the surgered manifolds | [classical] |
| step | the smooth flow `dg/dt = -2 Ric` on an interval between surgery times | [classical] |
| **ledger at the floor** (cost >= 0, floor 0) | the W-entropy `mu(g(t), tau_0 - t)`, non-decreasing; its derivative is `2 tau int abs(Ric + Hess f - g/(2 tau))^2 u dV >= 0`, zero exactly on shrinking solitons. It is bounded above by 0, the Euclidean value, while the flow exists. The reduced volume `V~(tau)`, non-increasing, `<= 1`, equal to 1 only for flat space, works the same way (Perelman 2002, sections 3 and 7, recalled) | [classical] |
| what the floor-ledger buys | kappa-noncollapsing at every scale below `sqrt T`: a collapsed ball would make the entropy (or reduced volume) small at a small scale, but monotonicity bounds it below by its value at the start. **A sign, carried to all scales, not a rate** | [classical] for the theorem; [reading] for "a sign, not a rate" (as in `BLOWUP.md` 6.5) |
| "balance" of the floor-ledger | the equality case: shrinking solitons. Blowup limits are modelled on them (kappa-solutions) | [classical]; [reading] that the soliton is the floor-ledger's balance state |
| **ledger above the floor, 1: the act count** | each surgery removes at least a volume `v(h, delta) > 0`. Volume grows at most at a controlled rate (`dV/dt = -int R dV`, R bounded below), so it stays below a bound `B(T)` on `[0, T]`. Hence at most `B(T)/v` surgeries on `[0, T]` (Perelman 2003a, recalled) | [classical]; the count is `accrue` with `c_i >= v`, `delta = 0` [paper: instance check, not formalised] |
| **ledger above the floor, 2: termination** | for simply connected M, the width W(t) (min-max area of sweepouts) satisfies `dW/dt <= -4 pi + (3/(4t + C)) W`, so the flow becomes extinct in finite time (Perelman 2003b; Colding-Minicozzi 2005, recalled) | [classical]; [reading]: cost `4 pi` per unit time above a floor that shrinks relative to it, the settle theorem in additive form (as in `BLOWUP.md` 6.4) |
| the boundary (DB) | a singular time; the high-curvature region is covered by canonical neighbourhoods (necks, caps, closed positively curved pieces) | [classical] |
| **the act at the boundary** | surgery: cut along a nearly round 2-sphere in a neck, glue standard caps, **discard components of known type**, restart | [classical] |
| what reaches the boundary | a finite catalogue: kappa-solutions, classified in dimension 3 | [classical] |
| the certificate | at extinction, read backwards: M is a connected sum of the discarded pieces (spherical space forms, `S^2 x S^1`); if `pi_1(M) = 1`, every piece is `S^3`, so M is `S^3` | [classical] |

### 1.2 Floor: what plays it

The owner's question was whether entropy monotonicity is "cost above a floor". **It is not. It is cost *at* the floor** (increment
>= 0, floor 0), which is the edge side of the settle theorem. On that side the form layer gives no step count, and Perelman gets
none from the entropy either. The entropy's role is to carry one estimate (no collapse) to every scale, because it is scale
invariant. **[reading]** on **[classical]** facts.

The step counts in Perelman's proof come from two other ledgers, and both are strictly above the floor. The volume ledger has a
quantum `v > 0` per act and a bounded budget, so finitely many acts. The width ledger has a cost `4 pi` per unit time, so
extinction by an explicit time. **[reading]**. So Perelman's proof uses **both sides of the edge, for different jobs**: the floor
side for rigidity (what the singularities look like), the side above the floor for counting (how many, and when it ends).
**[reading]** (new in this note; the dichotomy itself is II.11, Lean).

### 1.3 Surgery: excision, but not R136a1

I.9: an act answered R136a1 is outside, and only a content-free **remnant tail** stays, "the count is the assertion of the
excision and carries none of the excised information" (I.9a). Perelman's surgery differs in exactly this respect. Every discarded
piece is of a known **type**, and the record of the cuts (a connected-sum decomposition) **rebuilds M completely**. The theorem
comes out of that record. **[classical]** for the facts. **[reading]**: Perelman's act is a *typed excision*. Its remnant carries
the type of what was cut, and the certificate is read from the remnants.

Care point **[paper]**: calling Perelman's surgery "R136a1-like" would be inexact. R136a1 forgets the excised content by design.
Perelman's surgery works only because it does not. If the paper uses the word, it should say "typed excision" and point here.

### 1.4 Where the decidable/undecidable edge sits

For the *proof*, see 1.2: the floor side (entropy) and the side above it (volume, width). For the *problem*, the recognition
question "is this manifold the sphere?":

* **Dimension 3: decidable.** Recognising `S^3` is decidable (Rubinstein 1995, Thompson 1994), and in NP (Schleimer 2011). After
  geometrisation the homeomorphism problem for closed 3-manifolds is decidable. **[classical]** (recalled; the last point also in
  arXiv 1508.06720).
* **Dimension >= 5: undecidable in general.** Recognising `S^n`, n >= 5, is undecidable (Novikov, in Volodin-Kuznetsov-Fomenko
  1974). The hard instances are homology spheres whose fundamental group cannot be decided trivial (word problem). **[classical]**
  (recalled; summarised in Poonen's sampler, arXiv 1204.0299).
* **Dimension >= 5 with `pi_1 = 1` given: decidable.** Nabutovsky-Weinberger: a simply connected manifold of dimension >= 5 can be
  recognised among simply connected manifolds. **[external]** (arXiv math/9707232, abstract read this round).

**Reading [reading].** The undecidable part is **one named hypothesis**, `pi_1 = 1`. Taken as a stated hypothesis and not checked,
it leaves a decidable remainder. That is the R136a1 move of I.9b in its proper use: name the part that cannot be settled from
inside and keep it outside, then settle the rest. In dimension 3 the promise is not needed: after geometrisation, 3-manifold
groups have a solvable word problem, so `pi_1 = 1` can itself be decided **[classical, recalled]**. In dimension >= 5 it cannot,
and recognition is a problem with a promise. For SU(N), simple connectivity is classical, so the question lies on the decidable
side.

### 1.5 The form-layer shape of the whole proof (a candidate theorem, not formalised) [paper]

Strip the geometry and four hypotheses remain. Each one is a geometric theorem in Perelman's case.

* (P1) a ledger at the floor that is scale invariant: gives one estimate at all scales;
* (P2) a catalogue C: everything that reaches a boundary is modelled on C;
* (P3) a budget with a quantum per act: finitely many acts on bounded time;
* (P4) a terminating ledger above the floor: the run ends.

If every act splits the state as `x = y * z` with `z` in C (typed excision), and the run ends at the unit, then `x` is a product of
catalogue pieces. The form layer can prove this conclusion: it is an induction over the acts, using P3 and P4 for finiteness. The
topology enters only through C and through one property ("`pi_1` trivial forces each factor trivial") **[paper]**. This is what a
"DMP-generalised Perelman" can honestly mean: the four slots and the reconstruction theorem. Filling P1 to P4 for a new geometric
flow is the hard work every time, and none of it is supplied by the form layer **[paper]**.

---

## 2. Independent check of the surgery sketch for VI.6.3j

The sketch (OPEN-CLAIMS-CLOSURES 2.3): false topologically for N >= 4; true topologically for N = 3; smooth N = 3 depends on the
inertia group of SU(3). M = SU(N), `n = N^2 - 1`, simply connected, closed, parallelisable. `H^*(M; Z)` is the exterior algebra on
classes of degrees 3, 5, ..., 2N - 1 (torsion free) **[classical]**.

### 2.1 N = 3, topological: confirmed, by my own computation and by the literature

**Literature [external].** X. Wang, "On 1-connected 8-manifolds with the same homology as `S^3 x S^5`", *Acta Math. Sinica (Engl.
Ser.)* 37 (2021), no. 6, 941-956 (arXiv 1810.08478). Theorem 1.1(2): the topological manifolds of this homology type are
`S^3 x S^5`, SU(3) and one more, `M_{1,0}`. Corollary 1.2(1): two of them "are homeomorphic if and only if they are homotopy
equivalent". SU(3) is in the class (`H^*` in degrees 0, 3, 5, 8). So every closed topological manifold homotopy equivalent to SU(3)
is homeomorphic to it. (Read in the arXiv version this round: Theorem 1.1, Corollary 1.2, section 5.)

**Own check [paper].** This repeats the sketch and fills its one gap.

* Surgery exact sequence (TOP, `n = 8 >= 5`, simply connected): `L_9(1) -> S(M) -> [M, G/TOP] -> L_8(1) = Z`. Here `L_9(1) = 0`,
  so S(M) injects into the normal invariants **[classical]** (Browder 1972; Wall 1970; Kirby-Siebenmann 1977, recalled).
* `pi_i(G/TOP)` is Z, 0, Z/2, 0 for i = 0, 1, 2, 3 mod 4 (i >= 1) **[classical]**. The cohomology of SU(3) lives in degrees 0, 3,
  5, 8. In the spectral sequence for `[M, G/TOP]`, the only diagonal term `H^p(M; pi_p(G/TOP))` with p > 0 is `H^8(M; Z) = Z`.
  So every normal invariant comes from the top cell: `[M, G/TOP]` is a quotient of `pi_8(G/TOP) = Z` under the collapse
  `c: M -> S^8`.
* **The gap the sketch left.** Differentials into the top term could make this a proper quotient. They cannot. The composite
  `pi_8(G/TOP) -> [M, G/TOP] -> L_8` is the isomorphism `pi_8(G/TOP) = L_8` (the surgery obstruction is additive under connected
  sum at the top cell). So `c^*` is injective, `[M, G/TOP] = Z`, and the obstruction map is injective on it.
* Hence `S^TOP(SU(3))` is one point. **Confirmed.**

### 2.2 N = 3, smooth: closed by the literature (the sketch's remainder)

**Reduction [paper, checked].** A smooth X homotopy equivalent to SU(3) is homeomorphic to it (2.1). The smooth sequence reduces
everything to the top cell in the same way: `pi_3(G/O) = pi_5(G/O) = 0`, and `pi_8(G/O) = Z + Z/2` with the Z/2 the image of
`Theta_8 = Z/2`, since `bP_9 = 0` (Kervaire-Milnor 1963, recalled) **[classical]**. So X is diffeomorphic to SU(3) or to
`SU(3) # Sigma^8`, with `Sigma^8` the exotic 8-sphere. The sketch's reduction to the inertia group is right.

**The inertia group contains `Sigma^8` [external].** Wang, Theorem 1.1(3): the smooth manifolds of this homology type are exactly
`S^3 x S^5`, `S^3 x S^5 # Sigma^8`, SU(3) and `M_{1,0}`. **SU(3) appears once, so `SU(3) # Sigma^8` is diffeomorphic to SU(3).**
Corollary 1.2(2): "A closed smooth 8-manifold M is diffeomorphic to `M_{1,0}` or SU(3) if and only if they are homotopy
equivalent." The mechanism (Proposition 5.5, Corollaries 5.6 and 5.7): SU(3) is the `S^3`-bundle over `S^5` with clutching
`i_* b eta_3 + sigma_* eta_3`, and Frank's pairing (Frank 1968) takes `(i_* b eta_3, a)` to `Sigma^8`. So the exotic sphere is
absorbed by a twist of the clutching map on the lower cells. All four clutchings in SU(3)'s orbit, with and without `Sigma^8`, give
SU(3). For `S^3 x S^5` the orbits of `0` and `Sigma^8` stay apart, so there the exotic sphere is not absorbed.

**Not settled here, and not needed:** whether the diffeomorphism `SU(3) # Sigma^8 -> SU(3)` can be chosen homotopic to the
standard homeomorphism (the *homotopy* inertia group). VI.6.3j asks only for "diffeomorphic". **[open, as far as checked]**

**Status of the N = 3 statement.** Topological and smooth: **[external]** (Wang 2021, published). It agrees with this note's own
surgery computation **[paper]**, so the citation is not taken on trust alone. Wang's Corollary 1.2(2) is stated for closed smooth
8-manifolds. A homotopy equivalence preserves dimension, so it applies directly.

### 2.3 N >= 4: confirmed, with the odd-N case completed

**Literature.** I found no paper that states this for SU(N). A negative search; Wang covers only dimension 8. The argument is a
standard surgery computation, written out in full so it can be checked **[paper]**.

* For `N >= 4`, the product `x_3 x_5` is non-zero in `H^8(M; Q)`, and `8 < n` (n is 15, 24, 35, ...).
* Rationally `[M, G/TOP] (x) Q = sum_i H^{4i}(M; Q)` (G is rationally trivial, so G/TOP is rationally BO) **[classical]**. Take
  a normal invariant x whose degree-8 rational class is non-zero. Since `H^4(M; Q) = 0`, there are no products in degree 8, so
  every rational coordinate system on G/TOP agrees in degree 8 up to a non-zero factor **[paper]**.
* **N even** (n odd): `L_n(1) = 0`, so x is realised by a homotopy equivalence `f: X -> M` **[classical]**.
* **N odd** (n = 0 mod 8): this is the step the sketch's phrase "the top part compensates the signature" left implicit. Use the
  group structure on `[M, G/TOP]` for which the surgery obstruction is a homomorphism (Ranicki 1992, recalled) **[classical]**.
  Put `y = x - c^*(theta(x))`, with c the collapse to the top cell. Then `theta(y) = 0`. And y agrees with x on `M` minus a disc,
  where all of `H^8` lives, so the degree-8 class is unchanged **[paper]**. Realise y.
* For the realising `f: X -> M`: `p_1(X) = 0` (`H^4 = 0`), and `p_2(X)` is non-zero (the L-class in degree 8 is `(7 p_2 - p_1^2)/45`).
  `M` is parallelisable, so `p(M) = 1`. A homeomorphism `X -> M` would carry `p_2(M) = 0` to `p_2(X)`, because rational
  Pontryagin classes are homeomorphism invariants (Novikov 1965) **[classical]**. So **X is not homeomorphic to SU(N)**.
  Different values of `p_2` give infinitely many such X.
* **Smooth too.** `G/O -> G/TOP` is a rational equivalence, so the same construction runs in the smooth surgery sequence, and the
  X can be taken smooth. So the statement is false in both categories. **[paper]**

### 2.4 What I confirm, and what I could not

| Part of the sketch | Verdict | Basis |
|---|---|---|
| N = 2 is Poincare (and diffeomorphic: TOP = DIFF in dimension 3, Moise) | confirmed | [classical] |
| N = 3 true topologically | **confirmed twice**: own computation with the gap filled (2.1), and Wang 2021 Thm 1.1(2), Cor 1.2(1) | [external] + [paper] |
| N = 3 smooth "depends on the inertia group" | the reduction is confirmed (2.2), and the answer is **yes**: `Sigma^8` is in the inertia group of SU(3) | [external] (Wang 2021 Thm 1.1(3), Cor 1.2(2), Cor 5.6, 5.7) |
| N >= 4 false topologically | **confirmed**; the odd-N obstruction step completed (2.3) | [paper] from [classical] theorems; no reference found that states it for SU(N) |
| N >= 4 smooth | false as well (not in the sketch) | [paper] |
| what I could not check | (a) Wang's proof in full: I read the statements and section 5, not sections 3 and 4 line by line; (b) the homotopy inertia group of SU(3); (c) a published statement for N >= 4 | |

### 2.5 Proposed replacement for row VI.6.3j (for the coordinator; not applied)

| VI.6.3j | "Poincare for SU(N)" (homotopy equivalent to SU(N) implies homeomorphic or diffeomorphic). N = 2: true (Poincare; TOP = DIFF in dimension 3). N = 3: true in both categories; every closed smooth manifold homotopy equivalent to SU(3) is diffeomorphic to it (in particular `SU(3) # Sigma^8` is diffeomorphic to SU(3)), and `S^TOP(SU(3))` is a point. N >= 4: false in both categories (`H^8(SU(N); Q) != 0` below the top degree gives infinitely many closed smooth manifolds homotopy equivalent to SU(N) with `p_2 != 0`, hence not homeomorphic to the parallelisable SU(N)) | external (N = 3); paper (N >= 4, a surgery computation from classical theorems) | Wang, Acta Math. Sinica 37 (2021) 941-956, Thm 1.1, Cor 1.2 (arXiv 1810.08478); Browder 1972; Wall 1970; Kirby-Siebenmann 1977; Novikov 1965; Ranicki 1992; `docs/unified/PERELMAN-DMP.md` 2 | none for N <= 3; for N >= 4 a published reference (optional) |

With this the class-(d) remainder "VI.6.3j, smooth N = 3" in OPEN-CLAIMS-CLOSURES section 5 closes. That leaves one fewer
genuinely open side question. VI.6.3 in Part VI ("For N >= 3 no theorem was found, it may fail in the smooth category ...") needs
the same correction. That is the coordinator's edit.

---

## 3. What a DMP-generalised Perelman adds, and what is worth writing in Lean

### 3.1 For SU(N): no new answer, one clean criterion, one falsifiability check

* **No new answer [paper].** The answer is complete and classical (section 2). A flow construction cannot improve on it. For
  N >= 4 the statement is false, so no construction can certify SU(N) from its homotopy type. For N = 3 surgery already decides
  it. And Ricci flow in dimension 8 has no catalogue (slot P2 is empty: singularities are not classified, and the symmetric SU(N),
  N >= 3, is an unstable profile, `BLOWUP.md` 7.3).
* **The "better construction" already exists, and it is surgery theory [reading].** It has the shape of section 1.5 in other
  clothes. The free possibility space is the normal invariants, which live on the cells below the top. The gate is the L-group,
  which consumes the top cell: a normal map passes (obstruction zero) or is outside. The structure set is what passes.
  **Criterion [paper, from classical surgery theory]:** for simply connected M of dimension >= 5, `S^TOP(M)` injects into
  `[M minus a disc, G/TOP]`. So M is topologically rigid **if nothing lives below the top cell**. If M is stably parallelisable
  and there is rational room below the top cell (some `H^{4i}(M; Q) != 0`, `0 < 4i < n`), M is **not** rigid. SU(3) is the first
  case and SU(N), N >= 4, the second. In DMP words **[reading]**: rigidity is an empty free possibility space under the gate, and
  the gate consumes exactly one degree of freedom (the top cell).
* **A falsifiability check [reading].** The owner expected "a better construction". The honest version of that expectation is
  testable: a construction that certified SU(N) for every N would be refuted by the N >= 4 counterexamples. DMP passes the test
  only if its construction *stops* at N = 3. Read this way, the result is a confirmation, not a defeat. The base SU(2) and its
  first extension SU(3) are rigid. From SU(4) on, the cohomology (`x_3 x_5` in degree 8) opens room below the top cell, and
  rigidity is lost.

### 3.2 For the Navier-Stokes card: the template names three missing slots [reading on classical facts]

| Slot (1.5) | Perelman | Navier-Stokes | Status for NS |
|---|---|---|---|
| P1, a scale-invariant ledger at the floor | W-entropy | none known; energy is supercritical (VI.3.4c) | [open] |
| P2, a catalogue of what reaches the boundary | kappa-solutions, classified | none; one profile is claimed for a model (Chen-Hou, Euler with boundary) | [open] |
| P3, a quantum per act with a bounded budget | volume `v(h, delta)` per surgery, at a fixed scale h | Caffarelli-Kohn-Nirenberg (1982) epsilon-regularity: a singular point costs at least epsilon of **scaled** local dissipation, i.e. about `epsilon r` of absolute dissipation at scale r. So the budget bounds the 1-dimensional parabolic measure of the singular set (zero), not the number of acts | [classical] for CKN; [reading]: the quantum shrinks with the scale, which is VI.3.4a's "a summable budget never pays a uniform positive cost" in Perelman's terms |
| P4 and the canonical continuation | extinction; Kleiner-Lott and Bamler-Kleiner: the continuation is canonical | non-uniqueness of weak continuation (VI.5.3) | [open] |

This sharpens VI.6.2's verdict ("passes as a description, not as a mechanism") into a list: NS lacks P1, P2 and a scale-free
P3, and its continuation is not canonical. Each gap is an existing open row (VI.3.4, VI.5.1, VI.5.3), so the comparison adds
precision, not a new claim. **[reading]**

### 3.3 Lean pieces worth writing (none written this round)

| Piece | What it states | Worth | Size |
|---|---|---|---|
| L1 `acts_le_of_accrue` | from `Accrues G c 0 n`, `c_i >= q > 0`, `G 0 >= 0` and `G n <= B`: `n <= B / q`. Perelman's surgery count as a corollary of `accrue` (slot P3) | yes: it puts Perelman's finiteness on the Lean side of the settle edge, next to `balanceBound` | ~20 lines |
| L2 `reconstruct_of_typed_excision` | a run whose acts split `x = y * z` with z in a catalogue C (in a monoid), ending at 1, gives x in the submonoid generated by C; with a predicate "trivial" that splits over products, "x trivial implies every piece trivial" (the abstract Poincare step) | yes: it is the form-layer content of section 1.5 and makes "typed excision vs R136a1" precise | ~60 lines |
| L3 SU(N) degree arithmetic | `decide`: degrees of `Lambda(x_3, x_5)` avoid 2 and 4 and 6 below 8; for N >= 4, `3 + 5 = 8 < N^2 - 1` | small; records the one arithmetic input of the criterion | ~15 lines |
| not worth it | surgery theory itself (L-groups, `G/TOP`, the exact sequence), Ricci flow, Wang's computation | none of it is in Mathlib; years of work, and the facts are classical | |

My recommendation: L1 and L2 together, as one small module under `Unified/` (for example `Unified/TypedExcision.lean`). They are
the honest form-layer part of "generalising Perelman for DMP". Every geometric input stays a named hypothesis, never an axiom.

---

## Sources

* G. Perelman, arXiv math/0211159 (2002), math/0303109 (2003a), math/0307245 (2003b) (recalled); Kleiner-Lott, *Geom. Topol.*
  12 (2008); Morgan-Tian, *Ricci Flow and the Poincare Conjecture* (2007); Colding-Minicozzi, *J. Amer. Math. Soc.* 18 (2005);
  Bamler-Kleiner, arXiv 1709.04122 (all recalled).
* X. Wang, "On 1-connected 8-manifolds with the same homology as `S^3 x S^5`", *Acta Math. Sinica (Engl. Ser.)* 37 (2021),
  941-956, doi 10.1007/s10114-021-0194-z; arXiv 1810.08478 (Theorem 1.1, Corollary 1.2, Proposition 5.5, Corollaries 5.6 and 5.7
  read this round).
* D. L. Frank, "An invariant for almost-closed manifolds", *Bull. AMS* 74 (1968), 562-567 (cited by Wang; not read).
* W. Browder, *Surgery on Simply-Connected Manifolds* (1972); C. T. C. Wall, *Surgery on Compact Manifolds* (1970);
  Kirby-Siebenmann, *Foundational Essays* (1977); S. P. Novikov, topological invariance of rational Pontryagin classes (1965);
  A. Ranicki, *Algebraic L-theory and Topological Manifolds* (1992); Kervaire-Milnor, *Ann. of Math.* 77 (1963) (all recalled).
* Rubinstein (1995), Thompson, *Math. Res. Lett.* (1994), Schleimer (2011) on `S^3` recognition; Volodin-Kuznetsov-Fomenko (1974)
  for Novikov's undecidability; B. Poonen, "Undecidable problems: a sampler", arXiv 1204.0299; A. Nabutovsky, S. Weinberger,
  "Algorithmic aspects of homeomorphism problems", arXiv math/9707232 (abstract read); arXiv 1508.06720 (3-manifold homeomorphism
  after geometrisation).
* L. Caffarelli, R. Kohn, L. Nirenberg, *Comm. Pure Appl. Math.* 35 (1982) (recalled).
