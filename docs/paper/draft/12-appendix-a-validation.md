# Appendix A. Validation: Poincare, SU(N) and the rigid groups

*Draft 4. Claim labels A.n are listed in `../CLAIMS.md`.*

## A.0 Poincare (Perelman), and SU(N)

**Purpose.** Check the restatement of VI.3.5 against a solved, accepted proof in which finite-time singularities occur, are
classified, and are cut at a boundary, after which the flow continues. **This box claims nothing new.** Everything in A.1 and
A.2 is **[classical]** (recalled from Perelman's three papers and the expositions; not re-checked for this draft), except the
fitting of the DMP vocabulary, which is **[reading]**.

## A.1 The proof as a ledger

On a closed 3-manifold Ricci flow can develop singularities in finite time (Hamilton). In one case the time is forced by a comparison:
`dR/dt >= Delta R + (2/3) R^2` gives, for positive scalar curvature, a singularity by `T <= 3/(2 R_min(0))` **[classical]**.

| Ledger element | Perelman | Fit |
|---|---|---|
| steps | the smooth flow between surgery times | yes |
| monotone quantity | the W-entropy, non-decreasing; its derivative is a sum of squares vanishing on shrinking solitons | partly: increments `>= 0`, floor 0, but **no uniform positive cost** |
| what it buys | kappa-noncollapsing at every scale: one estimate at all scales, from a scale-invariant quantity | yes: the "one scale suffices" of Chen-Hou |
| number of steps on `[0, T]` | each surgery removes at least a definite volume; volume is bounded: finitely many surgeries | yes: a quantum per step |
| what reaches the boundary | kappa-solutions, classified in 3D; canonical neighbourhoods | partly: a classification, not a certified damping |
| the boundary (DB) | a singular time | yes |
| the act at the boundary | surgery: cut along necks, glue caps, discard known pieces, restart | yes, and stronger: the act is defined |
| the end | finite extinction for simply connected manifolds (Perelman; Colding-Minicozzi) | yes: the last boundary, where the certificate is read |

**Why surgery is a well-defined act, and why extinction certifies the sphere.** The cut runs through a nearly round 2-sphere in a
neck, so each surgery is a connected-sum decomposition plus discarded pieces of known type. Later, singular Ricci flows through the
singularities were constructed as limits of Ricci flows with surgery (Kleiner-Lott) and proved unique and stable (Bamler-Kleiner): for Ricci flow in 3D
"the equation selects the continuation" is a theorem. For simply connected `M`, running the surgeries backwards writes `M` as a
connected sum of 3-spheres, which is the 3-sphere.

## A.2 Verdict **[reading]**

The restatement passes as a **description**: every element of VI.3.5 has an exact counterpart in Perelman's proof (forced time, one
scale-invariant estimate, a defined act at a boundary, a quantum per act, a final certificate). It does **not** pass as a
**mechanism**: what reaches Perelman's boundaries is decided by classifying all blowup shapes, not by a cost above a floor; the
monotone quantity buys a sign, not a rate; and Ricci flow passes a sequence of boundaries and continues, while the Chen-Hou time `T*`
is terminal. Nothing new is claimed.

## A.3 Poincare and SU(N)

The first author asked whether Perelman's Poincare extends to every SU(N) through DMP. The exact answer, by what holds:

* **SU(2) is the 3-sphere.** The unit sphere of `C^2` is in bijection with SU(2) **[Lean]** (`Unified/BlowupSUN.lean`:
  `su2Mat_mem`, `su2_form`, `sphereEquivSU2`); that the bijection is a diffeomorphism is **[classical]**. So the object Perelman
  certified is the group manifold of SU(2).
* **Every SU(N), with its bi-invariant metric, shrinks to a point at time `1/N`**, with no surgery: `g(t) = (1 - N t) g(0)`, with
  `Ric = (N/2) g` in the normalisation `<X, Y> = -tr(XY)`. The ODE is **[Lean]** (`shrink_hasDerivAt`, `shrink_unique`,
  `shrink_pos`, `shrink_extinct`, `einstein_hasDerivAt`, `einstein_unbounded`, `sun_extinction`); the curvature constant is
  **[classical]** and checked **[numerical]** for N = 2, 3, 5, 11 (`blowup_sun_check.log`). This is Perelman's final event delivered
  by symmetry. **It carries no topological information**, because every positive Einstein manifold shrinks the same way.
* **Only SU(2) is stable.** Positive-Ricci metrics on a closed 3-manifold flow to constant curvature (Hamilton) **[classical]**. For
  every `N >= 3`, the first Laplace eigenvalue `N - 1/N` lies strictly inside the Cao-He conformal instability window, and for
  `N = 2` it sits exactly on the lower edge (Obata's case). The inequalities for the number `N - 1/N` are **[Lean]** (`sun_window`, `su2_window_edge`); that `N - 1/N` is the first Laplace eigenvalue (the Casimir of the fundamental representation) is **[classical]**. That the window implies
  instability is **[external]** (Cao-He; Kroencke).
* **A genuine "Poincare for SU(N)"** (every closed manifold homotopy equivalent to SU(N) is homeomorphic or diffeomorphic to it) is a
  surgery-theory question. It is answered for `N = 3` (published) and for even `N >= 4` (a surgery computation here); odd `N >= 5` is
  open. For `N = 2` it is Poincare **[classical]**. For `N = 3` it holds in both categories:
  every closed smooth manifold homotopy equivalent to SU(3) is diffeomorphic to it, `SU(3) # Sigma^8` included **[external]**
  (X. Wang, arXiv 1810.08478, Theorem 1.1 and Corollary 1.2). For even `N >= 4` it fails in both categories: there is rational room below
  the top cell (`x_3 x_5` in degree 8), so surgery gives closed smooth manifolds homotopy equivalent to SU(N) with a non-zero
  Pontryagin class, not homeomorphic to the parallelisable SU(N) **[paper]** (a computation from classical surgery theory,
  `docs/unified/PERELMAN-DMP.md` 2). The sketch is complete for even N, where N^2 - 1 is odd and the surgery obstruction group
  vanishes; for odd N the dimension N^2 - 1 is divisible by 8, the obstruction lies in L = Z, and it still has to be shown to vanish
  for the chosen normal invariant, or be killed by another class **[open]** for odd N >= 5. Ricci flow does not reach it. In DMP terms the rigid cases are those with nothing below the gate
  (the top cell), and a construction that certified every SU(N) would be refuted at N = 4 **[reading]**.
* **The rigid SU(N).** With the point SU(1), the SU(N) whose homotopy type determines them include N = 1, 2, 3 and exclude every even
  N >= 4; odd N >= 5 is open (the bullet above),
  and the circle U(1) is rigid too **[paper]** (from the bullet above; S^1 **[classical]**) (A.3k). The rigid factors are
  U(1), SU(2) and SU(3), the Standard Model's. The first author reads this as the start `{infinity, 2, 3}`: the largest start built from
  SU(N) that a description can still certify (Part X 4.4) **[reading]**.

## A.4 The Navier-Stokes statement, side by side **[reading]**

| | Perelman | Chen-Hou | Navier-Stokes (claimed route I) |
|---|---|---|---|
| why one estimate covers all scales | scale-invariant entropy | scale invariance of the equation | scale invariance; the zoomed equation is autonomous |
| what reaches the boundary | a classified catalogue | one certified profile | one certified profile, if the certificate holds |
| the act at the boundary | defined, then canonical | open | open |
| status | accepted proof | accepted, with a wall | claimed, certificate unreleased |

## A.5 The rigid groups, the U(1) gate and its two witnesses

**The results of this section, first.** The bullets below interleave results and the first author's readings; these are the
results, each with its status.

1. Sp(2) = Spin(5) is strongly topologically rigid: its topological structure set is a point, so every homotopy equivalence from a
   closed topological manifold to Sp(2) is homotopic to a homeomorphism **[paper]** (a surgery computation from classical theorems,
   independently read; `docs/unified/G2-SP2-RIGIDITY.md` 1; claim A.5j).
2. G2's topological structure set has exactly two elements; the second is carried by the class x_3^2 in degree 6, pulled back from
   S^6 = G2/SU(3), and no characteristic class tells it from G2 **[paper]** (claim A.5p).
3. Whether that second element is G2 itself, seen through a self-equivalence of G2, is **[open]**, reduced to one test (claim A.5r).
4. In Lean, a manifold's rigidity box is DMP-complete exactly when it is rigid (II.4d), and G2 is rigid if its box shares the gate
   with a certified box; that sharing is at least as strong as the rigidity it concludes, so this restates the question and is not
   evidence for its answer **[Lean]** (`ETM/G2Rigidity.lean`, `g2_rigid_of_one_assumption`; claim A.5u).

* **The Standard Model's factors are the rigid ones.** Among U(1) and the SU(N), the groups determined by their homotopy type
  include U(1), SU(2) and SU(3) and no even SU(N) with N >= 4; odd N >= 5 is open **[paper]** (from A.3j, A.3k) (A.5i). The first author reads the selection as rotation: other
  compact groups do not survive it, and SU(N) is the language the encoder speaks (Part X 4.4). It would be a DMP-flavoured
  consequence beyond the standard expectation (compare IX.5e: no DMP theorem selects Z_6 or the hypercharges) once the other groups are settled; for now it is a reading. The rigidity of
  Sp(2) = Spin(5) is **[paper]** (A.5j: strongly rigid, topologically) and of G2 is **[open]** (A.5r), but by the next bullet neither decides anything.
* **Only U(1) carries content across the gate.** The first author's reading: the survivors carry nothing across the gate; only U(1) does,
  so only it certifies. Exact counterpart: content crosses as a phase with a direction, in a representation that is not its own
  conjugate. Among compact simple groups such representations exist exactly for SU(N), N >= 3, Spin(4k+2) and E6; G2, Sp(n),
  Spin(2n+1) and SU(2) have only self-conjugate ones, and U(1) has the charges **[classical]** (A.5k). So Sp(2) and G2 carry no
  oriented phase, rigid or not. Among the groups that can, rigidity leaves only SU(3): SU(N), N >= 4, fails, and Spin(4k+2),
  k >= 2, and E6 have the same rational room below the top **[paper]** (rational test; the surgery step not written out for
  them) (A.5l). A non-abelian factor carries the phase only through its centre on the U(1) circle, Z_2 for SU(2) and Z_3 for
  SU(3), glued to hypercharge as Z_6 **[reading]** (A.5m); that the Standard Model's trivially acting centre is Z_6 is **[Lean]** (IX.3). In the first author's words, only U(1) certifies; the factors certify through it
  **[reading]** (A.5m). Care point: "carries content" is identified with "has a complex representation", and that identification
  is the reading.
* **The two hidden witnesses.** The first author's reading: the two that do not carry, Sp(2) and G2, are dimensionless for
  DMP-completeness, and they are the two witnesses the U(1) gate needs to certify. It checks that the constants resolve to 1,
  certifies and transports the content, and keeps its witnesses hidden, which it can because they are dimensionless to the
  encoder. Exact counterparts: the simply connected compact simple groups of rank 2 are exactly SU(3), Sp(2) = Spin(5) and G2 **[classical]**
  (A.5n), so SU(3) with its two witnesses is the whole of rank 2. The encoder tells a phase from its conjugate; Sp(2) and G2 have
  only self-conjugate representations and their centres lie on the real points {+1, -1} of the circle **[classical]**, so the
  encoder reads no orientation from them. The check "resolves to 1" has the encoder's root as its counterpart: the norm read from both sides agreeing, the field
  `root : ‖psi'‖ = ‖psi‖` of the encoder structure **[Lean]** (`Encoder.root`; equality of the two norms, a datum of an encoder, not "= 1"). The witness role is a **[reading]** (A.5o). It needs both witnesses rigid, which makes it
  falsifiable. Sp(2) passes in the strong form: its topological structure set is a point, so every homotopy equivalence to it from a closed topological manifold is homotopic to a
  homeomorphism (its cells sit in dimensions 3 and 7, where G/TOP has no homotopy, and the top cell is the Kervaire invariant)
  **[paper]** (A.5j, independently read). G2 is not strongly rigid: its topological structure set has exactly two elements, the second carried
  by the class x_3^2 in degree 6, pulled back from S^6 = G2/SU(3), and no characteristic class tells the fake from G2 **[paper]**
  (A.5p). Whether the fake is G2 itself, seen through a self-equivalence of G2, is **[open]**, reduced to one test (A.5r). The first author reads the fake G2 as cancelled by the reflection
  positivity of the start: the room is the class x_3^2 in degree 6, its square x_3^4 vanishes **[classical]**, and in reflection
  positivity a state with vanishing reflected square is null. Care point: a Z/2 class has no sign and the cup square is not the
  reflection form, so this is a **[reading]** (A.5q). Its mathematical counterpart is exact: "cancelled" means absorbed by a
  self-equivalence of G2, which is the test of A.5r; the reading predicts that it exists. The test has one live candidate, a map that runs through SU(3), the
  confined fibre of G2 -> S^6, whose top cell opens onto G2's 8-cell **[classical]**; it carries the fake's class exactly when what
  crosses that channel is an odd multiple of nu, squared to nu^2 **[sketch]**. The first author reads this as a confined CMOS that needs its
  interface channel open, with the square folding in through reflection positivity, which predicts "odd" **[reading]** (A.5s). The
  first author goes one step further: since the DB can be drawn freely, whatever can be placed through the gate can be certified, so the
  channel goes back into O1, the one assumption (X.68a, the scale certificate, **[Lean]** from it) **[reading]** (A.5t). Care
  point: G2's rigidity is a finite computation, true or false whatever is assumed, so the assumption cannot decide it; the reading
  predicts its answer, and the computation tests both the prediction and how far "placed, hence certified" reaches. In the
  first author's words, the one assumption predicts and certifies that the G2 channel exists as a DMP-complete state, which is O1 read as
  constructability. This is a theorem one layer down. IM's rigidity box is DMP-complete exactly when the manifold is rigid
  (II.4d); applied to G2, G2 is rigid exactly when its box is DMP-complete, and G2 is rigid if its box shares the gate with the
  certified one box **[Lean]**, from one named External slot (the surgery input, which Mathlib cannot state: the published Kreck-Lueck criterion together with this paper's own two-element structure set A.5p, which is **[paper]**), the one assumption as
  a named OpenStep, and the certified one box as a plain hypothesis (A.5u, A.5v; `ETM/G2Rigidity.lean`, `g2_rigid_of_one_assumption`). The sharing is at least as strong as the rigidity it concludes, so this is a reformulation of the question, not evidence for its answer. The corollary is the next layer's named
  hypothesis, never a Lean axiom, and the linter lists it. A computation showing G2 not rigid would refute the sharing for G2
  **[Lean]** (`g2_not_shared_of_not_rigid`); G2's unconditional rigidity stays **[open]** (A.5r). The first author reads the missing
  sign itself as the point: Z/2 carries no order, so no floor, so no decidable reading, and only a start that forces one is
  DMP-complete (Part X 4.3, X.70).
