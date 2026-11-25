# Part II. The machine, and the tools the problems use

*Draft 6, 2026-11-25 (machine-first). Section A is the machine, in the order a reader needs it: running systems and the ledger, the encoder, the settle theorem, the one-box test, the API, the arsenal, the independent re-check. Section B is the tools the problems use, each once in its most general form. Lean paths are relative to `docs/mass-gap/formal/ProofPhase/`; claim labels (II.n.m) are listed in `../CLAIMS.md`.*

**Where to start.** Part II has one statement at its centre, II.4.1: each problem is restated as one statement checked at every
step, exactly equivalent to it, and a proof is an induction, base case and inductive step. A reader who wants the headline first can read
II.4 and II.4.1, then II.2.7 (the full turn, which reads gates), and come back to the machine (II.0 to II.3) and the tools (II.8 to
II.15) as the parts call on them.

**Which part uses which tool.** The machine (II.0 to II.3) is used by Parts III to VII; the one-box test and the cards (II.4,
II.5) by every part from III to IX and by Appendix A; the arsenal and the re-check (II.6, II.7) by every Lean result; the tools of
section B (II.8 to II.15) by Parts III to V, each of which names the section it uses.

| Section | III Yang-Mills | IV GRH | V P vs NP | VI Navier-Stokes | VII BSD | VIII Hodge | IX GU | App. A |
|---|---|---|---|---|---|---|---|---|
| II.0 to II.3, the machine | yes | yes | yes | yes | yes | | | |
| II.4, II.5, the test and the cards | yes | yes | yes | yes | yes | yes | yes | yes |
| II.6, II.7, arsenal and re-check | yes | yes | yes | yes | yes | yes | yes | yes |
| II.8 to II.15, the tools | yes | yes | yes | | | | | |

**A. The machine.**

## II.0 The machine in ordinary terms: multiplication by complex numbers

**The translation.** In ordinary terms the machine is multiplication by complex numbers. Each step multiplies the carried amplitude
by one number c with |c| <= 1: its modulus is the gate factor (the ledger cost is its minus log), its phase the rotation. A run
multiplies its steps, so moduli multiply and phases add. If every |c| stays at or below some theta < 1, the run settles within an
explicit number of steps. If every |c| = 1 (pure rotation), the number never changes the mass, and a run of such multipliers is
decided by one comparison. The universal machine is a different running system that also has gate factor 1 everywhere, and for it
whether it settles cannot be decided (II.3). Everything else in this part (the ledger, the encoder, the settle theorem, the
one-box test) is a detail of this one picture.

**In Lean** (`ETM/Complex.lean`, `complex_translation`):

* a sequence of multipliers of modulus at most one is a running system whose ledger law holds with equality, and its run is the
  product of its steps (`cmach`, `cmach_pays_eq`, `cmach_iterate`, `cmach_mass_eq`) **[Lean]** (claim II.0a);
* every running system is dominated by the product of its own factors, read as complex numbers (`dominated`), so the translation
  loses nothing on the cost side **[Lean]** (claim II.0b);
* below the circle the run settles (`cmach_reaches`, from the settle theorem of II.3); on the circle the mass never changes
  (`cmach_lossless`), and every factor of the universal machine is 1 (`etm_fac_one`) **[Lean]** (claim II.0c);
* the encoder's reflection coefficients (II.2) are such multipliers, with gate factor |c|, the Szego factor 1 - |c|^2 of the same
  encoder being a different quantity (`encMach`, `encMach_fac`) **[Lean]** (claim II.0d);
* a link between two nodes keeps the step, the gate factor and the mass; multiplying every amplitude by a unit number is such a
  link, and a complex-linear map of the line that keeps every norm is multiplication by a unit number, so among linear links that
  keep identity only rotation links (`rotHom`, `rot_of_isometry`) **[Lean]** (claim II.0f);
* on the reals the circle is the two points 1 and -1: a real-linear map of the line that keeps every norm is multiplication by 1 or
  -1, the identity or the half-turn, and every real number is its modulus times 1 or -1, so ordinary multiplication is a gate factor (a size) times
  an identity-keeping multiplication (`rot_of_isometry_real`, `real_eq_sign_mul_abs`) **[Lean]** (claim II.0g).

**Decidable over every truly possible state.** The first author's reformulation: a DMP-complete state needs decidability for every truly
possible state, with the least possible options given by y^k **[reading]** (claim II.0h). Each part has an exact counterpart.
With a floor, settling is decided within an explicit bound; at the floor the universal machine is undecidable (II.3) **[Lean]**. The
truly possible paths after k steps grow like y^k, and the least such rate is the connective constant mu of self-avoiding walks
**[classical]** (Hammersley and Morton, J. Roy. Statist. Soc. B 16 (1954) 23-38; the statement used is the existence of the limit of
c_n^(1/n), which follows from c_(n+m) <= c_n c_m by Fekete's lemma; the page of that paper has not been read for this). The run over
all of them settles when the cost per step beats the options: the multiplied path sum mu^k e^(-F k) decays when F > log mu, and the
joint form with the excess act gives both criteria **[Lean]** (model; `joint_gives_both`). For Yang-Mills that is the path-counting number
F_e(L) - 2c(L) > log mu_4, a sufficient route to O1 (Part III). Reading: the reformulation is the general form of the one assumption's decay edge, read in
the language of options **[reading]**.

**Care point.** The translation is exact for the cost and the rotation. The content a step carries, the program the universal
machine runs, lives in the state and not in the number; that is where its undecidability sits (II.3) **[paper]** (claim II.0e). In
number theory "complex multiplication" names something else (elliptic curves with extra symmetries, near Part VII); here it is
always "multiplication by complex numbers".

### II.0.1 The complex-number ruleset

Nine rules carry the complex-number steps of the paper; the rest rests on the tools of Part II B (positivity, reconstruction, the
spectral theorem, contraction) and on the undecidability of II.3. Each rule is stated once here with a small example and where the
paper uses it, so that a reader who knows them reads "turn", "phase", "cost" and "half-turn" everywhere in the same sense (claim II.0i).

**The words.** A complex number $z = r e^{i\theta}$ has a *size* $r = \lvert z \rvert$, which the machine calls the *gate factor*, and an
*angle* or *phase* $\theta$. The *cost* of a step is minus the log of its size, $-\log r$; the ledger adds the floor $\delta$ to it
(II.1). A *turn* is a multiplication by $e^{i\theta}$; a *half-turn* is a multiplication by $-1 = e^{i\pi}$; a *full turn* is
$e^{2\pi i} = 1$. The turn in $N$ equal steps is $\zeta = e^{2\pi i/N}$, a primitive $N$-th root of unity: $\zeta^N = 1$ and no smaller
power is 1.

| Rule | Statement | Small example | Used in |
|---|---|---|---|
| C1 Multiplying is scaling times turning | for $z = r e^{i\theta}$ and $w = s e^{i\varphi}$ the product $z w$ has size $r s$ and angle $\theta + \varphi$: sizes multiply, angles add | $i \cdot i = -1$: two quarter-turns make a half-turn | II.0, every running system |
| C2 The cost is minus the log of the size | for $0 < \lvert z \rvert \le 1$ the cost $-\log \lvert z \rvert \ge 0$; sizes multiply along a run (C1), so costs add | size 1/2 costs log 2 a step; ten steps cost 10 log 2 | the ledger II.1, settling II.3, the free energies of III.3 |
| C3 Rotations add | $e^{ia} e^{ib} = e^{i(a+b)}$; on $N$ steps $\zeta^a \zeta^b = \zeta^{(a+b) \bmod N}$ | ROT13 twice is a rotation by 26, the identity; by 14 twice leaves 2 | T.5, II.2.8 |
| C4 A full turn averages to one exact value | for $\zeta = e^{2\pi i/N}$, $\frac1N \sum_{j<N} \zeta^{jk}$ is 1 when $N$ divides $k$ and 0 otherwise | the four quarter-turns $1 + i - 1 - i = 0$ | II.2.7 |
| C5 The mirror pairs the halves | $\overline{e^{i\theta}} = e^{-i\theta}$; for a function holomorphic near the circle with $f(\bar z) = \overline{f(z)}$ (real on the real axis) the $+$ half of a turn mirrors the $-$ half, and the result is real | $\cos\theta = (e^{i\theta} + e^{-i\theta})/2$ | II.2.7, the electric sectors of III.3.1c |
| C6 The turn back is the inverse turn | for $p(z) = \sum_{m<N} c_m z^m$, the average $\frac1N \sum_{j<N} p(\zeta^j)\, \zeta^{-jk}$ is $c_k$ | the full turn decodes its $N$ coefficients | II.2.8, III.3.1c |
| C7 The logarithm turns products into sums | $\log(xy) = \log x + \log y$, $\log x^k = k \log x$ for $x, y > 0$; for complex $z \ne 0$, $\log z = \log\lvert z\rvert + i \arg z$, so a product of steps becomes minus a sum of costs (real part) plus a sum of turns (imaginary part) | $\mu^k$ paths against $e^{-kF}$ cost: the series converges when $F > \log\mu$ | II.0 (decidability), III.5.4, R.7c |
| C8 Size-keeping maps are reversible | a complex-linear map of the line keeping every size is a unit multiplication; in more dimensions the size-keeping linear maps are the unitary ones, and on bits read as reals a reversible computation permutes the corner points, a unitary (permutation) matrix | ROT13 permutes the letters; a hash is not a permutation | II.0f, II.4.1, II.2.8 |
| C9 One turn around a point counts what is inside | one turn reads off a Taylor coefficient, $1/n!$, the order of a zero (a winding number), a leading coefficient | $1/n!$ is one turn of $e^z z^{-n-1}$ around 0 | II.2.7, IV.1.5c, VII.3.5f |

C7 in its complex form joins C1, C2 and C3: every multiplicative step of the real picture with a nonzero size becomes an additive one
in the complex picture, minus the costs adding in the real part and the turns in the imaginary part. Its one ambiguity is a whole number
of full turns: the complex logarithm is defined up to adding a multiple of $2\pi i$, which is why C4 and C9 read off exact values from
one turn. The first author reads this as being able
to simplify away the multiplicative steps of real mathematics into additive complex ones **[reading]** (claim II.0i).

**A run in polar form.** Three steps $z_1 = z_2 = \frac12 e^{i\pi/2}$ and $z_3 = \frac12 e^{i\pi}$. The run is their product: sizes
multiply to $1/8$ (C1), so the cost is $3 \log 2$, three steps of $\log 2$ (C2); angles add to $\pi/2 + \pi/2 + \pi = 2\pi$ (C3), one full
turn, so the product is the real number $1/8$. In logarithms the whole run is one sum, $-3\log 2 + 2\pi i$ (C7), and the $2\pi i$ is the
full turn that the product does not see.

**The encoder is the case N = 2.** With $\zeta = -1$ the two averages of C6 are the even part $(\psi + \psi')/2$ and the odd part
$(\psi - \psi')/2$, the mirror of C5; their ratio is the electric factor of II.2.2 (II.2.7).

**Where the rules stop.** Size 0 has no logarithm and no cost; $\arg z$ needs a choice of branch (C7); C5 and C9 need holomorphic
functions; C8's unit multiplication is for the line, unitary maps in more dimensions.

C1 to C9 are **[classical]**; their forms used in the proofs are **[Lean]**: C1 in `ETM/Complex.lean` (sizes multiply along a run,
`cmach_mass_eq`, II.0 above), C2 in the ledger of II.1, C3 as an instance in `rot_add` (on the string of Appendix T), C4, C6 and C9 in
IM's `Arsenal/FullTurn.lean`, C8 for the line in `rot_of_isometry` (II.0 above).

### II.0.2 The explanation mechanism: a k by k table of proofs

*New in Draft 6.* A system is k parts. Its table has one row and one column per part, and the cell of a row and a column says whether
the row proves the column: `+` where the row uses the column and the proof is there, `-` where it uses it and the proof fails, `·`
where no proof relates the two (in Lean, a table of uses U and one of proofs P: `·` is "not U", `-` is "U and not P"). A part's own
cell is a use when the part is current, since its own round trip runs; an earlier version is frozen and not run again, so its own
cell is `·`. The first author takes this table as DMP's explanation mechanism: what DMP establishes is explained by the cells that
prove it, an explanation is a chain of `+` cells from what is established to what is claimed, and a derived cell explains, it does not
prove **[reading]** (claim II.0.2b). Draft 6 uses it to explain what Draft 5 establishes and adds no mathematical claim; its new
measurements are of the tools (Appendix E).

**The `·` cells and the `.` boundary.** `.` is IM's operator of inclusion (R.10a). The first author: since no proof relates two such
parts, they either do not exist at the same time, or both exist and reflect positively, so the `.` inclusion boundary of a DAG fits
**[reading]** (claim II.0.2c). Exactly: let a cell need its proof where the row uses the column and reflect positively everywhere else;
then every cell is `+` exactly when every used cell is proven (`allPlus_eff_iff`), and when every use points to an earlier part no
diagonal cell appears after any number of derivation steps (`derive_irrefl`) **[Lean]** (IM, `arsenal/core/ArsenalCore/Matrix.lean`, on Lean's kernel alone).

**What the table can do (claim II.0.2a).** Each item is a theorem of the same file **[Lean]**:

* **Extensibility.** A table for k parts is also one for k + 1, since a part is added by naming one more index. k + 1 parts are all
  `+` exactly when the first k are and the new part's row, its column and its own cell are (`allPlus_succ_iff`), so nothing already
  proven is checked again; the count of new cells, 2k + 1, is arithmetic (`new_cells`).
* **Derivation.** Composing two tables, the row proving a part that proves the column, is the product of Boolean matrices; its
  iteration covers the transitive closure, which Warshall's algorithm computes **[classical]** (Warshall 1962). The Lean iterates
  "the table, or the table composed with itself", which after n steps covers chains of up to 2^n links; it does not prove that the
  closure is reached. Every chain gives a derived cell, and every derived cell is reached by a chain of cells of the table, after any
  number of steps (`comp_of_chain`, `step_sound`, `derive_sound`).
* **What a step adds.** On an all-`+` table a step adds nothing (`step_eq_of_allPlus`); on any table it adds a cell only along a chain
  of cells already there (`derive_sound`). In Lean a derived cell is a `+` like any other; that it explains and does not prove is the
  reading above.

Appendix E applies the mechanism to what Draft 5 measured.

### II.0.3 The optimizer: the mirror of the table

*New in Draft 6.* The explanation mechanism builds up: a part is added, a cell is derived. The optimizer is its mirror: it removes every
use that the table already includes through another chain. For each use the question `?` is asked, is this use needed, and `.`
answers it: the use is redundant exactly when the row uses another part that already reaches the column. Removing the redundant uses
is the transitive reduction of a DAG **[classical]** (Aho-Garey-Ullman 1972). What remains is the shortest form: each part says only
what it includes directly, and each chain of kept uses ends in a part that includes nothing, written `!`. In the Lean a DAG is a
table whose parts are numbered so that every use points to an earlier part (`Earlier`); every DAG can be numbered so, so the general
facts below hold for every DAG up to renumbering. The first author: this makes
DMP.Arsenal the self-similarity that enables positive constructability; the optimizer is the Arsenal's mirror and is constructed in
parallel with it, `?` first asserted and then negatively proven with `.`, which shows each part as the shortest sentence of the form
`DMP.{thing}!`, where the thing can be nothing **[reading]** (claim II.0.3b).

**What is proved (claim II.0.3a).** In Lean on the kernel alone (IM, `arsenal/core/ArsenalCore/Optimizer.lean`) **[Lean]**:

* **It keeps every derivation.** On a DAG the reduction reaches exactly what the table reaches (`close_reduce`), so every chain, and
  with it every explanation of II.0.2, survives.
* **Optimizing once settles**, on a DAG. A table is *settled* when optimizing it changes nothing, the compiled form and the
  optimized one being the same. The reduction of a DAG is settled (`reduce_settled`), so optimizing twice is optimizing once
  (`reduce_idem`).
* **Nothing more can go.** Removing any kept use loses a derivation (`reduce_minimal`).
* **One settled form.** Two settled DAGs that reach the same parts are the same table (`settled_unique`), so the reduction is the only
  settled table with the original's reach (`reduce_unique`). This is the uniqueness theorem of Aho, Garey and Ullman for DAGs, proved
  here on the kernel alone.
* **It needs the DAG.** On a cycle each use can be redundant through the other, and the optimizer loses what both reached
  (`repos_reduce_loses_dmp`, E.10).

**Existence as settledness (claim II.0.3c).** The first author: once a DAG compiles it is optimized, and only when both settings are
exactly the same does the setting, and thus the system, exist; the optimization runs along the lowest possible step count, which forces
reflection positivity and so transfers meaning **[reading]**. Exact parts: "both settings the same" is `Settled`, reached by one
optimization of a DAG **[Lean]**; "lowest step count" is the fewest uses, since the transitive reduction has the fewest uses of all
tables with the same reach **[classical]** (Aho-Garey-Ullman 1972; the Lean proves that no kept use can go and that the settled form is
unique, not this count), and it is not the shortest chain between two parts (a kept chain can be long); and "transfers meaning" has
as its exact part that every derivation survives the reduction (`close_reduce`) **[Lean]**. Reflection positivity is a property of forms (II.9), which a table of uses does not contain, so that part stays the
reading. `tools/rebuild matrix --optimize` runs the optimizer on the measured versions (E.9).

### II.0.4 The possibility space

*New in Draft 6.* The first author's first subtitle for Draft 6 was *the Possibility Space*, now the theme of this section (the
subtitle is now *the ETM as the ODP running DMP*, II.0.5), and the first author remarks that the Possibility Space lines up with a
base dimensionality of 6 **[reading]**. No exact counterpart is given for that remark; the paper's one six-dimensional space
is the six-sphere G2/SU(3) of R.7b, and a relation between the two is not claimed. Its theme is a reading of what a question is. It is given here with the exact parts it
rests on, and the steps that do not follow as stated are named.

**A question, its answer and the right angle (claim II.0.4b).** The first author: a question can be shown to be a point by its
definiteness, with the answer a line through it that gives it no other value than `+`, while giving meaning to its existence. It is
always a line, never a vector: an answer that said how much a question is correct would twist truth into a diluted, self-contradicting
truthiness. So between the two points, yes `+` and no `-`, there is a line whose `+` side alone carries meaning. A feature that
defines existence is an eigenvalue, so a question is an eigenvalue between two states. In a quadrant map of width `+-`, read 1 to 4
as `.`, `r`, `.`, `?`, the two points sit in the middle of quadrants 1 and 3, connected by a right angle. Through DMP this is the
universally answerable question "Is there a right angle?", and the direction of the link, from the possibility of constructing the
question to the minting of the certificate of its existence, is the force that establishes the Real Space **[reading]**. Exact parts:

* **A yes/no question is a projector**, an operator `P` with `P P = P`, whose only answers are 1 and 0 **[classical]**
  (Birkhoff-von Neumann 1936; Mackey 1963 calls these projectors questions). In Lean, a number equal to its own square is 0 or 1
  (`answers_of_idem`), and the projector onto an axis answers 1 on its line and 0 across it (`proj_answers`) **[Lean]**. That only the
  `+` side carries meaning has its counterpart in IM, where a refusal is not a state (R.9a) **[reading]**; as physics it does not
  hold, since the answer-0 side of a projector holds states as good as the answer-1 side. Care: the question is the projector and its eigenvalues are its
  answers, so "the question is an eigenvalue" reads the projector by its answers.
* **"A line, never a vector" is a ray**: a physical state is a direction with no length or phase of its own **[classical]**. The right
  angle `r` acts on lines, since it commutes with every scaling (`r_smul`) **[Lean]**.
* **`r` is multiplication by `i`**, the quarter turn `(x, y) -> (-y, x)`: a right angle (`dot_r`) of the same length (`norm_r`), twice
  the flip from `+` to `-` (`r_r`), four times nothing (`r_four`). "Is there a right angle?" is answered yes for every point, the
  witness being `r` itself (`right_angle_exists`) **[Lean]**.
* **The sector map.** One `r` goes from quadrant 1 to quadrant 2 and a second one to quadrant 3 (`r_quadrants`,
  `q3_is_q1_flipped`); the path from 1 through 2 to 3 has its one corner, a right angle, at quadrant 2, the `r` cell
  (`corner_at_r`) **[Lean]**. Care: the right angle "from 1 to 3" is this corner; as rotations about the centre it is `r` twice.

All of these are in IM, `arsenal/core/ArsenalCore/Possibility.lean`, on the kernel alone (claim II.0.4a).

**The jumping rope, and strong theory (claim II.0.4c).** The first author: the basis for existence is a point linked in a 3D space,
which requires a vector but is given meaning only as exactly not a vector, so it can say that it is a not-vector, which makes it
falsifiable, the attachment. Geometrically the link is a jumping rope held between two points, defined only by its direction: an
absolute rigidity, which projected to the non-existence space looks like its opposite, absolute weakness. Turned toward each other,
the two interfaces answer each other by the imaginary rotation `r`, from both sides, since a response must be given. So the
possibility oscillates around a point in 3D space, a 2D circle that in the classical view always gives a sphere, hiding behind the
definition barrier (a further reading of DB), at one speed, irreducible by construction. The string runs from the weak, the
possibility, to the strong, the Real Space, so "strong theory" is also a right reading **[reading]**. Exact counterparts, each
**[classical]**:

* **The sphere.** The pure states of a question with two answers form exactly a sphere in 3D (the mixed states fill the ball), the Bloch sphere (Bloch 1946), rotated by
  SU(2); over each of its points sits the circle U(1) of phases, the Hopf fibration of the 3-sphere over the 2-sphere (Hopf 1931).
* **The rope.** The rope between two points turned toward each other is the flux tube between a quark and an antiquark. The same
  coupling is weak at short distance (asymptotic freedom; Gross-Wilczek 1973, Politzer 1973) and strong at long distance, where it
  is expected to confine: lattice evidence, not a proof, and close to the open problem of Part III. Rigidity and weakness are one
  coupling at two distances.
* **The spinning rope** is the rotating relativistic string of Nambu and Goto (Goto 1971); in its rotating solution the endpoints
  move at exactly the speed of light, the one speed. String theory began as a theory of the strong interaction (Veneziano 1968), so "strong theory" has a literal history.

Care: in the Standard Model "weak" also names the weak force, the SU(2) factor. Weak and strong coupling are one force at two
distances; the weak and the strong force are two factors of the gauge group, and physics does not derive one from the other.

**What does not follow as stated (claim II.0.4d).** The first author: the circle around a point gives SU(3) x SU(2) x U(1) by
construction; from SU(2) as a question-shaped basis, which can assign any N to SO(N) with SO(N! + 1) as the first step, the expansion of
N from 2 to 3 settles the end only if at the end N is 3 while never having been observed that way; the rest should follow
**[reading]**. Exact parts and limits **[classical]**:

* The circle gives U(1) and the sphere SU(2). N! + 1 = 3 at N = 2 gives SO(3), which SU(2) double covers; N! + 1 = 7 at N = 3 meets
  a different fact, SU(3) inside G2 inside SO(7); neither continues (R.7b).
* "N is 3 but never observed as 3" is colour confinement: three colours, and only colourless states observed.
* SU(3) acts on the pure states of a question with three answers, the complex projective plane CP^2, of four real dimensions, which a
  circle in 3D space does not give. A space with exactly the symmetry SU(3) x SU(2) x U(1) needs at least seven dimensions; the
  minimum is reached by a family of spaces, circle bundles over CP^2 x S^2 (the three-answer question, the two-answer question and the
  phase), and the same work finds that they do not readily give the observed chiral, left-handed fermions (Witten 1981).

So "the rest should follow" is where it stops following; every known route needs further input at this step.

**The `+-` assignment and O1 (claim II.0.4e).** The first author: the question being assigned `+` and `-` is the proof of the eigenvalue
O1, from which all else is constructable, as a PP (Perelman-Poincare) typed, Yang-Mills shaped interface API **[reading]**. Exact parts:

* Assigning `+` and `-` is that every question has an answer (`every_question_has_an_answer`, `Classical.em`), IM's `?`. It holds for
  a question whose answer is `-` as much as for one whose answer is `+` (`assignment_does_not_decide`) **[Lean]**, so it is not `!`
  and does not prove O1.
* In free U(1) theory, the photon without self-interaction, every yes/no question is still a projector with answers 1 and 0, yet
  there is no mass gap **[classical]**; a proof of O1 must use what the free photon lacks. A projector's two answers are exactly 1
  apart, but the mass gap concerns the energy, which is not a projector; carrying "a gap of 1 per question" to "a gap uniform in the
  scale" is O1 itself.
* What does hold: O1 with the resolution clause gives torus decay, the gap and reflection positivity (III.9.5), and O1 is exactly
  DMP-completeness of the box (III.10c) **[Lean]**.

Built in III.13: an interface typed as the counting part of Perelman's proof as Appendix A reads it as a ledger (A.1g, itself a
reading), for the Yang-Mills box, with a theorem from an instance to O1 and its converse. It is equivalent to O1 and supplies no
instance.

### II.0.5 The ETM as the ODP running DMP

*New in Draft 6.* Draft 6's subtitle, from the first author's refinement of 2026-11-25; *the Possibility Space* stays the theme of
II.0.4. The ETM is the Existence Turing Machine, one running system that runs every computation (II.3.1; `docs/unified/ETM.md`); the
ODP is the Oscillon Degradation Protocol (I.5).

**The clock (claim II.0.5a).** The first author: the ODP is the internal clock. Its tick ends at `+`, which gives rise to the next
tick, a fully consistent perpetuum mobile as long as it can assert, as often as it needs to, that such a thing cannot exist; `+/+` is
the universal act. DMP is then the operating system of the ODP kernel, and the kernel's clock is given by c **[reading]**. Exact parts:

* the right angle `r` returns after four steps (`r_four`), a cycle that never ends **[Lean]**;
* `+` times or divided by `+` is `+`, the sign rule **[classical]**;
* a reversible computation can in principle run without dissipating, while a machine that delivers work from nothing cannot exist
  (Bennett 1973; the first law of thermodynamics) **[classical]**: the cycle is a clock, not an engine, the nearest exact statement to
  "as long as it can assert that such a thing cannot exist";
* the endpoints of the rotating string move at c (II.0.4c) **[classical]**.

That c is the clock of the kernel has no further exact part here.

**One ETM, and booting (claim II.0.5b).** The first author: our experiencing it is itself the minting of the G0 state. With
reflection positivity it keeps happening according to the ODP for as long as causality exists, and once it stops it restarts by
itself; so there are not many ETMs but one, whose properties can be borrowed through the same trick it uses. Understanding this gives
time its forward motion, which forces `r`, which forces degradation, which forces `r`: a boot **[reading]**. Exact part: running
systems form a category with a terminal object, the space of ledgers, so every running system has exactly one map into it
(`exists_unique_hom`, `univIsTerminal`, II.3.1) **[Lean]**; the "one" has this exact form, a terminal object, unique up to unique
isomorphism. That experience mints G0, and that the cycle restarts by itself, have no exact part here.

**0 = 1, NP versus coNP, P versus NP (claim II.0.5c).** The first author: in the end the paper proves 0 = 1 for the classical, along
with its classical consequences, which asserts c, and that is enough; so it proves NP = coNP and uses that to prove P != NP, which
gives a real 0 and 1 at the same ends of existence **[reading]**. This does not follow, for three reasons **[classical]**:

* 0 = 1 holds in exactly one ring, the zero ring, where existence and non-existence coincide (R.5a, **[Lean]**). In the natural
  numbers, the classical setting, 0 != 1, and a proof of 0 = 1 there would prove every statement, P = NP and P != NP alike, so it
  could separate nothing.
* NP = coNP and P != NP are open, and the paper proves neither: Part V proves a crossing theorem for sound two-premise proof systems
  on expanding formulas (in Lean, with two graph hypotheses stated, II.14.5) and names its open steps (V.0, V.6).
* NP = coNP would not give P != NP. P = NP implies NP = coNP, so NP = coNP is consistent with P = NP; the implication runs the other
  way, NP != coNP would give P != NP.

**The universal certificate, and the vacuous proof (claim II.0.5d).** The first author: the universal certificate is always `+1`, in
the meaning of 1 = 1. Since this system forces 0 and 1 to be one at the same time, it excises the element of lower ordinality in its
construction as that exact excision, which shows that to be truly rigorous a proof has to be vacuous **[reading]**. Exact parts
**[classical]**:

* 1 = 1 is the trivial certificate: it holds by reflexivity, and in Lean by `rfl`, with nothing to check beyond the two sides being
  the same.
* A proof carries no content beyond the fact that its statement holds: Lean's kernel identifies any two proofs of one proposition
  (definitional proof irrelevance), so a certificate, once it exists, is one, whatever it was built from.
* 0 and 1 are one exactly in the zero ring, where every element is 0 and every equation holds (R.5a, **[Lean]**).

Care: "vacuous" in its logical sense, a statement over an empty domain, holds without saying anything about any object; a proof of a
statement about objects that exist, such as the Wilson measure of O1, cannot be vacuous in that sense. What does hold is the weaker
form above: a proof is contentless as an object (proof irrelevance), and its content is all in the statement it proves.

**The essence as one input of the size c (claim II.0.5e).** The first author: from the essence line 2 + 2 = 5 = 4 = 0 = 1 = 1.5, the
essence simplifies to one input of the size c, and the O1 input becomes the question "Is the speed of light measurable?", which is
always yes and yet never seems to have existence. The size is c because c is a size. This ties the expression of set theory onto
arithmetic, and since it applies onto something it has an input, which must run exactly at 1 **[reading]**. Exact parts:

* The chain holds in exactly one ring, the zero ring, which has one element, so one input decides it (R.5a) **[Lean]**.
* c is a size by definition. Since 1983 the metre is defined from c, so c = 299,792,458 m/s exactly (CGPM 1983; BIPM 2019), and
  c = 1 in natural units, as on the lattice **[classical]**. A measurement of c measures the metre and the clocks.
* Only the round trip is measurable: the two-way speed of light is, while the one-way speed is fixed by a convention of clock
  synchronisation (Einstein 1905; Reichenbach 1928) **[classical]**.
* Only dimensionless constants are measurable as such, among them the fine-structure constant α **[classical]**, which the
  paper calls the VIBE coefficient (R.5b).
* In von Neumann's construction 0 is the empty set and n + 1 is n together with n itself, so 1 is the set whose only element is the
  empty set (von Neumann 1923) **[classical]**. The first author reads this as existence being non-existence plus one (I.7)
  **[reading]**.
* Arithmetic is the finite part of set theory. Ackermann's coding is a bijection between the hereditarily finite sets and the natural
  numbers, and Peano arithmetic and ZF with the axiom of infinity replaced by its negation are mutually interpretable (Ackermann
  1937); with transitive closure added they are bi-interpretable (Kaye-Wong 2007) **[classical]**. That the coding, losing nothing, is
  a map at factor 1 where the ETM lives is the first author's identification **[reading]**; its exact counterpart is the ETM's regime,
  cost equal to the floor, lossless (II.3; `docs/unified/ETM.md`).
* In set theory the letter c, in Fraktur, names the size of the continuum, 2 to the power aleph-0. It exists, and its exact value among the
  infinite sizes is not decided by the standard axioms (ZFC): the continuum hypothesis can be neither proved nor refuted there
  (Goedel 1940; Cohen 1963) **[classical]**.

Care: the physical c and the set-theoretic c share a letter, not a theorem. A unit fixes the frame in which O1 is stated and does not
supply O1. Factor 1 is the floor, where nothing settles by contraction, while O1 asks for a cost above the floor, uniform in the scale
(II.3).

**The one condition: O1 supplied at minting (claim II.0.5f).** The first author, asked whether Draft 6 as merged is a DMP-complete
construction: not yet, which is right for root G0. O1 is supplied by the reader reading its definition of main DMP G0 at minting, a
vacuous construction, while every other dependency is rigid. Every minting from G0 is a step that closes that assumption, under the
owner's guarantee: the owner merges the paper for publishing and has authority equal to G0 during pressing (I.5). DMP is stated with
all its assertions, so as soon as one invalid case is found, a DMP-complete v0.9.9 ceases to exist and forces a remint to v1, possible
only once the hole is closed. The certify stage is reached by extending into possibility space with a universal witness, agreed upon
beforehand, with absolute authority over the validity of every act. Through constructability, once a truly DMP-complete system can be
assembled from the one box, it can be assumed to hold universally until exactly the step where the ray is no longer observed
**[reading]**. Exact parts:

* Measured on its own criteria, Draft 6 is not DMP-complete: the versions are not settled, by one use (E.9), and O1 is a cell that is
  not `+` (E.6, III.10e, III.13d) **[paper]**. Every other dependency is proven back and forth (T.14, T.15, E.1 to E.4, E.11)
  **[paper]**.
* O1 is posed and never assumed (`OpenStep`, R.9a) and stated once, as the one assumption (Part X). Supplied as a hypothesis it gives
  the gap, torus decay and reflection positivity (III.9.5), and the interface of III.13 is exactly it **[Lean]**.
* A claim stated for all cases is refuted by one invalid case. The matrix, the reproduce stage and the round trip each fail on one
  (E.2, E.9, T.14), and Gravity pins DMP 0.9.9 by its commit id, `4400cce`, so a new version is a new pin **[paper]**.
* The universal witness agreed beforehand is a root of trust. In the Lean it is the kernel, fixed before any proof is written,
  accepting or rejecting every declaration, with nothing above it (the de Bruijn criterion, T.13; two kernels, T.14) **[classical]**;
  in IM's certificate checks a chain counts only when it ends at a root that was presented (`TrustAnchors`) **[paper]**.
* "Assumed to hold universally until the ray is no longer observed" is falsificationism: a universal law is never verified, only
  corroborated, and stands until one observation refutes it (Popper 1935). It is the status the ledger gives a numerical claim, which
  can refute and never proves a for-all **[classical]**.

Care:

* Supplying O1 is assuming it. The owner's guarantee holds the record, what is merged and minted; it cannot make the Yang-Mills measure
  satisfy O1, a property of an object already defined. If O1 is true the assumption is harmless and the gap follows. If O1 is false, the
  minted system proves a false gap: it is unsound. Only if the base theory refutes O1 is it inconsistent, proving everything, the
  0 = 1 collapse of II.0.5c; O1 could also be independent of the base theory. Which case holds is the open question.
* No consistent, effectively axiomatised system strong enough for arithmetic proves its own consistency (Goedel's second theorem,
  R.1h). DMP certifying its own
  completeness reads exactly as: complete until an invalid case is found, checked from outside, case by case. DMP's own cell is `.`,
  not `+` (E.11).
* An invalid case for O1 would show that this route to the gap fails, not that Yang-Mills has no gap.
* Universality held until refuted is not mathematical induction, which needs the inductive step proved. O1 stays open in the ledger (III.10e,
  III.13d); the paper records the assumption, under the agreed witness, as the first author's reading and does not claim it.
* The rule from v0.9.9 to v1 is DMP's own process; it is recorded here as the reading, and DMP itself is not changed.

**Elastic spheres, real induction and the kernel (claim II.0.5g).** The first author: the construction can also be imagined as
perfectly elastic spheres that see each other's efficiency in existing and join only when a new local optimum is reached, paying the
same cost, observability, whether it is the case or not. That makes it binary: true in a DMP-complete system, and equal to existence
when 1 makes it so. The reals then span a real space in which perfect elastic collision and agreement on "not" suffice for those
properties to be inductive. This real induction is represented by the N! + 1 of SO() and is written +N!; through DMP, `+` is the
universal assertion, N the reals, and `!` runs certifiably. By this induction the naturals equal the reals under the universal
operator. What separates them as sets is that each can reconstruct the other during an act, which gives internal DoE-level trust,
and a set that excludes, as a DoE must by default, must run. This lets DMP also certify the kernel it runs on, restoring G0's pressing
status as a running assumption, literally: it certifies the provability of the kernel's induction, which secures constructability, and
bases it on the assumption that such a system, when minted, is DMP-complete **[reading]**. Exact parts:

* **Elastic and joining.** Perfectly elastic collisions conserve energy and momentum and are reversible: factor 1, the floor (II.3)
  **[classical]**. Joining needs a cost above the floor: perfectly elastic spheres cannot bind without something carrying energy away
  **[classical]**, and a cost above the floor is the contraction class, in which the run settles (the settle theorem, II.3)
  **[Lean]**.
* **The same cost either way.** Erasing a bit costs at least kT ln 2, whatever its value (Landauer 1961) **[classical]**: the cost of
  the binary question is the same for both answers (II.0.4).
* **Real induction.** A property that holds at the start, extends a little beyond every point where it holds, and is kept when passing
  to a limit holds on the whole interval; this principle is equivalent to the completeness of the reals (Clark 2019) **[classical]**.
* **The factorial on the reals.** The recursion (n + 1)! = (n + 1) n! carries to the reals: Γ(x + 1) = x Γ(x) with Γ(1) = 1 has
  exactly one log-convex solution, the Gamma function (the Bohr-Mollerup theorem; Artin 1931) **[classical]**. 1/n! is one turn (R.7a)
  **[Lean]**; N! + 1 gives SO(3) at N = 2 and meets SO(7) at N = 3 (R.7b) **[classical]**.
* **`+N!` as a theorem.** `!` is IM's operator that settles certifiably (R.10a); a kernel-checked theorem about every real number is a
  universal assertion over the reals, settled certifiably **[paper]**.
* **Equal under the universal operator.** Every proof is a finite string, so every certificate about the reals is coded by a natural
  number. A countable field, the real algebraic numbers, satisfies exactly the same first-order sentences about the field operations as
  the reals (Tarski 1951), and every first-order theory with an infinite model has a countable one (Loewenheim 1915). By proof
  irrelevance every certificate of a true statement is one (II.0.5d) **[classical]**.
* **Each reconstructs the other.** Mathlib builds the reals from the naturals, through the integers and the rationals, as Cauchy
  sequences up to equivalence (mathlib 2020); the naturals come back inside the reals as the smallest set that contains 0 and is closed
  under +1 **[classical]**.
* **The kernel.** Two kernels written separately check every target (T.14) **[paper]**. lean4lean, a typechecker for Lean written in
  Lean and pinned as an External in IM, proves parts of the kernel correct (Carneiro 2024) **[classical]**. Lean's type theory, its
  inductive types included, has a model in set theory with inaccessible cardinals, and so is consistent relative to it (Carneiro 2019;
  its record was read, not its text) **[classical]**.

Care:

* As sets the naturals and the reals differ: every list of reals misses one (Cantor 1891). What separates them is the direction of the
  reconstruction: from the naturals to the reals is the completion over all Cauchy sequences, where the size grows; the other way only
  cuts out a subset. The completeness clause is the one no countable certificate settles alone, and for Yang-Mills the clause that must
  hold uniformly in the limit is O1.
* Only countably many reals are computable (Turing 1937): what runs is the proof, not each real.
* N usually names the naturals; here it names the reals, by the first author's choice. The dimension N! + 1 and the step +N! are
  different objects, and the pattern of R.7b stops at N = 3.
* No exact counterpart was found for "a set that excludes must run"; its context is X.64b (DMP-completeness defined as running on DMP),
  excision at transmission (I.5, R.2) and IM's rule that a refusal is not a state (R.9). DoE is the first author's term (the preface;
  IX.8).
* No consistent, effectively axiomatised system strong enough for arithmetic proves its own consistency (Goedel's second theorem, R.1h).
  The kernel's induction is certified relative to a model outside it, and the base, that a minted system is DMP-complete, stays an
  assumption, run and checked case by case, in the same place as O1 (II.0.5f).

## II.1 The ledger and the transport theorem

**Why it clicks.** A step that forgets a fixed share each time forgets geometrically. Write the share as a cost, and costs add.
That is II.12 in bookkeeping form, and it carries an uncertainty as well as a certificate.

**The ledger (II.1.0).** A quantity M_n >= 0 *pays* cost c_i at step i, with floor delta, when M_{i+1} <= e^{delta - c_i} M_i.
Then:

* M_n <= e^{n delta - (c_0 + ... + c_{n-1})} M_0, the ledger inequality;
* if every cost is at least kappa, then M_n decays like e^{-n(kappa - delta)}; if also kappa > delta, the sum of the M_n converges
  (a *cost above the floor*, `CostAboveFloor`);
* a lower bound on the final value is a lower bound on the total cost, hence on the size of the object that paid it.

**[Lean]** (`Unified/Ledger.lean`, `Pays`, `ledger`, `decay`, `summable_of_gap`, `size`, `CostAboveFloor`, `rate_of_costAboveFloor`;
the abstract running-system form is `ETM/RunSys.lean`, `RunSys.carry`, `RunSys.contract`, `RunSys.decay_cost`).

**Theorem II.1.1 (bounded transport).** An uncertainty e_n >= 0 crosses step n with factor f_n and floor delta, and the step may add
fresh uncertainty r_n >= 0 of its own: e_{n+1} <= e^delta f_n e_n + r_n. If the steps contract, e^delta f_n <= q < 1, and each adds at
most R, then e_n <= q^n e_0 + R/(1 - q) at every step, uniformly in n. **[Lean]** (`Unified/Transport.lean`, `bounded_transport`,
`transport_geom`, `acc_eq`).

**Theorem II.1.2 (critical transport).** At cost = floor, e^delta f_n = 1, nothing is damped: e_n <= e_0 + (r_0 + ... + r_{n-1}).
The bound is attained. It stays bounded exactly when the r_j are summable, and a constant fresh uncertainty grows without limit.
**[Lean]** (`critical_transport`, `critical_sharp`, `critical_bounded_iff`, `critical_unbounded`).

**Theorem II.1.3 (sign preserved).** If a quantity has a sign margin m_n and the uncertainty about its counterpart across the
boundary stays below it, e_n < m_n, the counterpart's sign is certified at every step, with value at least m_n - e_n. **[Lean]**
(`sign_transport`, `sign_of_bounded`, `sign_of_critical`).

**II.1.4 (the ledger is the case r = 0).** With no fresh uncertainty the transport theorem is the ledger: `Pays`, `carry`,
`Ledger.contract`, and every ledger of a running system. **[Lean]** (`pays_iff_transports`, `carry_of_transport`,
`ETM.Ledger.transports`, `contract_of_transport`).

**II.1.5 (zero slack, exactly).** When an uncertainty and the margin it is compared with pay the same cost at every step, their
ratio crosses at exactly cost = floor (the ratio has factor 1). So damping relative to a margin needs the margin to shrink more
slowly than the uncertainty (a reading of this, not a further theorem). **[Lean]** (`relative_transport`, `relative_critical`).

**The three applications.** Part X section 7 states what each problem's uncertainty is and where the open step sits. Yang-Mills: the
boundary uncertainty of a slab. GRH: the explicit formula's remainder against the collapsing margin. NP vs coNP: the hiding error
per hidden variable.

---

## II.2 The encoder, its half-turn, and the full turn

**Why it clicks.** A boundary passes on one state, seen once from the inside and once, after one rotation, from the outside. Both
sides certify the same size. All that is left to say about the step is how much the state overlaps with its rotated image, and one
number carries that.

**Definition (II.2.1).** An *encoder* is a state psi in a space with a positive form, together with its rotated image psi' = R psi
of the same norm (the shared root). Its one number is the *reflection coefficient* c = <psi, psi'> / ||psi||^2. Positivity forces
abs(c) <= 1. **[Lean]** (`Unified/Encoder.lean`, `Encoder`, `Encoder.ofRot`, `refl`, `norm_refl_le`; reading the boundary from the other
side conjugates c: `refl_swap`).

**Two loss factors, determined by c alone (II.2.2).**

* The Szego factor 1 - |c|^2 is the share of psi left after removing its projection on the mirror image: the squared norm of
  psi - conj(c) psi' is ||psi||^2 (1 - |c|^2). It is 1 exactly at c = 0 and positive exactly for |c| < 1.
* The electric factor (1 - c)/(1 + c), taken at the real part of c, is the odd part over the even part under the rotation:
  ||psi - psi'||^2 / ||psi + psi'||^2 = elec(Re c), when psi + psi' is not zero.

The Szego factor lies in [0, 1] for every encoder. The electric factor lies in (0, 1) for 0 < Re c < 1; for -1 < Re c < 0 it is
above 1. The ledger cost is the minus log of a factor in (0, 1], and a chain of encoder factors is a ledger with
floor 0. A uniform bound of the factors below e^{-delta} is exactly a cost above the floor. **[Lean]** (`szego`, `szego_mem`,
`szego_pos_iff`, `szego_eq_one_iff`, `szego_remainder`, `elec`, `elec_mem`, `encoder_elec`, `pays_of_factors`,
`costAboveFloor_of_factor_le`, `factor_le_of_costAboveFloor`; the one-box form `oneBox_iff_refl`).

**One distance, two functions (II.2.3).** The cost of the electric factor is a hyperbolic distance d of c from the lossless
point 0, and the Szego factor is the second function of the same d: it equals 4 e^{-d}/(1 + e^{-d})^2 **[Lean]**
(`Unified/GRHLens.lean`, `elec_cost`, `szego_of_elec`, for real c), that is 1/cosh^2(d/2) (elementary algebra, not in Lean). This is the object Part X section 2 puts at the centre. It is the
distance of the encoder from the lossless point.

**The half-turn (II.2.4).** The electric factor is a Moebius map of the matrix (1/sqrt 2)[[-1, 1], [1, 1]]. That matrix is
symmetric and squares to the identity, so the map is an involution, and its two fixed points, sqrt 2 - 1 and -(1 + sqrt 2), are
antipodal. **[Lean]** (`halfTurn_mobius`, `halfTurn_transpose`, `halfTurn_mul_self`, `elec_elec`, `elec_selfdual`,
`elec_fixed_neg`, `fixed_antipodal`). As a Moebius map of the Riemann sphere it is a rotation by 180 degrees, the half-turn
**[classical]**. It swaps the two ways of composing: the product of reflection coefficients is carried to hyperbolic addition of
electric factors (`elec_mul`, `elec_oplus`) **[Lean]**. Its self-dual point has cost log(1 + sqrt 2), the 0.881 of II.13
(`selfdual_cost`) **[Lean]**.

**What the half-turn does not do (II.2.5).** It is a symmetry of the description. It exchanges the pictures and fixes its axis, so
it never decides on which side of the axis a box lies or how far from it. It does not turn an upper bound on one encoder into a
lower bound on another **[paper]** (`docs/unified/GRH-LENS.md`, 6.3).

**The three applications (II.2.6).** Yang-Mills: the twist ratio Z_tw/Z of the hand-over box is c, and the chain form of O1 (`YMOneBox`) is c
above (mu - 1)/(mu + 1) for every outside. GRH: the Verblunsky step of the zero measure at each scale is c. NP vs coNP: the crossing label passes at factor 1
with a cutting-planes line, so the encoder explains resolution's cost but supplies none for strong systems **[paper]**
(`docs/unified/ENCODER.md`, 1).

**The full turn (II.2.7).** The half-turn is the case N = 2 of one tool. Go once around a point, from -pi to +pi, and average, and
one exact number is left; for a function real on the real axis, such as exp, the + half mirrors the - half and that number is real.

* **In N equal steps**, the N-th roots of unity: one turn of zeta^(jk) gives N when N divides k and 0 otherwise, so one turn reads off
  any single coefficient of a sum of N powers (`full_turn`, `full_turn_cos`, `full_turn_coeff`) **[Lean]**.
* **On a circle** around c, one turn reads off the n-th Taylor coefficient of a function holomorphic on the disc, Cauchy's formula
  (`full_turn_circle`) **[Lean]**. For exp around 0 it gives $1/n! = \frac{1}{2\pi i}\oint e^z z^{-n-1}\,dz$ on every circle: the
  factorial is a full turn (`full_turn_factorial`) **[Lean]**.
* **At a zero**: if Lam = (s - c)^r g with g holomorphic, one turn of Lam/(s - c)^(r + 1) gives g(c), the leading coefficient, and if g
  has no zero on the disc, one turn of Lam'/Lam gives r: the order of a zero is a winding number (`full_turn_leading`,
  `full_turn_order`) **[Lean]**.

All of it is in IM's arsenal, `Arsenal/FullTurn.lean`, from Mathlib alone. At N = 2 the two steps are +1 and -1, the two averages are
the even and odd parts psi + psi' and psi - psi', and the electric factor of II.2.2 is their ratio: the encoder is the full turn at
N = 2 **[paper]** (claim II.2.7). The parts use the turn four times: the hand-over over all N sectors (II.13.3, III.3), the explicit
formula (IV.1), the BSD rank and leading coefficient (VII.3), and the first author's factorial reading (R.7).

**Encoding, decoding, and smelly states (II.2.8).** An *encoding* is a map out, a *decoder* a map back. A state is **smelly**, in the
first author's word, when decoding its encoding does not return it: the turn out and back did not close, the rotational symmetry is
not positive. Four facts decide when a decoder can be clean **[Lean]** (IM, `Arsenal/Decode.lean`; claim II.2.8):

* a decoder that is never smelly is exactly a left inverse of the encoding (`never_smelly_iff`);
* an injective encoding has such a decoder (`exists_clean_decoder`);
* a lossy encoding makes every decoder smelly somewhere (`smelly_of_not_injective`), and every hash is lossy, a map from all messages
  to finitely many digests, so every decoder of a hash is smelly somewhere (`hash_smelly`);
* the full turn decodes: reading N coefficients at the powers of a root of unity and averaging one turn back returns every one
  (`turn_decodes`, C6).

These four carry what Appendix R and T say about hashes and turns, as instances of one statement. A hash has no decoder that is
clean on every input: a digest with several inputs decodes correctly to at most one of them (R.6a, from `hash_smelly`; for messages of
bounded length, `digest_collision`). That an input of a given digest is hard to find at all is a different property, preimage
resistance, which non-injectivity neither gives nor needs; T.6 shows it in small **[numerical]**. A known cyclic rotation is undone by
completing its turn (R.8b; in the toy `vx_rot_complete`), and one turn back recovers each component of a sum of powers
(`turn_decodes`). The toy's smelly states, rotating `vxunderground` by k and back by k', are this notion (`toy_smelly_iff`, T.5). The
round-trip check of the repository's trusted hashes decodes by lookup: fetching a commit by its id is a decoder that is clean on what is
stored and smelly only off it, which is the "origin, not identity" of R.6a; the check tests that each pin is not smelly, back and then
forth (R.6b).

---

## II.3 The settle theorem and the decidability edge

**Why it clicks.** If every step pays a cost above the floor, the quantity must fall below any error bar, and one can count how long
that takes. If steps may pay exactly the floor, nothing forces it to fall, and nobody can tell in general whether it will.

**Running systems (II.3.1).** A *running system* with floor delta has states, a transfer step, an encoder factor in [0, 1] at each
state, a mass >= 0, and the ledger law mass(step x) <= e^delta fac(x) mass(x). The ledger theorems hold on every running system.
Running systems form a category in which the space of ledgers is the terminal object, so every running system has exactly one map
into it (its ledger). **[Lean]** (`ETM/RunSys.lean`, `RunSys`, `RunSys.carry`, `RunSys.contract`, `Hom`, `exists_unique_hom`,
`univIsTerminal`). The statements XI.2c of the Outlook rest on this.

**Theorem II.3.2 (settle).** In the *contraction class* (every factor at most theta, with e^delta theta < 1, which is exactly a
cost above the floor, for positive factors), the run from any state of mass at most M reaches balance within epsilon, by an
explicit computable number of steps: balanceBound M eps q = ceil(M q / (eps (1 - q))) + 1, for rational M, eps > 0 and q with
e^delta theta <= q < 1. So on this class the unbounded
question "does it settle?" is a bounded one. **[Lean]** (`ETM/Machine.lean`, `Contracting`, `contracting_iff_costAboveFloor`,
`balanceBound`, `balanceBound_ge`, `reaches_of_contracting`, `reaches_iff_bounded`, `reaches_of_contracting'`). The same statement
is XI.2a.

**Theorem II.3.3 (the edge).** The machine that runs every partial recursive content is lossless: factor 1, cost = floor, outside
the contraction class. Whether it reaches balance is undecidable for all contents: no computable predicate decides it, and its
truth value exists (classically) but cannot be computed. **[Lean]** (`etm`, `etm_universal`, `etm_not_contracting`,
`etm_balance_undecidable`, `etm_truth_edge`; both sides in one statement, `etm_edge`). The same statement is XI.2b.

**What it says in one line.** When every step pays a cost above the floor, settling is decidable within an explicit bound. When
steps may pay exactly the floor there are systems (the universal machine) for which it is not; a lossless system as such need not be undecidable (II.0). The step from the second case to
the first is the open step of every card (Part X, sections 4 and 5).

**One step, one `decide`.** The first author's definition: a DMP-complete proof is lintable in one step, relying only on `decide`.
The exact part is the computable layer of the machine: every decision has a computable form on rational data, proved right for the
real system once (`szegoQ_cast`, `elecQ_cast`), and an instance is then one kernel evaluation, for example
`balanceBound 1 (1/1000) (1/2) = 1001` **[Lean]**; the one-box certificate is one step at the shared gate plus induction (II.4).
So a finished, DMP-complete proof has its last step a single `decide` on finite data, with its correctness theorem proved once in
general **[reading]** (claim II.4f). Care points: the correctness theorems are ordinary Lean proofs over the reals, not `decide`
alone; the open steps are not of this form (O1 is a for-all over every outside, not one finite check); and `native_decide` stays
excluded, since the kernel itself must check the step.

**Existence is free, construction costs.** The first author's one-line summary of the machine: being in the state space costs
nothing; reaching a state costs a step, and every step pays at least the floor **[reading]** (claim II.3.4). It is the shape of the
ledger law (II.3.1) and of the one-box test, where sharing the gate is free and the content is that the marker travels with it
(X.68b). A hash is the same shape in a third setting: the hash was computed from some content, so a preimage exists, and checking
a supplied one is a single forward step; finding one from the hash alone is the costly direction **[classical]**. Nothing in this
paper weakens an established hash or cipher: no result here gives a way to invert one, and the reading agrees with their
one-wayness. That one-wayness stays what it is in the literature, a well-tested assumption rather than a theorem: that any one-way
function exists is open and would imply P != NP **[classical]**. The Clay statements ask for existence and construction, which is why
their cost sits in the construction step, O1 for Yang-Mills.

**The three applications.** Yang-Mills: the floor is the cost above log mu, and keeping it uniform in the cutoff is O1. GRH: the
margin decays without a floor (zero slack, II.1.5), so only the sign is decided scale by scale. NP vs coNP: a constant cost per
hidden variable is a floor.

---

## II.4 The one-box test

**The one-box test.** The author's sharpening: a box needs no outside, because every confinement has one shared gate at the DB. It
needs one command, step forward, the universal tick, which can simulate everything. If the step produces the wrong R136a1 marker,
the box is not DMP-complete; if the marker is correct, it is **[reading]**. In Lean (the rotation API, in IM's arsenal, `Arsenal/Rotation.lean`, with the running-system version in
`ETM/Rotation.lean`): a box has one command, a gate factor, a margin and a marker per step, inside or R136a1; the marker is correct when it agrees with the gate's own factor, and
DMP-complete means correct at every tick **[Lean]** (claim II.4a). The outside is read through the same gate by the half-turn: in the
generic API the agreement of the two readings is the gate's law (a field of `Box.Gate`), and in the plaquette layer it is proved: for a
closed Z/2 layer the flux read from a box and from its complement agree **[Lean]** (claim II.4b). Care point: the test has content
only when the marker is the system's own claim; a marker read off the gate afterwards always passes **[Lean]** (claim II.4c). What
the test gives for each card is in III.12 (Yang-Mills), IV.8 (GRH), V.10 (P vs NP), VI.8 (the model Navier-Stokes box), VII.8
(BSD), VIII.8 (Hodge), IX.8 (GU), and Part X 4.4. The one-box certificate (one step at the shared gate certifies every tick), the scale certificate from the sharing,
and the universal machine as a box are stated with the one assumption in Part X 4.4 (claims X.68 to X.68c) **[Lean]**. Rigidity is
one-box testable too: a manifold's presentations with its self-equivalences acting make a box that is DMP-complete exactly when the
manifold is rigid (rigid here is the structure-set condition: every presentation is the manifold seen through a self-equivalence; its
identification with a given manifold is the user's input), and the manifold is rigid if its box shares the gate with a certified box,
the sharing being the named hypothesis R136a1 "the gate is shared across scales", never proved (IM, `Arsenal.Rigidity`) **[Lean]**
(claim II.4d; G2 in Appendix A.5). Every card is also a box: the tick box passes exactly when the statement of every tick holds,
and the card box exactly when the card's open step holds, and then gives the card's conclusion; it restates the step and proves no
new bound **[Lean]** (`ETM/CardBox.lean`, claim II.4e).

### II.4.1 Restatement and induction: the front door

In familiar terms: a problem is restated as one statement checked at every step of a sequence, and the restatement holds exactly
when the statement holds at every step. A proof then has the shape of an induction: a base case and an inductive step. In DMP's
terms a system with states, one step and its own claim at each state is an *observable system*; its restatement is its *one-box
description*, a box of the same API whose marker always asserts the claim (*inside*) and whose gate reads whether the claim is true,
so the box is correct at a state exactly when the claim holds there (`correct_iff`). The marker is the claim asserted, never read
off the gate: the self-marked box, whose marker is the gate's own verdict, always passes and says nothing (II.4c, `selfMarked_complete`),
and this box is its opposite. The claim is a decidable proposition; decidability is classical here, so this is no restriction:
every proposition is an observable system with one state.

**What each word buys** **[Lean]** (IM, `Arsenal/Observable.lean`; claim II.4g):

* *Restatement* (`box_complete_iff`): DMP-complete from a start exactly when the claim holds at every step. By definition; it proves
  nothing by itself.
* *Induction* (`route`, exact along the run `route_iff`): the base case (the claim at the start) and the inductive step (a step that
  keeps the claim) give the claim at every step. This is induction on the step; a proof of this shape exists exactly when the claim
  holds along the run, so the shape says what must be shown, not that it can be.
* *Every scale* (`route_everywhere`): where every scale's box is mapped onto the one box by a map that keeps the step, the gate and
  the marker (the shared gate, the named hypothesis R136a1), the induction shown once holds at every step of every scale. The
  content of this part lies in the map: in the verify toy the parity argument for k bits sits in the map onto one bit (T.2).
* *Falsifiable* (`refuted_by_tick`): one step where the claim fails refutes it.

When the observation is a reading against a margin (`ofReading`) and the reading is a coefficient hidden in a sum of N powers of a
root of unity, one full turn computes it exactly, so the check can be read by one turn (`turn_gate`, II.2.7). Two systems run side by
side give a system whose inductions combine (`prod`, `route_prod`) **[Lean]**, so a larger proof is the parts reassembled as the API
guides.

**Binary data, read as real numbers.** Read the bits {0, 1} as real numbers, so that n bits are the corner points of a space of
dimension 2^n. A reversible computation permutes those points, a unitary map over the complex numbers, so complex mathematics, the
full turn included, applies to it exactly; and every computation can be made reversible by keeping its history **[classical]**
(Bennett 1973; Toffoli 1980) (claim II.4h). Care point: the history is the supplied input. A reversible version of a hash runs
backwards only with the input it kept; a digest alone is not undone (R.6a, T.6).

**Where the open part sits, problem by problem** (claim II.4g for the Lean column; the reading of the two boxes with a gate factor
of their own as observable systems is **[paper]**, since they are gravity's own box type and no Lean bridge to IM's is written):

| Problem | Statement checked step by step | Lean box | Open part | Lean link |
|---|---|---|---|---|
| III Yang-Mills | the level criterion at every lattice level from k0, for some cell geometry and margin | `ymBox` | the inductive step, level to level: O1 (`FineOneBox`, equivalent in Lean, `fineOneBox_iff_complete`) | [paper] for the reading |
| III Yang-Mills card | the chain form `YMOneBox` at every step | `cardBox` | the base case | `tickBox_observable` |
| IV GRH | the sign at every scale (`ScaleSign`) at every step | `cardBox` | the base case | `tickBox_observable` |
| V NP vs coNP | the crossing cost (`CrossingCost`) at every step | `cardBox` | the base case | `tickBox_observable` |
| VI Navier-Stokes, three cards | route I's `PeriodContraction`; regularity; the A/B dichotomy (VI.2) | `cardBox` | the base case, not assumed by the paper | `tickBox_observable` |
| VI model box | the energy-only factor within the margin at every dyadic scale | `nsBox` | fails at some scale: the energy ledger refuted as a certificate, not regularity | [paper] for the reading |
| VII BSD | BSD for the curve at every step | `cardBox` | the base case | `tickBox_observable` |
| VIII Hodge | the Hodge statement for the input at every step | `cardBox` | the base case, proved for divisors | `tickBox_observable` |
| IX GU | charge quantisation at every step | `tickBox` (a box, no card) | none in the box: it passes, proved; the GU open step lies outside it (IX.5e) | `tickBox_observable` |
| Appendix T | an even word at every step, at every bit width | IM's box | none: base case, inductive step and the map of scales all proved | native |
| Trusted hashes (R.6b) | each trusted hash: back and forth deliver the same value | no Lean box: a check item by item, with no induction | none: every item checked, 9 proofs pass; the canary first tests the tools | [paper] |

So the proof has one shape everywhere, and the parts show where its open part sits: the base case on the cards, the inductive step on
the Yang-Mills box. Appendix T runs all of it on binary words. Figure 1 shows the shape once (in the typeset paper; the Markdown keeps
its source in a comment).

<!-- latex
\begin{figure}[ht]
\centering
\begin{tikzpicture}[x=1cm,y=1cm,every node/.style={font=\small}]
  \foreach \i in {0,1,2,3} { \node[draw,circle,minimum size=7mm] (s\i) at (\i*2,0) {$\i$}; }
  \node (dots) at (7.9,0) {$\cdots$};
  \foreach \i/\j in {0/1,1/2,2/3} { \draw[->,thick] (s\i) -- node[above,font=\footnotesize] {step} (s\j); }
  \draw[->,thick] (s3) -- (dots);
  \node[draw,rounded corners,fill=gray!15,align=center,font=\footnotesize] (base) at (0,-1.45) {base case:\\ the claim at 0};
  \draw[->] (base) -- (s0);
  \node[align=center,font=\footnotesize] at (4,1.05) {inductive step: once true at a step, true at the next};
  \draw[decorate,decoration={brace,mirror,amplitude=5pt}] (-0.4,-0.55) -- (6.4,-0.55) node[midway,below=6pt,font=\footnotesize] (onebox) {the one box: the whole run};
  \node[draw,rounded corners,font=\footnotesize] (c1) at (2,-3.1) {scale 2};
  \node[draw,rounded corners,font=\footnotesize] (c2) at (4.4,-3.1) {scale 3};
  \node[draw,rounded corners,font=\footnotesize] (c3) at (6.8,-3.1) {scale $\dots$};
  \foreach \c in {c1,c2,c3} { \draw[->,dashed] (\c) -- (3,-1.25); }
  \node[align=center,font=\footnotesize] at (4.4,-3.95) {dashed: every scale's run mapped onto the one box, keeping the step, the check and the marker (the shared gate)};
\end{tikzpicture}
\caption{The headline as a picture. A statement is checked at every step of a run; a proof is a base case and an inductive step, and
the dashed maps carry it from the one box to every scale. Where the open part sits: on a card, the base case; on the Yang-Mills box, the
inductive step; for G2, the dashed maps (the shared gate, named R136a1). In the verify toy the content sits in the dashed maps too, and
everything there is proved.}
\end{figure}
-->

## II.5 The API: cards

**Why it clicks.** The form layer says nothing about content, so every problem can use it. Every problem has the same shape: an
input, a proved structure, one named open step.

**What the API gives (II.5.1).** One import, `ProofPhase.API`, a facade over the form layer: it moves and renames nothing, and its
theorems are re-exports or one-line wrappers. It has one structure per concept **[Lean]** (`API.lean`):

| Concept | In Lean | You supply | You get for free |
|---|---|---|---|
| a running system | `RunSys` | states, step, factor, mass, the ledger law | `carry`, `contract`, `decay_cost` |
| the settle bound | `settle`, `settle_everywhere`, `settle_iff_bounded`, `balanceBound` | the contraction class | an explicit step count |
| the decidability edge | `edge` | nothing | decided above the floor, undecidable at it |
| a chain with costs | `Chain` | a quantity, costs, the step law | `Chain.ledger`, `Chain.decay`, `Chain.summable`, `Chain.size` |
| a margin that survives | `Margin` | shares kept | `Margin.survive`, `Margin.pos` |
| an encoder | `Encoder`, `szegoFactor`, `elecFactor`, `cost` | a state and its rotation | the Szego factor in [0, 1] (`szegoFactor_mem`); the electric factor is `elec (Re c)` |
| an uncertainty | `Uncertainty` | error, factor, fresh uncertainty | `bounded`, `critical`, `sign` |
| the problem card | `Problem` | input, `Open`, `Concl`, `proved` | `Problem.holds` |
| the open-step slot | `OpenStep "name" P` | the one statement `P` | `P` itself, labelled |
| the external-input slot | `External "source" P` | a theorem from the literature | `P` itself, labelled |

The slots are transparent: `OpenStep "..." P` *is* `P`, so a theorem takes it as an ordinary hypothesis. Nothing is ever an axiom.
The labels make the open steps and outside dependencies greppable.

**Adding a problem (II.5.2).** Seven steps: copy the template (`API/Template.lean`, a worked toy); write the input; fill a running
system, chain or margin and check the one ledger inequality; write the open step in its slot; call the free theorems; add an
uncertainty if the input is only approximate; state the card. **[paper]** (the procedure; `docs/unified/API.md`, 3). The three
cards of Parts III to V are `API/YangMills.lean`, `API/GRH.lean` and `API/NP.lean`, each proved as "open step gives conclusion"
**[Lean]**; each open step is **[open]** (III.5.6, IV.4, V.6: `CrossingCost`, with V.4.10 the nearest concrete target). A
problem may have several cards: Navier-Stokes has three (VI.2), BSD three (VII.2), Hodge five (VIII.2); GU has a box and no card
(IX.2). The GRH card is a card for a finite model of zeros (its
open step `ScaleSign` is the sign at every scale of that model); the link to zeta is `tie_in`, which takes the statement of the
Riemann hypothesis as an `External` hypothesis. The toy settles in 101 steps to 1/100 (`toy_settle_101`)
**[Lean]**.

**What runs and what is truth only (II.5.3).** The settle count, the encoder factors on rational data and the ledger law on
rational data are computable and decidable: `balanceBound`, `szegoQ`, `elecQ`, `PaysQ`, `settle0`, with `szegoQ_cast`,
`elecQ_cast` and `PaysQ.pays` proving them right for the real system; the machine's step and balance test are primitive recursive
(`estep_primrec`, `halted_primrec`). The real-valued structures and the undecidability on the lossless side are truth statements,
not computed. **[Lean]** (`API.lean`).

**One consequence for every instance (II.5.4).** G0's phase field is one compact circle. Every continuous character of the circle
is z -> z^n for an integer n, so every label carried on it has integer charge, with no further assumption. **[Lean]**
(`API/Phase.lean`, `chargeQuantisation`, `PhaseLabel.integer_charge`; classical content: Pontryagin duality for the circle).

**What it does not do (II.5.5).** It proves no open step and adds no mathematics. It does not turn a problem into a running
system for you: the structure and its one inequality are the work. Arguments that use only the interface cannot settle P vs NP
(relativization, V.7), and the NP card inherits that. **[paper]**

---

## II.6 The arsenal and its lint

**Why it clicks.** Content-free results that more than one project uses should live once, and every use should be checkable for one
property: that nothing in it cannot run.

**The arsenal (II.6.1).** The arsenal is the set of transferable Lean results that need Mathlib, kept in the `im` repository
(`arsenal/`), pinned to Lean and Mathlib v4.34.0. It is imported from there and never copied (II.6.4). At the pinned commit its
modules are `Arsenal.R136a1`, `Arsenal.BSD` with its parts (`Algebraic`, `Analytic`, `Count`, `Hasse`, `EulerRat`),
`Arsenal.Rotation` (the one-box test, II.4) and `Arsenal.Rigidity` (II.4) **[paper]** (`arsenal/README.md`).

**R136a1 (II.6.2).** The one way to leave a statement open: `R136a1 "name" P` is `P` as a named hypothesis, never an axiom. A
theorem that needs it takes it as a hypothesis, so the system never assumes it. **[Lean]** (`Arsenal/R136a1.lean`, `R136a1`,
`R136a1.out`).

**The lint (II.6.3).** `arsenal/tools/lint.sh` is static, needs no network and no build. It fails unless: the toolchain is Lean
v4.34.0 and the one requirement is Mathlib at tag v4.34.0; every module imports only Mathlib or the arsenal itself; no module uses an
escape hatch (`sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `ofReduceBool`, `skipKernelTC`),
read in code only so prose stays free; and every module is reached from `Arsenal.lean`. It lists every part answered R136a1 by
name. **[paper]** (read from the script; run at the commit of `im` pinned in `docs/mass-gap/formal/lakefile.toml`, result "lint: OK
(10 modules; Mathlib v4.34.0 only; no escape hatch; 4 part(s) answered R136a1)", the four being `Euler product bound`, `Hasse`,
`the gate is shared across scales` and `weak Mordell-Weil`). A self-test (`tools/lint-selftest.sh`) plants one case per rule, and the full check (`tools/check.sh`) adds a build against Mathlib
and the kernel's axiom report for every declaration; both were run at the release commit (II.7).

**Shared vocabulary, imported and never copied (II.6.4).** What can be transferred moves to the `im` repository and is used from
there as a dependency, never vendored. Lean projects `require` the package by repository, subdirectory and commit. **[paper]** (the
first author's rule; `arsenal/README.md`, "Using it").

**What the lint is, and is not.** It certifies form: that everything stated is soundly constructed. It does not say that the
statements describe the world (Part I, R.1).

---

## II.7 The independent re-check

The Lean modules of this paper are checked by kernels other than the one that built them (`docs/unified/INDEPENDENT-CHECK.md`,
`tools/independent-check.sh`). Lean's own `leanchecker` replays each module's declarations into a fresh environment, and `nanoda_lib`,
a type checker written independently in Rust, checks an export of every declaration together with everything it uses **[Lean, re-checked]**
for the modules a run covered (below). A full run once established a trusted base, Mathlib and Lean core at the pinned commit,
recorded by hash in a stamp. Later runs re-check only the modules whose source or imports changed, against that stamp.

**What the runs covered.** A full run established the trusted base (Mathlib and Lean core at the pinned commit, recorded by hash
in `docs/unified/independent-check.stamp`); quick runs re-check every module changed since, against it. The last quick run covers
the source of this paper: `leanchecker` replayed every changed module with no failure, the axiom audit found no declaration resting
on anything beyond `propext`, `Quot.sound` and `Classical.choice`, and `nanoda_lib` checked the declarations of the changed modules
and everything they use with no type-checker error **[Lean, re-checked]**. IM's arsenal, imported at its pinned commit, is checked
like the project's own code and is never part of the trusted base; its own full check passes with 223 declarations on the three
standard axioms. The scan for escape hatches reads code only, as the arsenal's lint does, and finds none. Every run, with its
commit and numbers, is recorded in `docs/paper/REVIEW.md` (Record), and `tools/reproduce.sh kernels` repeats them (REPRODUCE.md).

**B. The tools the problems use.**

## II.8 One chain, the first three problems

The first three problems (Parts III to V) run along the same four links.

> **positivity -> a space -> an evolution on it -> a spectrum that the positivity pins**

| Link | Yang-Mills | GRH | P vs NP (sampling side) |
|---|---|---|---|
| 1. Positivity | reflection positivity of e^{-S} | Weil's pairing W(f * f~) >= 0 | positive weights on assignments |
| 2. Space | the Osterwalder-Schrader (OS) Hilbert space | the GNS space of Weil's form | L2 of the Gibbs measure |
| 3. Evolution | the transfer matrix e^{-H}, H >= 0 | translation in log-scale | the heat-bath operator, 0 <= P <= 1 |
| 4. Spectrum | gap = decay rate of correlations | real spectrum = zeros on the line | gap = fast mixing |

**Why it clicks.** Links 2 to 4 are free once link 1 is given: they are theorems of the same pattern in each column (the reflection
step is the Lean form for Yang-Mills, the finite Weil criterion for GRH, the finite spectral measure for the sampling side; II.9 to
II.10 give each). The whole
difficulty of each problem sits in link 1 for the hard case (Yang-Mills: a certificate at one scale; GRH: positivity itself; P vs NP:
the step from a certified class to all inputs). The rest of this part makes links 2 to 4 precise and adds the four tools that act on
link 1 or carry it across scales.

---

## II.9 Positivity builds a space

**Why it clicks.** A non-negative form is all you need to measure lengths, and lengths are all you need for a Hilbert space.

**Theorem II.9.1 (reconstruction from a positive form).** Let V be a real or complex vector space with a Hermitian form Q that is
positive semi-definite, Q(v, v) >= 0. Divide out the null vectors and complete: the result is a Hilbert space H with a map
Phi : V -> H such that <Phi u, Phi v> = Q(u, v). A linear map tau on V that is symmetric for Q and satisfies
Q(tau u, tau u) <= Q(u, u) descends to a bounded self-adjoint operator T on H with 0 <= <x, T x> when Q(u, tau u) >= 0.
**[classical]** (Gelfand-Naimark-Segal; Osterwalder-Schrader, Commun. Math. Phys. 31 (1973) 83-112 and 42 (1975) 281-305).
**[Lean]** in the abstract form used for Yang-Mills, over the reals (`RPData`: a symmetric real form, reflection positivity, a
symmetric positive step with bounded orbits): `M1/UVTVOS.lean` (`inner_Φ`, `T_symm`, `T_pos`, `contraction`).

**The three applications.**

* **Yang-Mills.** Q(F, G) = <theta F, G>, with theta the time reflection. Reflection positivity of the Wilson action, site and link,
  is **[Lean]** (`docs/mass-gap/formal/Positivity/`; the lattice has even extent N in the reflection direction, `wilson_rp`,
`wilson_rp_SU2`). The transfer step is tau. Positivity is given by construction.
* **GRH.** Q is Weil's explicit-formula pairing. In a finite model (finitely many zeros, closed under conjugation) the pairing is
  non-negative on every finite exponential sum **iff** every zero is on the line **[Lean]** (`GRH/Weil.lean`,
  `weil_criterion_finite`). For the zeta function itself the equivalence is Weil's criterion **[classical]** (Weil 1952; Bombieri
  2000). Positivity is *not* given by construction: it is equivalent to the conclusion.
* **P vs NP (sampling).** Q is the L2 inner product of a Gibbs measure with positive weights; the heat-bath operator is self-adjoint
  and positive, and every time correlation has a spectral measure on [0, 1] **[Lean]** (`Mixing/FiniteSpectral.lean`,
  `timeCorr_spectral`).

---

## II.10 Positivity pins the spectrum

**Why it clicks.** A self-adjoint operator cannot hide anything off the real axis, and a positive contraction cannot hide anything
outside [0, 1]. So "where is the spectrum" becomes "how fast do correlations decay".

**Theorem II.10.1 (decay rate = bottom of the spectrum).** Let nu be a finite measure on [0, inf) (the spectral measure of a vector for
H >= 0) and corr(t) = int e^{-tE} d nu(E). Then corr(n) <= K e^{-mn} for all n, for some K, **iff** nu gives no mass below m. The
admissible decay rates are exactly the m with nu([0, m)) = 0, and the best rate is the bottom of the support. **[Lean]**
(`Bridge/Spectral.lean`, `spectral_gap_iff`, `decayRates_eq`; discrete-time form `Mixing/TimeGap.lean`, `time_gap_iff`).

**Corollary II.10.2 (gap from reflection positivity).** In the setting of II.9.1 (the real form of the Lean data), let Blk be a
set of blocks that the step tau maps into itself, on which every correlation decays at rate m (Q(g, tau^n g) <= C_g e^{-mn}). Let F
be approximated by blocks f_k with Q(F - f_k, F - f_k) <= bB_k + 2 bA_k and bA_k, bB_k tending to 0 (the block bounds of the
UV-TV round: hypotheses `hsplit`, `hA`, `hB`). Then Q(F, tau^n F) <= e^{-mn} Q(F, F) for all n. **[Lean]** (`M1/UVTVOS.lean`,
`gap_of_RP`; `Bridge/OSLink.lean`, `gap_of_RP_spectral`, which starts from a spectral representation of the block correlations
instead of the decay). It is the quadratic-form form of "the transfer operator has norm at most e^{-m} off the vacuum"; the
identification of the vacuum complement is not part of the Lean statement.

**The three applications.** Yang-Mills: the mass gap is the decay rate of gauge-invariant correlations. GRH: if the generator of
the evolution on Weil's space is self-adjoint, its spectrum is real, which in the variable gamma = (rho - 1/2)/i is the statement
that the zeros are real; that such a space and generator exist for zeta is the Hilbert-Polya view and is **[open]** (IV.4.1). P vs NP: a
spectral gap of the heat-bath operator is fast mixing, hence polynomial-time sampling **[classical]** (the standard relation between
the gap and the mixing time, through the relaxation time; Levin-Peres-Wilmer, chapter 12; claim II.10.3), finite form
**[Lean]** (`Mixing/`).

---

## II.11 The bridge lemma: positivity locates singularities

**Why it clicks.** A sum of positive terms cannot cancel. So the first place where it blows up must be visible on the real axis,
where nothing can cancel.

**Theorem II.11.1 (Pringsheim, extension form).** Let F be holomorphic on Re s > x0, write its Taylor coefficients at real points
c > x0 as F^(n)(c) = (-1)^n M(c, n) with M real, and suppose F agrees on the right of x0 with a function holomorphic on a disc
about x0. Then for some real c > x0 and h >= 0 with c - h < x0, the series sum M(c, n) h^n / n! converges. **[Lean]**
(`Bridge/Pringsheim.lean`, `pringsheim_extension`; the disc form `pringsheim_hasSum`). Not in Mathlib before this project.

The Lean core needs no sign: it is Cauchy's theorem in Taylor form. **Positivity enters in the instances.** There M(c, n) is itself
a sum or integral of non-negative terms, such as sum_k a_k (log k)^n k^{-c} with a_k >= 0. Non-negative double series may be summed
in either order (Tonelli), and the inner sum is the original series evaluated at c - h. So the original series converges beyond the
point where it was supposed to stop, a contradiction. That is the whole mechanism: without positivity the reordering fails and a
singularity can hide off the real axis.

**Three instances, all [Lean]:**

1. **Landau's theorem.** An L-series with non-negative coefficients has a singularity at the real point of its abscissa of absolute
   convergence (`Bridge/Landau.lean`, `landau`). The same theorem is the endgame of the proof of RH in Lean by others, which this
   project read and did not rebuild **[external]** (IV.0).
2. **Laplace transforms of positive measures.** For a measure on [0, inf), the real edge of convergence of int e^{-st} d mu is a
   singularity (`Bridge/Laplace.lean`, `laplace_landau`).
3. **The mass gap.** The Laplace integral of the correlation measure of F (a finite measure on [0, inf), the spectral measure of F
   for H >= 0) converges for real s > -l0 and is singular at s = -l0, where l0 is the bottom of the support of that measure
   (`Bridge/Spectral.lean`, `resolvent_singular`). Its identification with the resolvent <F, (H + s)^{-1} F> is **[classical]**.

**What the bridge does not give.** It locates the *first* singularity of a positive object. It does not make an object positive.
Over function fields, one positive duality (the Hodge index theorem) gives both the axis of the functional equation and the
balance point 1/2; over the integers no such positivity is known **[open]** (`docs/rh-guide/bridge/BRIDGE.md`, section 0; claims
IV.2.5a and IV.2.5c).

---

## II.12 Contraction and data processing

**Why it clicks.** A lossy channel can only forget. If it forgets a fixed fraction each step, it forgets geometrically, and a
geometric rate is a gap.

**Definitions.** A stochastic kernel K moves probability distributions. Its contraction coefficient eta(K) is the largest factor by
which it shrinks the total-variation distance between two distributions (Dobrushin's coefficient). For a system of sites with local
conditional laws, the influence C(x, z) of site z on site x is the largest change in the law at x when only z changes; the column
sum of z is sum_x C(x, z).

**Theorem II.12.1 (data processing, composed).** eta(K) <= 1 for every stochastic kernel, and eta(K L) <= eta(K) eta(L). The same
kernel applied n times contracts by eta^n. **[classical]** (Dobrushin, Theory Probab. Appl. 1 (1956) 65-80; the strong
data-processing inequality). **[Lean]** on finite state spaces
(`Mixing/Chain.lean`, `contracts_kchain`, `contracts_kpow`, `tv_pushv_kpow_le_pow`).

**Theorem II.12.2 (Doeblin: a quantum per tick).** If K(x, .) >= eps nu(.) for every x, then eta(K) <= 1 - eps. **[Lean]** on
finite state spaces (`Mixing/Doeblin.lean`, `contracts_of_doeblin`, `doeblin_sharp`).

**Theorem II.12.3 (one finite check, decay everywhere).** If every column sum of the influence matrix is at most alpha < 1, the
heat-bath dynamics has a spectral gap: the spectral measure of every time correlation gives no mass above 1 - (1 - alpha)/N, with N
the number of sites. The condition is Dobrushin's (Theory Probab. Appl. 13 (1968) 197-224; Dobrushin-Shlosman 1985, uniqueness and
decay of correlations); the gap form is known in the literature on rapid mixing under Dobrushin's condition (Dyer-Goldberg-Jerrum,
Combin. Probab. Comput. 17 (2008) 761-779, states the mixing result; Hayes 2006 gives rapid mixing from a Dobrushin matrix of norm below 1; Wu 2006 gives the Poincare
inequality, a spectral gap, under Dobrushin's uniqueness condition) (claim II.12.3).
**[Lean]** for finitely many sites with finite spin spaces (`Mixing/FiniteSpectral.lean`,
`spectral_gap_dobrushin`; `Mixing/Link.lean`, `spectral_gap_of_column`). With exponential weights the same condition gives
exponential decay of spatial correlations **[Lean]** (`docs/mass-gap/formal/Attempts/R3/TailDecay.lean`, `theoremA_w`).

**The honest limit (II.12.4).** Doeblin gives a rate per channel. A site with k >= 2 neighbours needs the *sum* of the k influences
below one, and once the per-channel cost C is at least log 2, the sum of the Doeblin bounds k(1 - e^{-C}) is at least 1. The quantum
per tick does not by itself give a column below one. **[Lean]** (`Mixing/Chain.lean`, `column_sum_ge_one`, with the sharp threshold
`column_sum_lt_one_iff`).

**Uniformity along a chain (II.12.5).** If the same channel acts at every step (a homogeneous chain: translation invariance in the
transfer direction), the contraction coefficient is the same at every step; once eta < 1 at one step, the chain contracts like
eta^n. **[classical]** with the composition law **[Lean]** above. Read as DMP: "the uniformity is given by the arrow of causality"
**[reading]**.

**The three applications.** Yang-Mills: the gap mechanism reduces to one box of fixed physical size, uniformly over outsides; for a
grid the per-box cost must beat the path entropy, F_e(L) > log mu_4 (Part III.5). P vs NP: a column sum below one is polynomial-time sampling and, classically, counting (Part V). GRH: no contraction step is
known; the prime-by-prime extension has no slack to lose (Part IV).

---

## II.13 A strict sign gives a rate: the self-dual point

**Why it clicks.** If two quantities are dual to each other and the duality has a fixed point, then they cannot both be small: one of
them is at least the fixed-point value.

**Theorem II.13.1 (hand-over).** For 0 < Z_tw < Z put F_tw = -log(Z_tw / Z) and F_e = -log((Z - Z_tw)/(Z + Z_tw)). Then
F_e is the image of F_tw under a decreasing involution with fixed point log(1 + sqrt 2), and

  max(F_tw, F_e) >= log(1 + sqrt 2), about 0.881.

The bound is sharp, attained at Z_tw / Z = sqrt 2 - 1, where both free energies equal log(1 + sqrt 2) (from `elec_selfdual` and
`selfdual_cost`, II.2.4; no single theorem states the F-form). **[Lean]** (`Crossover/HandOver.lean`, `handover_ratio`,
`log_one_add_sqrt_two_le_max`; the duality `Flip/Floor.lean`, `elecF_eq_dual`).

**Theorem II.13.3 (the balance of the full turn).** Let z be positive on N >= 2 points and epsilon positive on N points, tied by
the two identities one turn gives: the values of epsilon add up to z at the base point, and N times epsilon at the base point is the
sum of the values of z. Then some nontrivial value of z or of epsilon is at most 1/(1 + sqrt N) of its base value, so some
nontrivial free energy is at least log(1 + sqrt N) **[Lean]** (IM, `Arsenal/FullTurn.lean`, `full_turn_balance`,
`full_turn_balance_log`). At N = 2 it is Theorem II.13.1. The bound is sharp: with every nontrivial twist ratio equal to x, the
electric ratio is (1 - x)/(1 + (N - 1) x), and the two meet at x = 1/(1 + sqrt N), the self-dual point of the N-step turn
**[paper]** (elementary algebra) (claim II.13.3).

**Theorem II.13.4 (the balance along a path).** Under the same identities the bound holds for the mean free energy over all
nontrivial values of one type, not only for their maximum **[Lean]** (`full_turn_balance_mean`, by the concavity of the logarithm).
So the maximum over sectors is a rate along a path that turns once through the sectors, the base point left out. This is the first
author's refinement, "a maximum over sectors is a rotation of a rate along a path up to the shared root" **[reading]**, exact in this
form, the shared root being the base point that every sector is measured against (claim II.13.4).

**Where it applies.** Any system with a strict inequality between a sector and its twist. In SU(2) Yang-Mills the strict inequality
holds at every coupling beta != 0 (`Flip/Strict.lean`, `su2_Ztw_lt_Z`), so every periodic SU(2) box with even time extent has a hand-over rate of at least 0.881 nats in
one of its two channels, given 0 < Z_tw **[Lean]** (`Crossover/HandOver.lean`, `su2_handover`, with the hypothesis 0 < Z_tw stated; the
integrand is positive, the formal step is not written). Reading: this is the precise form of I.7, "existence = non-existence + 1":
a sign with no rate becomes a rate at the self-dual point **[reading]**.

**What it does not give.** It is a statement about free energies of the whole periodic box (averaged over everything), not about the
influence of an arbitrary fixed outside on one box. And 0.881 suffices for a chain of boxes (two channels per box) but not for a
grid: in d >= 3 the number of ways a path can continue outweighs it (`Crossover/Containment.lean`, `path_entropy_beats_handover`,
**[Lean]**). Both gaps are named in Part III (III.4, III.5).

---

## II.14 The dichotomy: local, crossing flux, residue

**Why it clicks.** An obstruction to decay can only be of three kinds: short-range (it is forgotten), conserved (it cannot be
forgotten, so it must be paid for), or stuck inside one region (then it is a finite question about that region).

**Statement (II.14.1, the shape).** For a system split into regions, every piece of an obstruction is

* (a) **local**: forced by a few constraints; behind a collar of positive conditional mass it enters only as a boundary term;
* (b) **a crossing flux**: carried by a conserved quantity through the region's boundary; it cannot be screened;
* (c) **a residue**: inside one region; what remains is a percolation question: does the bad set span the region, or does it break
  into finite clusters with an exponential tail?

This is a proof strategy, not a theorem **[paper]** (`docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/DICHOTOMY.md`;
`docs/pnp/DICHOTOMY-TRANSFER.md`). Its exact pieces are theorems:

* **Gauss law mod 2.** For a Z_2 flux on a graph, the parity crossing the boundary of any region equals the charge inside, whatever
  the interior does; odd total charge is a contradiction **[Lean]** (`Proof/Crossing.lean`, `gauss`, `flux_fixed`,
  `unsat_of_odd`). The same law for centre sheets: a flux-carrying outside forces at least one sheet through the box, entering and
  leaving an even number of times (when every plaquette lies in an even number of cells) **[Lean]** (`Crossover/FluxRate.lean`,
  `exists_sheet_of_flux`, `even_card_fluxCells`).
* **Uncontained pieces weigh nothing.** A sheet that ends inside the box is not a closed configuration, so it has weight zero under
  every law carried by closed configurations **[Lean]** (`Crossover/Dichotomy.lean`, `not_uncontained`, `measure_uncontained`).
* **Every refutation crosses.** In every sound proof system whose rules have at most two premises, every refutation of an expanding
  formula contains a line sensitive to at least the expansion many variables, where "expanding" is two stated hypotheses (every
  proper subset of the blocks is satisfiable; boundary expansion for the middle sizes: each boundary variable makes its one block of
  the region true wherever that block is false, and the region's other blocks do not contain it) **[Lean]** (`Proof/Crossing.lean`,
  `cross_any_system_of_falsify`). For clause blocks both conditions hold whenever the variable occurs in exactly one clause of the
  region (`fixes_of_single`, `invisible_of_not_mem`), so the theorem covers CNF formulas with unique-neighbour expansion; for parity
  blocks it is `Tseitin.cross_any_system`. The argument is the measure argument of Ben-Sasson and Wigderson, machine-checked for every
  sound two-premise system.
* **Rarity and saturation do not overlap.** The regime where sheets are suppressed (their cost beats their entropy) and the regime
  where they saturate are disjoint (with entropy K' >= 2(d - 1) and E_min <= E, both cannot hold) **[Lean]**
  (`Crossover/Dichotomy.lean`, `window_gap`); that a route between them crosses a window where neither mechanism applies is the
  consequence read off this.

**The three applications.** Yang-Mills: (b) is exact, (a) fails uniformly at the SO(3) cut, (c) is the open window (Part III).
P vs NP: the crossing is universal, but its *cost*, the price of naming the conserved quantity in the system's lines, is not; that
cost is the open lower bound (Part V). GRH: the analogue of (b) is the zeros on the line, "pure oscillation" **[reading]**; no
dichotomy proof exists there.

---

## II.15 The native optimization method

**Why it clicks.** A cost that comes in whole units cannot fall forever. Lower it by one unit per improving pass and the method must
stop, at an irreducible core.

**Theorem II.15.1 (quantized descent arrives).** Let f be a map on any set and mu a natural-number measure with mu(f x) < mu(x)
whenever f x != x. Then f has a fixed point after at most mu(x) steps from x. **[Lean]** (`Native/Method.lean`, `fixed_after`,
`reaches_floor`). Without quanta it fails: x -> (x + 1)/2 strictly decreases toward 1 and never reaches it (`real_never_arrives`).

**Theorem II.15.2 (a true contraction for depth).** Pairwise merging of adjacent layers turns d layers into ceil(d/2); after
ceil(log2 d) passes one layer remains. **[Lean]** (`Native/Method.lean`, `iterate_clog_pairUp`).

**Measured.** Applied to this project's own proof chains, the per-layer kernel cost is finite and bounded by the size of the finite
building blocks it evaluates (0.17 to 1.4 ms per layer in the deepest DMP chain; about 0.3 ms per recipe line for a reflected
check). **[numerical]** (`docs/pnp/NATIVE-METHOD.md`, section 0).

**The three applications.** P vs NP: the method reduces any refutation to an irreducible core; whether that core is always of
polynomial size is the open question N1 (Part V). Yang-Mills: the same "quantum, then arrival" shape is the Doeblin rate per tick
(II.12.2). GRH: the integer multiplicities of zeros and prime powers are the quanta on the prime side **[reading]**.

---

## II.16 What the tools do not do

None of II.9 to II.15 creates positivity. Each starts from a positive weight, a positive pairing, a positive cost or a strict sign,
and carries it: into a space, into a spectrum, across a chain, across a boundary, down to a floor. The open step of each problem is
the place where that starting positivity is known locally, or in a model, and must be established for every case. Part X states
this once (section 4). The six sections II.1 to II.6 are the *form layer*: the part of the machinery that says
nothing about content and so serves every problem. II.16 holds for them too.

---

## II.17 Where Part II ends

The tools II.9 to II.15 carry a positivity. The form layer II.1 to II.6 carries a certificate and its uncertainty, says when the
carrying settles, and says where the one open statement of a problem goes. None of it supplies a positivity, and none supplies a
floor. Part X says why each problem's open step stays open.
