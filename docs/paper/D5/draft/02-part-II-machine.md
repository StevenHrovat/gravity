# Part II. The machine, and the tools the problems use

*Draft 5, 2026-11-25 (machine-first). Section A is the machine, in the order a reader needs it: running systems and the ledger, the encoder, the settle theorem, the one-box test, the API, the arsenal, the independent re-check. Section B is the tools the problems use, each once in its most general form. Lean paths are relative to `docs/mass-gap/formal/ProofPhase/`; claim labels (II.n.m) are listed in `../CLAIMS.md`.*

**Where to start.** Part II has one statement at its centre, II.4.1: every observable system has a one-box description,
DMP-complete exactly when its claim holds at every tick, with a route to the proof. A reader who wants the headline first can read
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
  -1, the identity or the half-turn, and every real number is its modulus times 1 or -1, so ordinary multiplication is a cost times
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

### II.4.1 The front door: every observable system

An *observable system* has states, one step and its own claim at
each state, a decidable proposition. Decidability is classical here, so this is no restriction: every proposition is an observable
system with one state. Its one-box description is a box of the same API with the same states and step, whose marker always asserts
the claim (*inside*) and whose gate reads whether the claim is true; the marker is not read off the gate, so II.4c's vacuity is
avoided, and the box is correct at a state exactly when the claim holds there (`correct_iff`).
Four facts hold for every observable system **[Lean]** (IM, `Arsenal/Observable.lean`; claim II.4g):

* *Representation* (`box_complete_iff`): the description is DMP-complete from a start exactly when the claim holds at every tick.
  This is by construction, a restatement.
* *A route to the proof* (`route`, exact along the run `route_iff`): the claim at the start and a step that keeps the claim make the
  description DMP-complete. This is induction on the tick.
* *Certified universally* (`route_everywhere`): once the route is shown, the claim is certified at every tick and, with the gate
  shared across scales (the named hypothesis R136a1, never an axiom), at every tick of every scale.
* *Falsifiable* (`refuted_by_tick`): one tick where the claim fails refutes it.

When the observation is a reading against a margin (`ofReading`) and the reading is a coefficient hidden in a sum of N powers of a
root of unity, one full turn computes it exactly, so the gate can be read by one turn (`turn_gate`, II.2.7). The cards of Parts III
(Yang-Mills), IV (GRH), V (NP versus coNP), VII (BSD) and VIII (Hodge), and the tick box of Part IX (GU), are observable systems:
the tick box of a sequence of statements passes exactly when the observable system with the ticks as states, the successor as step
and the statement as claim has a DMP-complete description (`ETM/CardBox.lean`, `tickBox_observable`) **[Lean]**. Part VI has no card
of its own (VI.8). A route has two parts, and where the open part sits differs. On a card the claim is the same at every tick, so the
step is free and the whole open statement is the start. On the boxes with a gate factor of their own, the Yang-Mills box (III.12)
and the model Navier-Stokes box (VI.8), the step carries the content. So the route has one form everywhere, and the parts show where
its open part sits. Two systems run side by side give a system whose routes reassemble (`prod`, `route_prod`) **[Lean]**, so a larger
proof is the parts reassembled as the API guides. Appendix T runs all of it on binary words.

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
