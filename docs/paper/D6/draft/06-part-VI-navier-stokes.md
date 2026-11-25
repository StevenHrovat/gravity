# Part VI. Navier-Stokes: three cards and the claimed certificates

*Draft 6. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/ProofPhase/`; notes relative to
`docs/unified/`. Claim labels (VI.n) are listed in `../CLAIMS.md`.*

**As a statement checked step by step (II.4.1).** Navier-Stokes has three cards (VI.2: route I, regularity, the A/B
dichotomy), each checked at every step of its card box, with the open part in the base case; the paper does not assume any of
them **[Lean]** for the card boxes (`tickBox_observable`). The model box of VI.8, built from the energy bound alone, is separate: its
statement is that the energy-only factor stays within the margin at every dyadic scale, and that fails at some scale
(`ns_not_complete`) **[Lean]**. What fails is the energy ledger as a certificate, not regularity.

## VI.0 What is proved, by whom, and what this part does

**The Clay problem** (Fefferman's official statement) asks one of four things. For three-dimensional incompressible Navier-Stokes
with viscosity nu > 0 and force f:

* **(A)** On R^3, with **zero force**, every smooth, divergence-free datum whose derivatives decay faster than any power has a smooth
  solution for all time with bounded energy.
* **(B)** The same on the torus R^3/Z^3.
* **(C)** On R^3 there are a smooth, rapidly decaying datum **and a smooth force** for which no such global solution exists.
* **(D)** The same on the torus, again with a force.

A proof of any one wins the prize **[classical]**. Two points matter below. (C) and (D) allow a force, so a forced blowup of the
admitted class would settle (C) as stated. A blowup with **no** force disproves (A) (or (B)) and so proves (C) (or (D)) with f = 0.

**State of the problem (2026-11-24).** Two claimed proofs of blowup were posted in autumn 2026. Neither is refereed, and neither is
checked in this project.

* **OpenAI, 8 September 2026:** blowup with a smooth, compactly supported force. It addresses (C) and (D) **[external,
  unverified]**.
* **Alpoge and Buckmaster, 20 November 2026:** blowup with **no force**. It addresses (A) and (B). It rests on a numerical
  certificate that is **announced, not released** (only its hash is public). **[external, unverified, certificate unreleased]**.

If either claim holds, the Clay problem is answered by others, in the direction of blowup. **This part proves no statement about
the real Navier-Stokes equations.** The status of the problem in this paper is: (A) and (B) are open here, and an external claim
asserts that they are false.

**What this part does.** It puts Navier-Stokes on the DMP API as a card (VI.2), and proves in Lean, as a skeleton, what the form
layer says about the two possible blowup routes and about regularity (VI.3). It records what is borrowed and its exact status
(VI.4), states the one open step (VI.5), and checks the restatement against Perelman's proof of Poincare (Appendix A). The Lean modules
contain **no Navier-Stokes object**: nothing in them is about the equations themselves.

## VI.1 The problem as stated, and what is known

**VI.1.1 No-go results** **[classical]** (recalled from the literature; not re-read for this draft).

| Result | What it rules out |
|---|---|
| Leray 1934: a singularity at T* forces `sup abs(u) >= c (nu/(T* - t))^{1/2}` and `norm(grad u)_{L^2} >= c (T* - t)^{-1/4}` | blowup slower than these rates |
| Necas, Ruzicka, Sverak 1996; Tsai 1998: no nonzero backward self-similar solution `(T* - t)^{-1/2} U(x / sqrt(T* - t))` with `U` in `L^3` (Tsai: `L^p`, `3 < p < infinity`, and under local energy bounds) | exact self-similarity at the Leray scaling |
| Caffarelli, Kohn, Nirenberg 1982: the singular set of a suitable weak solution has zero one-dimensional parabolic measure | singularities along curves; isolated points remain |
| Escauriaza, Seregin, Sverak 2003; Seregin 2012: a solution bounded in `L^infinity_t L^3_x` is smooth; at a singular time the `L^3` norm must tend to infinity | blowup with a bounded scale-invariant norm |
| Axisymmetric Type I exclusion (Chen-Strain-Tsai-Yau; Koch-Nadirashvili-Seregin-Sverak) | axisymmetric Type I blowup |
| Chae-Wolf; Pineau-Vicol (as reported by Alpoge-Buckmaster): a smooth backward discretely self-similar solution, continuous in time with values in `L^p`, `p` in `[3, infinity)`, obeys the Type I bound; a nonzero one with the Type I bound needs a period bounded below by a number depending only on the profile's Type I constant (Pineau-Vicol: also for rotations by a small angle) | discretely self-similar solutions with a too-small period |

What these leave open: **discretely self-similar** solutions (the shape repeats after a fixed zoom), asymptotically self-similar
solutions, and Type II rates.

**VI.1.2 Tao's averaged equations** **[classical]** (Tao, J. Amer. Math. Soc. 29 (2016)). Replace the nonlinearity by an average of
rotated and dilated copies. The average keeps the energy identity and the standard estimates, and the averaged equation blows up in
finite time. So a proof of global regularity must use finer structure of the true nonlinearity than the energy identity and those
estimates.

**VI.1.3 Numerical evidence by others** **[external]**. Hou (arXiv 2107.06509, 2021, revised 2022) reports an axisymmetric scenario
with smooth data: vorticity growth of about 10^7 with nearly self-similar singular scaling (the abstract's words; the constant
viscosity and the Leray-type rates are as the notes recall, not re-read). It is numerical evidence, not a proof. Strict Type I axisymmetric blowup is excluded (VI.1.1), so a singular scenario would have to deviate from the observed rate;
the tension is noted here, not resolved.

## VI.2 The card

The DMP API (`docs/unified/API.md`) gives every problem one shape: a well-defined input, a proved structure on it, and one named open
step in a slot, with external inputs in their own slot. Navier-Stokes has three cards in `Unified/NavierStokesAPI.lean`
(namespace `ProofPhase.API.NavierStokes`). The table fills the API's template.

| API concept | Navier-Stokes | Lean |
|---|---|---|
| **Input** | route I: the perturbation states, the period map, the size (rescaled `H^1`), a contraction constant `rho`, a quadratic constant `C`, a ball radius `delta` with `rho + C delta < 1`; route II: a profile certificate and a trajectory; regularity: a chain over dyadic scales | `DSSInput`, `RouteIInput`, `DyadicInput` |
| **Running system** | route I: states in the ball, one step is one period, factor `rho + C size`, mass the perturbation size | `system`, `contracting` |
| **Chain** | regularity: the quantity carried to dyadic scale `2^{-k}`, cost the share dissipated per scale, floor the share the transfer adds back | `regularity` |
| **Uncertainty** | route II: the perturbation, factor `q + C M`, fresh uncertainty the profile residual plus the viscous term | `eulerUncertainty`, `routeII_bounded` |
| **Open-step slot** | route I: `PeriodContraction`; regularity: a uniform dissipation cost per dyadic scale above the transfer floor; the tie: the certificate | `PeriodContraction`, `regularity`, `abProblem` |
| **External-input slot** | Alpoge-Buckmaster's Theorems 7.1 and 1.1 and their Lean library | `ABInterface.thm71`, `.thm11`, `.formal` |
| **Computable layer** | the window decision; the settle count | `windowQ`, `windowQ_correct`, `settles_by` |

The three cards, in the card shape:

| Card | Input | The one open step | Conclusion | External input |
|---|---|---|---|---|
| **Route I** (`routeI`) | a non-steady periodic profile of the zoomed equation at the Leray scaling, and a perturbation in a ball | `PeriodContraction`: one period contracts the perturbation, after finitely many directions are removed by the datum **[open]** | the perturbation settles onto the profile within every epsilon; the periods fill the finite time 1; the `H^1` amplitude tends to infinity; the profile is not steady | none in the card; the content is what a certificate supplies |
| **Regularity** (`regularity`) | a chain over dyadic scales | every dyadic scale dissipates a uniform cost above the transfer floor **[open]** | the carried quantity decays at a positive rate and is summable over all scales | none |
| **External tie** (`abProblem`) | the interface `ABInterface` | the Alpoge-Buckmaster certificate satisfies their Appendix B (unreleased) **[open]** | not (A) and not (B), so (C) and (D) with zero force | their Theorems 7.1 and 1.1 and their Lean library, as `External` fields |

Nothing is an axiom. An `OpenStep` or `External` slot is an ordinary hypothesis, and neither appears in the axiom audit. The three
statements of the interface (a certificate exists; a profile exists; Fefferman's (A); (B)) are **named, not defined**: this library
has no Navier-Stokes object. Replacing the names by real definitions is the first item of the audit (VI.5).

## VI.3 What is proved

All of this is **[Lean]**, standard axioms only (`docs/unified/navierstokes-axioms.log`: 52 declarations on the three standard
axioms, 4 on none; the source contains no `sorry`, `admit`, `native_decide` or `axiom`). None of it proves a statement about the
equations. Each result says what the ledger gives from a hypothesis.

### VI.3.1 The window

Zoom at the singularity's own rate. If the singular region shrinks like `(T* - t)^alpha`, the viscous term in the zoomed frame has
the weight `(T* - t)^{1 - 2 alpha}`. The local energy near the singular point scales like `(T* - t)^{5 alpha - 2}`. The scalings are
**[classical]**; the arithmetic is **[Lean]**.

| `alpha` | Viscous floor | Local energy | Verdict |
|---|---|---|---|
| `> 1/2` | grows without bound (`nsViscous_tendsto_atTop`); no one-scale certificate covers all steps (`ns_no_uniform_certificate`) | bounded | excluded |
| `= 1/2` | constant (`nsViscous_half`): part of the zoomed equation; Type I (`ns_typeI_iff`) | bounded | **route I**: the Leray end |
| `2/5 <= alpha < 1/2` | shrinks (`nsViscous_le`), summable over steps (`nsViscous_summable`) | bounded (`ns_energy_window`) | **route II**: Type II |
| `< 2/5` | shrinks | unbounded | excluded |

`ns_window` (`Unified/NavierStokes.lean`) says that a bounded viscous floor and a bounded local energy hold together exactly for
`2/5 <= alpha <= 1/2`. `nsViscous_bounded_iff` says the floor is bounded exactly when `alpha <= 1/2`.

The window decision runs. `windowQ` sorts a rational exponent into one of the four rows, and `windowQ_correct`
(`Unified/NavierStokesAPI.lean`) proves the computed answer right for the model's statement (the exponents of the table): "inside" exactly when the viscous floor and
the local energy are bounded, "Leray" exactly when the Type I bound holds as well (`windowQ_admissible_iff`, `windowQ_leray_iff`,
`windowQ_half`). This follows the API's rule for a new instance: the decision runs, and a theorem proves it right.

### VI.3.2 Route I: the Leray end, a discretely self-similar profile

The hypothesis is a structure, `LerayDSSCertificate`: a profile `W` (with values in an arbitrary type) that is periodic in zoomed
time with period `S > 0` and **not steady**; a number `A > 0`, meant as a lower bound on the profile's rescaled `H^1` size (the
structure carries no norm, so `A` is only a constant); a contraction `0 <= rho < 1` and a constant `C >= 0`. The period inequality
`M(n+1) <= rho M(n) + C M(n)^2` is not a field of the structure: it is a hypothesis of the theorems below and the open step
`PeriodContraction` of the card. It is the period map on the complement of finitely many directions, which the choice of datum
removes.

The ledger then proves (`ns_blowup_of_dss`):

* the perturbation decays geometrically, `M(n) <= (rho + C delta)^n delta`, for a start `M(0) <= delta` with `rho + C delta < 1`
  (`ns_dss_converge`): the solution converges to the profile;
* infinitely many periods fit into the finite time 1 (`ns_period_hasSum`, via `nsPeriodLength`);
* the amplitude `e^{nS/4} (A - M(n))` tends to infinity (`ns_dss_amplitude`); this defined sequence stands for the rescaled `H^1`
  size times `e^{nS/4}`, whose growth is the rate `(T* - t)^{-1/4}`, Leray's lower bound; that the sequence is the `H^1` norm of a
  solution is **[paper]**, not in the Lean;
* the profile is not steady (`LerayDSSCertificate.not_steady`), so exact self-similarity is not used.

In ledger language: the free flow pays `S/4` per period at floor 0 (`ns_free_flow_pays`, an identity for the supplied decay
`e^{-k S/4}`), which is the ledger form of the subcriticality of `H^1` (VI.3.2c); the contraction `rho` is a separate hypothesis. A period factor `0 < rho < 1` is a cost `-log rho` above floor 0 for one step type
(`ns_dss_costAboveFloor`); the zoomed equation is autonomous, so one period is every period.

The API card `routeI` assembles this: from `PeriodContraction` (the open step) it concludes settling onto the profile (the API's
`settle_everywhere`), with the period count from `settles_by`, together with the three consequences above. Settling in the zoomed
frame is blowup in real time through the scaling `T* - t = e^{-s}` (here `T* = 1`, `ns_period_hasSum`) **[paper]**; no
statement about the equations is in the Lean. The open step is the content a certificate would supply (VI.5).

### VI.3.3 Route II: inside the window, viscosity as a shrinking residual

`EulerProfileCertificate` is the Chen-Hou one-scale certificate (damping `q`, nonlinear constant `C`, profile residual `epsilon`,
focusing margin) with the exponent in `2/5 <= alpha < 1/2` and the trapping condition raised by the viscosity:
`(1 - q)^2 >= 4 C (epsilon + nu)`. From it the ledger proves trapped perturbation, a finite `T*` and unbounded amplitude
(`ns_blowup_of_euler_profile`), stated also as a cost above a floor (`ns_euler_gap_of_costAboveFloor`). Below the Leray scaling the
viscous term is a summable fresh uncertainty, so even with no damping its accumulated total stays bounded
(`ns_viscous_transport_bounded`); at `alpha = 1/2` it is a constant fresh uncertainty and accumulates without bound
(`ns_viscous_transport_unbounded_at_leray`). The API gives the same bound in its own form (`routeII_bounded`):
`M(n) <= M(0) + 2 (epsilon + nu)/(1 - q)`.

The consequence for the two routes, in the ledger's transport bound: at the Leray scaling a perturbative treatment of viscosity at
cost = floor fails (the constant fresh uncertainty accumulates), so in this bound the viscous term has to sit inside the profile
equation, which is route I. This is a statement about the bound, not about the equations. **No route II profile is known [open].**

### VI.3.4 Why the energy ledger cannot decide

The energy identity is one global sum: total dissipation is at most the start energy. A summable budget never pays a uniform
positive cost per step (`ns_energy_budget_not_costAboveFloor`), and dissipated shares whose partial sums stay below the start energy
are such a budget (`ns_energy_identity_not_costAboveFloor`, `energy_cannot_fill`). Per dyadic scale the viscous cost grows like
`nu 4^k` while the transfer bound that energy alone allows grows like `K 2^{5k/2}`; whatever `nu` and `K > 0`, the bound overtakes the
cost at some scale (`dyadic_supercritical`). The scalings are **[classical]** (Bernstein); the arithmetic is **[Lean]**. In two
dimensions the same count is critical, which is why 2D Navier-Stokes is regular **[classical]**.

So the regularity card's slot cannot be filled from the energy identity. This is the ledger form of Tao's averaged equations (VI.1.2):
they keep this identity and blow up.

### VI.3.5 The blueprint: Chen-Hou, as a skeleton

Chen and Hou proved stable, nearly self-similar finite-time blowup for 2D Boussinesq and for 3D axisymmetric Euler with smooth data
and a solid wall, by a computer-assisted proof **[external]** (arXiv 2210.07191 and 2305.05660). It is not Navier-Stokes: there is
no viscosity, there is a wall, and the flow is axisymmetric. The project restates its ledger in `Unified/Blowup.lean`:

* if the one-step certificate holds (`(1 - q)^2 >= 4 C r`) and the start is in the ball, the perturbation stays in the ball forever
  (`trap`, `trap_radius`, `trap_of_gap`), and the threshold is sharp (`escape_of_below`, `escape_pos`);
* the certificate follows from `CostAboveFloor` of `1 - q` over `2 sqrt(C r)` for one step type (`gap_of_costAboveFloor`: the strict
  cost condition implies the trapping gap; the converse and the boundary case are not proved);
* under a focusing margin the real durations are summable, the total time `T*` is finite, and the amplitude is unbounded
  (`durations_pay`, `arrival`, `amplitude_unbounded`, assembled in `blowup_of_certificate`);
* every rescaled step adds one fixed quantum to the Beale-Kato-Majda count **[reading]**: the Lean content is only the identity
  `boundary_quantum` (the sum of the inverse durations times the durations is n); the Beale-Kato-Majda count is not defined in Lean.

All of this except the last item is **[Lean]** for the skeleton. The partial differential equation enters only as the step inequality, a hypothesis. That
BKM's integral is infinite exactly when smooth continuation fails is **[classical]**.

## VI.4 What is borrowed

### VI.4.1 Alpoge and Buckmaster: the unforced claim **[external, unverified, certificate unreleased]**

The claim, as the notes read it from the paper itself (79 pages, version of 20 November 2026):

* **Statement.** Smooth, compactly supported, divergence-free data on R^3, and smooth data on the torus, whose **unforced**
  solutions blow up in finite time. The paper says this disproves (A) and (B).
* **Route.** A profile of the Navier-Stokes equations in self-similar variables, with the viscous term inside the profile equation,
  periodic in zoomed time up to an isometry: backward discretely self-similar, the case Bradshaw and Tsai left open. Their Theorem
  1.1 says one such profile gives blowup at Leray's rate, stable in finite codimension. Their Theorem 7.1 says an approximate profile
  with explicit inequalities (a **certificate**) gives an exact profile nearby. This is exactly route I of VI.3.2.
* **The candidate.** Found by Newton's method after continuation. Not axisymmetric: invariant under rotation by `2 pi/19` about one
  axis and by `pi` about another. Period about 0.36.
* **What is not available.** The certificate is **not released**; the paper gives only its SHA-256 hash,
  `3f7a335b84b6c7631742cacc5343dfcd11cf72f5221ff79b2b9268790b4b22c5`, and says it will be released. The interval-arithmetic check
  (128 bits) is outside their formalisation and not in their repository. Their Lean library (about 2,270 files and 600,000 lines, Lean
  4.33) was patched on 20 November and the patched package was not rebuilt, per its README. Its formal Theorem 1.1 has no rate, and
  the paper's prose no longer follows the Lean proof.
* **Expert status.** The notes record Tao's blog post of 20 November: technically human-readable, broadly clear strategy, a
  professional write-up still needed. No referee report exists.

This project did **not** rebuild their library, did **not** see the certificate, and did **not** check any of their inequalities. It
reads the claim, records it, and uses it only as an external input in a named slot.

How their profile avoids the no-go results (VI.1.1) **[external]**: it depends on zoomed time, so Necas-Ruzicka-Sverak and Tsai
(which exclude steady profiles) do not apply; it is bounded in weak `L^3` but not `L^3`, consistent with Escauriaza-Seregin-Sverak;
it is not axisymmetric; its period lies above the Chae-Wolf lower bound, with the constant not checked here.

### VI.4.2 OpenAI: the forced claim **[external, unverified]**

For every `nu > 0`, a smooth force with compact support, a compact set, and a smooth solution on `[0, 1)` with zero initial velocity
and bounded energy whose sup-norm is unbounded as `t -> 1`; the paper says this establishes (C), and (D) by a corollary. An
independent build record of its Lean proof (posted on Zenodo on 10 October 2026, Lean v4.34.0-rc2, as the notes record it; the record
was not found again for this draft) reports the three standard axioms, no `sorry`, and a match to a public formalisation of
(C) and (D) **[external, not rebuilt here]**. A preprint (arXiv 2610.08144) shows lemma-level places where the Lean proof is not a
faithful translation of the written one, and expressly claims nothing about the written proof's correctness **[external]**. Because a
force is allowed in (C) and (D), this claim, if it holds, answers (C) and (D) as stated but says nothing about (A) and (B), which have
zero force.

### VI.4.3 Smaller programmes **[external]**

Petrillo and Glimm (arXiv 2609.23868) set a target for a computer search for unforced blowup; its implications are proved in Lean over
Mathlib with no Navier-Stokes object. Cheskidov, Dai and Palasek (arXiv 2609.26790) prove cascade blowup in dyadic shell models, not
in Navier-Stokes. The companion unforced Euler claim by Alpoge, Buckmaster and Coiculescu was not read.

### VI.4.4 The logic point **[classical]**

The first author's scope decision is that a blowup that cannot be ruled out is in itself enough for an existence to be constructed where it
blows up. The exact statement behind it is Goedel's completeness theorem: if ZFC plus "some smooth datum blows up" is consistent, a
model of it exists. Three senses of "cannot be ruled out" must be kept apart: (a) one method cannot rule it out (the energy method;
VI.3.4); (b) the axioms cannot refute it (independence; **not known** for Navier-Stokes); (c) it is not ruled out for the real
equations over the real numbers. A completeness model for (b) may be nonstandard, so it settles nothing about the actual equations.
Only a proof settles the Clay question. The two 2026 claims are proofs of that kind: an explicit datum and an argument, not a
completeness model. If correct, they are the first author's "existence constructed where it blows up", in the standard sense.

## VI.5 The one open step

**The open step of the card.** The route I card has one open step: **`PeriodContraction`. One period of the zoomed flow, from a
non-steady periodic profile at the Leray scaling, contracts the perturbation, on the complement of finitely many directions removed
by the datum, in a real norm, with `rho + C delta < 1`.** In the external tie, this is the statement "the Alpoge-Buckmaster
certificate satisfies their Appendix B". It is exactly what their unreleased certificate claims to supply. Everything else in the
card is proved (VI.3) or is a named external theorem (VI.4.1). **[open]**

**The other slot, stated exactly.** The regularity card names what regularity would need: **every dyadic scale dissipates a uniform
cost above the transfer floor, from the true nonlinearity.** The energy identity cannot supply it (VI.3.4). If the 2026 claims hold,
the slot cannot be filled for some data. **[open; false if the unforced claim holds]**

**What this does to the problem.** The API does not settle Navier-Stokes as regular. It settles blowup in the Leray window once one
named slot is filled (the period contraction), which is a claimed but unreleased certificate today. The mechanical answer is
therefore: **open, with the open step located and an external claim asserting it holds.** Route II has no candidate **[open]**. What
continues past `T*` for a blowup solution is **[open]** (weak solutions are not unique in general; for Ricci flow the same question
is a theorem, A.1f).

**What would discharge the external inputs by import.** The notes list twelve audit items, none done. The ones that change the
status of the tie:

1. Replace the named statements by real definitions of (A) and (B) (a pinned public formalisation), and check in one environment
   that their formal Theorem 1.1 has exactly the type "not (A) and not (B)", word by word against Fefferman.
2. Rebuild their library after the 20 November patch; run the axiom audit on the comparator statements; search for `sorry`,
   `native_decide`, custom notation that could change a statement's meaning.
3. When the certificate is released: check its hash against the published one; check it has the form of their Appendix B; re-verify
   the Appendix B inequalities with an **independent** interval implementation. This is the step that today rests on one computation
   by the authors.
4. Identify the two derivation steps that their paper says are proved in the Lean and not in the prose.
5. Map their Appendix B row by row onto `LerayDSSCertificate`.

Until these are done, everything in VI.4.1 stays **[external, unverified]**. The project's policy is to cite and audit, not vendor.
An independent construction of the profile from scratch is beyond reach now: it is a genuinely three-dimensional, time-periodic
shape with an operator-level certificate at 128-bit precision **[reading]**.

## VI.6 DMP readings attached to this part (all [reading])

* **A blowup is a certificate that infinitely many steps fit in finite time.** The finite check at one scale is what makes the
  packing geometric; `T*` is the boundary where the smooth description ends, and the profile is what crosses it. This is the
  hand-over of the form layer run in reverse.
* **The same theorem as the mass gap.** `summable_of_gap` gives a finite correlation length in Yang-Mills and a finite `T*` here
  (Lean for both uses; the parallel is the reading).
* **Scale invariance as the arrow of causality.** Because the zoomed equation is autonomous, the set of "outsides" has one element:
  the same step at every scale, so the for-all over steps costs nothing.
* **"Does not run, hence blows up."** In ledger terms the energy ledger cannot pay a uniform cost per scale (VI.3.4). The
  first author's reading came after both claims were public (8 September and 20 November), so it agrees with the side the claims
  assert and is not a prediction made before them. It proves nothing: a method's failure to exclude blowup is not blowup. The
  claims, if correct, prove it by a certified profile. Running has a precise statement: an object runs on DMP when the running-state
  hypothesis R of Part X 4.2 holds (the first author's definition, X.64b). The first author's reading: the whole process is
  described and Navier-Stokes does not build in it (the energy ledger cannot pay a uniform cost per scale, VI.3.4a and VI.3.4b,
  **[Lean]**), so it does not run, and blowup is the expected consequence. The negative result is the expected one, and it
  makes the framework falsifiable: global regularity would refute it **[reading]** (VI.7e). Blowup of the real equations is still
  the card's open step (VI.5.1, **[open]**); in the settling machine a missing floor gives undecidability (II.3), so the step from
  "does not run" to blowup is the reading, not a theorem. The model box of VI.8 shows the wrong marker for the energy-only ledger
  **[Lean]** (model, VI.7g). It covers the energy-only ledger, not an
  actual solution with a better transfer bound **[reading]** (VI.7h).
* **Settle means opposite things on the two cards.** In the API, "settle" means the carried quantity dies out. For regularity that
  quantity is the cascade, so settling means regular; for route I it is the perturbation from the blowup profile, so settling means
  blowup. The same theorem answers opposite physical questions.

## VI.7 What would close it

If the Alpoge-Buckmaster certificate is released and verifies independently, the route I card's open step is discharged, (A) and (B)
fail, and the Clay problem is answered in the direction of blowup, by their work, with this part supplying the ledger skeleton and the
audit. If the certificate fails an inequality, the open step stays open and the regularity slot stays as it is. Either way the paper
changes in one place per card, as X.8 describes. A proof of **regularity** would
have to fill the regularity slot from the true nonlinearity, which the energy identity cannot do (VI.3.4), and which the unforced
claim, if true, makes impossible for some data.

---

## VI.8 The box in the one-box test

**The model box.** `nsBox nu K theta` has the dyadic scales k as its ticks, floor 0, margin theta < 1, and the marker "inside" (the
claim "regular") at every scale. Its gate factor at scale k is the energy-only transfer bound K 2^(5k/2) over the viscous cost
nu 4^k, clipped to [0, 1] (`nsFac`) **[Lean]** (`ETM/RotationInstances.lean`, `nsFac`, `nsBox`).

**What the test gives.** Since 2^(5k/2) outgrows 4^k, the factor reaches 1 at some scale (`nsFac_eq_one`); the gate reads outside
there while the marker says inside, so the box is not DMP-complete (`ns_gate_outside`, `ns_wrong_marker`, `ns_not_complete`)
**[Lean]** (claim VI.7g). This is the classical supercriticality of the energy (VI.3.4), formalised. The box is a model, built from
the energy bound alone; it is not the box of any of the three cards of VI.2, whose boxes pass exactly when their open steps hold
(`cardBox_complete_iff`). So the test says that the energy ledger cannot certify regularity, and nothing about the equations
themselves.
