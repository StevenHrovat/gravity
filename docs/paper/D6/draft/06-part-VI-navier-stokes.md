# Part VI. Navier-Stokes: three cards and the claimed certificates

*Draft 6. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/ProofPhase/`; notes relative to
`docs/unified/`. Claim labels (VI.n) are listed in `../CLAIMS.md`.*

**Plug in here.** Gives: three Navier-Stokes cards, and why the energy ledger alone is no certificate. Needs: II.4.1
and II.1. Route: off both routes. VIBE coefficient: the scales are dyadic, 2^-k, each a halving of length, and the energy-only model
box fails at some dyadic scale (`ns_not_complete`) **[Lean]**.

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

**The full text.** This part is contracted. Every derivation it leaves out is in the full Draft 6 at the git tag `d6-full`, and in Draft 5 section by section; every claim keeps its row, status and evidence in `../CLAIMS.md`.
