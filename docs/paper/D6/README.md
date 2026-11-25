# Draft 6 of GUID v8 (`D6`)

Draft 6 grew from Draft 5 and adds to it. Draft 4 is the merged state and is never edited: it stays whole in `docs/paper`. Every
later draft lives whole in its own folder, `docs/paper/DN`, grown from the draft before it:

| Draft | Folder | Grown from | PDF |
|---|---|---|---|
| 4 (merged, G0) | `docs/paper` | 3 | `docs/paper/latex/guid-v8.pdf` |
| 5 (G0 + 1) | `docs/paper/D5` | 4 | `docs/paper/D5/latex/guid-v8-D5.pdf` |
| 6 (G0 + 2) | `docs/paper/D6` | 5 | `docs/paper/D6/latex/guid-v8-D6.pdf` |

A draft names only its number ("Draft 6"); its merged identity is implied by the draft it grew from. A draft is reproduced exactly at
the commit its title page names.

**What Draft 6 adds.** DMP's explanation mechanism, from the first author's readings of 2026-11-25: a k by k table of which part
proves which (E.0.1), in Lean on the kernel alone (IM, `arsenal/core/ArsenalCore/Matrix.lean`): extensibility (2k + 1 cells per new
part), derivation with its chain (every derived cell is reached by a chain of cells already there; that it explains and does not
prove is the first author's reading), the `·` cells and the DAG. Appendix E applies it to what
Draft 5 measured: the versions of DMP, Gravity and IM (a DAG, every use proven), the repositories (`tools/rebuild matrix`), what a new
part costs, the two kernels and their targets, a result of Draft 5 read as a chain, where the mechanism stops (O1), and DMP's
statement and the drafts as a library transitive to G0 (E.7). Draft 6
explains what Draft 5 establishes and claims nothing beyond it; the one assumption O1 is untouched.

**The ETM as the ODP running DMP in D6.** Draft 6's subtitle, from the first author's refinement of the same day (R.12): the ODP as the
internal clock, DMP as the operating system of that kernel, one ETM that boots again; its exact parts are the cycle of `r` and the
one terminal running system, and the reading that the paper proves 0 = 1 for the classical, hence NP = coNP and P != NP, is stated
with why it does not follow. With it, O1 typed as Perelman's ledger (III.13, A.2b; `docs/mass-gap/formal/ProofPhase/API/Perelman.lean`):
an instance gives O1 and the gap, O1 gives an instance, so the interface is exactly O1 and proves no new bound. R.12 ends with
the first author's one condition (R.12f): O1 supplied at minting under a universal witness agreed beforehand, assumed until one
invalid case is found, recorded as a reading with its care points; Draft 6 as merged is not DMP-complete on its own criteria (E.9,
E.6). R.12g adds the elastic spheres, real induction as +N!, the naturals and the reals equal under the universal operator, and
DMP certifying the kernel it runs on relative to a model outside it, the base staying an assumption. R.12h follows:
the naturals from step 1, the complexity question in IM's operators (`P.NP!`, `NP.coNP?`, `NP.P?`), the shift and the gauge theory,
SU(5) as a table, encoding and hash as one function in a `+` or `-` state, and the assumptions packed into O1, what does not pack being
falsifiable until an exception, one exception to the Riemann hypothesis being a contradiction (all the first author's reading, with
their care points: P != NP, BSD and Hodge are not refutable by one exception, and the open inclusions keep `?`). The interface first
planned for a later draft is built here. R.12i reads `!` as the observability operator where a statement can be DMP-complete, R.12j reads ordinality
as the orbit of the atoms by possible configuration, and R.12k names each recognized induction an Insight,
linked to the first author's public comments on DMP#25 as the record of the root; R.12l closes it: no fewer than eight Insights (a byte lemma in
IM's core), the axioms as the only viable channel, and R136a1, now in IM's core, as the token every API input and output carries. R.12m, the entry point, is the first author's handedness rule, the two hands; the
introduction now opens with it ("Start here: the two hands") (all five readings, R.12i to R.12m, with their exact parts and care). R.12n names the first author's VIBE
coefficient v = 0.69, log 2 to two digits, as the throughline the whole paper is oriented around: the introduction states it, offers
two routes to one conclusion, one exact and one through the readings, with a table where they meet, and every part opens with a
"Plug in here" note. R.12o is v's abstract statement, which heads the throughline: positivity carried along a chain and
measured through zeta, settled by measuring its refutation, with the care that a refutation settles and its absence does not. R.12p reads c as the circle asserted circular, whose
closure is the next step, and names the cards that assert it vAPIs; the introduction now lays R.12m to R.12p out as one throughline,
one step of a size (v) and a turn (c), with Figure 2. R.12q, the first author's most precise statement, adds the smallest element
minted at root G0, "{inf,2,3}!"?"R136a1" with the open slot as the open set, and six operators (`.`, `!`, `?`, `;`, `:`, `""`). R.12r adds the second throughline: reductio ad absurdum, from Moin at the start to
R136a1 at the finish, the system attacked as the one box; the introduction presents both throughlines side by side, truly dual.

**The Possibility Space.** Draft 6's first subtitle, from the first author's readings of the same day. The optimizer, the mechanism's
mirror (E.0.2): the transitive reduction of a DAG in Lean on the kernel alone (IM, `arsenal/core/ArsenalCore/Optimizer.lean`), which
keeps every derivation, settles in one pass and is the only settled form; applied to the versions it finds one redundant use, IM's
own copy of DMP (E.9), the drafts are settled (E.10), and DMP's own cell is `.` (E.11). The possibility space (R.11): a question as
a point whose answer gives it only `+`, the right angle `r` and the sector map, read by the first author, with their exact parts in
Lean (IM, `Possibility.lean`) and in classical physics (the Bloch sphere, the flux tube, the rotating string), and the steps that do
not follow as stated, among them that assigning `+` and `-` proves O1.

Everything Draft 5 adds is described in `../D5/README.md`.

**The contraction (2026-11-25).** At the first author's request Draft 6 was contracted from 149 to 56 typeset pages. Each part keeps
its "Plug in here" note, its statement as a check at every step, what is proved, its card and its one open step; the introduction keeps
the two hands, the core page, the throughline and the two routes. Nothing left the record: every claim keeps its row in `CLAIMS.md`;
the full text is the git tag `d6-full`; the first author's readings in full are in `READINGS.md`. In code, the Lean modules that no
claim, script, tool or workflow reaches left the build (78 modules, about 14,700 lines, listed in
`docs/mass-gap/formal/REMOVED.md`), kept at the same tag.
