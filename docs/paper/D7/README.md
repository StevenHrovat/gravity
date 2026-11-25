# Draft 7 of GUID v8 (`D7`)

Draft 7 grew from Draft 6 and adds to it. Draft 4 is the merged state and is never edited: it stays whole in `docs/paper`. Every
later draft lives whole in its own folder, `docs/paper/DN`, grown from the draft before it:

| Draft | Folder | Grown from | PDF |
|---|---|---|---|
| 4 (merged, G0) | `docs/paper` | 3 | `docs/paper/latex/guid-v8.pdf` |
| 5 (G0 + 1) | `docs/paper/D5` | 4 | `docs/paper/D5/latex/guid-v8-D5.pdf` |
| 6 (G0 + 2) | `docs/paper/D6` | 5 | `docs/paper/D6/latex/guid-v8-D6.pdf` |
| 7 (G0 + 3) | `docs/paper/D7` | 6 | `docs/paper/D7/latex/guid-v8-D7.pdf` |

A draft names only its number ("Draft 7"); its merged identity is implied by the draft it grew from. A draft is reproduced exactly at
the commit its title page names.

**What Draft 7 adds.** O1 as a Perelman-typed, Yang-Mills shaped interface (III.13), from the first author's reading in Draft 6
(II.0.4e), in Lean (`docs/mass-gap/formal/ProofPhase/API/Perelman.lean`): the counting part of the ledger Appendix A reads off
Perelman's proof (a bounded monotone quantity that gains a quantum at every failing step, so only finitely many steps fail) as a type;
typed for the Yang-Mills box, an instance gives O1 and the gap, and O1 gives an instance, so the interface is exactly O1 and proves no
new bound; a gapless toy is rejected and a gapped one accepted. Appendix A's verdict gains A.2b. O1 stays the one open step.

**What Draft 6 adds.** DMP's explanation mechanism, from the first author's readings of 2026-11-25: a k by k table of which part
proves which (II.0.2), in Lean on the kernel alone (IM, `arsenal/core/ArsenalCore/Matrix.lean`): extensibility (2k + 1 cells per new
part), derivation with its chain (every derived cell is reached by a chain of cells already there; that it explains and does not
prove is the first author's reading), the `·` cells and the DAG. Appendix E applies it to what
Draft 5 measured: the versions of DMP, Gravity and IM (a DAG, every use proven), the repositories (`tools/rebuild matrix`), what a new
part costs, the two kernels and their targets, a result of Draft 5 read as a chain, where the mechanism stops (O1), and DMP's
statement and the drafts as a library transitive to G0 (E.7). Draft 6
explains what Draft 5 establishes and claims nothing beyond it; the one assumption O1 is untouched.

**The Possibility Space.** Draft 6's subtitle, from the first author's readings of the same day. The optimizer, the mechanism's
mirror (II.0.3): the transitive reduction of a DAG in Lean on the kernel alone (IM, `arsenal/core/ArsenalCore/Optimizer.lean`), which
keeps every derivation, settles in one pass and is the only settled form; applied to the versions it finds one redundant use, IM's
own copy of DMP (E.9), the drafts are settled (E.10), and DMP's own cell is `.` (E.11). The possibility space (II.0.4): a question as
a point whose answer gives it only `+`, the right angle `r` and the sector map, read by the first author, with their exact parts in
Lean (IM, `Possibility.lean`) and in classical physics (the Bloch sphere, the flux tube, the rotating string), and the steps that do
not follow as stated, among them that assigning `+` and `-` proves O1.

Everything Draft 5 adds is described in `../D5/README.md`.
