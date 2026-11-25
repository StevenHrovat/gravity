# Appendix A. Validation: Poincare, SU(N) and the rigid groups

*Draft 6. Claim labels A.n are listed in `../CLAIMS.md`.*

**Plug in here.** Gives: the check against Poincare (Perelman), SU(N) and the rigid groups, and III.13's ledger as a
type (A.2b). Needs: II.4.1, and III.13 for A.2b. Route: off both routes. VIBE coefficient: does not enter exactly.

## A.0 Poincare (Perelman), and SU(N)

**Purpose.** Check the restatement of VI.3.5 against a solved, accepted proof in which finite-time singularities occur, are
classified, and are cut at a boundary, after which the flow continues. **This box claims nothing new.** Everything in A.1 and
A.2 is **[classical]** (recalled from Perelman's three papers and the expositions; not re-checked for this draft), except the
fitting of the DMP vocabulary, which is **[reading]**.

## A.2 Verdict **[reading]**

The restatement passes as a **description**: every element of VI.3.5 has an exact counterpart in Perelman's proof (forced time, one
scale-invariant estimate, a defined act at a boundary, a quantum per act, a final certificate). It does **not** pass as a
**mechanism**: what reaches Perelman's boundaries is decided by classifying all blowup shapes, not by a cost above a floor; the
monotone quantity buys a sign, not a rate; and Ricci flow passes a sequence of boundaries and continues, while the Chen-Hou time `T*`
is terminal. Nothing new is claimed.

## A.2b The ledger as a type

*New in Draft 6.* The verdict of A.2 stays: as a model of the restatement, Perelman's proof passes as a description, not as a
mechanism. III.13 turns the counting part of the ledger (a bounded monotone quantity, a quantum per boundary event, finitely many
events) into a type with a theorem: an instance gives O1, and O1 gives an instance, with W taken as a counter **[Lean]**. So the type
adds no mechanism beyond O1 itself; whether Yang-Mills has an instance is O1 **[open]** (claim A.2b).

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

The bullets that follow these results in the full text, each result beside the first author's reading of it, are in `READINGS.md` and at the tag.

**The full text.** This part is contracted. Every derivation it leaves out is in the full Draft 6 at the git tag `d6-full`, and in Draft 5 section by section; every claim keeps its row, status and evidence in `../CLAIMS.md`.
