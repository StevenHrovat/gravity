# Part X. The one assumption and the rigid start: what the cards show together

*Draft 6. Claim labels (X.n) are listed in `../CLAIMS.md`.*

**Plug in here.** Gives: the cards side by side, the one assumption and the rigid start. Needs: the parts it compares
(III to IX), or their "Plug in here" notes. Route: the exact route, stop 5. VIBE coefficient: the rigid start {infinity, 2, 3} is
certified up to a = 0.69 (X.58, X.65) **[certified]**; on the GRH route the summed remainders must stay below log 2 (X.7h)
**[Lean]**, and beyond Dirichlet that is open (X.7i) **[open]**.

**Contracted.** Sections and labels this part names but does not print are in the full Draft 6, the git tag `d6-full`, and in Draft 5 section by section; every label is a row of `../CLAIMS.md` with its status and evidence.

**The one assumption in the terms of II.4.1.** On each card the one assumption is the card's base case, its open statement: the
card's box checks the same statement at every step, so the inductive step is free. The other half of the assumption, the gate shared
across scales, has content only where a family of scales is defined and mapped onto the one box, as for G2 (A.5) and in the verify toy;
on the cards no such family is defined in Lean, and sharing with a constant box adds nothing **[paper]**. In the toy the sharing is a
theorem: every bit width is mapped onto one bit by reduction modulo 2, and the parity argument for each width sits in that map
(`evens_everywhere`, T.2) **[Lean]**.

## X.4 Why O1 is always the open step

### X.4.4 The paper's one assumption

This is the one place where the paper states what it assumes. Every result that uses it carries the mark **[conditional]**. The
project's release criterion (IX.0) asks for it proved; it is not proved here.

**The assumption, as a schema.** It has no single formal statement. Its instances are named hypotheses in Lean, each **[open]**
unless said otherwise:

1. *Yang-Mills*: `FineOneBox`, the hypothesis of the one-box assembly for the Wilson measure (III.5.9). The Yang-Mills card itself
   (`API/YangMills.lean`) has the chain form `YMOneBox` as its slot, related to `FineOneBox` only in prose (path counting, III.5.9).
2. *GRH*: `ScaleSign`, the sign carried at every scale, for a finite model of zeros (`API/GRH.lean`). For a model of zeta's zeros it
   holds under Mathlib's statement of the Riemann hypothesis, which others have proved (IV.0), so on that model the instance is
   discharged by an external result; beyond Dirichlet L-functions no card is written.
3. *NP vs coNP*: `CrossingCost` (`API/NP.lean`), reached through lifting with a suitable constant gadget (V.4.11).
4. *BSD*: the card's statement `BSDStatement`, from order 2 on (VII.2).
5. *Hodge*: the card's statement `HodgeConjecture`, for codimension p >= 2 (VIII.2).
6. *Across scales*: `SharedGate`, a box's gate shared with the certified one box at every scale (`scale_certificate`, II.4).
7. *G2*: the sharing for G2's rigidity box (A.5u).

These are different statements; what they share is the form of the step, each saying that a box is DMP-complete. Two abstract
bounds on one sequence of tick factors, which the paper reads as GRH's edge and O1's edge, are proved independent (section 2,
`transport_not_decay`, `decay_not_transport`); no theorem relates the instances to one another. Navier-Stokes is not an instance:
its model box is not DMP-complete (`ns_not_complete`, VI.8); nor is the GU card's open step, which is not a statement about its box
(IX.8) **[paper]** (claim X.64).

**What can be shown about O1.** The first author's statement: the only thing that can be shown is that O1 does not fail for anything that
can be described as existing in the containing DB. Three things stand behind it, each with its own status.

* **Any failure is describable.** O1 is a universal statement over describable instances: one box of fixed physical size, one
  outside, one level. A configuration at or below the floor would therefore be a finite witness against O1; a failure may also appear only as a limit of a family of
  configurations, since O1 asks for a strict margin uniformly **[paper]** (logic) (claim X.72).
* **None has been found.** The certified start holds with margins (X.65, **[certified]**); per-box positivity holds by construction
  (III.9.5a, **[Lean]**); small tori pass centrally at L = 6 but are not certified (III.7.1, **[numerical]**). The one refuted check
  (III.7.2) is the chain criterion in another geometry and bears on O1 neither way, and the cubic one-box geometry is untested by
  saved data (III.7.3).
* **Care point.** "O1 does not fail for any describable instance" is O1 itself, not a weaker statement that could be proved on the
  side. It is the one assumption phrased so that it can be falsified: a describable configuration at or below the floor would refute it. The first author reads
  it as the containing DB's guarantee that whatever exists in it can be described **[reading]** (claim X.72a).

**What follows under it.** If the process is accepted, every start is oriented, that is directed through `{infinity, 2, 3}`:

* **At the start, certified.** At supports where only the real place and the primes 2 and 3 enter (up to a = 0.69), Weil's form
  is positive with an explicit margin, c = 1.5e-9, 3.4e-11, 6.4e-13 at a = 0.60, 0.65, 0.69. So the first tick is certified
  positive with a margin, and the sign is fixed there **[certified]** for the enclosures, **[paper]** for the analytic estimates
  that tie them to Weil's form (the tail and cross-term bounds of the note, not independently read) (ball arithmetic;
  `docs/unified/GRH-ONEBOX-CERT.md`), with the abstract step **[Lean]** (`GRH/OneBoxCert.lean`, `onebox_positive`; claim X.58b).
  This is claim X.65. The first author reads the certificate as 1.5 = 3/2: the sum of `{infinity, 2, 3}`, existence and a spin
  giving it direction (3/2 = 1 + 1/2), the ratio of the start's primes and the perfect fifth of the piano guide; any description,
  decimal included, is existence, and the certificate shows this one is a valid sublayer, the spin being reflection positivity on a
  primitive **[reading]** (claim X.65a). Care point: which digits a margin shows depends on how Weil's form and the test function
  are normalised; what is certified is that the margin is positive, at that size.
* **For every later tick, conditional.** The sign at the start, and with it the direction of every later tick, is fixed *only if*
  the process is accepted. This is **[conditional]** on the acceptance (claim X.66). It is not a theorem that the margin survives:
  for GRH that is the open step (claims X.9, X.46), and the margin collapses fast beyond the start (an upper bound of about 3.6e-15 on the smallest value at a = 0.75, from a trial polynomial; the certification failed there)
  **[numerical]**, so it cannot be carried outward by computation.

**How to read a conditional result.** Whenever Part X, or a later part, writes "conditional on the established process", it means
exactly this: the statement holds if the process of G0 to the hand-over is established, and the process being established is the
assumption of this subsection. Where a result holds without it, the result says so: the Lean theorems of section 2 (the geometry
of the two edges), the transport theorem (II.1) and the certified start do not use it. **[paper]** (claim X.67).

**Why it is stated plainly.** The release criterion asks for it proved. Until it is, the abstract and the introduction say that every
result using it is conditional on it, and they name it as one assumption, read the same way on five cards.

## X.8 What this part adds up to

1. Every card needs the same container, a containing existence with free possibility space (section 1). The cards share one geometry (section 2) and one slot (section 4). What each card asks of the geometry differs, so no single statement
   proves them all.
2. The open step of each card is the same assertion in the card's terms: "this object runs", with a floor, uniformly (sections 4.2 and 6).
3. The proved obstructions say why assembly with slack cannot supply it (the table in section 4.1).
4. The dichotomy of II.3 says what would follow: with a floor, a settling bound; without it, no decision procedure (section 4.3).

Sections 1, 2, 4.1 to 4.3 and 6 of this part are in the full text.

When a step closes, the change to the paper is local: the status in `../CLAIMS.md` moves from open to Lean (or paper), the section's
verdict line changes, one cell of the table in section 4.1 changes, and the introduction's list of what remains shrinks by one item. No other
section needs to move. That is the test of the paper's structure.
