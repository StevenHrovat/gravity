# Part VI. The common open step, and what closes it

*Draft 1, 2026-11-23. Claim labels (VI.n) are listed in `../CLAIMS.md`.*

## VI.1 One shape

Parts III to V end at three open steps. They look different. They have one shape:

> **A positivity, or a certificate, is known for one unit (one box, a finite model, one certified class). What is missing is that
> it holds for every case, without loss.**

| | Proved for one unit | Missing for every case | Why the naive carry-over fails |
|---|---|---|---|
| Yang-Mills | each box has a hand-over rate of at least 0.881 in one of two channels **[Lean]** (II.5); a lossy re-encoding contracts, and the same contraction repeats along the chain **[Lean]** (II.4) | **the one-box statement:** the loss rate eta < 1 at one box scale, for every well-defined outside **[open]** | the rate is annealed, not uniform over outsides; at the SO(3) cut a sheet is free; between rarity and saturation lies a window (II.6) |
| GRH | Weil positivity in finite models **[Lean]** (IV.1); each prime step holds numerically **[numerical]** (IV.3) | **a positive space built from arithmetic alone** **[open]** (IV.4) | the margin collapses super-exponentially: every step is an exact cancellation, so no estimate with slack can work |
| P vs NP | inside the certified class every task is polynomial **[Lean]**/**[classical]** (V.1); every refutation crosses **[Lean]** (V.3.7) | **from the class to all inputs; the cost of naming the crossing in strong systems** **[open]** (V.5) | the crossing is universal but its cost is not: a conserved quantity can have a cheap name (a parity) |

**Reading (VI.1).** In DMP terms all three ask the same question: how a certified act hands its certificate to the next act without
loss, so that remnants accumulate into existence instead of eroding it. **[reading]**

## VI.2 What the author's answer settles, and what it does not

The author answered the composition question with the act carrier (I.4): a certificate passes without loss when a conserved
quantity carries it; and supplied the uniformity: "the uniformity is given by the arrow of causality" (2026-11-23).

* **For Yang-Mills this reduced the problem to one box at one scale.** The conserved carrier (the centre flux) is in hand **[Lean]**;
  superadditivity along the chain is proved in abstract transfer-matrix form **[Lean]**; uniformity along the chain is translation
  invariance of the transfer step **[classical]**. What is left is one number at one scale, uniformly over outsides **[open]**
  (Part III, section 0).
* **For GRH and P vs NP the carrier is identified, not the step.** In GRH the "null" carriers are the zeros on the line (pure
  oscillation) **[reading]**; in P vs NP it is the parity a proof line names **[Lean]** for Tseitin. Their open steps stay as stated.

## VI.3 What would close each step

| Problem | Closing statement | What can and cannot help |
|---|---|---|
| Yang-Mills | a worst-case argument for one DB: for every well-defined outside, either the box contracts or the non-contracting part is a contained sheet of weight at most e^{-c\|sheet\|} | measurements can refute or guide, never establish a for-all statement (provability rule, `docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/REDESIGN.md`, section 8) |
| GRH | any one of the five forms (IV.4), built without the zeros; best candidate: an arithmetic positivity of Hodge-index type, which would also explain why the two 1/2s coincide (IV.2.6) | estimates with slack cannot work (IV.3.7); weight positivity alone is provably not enough (IV.3.8) |
| P vs NP | a non-relativizing, non-natural, non-algebrizing argument for the crossing, or a superpolynomial Frege lower bound through steps T and H | the native method relocates, not removes, the open step (V.4.3) |

## VI.4 Why Yang-Mills is the model

Only in Yang-Mills is the starting positivity given by construction: e^{-S} >= 0 together with locality gives reflection positivity,
and the whole chain of II.0 runs from it. The other two problems lack exactly that: an arithmetic G0 in which Weil positivity is a
construction (GRH), and a description language in which the existence of every instance is local (P vs NP). **[reading]** for the
identification; the asymmetry itself is the content of II.1.

So the order of closing is likely: Yang-Mills first (one box, one scale, one worst-case argument), then the transfer of its method.
This is an expectation, not a claim. **[reading]**

## VI.5 The paper as it will close

Each open step is stated in this draft in the exact form that would close it. When a step closes, the change to the paper is
local: the status in `../CLAIMS.md` moves from open to Lean (or paper), the section's verdict line changes, and the abstract's list
of what remains shrinks by one item. No other section needs to move. That is the test of the paper's structure.
