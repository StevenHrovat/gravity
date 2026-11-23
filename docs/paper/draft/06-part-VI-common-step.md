# Part VI. The common open step, side by side

*Draft 2, 2026-11-23. Claim labels (VI.n) are listed in `../CLAIMS.md`.*

## VI.1 One shape

Parts III to V end at three open steps. They look different. They have one shape:

> **A positivity, or a certificate, is known for one unit. What is missing is that it holds for every case at once, without loss, and
> no assembly with slack can supply it.**

In each problem the work of this paper has driven the open step to a single object, and in each it has also proved why the natural
ways of assembling that object from smaller pieces fail.

## VI.2 The open step in its sharpest form, per problem

| | Yang-Mills (SU(2)) | GRH (beyond Dirichlet; independently for Dirichlet) | NP vs coNP (via proof complexity) |
|---|---|---|---|
| **The one object** | one box of fixed physical size | Weil's form at every support, from arithmetic alone | a cost measure on cutting-planes lines |
| **The open statement** | F_e(L) > log mu_4 = 1.91 (r(L) > 0.74), uniformly over every well-defined outside (III.5.6) **[open]** | lambda_min(a) >= 0 at every support, built from the primes, the characters and the real place without the zeros; eight faces (IV.4) **[open]** | interface hardness at width 3: a superpolynomial lower bound on dag-like protocols for the falsified-clause search of a random 3-CNF (V.4.10) **[open]** |
| **Proved for one unit** | max(F_tw, F_e) >= 0.881 per box (III.3.1) **[Lean]** | positivity in finite models (IV.1) **[Lean]**; each prime step numerically (IV.3.2) **[numerical]** | duality floor (e + 1)/2 for unit thresholds (V.4.5) **[Lean]**; every refutation crosses (V.4.3) **[Lean]** |
| **Why the unit does not carry** | 0.881 covers a chain (two channels), not a grid; path entropy log mu_4 beats it in d >= 3 (III.4.1, III.5.4) **[Lean]** | only the full set of primes is positive; place-by-place and two-term assembly fail (IV.3.5, IV.3.7, IV.3.8) **[Lean]** + **[numerical]** | weighted lines are cheap in both channels; one line aggregates its units (V.4.4, V.4.6) **[Lean]** |
| **What no duality supplies** | 't Hooft's relation forces nothing for n >= 2 sectors (III.4.4) **[Lean]** | the functional equation allows off-line pairs (IV.2.1, IV.2.2) **[Lean]** + **[classical]** | the duality floor fails for weighted lines (V.4.6) **[Lean]** |
| **The quantifier that makes it hard** | every outside (worst case, not typical) | every support, with margin 1e-9 | every refutation, of a structureless formula |
| **What measurement says** | passes centrally at L = 6, beta 2.3; not certified (III.7.1) **[numerical]** | holds at every step computed, by exact cancellation (IV.3.2) **[numerical]** | no measurement bears on a lower bound |
| **The "it runs" form** | the positive norm is free (RP); the margin eta < 1 is missing | the margin is not needed; the positive norm (Weil) is missing | the "it runs" object is the dag-like protocol; its size is missing |

The last row is formal for the first two problems: `runs_two_targets` (`Crossover/Runs.lean`) and `runs_and_mirror_on_line`
(`GRH/Tate.lean`) state the two targets side by side **[Lean]**. For NP vs coNP it is the notes' identification of the size-indexed
object for CP (`CP-DUALITY.md`, 0.5) **[paper]**.

## VI.3 What the act-carrier answer settled, and what it did not

The owner answered the composition question with the act carrier (I.4): a certificate passes without loss when a conserved quantity
carries it; and supplied the uniformity: "the uniformity is given by the arrow of causality". The containment reading moved the
requirement inside one box.

* **Yang-Mills: reduced to one number at one scale.** The conserved carrier (centre flux, Gauss's law on both sides of every DB) is in
  hand **[Lean]**; superadditivity along a chain **[Lean]**; uniformity along it **[classical]**; physical units **[Lean]**. The grid
  needs the influence to run in tubes, and tubes need F_e above the path entropy: O1 **[open]**.
* **GRH: the carrier is identified, and the step is located.** On the constructed space the scaling flow is an isometry; what remains
  are the zeros and the orbit lengths log p **[classical]**. The sign is global and all-or-nothing **[numerical]** + **[Lean]**.
* **NP vs coNP: the carrier is identified, and the step is located.** The parity a proof line names carries the crossing (Tseitin)
  **[Lean]**; in CP the crossing is forced and speakable in one line **[Lean]**; converting it into size is the open step.

**Reading (VI.3).** In DMP terms all three ask how a certified act hands its certificate to the next act without loss, so that remnants
accumulate into existence instead of eroding it. The three answers so far: in Yang-Mills, existence must outrun possibility by the path
entropy; in GRH, every building block must enter at once, at its exact place; in NP vs coNP, the pair must be charged at its interface.
**[reading]**

## VI.4 What would close each step, and what cannot

| Problem | Closing statement | What cannot help (proved or measured) |
|---|---|---|
| Yang-Mills | a worst-case argument for one box of fixed physical size: F_e(L) > log mu_4 for every well-defined outside, with the per-box product structure along paths (III.5.7) | measurements refute or guide, never establish a for-all statement; Doeblin floors vanish in the continuum (III.4.2); duality forces nothing for n >= 2 (III.4.4); the Bogomolny floor loses to entropy (III.5.5) |
| GRH | any one of the eight faces, built without the zeros: an exact identity coupling all primes up to the scale and the real place | estimates with slack (IV.3.2); place-by-place, subset or two-term assembly (IV.3.5 to IV.3.8); weight positivity alone (IV.3.10); the mirror constants (IV.2.6) |
| NP vs coNP | a size-forcing cost measure for CP at width 3 (N2); for the full problem, superpolynomial bounds for every system (N3 and beyond) | single-line measures (V.4.6); positivity to rank only (V.4.9); the native method relocates, not removes, the floor (V.5.3); every argument must pass three barriers (V.7) |

## VI.5 Why Yang-Mills is the model

Only in Yang-Mills is the starting positivity given by construction: e^{-S} >= 0 together with locality gives reflection positivity,
and the whole chain of II.0 runs from it. The other two problems lack exactly that: an arithmetic G0 in which Weil positivity is a
construction (GRH), and a description language in which the existence of every instance is local (P vs NP). **[reading]** for the
identification; the asymmetry itself is the content of II.1 and of VI.2's last row.

So the order of closing is likely: Yang-Mills first (one box, one number, one worst-case argument), then the transfer of its method.
This is an expectation, not a claim. **[reading]**

## VI.6 The paper as it will close

Each open step is stated in this draft in the exact form that would close it. When a step closes, the change to the paper is local:
the status in `../CLAIMS.md` moves from open to Lean (or paper), the section's verdict line changes, one cell of the table in VI.2
changes, and the abstract's list of what remains shrinks by one item. No other section needs to move. That is the test of the paper's
structure.
