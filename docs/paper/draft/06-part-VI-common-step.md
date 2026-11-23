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

## VI.7 Uncertainty transported across the DB

The owner's approach for the content layer: "Exactly define the uncertainty, then transport it in a meaningful way across a DB." Each
column keeps its uncertainty in one named bridge to the real object; the finite model asserts only itself. That uncertainty is itself
a carried quantity, so the ledger applies to it with one more term (`docs/unified/TRANSPORT.md`).

**The theorem.** An uncertainty e_n >= 0 crosses step n with factor f_n and floor delta, and the step may add fresh uncertainty
r_n >= 0 of its own: e_{n+1} <= e^delta f_n e_n + r_n.
- **Bounded (VI.7a).** If the steps contract, e^delta f_n <= q < 1, and each adds at most R, the uncertainty stays at most
  q^n e_0 + R/(1 - q) at every step, uniformly in n **[Lean]**.
- **Critical (VI.7b).** At cost = floor, e^delta f_n = 1, nothing is damped: e_n <= e_0 + (sum of the r_j). The bound is attained, it
  stays bounded exactly when the r_j are summable, and a constant fresh uncertainty grows without limit **[Lean]**.
- **Sign preserved (VI.7c).** If a quantity has a sign margin m_n and the uncertainty about its counterpart across the DB stays below
  it, e_n < m_n, the counterpart's sign is certified at every step, with value at least m_n - e_n **[Lean]**.
- With no fresh uncertainty the theorem is the ledger itself: `Pays`, `carry`, `Ledger.contract`, and every DMP ledger of
  `ETM/RunSys.lean` (VI.7d) **[Lean]**.

**Zero slack, exactly (VI.7e).** When the uncertainty and the margin it is compared with pay the same cost at every step, their ratio
crosses at exactly cost = floor. Damping relative to a margin exists only if the margin shrinks more slowly than the uncertainty
**[Lean]**.

**Where each uncertainty sits, and what the open step needs in these terms.**
- **Yang-Mills (VI.7f, VI.7g).** The uncertainty is the boundary uncertainty of a slab: how large the charged (twisted) sector can be
  against the neutral one, at any outside; O1 is the margin 1/mu. In the slab geometry the slab chain carries it with each layer's own
  factor and adds nothing (zero join loss), and any positive twist ratio clears O1 with enough layers on a fixed lattice **[Lean]**.
  The open step: a cost above the floor at fixed physical length, uniform in the cutoff (the twist ratio bounded below as the lattice
  spacing goes to zero), plus, in the box geometry, the side seam added at each join. For three slabs at the self-dual factor the
  seam must stay below (1/mu - (sqrt 2 - 1)^3)/sqrt 2 per join **[open]**.
- **GRH (VI.7h, VI.7i).** The uncertainty is how far zeta's margin (the Szego prediction error at scale n) is from the finite model's,
  relative to the model's; the explicit formula's remainder enters each scale as the relative difference of the two factors
  1 - |k|^2. In log form it crosses at exactly cost = floor: zero slack. Zeta's margin is certified, with size, while the summed
  remainders stay below log 2; the sign alone is decided step by step **[Lean]**. The open step: remainders, measured against a
  margin that collapses, that are summable with total below log 2, from the primes alone, beyond Dirichlet **[open]**.
- **NP vs coNP (VI.7j, VI.7k, VI.7l).** The uncertainty is the hidden information per variable, the pointer of the gadget, log m bits.
  Each hidden variable a refutation must resolve takes a fixed share of the line count across the two-party split. That is a ledger
  with no fresh uncertainty, and it is exactly a size bound; lifting supplies the cost c log n per variable **[Lean]** from
  **[external]**. The open step: a constant cost c > 0 per hidden variable for a constant-size gadget (`LiftCPConst`) **[open]**. In
  the known proofs the per-block hiding errors add up across all blocks with no damping, which is why the gadget grows with n
  **[reading]**.

**Side by side (VI.7m).** `three_bridges` (`Unified/All.lean`) states the three columns in one theorem, each as "named hypothesis
=> the uncertainty is transported below the margin and the sign holds" **[Lean]**. It is the transport counterpart of
`three_instances`. The theorem is not empty: on a perturbed Doeblin chain every hypothesis is proved, and the uncertainty stays below
the margin at every step; without mixing, a perturbation of the same size erases the margin (VI.7o) **[Lean]**.

**The running-state axiom (VI.7n).** Each named hypothesis says that its object is in a running state. With that statement taken as a
named axiom R, the three conclusions follow: the boundary uncertainty stays below 1/mu, zeta's margin keeps its sign, the crossing
cost is paid **[Lean]** for the implication. R for the specific objects (the Wilson measure in the continuum, the L-functions beyond
Dirichlet, strong proof systems) is exactly the open step of each problem **[reading]**.
