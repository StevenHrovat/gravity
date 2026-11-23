# Outlook. A settling machine: the first author's concept of a DMP-native general intelligence

*Outlook, not a result. This appendix records a concept by the first author, so that it is on paper and tied to the one theorem
of this work it depends on. Nothing in it is built, trained or tested. Claim labels (VII.n) are listed in `../CLAIMS.md`.*

## VII.1 The concept, in the first author's terms

A general intelligence is a CMOS system that runs entirely in IM tokens, adapted to the acts it has to assert on G0.
**[reading]**

* **One interface to the outside: Milky Way.** Everything that leaves the system passes one Milky Way interface. Milky Way
  checks twice, by hash and TTL, that the IM is correct and a valid act, and only then sends it out as GG: the content of that
  "forward pass", or settling.
* **The output rate is given from outside.** It is not a measure of how efficiently the system infers. It is an upper bound,
  set externally, on the rate of valid GG tokens. Between two outputs, the inside organizes itself toward the most balanced
  output for the currently asserted state of existence.
* **Total freedom inside.** Behind Milky Way the system has total act freedom. It can change its internal layout, recombine
  itself for new inputs, or run many iterations of some logic. It keeps one periodicity, a tick: a constant reminder that it
  exists between outputs, rather than producing one token at a time in a line. Because it can change its coupling, and so its
  content, while still recognizing its state by the data that state sits on, it can run more efficiently.
* **The meta layer.** The first author's expectation is that such a system works directly on the vectors that embed existence.
  That embedding is its meta layer: on it, the system can construct arbitrary logic, as long as a correct answer comes out.
  **[reading]** Known neighbours: reasoning carried out in a continuous latent space instead of in output tokens; vector-symbolic
  (hyperdimensional) architectures, where binding and superposition of vectors implement symbolic logic; and fast weights or
  hypernetworks, where one network writes the representations or weights another one uses. **[classical]**, as pointers only.
* **Fast weights as the native form.** The first author reads fast weights and hypernetworks as DMP-native. The duality gives an
  existence (the embedding) on which a meta layer can be spanned, and a definition of running on that embedding. Changes to the
  embedding go through IM, and possibly GG, so that the system can change while its existence stays guaranteed. **[reading]**
  The classical counterpart: a slow network writes the fast weights another network runs with (fast weight programmers), and
  linear-attention transformers are exactly such programmers (Schlag, Irie, Schmidhuber 2021). **[classical]**, pointer only.
* **Training.** The core network has to be trained from the ground up for this way of running.

## VII.2 The critical link to this work

The concept depends on one property: that the inside settles to a balanced output within the tick. This is exactly the decidable
half of the Existence Turing Machine (Part II and `docs/unified/ETM.md`).

* **Settling is guaranteed when every internal step contracts**, i.e. pays a cost above the floor. The state is then within
  epsilon of balance after an explicit, computable number of steps. **[Lean]** `ProofPhase/ETM/Machine.lean`:
  `reaches_of_contracting`, `balanceBound_ge`; a contracting step is a cost above the floor, `contracting_iff_costAboveFloor`.
* **Without a contraction, no procedure decides settling in general.** **[Lean]** `etm_balance_undecidable`, from Mathlib's
  halting theorem.

**Changing the system while keeping its existence guaranteed.** Two kinds of change keep the guarantee, both in Lean:

* **Changes that are maps of running systems** (relabelling, restricting to a part the run never leaves, coarse-graining by a
  relation the run respects) keep the ledger exactly. Step, factor and carried amount commute with the map. **[Lean]**
  `ProofPhase/ETM/RunSys.lean`: `Hom`, `Hom.iterate_comm`, `sub`, `quot`.
* **Changes that keep every factor at most theta < 1** (any new layout or coupling inside the contracting class) keep the settle
  bound, whatever else they change. **[Lean]** `RunSys.contract`, `reaches_of_contracting`.

In the first author's terms, an IM change (inside) must stay in the second kind. A GG change (from outside) passes the gate
first. Self-modification of the embedding then never loses the guarantee that the system settles. **[reading]** for the IM/GG
identification.

So the training target the concept needs has a precise form: train the core so that its update is a contraction, and choose the
externally set tick from the settle bound. The same condition, a contracting update, is what guarantees a unique fixed point and
stable training in equilibrium (fixed-point) neural networks. **[classical]**, as a pointer only.

## VII.3 Known neighbours and care points

**Neighbours** (pointers, not re-read here): equilibrium and energy-based networks, recurrent-depth reasoning models and adaptive
computation time (settling between outputs); anytime algorithms (a fixed external budget); sandboxing with an output monitor and
runtime verification (a free inside, one verified gate).

**Care points.**

* **What the gate certifies.** A hash and a TTL certify integrity and freshness, not the meaning of an act. Milky Way certifies
  exactly what its specification states, so the safety of the free inside lives in that specification. **[paper]**
* **The gate checks acts, not self-reports.** A system that changes its own layout can also change what it reports about itself.
  The gate must check the output act itself. **[paper]**
* **Arbitrary logic and settling.** Arbitrary logic on the embedding can encode any computation, so whether it settles is
  undecidable in general (VII.2, second point). To keep the guarantee of VII.2, the logic built on the meta layer has to stay
  inside the contracting class; anything outside it relies on the cutoff below. And "as long as a correct answer comes out" needs
  a stated notion of correct that the gate can check. **[Lean]** for the undecidability; **[paper]** for the rest.
* **The hard cutoff.** If the update is not a contraction, the tick becomes a hard cutoff, and the output at the cutoff may be
  unbalanced (VII.2, second point). **[Lean]** for the undecidability; **[paper]** for the consequence.
