# A native, layer-wise proof-optimization method: finite cost per layer, and where the gap is

Private working note, 2026-11-23. The owner, on `NATIVE-OPTIMIZATION.md`: "The cost of checking is kept finite by the
fact that the first building blocks are quantized and thus finite by definition. I am also thinking about a kind of
gap-like quality that emerges when running a proof, as it has to. What should come out is a native method to reduce the
inefficiencies in an existing proof, so that there is a finite cost associated with each layer."

This note:
* defines the layers of a proof and a cost per layer, and measures it;
* states the method as a sequence of passes;
* says honestly which kind of gap the passes have (contraction, or strict decrease only), with the abstract part proved
  in Lean;
* applies the method once to a real ProofPhase chain, with the same statements kernel-checked and the per-layer costs
  before and after.

Claim marks as in `PROOF-SYSTEMS.md`.
* **[Lean]**: `ProofPhase/Native/Method.lean` and `ProofPhase/Native/RouteBChain.lean` (`axioms-method.sh`,
  `axioms-method.log`: 15 declarations, standard axioms, no `sorry`).
* **[measured]**: `metrics/Layers.lean`, `metrics/ReflectionScale.lean`, `metrics/run-layers.sh`, output
  `metrics/layers.txt`.

---

## 0. The short answer

1. **Layers and cost.** A layer is a depth level of the proof's dependency DAG: layer 1 holds the theorems that use no
   other project theorem, layer k those whose longest chain below has k - 1 steps. The cost of a layer is what the
   kernel spends checking its declarations (measured in nanoseconds), together with their proof-term size and count.
   **[measured]**
   * In DMP's deepest chain every layer above the bottom two holds a single lemma (three checker-equals-definition
     steps, then the two top compositions), each costing 0.17 to 1.4 ms.
   * A reflected check of a DMP recipe has a proof term of constant size (20 nodes), while the kernel cost grows
     linearly with the number of building blocks: about 0.3 ms per recipe line, from 4 to 128 lines.

   So the cost per layer is finite and bounded by the size of the finite building blocks it evaluates, as the owner
   says.
2. **The gap, honestly: a quantum, not a contraction of the work.** Three statements are proved in Lean. **[Lean]**
   * Every pass that changes a proof lowers a natural-number measure (named lemmas, layers). One quantum per change is
     enough: the method stops after at most as many passes as the starting measure (`fixed_after`). This is a sign
     with no rate, like Z_tw < Z, and it still **arrives**, because the measure is quantized.
   * Without quanta it would not arrive: the real map x -> (x + 1)/2 strictly decreases and contracts by 1/2 toward 1,
     and never reaches it (`real_never_arrives`).
   * **A true contraction (factor 1/2) exists for depth:**
     * pairwise merging of layers ("pointer jumping") turns d layers into ceil(d/2), so one layer after ceil(log2 d)
       passes (`iterate_clog_pairUp`);
     * the total checking work is conserved (`sum_pairUp`), and the per-layer cost at most doubles each pass;
     * more generally, a quantized measure halved toward a floor arrives in log2(excess) + 1 passes (`reaches_floor`).

   No pass of the method contracts the checking work itself: regrouping and renaming do not delete work. The floor of
   the work is the irreducible core.
3. **Applied once** to the bottom of the `yang_mills_assembly` chain (Route B correlation bounds). The two bounds were
   re-proved in a new file with **the same statements** (kernel `rfl` check), the four-lemma measurability ladder
   replaced by one `fun_prop` call. **[Lean]** + **[measured]**

   | | before | after |
   |---|---|---|
   | theorems | 16 | **12** |
   | layers | 5 | **4** |
   | term size | 3778 | **3541** (-6%) |
   | kernel time | 19.9-27.1 ms | the same within noise |

   The checking work moved into the top lemma, which is what the conservation theorem predicts.
4. **The method, in one line.** Make each layer one decision, then compute:
   * merge or inline the single-purpose lemmas (passes 1, 2);
   * turn finite case analysis into a checker proved equal to the statement, then let the kernel evaluate (pass 3);
   * let automation carry regularity (pass 4).

   Each pass lowers a quantized measure, so the method terminates; depth contracts by 1/2 under merging; the work per
   layer stays finite and bounded by the finite building blocks. **[Lean]** for the dynamics, **[measured]** for the
   costs.

---

## 1. Layers and the cost per layer

**Definition.** For a root theorem R, take the project theorems its proof uses, transitively (the DAG). Each theorem
gets a depth: 1 if it uses no other project theorem, else 1 + the largest depth among those it uses. **Layer k** is the
set of theorems of depth k. Its **cost** is the sum over its theorems of:
* the number of distinct nodes of the proof term, with compiler auxiliaries inlined;
* the kernel re-check time: each declaration is type-checked again by Lean's kernel under a fresh name, best of 5 runs.

`metrics/Layers.lean` computes both. **[measured]**

**Why the cost per layer is finite.** A layer has finitely many declarations, each with a finite proof term. Checking a
term costs work for every node, plus the evaluation of every definition the kernel unfolds. Lean admits only total
definitions (structural or well-founded recursion), so every evaluation terminates. With finite building blocks (a
recipe of n lines, each line a finite record), a checker defined by recursion over the blocks does a bounded amount of
work per block. **[classical]** for totality in Lean; the per-block bound is measured, not proved: Lean's kernel cost
model is not formalized.

**Measured: the cost tracks the building blocks.** A DMP recipe of n lines (a galaxy and n - 1 stacked knowledge
layers), its verdict proved by `rfl`, so the kernel evaluates the checker. **[measured]**

| recipe lines | proof-term size | kernel time |
|---|---|---|
| 4 | 20 | 2.5 ms |
| 8 | 20 | 2.7 ms |
| 16 | 20 | 5.2 ms |
| 32 | 20 | 9.6 ms |
| 64 | 20 | 19.0 ms |
| 128 | 20 | 41.7 ms |

The proof stays the same size; the checking cost is about 0.3 ms per line, linear in the number of quantized building
blocks. This is the owner's first sentence measured: the cost is finite because the blocks are finite, and it is
proportional to how many there are.

**Measured: the per-layer cost of DMP's deepest chain** (`Cmb.producer_minted`, the reflection ladder). **[measured]**

| layer | theorems | term size | kernel time | content |
|---|---|---|---|---|
| 1 | 5 | 608 | 0.97 ms | `independentB_iff` and four base facts |
| 2 | 3 | 580 | 1.10 ms | `mintedB_iff`, two sealing facts |
| 3 | 1 | 1299 | 1.37 ms | `lineOkB_iff` |
| 4 | 1 | 204 | 0.19 ms | `wfB_iff` |
| 5 | 1 | 705 | 0.73 ms | `verdict_proven_iff` |
| 6 | 1 | 189 | 0.17 ms | `sealed_proven_complete` |
| 7 | 1 | 162 | 0.24 ms | `producer_minted` |
| total | 13 | 3747 | 4.8 ms | |

Above layer 2 every layer holds a single lemma, with a cost under 1.4 ms:
* three are decisions, a checker proved equal to one level of the definition (`lineOkB_iff`, `wfB_iff`,
  `verdict_proven_iff`);
* two are the top compositions.

That is the native shape: **one irreducible step per layer, each with a finite, small cost.**

## 2. The method: four passes

Each pass maps a proof to a proof of **the same statement** (checked by the kernel with `rfl` between old and new).

| Pass | What it does | Measure it lowers | Where it applies |
|---|---|---|---|
| 1. Inline | replace a lemma used once by its proof at the use | named lemmas (by at least one per change) | 30% of DMP theorems and 43% of ProofPhase theorems are used exactly once (`NATIVE-OPTIMIZATION.md`). In DMP each name is a gated claim, so pass 1 is not applied there. |
| 2. Merge layers | pointer jumping: compose a lemma with the one it uses when both are single-purpose | layers, by a factor 1/2 per pass | chains of single-purpose lemmas |
| 3. Reflect | replace a case analysis over a finite object by a Boolean checker proved equal to the statement, then `decide`/`rfl` | case splits; the proof term becomes constant size | finite objects (DMP's recipes; the finite parts of ProofPhase) |
| 4. Automate regularity | replace measurability, continuity and congruence ladders by `fun_prop`, `measurability`, or discrete instances | named regularity lemmas and the layers they occupy | 453 ProofPhase theorems (16%) are regularity lemmas by name |

**Order:** 4, 3, 1, 2. Automation and reflection remove lemmas, inlining removes the single-use ones they leave behind,
and merging shortens what remains. Each pass is idempotent on its own: a second application changes nothing.
**[reading]**, from the application in section 4.

## 3. The gap: what kind, honestly

The question was whether running the method is a contraction (each pass lowers a measure by a factor alpha < 1, so
O(log) passes, the Dobrushin pattern of `Mixing/Glauber.lean`), or only a strict decrease (a sign with no rate, as with
Z_tw < Z).

| Measure | Behaviour under the passes | Result | Level |
|---|---|---|---|
| named lemmas (an integer) | strictly lower after every pass that changes something; no rate in general | **arrives after at most as many passes as there are lemmas** (`fixed_after`): the quantum is the gap | **[Lean]** (abstract) |
| layers (depth) | under pass 2: d -> ceil(d/2) | **contraction, alpha = 1/2**: one layer after ceil(log2 d) passes (`length_iterate_pairUp`, `iterate_clog_pairUp`) | **[Lean]** |
| any quantized measure halved toward a floor m | 2 (mu' - m) <= mu - m | arrives at m after log2(mu - m) + 1 passes (`reaches_floor`) | **[Lean]** |
| the same without quanta | x -> (x + 1)/2 on the reals | strictly decreasing, contracting by 1/2, **never arrives** (`real_never_arrives`) | **[Lean]** |
| total checking work | conserved by merging (`sum_pairUp`); per-layer cost at most doubles (`le_two_mul_of_mem_pairUp`); unchanged within noise by passes 1 and 4 on the real target | **no contraction**: the floor is the irreducible core, and no pass deletes the core's work | **[Lean]** (merging) + **[measured]** (section 4) |

**In plain words.**
* The gap is the quantum. Every improvement removes at least one whole unit (a lemma, a layer, a node). So a strict
  decrease, which on the reals would only approach its limit, **arrives** in finitely many steps.
* Where the method is a contraction is the depth: merging halves the number of layers per pass, and in exchange each
  layer carries up to twice the work.
* The total work is not contracted. It is conserved by regrouping and bounded below by the work of the irreducible
  core, so the gap of the work is the distance from zero to that core: positive, and finite per layer.

This mirrors the mass gap's two readings in `MassGap.lean`: the counted quantity keeps a gap of one quantum, while the
continuous one (here, kernel time) has no uniform gap. **[reading]**

## 4. Applied once: the bottom of the Route B chain

**Target.** `ProofPhase/RouteB/Chain.lean`, the correlation bounds `abs_ccorr_le` and `abs_nCorr_le`, at the bottom of
the longest chain under `yang_mills_assembly` (`NATIVE-OPTIMIZATION.md`, section 2). Below them sit four named
measurability lemmas (`measurable_cweight`, `measurable_cstep`, `measurable_sp`, `measurable_tm`).

**The optimized file.** `ProofPhase/Native/RouteBChain.lean` re-proves both bounds:
* passes 4 and 1: the measurability of the chain weight is discharged in place by one `fun_prop` call from the weight's
  two measurability fields, so the four ladder lemmas are not used;
* the statements are identical: the kernel accepts `rfl` between `abs_ccorr_le'` and `abs_ccorr_le`, and between
  `abs_nCorr_le'` and `abs_nCorr_le` (`axioms-method.log`). **[Lean]**

**Per-layer costs** (first of three runs in `metrics/layers.txt`; layer 1 includes the chain weight's field
projections, which are theorems). **[measured]**

| layer | before: theorems / term size / kernel | after: theorems / term size / kernel |
|---|---|---|
| 1 | 9 / 507 / 1.9 ms | 7 / 267 / 1.3 ms |
| 2 | 3 / 1093 / 2.8 ms | 2 / 712 / 1.8 ms |
| 3 | 2 / 431 / 4.1 ms | 2 / 1917 / 13.7 ms |
| 4 | 1 / 1102 / 8.2 ms | 1 / 645 / 3.0 ms |
| 5 | 1 / 645 / 2.9 ms | (none) |
| **total** | **16 / 3778 / 19.9 ms** | **12 / 3541 / 19.9 ms** |

Over three runs the totals are 19.9 / 20.6 / 21.5 ms before and 19.9 / 20.8 / 24.2 ms after.

**Reading the numbers.**
* **Removed:** 4 named lemmas (-25%) and 1 layer.
* **Depth 5 to 4, not 5 to 2:** the bound also rests on `cZ_nonneg`, whose own chain keeps layer 3 occupied.
* **Term size -6%.**
* **Kernel work unchanged within noise:** the measurability work moved into `abs_ccorr_le'` (layer 3 now costs 13.7
  ms). That is the conservation statement of section 3, seen on a real proof.

The saving is in names and layers, which is what a reader, a maintainer and the dependency graph pay for. The kernel's
work is a property of the content.

**What a full application would save** (proposal). The same pass on the other two deep chains of
`NATIVE-OPTIMIZATION.md`:
* `su2_flipProb_lt_half`: three continuity lemmas at the bottom;
* `spectral_gap_dobrushin`: two congruence lemmas.

Each would lose its regularity bottom, about 2-3 layers per chain. Across ProofPhase, the 453 regularity-named theorems
are the candidates for pass 4.

## 5. DMP reading (separate, marked)

Everything here is **[reading]** unless marked otherwise.

* **"The cost of checking is kept finite by the fact that the first building blocks are quantized."** Measured
  directly: a reflected check of n recipe lines costs about 0.3 ms per line, with a proof term of fixed size. The
  blocks are finite records, so each contributes a bounded amount of kernel work, and the total is finite and
  proportional to their number **[measured]**. A layer of the proof is a level of the definition (independent, minted,
  line ok, well formed, verdict), and its cost is that of one checker run over finitely many blocks.
* **"A gap-like quality that emerges when running a proof, as it has to."** Two gaps appear, as in the mass gap.
  * **Counted:** every improvement of a proof removes at least one whole unit. So the optimization arrives in finitely
    many steps, and the number of irreducible steps is a positive integer, never zero for a non-trivial statement
    (`fixed_after`, **[Lean]**).
  * **Continuous:** kernel time. It has no uniform gap between proofs of similar content, and regrouping does not
    lower it (section 4).

  The owner's "as it has to" matches the first: a quantized measure cannot decrease forever without arriving.
* **"A native method to reduce the inefficiencies, so that there is a finite cost associated with each layer."** The
  method of section 2, in DMP's own pattern:
  * make each layer one decision (a checker proved equal to one level of the definition);
  * let the kernel compute (reflection);
  * remove the bookkeeping that is not a decision (automation, inlining);
  * merge layers where the chain is a single path (contraction by 1/2 in depth).

  The cost per layer is then the cost of one decision over finitely many blocks: finite, measured, and visible.
* **"A contradiction is a disagreement at G0, excised at once, leaving only the remnant of its not existing"** (the
  owner, PREP entry of that name). For refutations this is a precise picture.
  * Deriving the empty clause is the excision. By the search reading (`TL.exists_falsified`, **[Lean]**), every
    assignment, every candidate world of the formula, is followed down the refutation to an axiom it violates: none
    survives.
  * The refutation is the remnant: the record that the formula's world does not exist. It exists exactly when the
    formula is unsatisfiable (`refutable_iff`, `Complete.lean`, **[Lean]**).
  * The remnant's minimal size is the open question: NP = coNP exactly when some proof system makes it polynomial for
    every unsatisfiable formula (Cook-Reckhow, **[classical]**).

  **Is the method's irreducible floor that minimal remnant?** No, and the difference is the useful part.
  * The method's floor is per proof. Its passes inline, merge, reflect and automate inside a given refutation, so it
    reaches the irreducible core of *that* refutation. It never searches for a different, shorter one.
  * The minimal remnant is per formula: the shortest refutation of all.
  * So the method's floor lies **at or above** the minimal remnant, and closing the distance is a search problem.
    For resolution that search is itself hard: finding a refutation of size polynomial in the shortest one is NP-hard
    (Atserias and Mueller, "Automating resolution is NP-hard", 2019). **[classical]**
  * Reflection does not escape this. A refutation by a checked exhaustive search has a proof term of constant size but
    2^n kernel steps. Cook-Reckhow counts checking time, so the remnant's size must include it.

  **What this adds:** a correct and standard reading (reductio as a process, the refutation as the certificate of
  non-existence) and one distinction: the per-proof floor that optimization can reach against the per-formula minimum
  that the open question is about. **It adds no bound on the minimum.**
* **What it does not do.** It does not lower the work of the irreducible core, and it does not shorten a computation
  that is long because the question is hard. That is the limit of `NATIVE-OPTIMIZATION.md` section 6 again: native
  optimization moves cost between proof length and checking time, and the open step of the size question stays where
  it was.

## 6. Files and how to re-run

| File | What |
|---|---|
| `../mass-gap/formal/ProofPhase/Native/Method.lean` | the dynamics: quantized termination, contraction to a floor, the real counterexample, pointer jumping (13 declarations) |
| `../mass-gap/formal/ProofPhase/Native/RouteBChain.lean` | the applied pass: `abs_ccorr_le'`, `abs_nCorr_le'` |
| `axioms-method.sh`, `axioms-method.log` | build, same-statement check, axioms, source grep |
| `metrics/Layers.lean` | per-layer cost (theorems, term size, kernel re-check time) of a root's DAG |
| `metrics/ReflectionScale.lean` | the reflected-check scaling test |
| `metrics/run-layers.sh`, `metrics/layers.txt` | the runner and its output (three ProofPhase runs, the DMP ladder, the scaling test) |

Re-run from the repository root inside the WSL replay distro:
* `bash docs/pnp/axioms-method.sh > docs/pnp/axioms-method.log 2>&1`;
* `bash docs/pnp/metrics/run-layers.sh`.

Both need the build folder seeded with a built `.lake`. Nothing existing was changed; the runners work on copies.
