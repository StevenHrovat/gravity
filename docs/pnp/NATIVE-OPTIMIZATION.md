# Native proof optimization: our own proofs as the real-world example

Private working note, 2026-11-23. The owner, on `DICHOTOMY-TRANSFER.md`: "it fits well into how many irreducible steps in the
logic chain are truly needed to get from the base axioms that define existence to the fact of the answer in question. This
shows a route for native proof optimization", and the prediction: "the native route for proof optimization is exactly how I
organized my DMP proofs, so in set theory, so that the only thing that has to be asserted is existence that proves the
question provably true. This also lets us check our proof construction as a real world example and maybe show how we could
further optimize it."

The note measures two bodies of Lean proof, both checked by the same Lean 4.34.0 kernel:
* the **gated DMP evidence**: `evidence/Dmp`, core Lean only, the 285 theorems the gate checks;
* the **ProofPhase** proofs: `docs/mass-gap/formal/ProofPhase`, on Mathlib, 2757 theorems (at the time of the run).

It then tests the owner's prediction, and finds the redundant and reducible steps. One reorganization is proved in a new
file with the original statements.

Claim marks as in `PROOF-SYSTEMS.md`. **[measured]** means computed from the compiled proofs by the read-only script in
`metrics/` (section 7); **[Lean]** means `ProofPhase/Proof/Native.lean` (`axioms-native.sh`, `axioms-native.log`).

---

## 0. The short answer

1. **The DMP proofs are constructive; the ProofPhase proofs are not.** **[measured]**
   * DMP: 91% of the gated theorems (259 of 285) use no `Classical.choice` at all; 70 use no axiom whatsoever. All 22
     existence statements are proved constructively: 18 with an explicit witness in the proof term, 2 by kernel
     computation, 2 by passing on an earlier witness.
   * ProofPhase: 4% are choice-free; 66% of its 133 existence statements carry an explicit witness.
   * In this precise sense the prediction holds: DMP asserts only existence it can exhibit.
2. **But the DMP proofs' main step is not usually a witness.** **[measured]**
   * Among the 161 DMP theorems no other theorem uses, witness-led proofs are 17 (11%).
   * The characteristic native step is **computation**: 64% of the DMP proofs use `rfl`, 36% `decide`, against 48% and
     6% in ProofPhase.
   * The longest DMP chains are ladders of "checker = proposition" lemmas (`independentB_iff`, `mintedB_iff`,
     `lineOkB_iff`, `wfB_iff`, `verdict_proven_iff`): a Boolean checker proved equal to the statement, one per level of
     the definition. After that the kernel evaluates the answer.

   So the existence DMP asserts is the **evaluated verdict**, a computation that comes out true. This is proof by
   reflection, the refined form of the prediction. **[reading]**
3. **DMP proofs are shallower and use fewer lemmas.**

   | | longest chain of named theorems: median / max | distinct theorems below one: mean / max |
   |---|---|---|
   | DMP | 1 / 7 | 1.9 / 19 |
   | ProofPhase | 2 / 14 | 8.4 / 159 |

   **[measured]**. Part of this is the subject matter: DMP's objects are finite, ProofPhase's are real analysis. The rest
   is organization (sections 2-3).
4. **Optimization, proved once.** My own `Cut.lean` (resolution) and `Crossing.lean` (every proof system) proved the
   same middle-line argument twice. `Native.lean` proves it once and recovers both main theorems with **exactly the same
   statements**, checked by the kernel. The two results now rest on 16 distinct lemmas instead of 21 (-24%). **[Lean]**
5. **Optimization, proposed.**
   * The longest ProofPhase chains end in regularity bookkeeping (measurability, continuity, congruence): 2 to 3
     levels at the bottom of each of the three deepest chains examined. In finite settings that is free with the
     discrete structure, or automatic with `fun_prop`.
   * The finite combinatorics in ProofPhase (`Proof/`) inherits `Classical.choice` from Mathlib in 79 of its 90
     theorems without any classical step of its own; a DMP-style core-Lean layer would make it constructive.
   * Lemmas used once (30% in DMP, 43% in ProofPhase) save names, not steps. In DMP each name is a gated claim tied to a
     sentence, so they stay.

   **[measured]** + proposal.
6. **What it means for the size question** (DMP section): reflection makes the proof term short and moves the cost into
   the kernel's computation. A native proof is short exactly when the question is efficiently decidable. For the coNP
   side, where no short certificate is known, the computation is the exponential search, so native optimization
   relocates the open step and does not remove it. **[reading]** on **[classical]**

---

## 1. What was measured, and how

A Lean metaprogram (`metrics/ProofMetrics.lean`) reads every theorem of a project from the compiled environment. It
inlines the compiler's auxiliary constants (matchers, abstracted sub-proofs) and records:

| Column | Meaning |
|---|---|
| `depthThm` | longest chain of named project theorems from this one down to a theorem that uses no other (the "longest chain from the axioms", counted in named steps) |
| `closureThm` | number of distinct project theorems below it (transitively) |
| `thmDeps` | project theorems used directly |
| `witness` | `Exists.intro`, `Subtype.mk`, `Sigma.mk` in the proof term: exhibiting something |
| `existsUse` | consuming a witness (`Exists.casesOn`, `Classical.choose`, ...) |
| `cases` | branching eliminations: case analysis on a type with at least two constructors, `match` with at least two arms, `if`, `Or.elim`, `byCases` |
| `induct` | recursion on a recursive type, well-founded recursion |
| `contra` | `False.elim`, `absurd`, `byContradiction`: closing a branch that cannot happen, or proof by contradiction |
| `classical` | an own classical step (`Classical.em`, `byContradiction`, `choice`, `choose`) |
| `decide`, `rfl` | kernel computation (`of_decide_eq_true`) and definitional equality (`Eq.refl`) |
| `axioms` | what the kernel says the theorem rests on (`Lean.collectAxioms`) |
| `goal` | the statement's head after its hypotheses: `exists`, `eq`, `iff`, `le`, `not`, ... |

**Limits.**
* The counts are of proof-term primitives, and tactics generate many of them: a `simp` that closes an impossible
  branch leaves an `absurd`. So "contradiction" mostly means "an impossible branch was closed" (constructive ex falso),
  not "proof by contradiction"; the latter is the `classical` column.
* ProofPhase rests on Mathlib, whose lemmas are not counted in depth or closure. DMP uses core Lean only.
* "Main theorems" are taken as the roots: theorems no other theorem of the project uses.

## 2. The numbers

**All theorems.** **[measured]**

| | DMP evidence (gated) | ProofPhase | ProofPhase/Proof (finite combinatorics) |
|---|---|---|---|
| theorems | 285 | 2757 | 90 |
| longest named chain: median / mean / max | 1 / 1.9 / 7 | 2 / 2.7 / 14 | 2 / 2.4 / 7 |
| distinct theorems below: median / mean / max | 1 / 1.9 / 19 | 1 / 8.4 / 159 | 1 / 3.7 / 37 |
| proof-term size: median / max | 265 / 19217 | 368 / 64894 | 381 / 6792 |
| no `Classical.choice` | **91%** | **4%** | 4% |
| own classical step | 4% | 4% | 8% |
| uses `decide` / `rfl` | 36% / 64% | 6% / 48% | 27% / 49% |
| contains a witness | 14% | 14% | 38% |
| contains a branching case split | 49% | 16% | 41% |
| contains a closed branch (`contra`) | 36% | 6% | 29% |
| contains induction | 12% | 1% | 23% |
| existence statements | 22 (8%) | 133 (5%) | 23 (26%) |
| of which with an explicit witness | 18 (and 4 more constructive, see section 0, item 1) | 88 (66%) | 18 |
| used by exactly one other theorem | 30% | 43% | 52% |
| thin wrappers (one lemma, no split, small) | 15 | 40 | 1 |

**Dominant shape of each proof** (first match in the order: induction, witness with contradiction, contradiction,
witness, case split, computation only, composition of lemmas). **[measured]**

| | DMP | DMP roots (161) | ProofPhase | ProofPhase roots (759) |
|---|---|---|---|---|
| composition of lemmas | 25% | 27% | 56% | 57% |
| closed branches (contradiction) | 24% | 23% | 4% | 3% |
| case split | 16% | 16% | 10% | 4% |
| induction | 12% | 7% | 1% | 1% |
| computation only | 11% | 17% | 15% | 24% |
| witness | 6% | 6% | 12% | 9% |
| witness with closed branches | 7% | 5% | 2% | 2% |

**Axiom profile of the DMP theorems.** 70 use no axiom; 81 only `propext`; 108 `propext` and `Quot.sound`; 26 add
`Classical.choice`. Of those 26, 12 take a classical step themselves; the other 14 inherit it from a core lemma.
**[measured]**

**The longest chains.** **[measured]**
* DMP, `Cmb.producer_minted` (7): `producer_minted`, `sealed_proven_complete`, `verdict_proven_iff`, `wfB_iff`,
  `lineOkB_iff`, `mintedB_iff`, `independentB_iff`. The two other depth-6 roots end in the same ladder. Every step
  below the top two says "this Boolean checker returns true exactly when the definition holds", one per level of the
  recipe (independent, minted, line ok, well formed, verdict).
* ProofPhase, `yang_mills_assembly` (12): the assembly and flux steps (`assembly_routeB`, `fluxGrowth_of_conjW`,
  `eventually_actRate`, `exists_fluxLimitSU2`, `exists_fluxLimit`, `exists_isTimeLimit`), two correlation bounds,
  then three measurability lemmas at the bottom.
* `Flip.su2_flipProb_lt_half` (13): ten content steps (polynomial ratios, Schur orthogonality), then three continuity
  lemmas at the bottom.
* `Mixing.spectral_gap_dobrushin` (10): the spectral chain and detailed balance (`rev`), then two congruence lemmas
  (`Zs_congr`, `update_congr_of_agree`).

16% of ProofPhase theorems (453) are regularity or side-condition lemmas by name (measurable, continuous, integrable,
congr, nonneg, pos, ...). In DMP there are 10, all congruence lemmas for the checker.

## 3. The owner's prediction, tested

**The prediction:** the DMP proofs are organized so that "the only thing that has to be asserted is existence that proves
the question provably true", and that organization is the native, optimal one.

| Reading of the prediction | Test | Result |
|---|---|---|
| Everything asserted to exist is exhibited (no existence without a construction) | choice-free theorems; existence statements proved with a witness | **Holds for DMP:** 91% choice-free, all 22 existence statements constructive. ProofPhase: 4% choice-free, 66% explicit witnesses. **[measured]** |
| The main step of a DMP proof is a witness | dominant shape of the roots | **Does not hold literally:** 11% of DMP roots are witness-led. The main steps are composition (27%), closed branches (23%), computation (17%) and case splits (16%). **[measured]** |
| The answer is a computation that comes out true (proof by reflection) | `rfl`/`decide` use; the checker-equals-statement ladder; worked layouts by `rfl` | **Holds:** 64% `rfl`, 36% `decide`; the longest chains are the reflection ladder; `Layouts.lean` computes verdicts by `rfl`. **[measured]** |
| DMP proofs are shorter or shallower | chain depth, closure | **Holds:** median chain 1 against 2, max 7 against 14, mean closure 1.9 against 8.4. Against the finite part of ProofPhase (`Proof/`) the gap narrows (max 7 against 7, mean closure 1.9 against 3.7), so it is part domain, part organization. **[measured]** |

**Verdict.** The prediction holds in a sharpened form. The existence DMP asserts is **the computed verdict**:
* each level of a definition gets a decision procedure;
* one lemma per level proves the procedure equal to the proposition (the `B_iff` ladder);
* the kernel then evaluates.

In set-theoretic terms, the asserted object is the evaluation, and the proof is "this computation exists and returns
true". Literal existence witnesses are a minority because most DMP statements are not existential (eq 100, other 37, and 32,
le 32, iff 25, exists 22): the native form of a universal law is a checked computation, not a witness. **[reading]**

## 4. Optimization, proved: one middle-line argument instead of two

**The redundancy.** `Cut.lean` (`PROOF-SYSTEMS.md`) and `Crossing.lean` (`DICHOTOMY-TRANSFER.md`) contain the same
argument twice: a measure created by no step, so a middle line exists, and that line sees the boundary.
* `Cut.lean` proves it for resolution clauses: `mu`, `implies_res`, `mu_res`, `mu_empty`, `exists_middle`,
  `mem_of_boundary`.
* `Crossing.lean` proves it for arbitrary lines: `muL`, `muL_inf`, `exists_middleL`, `sensitive_of_boundary`.

The resolution version is a special case, written out again.

**The reorganization** (`ProofPhase/Proof/Native.lean`, **[Lean]**; existing files unchanged):
* `SDG Ax G`: derivations whose every line has a property G. G = "is an `SD` line" gives every proof system; G = "is a
  clause of at most W literals" gives resolution of width W.
* `exists_middleG`, `crossG`: the one middle-line argument and the one crossing theorem, for any G.
* `WD.toSDG`: a resolution derivation is a derivation of clause lines. `mem_of_sensitive`: a clause that changes value
  when x flips contains x. These two are the whole resolution-specific part.
* `width_ge'` and `cross_any_system'`: **the same statements** as `ProofPhase.Proof.width_ge` and
  `ProofPhase.Proof.cross_any_system`. The kernel accepts `rfl` between each pair (`axioms-native.log`), which it does
  only when the two statements are identical.

**What it saves.** **[measured]**

| | before | after |
|---|---|---|
| distinct project theorems the two results rest on together | 21 | **16** |
| resolution-specific lemmas | 9 (`mu_le`, `mu_spec`, `mu_ax`, `mu_res`, `mu_empty`, `implies_res`, `WD.implies_univ`, `exists_middle`, `mem_of_boundary`) | 2 (`WD.toSDG`, `mem_of_sensitive`) |
| proof-term size of the width theorem | 1392 | 1087 |
| longest named chain: width / crossing theorem | 5 / 4 | 5 / 5 |

The saving is in distinct lemmas, not in chain depth: the general route has one more level for the crossing theorem.
This is the general pattern: removing a duplicated argument shrinks the closure, while depth is set by how many levels
the statement has.

**Checked and not taken:** a witness version of `mem_of_sensitive`. Take the literal that the flip makes true; it
names x. It still needs one decidable case split (is the literal's variable x or not), so it is no shorter. **[Lean]**
attempt not kept; reported for completeness.

## 5. Optimization, proposed

| Finding | Where | Native reorganization | Estimated saving | Level |
|---|---|---|---|---|
| Regularity bookkeeping sits at the bottom of the longest chains | ProofPhase: `yang_mills_assembly` (3 of 12 steps), `su2_flipProb_lt_half` (3 of 13), `spectral_gap_dobrushin` (2 of 10); 453 theorems (16%) by name | finite state spaces with the discrete measurable structure (everything measurable, as `Mixing/Classical.lean` already does); `fun_prop` and `measurability` for the rest | 2-3 levels on those chains; many one-use lemmas disappear | proposal |
| Finite combinatorics inherits `Classical.choice` from the library | `Proof/`: 79 of 90 theorems inherit choice with no classical step of their own | a core-Lean layer in DMP style (decidable checkers, `decide`) for the finite parts | constructive results; a resolution refutation becomes a checkable, computable object | proposal |
| Lemmas used exactly once | DMP 85 (30%), ProofPhase 1183 (43%) | inline | saves names, not logical steps. In DMP each name is a gated claim tied to a DMP sentence: keep | measured; no action for DMP |
| Thin wrappers (one lemma, no split) | DMP 15, ProofPhase 40 | inline or state as `abbrev` | small. The DMP ones restate DMP sentences (e.g. `same_part_is_no_duality`), which is their job | measured; no action for DMP |
| Parallel developments of one argument | `Cut.lean` / `Crossing.lean` | one general theorem plus one translation per proof system | 21 to 16 lemmas | **[Lean]**, section 4 |
| Case splits that a witness would remove | searched: proofs with both a witness and closed branches (DMP 19, 12 of them in `R1Bridge`, where the model is checked row by row; ProofPhase 58) | none found that a witness removes: the closed branches are the impossible rows of a finite check | none | measured |

**The irreducible core.** After the proposed reorganizations, what remains is, per main theorem:
* in DMP, one step per level of the definition (the reflection ladder) plus the top-level composition;
* in ProofPhase, the chain minus its regularity bottom (9 of 12 for `yang_mills_assembly`, 10 of 13 for
  `su2_flipProb_lt_half`).

These counts are the "irreducible steps in the logic chain" in the owner's words, measured. **[measured]** +
**[reading]**

## 6. DMP reading (separate, marked)

Everything here is **[reading]** unless marked otherwise.

* **"How many irreducible steps are truly needed from the base axioms that define existence to the fact of the
  answer."** In DMP's own Lean that number is the depth of the reflection ladder:
  * independent;
  * minted;
  * line ok;
  * well formed;
  * verdict;
  * sealed;
  * producer.

  One step per level at which existence is defined, measured at 7 for the deepest root **[measured]**. Each step proves
  that a computation equals a definition, and nothing else is asserted.
* **"Only existence that proves the question provably true is asserted."** Measured form: 91% of the gated DMP theorems
  use no choice, and every asserted existence is exhibited or computed. Where the statement is not existential, the
  native form is a checked computation (`rfl`, `decide`), so the asserted existence is the evaluation itself. That is
  the Curry-Howard reading of the owner's words: a proof is a program, and DMP's proofs are programs that run.
* **What native optimization does to the size question.** Reflection makes the proof term short (one lemma per level,
  then "compute") and moves the cost into the kernel's computation.
  * For a question that is efficiently decidable, the computation is short, and so is the native proof.
  * For an unsatisfiable formula with no known short certificate (the coNP side of `PROOF-SYSTEMS.md`), the
    computation is the exhaustive check. A reflective proof is then a short term whose checking takes exponential time,
    which is the same open question measured in kernel time instead of proof length (Cook-Reckhow counts both:
    verification must be polynomial).

  So native optimization is the right way to build proofs, and it does not touch the open step: it relocates it from
  "how long is the record" to "how long does the record take to check". **[reading]** on **[classical]** (proofs by
  reflection; Cook-Reckhow's polynomial-time verifier)
* **The real-world check of our own construction.** The DMP evidence is built the native way and measures as such:
  constructive, shallow, computed. ProofPhase is built the classical-analysis way, and its depth is part content, part
  bookkeeping. The bookkeeping is where a native reorganization saves. Where ProofPhase repeats itself, a native
  reorganization saves distinct lemmas, as `Native.lean` shows.

## 7. Files and how to re-run

| File | What |
|---|---|
| `metrics/ProofMetrics.lean` | the read-only metaprogram: per-theorem metrics, longest chains (`showChains`) |
| `metrics/analyse.py` | the summary tables |
| `metrics/run-metrics.sh` | copies `evidence/` and the formal project into a build folder, builds the copies, runs both; writes `metrics/report.txt` |
| `metrics/report.txt` | the summary this note quotes |
| `../mass-gap/formal/ProofPhase/Proof/Native.lean` | the reorganization of section 4 |
| `axioms-native.sh`, `axioms-native.log` | build, same-statement check, axioms (11 declarations, standard axioms), source grep |

Re-run from the repository root inside the WSL replay distro (Lean 4.34.0):
* `bash docs/pnp/metrics/run-metrics.sh`, after seeding the build folder with a built `.lake` of the formal project;
* `bash docs/pnp/axioms-native.sh > docs/pnp/axioms-native.log 2>&1`.

Nothing under `evidence/`, `vendor/dmp/` or existing Lean was changed; the script works on copies.
