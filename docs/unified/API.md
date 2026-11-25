# The form layer as a pure API: add a new problem in seven steps

2026-11-23, extended 2026-11-24. Lean: `docs/mass-gap/formal/ProofPhase/API.lean` (the facade), `API/Template.lean` (a worked toy),
`API/YangMills.lean`, `API/GRH.lean`, `API/NP.lean` (the three problems in the API's shape), `API/Phase.lean` (the G0 link, section 8). Axioms: `api-axioms.sh`,
`api-axioms.log` (standard axioms only: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`). Background: the owner's
reading in `mass-gap/weak-coupling/PREP.md` ("every problem is a well-defined input plus a proved structure"),
`UNIFIED.md`, `ENCODER.md`, `ETM.md`, `TRANSPORT.md`.

**Status marks.** **[Lean]** = proved in Lean, standard axioms only. **[open]** = not proved by anyone; it enters the Lean
only as a named hypothesis, in the `OpenStep` slot. Nothing here proves a problem; the API makes each problem's shape, and
its one open step, the same and easy to see.

---

## 1. In plain words

The form layer says nothing about content, so it can be used for anything. Every problem the project treats has the
same shape:

1. a **well-defined input** (a chain of boxes, a model of zeros, a proof system, a coin);
2. a **proved structure** on it: something carried along a chain of steps, each step paying a price (a factor between 0
   and 1, or a cost with a floor), plus the theorems that follow for every such chain;
3. **one named open step**: the single statement about the running state that nobody has proved (each step pays more than
   the floor; no step overdraws the margin; a crossing cost exists).

The API is one import that gives the structures for 2 and the two slots for 3. To use it you fill in the structures with
your input and write your open step in its slot. The ledger, transport, settle and decidability theorems then come for
free.

```lean
import ProofPhase.API
open ProofPhase.API
```

It is a facade: it moves and renames nothing in the existing form layer, and its theorems are re-exports or one-line
wrappers of it (so checking it adds almost nothing, see section 5).

## 2. What is in the API (one structure per concept)

| concept | in Lean | you supply | you get for free |
|---|---|---|---|
| a running system | `RunSys δ` | states, `step`, `fac x ∈ [0,1]`, `mass x ≥ 0`, the ledger law `mass (step x) ≤ e^δ fac x mass x` | `S.carry`, `S.contract`, `S.decay_cost`, `S.trace` (unique map into the ledger space) |
| the settle bound | `settle`, `settle_everywhere`, `settle_iff_bounded`, `balanceBound` | `S.Contracting θ` (every factor ≤ θ, `e^δ θ < 1`) | an explicit step count after which the mass is below any `ε` |
| the decidability edge | `edge` | nothing | cost above the floor: decided, explicit bound; cost = floor (the lossless `etm`): universal and undecidable |
| a chain with costs | `Chain δ` | a quantity `M ≥ 0`, costs `c`, `M (i+1) ≤ e^{δ − c i} M i` | `Chain.ledger`, `Chain.decay`, `Chain.summable` (gap = cost − floor), `Chain.size`, `Chain.size_log` |
| a margin that survives | `Margin` | `M`, shares `f ≥ 0`, `f i · M i ≤ M (i+1)` | `Margin.survive`, `.nonneg`, `.pos` |
| an encoder at a boundary | `Encoder 𝕜 E` | a state and its rotated image of the same norm | the reflection coefficient, `szegoFactor`, `elecFactor` (both in `[0,1]`), `cost`, the duality |
| an uncertainty | `Uncertainty δ` | `e`, `f`, `r`, `e (i+1) ≤ e^δ f i e i + r i` | `.bounded`, `.critical`, `.sign`, `.sign_of_bounded`; a run is the case `r = 0` (`RunSys.uncertainty`) |
| the problem card | `Problem` | input type, `Open`, `Concl`, `proved` | `Problem.holds` |
| the open-step slot | `OpenStep "name" P` | the one statement `P` | a label; `P` itself |
| the external-input slot | `External "source" P` | a theorem imported from the literature | a label; `P` itself |

The slots are transparent: `OpenStep "…" P` *is* `P`, so a theorem takes `(h : OpenStep "…" P)` as an ordinary hypothesis.
Nothing is ever an axiom. The labels make the open steps and the outside dependencies greppable:
`grep -rn "OpenStep\|External" ProofPhase/`.

Two horizons. `Chain` and `Uncertainty` are for an infinite chain (all steps). For a finite horizon (a fixed number of
restrictions, as in NP vs coNP) use the raw `Pays` and `size`, which the API re-exports.

## 3. To add a new problem

The example for every step is `API/Template.lean`: a coin that flips with probability `p`, and two observers whose beliefs
are `a` and `b`. Do the steps in order; each is a few lines.

1. **Copy the template.** Copy `API/Template.lean`, rename the namespace, keep `import ProofPhase.API`. Nothing else is
   needed to start.
2. **Write the input.** The data the problem is stated on, as plain definitions and numbers; in the toy, `flip p a`, one
   tick of the chain. Put what a reader must see first (which input values are allowed) into a structure or hypotheses
   (the toy: `0 ≤ p ≤ 1`).
3. **Build the running system and check the ledger law.** Fill a `RunSys δ`: states, step, the factor in `[0,1]`, the
   mass, and prove the one inequality `mass (step x) ≤ e^δ · fac x · mass x` (the toy: `chain`, with the factor
   `|1 − 2p|` and the mass `|a − b|`; the proof is one line). If your quantity is a stream rather than a state
   system, fill a `Chain` (costs and floor) or a `Margin` (shares kept) instead; the YM instance does this
   (`API/YangMills.lean`, `chain`). The factor can also come from an `Encoder` (the Szego or electric factor, in `[0,1]` by
   positivity); no encoder is needed in the toy.
4. **Write the open step in its slot.** One statement, with a plain-words name:
   `def Mixing p : Prop := OpenStep "the coin is neither fixed nor always flipping" (0 < p ∧ p < 1)`. It is usually
   "the system is in the contraction class" or "this cost exceeds the floor". If you can prove it, prove it (the toy:
   `mixing_quarter`); if not, leave it as the hypothesis of your theorems. External theorems from the literature go in the
   `External "source" P` slot the same way.
5. **Get the theorems for free.** Call the API on your system: `S.carry`, `S.contract` (decay), `settle_everywhere` and
   `settle` (an explicit step count, the toy: 101 steps to `1/100`), and `Chain.decay` / `Chain.summable` for a chain.
   The toy shows each in one line (`toy_carry`, `toy_decay`, `toy_settles`, `toy_settle_101`).
6. **Add uncertainty if the input is only known approximately.** Fill an `Uncertainty` (error bound, factor, fresh
   uncertainty per step) and get bounded transport and sign preservation (the toy: rounding errors in the computed
   beliefs, `noisy`, `toy_bounded`, `toy_sign`).
7. **State the card.** `def problem : Problem := { name, Input, Open, Concl, proved }`: the input, the one open step,
   the conclusion, and the proof of "open step gives conclusion" (usually a call to step 5). A reader then sees the
   uniform shape in a dozen lines. `API/YangMills.lean`, `API/GRH.lean`, `API/NP.lean` are three such cards.

The whole skeleton, with `…` for your content (the toy fills it in `API/Template.lean`):

```lean
import ProofPhase.API
open ProofPhase.API

def mySystem … : RunSys δ where        -- step 3: the proved structure
  X := …;  step := …;  fac := …;  mass := …
  fac_nonneg := …;  fac_le_one := …;  mass_nonneg := …;  pays := …

def MyOpenStep … : Prop := OpenStep "plain-words name" (…)        -- step 4: the one open step

theorem my_result (h : MyOpenStep …) … := settle_everywhere mySystem … -- step 5: free theorem

def problem : Problem where            -- step 7: the card
  name := "…";  Input := …;  Open i := MyOpenStep …;  Concl i := …;  proved i h := my_result h
```

**Check it.** Build the file (`bash docs/mass-gap/formal/sync-build.sh ProofPhase.API.<YourFile>`), then run the axiom audit
(copy `api-axioms.sh` and add your module): it must show only `propext`, `Classical.choice`, `Quot.sound`. An `OpenStep`
or `External` hypothesis never appears as an axiom, because it is a hypothesis.

## 4. The three problems in the API's shape

| | input | structure (proved) | the one open step (`OpenStep`) | conclusion | external input |
|---|---|---|---|---|---|
| Yang-Mills (`API/YangMills.lean`) | boxes with `d` continuations, weights `≤ e^{−Fe}`, a chain of outsides | the path sum is a `Chain`, cost `Fe`, floor `log d` | O1: `YMOneBox`, the cost of one box exceeds `log d`, over every outside | decay rate `κ − log d > 0`, summable | none |
| GRH (`API/GRH.lean`) | a finite model of zeros on a grid | margin carried per scale; `ScaleSign` is positivity of Weil's form | `ScaleSign`: no scale step overdraws the margin | zeros on the line; Weil pairing `≥ 0` | `tie_in`: Mathlib's `RiemannHypothesis` (`ExtRH`) gives `ScaleSign` for zeta |
| NP vs coNP (`API/NP.lean`) | a proof system (its refutations), cost `θ`, `b` restrictions | restrictions pay cost `θ` per step (finite-horizon `Pays`), one line left is the quantum (`size`) | `CrossingCost`: `b` restrictions, each keeping at most `1 − θ` of the costly lines | every refutation has at least `e^{θ b}` lines | `lifted`: GGKS lifting (`LiftCP`) for cutting planes |

Each card is `Open i → Concl i`, proved by the existing theorems (`Unified/YangMills.lean`, `GRH.lean`, `ProofSize.lean`);
the API files add no mathematics. **[Lean]** for each "open step gives conclusion"; **[open]** for each open step.

## 5. Cost, limits, and where things went

* **Size.** `API.lean` has about 50 top-level commands (5 structures, 5 abbreviations, 8 definitions, 22 theorems, most of them
  one-line calls into the form layer, 4 aliases, 5 export lines); the template 25, the three problem
  files 4, 3 and 3, the G0 file 2 (the audit counts 231 constants including what Lean generates for structures). No proof is duplicated.
* **Measured** (2026-11-24, `tools/independent-check.sh quick`, stamp matched, result PASS; run twice, the second time with the
  computable layer and the phase file added): the six API modules replay in about 3 minutes when the machine is idle
  (`API.lean` 128 s cold, the examples 8 to 15 s each; 442 s for `API.lean` on a busy machine); the whole quick run took
  25 to 32 minutes because it also re-checked other changed modules of other rounds. Build: seconds each on top of the form
  layer. Axiom audit of all six: `api-axioms.log` (231 constants, none non-standard).
* **What it does not do.** It does not prove any open step and it adds no new mathematics. It does not turn a
  problem into a running system for you: step 3 (the structure and its one inequality) is the work, and the open step is
  whatever it is. Interface-only arguments cannot settle P vs NP (relativization); the NP card inherits that.
* **A note on `RunSys` theorems.** `RunSys` is an `abbrev` of `ETM.RunSys`; use dot notation (`S.carry x n`,
  `S.contract h x n`). `settle`, `settle_everywhere`, `edge` are plain functions (`settle S hS x …`).
* **Mapping to the existing names.** `Pays`/`carry`/`ledger`/`decay`/`size`/`survive` = `Unified/Ledger.lean`; `Encoder`
  = `Unified/Encoder.lean`; `Transports`/`transport`/`bounded_transport`/`critical_transport`/`sign_transport` =
  `Unified/Transport.lean`; `RunSys`, `Contracting`, `balanceBound`, `etm_edge` = `ETM/RunSys.lean`, `ETM/Machine.lean`.

---

## 6. What runs and what is truth only

A running system replaces a *choice* by a *link to G0*: every decision it makes has a computable form, and a theorem says
the computed answer is right for the real-valued system. The real-valued structures are classical statements (the truth
side); they are not computed. The template runs its decisions: `ticksNeeded (1/4) (1/100)` evaluates to `101` when the
file is checked (`#eval`), the computed distance after that many ticks is checked by `#guard`, and `ticksNeeded_correct`
proves the computed answer right for the real chain.

| API item | runs (computable) | truth only (classical, `noncomputable`) |
|---|---|---|
| `balanceBound M ε q` (the settle count) | yes, a `ℕ` from rationals | |
| `settle0` (floor 0, rational `q < 1`, rational `ε`) | the count runs; its hypotheses are decidable inequalities on `ℚ` | the conclusion about the real system |
| `szegoQ`, `elecQ` (encoder factor from a rational coefficient) | yes; `szegoQ_cast`, `elecQ_cast` equal the real factors | the real `szego`, `elec`, `Encoder.refl` |
| `PaysQ M f n` (ledger law on rational data) | yes, `Decidable` (`decide`, `#guard`); `PaysQ.pays` gives the real ledger | `Pays`, `Chain`, `Margin` |
| the ETM step and balance test (`estep_primrec`, `halted_primrec`) | yes, primitive recursive | |
| `RunSys`, `Contracting`, `Uncertainty`, transport bounds | | real-valued statements and proofs |
| `etmTruth` (does the ETM reach balance?) | | yes: binary, total, not computable (`etm_truth_edge`) |
| `edge` (decidable above the floor, undecidable at it) | the bound on the contraction side | the undecidability on the lossless side |
| `OpenStep`, `External` | | hypotheses, never computed |

Rule for a new instance: give each decision a rational (or finite) form with an explicit bound, a witness or a decidable
check, and prove it right once against the real system (the template's `ticksNeeded_correct` is the pattern); keep the
truth statement marked.

## 7. Extracting the core into a standalone package

The core (the part that must stand alone) is exactly the import closure of `API.lean`: it imports Mathlib and nothing
else, so it works with Lean and Mathlib alone (checked: the six files below import only each other and Mathlib).

**Moves (the core, six files):**

| file now | imports | new module (proposal) |
|---|---|---|
| `Unified/Ledger.lean` | `Mathlib` | `Form.Ledger` |
| `Unified/Encoder.lean` | `Unified.Ledger` | `Form.Encoder` |
| `ETM/RunSys.lean` | `Unified.Ledger` | `Form.RunSys` |
| `ETM/Machine.lean` | `ETM.RunSys`, `Unified.Encoder` | `Form.Machine` |
| `Unified/Transport.lean` | `ETM.RunSys` | `Form.Transport` |
| `API.lean` | the four above | `Form.API` |

Plus, for the phase field (section 8): the part of `General/GUCharge.lean` that proves `circle_char` (its lines up to
and including `circle_char`; checked to compile with `import Mathlib` alone; the later items use `General/GUCentre`) as
`Form.Phase`, and `API/Phase.lean` then becomes the core's own discharge of `ChargeQuantisation`.

**Stays (instances, import the core):** `API/Template.lean` (imports only `API`; it may travel as the package's example),
`API/YangMills.lean`, `API/GRH.lean`, `API/NP.lean`, and every module of the existing form layer that is not in the table
(`Unified/YangMills.lean`, `GRH.lean`, `ProofSize.lean`, `Blowup*.lean`, `ElectricSUN.lean`, the `*Instances.lean`,
`TransportBridges.lean`, `ETM/Instances.lean`, `ETM/Rooted.lean`, ...). Moving renames only the `import` lines: 12 existing
files import a moved module and would change `import ProofPhase.Unified.Ledger` to `import Form.Ledger` (and the same for
the others); the Lean namespaces (`ProofPhase.Unified`, `ProofPhase.ETM`, `ProofPhase.API`) can stay as they are, or be
renamed in one pass. The library root must not be `ProofPhase`: a second package may not define modules of the same
name.

**Where it lives (the owner's rule: what can be transferred moves to DMP.IM and is used from there as a dependency,
never vendored).** A sibling Lake package inside the `im` repository, `form/`, next to the existing Mathlib-free `Im`
package, which stays untouched:

```
im/form/lean-toolchain          leanprover/lean4:v4.34.0
im/form/lakefile.toml
im/form/Form.lean               (imports the modules above)
im/form/Form/Ledger.lean  Encoder.lean  RunSys.lean  Machine.lean  Transport.lean  API.lean  Phase.lean
```

`im/form/lakefile.toml`:

```toml
name = "form"
version = "0.1.0"
defaultTargets = ["Form"]

[leanOptions]
autoImplicit = false

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.34.0"

[[lean_lib]]
name = "Form"
```

`gravity-ym/docs/mass-gap/formal/lakefile.toml` then depends on it by git (the `rev` is the `im` commit that holds
`form/`):

```toml
[[require]]
name = "form"
git = "https://github.com/StevenHrovat/im"
subDir = "form"
rev = "<commit of im that contains form/>"
```

Both packages pin the same Mathlib (`v4.34.0`), so the dependency adds no second Mathlib build. This repository's
`independent-check.sh` and `sync-build.sh` copy only the project's own libraries; after the move they need the dependency
fetched (`lake update`), a separate step. The move itself, and the `im` repository, are not touched by this round.

## 8. What the G0 link gives every instance

G0's phase field is one compact `U(1)`: Mathlib's `Circle` (`Phase` in the API). A label carried on it is a continuous
character of the circle (`PhaseLabel`). The classical fact (Pontryagin duality for the circle) is that every such
character is `z ↦ z ^ n` with `n` an integer, so **every label carried on the G0 circle is quantised**: charge is an
integer, with no further assumption. This is the one checkable consequence of being linked to G0 that holds for every
instance, not only for one problem.

* **Core:** `ChargeQuantisation` (the statement), `PhaseLabel.charge` (takes the statement as an `External`
  hypothesis, so the core does not depend on where the proof lives).
* **Proved:** `API/Phase.lean`, `chargeQuantisation` and `PhaseLabel.integer_charge` (no hypothesis), from the GU round's
  `circle_char` (`General/GUCharge.lean`: Fourier coefficients and Parseval on `AddCircle`; **[Lean]**, classical
  mathematics). Nothing is duplicated.
* **Used by:** `g0_charge_thirds` in `General/GUCharge.lean` is the GU instance of it (hypercharge on the circle, the
  `Z_6` selection, charges in thirds).
* **Contrast** (`line_char`, same file): on the real line every real `a` gives a character `t ↦ e^{i a t}`; it is
  quantised only when the phase group is compact. Compactness of G0's phase is exactly what forces integer charge.
