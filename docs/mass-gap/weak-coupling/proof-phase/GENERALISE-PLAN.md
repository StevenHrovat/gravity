# Plan: the proof over any compact simple gauge group, with d explicit (2026-11-23, concept, not started)

The owner asked for this plan ("Yes, plan like that please", 2026-11-23), after the reading in `PREP.md` "Can DMP extend to d >= 4".
This note is the concept. Building it needs the owner's OK.

## Why

- **The gauge group is required, not optional.** The Clay problem asks for every compact simple gauge group G, not only SU(2). Today
  the proof is written for SU(2). Generalising to G is therefore part of the goal, and doing it now shapes the remaining work (P4, the
  IR side, the vortex layer) so that it never has to be redone.
- **d is a clarity win.** The problem fixes d = 4, so d as a parameter proves nothing new. Its value is that every place where 4 is
  used becomes a named hypothesis `hd : d = 4`. A reader (or reviewer) then sees at once that the proof uses d = 4 in exactly the
  places the physics says it must: Balaban's marginal scaling and the vortex-sheet capacity.

## What exists (survey, 2026-11-23)

- The base object is already generic: `GaugeConnection G d N` (`AreaLaw/Lattice.lean`) takes the group G and the dimension d.
- About 20 folders of `ProofPhase` (119 files; an earlier count of 176 was a counting slip) mention SU(2) in code, about 960 times. Most are instantiations at the end of a generic
  argument. The substance sits in a few places: the strict flip bound (`Flip/Strict.lean`, 1217 lines, built on explicit 2x2
  matrices), the one-box cube estimates (`OneBox2/`), the blocking projection onto SU(2) (`RouteA/Blocking.lean`), the kernel density
  (`Book/KernelDensity.lean`) and the Z2 centre layer of M1.
- `d := 4` or `Fin 4` appears in code about 85 times, in about 20 files.
- The newest modules (OS, CouplingDS, the assembly, Interface) already take G and d as parameters or are abstract.

## The shape after generalising

1. **A gauge-group package.** One structure collects what the proof uses from the group: compact, with its Haar measure; a finite
   centre Z(G); the adjoint quotient G/Z(G); the Wilson character (real part of the trace) with its bounds; the twist by a central
   element. SU(2) is the first instance (centre Z2, quotient SO(3)); SU(N) is the second (centre Z_N).
2. **M1's split becomes G/Z(G) and the centre layer Z(G).** The mod-2 Stokes blocking becomes mod-N; the decoder and the label gas
   carry a Z_N label instead of a Z2 one. On paper this is mostly bookkeeping; the one real check is that the strict flip bound
   (twisted partition function below the untwisted one for nonzero coupling) holds for every nontrivial central twist.
3. **d explicit.** Generic modules take d; the two Balaban places take `hd : d = 4`.

## Phases

| Phase | What | Who | Size |
|---|---|---|---|
| 0 | Read-only audit: for each module, generic / SU(2) only by instantiation / SU(2) in substance; the same for d. A table. | Haiku subagent | small |
| 1 | The gauge-group package, and generic versions of the instantiation-only modules, written as new modules beside the old ones. The old SU(2) theorems are re-derived as one instance, so the gate stays at 285 and grows. | one Sonnet session, after the running Lean sessions return | medium |
| 2 | The SU(N) instance: centre Z_N, Haar, character bounds (Mathlib has the special unitary group; the centre needs work) | same session | medium |
| 3 | Substance: the strict flip bound for every central twist, the Z_N centre layer of M1 on paper, and the d-explicit Balaban places | Opus session, reviewed by REVIEW-2 and REVIEW-3 | large |

## Rules for the build

- **Nothing existing is edited**: new generic modules sit beside the SU(2) ones. Each phase ends with the old SU(2) statements as
  corollaries of the generic ones, so nothing proven is put at risk.
- **Order**: phase 1 starts only after the crossover and ScaleHyp sessions have reported, so no two sessions write Lean at once.
- **Not a GPU matter**: this is paper and Lean only.

## Recommendation

Run phase 0 now (cheap, read-only), and start phases 1-2 as one session when the running Lean sessions are back. Phase 3 waits until
P4 and the IR side have settled, because they decide which group facts the proof finally needs.
