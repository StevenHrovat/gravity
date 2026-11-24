# The rotation API: one box, one command, one test (2026-11-24)

Lean: `docs/mass-gap/formal/ProofPhase/ETM/Rotation.lean` (core) and `ETM/RotationInstances.lean` (instances), imported
by the ETM summary `ETM/ETM.lean`. 75 declarations, standard axioms only (72 on `propext, Classical.choice, Quot.sound`,
3 on none), no `sorry`, `admit`, `native_decide` or `axiom`: `docs/unified/rotation-axioms.log`, made by
`docs/unified/rotation-axioms.sh`. The open statement X.64 appears once, as a named hypothesis (`OpenStep`), never as an
axiom.

**The core is in IM (2026-11-24).** The marker, the generic box and its test, the two-sided gate, the one-box and scale
certificates, the finite check and the vacuity checks moved to IM's arsenal, `arsenal/Arsenal/Rotation.lean`
(`StevenHrovat/im#11`, Mathlib only, the sharing answered `R136a1 "the gate is shared across scales"`); gravity pins it in
`lakefile.toml`. `ETM/Rotation.lean` keeps the running-system box (ledger, margin as a cost above the floor, balance marker,
contraction class, universal machine): `Box.toArsenal` forgets the mass, its definitions agree with IM's by `rfl`, and the
generic theorems are IM's, applied. The axiom log now covers 77 declarations on the gravity side.

## 1. What was built

**The box** (`Box δ`). A running system `S : RunSys δ` (from `ETM/RunSys.lean`: the step, the gate factor `fac`, the mass,
the ledger law) with:

* **one command**, the step at the one shared gate (the universal tick);
* a **gate margin** `θ` with `e^δ θ < 1`, i.e. a cost above the floor;
* the **marker** the box produces at each state, `inside` or `r136a1` (DMP's marker for "outside").

There is no outside input. The outside is read through the same gate by the **half-turn** (`Gate`: a reading from
inside, a reading from the other side, and the flux law saying they agree). `complete_halfTurn` proves that the test read
after the half-turn is the same test. The concrete half-turn is the plaquette layer: for a closed `ℤ/2` layer the flux
read from a box and from its complement agree (`crossoverGate`, from `cob_restrict_eq_cob_restrict_compl`).

**The test.** The gate's own verdict at a state is `inside` when the gate factor is within the margin and `r136a1`
otherwise (`gate`). The marker is **correct** when it agrees with that verdict (`Correct`). Nothing outside the box is
consulted, so the test is not circular. `DMPComplete x` means every tick from `x` gives the correct marker. One wrong
marker means not DMP-complete. `Settles x` means correct from some tick on.

## 2. The theorems and their status

| # | Statement | Lean name | Status |
|---|---|---|---|
| 1a | **One-box certificate**: if the marker is correct at the start and one step at the shared gate keeps it correct, it is correct at every tick | `Box.onebox_certificate`; exact form along the run `Box.dmpComplete_iff_orbit` | Lean |
| 1b | **Scale certificate**: if every scale's box is rebuilt from the one box through its gate (`SharedGate`: same margin, a morphism of running systems that keeps step, gate factor and mass, sends start to start and carries the marker), then a box certified at one scale is correct at every scale | `Box.scale_certificate`, `Box.onebox_everywhere` | Lean from the named hypothesis X.64 (`OpenStep "X.64: ..."`) |
| 1c | Falsifiability of the sharing: a certified one box plus one scale with a wrong marker refutes `SharedGate` for that family; the sharing is satisfiable (the box with itself) | `Box.not_shared_of_wrong`, `Box.sharedGate_self` | Lean |
| 1d | Sharing the gate alone is free: every box's verdict is read through its trace into the terminal object. What X.64 adds is that the **marker** travels with the gate | `Box.gate_through_trace` | Lean |
| 2a | **The universal machine is a box** (`etmBox`: the ETM, margin 1/2, balance marker). It is lossless, so its gate reads `r136a1` at every state. It is DMP-complete from a description exactly when the description runs forever | `etmBox`, `etmBox_gate`, `etmBox_complete_iff` | Lean |
| 2b | **The price**: `DMPComplete` is not decidable for all content; neither is `Settles` | `etmBox_complete_undecidable`, `etmBox_settles_iff`, `etmBox_settles_undecidable` (from `etm_balance_undecidable`) | Lean |
| 2c | **Contraction class** (cost above the floor), balance marker: from the explicit tick `balanceBound M ε q` on, every marker is correct, so `DMPComplete` is a finite check of the ticks below the bound | `Box.settles_of_contracting`, `Box.complete_iff_bounded`, `Box.settles_of_contracting'`; both sides together: `rotation_edge` | Lean |
| 3a | **Yang-Mills, chain form of O1**: O1 (`YMOneBox Fe μ`, `μ ≥ 1`) holds **exactly** when some margin makes every chain of outsides DMP-complete (gate factor `min 1 e^{−Fe}`, floor `log μ`, claim `inside`). Both directions | `o1Box`, `o1_iff_complete` | Lean |
| 3b | **Yang-Mills, Wilson measure**: `FineOneBox T` holds **exactly** when, for some valid box geometry and some margin `θ < 1`, the Yang-Mills box is DMP-complete from its start level. Both directions | `Geo`, `LevelBox`, `ymFac`, `ymBox`, `fineOneBox_iff`, `ym_complete_iff`, `fineOneBox_iff_complete` | Lean |
| 3c | `FineOneBox` gives the correct marker at every level from `k₀` (every volume); a DMP-complete Yang-Mills box gives the one-box assembly (decay, gap in both orders, RP, with non-triviality as input) | `fineOneBox_correct`, `ym_assembly_of_complete` | Lean |
| 3d | The Yang-Mills box **is** DMP-complete | none | open (it is `FineOneBox`, i.e. O1; conditional on X.64) |
| 4 | **Navier-Stokes**: with the energy-only transfer bound `K 2^{5k/2}` against the viscous cost `ν 4^k` as gate factor (clipped to [0, 1]) and the claim `inside` (regular) at every dyadic scale, the gate reads `r136a1` at some scale, so the marker is wrong there and the box is not DMP-complete; for every `ν, K > 0` and every margin `θ < 1` | `nsBox`, `ns_gate_outside`, `ns_wrong_marker`, `ns_not_complete` (from VI.3.4b, `dyadic_supercritical`) | Lean (model, as VI.3.4b) |
| 5 | Vacuity: a box whose marker is its own gate verdict is always DMP-complete; a box with a wrong marker exists | `Box.selfMarked_complete`, `Box.exists_not_complete` | Lean |
| | The round in one statement (1a, 1b, 2b, 3a, 3b, 4) | `rotation_round` | Lean (1b from its hypothesis) |

## 3. Care points

1. **The marker must be the system's own claim.** If the marker is read off the gate afterwards, every box passes
   (`selfMarked_complete`). The class has content only when the instance fixes the marker. For Yang-Mills and
   Navier-Stokes the claim is "inside at every scale". DMP-completeness is then exactly "the gate reads inside at every
   scale", so all the content sits in the gate factor. That is why the equivalences 3a and 3b are the guard against a
   vacuous class: for Yang-Mills the class carries exactly O1, no more and no less.
2. **X.64 is carried, not proved.** It enters only as the hypothesis of `scale_certificate` (`SharedGate`). The owner's
   reason for it, "every tick can be reconstructed from any scale because of GRH", is not in Lean. Our GRH-to-O1 work
   shows that GRH supplies the sign, not the floor, so "certified on the box, hence everywhere" stays conditional on X.64.
   1d sharpens what X.64 says: sharing the gate is free (every system maps uniquely into the terminal object); the
   assumption is that the marker travels with it.
3. **Where the Yang-Mills converse needs uniformity.** 3b goes through because the box geometry (cells, cell constants,
   the rate λ, the box diameter D₀, the box size n_max, the start level k₀) is part of the box and fixed across levels.
   The gate factor at level `k` is then the best one-box ratio at that level (an infimum, `ymFac`), and a margin θ < 1 at
   every level gives one ratio `γ = (max θ 0 + 1)/2 < 1` for all levels. If each level could choose its own geometry, the
   converse would fail: DMP-completeness would give level criteria whose constants drift with the level, and
   `FineOneBox`'s decay constant needs them uniform. That uniformity is precisely the shared-gate content (care point 2).
   "Every scale" means every level from k₀, in every volume; levels below k₀ are not tested.
4. **`ymFac` is a reading, not an estimate.** It is a classical infimum (not computable). The Yang-Mills box restates
   `FineOneBox` in the test's language and proves no new bound. The mass of every chain box is the running product of the
   factors; it only makes the ledger law hold and carries no content.
5. **Navier-Stokes is at model level, and only for the energy-only ledger.** The gate factor uses the two scalings of
   VI.3.4b as given exponents. Lean shows that the energy-only ledger contradicts the claim "regular at every scale" at
   some scale. It says nothing about an actual solution, whose transfer may be bounded better than by the energy alone;
   that gap is the open problem. "Not DMP-complete, hence blowup" stays the reading VI.7e.
6. **The ETM uses the balance marker** ("inside" once the run is within ε of balance). On the contraction class the
   early ticks (mass still above ε) can carry a wrong marker, so the right notion there is `Settles`, and
   `complete_iff_bounded` makes `DMPComplete` a finite check. On the ETM both notions are undecidable. The ETM is
   DMP-complete exactly while its content runs, which matches "the one box is a *running* system".
7. **The half-turn in Lean** is the flux-law equality. The box reads its gate factor; `complete_halfTurn` says that
   reading the gate from the other side changes nothing, provided the inside reading is the factor. Building a two-sided
   gate for the Yang-Mills box itself (factor read from the outside configuration) was not attempted.
8. **Build cost.** The ETM summary `ProofPhase.ETM.ETM` now imports `RotationInstances`, which pulls `OneBox.Fine` and the
   Navier-Stokes API into that target. Neither ETM module is in the 285-theorem gate.
9. Cosmetic: the two-sided gate is named `ProofPhase.ETM.Box.Gate` (declared inside the `Box` namespace).

## 4. Proposed ledger rows (not applied)

New IDs follow the last rows of each part on 2026-11-24 (I.11a, III.10b, VI.8, X.67).

*Applied by the coordinator on 2026-11-24 after an independent rebuild (75 declarations, standard axioms only), with Part I's
rows filed as I.8i to I.8k (under I.8, the existence linter) instead of I.12a to I.12c.*

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| I.12a | The one box: one command (the step at the one shared gate, the universal tick), the half-turn to read the other side, and a marker per step, inside or R136a1; the marker is correct when it agrees with the gate's own factor; DMP-complete means correct at every tick from the start | Lean (definitions) | `ProofPhase/ETM/Rotation.lean`, `Marker`, `Box`, `Box.gate`, `Box.Correct`, `Box.DMPComplete` | none |
| I.12b | No outside input: a verdict read after the half-turn is the verdict read from inside; in the plaquette layer the flux read from a box and from its complement agree | Lean | `ProofPhase/ETM/Rotation.lean`, `Box.Gate`, `Box.Gate.halfTurn`, `Box.complete_halfTurn`; `ProofPhase/ETM/RotationInstances.lean`, `crossoverGate`, `crossover_halfTurn` | none |
| I.12c | The test has content only when the marker is the system's own claim: a marker read off the gate afterwards always passes, and a box with a wrong marker exists | Lean | `ProofPhase/ETM/Rotation.lean`, `Box.selfMarked_complete`, `Box.exists_not_complete` | none |
| III.10c | O1 (chain form, `YMOneBox`) holds exactly when some margin makes every chain of outsides DMP-complete (gate factor min(1, e^{-F_e}), floor log mu, claim inside) | Lean | `ProofPhase/ETM/RotationInstances.lean`, `o1Box`, `o1_iff_complete` | none |
| III.10d | `FineOneBox` holds exactly when, for some valid box geometry fixed across levels and some margin below 1, the Yang-Mills box is DMP-complete from its start level; it then gives the one-box assembly; the converse needs the geometry fixed across levels | Lean | `ProofPhase/ETM/RotationInstances.lean`, `ymBox`, `fineOneBox_iff`, `ym_complete_iff`, `fineOneBox_iff_complete`, `fineOneBox_correct`, `ym_assembly_of_complete` | none |
| III.10e | The Yang-Mills box is DMP-complete (equivalently `FineOneBox`, i.e. O1) | open (conditional on X.64) | III.10d; III.5.6 | a proof of O1 |
| VI.7g | With the energy-only transfer bound against the viscous cost as gate factor and the claim "regular" at every dyadic scale, the gate reads R136a1 at some scale for every nu, K > 0 and every margin below 1: the Navier-Stokes box is not DMP-complete | Lean (model, as VI.3.4b) | `ProofPhase/ETM/RotationInstances.lean`, `nsBox`, `ns_gate_outside`, `ns_wrong_marker`, `ns_not_complete` | none |
| VI.7h | VI.7g covers the energy-only ledger only; an actual solution with a better transfer bound is not covered, so "not DMP-complete, hence blowup" stays the reading VI.7e | reading | `docs/unified/ROTATION-API.md` 3(5) | a proof of blowup or of regularity (VI.5.1) |
| X.68 | One-box certificate: correct at the start and one step at the shared gate keeps it correct, hence correct at every tick (exact along the run) | Lean | `ProofPhase/ETM/Rotation.lean`, `Box.onebox_certificate`, `Box.dmpComplete_iff_orbit` | none |
| X.68a | Scale certificate: if every scale's box is rebuilt from the one box through its gate (same margin, a morphism keeping step, factor and mass, start to start, carrying the marker), a box certified at one scale is correct at every scale; a scale with a wrong marker refutes the sharing | Lean (from the named hypothesis X.64) | `ProofPhase/ETM/Rotation.lean`, `Box.SharedGate`, `Box.scale_certificate`, `Box.onebox_everywhere`, `Box.not_shared_of_wrong`, `Box.sharedGate_self` | a proof of X.64 |
| X.68b | Sharing the gate alone is free (every system maps uniquely into the terminal object); the content of X.64 is that the marker travels with the gate | Lean (the free part); reading (the content of X.64) | `ProofPhase/ETM/Rotation.lean`, `Box.gate_through_trace` | none |
| X.68c | The universal machine is a box whose DMP-completeness from a description is exactly "the description runs forever", undecidable over descriptions (as is settling); on the contraction class the test settles from the explicit tick balanceBound, so DMP-completeness is a finite check | Lean | `ProofPhase/ETM/Rotation.lean`, `etmBox`, `etmBox_complete_iff`, `etmBox_complete_undecidable`, `etmBox_settles_undecidable`, `Box.settles_of_contracting`, `Box.complete_iff_bounded`, `rotation_edge` | none |
| X.68d | The owner's ground for X.64, "every tick can be reconstructed from any scale because of GRH": GRH supplies the sign, not the floor, so the shared-gate step is X.64 itself and every "certified on the box, hence everywhere" is conditional on it | conditional (on X.64) | `docs/unified/ROTATION-API.md` 3(2); GRH-to-O1 note | X.64 |

## 5. Rebuild

In the WSL distro `ym-replay` as `ym` (build folder `~/formal-rot`, seeded from a built `.lake`; deletable):

```bash
FORMAL_DST=~/formal-rot bash /mnt/c/claude/gravity-ym/docs/mass-gap/formal/sync-build.sh ProofPhase.ETM.ETM
cd /mnt/c/claude/gravity-ym && bash docs/unified/rotation-axioms.sh > docs/unified/rotation-axioms.log 2>&1
```
