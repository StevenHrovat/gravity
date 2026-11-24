# Phase 0 audit: where SU(2) and d = 4 sit in the Lean proof (2026-11-23)

Phase 0 of `GENERALISE-PLAN.md`, started on the owner's word ("Yes, start phase 0"). Read-only: nothing was edited or built. Done by a
Haiku subagent; the coordinator spot-checked the key claims against the files (file count 119; `abbrev SU2` at
`AreaLaw/Concrete.lean:293`; `card_boxBlock` with `Fin 4` at `OneBox/Torus.lean:101-103`; `3^4 = 81` at `OneBox2/Anchor.lean:268-271`;
`projSU2` at `RouteA/Blocking.lean:272`; `SU2 3` at `Objects.lean:430`; `(1+R)^4` and `24/r^4` in `V4/Recursion.lean`; the stale
reference at `RouteB/Chain.lean:23`). The rest rests on the subagent's reading.

## What it means for the plan

1. **In Lean, d = 4 is only lattice counting.** Every `needs4` place is a volume factor: 4 link directions per site (`card_boxBlock`),
   `3^4` neighbours, `(2r+1)^4` boxes, `(1+R)^4` growth, `24/a^4 = 3!/a^4` (a tail sum of `x^3 e^{-ax}`). Each has an obvious
   d-version (`d`, `3^d`, `(2r+1)^d`, `(1+R)^d`, `(d-1)!/a^d`). The physical uses of d = 4 (Balaban's marginal scaling, the
   vortex-sheet capacity) are not in Lean at all; they sit in the paper parts and enter Lean as named hypotheses. So making d explicit
   in Lean is mechanical, and the `hd : d = 4` hypotheses the plan foresaw belong to the paper-level inputs, not to these modules.
2. **The gauge group splits cleanly.** 54 files (14,000 lines) are already generic or group-free; 45 files (12,500 lines) use SU(2) only
   in how statements are written (`inst`); 20 files (6,800 lines) use SU(2)-specific facts (`subst`).
3. **The `subst` work falls into five group facts**, which is the content of the planned gauge-group package:
   - explicit 2x2 matrices, adjugate and Mandelstam identities (`Flip/Strict`, `FluxVac/Branches`, `SectorS/Loops`, `RouteA/Blocking`,
     `Saturation/Tests`, `Flip/Bound`, `M1/Vortex`, `Certified/AdjointW`);
   - the centre {+1, -1} and the Z2 layer (`Adjoint/CentreSplit`, `DMP/VacuumAct`, `Flip/Bound`, `RouteB/FluxEnergy`,
     `RouteA/CentreBlind`, `Repair/WeightedW`, `Objects`); in `CentreSplit` and `VacuumAct` it is in the statements, not only proofs;
   - trace bounds and characters (`Book/KernelDensity`, `Certified/AdjointW`, `Certified/Measured`, `RouteA/CentreBlind`, `Flip/Strict`);
   - the projection onto SU(2) and the SU(2) geodesic metric `geodSU2` (`RouteA/Blocking`; `geodSU2` is used in statements of the
     Interface and OneBox modules and, through `exists_geodSU2_pos`, by `Repair/GeneralSupport`, `V4Bridge`, `WeightedW`);
   - the fundamental representation of dimension 2 (`OneBox2/Wilson`, used by all of OneBox2).
4. **A third axis: spatial dimension 3** is written explicitly in five files (`Objects`, `DMP/VacuumAct`, `Flip/Bound`,
   `FluxVac/Branches`, `RouteB/FluxEnergy`), the time-slice (transfer-matrix) objects. With d explicit these become `d - 1`.
5. **The cheapest first step** is the shared counting lemma `card_boxBlock` (`OneBox/Torus.lean:101`): in d it clears most of the
   `needs4` chain (Fine, Cube, Torus/Local, CondMass).

## Revised phase 1 scope (concept)

- A small `Counting` layer in d: link directions, neighbour and box counts, `(1+R)^d` growth, the tail sum `(d-1)!/a^d`.
- The gauge-group package with the five facts above as fields: a metric with positivity (replacing `geodSU2`), a projection onto G,
  a central element set with the twist, trace and character bounds, the dimension of the fundamental representation.
- New generic versions of the 45 `inst` files beside the old ones; the old SU(2), d = 4 statements re-derived as one instance.
- The 20 `subst` files wait for phase 3, except where a fact is a one-line package field.

## Totals

| G axis | files | lines | | d axis | files | lines |
|---|---|---|---|---|---|---|
| generic | 28 | 8,206 | | generic | 17 | 4,624 |
| inst | 45 | 12,477 | | fixed4 (written, not needed) | 29 | 7,254 |
| subst (incl. 4 uncertain) | 20 | 6,779 | | fixed3 (spatial 3) | 4 | 1,535 |
| none | 26 | 5,696 | | needs4 (counting; 6 not traced) | 21 | 6,889 |
| | | | | none | 48 | 12,856 |

119 files, 33,158 lines. Uncertain `subst?`: `Adjoint/CentreSplit`, `OneBox2/Wilson`, `Repair/GeneralSupport`, `Repair/V4Bridge`.
Not traced line by line (`needs4?`): `Certified/AdjointW`, `Certified/Measured`, `V3/TimeSep`, `V3/W1Route`, `V4/Gap`, `V4/Recursion`.

## Small finding

`RouteB/Chain.lean:23` cites `RouteB.FluxEnergy.su2Weight` in a doc comment; no such declaration exists in `FluxEnergy.lean`. A stale
comment only; to fix when the file is next touched.

## Per-file table (paths relative to `formal/ProofPhase`)

| path | G | d | lines | key evidence |
|---|---|---|---|---|
| Assembly.lean | inst | needs4 | 522 | `^4` in ObsTransfer defs 417-418, 453; `(d := 4)` 178, 207, 249 |
| Objects.lean | subst | fixed4 | 488 | su2Centre and R4 flux layer 438, 444; `SU2 3` at 430 |
| Adjoint/CentreSplit.lean | subst? | none | 283 | negOneSU2 in defs/statements 231-238; proof generic |
| Adjoint/TwoType.lean | generic | none | 509 | SO(3) only in header comment |
| Adjoint2/CostCoupling.lean | generic | none | 617 | "4" only in a comment heading |
| Adjoint2/PatternAssembly.lean | inst | fixed4 | 290 | `GaugeConnection SU2 4` in statements 249-253 |
| Adjoint2/Transfer.lean | generic | none | 456 | "Z2" hits are hypothesis names |
| Book/Cells.lean | generic | generic | 301 | no SU2; `variable {d}` |
| Book/KernelDensity.lean | subst | fixed4 | 206 | trace bound 127-129; vMF density 133-201 |
| Book/NoiseLaw.lean | generic | generic | 332 | no SU2 |
| Book/SU2Inst.lean | inst | none | 28 | SU2 instances only |
| Book/TwoSize.lean | inst | fixed4 | 174 | `GaugeConnection SU2 4` 62, 72 |
| Centre/Combined.lean | inst | generic | 177 | `productHaar SU2` 84-103; generic proof |
| Centre/Comparison.lean | generic | none | 176 | SO(3) only in comments |
| Centre/Ginibre.lean | none | none | 312 | Ising spins |
| Centre/Z2Wilson.lean | subst | generic | 260 | Z2 itself as the gauge group |
| Certified/AdjointW.lean | subst | needs4? | 278 | adjoint character 142-166; geodSU2 177; `(d := 4)` 219 |
| Certified/Measured.lean | subst | needs4? | 201 | characters 50-74; `(d := 4)` 154 |
| Crossover/Openness.lean | generic | generic | 141 | no SU2 |
| Crossover/P4Chain.lean | inst | needs4 | 635 | `GaugeConnection SU2 4`; `^4` 380-406 |
| DMP/Doubling.lean | none | none | 281 | no hits |
| DMP/VacuumAct.lean | subst | fixed3 | 351 | negOneSU2 254; Wilson chain on `LatticePlaquette 3` 235-237 |
| Defects/Annealed.lean | generic | none | 192 | G is a graph |
| Defects/EffDist.lean | generic | none | 318 | no hits |
| Defects/Quenched.lean | generic | none | 144 | G is a graph |
| Defects/Supplier.lean | inst | fixed4 | 255 | `GaugeConnection SU2 4` 206-212 |
| Existence/Bridge.lean | inst | fixed4 | 312 | `wilsonMeasure SU2 2 β 4 N`; `(d := 4)` |
| Flip/Bound.lean | subst | fixed3 | 450 | 2x2 centre proofs 408-412; `LatticePlaquette 3` |
| Flip/Floor.lean | inst | none | 399 | su2_gap statements 312-344 |
| Flip/Strict.lean | subst | none | 1217 | 2x2 matrices 777-802; adjugate/trace 823-837; centre 874-877 |
| FluxVac/Branches.lean | subst | fixed3 | 308 | 2x2 `su2_hz`, negOneSU2 flip 158-190 |
| H1/Level.lean | inst | needs4 | 200 | `(1+D/L)^4` 142; `24/a^4` 163 |
| H1/Split.lean | inst | fixed4 | 407 | `LatticeLink 4` 323-350 |
| Interface/DenseTransfer.lean | inst | needs4 | 108 | geodSU2 55; `(1+D/L)^4` 54, 86 |
| Interface/MeasBlocking.lean | inst | needs4 | 262 | geodSU2 58-85; `^4` 85, 182, 208 |
| Interface/RandBlocking.lean | inst | needs4 | 348 | `(G := SU2) (d := 4)` 248-249; `^4` 174, 271 |
| Interface/SpectralUpgrade.lean | none | none | 295 | no hits |
| M1/Assembly.lean | generic | none | 304 | abstract X, Y |
| M1/CutAvoid.lean | none | none | 118 | inner-product space |
| M1/Dilution.lean | none | generic | 231 | d a parameter (206) |
| M1/Exact.lean | none | none | 153 | measure resampling |
| M1/FibreMass.lean | none | none | 74 | measure lemmas |
| M1/FluxTube.lean | none | generic | 64 | over `Fin n` |
| M1/Footprint.lean | none | none | 45 | real lemma |
| M1/LocalMod.lean | none | none | 104 | ring lemmas |
| M1/OffCentre.lean | none | none | 55 | weighted averages |
| M1/Routine.lean | generic | none | 75 | `{G} [Group G]` |
| M1/Twist.lean | generic | none | 144 | `{G} [Group G]` |
| M1/UVTVCov.lean | none | none | 313 | probability space |
| M1/UVTVFront.lean | none | none | 172 | real analysis |
| M1/UVTVInfluence.lean | generic | none | 88 | ScaleHyp over abstract sites |
| M1/UVTVInterface.lean | none | none | 220 | abstract; `C := 4` a constant |
| M1/UVTVOS.lean | none | none | 312 | RPData |
| M1/UVTVReflect.lean | none | none | 274 | measure space |
| M1/UVTVScale.lean | generic | none | 378 | abstract sites |
| M1/Vortex.lean | subst (mixed) | none | 151 | generic core 44-120; central -1 at 129-146 |
| OS/GapLoc.lean | inst | fixed4 | 223 | `GaugeConnection SU2 4` 52, 155, 163 |
| OS/Torus.lean | generic | generic | 404 | `{d N}`, `{G} [Group G]` |
| OS/Window.lean | none | none | 235 | WinRP |
| OneBox/CouplingDS.lean | generic | none | 721 | abstract |
| OneBox/Criterion.lean | generic | none | 196 | abstract |
| OneBox/Fine.lean | inst | needs4 | 233 | `K := 4(2r+1)^4` 130 |
| OneBox/Restricted.lean | generic | none | 276 | abstract |
| OneBox/Tests.lean | inst | fixed4 | 134 | geodSU2 92 |
| OneBox/Torus.lean | inst | needs4 | 206 | `card_boxBlock` with `Fin 4` 101-103 |
| OneBox2/Anchor.lean | inst | needs4 | 451 | `3^4 = 81` 268-271 |
| OneBox2/Concrete.lean | inst | fixed4 | 117 | `gaugeSpec (G := SU2) (d := 4)` 53 |
| OneBox2/Cube.lean | inst | needs4 | 454 | `K := 4(2r+1)^4` 364 |
| OneBox2/CubeAnchor.lean | inst | fixed4 | 167 | `SU2 4 N` |
| OneBox2/Lift.lean | generic | none | 202 | abstract |
| OneBox2/Wilson.lean | subst? | fixed4 | 190 | `unitaryGroup (Fin 2)` 65; `gaugeTrace SU2 2` 87 |
| Quantum/BlockedRoute.lean | inst | needs4 | 438 | `(1+x)^4` box count 313-319 |
| Quantum/LemmaT.lean | inst | fixed4 | 440 | 4s are type arguments |
| Quantum/LimitStates.lean | inst | fixed4 | 137 | `InfLink → SU2` |
| Quantum/PerVolume.lean | inst | fixed4 | 388 | generic core 1-183 |
| Repair/GeneralSupport.lean | subst? | fixed4 | 257 | `exists_geodSU2_pos` 187-224 |
| Repair/MulNoise.lean | inst | fixed4 | 185 | generic 49-160 |
| Repair/Noisy.lean | inst | fixed4 | 370 | generic core 1-275 |
| Repair/V4Bridge.lean | subst? | fixed4 | 171 | `exists_geodSU2_pos` 82 |
| Repair/WeightedW.lean | subst | fixed4 | 403 | `exists_geodSU2_pos` 338-342 |
| RouteA/BlockedSlab.lean | inst | needs4 | 497 | `(1+x)^4`, 4! 204-216 |
| RouteA/Blocking.lean | subst | generic | 642 | `Matrix (Fin 2)` 259-323; projSU2 272 |
| RouteA/CentreBlind.lean | subst | generic | 84 | negOneSU2 60; trace -2 70 |
| RouteB/Chain.lean | generic | none | 623 | generic G with Haar |
| RouteB/Duality.lean | generic | needs4 | 208 | `Fin 4` rotation 160-168; 4D plane pairing 194-205 |
| RouteB/FluxEnergy.lean | subst (mixed) | fixed3 | 426 | generic core 61-300; 2x2 lemmas 407-424 |
| RouteB/HankelRate.lean | none | none | 251 | sequences |
| RouteB/Sector.lean | none | none | 49 | abstract |
| Saturation/EnergyEntropy.lean | none | generic | 167 | `2 ≤ d` 117 |
| Saturation/Reduction.lean | inst | fixed4 | 169 | `(1 : SU2)`, `LatticeLink 4` |
| Saturation/Sheet.lean | none | generic | 477 | sheet combinatorics |
| Saturation/Tests.lean | subst | generic | 184 | centre -1 on 2x2 99-110 |
| Saturation/Vortex.lean | generic | generic | 355 | generic G with Haar |
| ScaleHyp/ScaleInst.lean | generic | generic | 347 | abstract; `scaleHyp_torus {d N}` |
| ScaleHyp/Counting.lean | none | generic | 229 | `(2R+1)^d` |
| ScaleHyp/BoxLaw.lean | generic | none | 249 | abstract |
| ScaleHyp/KernelCoupling.lean | generic | none | 136 | abstract |
| ScaleHyp/MaxCoupling.lean | generic | none | 187 | abstract |
| SectorS/ConjS.lean | inst | fixed4 | 103 | `(d := 4) (G := SU2)` 60-61 |
| SectorS/GeneratorRate.lean | none | none | 190 | inner-product space |
| SectorS/Loops.lean | subst | generic | 229 | 2x2 Mandelstam 44-90 |
| SectorS/Mixture.lean | generic | none | 127 | abstract |
| Seg1/Envelope.lean | inst | fixed4 | 305 | `GaugeConnection SU2 4` 204-298 |
| Seg1/KP.lean | none | none | 541 | polymer gas |
| Seg1/Mobius.lean | none | none | 463 | subset-lattice calculus |
| Seg2/Filter.lean | inst | fixed4 | 400 | generic core 71-282 |
| Torus/Local.lean | inst | needs4 | 450 | `4*(2r+1)^4` 118-159 |
| Torus/Top.lean | none | none | 71 | assembly statements |
| UV/Split.lean | inst | fixed4 | 470 | `RPBlocking SU2 4` 419-421 |
| V3/CondInputs.lean | inst | fixed4 | 166 | `GaugeConnection SU2 4` 56 |
| V3/CondMass.lean | inst | needs4 | 347 | `K := 4(2r+1)^4` 221 |
| V3/TimeSep.lean | inst | needs4? | 228 | `24/a^4`, `(1+D/L)^4` 180-208 |
| V3/Top.lean | inst | fixed4 | 152 | binders 84-115 |
| V3/W1Route.lean | inst | needs4? | 361 | `(1+D/L)^4` 323; `24/a^4` 340 |
| V4/Gap.lean | inst | needs4? | 259 | `(1+D/L)^4` 226-227; `24/a^4` 256-257 |
| V4/LCP.lean | inst | none | 132 | `IsFluxLimitSU2` (Objects:456) |
| V4/Recursion.lean | inst | needs4? | 203 | `(1+R)^4` 83-190; `24/r^4` 186 |
| V4/Top.lean | inst | fixed4 | 117 | binder 104 |
| V4/UV.lean | inst | fixed4 | 58 | binders 50-54 |
