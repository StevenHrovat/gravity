# W1: P4 as one named Lean hypothesis at M1's hand-over, and the exact chain to the assembly (c9a-crossover, round 2, 2026-11-23)

Lean: `formal/ProofPhase/Crossover/P4Chain.lean` (new; 23 theorems and 9 definitions). Built in `~/formal-p4` with
`build-p4.sh` ("Build completed successfully", no warnings in the new file); axioms with `axioms-p4.sh` -> `axioms-p4.log`
(every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`, no new axiom).

Claim marks as in `NOTE.md`: **Lean**, **paper**, **sketch**, **citation**, **numerical**, **open**.

---

## 0. Result in plain words

1. **P4 is now one named hypothesis on a class of laws, at the place where M1 ends** (Lean). `P4Star C λ` says: every law
   of the class `C` (laws of block states on the `L_*` tori, every volume) satisfies the one-box criterion with one set of
   constants. M1's hand-over is a second named hypothesis, `M1HandOver T B C`: from some level on, the `L_*` block laws of
   M1's randomized blocking lie in `C`. With these and the ultraviolet transfer, `yang_mills_assembly_p4Star` gives the
   v4 conclusions (torus decay, the gap in both orders of limits, reflection positivity, non-triviality).
2. **The gauge-restricted form now has a consumer** (Lean). `NOTE.md` stated `P4_*` with influences tested only on
   gauge-invariant functions (a weaker influence clause, plus covariance of the box specification; the natural form for a
   gauge theory), but the existing law route consumed only the unrestricted form. `P4StarInv` and `yang_mills_assembly_p4StarInv` close that: the one-box theorem with the real gauge action gives
   decay for a gauge-invariant second observable (`lawGapBddWInv_of_oneBoxLawInv`), and the v4 cut needs exactly that,
   provided the transfer's coarse approximant `g` is gauge invariant (`RandObsTransferPhysTWInv`, which implies the old
   transfer). The restricted route trades a weaker influence clause for covariance of the box specification and a stronger
   transfer. The test-class gain is real only for boxes with interior sites (a site all of whose incoming links lie in the
   box carries an admissible gauge rotation); for a one-site box the admissible group is essentially central and nothing is
   gained. P4's boxes have side `~ N_*`, so the gain applies there.
3. **The other split of P4 is now available over M1's hand-over** (Lean). Version 4's recursion lemma, restated for any
   family of `L_*` laws (`lawGapBddW_of_stageTwo`), gives `yang_mills_assembly_stageTwo`: **landing** (the `L₁` law gap,
   strong coupling) plus **stage two** (`V4.StageTwoW`) across the crossover. Reading (not a theorem): stage two is the Lean
   form of what the conditional mass (WL) must deliver (section 3).
4. **The net form makes the tail clause explicit** (Lean). `p4StarInv_of_net`: closeness to reference specifications gives
   the criterion on a shell of positions, but `IsNearSpec` costs `2δ` at every outside position, so the lemma cannot use
   closeness off the shell and takes a separate **tail clause** (influences off the shell bounded directly). The tail
   clause is the one-box influence bound of the actual law off the shell, i.e. half of P4 itself: the net form does not
   reduce P4, it moves its content into the tail, which is quasi-locality of the box laws in the boundary condition.

---

## 1. The chain

```
 P4Star C λ ─┐                              (unrestricted)
             ├─ oneBoxLaw_of_p4Star ─> OneBoxLaw (randBlockedLaw T B) λ
 M1HandOver ─┘        └─ lawGapBddW_of_oneBoxLaw ─> LawGapBddW ─ randBlockGapBddW_of_lawGapBddW ─> RandBlockGapBddW
                                                                    + RandObsTransferPhysTW ─> yang_mills_assembly_v4_bdd_rand

 P4StarInv C λ ─┐                           (gauge-restricted)
                ├─ oneBoxLawInv_of_p4StarInv ─> OneBoxLawInv ─ lawGapBddWInv_of_oneBoxLawInv ─> LawGapBddWInv
 M1HandOver ────┘     ─> RandBlockGapBddWInv + RandObsTransferPhysTWInv ─ randTorusDecayLoc_of_blockGapBddWInv ─> assembly

 LawGapBddW of (randBlockedLaw T B).map B₂   (landing at L₁)
 + StageTwoW (randBlockedLaw T B) B₂ s       (stage two, the crossover)
      ─ lawGapBddW_of_stageTwo ─> LawGapBddW of the L_* laws ─> RandBlockGapBddW ─> assembly
```

| theorem | statement | level |
|---|---|---|
| `oneBoxLaw_of_p4Star` | `P4Star C λ ∧ M1HandOver T B C ⇒ OneBoxLaw (randBlockedLaw T B) λ` | Lean |
| `randBlockGapBddW_of_lawGapBddW` | the law gap of the block laws is the block gap of the randomized blocking (pushforward) | Lean |
| `yang_mills_assembly_p4Star` | `OnLCP' ∧ NonTrivial ∧ P4Star ∧ M1HandOver ∧ RandObsTransferPhysTW ⇒` v4 conclusions | Lean |
| `lawGapBddWInv_of_oneBoxLawInv` | gauge-restricted one box `⇒` W₁ gap for gauge-invariant `g` | Lean |
| `randTorusDecayLoc_of_blockGapBddWInv` | the v4 cut with gauge-restricted gap and gauge-invariant approximants | Lean |
| `yang_mills_assembly_p4StarInv` | as above with `P4StarInv` and `RandObsTransferPhysTWInv` | Lean |
| `p4StarInv_of_net` | closeness to references on a shell + tail clause + margin `⇒ P4StarInv` | Lean |
| `lawGapBddW_of_stageTwo` | landing + stage two `⇒ LawGapBddW` of any family of `L_*` laws | Lean |
| `yang_mills_assembly_stageTwo` | landing + stage two over M1's hand-over `⇒` v4 conclusions | Lean |

Monotonicity (`p4Star_mono`, `m1HandOver_mono`): any class containing M1's will do. The class may be taken as large as is
convenient for a proof (for example, all laws of Balaban's form with constants in a compact range), at the price of a
stronger `P4Star`.

## 2. What each named input bundles

| input | contents | level |
|---|---|---|
| `M1HandOver T B C` | (i) M1's law form at the stopping scale (`m1_laws`, inductive form, `UV-TV.md` 37); (ii) the interface R11: an encoding of the block state `(V, τ)` as a coarse configuration, built into the randomized blocking `B` (the noise carries M1's independent Haar values on swallowed coarse bonds); (iii) the threshold `a ≤ a₀(γ)`, as the level `k₀` | M1 paper; R11 owed |
| `P4Star C λ`, `P4StarInv C λ` | the crossover | **open** |
| `RandObsTransferPhysTW T B` | M1's R10 plus Lemma UV-TV (OS-norm density of block observables) | M1 paper (citation-level readings, `UV-TV.md` 37) |
| `RandObsTransferPhysTWInv T B` | the same, with gauge-invariant coarse approximants of gauge-invariant fine observables | sketch: if the blocking is covariant in law under coarse gauge transformations, `E[G | block]` is coarse-gauge invariant, and averaging any approximant over coarse gauge transformations keeps `|g| ≤ 1` and the Lipschitz constant (`geodSU2` is bi-invariant) and does not increase the `L¹` error (Jensen). Not written out |
| `StageTwoW` | quasi-locality of `E[f | B₂]` and conditional decoupling across the crossover | **open**; the Lean target of (WL), section 3 |
| landing | `LawGapBddW` of the `L₁` laws | **open**; strong coupling (`FineOneBox`, the split `γ_Z + γ_A < 1`, certified windows c3c/c4d) |

**A tension to resolve in R11 (flag).** `P4StarInv` asks the box specifications to be covariant under the SU(2) gauge
action on the coarse configuration. That holds if the encoding of `(V, τ)` into a coarse SU(2) configuration is gauge
covariant. REVIEW-2 G5 (M1, round 25) found **no covariant SU(2) encoding** and recommended that the interface take
`(V, closed τ)` directly with gauge-invariant observables. Then the state space of the assembly is not
`GaugeConnection SU2 4 _` and every statement above has to be re-instantiated on the per-site space
`S = SO(3)^d × Z2^{d(d-1)/2} × N^d` (M1 round 41). The law layer here uses the SU(2) structure only through `gaugeAct` and
`linkDist` (the cut lemma also uses the torus symmetries `gaugeInvariant_tShift`, `measurePreserving_thetaConn`,
`mirrorLink`); the generic layer (`abs_cov_le_of_oneBox`, `Openness`) is already state-space generic. Until R11 is done:
with a non-covariant encoding use `P4Star` (unrestricted) and the old transfer; the restricted route needs covariance twice,
of the box specifications and of the blocking (for `RandObsTransferPhysTWInv`), so it waits for the `(V, τ)` interface. A
new state space also changes the class `C`; the mechanism of P4 (the crossover) is the same.

## 3. Stage two is what (WL) must deliver (paper sketch)

`StageTwoW ν B₂ s` (V4/Recursion.lean) asks, for `L_*` observables `f` (oscillations `vf` on `A`) and `g` (Lipschitz `Lg`) at
distance `R`, for `L₁` approximants `f₂, g₂` with

* (a), (b): `‖E_ν[f | B₂] − f₂ ∘ B₂‖₁`, `‖E_ν[g | B₂] − g₂ ∘ B₂‖₁ ≤ c (1 + Σvf)(1 + Lg) e^{−mR}`;
* (c): `|E_ν[fg] − E_ν[E[f|B₂] E[g|B₂]]| ≤ c (1 + Σvf)(1 + Lg) e^{−mR}`.

Write `B₂` as the composite of `N = log_L(L₁/L_*)` steps `X_{i+1} = R_i(X_i, ω_i)`, `i = 0, ..., N − 1`, and `K_i` for the
reverse kernels (law of `X_i` given `X_{i+1}`). Each step uses fresh independent noise and depends on the fine field only through `X_i`, so the scale
filtration is Markov and `E[f | X_{i+1}] = E[E[f | X_i] | X_{i+1}]` (tower property). By the law of total covariance along the scales (M1 used the same device,
`UV-TV.md` 38.1), (c) is the sum over `i` of `E[Cov_{K_i}(f_i, g_i)]` with `f_i := E[f | X_i]`, and (a), (b) say that the
projections `f_i` stay quasi-local step by step. Both follow if, at every crossover scale, the reverse kernel decorrelates
at the block scale with errors of Dobrushin shape `(1 + Σvf)(1 + Lg)` (Dobrushin-type conditional mixing gives exactly that
shape, `Recursion.lean` docstring). That per-scale statement is (WL); its precise forms are in `WL.md`.

Rate bookkeeping (sketch). If step `i` decorrelates at rate `m_*` per scale-`i` lattice unit, its term is
`≤ C e^{−m_* R/L^i}` at `L_*` distance `R`. The sum over `i < N` is dominated by the last step, so stage two holds at rate
`m ~ m_* L/s` in `L_*` units (`s = L₁/L_* = L^N`), i.e. one inverse `L₁` length, as it must be: the gap in `L_*` units is
`~ 1/s`. The prefactors grow by a factor `C_osc` per step (the oscillation sum of a projection is bounded by the summed
influences of the coarse variables), so `K ~ C_osc^N`: a constant, since `N` is fixed, but large. The support of the
approximants also grows, which is why `StageTwoW` allows the factor `(1 + R)⁴` in the oscillation sum; the recursion lemma
absorbs it by halving the rate (`poly_exp_le`). Stage two needs (WL) at
every scale with one rate in block units, and nothing at the `L₁` scale itself, which the landing covers.

## 4. The net form and the tail clause (Lean)

`p4StarInv_of_net` is the honest version of `NOTE.md` 2.4's "compactness reduction":

* hypotheses per volume: a box `Λ₀`, reference influences `κ̄` with the one-box sum at `γ`, a shell `sh` of weighted size
  `≤ S`, the margin `γ + 2δS/|Λ₀| ≤ γ₁ < 1`;
* per law of the class and per block `t`: a covariant specification `δ`-close (worst case, `IsNearSpec`) to a reference
  `q t`; the reference's influences `≤ κ̄` on the shell; **the law's own influences `≤ κ̄` off the shell**.

The lemma cannot do without the last clause: `isInfluenceBoundOn_of_near` adds `2δ` at **every** position, and the outside
of a box on a torus of side `M` has `~M⁴` positions, so closeness alone gives a one-box sum growing with the volume.
(Whether some other argument could avoid a tail bound is not addressed.) The tail clause is the actual law's own influence
bound off the shell, half of P4 itself; quasi-locality is exactly the input that `NOTE.md` 2.4 called "(ii) is the whole
problem". The Lean statement shows where it enters.

## 5. Not done in this round

* The R11 refactor (the assembly on the `(V, τ)` state space).
* A written-out proof of `RandObsTransferPhysTWInv` from M1's transfer (sketch in section 2).
* (WL) itself (`WL.md`).

## 6. Files

* `formal/ProofPhase/Crossover/P4Chain.lean` (new).
* `build-p4.sh`, `axioms-p4.sh`, `axioms-p4.log` (new; the build folder `~/formal-p4` is deleted at the end of the round).
