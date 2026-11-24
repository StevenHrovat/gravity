# Cycle 2, workstream C: `TorusDecay` through the blocked route, and the assembly kept current (2026-11-22)

Lean: `../../../formal/ProofPhase/Torus/Local.lean`, `../../../formal/ProofPhase/Torus/Top.lean` (new); edits to
`../../../formal/ProofPhase/Objects.lean`, `../../../formal/ProofPhase/Assembly.lean`, and one downstream fix in
`../../../formal/ProofPhase/Quantum/BlockedRoute.lean`. Built in `~/formal-c2c` (Lean 4.34.0, Mathlib v4.34.0); every `ProofPhase`
module builds except c2a's in-progress `Adjoint/CentreSplit.lean` (errors in its own generic centre-flip lemmas, lines 122 and 179,
unrelated to these edits). `axioms.sh`: 27 headline theorems, all `propext, Classical.choice, Quot.sound`; no `sorry`, no
`native_decide`, no new axioms.

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2c-torus/setup.sh
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2c-torus/build.sh ProofPhase.Torus.Top
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2c-torus/axioms.sh
```

Marks: **S** substantive, **D** definitional or elementary. "YM" = what is Yang–Mills-specific in the hypotheses.

## 0. Result in one paragraph

The blocked route at `L₁` now reaches the gap **in both orders of limits** for every observable of bounded physical extent, from
three open inputs: `H1Local`, `LimitDprime` and a new transfer hypothesis `ObsTransferPhys` (P5.2 with the approximant's size
measured in physical units, not in fine links). `ObsTransferPhys` is weaker than workstream 1's `ObsTransferU` (proved) and than the
literal "counted in `L₁` cells" form (proved). The assembly lists these inputs instead of `SlabDecay`; its conclusion is the gap for
bounded-extent observables (`MassGapLoc`), which is the form the Clay spectral gap needs. The flux energy in `OnLCP`/`ConjW` is now the
4D one (`fluxRate`), with no transfer operator; the pure-noise lemma still holds.

## 1. The transfer hypothesis in physical size (task 1)

**Why the old one stops at `SlabDecay`.** `ObsTransfer` bounds the coarse support of the block approximant by `K(|A₀|+1)(1+D/L₁)⁴`
with `|A₀|` the number of fine links. A fixed physical observable has about `(R/a_k)⁴` fine links, so the `SlabDecay` constant grows
with the level.

**`ObsTransferPhys T B`** (`Assembly.lean`, open). One rate `m > 0`; for every physical extent `R` there are `c`, `K`, `k₀` such that
for all levels `k ≥ k₀`, volumes `j`, fine observables `F`, `G` (measurable, gauge invariant, `|·| ≤ 1`) depending on link sets
`A₀`, `B₀` of physical extent `≤ R` (`PhysExtent`: `a_k · linkDist ≤ R` for any two links) at physical distance `≥ D`, there are
coarse observables `f`, `g` (`|·| ≤ 1`, supports `A'`, `B'` at physical distance `≥ D/2`) with
(i) a Dobrushin oscillation bound `v_f` of total `Σ_{A'} v_f ≤ 2K(1 + D/L₁)⁴` (level-uniform, independent of the fine-link count),
(ii) `‖E[F|Φ] − f∘Φ‖₁, ‖E[G|Φ] − g∘Φ‖₁ ≤ c e^{-mD}`, (iii) `|E[FG] − E[E[F|Φ]E[G|Φ]]| ≤ c e^{-mD}`.
YM: the Wilson measure `T.ym k j`, its blocked law through `B`, SU(2) coarse links.

**Comparison** (all Lean, **D** except the counting lemma, which is elementary combinatorics):

| statement | Lean |
|---|---|
| `ObsTransferU T B → ObsTransferPhys T B` | `obsTransferPhys_of_U` (via `card_le_of_siteDist`: `ℓ^∞` diameter `≤ r` ⇒ at most `4(2r+1)⁴` links; `card_le_of_physExtent`) |
| `ObsTransferCell T B → ObsTransferPhys T B` | `obsTransferPhys_of_cell` (`ObsTransferCell`: coarse support `≤ K(1+R/L₁)⁴(1+D/L₁)⁴`, one `K`) |
| `ObsTransfer` vs `ObsTransferPhys` | incomparable (the old one covers unbounded supports, the new one asks a level-uniform size) |

So `ObsTransferPhys` is the weaker sufficient hypothesis and the one put into `OpenPieces`. Physically it is the natural form of
H1-fine: the conditional expectation of an observable living in a region of size `R` is quasi-local in the `L₁` block variables near
that region, with a size that does not depend on how finely `F` resolves the region. Workstream 1's hard case for `ObsTransferU`
(observables spread over the torus with many coarse links of large oscillation) is outside its scope.

**The new targets** (`Torus/Local.lean`):
* `TorusDecayLoc V`: one rate `m > 0`; for every `s` and `R` one `k₀` and one `C ≥ 0` such that for every level `k ≥ k₀`, every
  fine-link bound `Vb`, every volume `j`, every `O : SlabObs V.T s Vb` with `O.Extent R`, and every `n` with
  `2n + 2⌈s/a_k⌉ + 2 ≤ side`: `|V.wcorr k j (O.F k j) n| ≤ C e^{-m n a_k}`. `TorusDecay V → TorusDecayLoc V`
  (`torusDecayLoc_of_torusDecay`, **D** + counting), so it is weaker than workstream 4's target.
* `MassGapLoc T` (`Objects.lean`) and `MassGapMFLoc V`: `MassGap`, `MassGapMF` restricted to `O.Extent R`, one rate for all `R`.
  `massGapLoc_of_massGap`, `massGapMFLoc_of_massGapMF` (**D**).

**Headline theorems.**

| Lean | exact statement | mark |
|---|---|---|
| `Torus.torusDecayLoc_of_blockedRoute` | `(B : BlockingFamily T) → 0 < λ → H1Local T B λ Vk Vinf → LimitDprime λ Vinf → ObsTransferPhys T B → TorusDecayLoc T.toV`, rate `min(λ/(4L₁), m)`, constant `(1−γ)⁻¹·4|K_{R+L₁}|·24(4/λ)⁴e^{λ/4} + 5c_{R+L₁}` | S (reduction; uses the law of total covariance `cov_transfer`, the slab separation `sep_shift_mirror`, and new: translations keep and reflections raise the link distance by at most one, `linkDist_shiftLink`, `linkDist_mirrorLink_le`) |
| `Torus.gapVF_of_family`, `Torus.gapMF_of_family` | one family with level-wise (resp. level-uniform) torus decay at rate `m ≥ 0` ⇒ every continuum limit point, volume first (resp. spacing first), is `≤ 2e^{-mτ}` | S (Theorem C on the torus, as in `latticeGap_of_slabDecay` and `massGapMF_of_torusDecay`, per family) |
| `Torus.bothOrdersLoc_of_torusDecayLoc` | `T.a → 0 → TorusDecayLoc T.toV → MassGapLoc T ∧ MassGapMFLoc T.toV` | D (from the two above) |
| `Torus.bothOrdersLoc_of_blockedRoute` | `T.a → 0 →` (blocked route with `ObsTransferPhys`) `→ TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV` | D (composition) |

**Which observables, and is that enough for Clay.** Covered: every measurable gauge-invariant slab observable `|F| ≤ 1` whose support
has physical extent `≤ R` at every level and volume, for any `R` and any number of fine links: Wilson loops and plaquette products of
physical size, smeared or averaged fields over a bounded region, and lattice-scale families (a single plaquette at every level has
extent `a_k → 0`). Missed: families of unbounded physical extent (volume averages over the whole torus, loops winding around it,
families whose support spreads as `k → ∞`). For the mass gap this does not matter: one rate `m` for all bounded-extent observables
gives, through `spectral_gap_of_decay` for each vector `(1−P_Ω)FΩ` and the density of bounded-extent local vectors in the OS Hilbert
space, the spectral gap `≥ m` of the reconstructed theory (paper step: the reconstruction P6.6 and the density are standard once the
limit is a state on the local algebra; not formalised). The unbounded-extent families are not local fields of the infinite-volume
continuum theory. Unchanged limits: bounded observables only (the bridge to unbounded local fields, P6.12, is open).

## 2. Assembly upkeep (task 2)

**The crossover now lists the sharpest open inputs.** `OpenPieces.crossover : BlockedTorusRoute T ∨ BlockedSlabRoute T ∨ (ConjW T ∧
SectorTransfer T)` with
* `BlockedTorusRoute T := ∃ B λ Vk Vinf, 0 < λ ∧ H1Local T B λ Vk Vinf ∧ LimitDprime λ Vinf ∧ ObsTransferPhys T B` (preferred),
* `BlockedSlabRoute T :=` the same with `ObsTransfer` (identical to `Quantum.BlockedRoute`).
`SlabDecay` is no longer a field (its other known sufficient condition, fine-level D′, is likely false); `assembly_routeA` still takes
it for any future proof.

**The top-level theorem moved** to `ProofPhase.Torus.Top` (full name unchanged, `ProofPhase.yang_mills_assembly`), because the blocked
route's last link is proved in modules that import `Assembly.lean`. Its conclusion is the common one of the three routes:

* `yang_mills_assembly : OpenPieces T → MassGapLoc T ∧ LimitRP T ∧ NonTrivial T` (was `MassGap T ∧ …` with crossover
  `SlabDecay T ∨ (ConjW T ∧ SectorTransfer T)`). Torus form via `Torus.bothOrdersLoc_of_blockedRoute`; slab form via
  **`RouteA.slabDecay_of_blockedRoute`** (workstream 1; `Quantum.slabDecay_of_blockedRoute`, workstream 3, is the independent
  duplicate and is not imported); route B via `assembly_routeB`.
* `yang_mills_assembly_torus : OnLCP T → NonTrivial T → BlockedTorusRoute T → OpenPieces T ∧ TorusDecayLoc T.toV ∧ MassGapLoc T ∧
  MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T` (**both orders of limits**).
* `yang_mills_assembly_slab : OnLCP T → NonTrivial T → BlockedSlabRoute T → OpenPieces T ∧ SlabDecay T ∧ MassGap T ∧ LatticeGap T ∧
  LimitRP T ∧ NonTrivial T`.
* `not_trivial` (unchanged statement and proof, `Assembly.lean`) and `not_trivial_top` (the same, re-checked in the top module):
  `∀ k, T.β k = 0 → ¬ OpenPieces T`. It uses only `OnLCP.running`, so no crossover option can bypass it.

**The flux energy is the 4D one** (`Objects.lean`, `Assembly.lean`; done, `not_trivial` unaffected):
* `IsFluxLimitSU2 β L h` := workstream 2's `RouteB.IsFluxLimit` for SU(2), periodic box, no twist; `exists_fluxLimitSU2`;
  `actRate L h := L · RouteB.fluxRate h`.
* `OnLCP.scheme : ∃ z⋆ > 0, ∀ hs, (∀ k, IsFluxLimitSU2 (β_k) (box k 0) (hs k)) → actRate (box k 0) (hs k) → z⋆` (was
  `actZ (β_k) (box k 0) → z⋆`).
* `ConjW T : ∃ δ > 0, ∀ k j h h', IsFluxLimitSU2 (β_k) (box k j) h → IsFluxLimitSU2 (β_k) (box k (j+1)) h' →
  (1+δ)² actRate (box k j) h ≤ actRate (box k (j+1)) h'`.
* `FluxGrowth T : ∃ δ > 0, ∃ z₀ > 0, ∃ k₀, ∀ k ≥ k₀, ∀ j h, IsFluxLimitSU2 (β_k) (box k j) h → z₀(1+δ)^{2j} ≤ actRate (box k j) h`.
* `OnLCP.eventually_actRate` (new, S small): from some level on every flux time limit of the unit box has act number `≥ z⋆/2` (by
  contradiction, choosing bad limits at infinitely many levels). `fluxGrowth_of_conjW` re-proved with it.
* Why "for every time limit": uniqueness of the `T → ∞` limit is not proved (Perron–Frobenius, standard). Stating the conditions for
  every limit makes them never weaker; when a limit vanishes from some time on, `fluxRate` is a junk value, which can only make the
  conditions harder. `fluxE`/`actZ`/`gaugeInvQ` stay in `Objects.lean`, unused by the assembly.

**`MassGapLoc`, `SlabObs.Extent`** are in `Objects.lean`; `PhysExtent`, `ObsTransferPhys`, `BlockedTorusRoute`, `BlockedSlabRoute`
in `Assembly.lean`; the stale "missing Lean link L1" remarks are removed from `Assembly.lean` and `ASSEMBLY.md`.

## 3. Duplicate cleanup (task 3)

Both `ProofPhase.RouteA.slabDecay_of_blockedRoute` and `ProofPhase.Quantum.slabDecay_of_blockedRoute` build unchanged. The assembly
uses the RouteA one (its module also provides `wcorr_le_blocked`, `slab_transfer_data`, `poly_exp_le`, reused by the torus form);
`Assembly.lean`, `Torus/Top.lean` and `ASSEMBLY.md` name the Quantum one as the independent proof. Downstream fix: in
`Quantum/BlockedRoute.lean`, `openPieces_of_blockedRoute` now builds the crossover as `Or.inr (Or.inl h)` (its `BlockedRoute` is the
second disjunct, definitionally); statement unchanged.

## 4. Unit tests

* **Photon (U(1), weak coupling).** All new hypotheses are stated for SU(2); the group-blind reduction would, for U(1), need
  `LimitDprime`, which fails for the massless photon (D′ at `L₁` implies a gap). `ObsTransferPhys` alone gives nothing. Pass.
* **Z₂ (gap, no confinement).** Conclusions are gap-type (`TorusDecayLoc`, `MassGapLoc`, `MassGapMFLoc`), true for weak-coupling Z₂;
  no area law is claimed. Pass.
* **Finite subgroups.** The reduction is group-blind (Dobrushin + conditional expectations); a finite subgroup with a gap would satisfy
  the conclusion as well, as it should for gap-type claims. No claim about which groups satisfy the hypotheses. Pass.
* **Deconfinement.** `TorusDecayLoc` asks decay only while `2n + 2⌈s/a⌉ + 2 ≤ side`; on tori of physical side below `1/T_c` this costs
  only a constant. `LimitDprime` at `L₁ < 1/T_c` is false, as the round-4 test demands. Pass.
* **Triviality / pure noise.** `not_trivial` holds after the edits (only `OnLCP.running` used). The φ⁴ test is not touched (no
  existence claim). Pass.
* **Banks–Zaks.** No matter fields; the conformal window would fail `LimitDprime` (no gap). Pass.

## 5. Blueprint changes (proposed; `PROOF-BLUEPRINT.md` not edited by this workstream)

* **P4.1′**: "`H1Local ∧ LimitDprime ∧ ObsTransfer ⇒ SlabDecay`; with `ObsTransferU` ⇒ `TorusDecay`" → add: "with `ObsTransferPhys`
  (P5.2 counted in physical size; weaker than `ObsTransferU`) ⇒ `TorusDecayLoc` (Lean, `Torus.torusDecayLoc_of_blockedRoute`), hence
  the gap for bounded-extent observables in both orders". Open inputs: `H1Local`, `LimitDprime` (adjoint half), `ObsTransferPhys`.
* **P5.2**: open; preferred form now `ObsTransferPhys` (Lean comparison: `obsTransferPhys_of_U`, `obsTransferPhys_of_cell`).
* **P6.11 (order of limits)**: add "`TorusDecayLoc ⇒ MassGapLoc ∧ MassGapMFLoc` (Lean); reached from the blocked route".
* **P7.1**: `yang_mills_assembly : OpenPieces T → MassGapLoc T ∧ LimitRP T ∧ NonTrivial T` in `ProofPhase.Torus.Top`; crossover =
  `BlockedTorusRoute ∨ BlockedSlabRoute ∨ (ConjW ∧ SectorTransfer)`; both orders: `yang_mills_assembly_torus`.
* **P7.4**: "reaches `SlabDecay`, not `TorusDecay`" → "reaches `TorusDecayLoc` (both orders) with `ObsTransferPhys`".
* **P7.5**: remove "the flux energy from the 4D measure (needs anisotropic tori)": the assembly now uses `fluxRate`.
* **P1.3′**: the identification with the Gauss-law transfer operator is no longer needed by the assembly.

## 6. For the parallel workstreams (names that changed)

* `ProofPhase.yang_mills_assembly` moved from `ProofPhase.Assembly` to `ProofPhase.Torus.Top`; conclusion `MassGapLoc` instead of
  `MassGap`.
* `OpenPieces.crossover` is a three-way disjunction (see §2); `Or.inl` now means the torus route.
* `OnLCP.scheme`, `ConjW`, `FluxGrowth` now use `IsFluxLimitSU2` and `actRate` (for every flux time limit); `actZ`, `fluxE` still exist.
* New in `Objects.lean`: `IsFluxLimitSU2`, `exists_fluxLimitSU2`, `actRate`, `SlabObs.Extent`, `MassGapLoc`, `massGapLoc_of_massGap`;
  `Objects.lean` now imports `ProofPhase.RouteB.FluxEnergy`.
* c2b's `SectorS/*.lean` build against the edited files. c2a's `Adjoint/CentreSplit.lean` did not build at the time of my check, with
  errors in its own generic lemmas (lines 122, 179); whether it also touches the changed names I could not see past those errors.
* The shared `../axioms-asm.sh` imports only `ProofPhase.Assembly`, so its `yang_mills_assembly` line no longer resolves; use
  `c2c-torus/axioms.sh` (not edited: outside this workstream's files).

## 7. Next step

The torus route has three open inputs. The most promising one to attack next is **`ObsTransferPhys`** for the concrete good blocking
(`RouteA.goodBlocking`): it is an ultraviolet statement (quasi-locality of `E[F|Φ]` and conditional decoupling at distance `D`),
plausibly provable at weak coupling from Lemma T (P3.2) plus a cluster expansion of the fine fields given the block
variables, with no confinement input; `LimitDprime`'s adjoint half (workstream 1) stays the real obstruction.
