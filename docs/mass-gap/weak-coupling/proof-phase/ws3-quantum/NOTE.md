# Proof phase, workstream 3: the quantum half into Lean, and the blocked route's last link (2026-11-22)

Brief: blueprint P3.2 (Lemma T), P3.3 (per-volume gap theorem), limit states (PROOF-NOTE Lemma 6.3), P7.4
(`H1Local ∧ LimitDprime ∧ ObsTransfer ⇒ SlabDecay`), review finding 5 (`dist` a metric). Rules: `../../attempts/RULES.md`
(proof-phase section, claim discipline).

Lean: four new files under `../../../formal/ProofPhase/Quantum/`, built in `~/formal-ws3` (Lean 4.34.0, Mathlib v4.34.0),
against the current `Assembly.lean` (with workstream 4's `oneLoopSlope = 11/(6π²)`) and `Existence/Bridge.lean`.
All four modules build; `axioms.sh` prints `propext, Classical.choice, Quot.sound` for all 29 headline theorems; no
`sorry`, no `native_decide`, no new axioms. Nothing outside `ProofPhase/Quantum/` and this folder was edited.

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws3-quantum/setup.sh
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws3-quantum/build.sh ProofPhase.Quantum.BlockedRoute
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws3-quantum/build.sh ProofPhase.Quantum.PerVolume
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws3-quantum/build.sh ProofPhase.Quantum.LimitStates
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws3-quantum/axioms.sh
```

Marks: **S** = substantive (real mathematical content), **D** = definitional or elementary (true by construction or
for any model). "YM" names what is Yang–Mills-specific in the hypotheses.

## 0. Result in one paragraph

All four tasks close in Lean. **P7.4 is proved**: `H1Local ∧ LimitDprime ∧ ObsTransfer ⇒ SlabDecay` (for `λ > 0`), so the
blocked route is a machine-checked sufficient condition for route A's field and feeds `yang_mills_assembly`
(`openPieces_of_blockedRoute`). **Lemma T** is in Lean for measures, maps and Markov kernels, with the conditional-law
part for block specifications at every boundary, and instantiated on the SU(2) Wilson measures. **The per-volume gap
theorem** is one Lean theorem on the real SU(2) Wilson family: one noisy blocking step + D′ for every mesh limit point
at L₁ ⇒ every mesh limit point of the L₁ block covariances decays with a volume-independent constant (order mesh →
volume → observable); review finding 2's "three islands" are joined for this route. **Limit states** exist at fixed
spacing (Prokhorov + Tychonoff on SU(2)^{links of ℤ⁴}), and the "every limit point" quantifiers of `MassGap` are
never vacuous. What does not follow: the per-volume theorem does not give `SlabDecay` (its `k₀` depends on the volume),
and P7.4 reaches `SlabDecay` but not workstream 4's `TorusDecay` (§4.3).

## 1. Lemma T (P3.2) — `Quantum/LemmaT.lean`

`RelClose ε μ μ' := μ' ≤ e^ε • μ ∧ μ ≤ e^ε • μ'` (measures; for finite measures, `dμ'/dμ ∈ [e^{-ε}, e^ε]`).
Abstract (any measurable spaces, no Gibbs or gauge structure; abstract-system theorems, instantiated below):

| Lean | exact statement | mark |
|---|---|---|
| `RelClose.map` | `RelClose ε μ μ' → Measurable f → RelClose ε (μ.map f) (μ'.map f)` (T(a), deterministic blocking) | D |
| `RelClose.bind` | `RelClose ε μ μ' → ∀ κ : Kernel α β, RelClose ε (μ.bind κ) (μ'.bind κ)` (T(a), noisy blocking) | D |
| `RelClose.map_comp` | two blocking steps; by induction any number | D |
| `relClose_withDensity_log` | `ρ, ρ' > 0`, `∀x, |log ρ x − log ρ' x| ≤ ε` ⇒ `RelClose ε (ν.withDensity ofReal∘ρ) (ν.withDensity ofReal∘ρ')` | D |
| `relClose_normalize` | `w, w' > 0` integrable, `∫w > 0`, `w' ≤ e^ε w`, `w ≤ e^ε w'` ⇒ `RelClose (2ε) (normalize q w) (normalize q w')` (T(b) core: the reweighting formula `q' = h q / ∫h dq`) | S (elementary) |
| `relClose_locSpec` | `LocalWeight W, W'`, `W' ≤ e^ε W`, `W ≤ e^ε W'` ⇒ `∀ B σ, RelClose (2ε) (locSpec ν B W σ) (locSpec ν B W' σ)`: **every block, every boundary condition** | S |
| `abs_integral_sub_le_of_relClose` | finite `μ`, `RelClose ε μ μ'`, `F` measurable `|F| ≤ M` ⇒ `|∫F dμ' − ∫F dμ| ≤ (e^ε − 1) ∫|F| dμ` | S (elementary) |
| `abs_integral_sub_le_osc` | probability measures, total oscillation `C` ⇒ `≤ (e^ε − 1) C` | S (elementary) |
| `tvClose_locSpec` | `Effective.TVClose B (locSpec ν B W') (locSpec ν B W) (e^{2ε} − 1)` (into `SpecDist` via `specDist_of_tv`) | D (from the above) |

Instantiated on `ProofPhase.Objects` (YM: SU(2), the 4D torus, the Wilson weight; per volume):

| Lean | exact statement | mark |
|---|---|---|
| `relClose_wilsonMeasure` | `RelClose (2·(2|β − β'|·#plaquettes)) (wilsonMeasure SU2 2 β 4 N) (wilsonMeasure SU2 2 β' 4 N)` | S (small) |
| `relClose_wilson_blocked` | the same for the images under any measurable blocking `Φ` (every `RPBlocking`) | D |
| `relClose_wilson_gaugeSpec` | `∀ B U, RelClose (2·(2|β − β'|·#touching B)) (gaugeSpec … β B U) (gaugeSpec … β' B U)`: local, every boundary | S (small) |

**Paper only:** T(b) for the conditional laws of *image* variables, which have no explicit densities: one needs a
version of `dμ'/dμ` clamped to `[e^{-ε}, e^ε]` (Radon–Nikodym, `rnDeriv ≤ e^ε` a.e. from `μ' ≤ e^ε μ`) and then
`relClose_locSpec`. Not formalised, because the per-volume chain below does not need it (it uses T(a) and the
expectation bound only). It is about 40 lines of Mathlib measure theory if wanted.

## 2. The per-volume gap theorem (P3.3) — `Quantum/PerVolume.lean`

**Objects.** `NoisyBlocking V X Y` for a `VTuning V` (workstream 4: bare coupling `β_{k,j}` may depend on the volume;
`Tuning.toV` embeds ours): per volume `j` a compact metric space `X j` with a reference probability measure, a compact
metric prediction space `Y j`, a continuous noise kernel `K_j ≥ m_j > 0` with `∫ K_j(x, y) d ref(x) = 1`, measurable
prediction maps `pred k j` of the fine SU(2) field, and a measurable blocking `Ψ_j : X j → GaugeConnection SU2 4
(coarseSide j)`. `noisyLaw ref K ν = (∫K(·, y)dν(y))·ref` (a probability measure, `isProbabilityMeasure_noisyLaw`, by
Fubini); `predLaw k j = (V.ym k j).map (pred k j)`; `l1Law k j = (noisyLaw (predLaw k j)).map Ψ_j`. YM: the fine
measures are the SU(2) Wilson measures, the L₁ variables are SU(2) links with product Haar reference and `linkDist`.

**Hypothesis H2-all (`LimitDprimeAll lam γ`, open, the crossover in per-volume form):** for every `j` and every weak
limit point `ν` of `k ↦ predLaw k j` (`IsMeshLimit`), `l1LawOf j ν = gibbsMeasure (haarG SU2) Vinf` for a potential
`Vinf` with pair oscillations `Sb` satisfying `FlatCriterionW linkDist lam Sb γ` (same `γ`, `λ` for all `j`, all `ν`).

| Lean | exact statement | mark |
|---|---|---|
| `tendsto_integral_blocked` | uniform convergence of `log ∫K(x, ·)dν_n` ⇒ `∫F d(Ψ_* noisyLaw ν_n) → ∫F d(Ψ_* noisyLaw ν_∞)` for every bounded measurable `F` and measurable `Ψ` (noise lemma output + Lemma T(a) + expectation bound) | S |
| **`NoisyBlocking.perVolumeGap`** | `0 ≤ λ`, `0 ≤ γ < 1`, H2-all ⇒ `∀ j f g A S_g v_f L_g R`, `BM f, BM g, DepOn f A, DepOn g S_g, OscBound f v_f, 0 ≤ L_g, OscBound g L_g, (∀ x∈A, y∈S_g, R ≤ linkDist x y)`, `IsLimitPoint (k ↦ cov (l1Law k j) f g) h` ⇒ `|h| ≤ (1 − γ)⁻¹ (∑_{a∈A} v_f a) L_g e^{-λR}` | **S** |
| `perVolumeGap_eventually` | same hypotheses, `ε > 0` ⇒ `∀ᶠ k, |cov (l1Law k j) f g| ≤ (1 − γ)⁻¹ (∑ v_f) L_g e^{-λR} + ε` | S |
| `exists_blockLimit` | **no open hypothesis**: `∃ φ` strictly monotone, `∃ ν_∞ : ∀ j, P(Y j)`, `∀ j`, `predLaw (φ n) j → ν_∞ j` weakly and `∫F d l1Law (φ n) j → ∫F d l1LawOf j (ν_∞ j)` for every bounded measurable `F` | S |
| `blockLimit_gap` | H2-all ⇒ along that `φ`, in every volume, block covariances converge and the limit's obey the D′ bound with one constant | S |

Proof of `perVolumeGap` (this is review finding 2's glue, now in one Lean theorem): a mesh limit point is the limit
along `φ`; Prokhorov (`ProbabilityMeasure (Y j)` compact metrizable) gives `ψ` with `predLaw (φ∘ψ n) j → ν_∞`; the
noise lemma `Attempts.R3.Wp.noise_uniform` gives uniform convergence of the log-densities; `relClose_withDensity_log` +
`RelClose.map` + `abs_integral_sub_le_of_relClose` make every bounded measurable expectation converge (the noise is
what makes this total-variation convergence, not only weak); so `h = cov(l1LawOf j ν_∞)`; H2-all at `ν_∞` (a mesh limit
point via `φ∘ψ`) identifies it as a D′ Gibbs measure; `Attempts.R3.decay_of_flatW` bounds it. Order: mesh (k → ∞ at
fixed j), then the volume (constant independent of j), then the observable — the order the reviewer checked.
`exists_blockLimit` does the "subsequence across volumes" with one subsequence for all volumes (Tychonoff on
`∏_j P(Y_j)`, first countable), so no diagonal argument is needed.

**What it is and is not (claim discipline).** Weaker than the mass gap in two ways: the observables are noisy L₁ block
observables, and `k₀` depends on the volume, so it does **not** give `SlabDecay`/`LatticeGap` (those need `k₀`
independent of the volume). Its hypothesis H2-all is at least as strong as a gap of the L₁ block theory (worst-case
D′, false below `1/T_c`; review finding 3). Unit tests: photon — H2-all fails (gapless limit), nothing proved;
Z₂/finite groups — the file is SU(2)-typed, the abstract part would apply verbatim and gives only decay (true for
weak-coupling Z₂, no area law); triviality — `exists_blockLimit` is an existence statement at the block level and says
nothing about non-triviality; pure noise (`β = 0`) satisfies everything and has a gap, so identification is not here
(it is in `OnLCP`, `NonTrivial`).

## 3. Limit states (Lemma 6.3) — `Quantum/LimitStates.lean`

| Lean | exact statement | mark |
|---|---|---|
| `exists_limitPoint_of_bdd` | `(∀ n, |u n| ≤ B) → ∃ h, IsLimitPoint u h` | D |
| `exists_infVol_limitPoint` | `∀ V k F n`, `F j` measurable, `|F j| ≤ 1` ⇒ `∃ h, IsLimitPoint (j ↦ V.wcorr k j (F j) n) h` (volume-dependent `β` allowed) | D |
| `massGap_nonvacuous` | `∀ T O τ, ∃ h g, (∀ k, IsLimitPoint (j ↦ T.wcorr k j (O.F k j) (T.steps k τ)) (h k)) ∧ IsLimitPoint h g` | D |
| **`exists_limitState`** | `∀ V k (j_n)`, `∃ φ` strictly monotone, `∃ μ : ProbabilityMeasure (InfLink → SU2)`, `wilsonState V k (j_{φ n}) → μ` weakly; `InfLink = (Fin 4 → ℤ) × Fin 4`, `wilsonState` = SU(2) Wilson measure pushed by the periodic extension `periodize` | S (Prokhorov + Tychonoff; YM: SU(2) compact, the Wilson measures) |
| `tendsto_integral_limitState` | along it, `∫ F ∘ periodize d(V.ym k j_n) → ∫ F dμ` for every continuous `F` on `SU(2)^{links of ℤ⁴}` | D |

`massGap_nonvacuous` is what the "every limit point" quantifiers of `MassGap` need: a statement universally quantified
over limit points could otherwise be vacuously true. **Paper only:** Lemma 6.3's convergence for bounded *measurable*
local `F` (needs the marginal density bound of PROOF-NOTE Lemma 2.1 and an L¹ approximation by continuous functions)
and translation/Θ-invariance of `μ_∞`; and the identification of the real limit points of `wcorr` with limit-state
correlations, which needs "the same continuous observable in every volume" (`SlabObs` allows any measurable family per
volume) — the same missing object (P6.7 fields) that blocks uniqueness of the limit.

## 4. P7.4, the blocked route's last link — `Quantum/BlockedRoute.lean`

### 4.1 The theorem (proved)

**`slabDecay_of_blockedRoute`** (S; YM: everything in `H1Local`, `LimitDprime`, `ObsTransfer`, `SlabDecay` is about the
SU(2) Wilson measure of the tuning and its blocking):
`(B : BlockingFamily T) → 0 < λ → H1Local T B λ Vk Vinf → LimitDprime λ Vinf → ObsTransfer T B → SlabDecay T`,
with rate `min(m, λ/(4L₁))` (`m` from `ObsTransfer`) and, at level `k`, constant
`4 (1 − γ')⁻¹ |K| (V k + 1) C_{λ/4} + 5c`, `C_r = 24 e^r / r⁴` (`γ'` from `blockGap_of_blockedRoute`).

Proof steps, each a Lean lemma:
1. `gaugeInvariant_comp_tShift`, `gaugeInvariant_comp_thetaConn` (from `tShift_gaugeTransform`,
   `thetaConn_gaugeTransform`: `Θ(g·U) = (g∘reflSite)·ΘU`, `S_j(g·U) = (g∘shiftSite j)·S_j U`) — the shifted and
   reflected slab observables are gauge invariant, as `ObsTransfer` requires. `depOn_filter`, `depOn_tShift_image`,
   `depOn_theta_image`: supports `S_n(supp ∩ slab)`, `Θ(supp ∩ slab)` (≤ `V k` links); `sep_shift_mirror`: link
   distance `≥ n`, so `ObsTransfer` applies with `D = n a_k`.
2. `abs_cov_sub_le_condExp` (any probability space, any sub-σ-algebra, S, elementary): from
   `∫|E[F|m] − f| ≤ δ`, `∫|E[G|m] − g| ≤ δ`, `|E[FG] − E[E[F|m]E[G|m]]| ≤ δ`, all functions bounded by 1:
   `|Cov(F, G) − Cov(f, g)| ≤ 5δ`.
3. `blockGap_of_blockedRoute` (Assembly) with `v_f = 2·1_{A'}`, `L_g = 2`, `R = D/(2L₁)`; `|A'| ≤ |K|(V k + 1)(1 + D/L₁)⁴`;
   `poly4_exp_bound`: `(1 + x)⁴ e^{-rx} ≤ 24 e^r / r⁴` absorbs the polynomial into half the exponential.

Consequences: `BlockedRoute T` (the four hypotheses bundled), `slabDecay_of_blockedRoute'`,
**`openPieces_of_blockedRoute : OnLCP T → NonTrivial T → BlockedRoute T → OpenPieces T`** and
`assembly_blockedRoute : OnLCP T → BlockedRoute T → MassGap T ∧ LatticeGap T ∧ LimitRP T` (D, given the above).
So the blocked route is now a proved sufficient condition for route A's hypothesis; the remark in `Assembly.lean`
("Missing Lean link L1 … paper only; this route is not part of `OpenPieces`") is out of date.

### 4.2 What the hypotheses carry

`LimitDprime` is worst-case D′ at L₁ (stronger than the gap, false below `1/T_c`), `H1Local` is the lattice-uniform
local convergence of blocked potentials (P3.2/P3.3 in a stronger, volume-uniform form than §2 proves), and
`ObsTransfer` (P5.2) is a conditional-decoupling statement about the fine theory given the block variables. Pure noise
satisfies `SlabDecay`; the identification sits in `OnLCP`/`NonTrivial`, as before. Photon: `LimitDprime` fails.

### 4.3 Why `SlabDecay` and not workstream 4's `TorusDecay`

`TorusDecay` asks one constant for all levels. Here the constant carries `V k` (the fine support bound of the slab
family) through `ObsTransfer`'s count `|A'| ≤ K(|A₀| + 1)(1 + D/L₁)⁴`, which counts **fine** links. With that count
stated in physical units (`a_k⁴|A₀|/L₁⁴`, i.e. L₁ cells) the same proof gives a level-uniform constant for families of
bounded physical support (`a_k⁴ V k` bounded), but not for all support bounds `V`, which `TorusDecay` quantifies over:
any Dobrushin-type route pays `∑ osc` of the observable; a support-independent constant is a spectral (transfer-matrix)
statement. Suggested change if wanted (not made: `Assembly.lean` is not mine): an `ObsTransfer` variant with the
physical count, plus a `TorusDecay` variant restricted to `sup_k a_k⁴ V k < ∞`.

## 5. `dist` as a metric (review finding 5)

The round-3 theorems need only `d(x, x) = 0` and the triangle inequality; they are correct as stated, and requiring a
metric would only weaken them. `linkDist` itself is **not** a metric: `linkDist_not_definite` (two distinct links at one
base site are at distance 0). A genuine metric: `linkMetric e e' = linkDist e e' + [e ≠ e']` with `linkMetric_self`,
`linkMetric_symm`, `linkMetric_triangle`, `eq_of_linkMetric_eq_zero`, `linkMetric_le` (≤ `linkDist + 1`), and
`blockGap_linkMetric`: the blocked-route block decay with distances in `linkMetric`, at the cost of a factor `e^λ`. All D.

## 6. Blueprint status changes (proposed for `PROOF-BLUEPRINT.md`)

| piece | was | now |
|---|---|---|
| P3.2 Lemma T | paper | **Lean** for maps, kernels, densities, block specifications at every boundary (`ProofPhase.Quantum.LemmaT`), instantiated on SU(2) Wilson measures; T(b) for image-variable conditional laws: paper (RN version step) |
| P3.3 per-volume gap theorem | paper | **Lean** (`NoisyBlocking.perVolumeGap`, `_eventually`, `blockLimit_gap`): one theorem from one noisy step + H2-all to the per-volume gap of the L₁ block observables of the SU(2) Wilson family, order mesh → volume → observable; H2-all open |
| P6.1 (block level) | external | `exists_blockLimit`: subsequential mesh limit of the noisy L₁ block theory in all volumes at once, **Lean**, no hypothesis (block level only, not fields) |
| P6.5 infinite-volume limit | open | existence of limit states at fixed spacing: **Lean** (`exists_limitState`, weak convergence); measurable-observable convergence and invariance: paper |
| P7.4 blocked route | paper only | **Lean** (`slabDecay_of_blockedRoute`, `openPieces_of_blockedRoute`); reaches `SlabDecay`, not `TorusDecay` (§4.3) |
| review finding 2 (three islands) | open | closed for the per-volume route (WpNoise + Lemma T + Robust in one theorem on SU(2) Wilson laws) |
| review finding 5 (`dist`) | open | answered (§5) |

`ASSEMBLY.md` "Missing Lean link L1" and the `Assembly.lean` section remark on it are stale; P7.4 can be listed in
`axioms-asm.sh` via `ProofPhase.Quantum.slabDecay_of_blockedRoute`.

## 7. Clicks with the other workstreams

* **Workstream 1 (route A, centre-blind block variables, a good blocking).** `slabDecay_of_blockedRoute` holds for
  **every** `BlockingFamily`, so a good blocking (P1.8) plugs in unchanged; but `H1Local`/`LimitDprime` type the coarse
  variables as SU(2) links. For centre-blind (SO(3)) variables the coarse group must become a parameter; the proof of
  P7.4 never uses SU(2) on the coarse side except through `blockGap_of_blockedRoute`, so the generalisation is
  mechanical. Likewise `NoisyBlocking.Ψ` could target SO(3) links: `perVolumeGap` only uses `haarG`, `linkDist`.
* **Workstream 4 (existence).** Volume-dependent couplings are respected (`VTuning` in `PerVolume`, `LimitStates`).
  The per-volume theorem is in their order (mesh first at fixed volume): `blockLimit_gap` is the block-level gap of
  exactly the kind of limit their construction produces, conditional on H2-all.
* **Workstream 2 (route B):** no contact; route B's sector transfer P5.1 is untouched.

## 8. Next step

Close the gap between the two forms of the crossover that now both feed Lean: H2-all (per volume, every mesh limit
point, proved to give the block gap) and `H1Local ∧ LimitDprime` (lattice uniform, proved to give `SlabDecay`). The
cheapest concrete step: an `ObsTransfer` with the coarse support counted in L₁ cells (§4.3), which would let P7.4 reach a
level-uniform constant for physically bounded observables, the form workstream 4's both-orders bridge consumes.
