# Workstream 4: existence and identification (blueprint P6.1-P6.10), 2026-11-22

Starting point: what the OpenAI Lean construction actually proves, read in its source; then the bridge to our objects
(`formal/ProofPhase/Objects.lean`, `Assembly.lean`); then the P6 statuses.

## How to read the claim levels

- **[source]**: I read the Lean *statement* in the OpenAI source myself (file:line below). Their *proofs* were not built or
  checked by us: the local clone in WSL `ym-replay` (`~/ym-replay/YM`, commit `b379615f`, 15 Nov 2026; submission
  `submissions/openai-20261028/submission`, Lean 4.32.0) has passed only the replay's integrity stage (`~/ym-replay/stage1.log`);
  its build cache holds 110 oleans (reference statement only, no `Solution.olean`), so no `#check` or `#print axioms` was
  possible. That the proofs check rests on the committee's audit and the README's verification record **[doc]**.
- **[doc]**: README or committee text only (the assessment's wording is quoted from `HANDOVER.md` §2; I did not re-read the PDF).
- **[Lean, ours]**: proved in our new file `formal/ProofPhase/Existence/Bridge.lean`, built in `~/formal-ws4` (Lean 4.34.0,
  Mathlib v4.34.0), axioms `propext, Classical.choice, Quot.sound` only, no `sorry` (`axioms-ws4.sh`).
- **[paper]**: an argument in this note, not machine-checked.

Paths below are relative to the submission folder; `YM/...` is its library.

## 1. What exactly is proved (their main theorem)

**Headline.** `YangMills.jointExistence : JointExistence` (`Solution.lean:4`; statement `ChallengeSpec.lean:186-188`) [source]:
for every `g : GaugeGroup` with `g.IsSimple` there is **one** `C : WilsonFamily g` with `WilsonRegularity C`, and **for every
strictly increasing volume sequence `p`** there are a further subsequence `q` and a `T : Hierarchy C` with
`T.Properties (p ∘ q)`. The detailed form is `YangMills.constructed` (`Construction.lean:15`), which returns per refinement one
table `S`, one `Final` record (`YM/Spec/Closed.lean:64`) and the clauses of `Headline.WilsonExistence`
(`YM/Nonperturbative/HeadlineSpec.lean:143`).

**Gauge groups** [source]. `GaugeGroup` (`PublicTheory.lean:25`): a closed subgroup of `U(n+1)` with its Lie algebra
`{X | exp(tX) ∈ G ∀t}`; `IsSimple` (`:39`): non-abelian and no proper ideals. So every compact Lie group with simple
non-abelian Lie algebra in some faithful unitary representation. SU(2) is `YM/Next/FOUNDATIONS/SU2.lean:36`
(`{X ∈ U(2) | det X = 1}`), specialised in `ConcreteSU2.lean:15`.

**Lattice objects** [source], `PublicWilson.lean`:
- configurations `(Site l × Axis) → G` on `(ℤ/l)⁴`, plaquette `U(x,i)U(x+i,j)U(x+j,i)⁻¹U(x,j)⁻¹`, one per site and `i < j` (`:20`);
- energy `Σ_p (1 − Re tr U_p/(n+1))` (`:25`); law `Z⁻¹ e^{−β E(U)}` times product probability Haar (`:29`); the Haar measure is
  `Measure.haarMeasure` normalised on the whole group (`YM/Gauge/MatrixGroup.lean:187`);
- `WilsonFamily` (`:35`): period `L_p` (physical side), denominator `D_N` (mesh `1/D_N`), lattice side `L_p·D_N`, bare coupling
  `beta N p` (**allowed to depend on the volume `p`**), insertions `Token → Site → Configuration → ℂ`. Internally `4 ∣ L_p`,
  `D_N` a product of odd block factors ≥ 3 (`YM/Lattice/Scale.lean:28-45`).

**Tuning** [source]. `WilsonRegularity.running` (`ChallengeSpec.lean:13`): `β_{N,p}/log D_N → slope > 0` **uniformly in `p`**; the
slope is `2·b₀ = slopeConstant = 11·C_A/(24π²)` (`HierarchyBridge.lean:18`, `YM/Gauge/Colors.lean:180-184`). With their colour
normalisation `C_A = 2N²` for SU(N) (my computation from those definitions), so the slope is `11N²/(12π²)` for `β' = 2N/g²`, i.e.
`11/(3π²)` for SU(2). Internally the bare coupling is shot per `(N, p)` so that the flow reaches a fixed reference value at their
unit (`YM/RG/History.lean:234-241`, `reaches : β N p 0 = bar`); `H1-OPENAI.md` puts `bar ≳ 9·10⁵`.

**Observables** [source]. Insertions are continuous, gauge invariant, and depend only on a fixed stencil in lattice units at every
spacing and volume (`ChallengeSpec.lean:15-22`); they are renormalised local polynomial insertions (`YM/Source/Construction.lean:42`,
"the normalized readout"). Correlations are smeared against tests supported **away from coincident points** and inside the
fundamental cell (`PublicWilson.lean:59-81`). No bounded block observables, no Wilson loops.

**Order of limits** [source]. `WilsonFamily.Converges` (`PublicWilson.lean:85`): for each fixed volume `p` the smeared moments
converge as `N → ∞` along the **full** mesh sequence; then the row limits converge **along the volume subsequence** `p∘q`. Mesh first,
volume second; subsequence only in the volume (`YM/Extraction/Limits.lean:32`, `Construction.lean:23` with mesh `Sequence.full`).
Pointwise (unsmeared) mesh limits on compact separated sets are also part of `Final` (`Spec/Closed.lean:23`, `Extraction/Limits.lean:57-68`).

**Axioms established** [source]:
- *Euclidean side, unselected table* (`Seed.kernel : S.Hierarchy`, `Spec/Closed.lean:24`; `YM/Euclid/Words.lean:141-149`): symmetry,
  real structure and signed reflections (`RealSpin`), translation invariance (`Homogeneous`), **reflection positivity about every
  coordinate axis** (`RP`, `:123`, and smeared `RPSmear`), smoothness off coincidences, a polynomial bound near coincidences
  (`Capped`). **Full O(4) covariance** of the table (`Locals.motion : X.turns.Oriented S`, `Spec/Closed.lean:39`;
  `YM/Euclid/Stress.lean:46`; `Ortho` = real 4×4 orthogonal matrices, `YM/Space/Orthogonal.lean:20`), and for every character
  (`YM/Phase/Mixture.lean:142`).
- *Wightman side, selected phase* (`Hierarchy.Reconstructed`, `ChallengeSpec.lean:117-143`; axioms `PublicTheory.lean:270-319`):
  W0 spectral representation, **positive energy** (spectrum in the forward cone) and **uniqueness of the translation-invariant
  vacuum**; W1 tempered fields on a dense invariant domain, cyclic vacuum, adjoints; W2 covariance under the full proper
  orthochronous **Poincaré** group (coordinates `PoincareCoordinates`, `:209-246`); W3 locality. Analytic continuation in ordered
  complex times recovers the selected Euclidean correlations (`root`, `:137`) and the Wightman vacuum moments are its boundary values
  (`boundary`, `:139`). Every character also has a Wightman reconstruction (`HeadlineSpec.lean:79`).
- *Not established as such*: the OS regularity (linear growth) condition; they reconstruct by direct analytic continuation instead.
  A cluster property is not stated separately; for a Wightman theory it is equivalent to the unique vacuum (standard), so the
  selected phase clusters, **with no rate**.

**The phase decomposition (important for identification)** [source]. The lattice limit (`correlation none`) is the **unselected**
table. The Wightman theory belongs to one **selected character** of a decomposition of it: `Hierarchy.Character` is a compact metric
space with a full-support probability measure (`ChallengeSpec.lean:34-40, 124-125`), `mixture` (`:133`): the unselected correlation is
the average of the character correlations. The decomposition is built from the commutative algebra of slab operators compressed to
the time-invariant vectors of the OS space of the Wilson limit (`YM/Phase/Mixture.lean:78-86, 127-148`; `heat : UniqueHeat`), i.e. the
standard decomposition into phases with a unique vacuum. **The Wightman theory is therefore a phase of the lattice limit, not
necessarily the lattice limit itself**; if the limit already has a unique vacuum the character space is a point.

**Non-triviality (`nonfree`)** [source] (`ChallengeSpec.lean:168-175`; detailed `HeadlineSpec.lean:84-120`): in the selected phase,
for the centred grade-4 field (identified in the detailed theorem with the trace of the conserved stress tensor minus its vacuum value,
`HeadlineSpec.lean:87-91`): (i) `r⁸ log²(1/r) · S₂(r) → 3·dim g/π⁴ > 0` as `r → 0` (time-axis pair at distance `r`); (ii) no finite
sum of massive Wick mass-shell profiles agrees with `S₂` at all small `r`; detailed: no finite Wick-polynomial correlator agrees, and
no Maxwell-Fock realisation (with an invariant-sector variant) reproduces it. The `log²` is the asymptotic-freedom signature.

**Uniqueness**: not claimed [source: volume subsequence and phase mixture are built into the statement; doc: committee "does not prove
that the infinite-volume limit is unique"]. **Correlation decay / gap**: no quantitative decay anywhere in the headline [source];
README: "A positive mass gap ... outside its scope" [doc]; committee: "no evidence for or against a mass gap" [doc].

**README vs Lean.** Every README claim I checked has a matching Lean statement: Wilson origin, Wightman reconstruction incl.
Poincaré covariance and unique vacuum, the phase average, OPE, the trace test. The README's "uniformly in the volume" for the running
matches `∀ᶠ N, ∀ p`. Not checked: the OPE content, the contact distributions (`Contacts.Solstice`), `Pert.FirstExtension`,
`Pert.Position.FourMeters`, `Independent.Core`.

## 2. The identification bridge

### What corresponds (checked)

| ours | theirs | status |
|---|---|---|
| `wilsonMeasure G n β` on `(ℤ/N)^d` (`e^{β Re tr U_p}`) | `wilsonLaw` at `β' = n·β` | **[Lean, ours]** `plaqLaw_eq_wilsonMeasure` for any compact group; SU(2): `β_ours = β'/2` (`wilsonMeasure_SU2_eq_plaqLaw`). `plaqLaw` is my restatement of `PublicWilson.lean:25-33` on our types; the type match (`Site × Axis` ↔ `LatticeLink`, same plaquette orientation, same `i < j` plaquettes, `{det = 1} ⊂ U(2)` ↔ `specialUnitaryGroup`, both Haar measures `haarMeasure ⊤` on a compact group) is by reading [source] |
| unit `L₁`, resolution `ℓ_k`, torus `j` of side `2(j+1)ℓ_k` | unit 1, `D_N`, period `L_p` | **[Lean, ours]** `WilsonData.toV`, `side_vol`: their lattice at `(N,p)` is our torus at level `N`, `j = L_p/2 − 1` (`4 ∣ L_p` makes it even); `ym_vol`: the measure there is their law at `β_{N,p}` |
| `Tuning.β k` (one per level) | `β_{N,p}` (per level and volume) | our `Tuning` cannot hold their family; **`VTuning`** (`β_{k,j}`) can; `Tuning.toV` embeds ours, `massGapVF_toV_iff : MassGapVF T.toV ↔ MassGap T` |
| `MassGap`: volume first, then spacing | mesh first at fixed volume, then volume (subsequence) | **`MassGapMF`** states the gap in their order (every volume sequence, every limit point) |
| slab observables: bounded, gauge invariant, in a time slab, `≤ V k` links | renormalised local insertions, unbounded, fixed lattice stencil, smeared at separated points | **no bridge yet** (see "must be proved", item 3) |
| `NonTrivial` (bounded slab correlation bounded away from 0) | `nonfree` (trace two-point function, selected phase) | no bridge (different observables) |
| `LimitRP` (proved) | `S.Hierarchy.positive` | same property, different objects |

**Order of limits, proved [Lean, ours].** `TorusDecay V`: `SlabDecay` with a constant independent of the level (one rate `m`; for each
thickness and support bound one `k₀` and one `C`; every torus, every level `≥ k₀`, while the correlation fits the torus).
`massGapMF_of_torusDecay`: `a_k → 0 ∧ TorusDecay V ⇒ MassGapMF V` (Theorem C on the torus, `corr_le_of_decay`, brings the constant to
`2` as the volume grows). `bothOrders_of_torusDecay`: for our tunings `TorusDecay ⇒ MassGap ∧ MassGapMF`. So **one statement uniform in
depth and volume gives the gap in both orders of limits**.
- Why not `SlabDecay` itself: its constant may grow with the level (D′'s sufficient condition gives `cubeConst` growing with
  `side L₀ a_k` and `V k`), and at fixed volume Theorem C cannot absorb a growing constant, so `SlabDecay` does not reach their order.
- Strength: `TorusDecay` is stronger than `SlabDecay` and `LatticeGap` (level-uniform constant); weaker-or-equal to what a gapped
  theory gives on large tori (the OS bound has constant `‖F̃Ω‖² ≤ 2` for every slab observable, whatever its support), and vacuous on
  small tori beyond a constant (the decay is only asked while `2n + 2·thick + 2 ≤ side`), so it passes the **deconfinement test**. It is
  group-blind and pure noise satisfies it (like `SlabDecay`): the identification stays with P6.2/P6.7. **Photon test**: the free
  photon fails it (power-law slab correlations), as it should; `plaqLaw_eq_wilsonMeasure` is a definitional identity and makes no
  claim either way.

### A convention error found in `OnLCP.running` [paper; arithmetic checked twice]

Our measure has weight `e^{β Re tr U_p}`. The standard SU(2) Wilson action is `β_std Σ(1 − ½ Re tr U_p)` with `β_std = 4/g²`, i.e.
weight `e^{(β_std/2) Re tr U_p}`, so **`β_ours = β_std/2 = 2/g²`** (this is exactly `plaqLaw_eq_wilsonMeasure` with `n = 2`). One loop:
`1/g² = 2b₀ log(1/(aΛ))`, `b₀ = 11/(24π²)`, so `β_std/log ℓ → 11/(3π²)` and **`β_ours/log ℓ → 11/(6π²)`**. `Assembly.lean:70-79` asks
`β_ours/log ℓ_k → 11/(3π²)` ("β = 4/g²"), twice the physical slope. Their family confirms it independently: their slope is `11/(3π²)`
for `β'` (computed above), hence `11/(6π²)` for our `β`, so **their family fails our `OnLCP.running` as written**. A family satisfying
it has physical spacing `∝ ℓ_k^{-2}` while it claims `a_k = L₁/ℓ_k`, so the physical size of `L₁` shrinks to zero: not a line of
constant physics. Fix (for the assembly's owner, not edited here): `oneLoopSlope := 11/(6π²)` (or define the weight as
`e^{(β/2) Re tr}`); `not_onLCP_of_bounded` and `bareRunning_witness` survive with the new constant; the ASSEMBLY.md item 7 slope
`11N²/(12π²)` is the slope for `β_std`; for our `e^{β Re tr}` with SU(N) it is `11N/(12π²)`.

### What must be proved to conclude "their limit satisfies our `MassGap` iff ours does"

1. **Tuning** (P6.7): fix the slope (above); generalise `OnLCP` to `VTuning` (running uniform in `j`, which they have); relate the
   renormalisation conditions: theirs fixes the coupling at their unit (`β = bar`), ours fixes the act number `z(L₁) = L₁·E_e → z⋆`.
   At weak coupling the small-box flux energy is a function of the running coupling at the box size ('t Hooft; Luescher's small-volume
   expansion), so `bar` determines `z⋆` to leading order. Needed: `z_k` converges along their family (a statement inside their
   controlled weak-coupling range, so plausibly reachable with their small-field bounds). Click with ws2 (act number) and ws3.
2. **Order of limits**: done for slab observables by `TorusDecay` (Lean). Converse direction (their order ⇒ ours) is not available
   in general; route through `TorusDecay` instead.
3. **Observables** (the real gap). Their fields are unbounded and renormalised and only their **separated** moments converge, so the
   law of a smeared field (needed for any bounded function of it) is not controlled (this is the committee's open "continuum
   probability measure"). Two ways across:
   - (a) *ratio form on the lattice* [paper]: on each RP torus the reflected correlation is `⟨ψ, Tⁿψ⟩` with `T ≥ 0` (transfer
     matrix), so a uniform spectral gap gives `|Cov(F∘S_n, ΘF)| ≤ Cov(F∘S_{n₀}, ΘF)·e^{−m(n−n₀)a}` for **every** L² function of the
     half, renormalised fields included, with no sup-norm constant. A `TorusDecayL2` in this form transfers to their separated two-point
     functions in their order and gives the gap of their unselected table; the bounded form `TorusDecay` implies it on the torus by
     the argument of `spectral_gap_of_decay` plus the Hankel/Theorem-C handling of the periodic time direction (to be written).
   - (b) *continuum measure*: construct the limit as a probability measure on distributions (open; committee list).
4. **Phases** [paper]: a gap of the unselected table forces a single phase. For a time-invariant observable `A`, the reflected
   covariance at large `τ` tends to `Var_μ(⟨A⟩_i) ≥ 0` (each phase clusters); decay to 0 gives `⟨A⟩_i` constant `μ`-a.e., hence
   everywhere (`characterContinuity`, full support), so the character map, which is bijective (`Mixture.lean:83`), has a one-point
   domain and selected = unselected. Then the gap passes to their Wightman theory (cyclic vacuum, fields dense).
5. **Uniqueness** is not needed for any of this (`MassGap`, `MassGapMF` quantify over every limit point and every volume sequence).

With 1-4, "`TorusDecayL2` for their family ⇒ their Wightman theory has a mass gap", and conversely "their theory has a gap ⇒
`MassGap` for their family" would additionally need the gap of the continuum theory to come back to bounded lattice observables (3b).

## 3. P6 statuses (blueprint v2 numbering)

| piece | status now | exact pointer | cheapest next step |
|---|---|---|---|
| P6.1 existence (subsequential), correlation functions | **external, statement verified in source** for their family, their observables, mesh-then-volume order; proof not checked by us. For our bounded slab observables limit points exist trivially (bounded by 2); existence of *a limit* is the uniqueness question | `ChallengeSpec.lean:186`, `PublicWilson.lean:85`, `Construction.lean:15` | the replay thread (HANDOVER A) builds the submission and runs `#print axioms YangMills.jointExistence` (about 3 h, 52 GB; not on this laptop while it is busy) |
| P6.2 identification: non-trivial, unique | non-triviality **external (source)** for their selected phase (`nonfree`, positive short-distance amplitude, not free); **open** for our `NonTrivial`; uniqueness **open** (not claimed by them) | `ChallengeSpec.lean:168-175`, `HeadlineSpec.lean:84-120` | add `NonTrivialSep` (separated renormalised two-point function bounded away from 0); their `TraceTest.amplitudePositive` + `shortDistance` discharge it for their family once the observable bridge 3(a) exists |
| P6.3 OS positivity | ours: **Lean** (`limitRP`); theirs: **external (source)**, every axis, smeared too | `Objects.lean` `limitRP`; `YM/Euclid/Words.lean:123-139` | none for positivity |
| P6.4 Euclidean invariance | theirs **external (source)**: translations and full O(4) on Schwinger functions, Poincaré W2; ours not statable (no continuum fields) | `Spec/Closed.lean:39`, `Euclid/Stress.lean:46`, `PublicTheory.lean:287` | adopt their field notion (fixed-stencil renormalised gauge-invariant insertion, `ChallengeSpec.lean:15-22`) as our P6.8 object; then state P6.4 on it |
| P6.5 infinite-volume limit | theirs **external (source)**: subsequential (compactness), with a phase decomposition; uniqueness **open**; `MassGapMF` needs none | `PublicWilson.lean:85`, `Mixture.lean:127` | none cheap; a gap gives single phase (item 4) but not uniqueness over volume subsequences |
| P6.6 Wightman reconstruction | theirs **external (source)**, selected phase and every character: W0 (unique vacuum, positive energy), W1-W3, Poincaré | `ChallengeSpec.lean:117-143`, `PublicTheory.lean:270-319`, `HeadlineSpec.lean:52-81` | for ours: known given OS axioms on a field algebra (P6.8) |
| P6.7 tuning inside the hypotheses | **open**, now with a **found error** (`OnLCP.running` slope off by 2) and a bridge object (`VTuning`, `WilsonData.toV`) [Lean, ours] | `Assembly.lean:70-79`; `Bridge.lean` | fix the slope; `OnLCPV` for `VTuning`; check `z_k` along their family (ws2/ws3) |
| P6.8 renormalised local fields as distributions | theirs **external (source, partial)**: fields smooth off coincidences, `Capped` growth, contact extension (README, `Contacts`, not read in detail), tempered Wightman fields; OS regularity not stated | `Euclid/Table.lean:88-99`, `HeadlineSpec.lean:153` | define `LocalField` in our Lean (stencil, gauge invariant, continuous) |
| P6.9 short-distance agreement with PT | theirs **external (source, partial)**: leading trace two-point asymptotics `r⁻⁸ log⁻²` with the one-loop amplitude; position-test comparison (not read) | `ChallengeSpec.lean:173`, `HeadlineSpec.lean:92` | none cheap for us |
| P6.10 every compact simple G | existence **external (source)** for every closed simple non-abelian matrix group; our bridge lemma `plaqLaw_eq_wilsonMeasure` is generic; our tuning, scheme and gap are SU(2) | `PublicTheory.lean:25-45` | generalise `Tuning`/`OnLCP` to SU(N) with slope `11N/(12π²)` for `e^{β Re tr}` |

**Not discharged by any of this:** the gap (P4, P5), our `NonTrivial`, uniqueness, our tuning. Nothing is marked discharged on a
README claim.

## 4. Clicks

- **The owner's DMP reading, instantiated twice.** Their existence proof *is* "the finite-depth family with depth-uniform bounds,
  the limit by compactness": per-level bounds whose constants depend on the level only, not on the cutoff or the volume
  (`History.Conv`, `YM/RG/History.lean:213`, budgets uniform in `p`, `H1-OPENAI.md` §2), give the mesh limit; the volume limit is only a limit point
  (compactness), and that is exactly why uniqueness is missing. The same shape for the gap is `TorusDecay` (one rate, one constant, every
  level, every torus), and Lean shows it makes the order of limits irrelevant (`bothOrders_of_torusDecay`). Where the analytic
  existence needs a choice (an order, a subsequence, a phase), the finite-depth uniform statement does not.
- **Gap ⇒ one phase.** Their selected phase is the price of non-uniqueness; a gap of the lattice limit removes the choice (item 4).
  Phases here are the time-ergodic components; this is P5.3's "uniqueness of the vacuum".
- **ws1 (route A):** aim at `TorusDecay` rather than `SlabDecay`; it is what a gapped theory gives (OS constant ≤ 2 on large tori) and
  it covers the OpenAI order. D′'s constant grows with the level, so D′ alone does not reach it.
- **ws2 (route B) / ws3 (quantum half):** their renormalisation condition `β(unit) = bar` and our `z(L₁) → z⋆` are both "fix the
  running coupling at one length"; at weak coupling they should be equivalent through the small-box flux energy (bridge item 1).
- **Statement bridge stage 2 of HANDOVER's aspirational plan** ("our lattice measure is their lattice measure") is now proved for the
  restated law (`plaqLaw_eq_wilsonMeasure`, `ym_vol`), with the type identification by reading.

## Files

- `formal/ProofPhase/Existence/Bridge.lean` (new): `plaqLaw`, `plaqLaw_eq_wilsonMeasure`, `wilsonMeasure_SU2_eq_plaqLaw`, `VTuning`,
  `Tuning.toV`, `WilsonData` (`toV`, `vol`, `side_vol`, `βv_vol`, `ym_vol`, `tendsto_a`), `MassGapVF`, `MassGapMF`, `TorusDecay`,
  `slabDecay_of_torusDecay`, `side_ge`, `massGapMF_of_torusDecay`, `bothOrders_of_torusDecay`.
- Scripts here: `setup-ws4.sh`, `build-ws4.sh`, `axioms-ws4.sh` (Lean); `probe.sh`, `probe2.sh`, `grep.sh` (read-only access to the
  replay clone). Build: `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws4-existence/build-ws4.sh`
  then `.../axioms-ws4.sh`.
- Nothing else was edited; no commit, no push, no GPU.
