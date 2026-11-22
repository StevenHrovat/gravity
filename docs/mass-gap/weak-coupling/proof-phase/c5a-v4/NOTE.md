# Cycle 5, workstream 1 (c5a-v4): assembly version 4, cut at L_* (2026-11-22)

Plan step 1 of the draft blueprint v4 (`../c4-fable/BLUEPRINT-v4-DRAFT.md`, read with `../c4-fable/REVIEW.md`). Lean in
`../../../formal/ProofPhase/V4/` (`LCP`, `Gap`, `Recursion`, `UV`, `Top`). `Objects.lean` and `Assembly.lean` are
**unchanged**; no renames; every existing theorem builds as before.

Build (in `~/formal-c5a`, Lean 4.34.0, Mathlib v4.34.0):

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c5a-v4/setup.sh
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c5a-v4/build.sh ProofPhase.V4.Top
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c5a-v4/axioms.sh
```

`axioms.log`: 24 headline theorems, all `propext, Classical.choice, Quot.sound`; no `sorry`, no `native_decide`, no new
axioms. Marks: **S** = substantive proof, **D** = definitional or bookkeeping.

---

## 0. Result in plain words

* The v4 top theorem is in Lean exactly as drafted (`yang_mills_assembly_v4`), for any `BlockingFamily`, with the tuning's
  unit read as L_*. It has one input of gap strength, `BlockGapUnifW`, and it is named as such.
* `OnLCP'` (two-sided renormalisation condition) is in Lean; `OnLCP -> OnLCP'` is proved; every use of `OnLCP` in the
  assembly needs only `OnLCP'` (in fact only clause (i), except route B which needs a lower bound).
* The recursion lemma **as drafted is not provable from v3's literal input shapes**; its true version is proved
  (`blockGapBddW_of_stageTwo`). It needs (i) a slightly weaker landing statement, the bounded block gap `BlockGapBddW`,
  which is all the top theorem consumes (so the top theorem is restated with it, `yang_mills_assembly_v4_bdd`, a stronger
  theorem), and (ii) the stage-2 errors with an oscillation/Lipschitz prefactor instead of v3's extent index. With these,
  cycles 2 to 4 are a proved strategy (a) for IR (`yang_mills_assembly_v4_strategyA`).
* Seg1 is wired into the ultraviolet layer as the supplier of the L_* theory (`gibbsRep_of_uv1Polymer`); nothing in the
  top theorem consumes it, and the note says why. Route B, the sup family and `H1LocalLipW ∧ LimitDprimeW` are out of the
  top statement (files kept).

---

## 1. The top theorem (`V4/Top.lean`)

```
theorem ProofPhase.V4.yang_mills_assembly_v4 {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T) (B : BlockingFamily T)
    {lam : ℝ} (hlam : 0 < lam) (hIR : BlockGapUnifW T B lam) (hUV : ObsTransferPhysTW T B) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T
```

Proof (S, three lines): `V3.torusDecayLoc_of_blockGapUnifW`, `Torus.bothOrdersLoc_of_torusDecayLoc` with
`OnLCP'.tendsto_a`, `limitRP`. The unit `T.L₁` is read as L_*; `B` blocks onto L_* cells; nothing in the statement depends
on which blocking (c5c's noisy local family plugs in once it is a `BlockingFamily`; if c5c changes the type of
`BlockingFamily`, the theorem is re-stated over the new type with the same proof, since it uses only `.B` and `.meas`).

The sharper form, with the infrared input the recursion lemma produces:

```
def ProofPhase.V4.BlockGapBddW (T : Tuning) (B : BlockingFamily T) (lam : ℝ) : Prop :=
  ∃ C ≥ 0, ∃ k₀, ∀ k ≥ k₀, ∀ j f g A Sg vf Lg R,
    Measurable f → Measurable g → (∀ V, |f V| ≤ 1) → (∀ V, |g V| ≤ 1) → DepOn f A → DepOn g Sg →
    OscBound f vf → 0 ≤ Lg → LipBound geodSU2 g (fun _ => Lg) → 0 ≤ R → (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |Cov_{T.ym k j}(f ∘ B, g ∘ B)| ≤ C * (1 + Σ_{a∈A} vf a) * (1 + Lg) * exp(-(lam * R))

theorem ProofPhase.V4.yang_mills_assembly_v4_bdd (hL : OnLCP' T) (hN : NonTrivial T) (B : BlockingFamily T)
    (hlam : 0 < lam) (hIR : BlockGapBddW T B lam) (hUV : ObsTransferPhysTW T B) : <same conclusion>
```

`blockGapBddW_of_unifW` (D): `BlockGapUnifW -> BlockGapBddW`. `torusDecayLoc_of_blockGapBddW` (S) is the v3 cut with the
weaker input (constant `C(1 + 2K)(1 + K)`; same rate `min(λ/(4L_*), m)`).

Packaged: `structure OpenInputsV4 T := lcp : OnLCP' T, nontrivial : NonTrivial T, layers : ∃ B lam, 0 < lam ∧
BlockGapBddW T B lam ∧ ObsTransferPhysTW T B`, with `yang_mills_assembly_v4_inputs`, `openInputsV4_of_unifW`,
`openInputsV4_of_levelTorusRouteW` (v3's preferred inputs at the same unit imply v4's: `OnLCP -> OnLCP'`,
`LevelDprimeW -> BlockGapUnifW`; v3's sup branch does not, it has no Lipschitz approximant) and `not_trivial_v4` (pure
noise fails `OnLCP'`).

**Generic form of the infrared statement** (`V4/Gap.lean`): `LawGapW ρ λ`, `LawGapBddW ρ λ`, `LevelDprimeWOn ρ λ` for any
family of laws `ρ k j` on tori of side `M j`, with `BlockGapUnifW T B λ ↔ LawGapW (blockedLaw T B) λ`, the same for the
bounded form, `LevelDprimeW T B λ ↔ LevelDprimeWOn (blockedLaw T B) λ` (`Iff.rfl`) and `lawGapW_of_levelDprimeWOn` (S).
This lets one statement be asked of the L_* theory and of its further blockings.

---

## 2. `OnLCP'` (`V4/LCP.lean`)

```
structure ProofPhase.OnLCP' (T : Tuning) : Prop where
  resolution : Tendsto T.ℓ atTop atTop
  running : Tendsto (fun k => T.β k / Real.log (T.ℓ k)) atTop (𝓝 oneLoopSlope)
  scheme : ∃ zlo zhi : ℝ, 0 < zlo ∧ zlo ≤ zhi ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ h : ℕ → ℝ,
    IsFluxLimitSU2 (T.β k) (T.box k 0) h → zlo ≤ actRate (T.box k 0) h ∧ actRate (T.box k 0) h ≤ zhi
```

* `OnLCP.toOnLCP'` (S): `OnLCP -> OnLCP'` with `[z⋆/2, 2z⋆]`. Uniformity over the flux time limits needs the choice
  argument of `OnLCP.eventually_actRate`, generalised to any neighbourhood (`OnLCP.eventually_mem_nhds`). The converse is
  false (a bounded act number need not converge).
* **Every use of `OnLCP` needs only `OnLCP'`** (checked by grep over `ProofPhase/`): `OnLCP.tendsto_a` (clause (i) only)
  in every route and top theorem (`OnLCP'.tendsto_a`); `OnLCP.eventually_actRate` in route B only, a lower bound
  (`OnLCP'.eventually_actRate`, `fluxGrowth_of_conjW'`); `not_onLCP_of_bounded` uses clause (ii)
  (`not_onLCP'_of_bounded`); `assembly_routeA'` restates route A. Elsewhere `OnLCP` is only passed into structure fields.
* **Choice of the scheme observable.** The draft offers "the segment-1 running coupling at L_* in `[ḡ/2, 2ḡ]`". There is
  no Lean object for that coupling (it belongs to UV1). `OnLCP'` therefore keeps the existing renormalised observable (the
  act number of the unit box) and only weakens convergence to a two-sided bound. Caveat for the blueprint: at L_* (weak
  coupling, small box) the SU(2) flux energy is a tunnelling quantity, exponentially small in `1/g²(L_*)` (review W11), so
  a two-sided bound on it is semiclassical rather than perturbative. A perturbative scheme (a small-loop or flow coupling of
  the L_* box) is the better final choice once UV1 provides the object; the top theorem uses only clause (i), so the
  choice does not affect any proof.

---

## 3. The recursion lemma (`V4/Recursion.lean`)

**As drafted:** "every v3 input set at L₁ = 2^r L_*, stated for the L_* theory, implies `BlockGapUnifW` at L_*".

**Finding: not as stated, for two reasons.**

1. *Extent.* v3's transfer hypotheses (`ObsTransferPhysTW`, `ObsQuasiLocTW`, `CondMassAnn`) have constants indexed by
   the physical extent of the observables and additive errors `c e^{-mD}`. Fed with L_* block observables of bounded
   extent, they give block decay only for block observables of bounded extent, with extent-dependent constants. But
   `BlockGapUnifW` quantifies over block observables of **any** support, and the top theorem really uses that: the
   approximants `ObsTransferPhysTW` produces have supports of unbounded extent (only the oscillation sum is controlled).
2. *Homogeneity.* `BlockGapUnifW` is homogeneous (`C (Σvf) Lg e^{-λR}`, any bounded `f`, `g`). A covariance transfer
   for bounded observables has additive errors; turning them into errors proportional to `Σvf · Lg` would need
   `sup |g − const| ≲ Lg`, false when `Sg` is large.

**True version (proved, S):**

```
def ProofPhase.V4.StageTwoW (ν : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (coarseSide j)))
    (B₂ : ∀ k j : ℕ, GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j)) (s : ℝ) : Prop :=
  ∃ m c K, 0 < m ∧ 0 ≤ c ∧ 0 ≤ K ∧ ∃ k₀, ∀ k ≥ k₀, ∀ j f g A Sg vf Lg R,
    [f, g measurable, |·| ≤ 1, DepOn A / Sg, OscBound f vf, 0 ≤ Lg, LipBound geodSU2 g Lg, 0 ≤ R, dist(A, Sg) ≥ R] →
    ∃ f₂ g₂ A₂ S₂ v₂ L₂, [measurable, |·| ≤ 1, DepOn A₂ / S₂, OscBound f₂ v₂,
      Σ_{A₂} v₂ ≤ K (1 + Σ_A vf)(1 + R)⁴, 0 ≤ L₂ ≤ K (1 + Lg), LipBound geodSU2 g₂ L₂,
      ∀ x ∈ A₂, y ∈ S₂, R/2 ≤ s · linkDist x y] ∧
      ‖E_ν[f | B₂] − f₂ ∘ B₂‖₁, ‖E_ν[g | B₂] − g₂ ∘ B₂‖₁, |E_ν[fg] − E_ν[E[f|B₂] E[g|B₂]]|
        ≤ c (1 + Σ_A vf)(1 + Lg) e^{−mR}            (ν = ν k j, B₂ = B₂ k j)

theorem ProofPhase.V4.blockGapBddW_of_stageTwo {T : Tuning} (B₁ : BlockingFamily T) (B₂ ...) (hB₂ : ∀ k j, Measurable (B₂ k j))
    {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hIR : LawGapBddW (fun k j => (blockedLaw T B₁ k j).map (B₂ k j)) lam₂)
    (hX : StageTwoW (blockedLaw T B₁) B₂ s) :
    ∃ lam, 0 < lam ∧ BlockGapBddW T B₁ lam          -- lam = min(lam₂/(4s), m)

theorem ProofPhase.V4.blockGapBddW_of_levelDprimeWOn ... (hD : LevelDprimeWOn (fun k j => (blockedLaw T B₁ k j).map (B₂ k j)) lam₂)
    (hX : StageTwoW (blockedLaw T B₁) B₂ s) : ∃ lam, 0 < lam ∧ BlockGapBddW T B₁ lam
```

So "v3 input set at L₁, stated for the L_* theory" = v3's D′ in W₁ form for the L₁ laws (`LevelDprimeWOn`, literally v3's
`LevelDprimeW` with the blocked law replaced by `(ν k j).map B₂`) plus `StageTwoW` (v3's (a), (b), (c) for the step
L_* → L₁ with the fine field replaced by the L_* block field, time separation dropped, extent index replaced by the
prefactor `(1 + Σvf)(1 + Lg)`). Proof: `Effective.cov_map` (Wilson block covariance = covariance under `ν`),
`RouteA.cov_transfer` on `ν` with `Φ = B₂`, `cov_map` again (covariance of the L₁ law), the L₁ input, and `poly_exp_le`
for `(1 + R)⁴`.

**`twoStage_blocked`.** For a block observable `F = f ∘ B₁` stage 1 is exact (`E[f ∘ B₁ | B₁] = f ∘ B₁`, zero defect),
so the two-stage split degenerates and only the covariance transfer on the L_* law remains; it is done directly.
`twoStage_blocked` remains the composition lemma in the *transfer* direction (v4's UV2 at L_* plus stage 2 give v3's
transfer at L₁), which v4's top does not need.

**Wired in:** `yang_mills_assembly_v4_strategyA` (S): `OnLCP' ∧ NonTrivial ∧ LevelDprimeWOn(L₁ laws) ∧ StageTwoW ∧
ObsTransferPhysTW T B₁ ⇒ OpenInputsV4 ∧ conclusion`. Cycles 2 to 4 are thus a proved strategy (a) for IR.

**Named limitations.**
* *Volumes.* `B₂ k j` must exist for **every** volume `j`. A uniform `2^r` blocking of the L_* torus of side `2(j+1)` exists
  only when `2^r | 2(j+1)`; for the others one needs cells of two sizes (`2^r` and `2^r + 1`) or another `B₂`. The lemma
  takes any measurable `B₂`; constructing one for all `j` is open (bookkeeping). Controlling only a subsequence of volumes
  would not do: `MassGapLoc` speaks about every limit point in the volume.
* `LevelDprimeWOn` keeps v3's finite range `D₁` and the Gibbs representation of the L₁ law (review 1.1, 1.3); c5c's
  weighted W₁ Theorem A and noisy blocking remove them. The lemma itself only needs `LawGapBddW` of the L₁ laws, so any
  better Dobrushin theorem plugs in through it.
* No `CondMassAnn`-type sufficient condition for part (c) of `StageTwoW` is stated; v3's `condDecouple_of_condMassAnn` is
  generic and transfers verbatim (one line, `|∫ f| ≤ ∫ |f|`).

---

## 4. Seg1 and the retired pieces (`V4/UV.lean`, `V4/Top.lean`)

* `UV1Polymer T B λ' M_E := Seg1.PolymerRepW coarseSide (blockedLaw T B) λ' M_E` (UV1 in c4b's vacancy-1 form, on the L_*
  laws of the top theorem) and `gibbsRep_of_uv1Polymer` (S, `Seg1.envelopeW_seg1`): local Gibbs representation with bounded
  potentials and one `EnvelopeW` for all levels and volumes.
* **Where Seg1 belongs, honestly.** It feeds UV, not IR, and in Lean it feeds nothing yet: the top theorem takes UV in its
  final form `ObsTransferPhysTW`, and no Lean theorem derives that from a Gibbs representation. UV1 is the supplier of the
  L_* theory, used on paper by the proof of UV2 (conditional mixing, c4a 2.2) and by every IR strategy stated for the L_*
  laws (`StageTwoW`, strategy (b) on cells). It is deliberately **not** a hypothesis of the top theorem (an unused
  hypothesis would be decoration). The draft's UV1 is the defect form (c5d).
* Not in the v4 top statement (files kept): route B (`ConjW ∧ SectorTransfer`), the sup family (`LevelDprime`,
  `LimitDprime`, `H1Local`, `ObsTransferPhysT`, `EnvelopeW`, `NearStable`), `H1LocalLipW ∧ LimitDprimeW` (now only inside
  strategy (a), through `LevelDprimeW`), the `_dec`/`_smoother`/`_condMass` variants.

---

## 5. Claim check: one gap-strength input (mandatory table)

"Gap" column as in the draft: **G** = gap strength or stronger; **N** = non-perturbative but should hold for the photon;
**P** = perturbative in kind; **B** = bookkeeping/data. "Decay in disguise?" asks whether the input is a decay statement for
observables of the Wilson measure.

### Hypotheses of the v4 top theorem

| input | layer | gap | decay in disguise? why |
|---|---|---|---|
| `OnLCP'.resolution` (`ℓ_k → ∞`) | ID | B | no; data of the tuning |
| `OnLCP'.running` (`β_k / log ℓ_k → 11/(6π²)`) | ID | P | no; bare coupling only |
| `OnLCP'.scheme` (`z_lo ≤ ℓ_k · fluxRate h ≤ z_hi`) | ID | P/N | **formally yes, in substance no**: `fluxRate` is the time-decay rate of the centre-odd Polyakov correlation, but on a fixed **finite spatial box** of side L_*. Positive flux energy in a finite box holds for the free photon (`E_n = g² n² L_z/(2L_xL_y)`, r4-conjw) and for gapless theories; it says nothing about infinite volume. At L_* it is a tunnelling quantity (semiclassical, not perturbative; see 2) |
| `NonTrivial` | ID | P | no; a **lower** bound on a correlation (anti-decay) |
| `B : BlockingFamily T` | data | B | no; a reflection-respecting map (deterministic: review 1.3) |
| `ObsTransferPhysTW T B` (a), (b) | UV | P | no; L¹ quasi-locality of `E[F | Φ_*]`, no covariance |
| `ObsTransferPhysTW T B` (c) | UV | P at L_* | no on its own: a conditional covariance given the L_* block field; the Gaussian photon satisfies it in time (c3a). By difficulty conservation (`UV.condDefect_eq`), **given IR**, (c) is equivalent to fine decay; that is the reduction, not a hidden gap |
| **`BlockGapUnifW T B λ`** (or **`BlockGapBddW`**) | IR | **G** | **yes, openly**: decay of block-observable covariances of the Wilson measure, uniform in level and volume. The one gap-strength input; the photon fails it (power law at L_*) |

No other hypothesis of the top theorem is a decay statement for observables of the Wilson measure in infinite volume.

### Strategy (a) for IR (not hypotheses of the top theorem)

| input | layer | gap | why |
|---|---|---|---|
| `LevelDprimeWOn` of the L₁ laws (v3's `LevelDprimeW`) | IR at L₁ | G/N | worst-case uniqueness of the L₁ theory; confinement-type; fails for the photon and below 1/T_c; the cheap half at L₁ ≈ 2.8/√σ (review 2.2) |
| `StageTwoW` (a), (b) | IR, L_* → L₁ | N | quasi-locality of `E[f | B₂]` at order-one coupling |
| `StageTwoW` (c) | IR, L_* → L₁ | **G** at L₁ ≈ 2.8/√σ | Lemma X; given the L₁ side, equivalent to the L_* block decay (difficulty conservation); at this L₁ the block field is near noise, so it is the glueball gap (review 2.2) |
| `UV1Polymer` | UV supplier | P | not an input of the top theorem |

### Unit tests of the v4 inputs

Photon: ID and UV can hold, IR fails (power law). Z₂ at weak coupling: IR holds and implies no area law (block torus decay
is gap-type). Deconfinement: IR is a statement on symmetric tori; on the small tori it is trivially true with a
`j`-dependent constant and uniformity bites only in large volume; no claim about boxes one block thick. Banks–Zaks: IR
fails. Triviality: no existence claim. Pure noise: fails `OnLCP'.running` (`not_trivial_v4`).

---

## 6. Changes proposed to the draft blueprint v4

1. §2 top theorem: built as drafted. Add the bounded form `BlockGapBddW` as the IR statement of record (weaker, all that is
   consumed, where the recursion lemma lands); keep `BlockGapUnifW` as its homogeneous sufficient condition.
2. §2 recursion lemma: replace by `blockGapBddW_of_stageTwo` with `StageTwoW` (prefactor form, any support) and the named
   volume limitation; drop "twoStage_blocked" from its proof description (stage 1 is exact for block observables).
3. §3.1 `OnLCP'`: the Lean form above (two-sided flux act number of the L_* box), with the caveat that at L_* this is
   tunnelling-sized; recommend switching the scheme observable to a perturbative coupling of the L_* box once UV1 defines
   it. Mark `OnLCP.scheme` "used by route B only, and there only as a lower bound".
4. §3.2: UV1 is consumed by no Lean theorem; it is the supplier of the L_* theory for UV2 and for strategies (a), (b).
5. §3.3 strategy (a): "Lean for the implications" is now true at L_* (`yang_mills_assembly_v4_strategyA`), with inputs
   `LevelDprimeWOn` (L₁ laws) and `StageTwoW`.
6. §4: add `OnLCP'.scheme` to the claim table as "decay in a finite box, photon passes, not gap strength".

## 7. Next step

The volume bookkeeping of strategy (a) (a `B₂` with two cell sizes for every `j`), then wire c5c's noisy `BlockingFamily`
and weighted W₁ Theorem A in through `LawGapBddW` (the recursion lemma needs only that), and state strategy (b)
(`CellDobrushin` for the unconditioned L_* law `⇒ LawGapBddW (blockedLaw T B)`, plan step 8) against the same interface.
