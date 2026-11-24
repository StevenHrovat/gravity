# Cycle 3, workstream 1 (c3a-uv): `ObsTransferPhys` for the good blocking (2026-11-22)

Brief: prove `ObsTransferPhys T goodBlocking` (the ultraviolet quasi-locality of the blocked theory: (a) coarse approximants with a
level-uniform oscillation sum, (b) `E[F|Φ] ≈ f∘Φ` in `L¹`, (c) conditional decoupling `|E[FG] − E[E[F|Φ]E[G|Φ]]| ≤ c e^{-mD}`), or
reduce it to a precisely stated, smaller, clearly ultraviolet lemma; decide whether (c) needs more than weak-coupling control inside
blocks of size `L₁`, and where `b₀ > 0` and large fields enter.

Claim levels as in `../../attempts/RULES.md`: **Lean**, **Lean (definitional)**, **paper**, **heuristic**, **numerical**
(pre-registered or marked exploratory). Lean: `../../../formal/ProofPhase/UV/Split.lean` (new, the only Lean file), built in
`~/formal-c3a` (Lean 4.34.0, Mathlib v4.34.0); `axioms.sh` prints 15 headline theorems, all `propext, Classical.choice, Quot.sound`;
no `sorry`, no `native_decide`, no new axioms (`axioms.log`). Numerics: `PREREG.md` (written before any run), `condphoton.py`,
`check.log` (Bloch vs dense brute force), `primary.log`/`primary.json` (the pre-registered run), `explore*.py`, `explore*.log`
(exploratory, after the registered run). CPU only, one process at a time.

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3a-uv/setup.sh
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3a-uv/build.sh ProofPhase.UV.Split
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3a-uv/axioms.sh
py condphoton.py check ; py condphoton.py run 8 2,4,8 0,0.5,1 --out primary.json
```

---

## 0. Results at a glance

1. **`ObsTransferPhys` is not proved.** What is proved (Lean) is where its content sits. **Difficulty conservation**
   (`condDefect_eq`): the quantity of (c) is `Cov(F,G) − Cov(E[F|Φ], E[G|Φ])`. Given (b), it equals the fine covariance minus the
   coarse covariance of the approximants up to `4ε` (`abs_condDefect_sub_cov_sub_le`); so once `LimitDprime` makes the coarse side
   decay, (c) is **equivalent** to the decay of the fine covariance (the other direction is `RouteA.cov_transfer`). (c) helps the
   route only if some mechanism makes it small directly. The mechanism available is the **constraint mechanism**: the block field
   pins the slow modes, so the conditional fine field is massive at the block scale, whatever the infrared behaviour.
2. **The noise-limit trap in reverse, exactly (Lean):** `|(c) − Cov(F,G)| ≤ ‖E[F|Φ] − E F‖₁`, the block field's information about
   `F` (`abs_condDefect_sub_cov_le`); with independence, `(c) = Cov(F,G)` (`condDefect_eq_cov_of_indep`). Decimation has a
   pure-noise limit (its information about every bounded-extent `F` tends to 0), so for decimation `ObsTransferPhys` **is** the gap
   (`TorusDecayLoc`) up to `o(1)`. The constraint argument fails there at one named step: the cost of hiding a slow mode from the
   block variable is `|Q(slow)|²/Var(Q) → 0` because `Var(Q)` grows linearly with `ℓ` (self-energy).
3. **Two-stage split (Lean):** for a composite blocking `fine → L₀ → L₁`, the estimates (b), (c) of the composite follow from those of
   the first stage on the Wilson measure plus those of the second stage **on the `L₀`-blocked law**, errors `ε₁+ε₂`, `δ₁+δ₂+4ε₁`
   (`twoStage`, `condDefect_tower`, `condExp_comp_map`, YM instance `twoStage_blocked`). This reduces `ObsTransferPhys T goodBlocking`
   to **Lemma UV** (§2.1: weak-coupling stage up to a scale `L₀` where the running coupling is small; clearly ultraviolet; uses
   `b₀ > 0` and Balaban-type large-field control) and **Lemma X** (§2.2: the `L₀ → L₁` stage on a fixed-resolution lattice theory).
4. **Verdict on the brief's question: (c) needs more than ultraviolet control at the `L₁` where `LimitDprime` can hold.** At an `L₁`
   in the weak-coupling regime, `ObsTransferPhys` *is* Lemma UV (no stage 2), but `LimitDprime` is false there (deconfinement test). At
   `L₁√σ ≈ 2.5–3`, where the centre and adjoint halves can hold, Lemma X spans the whole crossover (couplings from `g⋆` to `O(1)`)
   and is non-perturbative. The gap content is conserved: moving `L₁` trades it between `LimitDprime` and Lemma X; it does not
   disappear into the UV. `ObsTransferPhys` stays free of confinement input (it holds for the photon, §3).
5. **Photon test, Gaussian computation (numerical, pre-registered; checked against a dense brute force to 10 digits):** for the
   linearised good blocking the conditional photon is **massive in the time direction, uniformly in the resolution**: conditional
   correlation of block-averaged `F₁₂` at `D = 3 L₁` is `~5·10⁻⁷` of its variance (`ℓ = 4, 8`, `w = 0.5, 1`), decay rate
   `≈ 4.5/L₁`, while decimation's conditional/unconditional ratio rises with `ℓ` (0.10, 0.40, 0.55 at `D = 3`) and its content falls
   (0.22, 0.09, 0.03): both directions of the trap confirmed. **New, and a defect:** in spatial directions the staple kernel at
   `w = 0.5, 1` has a near-blind (at `w = 1/2` exactly blind) **spatial checkerboard mode** at the coarse zone corner, and the
   conditional correlation decays slowly with alternating sign (pre-registered G1/G2 fail in space). A small staple weight
   (`w = 0.1`, exploratory) removes the stagger but drifts towards decimation (`R(3)` 0.03 → 0.11, content falling, `ℓ = 4 → 8`):
   none of the tested weights is good in both respects; the kernel needs redesign for spatial quasi-locality.
6. **What the assembly needs is the time direction only:** `Torus.torusDecayLoc_of_blockedRoute` applies `ObsTransferPhys` only to
   the time-separated pair `F∘S_n`, `F∘Θ`. Proposed: a time-separated form `ObsTransferPhysT` (paper, §7), for which the Gaussian
   test passes uniformly in `ℓ` for `w = 0.5, 1`.
7. **Clicks (§4):** (c) in the time direction is **smoother stability of a hidden Markov model** (the transfer-matrix chain observed
   through the block variables); stability comes either from ergodicity of the signal (the gap: circular) or from uniform
   **observability** (the constraint mechanism); the noise-limit trap is loss of observability; the photon is a Kalman filter for an
   unstable but observable signal. And: keep the annealed (`L¹`) form, which is what makes large fields manageable.

## 1. What (c) is (Lean, generic)

`condDefect μ m F G := ∫FG − ∫E[F|m]E[G|m] = E[Cov(F,G | m)]` (part (c) of `ObsTransferPhys`, with `m = σ(Φ)`).

* `condDefect_eq` (**D**, the identity that organises everything): `condDefect m F G = Cov(F,G) − Cov(E[F|m], E[G|m])`.
* `abs_condDefect_sub_cov_sub_le` (**S**, small): with approximants `‖E[F|m] − f‖₁, ‖E[G|m] − g‖₁ ≤ ε`, `|f|,|g| ≤ 1`:
  `|condDefect − (Cov(F,G) − Cov(f,g))| ≤ 4ε`. With `LimitDprime` giving `|Cov(f∘Φ, g∘Φ)| ≤ C e^{-λR}`, (c) holds iff the fine
  covariance decays. So `ObsTransferPhys` is never weaker than the conclusion of the route; it is a reformulation that pays off only
  if (c) can be proved by a mechanism other than fine decay.
* `abs_cov_condExp_le`, `abs_condDefect_sub_cov_le` (**S**, small): `|Cov(E[F|m], E[G|m])| ≤ ‖E[F|m] − E F‖₁` and hence
  `|condDefect − Cov(F,G)| ≤ ‖E[F|m] − E F‖₁`. `condDefect_eq_cov_of_indep` (**D**): if `σ(F)` and `m` are independent, (c) is the
  fine covariance.

**Decimation (`w = 0`), why it fails, precisely.** Round 4 and `ws1-routeA` §2: the decimated coarse link has one-loop self-energy
growing like `g²ℓ`, so its law tends to Haar (pure noise), and (power counting, the same suppression on every connected
correlator containing a thin line) `‖E[F|Φ] − E F‖₁ → 0` for every bounded-extent `F`. By `abs_condDefect_sub_cov_le`, (c) for
`k ≥ k₀` with fixed `c, m` then reads `|Cov(F,G)| ≤ c e^{-mD} + o(1)`: `TorusDecayLoc` itself. Any proof of (c) must therefore use
the **content** of the block variable. In the Gaussian picture the conditional covariance is `Γ = C − CQ*(QCQ*)⁺QC`; a slow mode
`φ` can be made invisible to `Q` by adding a short-wavelength correction of energy `≈ |Qφ|²/Var(Q)`, and `Var(Q) ∝ ℓ` for
decimation (linear self-energy) while it stays bounded for the smeared blocking. So the coercivity ("Poincaré on `ker Q`") step that
gives the conditional field a mass `~1/L₁` holds for the good blocking and fails for decimation as `ℓ → ∞`. Numerically (§3): for
decimation the conditional/unconditional ratio at `D = 3L₁` rises 0.10 → 0.40 → 0.55 (`ℓ = 2, 4, 8`) and the explained fraction of
the variance falls 0.22 → 0.09 → 0.03.

**The other end of the trap.** A blocking that keeps everything (`Φ` injective) makes (c) zero and puts the whole gap into the
coarse theory; one that keeps nothing makes (c) the whole gap. `condDefect_eq` is the exact bookkeeping between the two ends.

## 2. The two-stage split and the remaining lemmas

**Lean (generic):** `condDefect_tower` (`𝒢 ≤ ℋ`: `(c)_𝒢(F,G) = (c)_ℋ(F,G) + (c)_𝒢(E[F|ℋ], E[G|ℋ])`), `abs_condDefect_sub_le`
(2-Lipschitz in `L¹`), `approx_tower` (`‖E[F|𝒢] − f₂‖₁ ≤ ‖E[F|ℋ] − f₁‖₁ + ‖E[f₁|𝒢] − f₂‖₁`), **`twoStage`** (stage-1 errors
`ε₁, δ₁`, stage-2 errors for the stage-1 approximants `ε₂, δ₂` ⇒ composite errors `ε₁+ε₂`, `δ₁+δ₂+4ε₁`), `condExp_comp_map`
(`μ[h∘B₁ | σ(B₂∘B₁)] = (B₁μ)[h | σ(B₂)]∘B₁` a.e.), `condDefect_map`, `approx_map`.
**Lean (Yang–Mills):** **`twoStage_blocked`**: for the SU(2) Wilson measure `T.ym k j` and reflection-respecting blockings
`B₁ : fine → intermediate`, `B₂ : intermediate → coarse`, the (b) and (c) estimates of `B₁.comp B₂` **in the syntactic form of
`ObsTransferPhys`** follow from (UV) the estimates for `B₁` on `T.ym k j` and (X) the estimates for the stage-1 approximants and `B₂`
on the intermediate law `(T.ym k j).map B₁`. The good blocking is an `n_k`-fold iterate of one smeared step, so it is such a
composite at every level (`n_k − r` steps, then `r`); the re-association across `smearIter`'s casts is elementary and not formalised.
The quantifier bookkeeping (supports, margins) is paper, below.

### 2.1 Lemma UV (open; ultraviolet; this is the "smaller, clearly ultraviolet lemma")

Fix the good blocking with weight `w > 0`, a dyadic tuning on the line of constant physics, and `L₀ = L₁/2^r`. Let `Φ₁` be the first
`n_k − r` smeared steps (fine torus → intermediate torus, cells of physical size `L₀`).

> **Lemma UV(`L₀`).** There are `β⋆ < ∞` and `m₀ > 0` such that, if the running coupling at scale `L₀` satisfies `β(L₀) ≥ β⋆`
> (weak coupling at `L₀`), then for every `R` there are `c` and `k₀` with: for all `k ≥ k₀`, volumes `j`, fine observables `F, G`
> (measurable, gauge invariant, `|·| ≤ 1`, physical extent `≤ R`, physical distance `≥ D`) there are intermediate observables
> `f₁, g₁` (`|·| ≤ 1`, measurable, depending only on intermediate links within physical distance `D/8` of the supports of `F`, `G`)
> with `‖E[F|Φ₁] − f₁∘Φ₁‖₁ ≤ c e^{-m₀D}`, the same for `G`, and `|condDefect_{σ(Φ₁)}(F, G)| ≤ c e^{-m₀D}` (all under `T.ym k j`).
> Expected rate `m₀ ~ 1/L₀`.

Why it is ultraviolet and what it needs (paper/heuristic, following Balaban's programme as read in `READING.md` §2):
* **Small fields.** Given the `L₀` block field, the fine field is a sum of fluctuation fields at the scales `2^i a_k`
  (`i < n_k − r`), each Gaussian to leading order with a covariance that decays like `e^{-c|x−y|/(2^i a_k)}` (the constraint
  mechanism at every scale; Balaban's `Γ_k` operators), plus polymer corrections of size `O(g_i)`. A contribution of scale `i` to
  (c) at distance `D` is `≲ e^{-cD/(2^i a_k)}`; summed over scales it is `≲ e^{-cD/L₀}`, uniformly in the number of scales.
* **Where `b₀ > 0` enters.** The expansion needs `g_i := g(2^i a_k) ≤ g⋆` at **every** scale and for **every** level `k`. Asymptotic
  freedom makes `g` increase monotonically towards the infrared, and the line of constant physics fixes `g(L₀)` independently of `k`;
  so `sup_i g_i = g(L₀) ≤ g⋆` uniformly. Without `b₀ > 0` there is no level-uniform small parameter as `a_k → 0`.
* **Where large fields enter.** Balaban's large-field regions (fine field far from the background at some scale) occur with
  probability `≤ e^{-p(g⋆)}` per block, `p(g) → ∞` as `g → 0` (CMP 122). Because `ObsTransferPhys` is in **annealed `L¹` form**
  (averaged over the block field), a large-field region spoils (b), (c) only locally; a failure at distance `D` needs a chain of
  large-field blocks from one support to the other, probability `≤ (C e^{-p})^{D/L₀}`. The quenched form (for every block
  configuration) would fail: rough block fields occur, and the conditional law given one is a strongly constrained system.
  **Recommendation: keep the annealed form.**
* **What is missing from the literature.** Balaban's published bounds control effective actions and the partition function
  (ultraviolet stability), not conditional correlation functions; Lemma UV needs the cluster expansion to carry two observables
  (done for abelian Higgs cluster properties by Balaban–Imbrie–Jaffe; not for non-abelian gauge fields). Gaussian level: §3.

### 2.2 Lemma X (open; the crossover stage)

> **Lemma X(`L₀ → L₁`).** For the intermediate laws `ν_{k,j} = (T.ym k j).map Φ₁` (a lattice theory with `2^r` intermediate links
> per `L₁` and quasi-local effective action converging as `k → ∞`), the last `r` smeared steps `Φ₂`, and intermediate observables
> `f₁, g₁` (`|·| ≤ 1`) supported within `D/8` of sets of physical extent `≤ R` at physical distance `≥ D`: there are coarse `f, g`
> with oscillation sum `≤ 2K(1 + D/L₁)⁴`, supports at physical distance `≥ D/2`, `‖E_ν[f₁|Φ₂] − f∘Φ₂‖₁ ≤ c e^{-mD}`, the same for
> `g₁`, and `|condDefect_{ν, σ(Φ₂)}(f₁, g₁)| ≤ c e^{-mD}`, uniformly in `k ≥ k₀` and `j`.

**Theorem (Lean per instance, `twoStage_blocked`; bookkeeping paper).** Lemma UV(`L₀`) ∧ Lemma X(`L₀ → L₁`) ⇒
`ObsTransferPhys T (goodBlocking …)` with rate `min(m₀, m)` (margins: `D/8 + D/8` keeps the supports at distance `≥ D/2`; extents
`R + D/4` are absorbed in `K(1 + D/L₁)⁴`).

**Why Lemma X is not ultraviolet.** It is (b), (c) for a theory whose couplings run from `g⋆` (at `L₀`) to `g(L₁)`. At the `L₁` the
route needs (`L₁√σ ≈ 2.5–3`, where the halves of `LimitDprime` can hold; `1/T_c ≈ 1.45/√σ`) the top scales are strongly coupled, so
there is no small parameter for the constraint mechanism; and by §1 Lemma X differs from the `L₀` theory's own decay by at most the
information of the `L₁` block variable about `f₁`. Leg C (c2a §5.1) found a deterministic `L₁` variable near Haar noise in the
adjoint channel at `L√σ ≥ 3.15`: for such a variable Lemma X is the gap of the `L₀` theory. The decisive quantity for Lemma X is
therefore the **content** of the `L₁` block variable (c3b's refit with the good blocking and a content check measures exactly this).

**The trade-off, stated once.** Choose `L₁` small (weak coupling): `ObsTransferPhys` = Lemma UV, but `LimitDprime` fails (it would
give Polyakov decay on one-block-thick tori). Choose `L₁` large: `LimitDprime` can hold, but `ObsTransferPhys` contains Lemma X.
The crossover is shared between `LimitDprime` and Lemma X at the same `L₁`; it is not removed.

## 3. The photon at Gaussian level (numerical)

**Set-up (`PREREG.md`).** Linearised abelian field on `(ℤ/Mℓ)⁴`, covariance `δ/p̂²`; the linearised good blocking (`n = log₂ℓ` steps,
staple weight `w`, normalised by `1 + w·#staples`; `w = 0` decimation); conditioning on all coarse plaquette fluxes and the coarse
zero-momentum sums; observable `X` = `F₁₂` averaged over a hypercube of side `L₁/2` (corner of the cell, or centred, i.e. between
the coarse time slices); partner translated by `D` cells in time or space. Exact Gaussian conditioning by Bloch decomposition over
coarse momenta; **checked against a dense brute force** (independent real-space path construction, 1540 constraints, 16384 field
variables) at `(M, ℓ) = (4, 2), (2, 4)`: agreement to `10⁻¹⁰` (`check.log`). Primary run `M = 8`, `ℓ = 2, 4, 8`, `w = 0, 0.5, 1`
(`primary.log`); the secondary run (`ℓ = 16`) was skipped as pre-registered, the primary taking over 5 minutes.

**Conditional correlation `Γ(D)/Γ(0)` (time direction) and the conditional/unconditional ratio `R(D)`:**

| `w`, placement | `ℓ` | `Γ/Γ₀` at `D = 1, 2, 3` | `R(3)` | content `κ` |
|---|---|---|---|---|
| 0 (decimation), corner | 2, 4, 8 | 2.7e-2, 1.3e-3, 2.5e-5 · 1.4e-2, 7.7e-4, 7.2e-5 · 1.2e-2, 6.5e-4, 9.2e-5 | 0.10, 0.40, 0.55 | 0.22, 0.09, 0.03 |
| 0.5, corner | 2, 4, 8 | 1.8e-2, 4.2e-4, 1.1e-5 · 8.8e-3, 1.1e-4, 7.5e-7 · 6.8e-3, 8.6e-5, 4.7e-7 | 0.05, 0.004, 0.003 | 0.12, 0.06, 0.04 |
| 0.5, centre | 4, 8 | 7.1e-3, 4.6e-5, 5.9e-7 · 5.1e-3, 3.0e-5, 3.8e-7 | 0.004, 0.002 | 0.018, 0.015 |
| 1, corner | 4, 8 | 9.2e-3, 1.2e-4, 2.5e-6 · 7.0e-3, 8.2e-5, 1.4e-6 | 0.014, 0.008 | 0.049, 0.037 |

(The unconditional `C(D)/C(0)` converges in `ℓ`: `1.3e-2, 7.9e-4, 1.6e-4` at `ℓ = 8`, a power law.) The smeared blocking's
conditional field decays at `≈ 4.5` per `L₁` in time, with the same profile at `ℓ = 4` and `8`; decimation's conditioning becomes
uninformative as `ℓ` grows.

**Spatial direction: the checkerboard defect.** For `w = 0.5` and `1` the spatial conditional correlation alternates in sign and
decays slowly (`ℓ = 8`, centre: `Γ/Γ₀ = 6.0e-3, 7.3e-4, −2.5e-4, 1.6e-4` at `D = 1…4`; `R(4) ≈ 2`, larger than unconditional).
Exploratory diagnosis (`explore.log`): the rank-3 (gauge-invariant) part of the coarse flux covariance `K(q)` has its minimum at the
spatial zone corner `q_s = (π, π, π)`, any `q₀`: `0.08` (`ℓ = 2`, `w = 1`) and `0.05` (`ℓ = 4`) against `1.1–1.4` for decimation; at
`w = 1/2` the single-step symbol loses rank exactly at `k = (π/2)⁴` (singular values `1.55, 0.32, 0, 0`), `K` drops from rank 3 to
rank 1 at the corner, and the conditional spectral weight is **discontinuous** there (limits `−0.125`, `−0.167`, `−0.25`, `0`
depending on the direction of approach): a power-law, alternating spatial tail. The singular set is a line in `q₀`, i.e. local in
time: the time direction is unaffected, as observed. The cause is the staple kernel, whose transverse factor `1 + 2wΣcos k_ν` and
off-diagonal staple terms nearly cancel the coarse field's response to a spatial checkerboard of wavelength `2L₁`. Exploratory
remedy tried: `w = 0.1` gives isotropic, non-alternating decay (`explore_w.log`, `explore_w8.log`), but it drifts towards
decimation: `R(3)` in time 0.034 → 0.114 (corner) and 0.044 → 0.082 (centre) from `ℓ = 4` to `8`, content `κ` (centre) 0.0094 →
0.0065. So the staple family offers a trade-off, not a fix: large `w` keeps the content and is blind to the spatial checkerboard,
small `w` sees the checkerboard and loses content like decimation. A kernel with a positive symbol on the whole coarse zone (for
example a heat-kernel-type transverse smearing of fixed physical radius) is the natural candidate; not tested.

**Pre-registered verdicts.** G1 (massive, `|R(4)| < |R(2)|`, `|R(4)| ≤ 0.3`): **holds in time, fails in space** (`w = 0.5, 1`).
G2 (uniform in `ℓ`, `|R(3)|` stable within 0.1 from `ℓ = 4` to `8`): **holds in time** (0.004 → 0.003; 0.014 → 0.008), **fails in
space** (corner `w = 0.5`: 3.0 → 0.06). G3 (content kept, `κ(8) ≥ ½κ(4)` at `w = 0.5`): **holds** (0.063 → 0.042; 0.018 → 0.015).
D1 (decimation loses it): **holds** (`R(3)` 0.10 → 0.40 → 0.55, exceeding the `w = 0.5` value by 0.55; `κ` 0.22 → 0.09 → 0.03).

**What this says.** The ultraviolet half of `ObsTransferPhys` (the constraint mechanism) works at Gaussian level in the time
direction, uniformly in the resolution, for the good blocking, and fails for decimation, as §1 predicts. The spatial defect is a
property of the specific staple kernel, not of the mechanism; it matters for the spatial summability in (a), not for the
time-separated pairs the assembly uses (§0.6). This is the photon unit test: `ObsTransferPhys` (time form) **holds for the free
photon**, as it should for a statement with no confinement input; the photon still has no gap because `LimitDprime` fails for it.

## 4. Clicks

* **(c) is filter stability (lead, heuristic; literature recalled, not re-verified).** The fine theory is a Markov chain in time
  (transfer matrix; the state is the slice field); the good blocking's block variables are local in time (one coarse time step
  depends on one time strip). Conditioning on them is smoothing in a hidden Markov model, and (c) for time-separated pairs is the
  mixing of the conditioned chain. HMM theory: the filter/smoother is stable if the signal is ergodic (here: the gap; circular) **or**
  under uniform observability (van Handel, Ann. Appl. Probab. 19 (2009) 1172, "uniform observability … filter stability for unstable
  signals"); for linear Gaussian models, detectability makes the Kalman filter exponentially stable even for unstable signals. Here:
  the photon is an unstable (massless) but observable signal, hence §3's time decay; decimation is unobservable in the limit; the
  noise-limit trap is **loss of observability**. For spatially extended signals the conditional law is a space-time Gibbs measure
  that can have phase transitions (Rebeschini–van Handel, "Phase transitions in nonlinear filtering", EJP 2015, recalled): (c) is a
  genuine uniqueness question for the conditional field, and Lemma X is "uniform observability at the crossover".
* **Same thing seen twice: the information bound.** `abs_condDefect_sub_cov_le` is the mutual-information form of the noise-limit
  trap of c2a §5 and of round 4's "pure noise satisfies every decay statement": the gap is split between `LimitDprime` (coarse
  covariance) and (c) in proportion to how much the block variable explains (`condDefect_eq`).
* **Route A′ (proposal, paper).** Block only to `L₀` (Lemma UV and `H1Local` at `L₀`, both ultraviolet), and replace `LimitDprime` at
  `L₁` by a Dobrushin-type condition on the `L₀` limit theory with **super-sites** (all `L₀` links of an `L₁` cell). No information is
  lost, so the noise-limit trap and Lemma X disappear, and the crossover sits in one IR condition on a fixed lattice theory. Caveat:
  in plain total-variation form a super-site condition fails (neighbouring cells interact through boundary plaquettes at the large
  `β(L₀)`, so the whole cell's law is boundary-sensitive); it needs a Dobrushin–Shlosman finite-volume form (influence on cell
  interiors) or a `W₁` form with a depth-weighted metric. Not formalised; `torusDecayLoc_of_blockedRoute` would need super-site
  coarse spaces.
* **Lemma T and robustness.** Relative closeness (`Quantum/LemmaT.lean`) is the right closeness for conditional statements (density
  ratios pass to conditional laws), but volume-uniformity needs locality; Lemma X's level-uniformity should therefore come from a
  robust (open-condition) proof, e.g. a Dobrushin condition for a soft (noisy) version of the `L₀ → L₁` step, not from a bare decay
  statement about the limit theory.

## 5. Headline theorems (`formal/ProofPhase/UV/Split.lean`)

| Lean | exact statement | mark | Yang–Mills in hypotheses |
|---|---|---|---|
| `condDefect_eq` | `m ≤ m₀ →` `condDefect μ m F G = cov μ F G − cov μ (μ[F|m]) (μ[G|m])` | D | no |
| `abs_condDefect_le` | `|condDefect| ≤ |cov F G| + |cov (μ[F|m]) (μ[G|m])|` | D | no |
| `abs_cov_condExp_le` | `Bdd1 F, Bdd1 G →` `|cov (μ[F|m]) (μ[G|m])| ≤ ∫|μ[F|m] − ∫F|` | S (small) | no |
| `abs_condDefect_sub_cov_le` | `|condDefect m F G − cov F G| ≤ ∫|μ[F|m] − ∫F|` (trap in reverse) | S (small) | no |
| `abs_condDefect_sub_cov_sub_le` | approximants within `ε` ⇒ `|condDefect − (cov F G − cov f g)| ≤ 4ε` | S (small) | no |
| `condDefect_eq_cov_of_indep` | `σ(F) ⫫ m ⇒ condDefect m F G = cov F G` | D | no |
| `condDefect_tower` | `𝒢 ≤ ℋ ≤ m₀ ⇒ condDefect 𝒢 F G = condDefect ℋ F G + condDefect 𝒢 (μ[F|ℋ]) (μ[G|ℋ])` | D | no |
| `integral_abs_condExp_sub_le`, `abs_condDefect_sub_le`, `approx_tower` | `L¹` contraction; 2-Lipschitz defect; approximants through the tower | S (standard) | no |
| `twoStage` | stage errors `(ε₁, δ₁)`, `(ε₂, δ₂)` ⇒ `ε₁+ε₂`, `ε₁+ε₂`, `δ₁+δ₂+4ε₁` | S (reduction) | no |
| `condExp_comp_map`, `condDefect_map`, `approx_map` | conditional expectations through `B₂∘B₁` computed on the image law `B₁μ` | S (measure theory) | no |
| `twoStage_blocked` | for `T.ym k j`, `B₁ : RPBlocking (side k j) K`, `B₂ : RPBlocking K (coarseSide j)`: (UV on `T.ym k j`) ∧ (X on `(T.ym k j).map B₁`) ⇒ the (b), (c) estimates of `B₁.comp B₂` in `ObsTransferPhys` form | S (reduction) | the SU(2) Wilson measure, reflection-respecting blockings; group-blind proof |

`Bdd1 μ F` := a.e. strongly measurable and `|F| ≤ 1` a.e. No theorem here estimates (c) for an interacting theory; none
distinguishes SU(2) from U(1) or Z₂ (by design: the content is located, not supplied).

## 6. Unit tests

* **Photon.** `ObsTransferPhys` (time form) holds for the free photon at Gaussian level with the good blocking (§3), uniformly in
  `ℓ`; that is correct and carries no gap (`LimitDprime` fails for U(1)). Decimation fails it for the photon (§1, §3). Lemma UV for
  U(1) is the free-field computation; nothing in it gives a mass.
* **Z₂ (weak coupling).** Gap, no confinement. (c) is gap-type and expected to hold (small fluctuations, informative block
  variable); the theorems here imply no area law. Pass.
* **Deconfinement.** (c) is conditional: on a torus one block thick the ordered Polyakov sector is carried by the block field, not by
  the conditional field, so (c) can hold below `1/T_c`; the deconfinement test bites on `LimitDprime`, as before. Pass.
* **Mixture.** For a reflection-positive invariant mixture `½(μ₁+μ₂)`, `condDefect_eq` puts the non-decaying between-component
  covariance into `Cov(E[F|Φ], E[G|Φ])` when the block field identifies the component (large volume), so (c) can hold while the
  coarse side does not decay; `ObsTransferPhys` alone gives no decay. Pass.
* **Heller endpoint.** A massless `0⁺⁺` with string tension: if the massless mode is observable through the block field (as for the
  photon), (c) holds and the coarse theory is gapless; no gap follows. Pass.
* **Triviality.** No existence claim; for a Gaussian (trivial) limit (c) holds as for the photon. Pass.
* **Banks–Zaks / finite subgroups.** Gap-type, conditional statements, no unconditional claim. Pass.

## 7. Blueprint and assembly changes (proposed; `PROOF-BLUEPRINT.md`, `Assembly.lean` not edited)

* **P5.2 / `ObsTransferPhys`:** "open" → "open; reduced (Lean, `UV.twoStage_blocked`) to **Lemma UV** (ultraviolet: weak coupling up to
  `L₀`; needs `b₀ > 0` and Balaban-type large-field bounds, extended to conditional correlations; Gaussian level verified
  numerically in the time direction) and **Lemma X** (the `L₀ → L₁` crossover on a fixed-resolution theory; not ultraviolet at the
  `L₁` of `LimitDprime`). Difficulty conservation (Lean): given `LimitDprime`, (c) ⇔ fine decay; for decimation `ObsTransferPhys` =
  the gap."
* **P4.1′/P4.1″:** add: "the noise-limit trap is the information bound `|(c) − Cov| ≤ ‖E[F|Φ] − EF‖₁` (Lean); content of the `L₁`
  block variable decides how the crossover is split between `LimitDprime` and Lemma X".
* **P1.8 (good blocking):** add: "Gaussian test: the staple kernel at `w = 1/2` is exactly blind to the spatial checkerboard at the
  coarse zone corner (rank loss), near-blind at `w = 1`; `w = 0.1` sees it but drifts towards decimation (exploratory). Proposed design criterion: the
  gauge-invariant part of the linearised coarse flux covariance is bounded below on the whole coarse zone, uniformly in `ℓ`."
* **`Assembly.lean`, proposal 1 (`ObsTransferPhysT`):** the same as `ObsTransferPhys` with the extra hypothesis that `A₀` lies in a
  time slab `t ≤ t₁` and `B₀` in `t ≥ t₁ + D/a_k` (or the mirrored order). `torusDecayLoc_of_blockedRoute` uses `ObsTransferPhys` only
  for `F∘S_n` and `F∘Θ`, which are time-separated, so its proof goes through unchanged (paper; one application site, `Local.lean`
  around line 283). Weaker hypothesis, same conclusion, and the direction in which the Gaussian test passes (`w = 0.5, 1`).
* **Proposal 2 (Route A′):** a fourth crossover disjunct with `L₀`-blocking and a super-site IR condition (§4); needs a super-site
  version of the Dobrushin chain (`R3` machinery with a product single-site space) and a Dobrushin–Shlosman or depth-weighted `W₁`
  form.

## 8. Next step

1. **Blocking design (cheap, Gaussian):** find a reflection-respecting slice smearing whose linearised coarse flux covariance is
   bounded below on the whole coarse zone uniformly in `ℓ` (no spatial checkerboard blindness) while keeping the content (`w = 0.1`
   loses it, `w = 0.5, 1` are blind; a heat-kernel-type transverse smearing is the candidate). `condphoton.py` tests a candidate in
   minutes; c3b should know that the current staple kernel at `w = 0.5` is exactly blind to the spatial checkerboard at the coarse
   zone corner.
2. **Lemma UV at Gaussian level, proved:** the coercivity bound `⟨φ, −Δφ⟩ ≥ c L₁⁻² ‖φ‖²` on `ker Q` for the linearised good blocking
   (time-separated form), uniformly in `ℓ`, is a finite-dimensional symbol estimate per coarse momentum (the computation of §3 made
   rigorous with interval bounds on `K(q)`); it is the base case of Balaban's fluctuation covariance for this blocking.
3. **Lemma X:** formulate it for a soft (noisy) version of the last `r` steps, where the conditional `L₀` field has a proper Gibbs
   specification, and test a conditional Dobrushin condition on c3b's fitted `L₀` action; or pursue Route A′.

## References (ideas only; recalled unless marked)

Balaban, CMP 95–122 (1984–1989), in particular "Large field renormalization" I–II, CMP 122 (1989) (`READING.md` §2.1, verified there
at record level); Dimock, "The renormalization group according to Balaban" I–III (arXiv:1108.1335, 1212.5562, 1304.0705);
Balaban, Imbrie, Jaffe, CMP 114 (1988) 257; Gawedzki, Kupiainen (block-spin conditional covariances; recalled); van Handel,
Ann. Appl. Probab. 19 (2009) 1172 and Ann. Probab. 37 (2009) 1876 (filter stability, observability; recalled); Rebeschini, van
Handel, EJP 20 (2015) and J. Stat. Phys. 157 (2014) (conditional Gibbs measures in filtering; recalled); Dobrushin, Shlosman
(finite-volume criterion; `READING.md` §4.3). Project: `../ws1-routeA/NOTE.md` (good blocking, power counting), `../c2a-adjoint/NOTE.md`
§5 (noise-limit trap), `../c2c-torus/NOTE.md` (`ObsTransferPhys`), `../../PROOF-BLUEPRINT.md`.

## Coordinator addendum (2026-11-22): the refit's weight w = 2 at the coarse zone corner

c3b-refit (`../c3b-refit/PREREG.md`) uses the staple kernel at `w = 2`. `explore_rank.py` (exploratory, Gaussian, eigenvalues of
the coarse flux covariance at the corner `q = (π, π, π, π)`):

| w | ℓ | non-zero eigenvalues (gauge-invariant part) | smallest / largest |
|---|---|---|---|
| 0.5 | 4, 8 | 0.181; 0.160 (rank 1: blind) | 0 |
| 1 | 4, 8 | 0.053, 0.100, 0.100; 0.044, 0.079, 0.079 | 0.53, 0.56 |
| 2 | 4, 8 | 0.0148, 0.303, 0.303; 0.0118, 0.221, 0.221 | 0.049, 0.054 |

`w = 2` is not blind at the corner (rank 3), and the weak mode is about 5 % of the others, stable from `ℓ = 4` to `8`. The design
criterion of §7 (P1.8, bounded below on the whole coarse zone) has not been checked away from the corner for `w = 2`. The refit's
pre-registration is not affected: it tests content and the halves criterion of the fitted action, not `ObsTransferPhys`.
