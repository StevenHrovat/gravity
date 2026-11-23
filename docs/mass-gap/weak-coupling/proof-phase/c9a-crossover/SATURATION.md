# Twist saturation at one box size: our own attempt, and the bond-moving bounds (2026-11-23)

Task (owner: "Let's first try it on our own ..."; PREP, "The duality is never alone while running"). The 't Hooft relation is
kinematic; while the system runs, the action selects the branch. The missing input is dynamical: **twist saturation at one box
size**, enough for the quantitative 't Hooft criterion of `TRANSFER.md` (summed electric weight `< 1` iff the average twist ratio
exceeds `(2^{n−1} − 1)/(2ⁿ − 1)`, `3/7` for `n = 3`). Use our pieces (strict flip bound, hand-over, superadditivity, conditional
mass, M1 at `L_*`). One outside tool is allowed: Migdal-Kadanoff-type bond-moving bounds (Tomboulis 2007), used inside our own
reduction, with the interpolation step located exactly. Also: does Kanazawa's twisted/untwisted theorem duplicate or extend
`Flip/Strict`?

Marks: **Lean** (`Crossover/Saturation.lean`, 4 theorems; `axioms-dy.log` now 48 Crossover theorems, standard axioms only),
**paper**, **sketch**, **citation** (the bond-moving statements and Kanazawa's theorem are from fetched texts, partly from
summaries of their later sections: recalled, not re-checked line by line), **numerical**, **open**.

## 0. Verdict in plain words

* **What our pieces give, exactly.**
  - *A tick-unit floor (Lean).* Configuration by configuration the twist changes the weight by at least `e^{−2βN}` (`N = L²` flipped
    plaquettes). So `Z_tw/Z ≥ e^{−2βL²}`, which saturates the twist only for `βL² ≤ ½ log(7/3) ≈ 0.42`. That is strong coupling in
    tick units, and it vanishes in the continuum, like plain Doeblin.
  - *A one-way link from the one-box statement to saturation (Lean).* A large electric free energy forces a saturated twist
    (`twist_ratio_of_elecF`). With superadditivity, `F_e(L) > 2c(L)` at one `L` makes `F_e(kL)` grow, so the twist saturates in long
    boxes. But that premise **is** the one-box statement, so saturation is a consequence of it, not an independent input.
  - *The rest is silent.* The strict flip bound bounds the twist from above; the hand-over picks no branch; the conditional mass is
    neutral-sector; M1 at `L_*` is weak coupling, the costly-twist (rarity) branch.
* **What the bond-moving bounds add, and where they stop.**
  - *What they add.* Rigorous one-sided bounds on `Z` and on the even sector `Z⁺`. The upper decimation flows to strong coupling
    for every β in `d ≤ 4` (Ito's theorem, citation), which our toolset lacked.
  - *Where they stop.* A lower bound on the twist ratio needs `Z⁺` from below and `Z` from above. The upper bound carries the
    normalisation `Π F̂₀^{|Λ'|}`, which is `≥ 1` (Jensen, Lean) and extensive in the box's lattice volume. The lower bound has
    normalisation 1.
  - *In our one-box form.* The mismatch is finite, because it is one box, not the infinite volume, so the bound is legitimate. But
    it is exponentially small in `(L/b)⁴` and grows like `log β` per moved plaquette at weak coupling (sketch). At a fixed
    physical box size (`L = ℓ/a → ∞`) it vanishes.
  - **So the one-box form localises Tomboulis's interpolation step to one box but does not avoid it.** The step needed is a lower
    bound on the box partition function matched to the upper decimation's normalisation within `O(1)`.
  - Kanazawa's flow objection (decimations with `r < 1` can flow to weak coupling) does not enter, because only the standard
    `r = 1` upper decimation is used.
* **First unclosable step:** twist saturation at one box of fixed physical size. Either route stops at the same wall:
  - the floor route needs strong effective coupling at the box scale, which is the crossover P4;
  - the bond-moving route needs the normalisation-matched lower bound, which is the interpolation step in one box.
* **Kanazawa: confirmation, no extension.** His inequality `Z_tw ≤ Z` for central twists is reflection positivity, non-strict
  (cited to earlier work), and his SU(2) bracket `1/2 < Z⁺/Z < 1` is `0 < Z⁻/Z < 1`. `Flip/Strict` proves the strict upper half in
  Lean for every `β ≠ 0`, `L`, even `T`. His Theorem 1 is an equality in the strong-coupling region (cluster expansion), not an
  inequality.
* **Numerical (preliminary, small-torus run, β = 2.3).** The cubic twist ratio crosses the threshold between `L = 4` (`r = 0.42`,
  just at the self-dual value) and `L = 6` (`r = 0.86`, one-sided 95 % lower bound 0.56). There, `F_e(6) ≈ 2.6`, above `log 8`
  centrally but not certified (95 % lower bound 1.26 statistically, 0.96 with the resolution floor). The action selects the
  saturated branch by `L ≈ 6` at this coupling. That is evidence, not proof.

## 1. What the action and our pieces give (Lean, paper)

| statement | Lean name | mark |
|---|---|---|
| pointwise `wt ≥ c · w` ⟹ `Z_tw/Z ≥ c`; for a twist of `N` plaquettes `c = e^{−2βN}` (each plaquette factor changes from `e^{βq}` to `e^{−βq}`, `|q| ≤ 1`) | `ratio_floor_of_pointwise` | Lean (abstract), paper (the factor) |
| `θ ≤ e^{−2βN} ↔ 2βN ≤ log(1/θ)` | `exp_floor_ge_iff` | Lean |
| `0 < Z_tw < Z`, `F_e ≥ log((1 + θ)/(1 − θ))` ⟹ `Z_tw/Z ≥ θ` | `twist_ratio_of_elecF` | Lean |
| `F_e(kL) ≥ k (F_e(L) − 2C)` | `flux_superadd_iter` (`CompositeHTF.lean`) | Lean |

* **The tick-unit floor.** At β = 0 the twist costs nothing (`Z_tw = Z`). The floor gives saturation (`θ = 3/7`) for
  `βL² ≤ ½ log(7/3) ≈ 0.42`: `β ≤ 0.11` at `L = 2`, `β ≤ 0.012` at `L = 6`. It is set in tick units and vanishes as `L = ℓ/a` grows.
  Renormalized at a blocked scale with coupling `β_eff` and `N_b` blocked plaquettes on the twist surface, the condition is
  `β_eff N_b ≤ 0.42`: strong effective coupling at the box scale, the wall of `RDOEBLIN.md` 3.
* **The electric route.** For one sector, saturation at `θ = 3/7` needs `F_e ≥ log 2.5 ≈ 0.916`, just above the self-dual
  `0.881` (at the self-dual point `r = √2 − 1 ≈ 0.414 < 3/7`). For the average over all `2ⁿ − 1 = 7` sectors, if multi-plane twist
  ratios were products of single ones (an assumption, sketch), the single ratio would need about `0.59`, i.e. `F_e ≳ 1.36`.
  Superadditivity makes `F_e(kL)` grow once `F_e(L) > 2c(L)`. That premise is the one-box statement itself, so the chain is:
  one-box statement ⟹ twist saturation in long boxes (Lean). The converse needs the neutral excess act `c(L)` small: the neutral gap.
* **The others.** `Flip/Strict` (`Z_tw < Z`) is the upper side. `HandOver.lean` (`max(F_tw, F_e) ≥ 0.881`) picks no branch. The
  conditional mass (`ROUTE3.md` 7) is a neutral-sector quantity. M1 at `L_*` has small `ḡ`, the costly-twist branch. Saturation,
  if it happens, happens between `L_*` and `L₁`: the crossover.

## 2. The bond-moving bounds inside our one-box form (citation, Lean, sketch)

**The tool** (Tomboulis 2007, arXiv 0707.2179, sections 2-3; citation, partly from a summary of the later sections). Character
expansion of the plaquette weight `f = 1 + Σ_j d_j c_j χ_j` with `c_j ≥ 0`. One decimation step of scale `b`:
* *Upper bound:* `Z_Λ ≤ F̂₀^{|Λ'|} Z_{Λ'}({c^U})` with `F̂_j = ∫ f^ζ χ_j/d_j`, `ζ = b^{d−2}` (plaquette moving), `ĉ_j = F̂_j/F̂₀`, and
  `c_j^U = ĉ_j^{b²}` (decimation in the plane). Iterated, `c^U → 0` for every β in `d ≤ 4` (Ito's theorem, citation): the upper
  flow reaches strong coupling.
* *Lower bound:* `Z_{Λ'}({c^L}) ≤ Z_Λ` with normalisation 1, for example `c^L = c^6`.
* *Twisted sectors:* `Z⁻ ≤ Z` when all `c_j ≥ 0`; `Z⁺ = (Z + Z⁻)/2` is reflection positive.

**Used for our target (sketch).** We need a lower bound on `r = Z⁻/Z = 2Z⁺/Z − 1` for one box of lattice size `L = b^k`:

    Z⁺/Z ≥ Z⁺_cell({c^L(k)}) / ( Π_{n=1}^{k} F̂₀^U(n)^{|Λ_box(n)|} · Z_cell({c^U(k)}) ).

* **Where an interpolation-type step is needed: the normalisation product.** `F̂₀ = ∫ f^ζ ≥ (∫ f)^ζ = 1`
  (`jensen_normalization`, Lean). `|Λ_box(1)| = 6 (L/b)⁴` moved plaquettes at the first level alone. At weak coupling `f` is peaked
  with width about `β^{−1/2}` on SU(2), and `log F̂₀^U(1)` grows like `log β` (sketch). So the denominator is at least
  `exp(6 (L/b)⁴ log F̂₀^U(1))`. The lower bound has no such factor. Tomboulis's interpolation is exactly the device that would make
  the two normalisations equal. The second mismatch is the couplings themselves: `c^L(k)` against `c^U(k)`.
* **Does the one-box form avoid it?** Partly. In the infinite volume the mismatch is `e^{O(|Λ|)}` and makes the bound empty without
  interpolation. In one box it is finite, so the bound is a valid inequality. But it is exponentially small in the box's lattice
  volume, and at a fixed physical box size (`L = ℓ/a`) that volume diverges as `a → 0`. At strong coupling (`F̂₀ ≈ 1`,
  `c^U ≈ c^L ≈ 0`) the bound is good, but there saturation is already given by the floor of section 1.
* **The step, named:** a lower bound on the box partition function `Z_box(β) ≥ e^{−K} Π F̂₀^U(n)^{|Λ_box(n)|} Z_cell(c^U(k))` with
  `K = O(1)` uniformly in `a` at fixed physical `L`. Equivalently, the box free energy equals the upper-decimated one up to a bounded
  boundary term. This is the interpolation step, for one box.
* **Kanazawa's flow objection** (with a modified decimation parameter `r < 1` the flow can reach weak coupling at large β; his
  remedy `r = 1 − 1/b²`) concerns the interpolated decimations. The standard `r = 1` upper decimation used here flows to strong
  coupling (Ito). The obstacle in our form is the normalisation, not the flow.

## 3. Kanazawa's theorem against `Flip/Strict` (confirmation only; citation)

Kanazawa, arXiv 0805.2742 (Phys. Lett. B 670, 2009), as fetched (sections 1-2 verbatim, later parts from a summary):
* **Theorem 1** is an **equality** relating `Z(c)/Z_Λ(c)` to a decimated ratio summed over twisted sectors, for U(N) (discrete
  U(1) subgroups) and SU(N) (`ℤ_N`), general character coefficients, periodic boundary conditions, in a strong-coupling window
  (cluster expansion). It is not an inequality between twisted and untwisted partition functions.
* The inequality `Z_Λ^g ≤ Z_Λ` for a central twist `g`, all β, is used by citation and proved by **reflection positivity**:
  non-strict.
* For SU(2), `1/2 < Z⁺/Z < 1`, i.e. `0 < Z⁻/Z < 1`.
* **Against ours:** `su2_Ztw_lt_Z` (`Flip/Strict.lean`) proves the **strict** `Z_tw < Z` for every `β ≠ 0`, every `L ≥ 1`, every even
  `T`, every spatial background twist, machine-checked, by the transfer-step criterion and Schur's lemma. So it duplicates the
  non-strict RP inequality, matches the strict upper half of his bracket, and is the only machine-checked version. The lower half
  (`Z⁻ > 0`) we still take as a hypothesis in `su2_handover`. Nothing in Kanazawa extends our result.

## 4. Numerical: where the action selects the branch (small-torus run, preliminary; `ONEBOX-CHECK.md` 8)

β = 2.3, snake estimator, all `L²` steps per torus (the full verdict table comes with the run's section 9):

| `L` | torus | `r = Z_tw/Z` | `log r` ± σ_stat | `F_tw` | `F_e` |
|---|---|---|---|---|---|
| 2 | `2⁴` | 0.116 | −2.16 ± 0.09 | 2.16 | 0.23 |
| 2 | `2³×4` | 0.394 | −0.93 ± 0.10 | 0.93 | 0.83 |
| 4 | `4⁴` | 0.425 | −0.86 ± 0.17 | 0.86 | 0.91 |
| 4 | `4³×8` | 0.757 | −0.28 ± 0.17 | 0.28 | 1.98 |
| 6 | `6⁴` | 0.863 | −0.15 ± 0.27 | 0.15 | 2.61 |
| 6 | `6³×12` | 0.835 | −0.18 ± 0.26 | 0.18 | 2.41 |

* **Reading.** In the cubic geometry the twist ratio passes the single-sector threshold `3/7` between `L = 4` (`r = 0.42`, at the
  self-dual point) and `L = 6` (`r = 0.86`; one-sided 95 % lower bound `e^{−0.147 − 1.645·0.265} = 0.56`). At `L = 6`, `F_e ≈ 2.6`
  exceeds `log 8 ≈ 2.08` centrally. Its one-sided 95 % lower bound is 1.26 statistically, and 0.96 under the resolution floor of 1
  (`RULES.md`), so it is not certified.
* **Provability.** This can refute "the twist never saturates at small `L`" and does not. It cannot establish saturation, and it says
  nothing about other β or about fixed physical size.

## 5. DMP reading (separate; not mathematics)

* **The duality is never alone while running.** The data at β = 2.3 show the selection the owner describes: below `L ≈ 4` the twist
  branch is suppressed (rarity side), at `L = 4` the system sits at the self-dual point, by `L = 6` the twist is nearly free and the
  electric channel carries the suppression (disorder side). The hand-over is where the run passes through the balanced state.
* **The cost of description.** Moving bonds is a re-description of the same existence on a coarser grid. Jensen says the
  re-description costs (`F̂₀ ≥ 1`): an upper bound that over-counts. A matched normalisation would be a description without loss.
  That is exactly what the interpolation step asks for, and what is missing.
* **Where the act becomes provable.** Saturation is what the one-box statement implies (Lean, one way). A proof of saturation would
  need the run itself, the crossover from the weak-coupling hand-over to the scale where the twist is free, in a form uniform in the
  tick.

## 6. Status

| step | result | mark |
|---|---|---|
| tick-unit floor `r ≥ e^{−2βL²}`; saturates for `βL² ≤ 0.42` | closed (strong coupling only, vanishes in the continuum) | Lean |
| one-box statement ⟹ twist saturation in long boxes | closed (one direction) | Lean (`twist_ratio_of_elecF` + `flux_superadd_iter`) |
| saturation from strict flip, hand-over, conditional mass, M1 | no (wrong side, no branch, neutral, weak coupling) | paper |
| bond-moving bounds inside the one-box form: valid, but normalisation `Π F̂₀^{|Λ_box|} ≥ 1` extensive in `(L/b)⁴` | localises the interpolation, does not remove it | citation, Lean (Jensen), sketch |
| **normalisation-matched lower bound on `Z_box` (one-box interpolation), equivalently strong effective coupling at the box scale (P4)** | **first open step** | open |
| Kanazawa vs `Flip/Strict` | confirmation; ours strict and machine-checked | citation |
| numerical: saturation between `L = 4` and `6` at β = 2.3 (cubic) | evidence | numerical (preliminary) |

## 7. Files

* `SATURATION.md` (this note); `formal/ProofPhase/Crossover/Saturation.lean` (new, 4 theorems); `axioms-dy.sh` extended,
  `axioms-dy.log` (48 theorems, standard axioms); `~/formal-dy` deleted.
* Sources: arXiv 0707.2179 (Tomboulis), 0711.4930 (Ito-Seiler), 0805.2742 (Kanazawa), read through the arXiv HTML versions; the
  later sections of the first and third were read as summaries only.
