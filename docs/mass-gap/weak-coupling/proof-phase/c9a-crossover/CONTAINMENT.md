# Reversed P4: containment instead of construction (2026-11-23)

Task (owner: "I think P4 has the wrong thought process ... the saturation has to be proven inside confinement and absent outside
that confinement, as a containing existence"; "Yes, attempt it"; via the coordinator):
* (a) **outside, absence:** in the containing weak-coupling region the twists are rare and stay below saturation; a lemma, with the
  scale range M1 covers;
* (b) **the container ends:** what exactly is needed to say the rarity branch fails at some finite scale, after which the electric
  channel carries `≥ 0.881` per box;
* (c) **inside, the payoff:** electric flux runs in tubes (a chain), so the hand-over's two-channel bound and superadditivity apply.
  **The decisive point:** derive the tube structure from saturation, not assume it (minimal-cost paths, Peierls for paths), and
  check whether `0.881` per box gives a convergent sum.

Marks: **Lean** (`Crossover/Containment.lean`, 8 theorems; `axioms-dy.log` now 56 Crossover theorems, standard axioms only),
**paper**, **sketch**, **citation**, **numerical** (small-torus run, preliminary), **open**.

## 0. Verdict in plain words

* **(a) closes as a lemma, with the right mechanism (Lean + citation).** For every box, `Z_tw/Z < 1` (strict flip, Lean). Also
  `Z_tw/Z = (1 − e^{−F_e})/(1 + e^{−F_e}) ≤ F_e` (`twist_ratio_le_elecF`, Lean): **the twist is rare exactly where electric flux
  is cheap.** In a physically small box, perturbation theory makes `F_e` of order `ḡ(L)²` (citation), so `r = O(ḡ²)`. The data
  agree (β = 3.5, `L = 2`: `F_e = 0.035`, `r = 0.018`). This is not M1's rarity, which is about large fields; M1 controls the law up
  to `L_*`, and the smallness of `F_e` there is perturbative.
* **(b) closes in long boxes, not in cubic ones.** At any fixed cross-section, the transfer kernel is strictly positive
  (`stepK_pos`, Lean). By Jentzsch/Krein-Rutman (citation) the vacuum is the unique top state and is centre-invariant, so the
  flux sector lies a factor `μ < 1` below per unit length. Then `F_e(T) ≥ −T log μ − log C` grows without bound
  (`elecF_lower_of_gap`, `exists_elecF_ge`, Lean). **The rarity branch fails in every long enough box: the container ends.** But
  `μ` and the length depend on the cross-section. In the cubic geometry the end needs `F_e(L) ≥ 0.881` at one `L`, i.e. `ḡ²` of
  order one, beyond perturbative or M1 control. Numerically (β = 2.3) it ends near `L = 4` (`F_e = 0.91`).
* **(c) The circularity is not broken: tube dominance needs more than the hand-over (Lean, sketch).** Gauss's law makes electric
  influence path-like (no sources, conserved mod 2). But a sum over paths with per-box cost `F` converges only if `F > log μ`, with
  `μ` the number of ways a path can continue (`tube_threshold`, Lean). Self-avoiding paths on `ℤ^d` have `μ ≥ d`, so in `d ≥ 3`
  the floor `0.881` gives `μ e^{−0.881} ≥ 3(√2 − 1) ≥ 1` (`path_entropy_beats_handover`, Lean): **path entropy beats the per-box
  cost, and the cheapest chain does not dominate.** In `d = 4`, `log μ₄ ≈ 1.91` (citation); rigorously between `log 4 ≈ 1.39` and
  `log 7 ≈ 1.95`. Equivalently, the single-sector twist ratio must exceed `(μ − 1)/(μ + 1) ≈ 0.74`.
* **First unclosable step:** at one box size, an electric cost per box above the path entropy, `F_e(L) > log μ₄ ≈ 1.91`
  (equivalently `r(L) > 0.74`), uniformly in the outside. That is the grid requirement of `NEIGHBOURS.md` (`log 8 ≈ 2.08`) refined
  by path counting. Containment moves the requirement inside, but does not lower it to the chain value. Numerically, at β = 2.3,
  `F_e(6) ≈ 2.6` passes it centrally (not certified).

## 1. (a) Outside: absence of saturation (Lean, citation, numerical)

| statement | Lean name | mark |
|---|---|---|
| `0 < Z_tw < Z` ⟹ `F_e ≥ 0` | `elecF_nonneg` | Lean |
| `Z_tw/Z = (1 − e^{−F_e})/(1 + e^{−F_e})` | `twist_ratio_eq` | Lean |
| `Z_tw/Z ≤ F_e` | `twist_ratio_le_elecF` | Lean |
| `Z_tw < Z` for every `β ≠ 0`, `L`, even `T` | `su2_Ztw_lt_Z` (`Flip/Strict.lean`) | Lean |

**The lemma (outside).** For every box, `r < 1`, and `r ≤ F_e`. So wherever the electric flux free energy is small, the twist is far
from saturation. In a physically small box (`L Λ ≪ 1`, `ḡ(L)` small), small-volume perturbation theory gives an electric flux
energy of order `ḡ²/L`, hence `F_e = O(ḡ(L)² T/L)` and `r = O(ḡ²)` (citation: small-volume expansions of Luescher and van Baal,
recalled, not re-checked).

**Scale range.** M1 controls the law from the cutoff to `L_*`, where `ḡ(L_*) = g_*` is small. The smallness of `F_e` up to `L_*` is
perturbative, consistent with M1 but not derived from it. M1's own rarity (released large fields, near-cut sets) is a different
statement: it concerns large fields, not the twist sector of a small box. **The mechanism outside is cheap electric flux (a
deconfined small box), and by duality that is a rare twist.**

**Data (small-torus run, preliminary).**

| β | `L` | torus | `r` | `F_e` |
|---|---|---|---|---|
| 3.5 | 2 | `2⁴` | 0.018 | 0.035 |
| 3.5 | 2 | `2³×4` | 0.074 | 0.149 |
| 2.3 | 2 | `2⁴` | 0.116 | 0.233 |
| 2.3 | 4 | `4⁴` | 0.425 | 0.907 |
| 2.3 | 6 | `6⁴` | 0.863 | 2.61 |

## 2. (b) The container ends (Lean core, citation, paper)

**In long boxes, rigorously (paper with a citation; Lean core).**
* At fixed cross-section `L_s`, the one-step transfer kernel is strictly positive and continuous on a compact space (`stepK_pos`,
  `Flip/Bound.lean`). So the transfer operator is compact and positivity improving.
* By Jentzsch's theorem (Krein-Rutman; citation) its top eigenvalue `λ₀` is simple with a positive eigenvector. The centre
  transformation commutes with it and maps positive vectors to positive vectors, so the top eigenvector is centre-invariant and lies
  in the `e = 0` sector. The flux sector's largest eigenvalue is `μλ₀` with `μ < 1`.
* Then `Z₁(T) ≤ C μ^T λ₀^T` (trace class) and `Z₀(T) ≥ λ₀^T`.
* `elecF_lower_of_gap` (Lean): `F_e(T) ≥ −T log μ − log C`. `exists_elecF_ge` (Lean): this exceeds any `θ`, in particular
  `0.881` and `log μ₄`, for `T ≥ T₀`.
* **So at every fixed cross-section the twist (rarity) branch fails in long enough boxes:** by the hand-over, the electric channel
  carries the suppression there.

**What this does not give.** `μ = μ(L_s)` may tend to 1 and `T₀(L_s)` to infinity as the cross-section grows. Uniformity in `L_s`
is a confinement statement. A grid of such long boxes is a chain along the long direction: the finite-cross-section gap again
(`RDOEBLIN.md` 2').

**In cubic boxes.** "The rarity branch fails at a finite scale" needs: there is an `L` with `F_e(L, L) ≥ log(1 + √2) ≈ 0.881`,
equivalently `r(L) ≥ √2 − 1`. Perturbatively `F_e ≈ c ḡ(L)²`, valid only while `ḡ` is small, where it stays below 0.881 if `g_*` is
chosen small. **Perturbation theory and M1 stop before the container ends.** The statement is a single-scale confinement input.
Numerically at β = 2.3: `F_e(4) = 0.907` (`r = 0.425`, at the self-dual point within errors).

## 3. (c) Inside: does saturation give tubes? (Lean, sketch, citation)

**What Gauss's law gives (paper).** The electric flux is conserved mod 2 (`even_card_fluxCells`: even number of flux faces per box).
So electric influence has no sources inside a box and propagates along connected paths of boxes. A `ℤ/2` line may also branch
(one in, three out is even), which only adds configurations.

**Peierls for paths (sketch for the expansion; Lean for the counting).** Bound the influence between two boxes at distance `D` by a
sum over paths of boxes, each box on the path costing a factor `e^{−F}`. This needs a product structure per box; the
annealed-to-quenched identification of `RATE.md` 5' is assumed here. With `μ` continuations per step, the sum is
`Σ_{n ≥ D} (μ e^{−F})ⁿ`.

| statement | Lean name | mark |
|---|---|---|
| `Σ xⁿ` summable ⟺ `x < 1` (`x ≥ 0`) | `path_sum_summable_iff` | Lean |
| `μ e^{−F} < 1 ⟺ F > log μ` | `tube_threshold` | Lean |
| `μ ≥ 3` ⟹ `μ (√2 − 1) ≥ 1` | `path_entropy_beats_handover` | Lean |

* **Counting (paper, citation).** Self-avoiding paths on `ℤ^d` have connective constant `μ_d ≥ d` (the `dⁿ` directed paths) and
  `μ_d ≤ 2d − 1` (non-backtracking). For `d = 4`, `μ₄ ≈ 6.77` (citation, recalled), `log μ₄ ≈ 1.91`; rigorously
  `log μ₄ ∈ [1.39, 1.95]`.
* **With the hand-over's 0.881:** `μ e^{−0.881} = μ(√2 − 1) ≥ 1` for every `μ ≥ 3`, so in every `d ≥ 3` the path sum diverges. The
  minimal-cost path does **not** dominate. Entropy wins, and the influence is not carried by one tube.
* **Threshold for tubes:** `F_e > log μ_d`, equivalently (`twist_ratio_eq`) a single-sector twist ratio `r > (μ − 1)/(μ + 1)`:
  about 0.74 for `μ₄ ≈ 6.77` (between 0.60 and 0.75 over the rigorous range).
* **Where it fails, exactly:** saturation at the self-dual point (`r ≈ 0.41`, `F_e ≈ 0.88`) is not enough. Strong saturation
  (`r > 0.74`, `F_e > 1.91`) would make the tube structure follow, and then the chain results apply. Strong saturation at one box is
  the grid requirement of `NEIGHBOURS.md` refined from `log 8` (column sum) to `log μ₄` (paths). **The circularity is not broken.
  It is narrowed to one number at one box.**
* **Numerical (preliminary, β = 2.3):** `F_e(6) ≈ 2.6 > 1.91` centrally (`r = 0.86 > 0.74`). Not certified: the 95 % lower bound of
  `r` is 0.56 statistically, and under the resolution floor of 1 on `F_e` the bound is 0.96.

## 4. DMP reading (separate; not mathematics)

* **Outside, non-existence keeps existing through assertion.** Outside the container (the small, weakly coupled box) the twist is
  rare because the electric flux costs almost nothing. The two are one fact seen from the two sides of the duality
  (`r ≤ F_e`).
* **The container must end, and does, along the run.** Along a long box the flux sector loses a fixed factor per unit length
  (Perron-Frobenius): the rarity branch cannot persist. This is the "it can never catch up" in exact form: `Z₁/Z₀ ≤ C μ^T`, `μ < 1`.
* **Inside, existence has to outrun possibility.** A tube exists as the carrier only if its cost per step beats the number of ways
  to continue (`F > log μ`). "Existence = non-existence + 1" in counting form: of the `μ` continuations per step, only one is the
  tube; the tube dominates only if the cost per step exceeds `log μ`. The balanced state (0.881) is not enough. Only past the balance
  point by the path entropy does the inside run as a chain.

## 5. Status

| step | result | mark |
|---|---|---|
| (a) `r < 1` everywhere; `r ≤ F_e`; small box: `F_e = O(ḡ²)` | closed (lemma); smallness perturbative | Lean; citation |
| (b) at fixed cross-section the rarity branch fails in long boxes | closed | Lean core, citation (Jentzsch), paper (centre invariance) |
| (b) in cubic boxes: `F_e(L) ≥ 0.881` at some `L` | open (beyond perturbative/M1 control); numerically `L ≈ 4` at β = 2.3 | open; numerical |
| (c) Gauss's law: influence path-like | | paper |
| (c) tube dominance needs `F > log μ_d`; `0.881` fails for `d ≥ 3` | closed (negative) | Lean (counting), citation (`μ₄`) |
| **strong saturation at one box: `F_e(L) > log μ₄ ≈ 1.91` (`r > 0.74`), uniformly in the outside** | **first open step** | open; numerical: passed centrally at `L = 6`, β = 2.3 |

## 6. Addendum: the law on both sides (Gauss) and the Bogomolny floor (2026-11-23, after the owner's two readings)

### 6.1 Tube structure from Gauss's law plus the per-box cost (paper; Lean where marked)

The owner: "The derivation is simply that a set of laws, IM, has to exist for that definition of existence, which are DMP-complete,
since IM already is both sides." The coordinator's mapping: the law on both sides of every DB is **Gauss's law** (the gauge
constraint). It holds identically inside and outside and is conserved across every face.

**What the law alone gives (Lean, paper).**
* *Both sides:* the flux through a box's boundary is the same seen from inside and from outside (`cob_restrict_eq_cob_restrict_compl`).
* *No sources:* the total flux out of a box is even (`sum_cob_restrict_eq_zero`, `even_card_fluxCells`).
* *No screening:* a flux-carrying outside forces a sheet through the box (`exists_sheet_both_sides`).
* *Path-like influence:* as a consequence, electric influence propagates along connected paths of boxes, never appearing or
  disappearing inside one.

That is the whole structural content of "tube": a conserved line with no sources. It follows from the law, without assuming tubes.

**What the law does not give.** Which of the paths carries the influence. The law allows every path, and branchings (one line in,
three out is even), with no preference. The **dominance of the cheapest path** is a comparison of cost and count. The per-box
electric cost `F` must exceed the path entropy, `F > log μ_d` (`tube_threshold`, Lean). The hand-over's `0.881` does not
(`path_entropy_beats_handover`, Lean, `d ≥ 3`). So the derivation is: **law (structure) + cost above entropy (dominance) ⟹ tube.**
It needs exactly one input beyond the law: `F_e(L) > log μ₄ ≈ 1.91` at one box, a property of the action, not of the constraint. It
also uses the product structure of per-box costs along a path (the annealed/quenched point of `RATE.md` 5').

### 6.2 The Bogomolny floor (citation, paper, sketch)

**The tool (citation).** For every configuration of topological charge `Q`, `S ≥ 8π²|Q|/g²`, saturated by (anti)self-dual fields;
self-duality exists only in `d = 4`. On a torus with 't Hooft twist `n_{μν}`, `Q ∈ −Pf(n)/2 + ℤ` for SU(2), so twists with odd twist
product force `|Q| ≥ 1/2` and `S ≥ 4π²/g² = π² β` (`β = 4/g²`). On the lattice it holds for admissible fields (Luescher: all
plaquettes near 1), which is M1's small-field region.

**Where it helps: outside, for multi-plane twist sectors (paper).** In the multi-sector sum `S_tw` of `TRANSFER.md`, the sectors with
odd twist product are suppressed by `e^{−π²β}` per box on admissible fields, a worst-case floor uniform over admissible outsides.
That strengthens lemma (a) for those sectors.

**Where it does not help.**
* *The single-plane twist of our hand-over and small-torus run* (one temporal plane `(0, k)`) has twist product zero. Its sector
  contains flat configurations (twist-eaters: `Ω₀ Ω_k = −Ω_k Ω₀` with the other two holonomies central), so `Q = 0` and the floor is
  0. The suppression of this sector at weak coupling is entropic (cheap electric flux, section 1), not an action floor.
* *Inside, for (c).* Bogomolny bounds the twist weight from **above** (rarity). Strong saturation needs twist weights **high**. It is
  the wrong side for the first open step.
* *Non-admissible fields* (M1's large fields) are excluded. There the floor is only the crude one, and the region is a rarity
  event (`RDOEBLIN.md` 4).

**Where entropy beats it (sketch).** A fractional instanton on the twisted torus has at least its 4 translation moduli. In lattice
units its weight is about `(L/a)⁴ · J(β) · e^{−π²β}`, with `J` the polynomial collective-coordinate factor. At a fixed physical box
size, one-loop running gives `β(a) ≈ (11/(3π²)) log(1/(aΛ))` for SU(2), so the floor is `π²β ≈ (11/3) log(1/(aΛ))`. The position
entropy is `4 log(L/a) = 4 log(1/(aΛ)) + O(1)`. Since `4 > 11/3`, **the entropy wins logarithmically as `a → 0`**, and the action
floor gives no uniform suppression at fixed physical size (one-loop sketch; determinants and the measure not checked). The floor is
useful at a fixed lattice box with large β, not uniformly in the tick.

### 6.3 DMP reading of the addendum (separate; not mathematics)

* **Does the derivation match "IM already is both sides"?** For the structure, yes. Gauss's law is literally the same statement on
  both sides of every DB (the boundary flux computed from inside equals the one computed from outside), and it alone makes the
  carrier a conserved, unscreenable, source-free line: the tube's shape. For the dominance, no. Which line carries the act is not
  in the law; it is decided by cost against possibility (`F > log μ`). The law makes every tube possible; the action has to make one
  tube cheaper than all the others combined. In the owner's terms, IM supplies the both-sided definition, and the act still has to
  outrun the possibility space.
* **The instanton as the first act.** Bogomolny is a worst-case floor on the action of a forced topological sector, an a-priori
  "pressing" in exactly the owner's sense. But it prices the rare side (twists with nonzero twist product), and its price `π²β`
  loses logarithmically to the position entropy `4 log(L/a)` as the tick shrinks. The pressing exists and is proved, but it is not
  yet a per-box certificate in physical units.

## 7. Files

* `CONTAINMENT.md` (this note); `formal/ProofPhase/Crossover/Containment.lean` (new, 8 theorems); `axioms-dy.sh` extended,
  `axioms-dy.log` (56 theorems, standard axioms); `~/formal-dy` deleted.
