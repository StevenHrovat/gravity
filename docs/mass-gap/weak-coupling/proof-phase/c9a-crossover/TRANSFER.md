# Transfer round: the per-box suppression a grid needs, from P vs NP and GRH (2026-11-23)

Task (owner: "Start both transfer rounds, please"; via the coordinator). Goal: the per-box suppression a grid needs,
`F > log(2d) ≈ 2.08` in `d = 4` (`NEIGHBOURS.md`), from the new transferables:
1. **New derivations and combined pairs** (from `docs/pnp/CP-DUALITY.md`). Does a two-channel cost, possibly charged per combined
   pair of block structures across a DB, give a duality floor above `log(2d)`?
2. **Holonomy as the remnant** (PREP, "the HTF is smoothed to zero globally; only the remnants remain"). Is the conserved `ℤ/2`
   holonomy's suppression summable over the `2d` channels where field-size suppression is not?
3. **"It runs"** (from `docs/rh-guide/grh/TATE.md` 2a). State the one-box statement as contractivity of the blocked transfer
   operator on the neutral sector, in the same form as TATE's target.

Marks: **Lean** (`Crossover/Runs.lean`, 7 theorems, importing `GRH/Tate.lean`; `axioms-dy.log` now 44 Crossover theorems,
standard axioms only), **paper**, **sketch**, **citation**, **reading**, **open**.

## 0. Verdict in plain words

* **1. No floor above `log(2d)` from duality. The exact multi-sector form shows why.** For `n` independent `ℤ/2` sectors,
  't Hooft's Fourier relation gives `(1 + S_tw)(1 + S_e) = 2ⁿ` (paper). Here `S_tw` and `S_e` are the summed twist and summed
  electric weights over all nonzero sectors. In cutting planes the two channels **add** to the line size (`thr_duality`), so the
  floor grows with the line. Here they **multiply** to `2ⁿ`, so the duality forces the smaller sum only below the self-dual value
  `√(2ⁿ) − 1` (`min_le_of_sector_product`, Lean). That value is `≥ 1` as soon as `n ≥ 2` (`selfdual_sector_ge_one`, Lean): for two
  or more sectors, duality allows both summed weights to be at least 1, so it forces no summable suppression. Combining a pair of
  block structures across a DB adds sectors (`n₁ + n₂`), which makes this worse, not better. The growing floor of cutting planes
  corresponds here to "one channel is large", the wrong direction for a rate.
* **What the summed form does give: the requirement as a quantitative 't Hooft criterion** (`electric_sum_lt_one_iff`, Lean).
  The summed electric weight is below 1 iff the summed twist weight exceeds `2^{n−1} − 1`. Equivalently, the average twist ratio
  over the `2ⁿ − 1` nonzero sectors exceeds `(2^{n−1} − 1)/(2ⁿ − 1)`: `3/7 ≈ 0.43` for `n = 3`. **This is the first step that does
  not close:** a dynamical statement at one box size (near-saturated twists, vortex condensation). It is not supplied by any
  duality or floor.
* **2. Holonomy is the right carrier and gives no extra summability.** It survives smoothing and is what crosses a DB, but
  conservation fixes how many times flux crosses the boundary (parity), not where. In `d = 4` a centre sheet cuts a box's boundary
  in a closed curve meeting 2 to 4 faces, so the face sum is `(2 to 4) ×` the number of sheet pieces. Summability needs the expected
  number of sheet pieces per box below `1/2` at best. With 6 plane orientations, that is a per-orientation flip probability below
  `1/12`, i.e. `F_tw > log 11 ≈ 2.40`, again above the duality floor (whose twist branch gives `p ≤ 1/(2 + √2) ≈ 0.29`).
* **3. "It runs" is one formal statement with two targets (Lean).** Both problems ask about an evolution that does not increase a
  positive norm. GRH needs every mirrored mode to be a **phase** (`runs_and_mirror_on_line`, Tate). The one-box statement needs
  **no phase mode** in the neutral sector, with a uniform margin: `‖T x‖ ≤ η ‖x‖` there with `η < 1` (`no_phase_mode`,
  `iterate_contraction`). `runs_two_targets` puts them side by side. The open steps are complementary. Yang-Mills has the positive
  norm for free (reflection positivity) and lacks the margin. GRH lacks the positive norm (Weil positivity) and needs no margin.

## 1. New derivations and combined pairs (paper, Lean)

**The two currencies in Yang-Mills (paper).** M1's split already has them. The small-field part ("axiom-near": SO(3) fluctuations,
cost `β` per unit plaquette deviation) and the derived, block-level structures (closed `ℤ/2` sheets, carried by attribution) pay in
different currencies. A block variable is introduced once and reused at every later scale: the "new derivation". The Lean
statement that the two currencies do not overlap is already there: `window_gap` (`Dichotomy.lean`), sheet Peierls and saturation
never hold at the same coupling. The only exact bridge between them is the hand-over, `max(F_tw, F_e) ≥ log(1 + √2)`.

**The multi-sector duality (paper: 't Hooft; Lean: the consequences).** With `n` independent twist sectors `k ∈ (ℤ/2)ⁿ`,
`Z_e(e) = 2^{−n} Σ_k (−1)^{e·k} Z(k)`. Evaluating at `e = 0` and summing over `e` gives `Z_e(0) = 2^{−n} Σ_k Z(k)` and
`Σ_e Z_e(e) = Z(0)`, so

    (1 + S_tw)(1 + S_e) = 2ⁿ,   S_tw = Σ_{k≠0} Z(k)/Z(0),   S_e = Σ_{e≠0} Z_e(e)/Z_e(0).

For `n = 1` this is the hand-over (`handover_ratio`: one of `r`, `(1 − r)/(1 + r)` is `≤ √2 − 1`).

| statement | Lean name | mark |
|---|---|---|
| `(1 + a)(1 + b) = 2ⁿ` ⟹ `min(a, b) ≤ √(2ⁿ) − 1` | `min_le_of_sector_product` | Lean |
| `n ≥ 2` ⟹ `√(2ⁿ) − 1 ≥ 1` | `selfdual_sector_ge_one` | Lean |
| `(1 + a)(1 + b) = 2ⁿ` ⟹ (`b < 1 ↔ 2^{n−1} < 1 + a`) | `electric_sum_lt_one_iff` | Lean |

**Against the cutting-planes pattern (paper).**
* *Cutting planes:* `k + (e − k + 1) = e + 1`. The channels add, so one of them is at least `(e + 1)/2`, a floor growing with the
  line. A large cost is what a lower bound wants.
* *Yang-Mills:* `log(1 + S_tw) + log(1 + S_e) = n log 2`. The logs add, so the larger summed weight is at least `√(2ⁿ) − 1`: a
  floor on how **unsuppressed** one channel is. A rate wants the opposite, a small summed weight, and duality caps the smaller
  one only at the self-dual value.
* *Pairs across a DB:* the sectors of two boxes combine, `n = n₁ + n₂`, and the self-dual value grows. The pair is the cutting-plane
  interface (where the hardness lives); in Yang-Mills the analogue of interface hardness is the dynamical value of `S_e`, not a
  duality.

**First unclosable step.** At one box size `L`, the summed electric weight `S_e(L) < 1` (minus the neutral share), equivalently
`S_tw(L) > 2^{n−1} − 1`: the twists near saturation, 't Hooft's criterion in quantitative form. The small-torus run of
`ONEBOX-CHECK.md` 8 measures the single-sector ratio `r`; at `L = 2`, β = 2.3 it is `0.12` (so `S_tw` for three equivalent
sectors is near `0.35` plus the multi-plane sectors, far below `3`). The full result comes with the run.

## 2. Holonomy as the remnant (paper, sketch)

* **Why it is the right carrier (paper, citation).** A flat connection still carries its holonomy around non-contractible loops
  (Aharonov-Bohm); the centre flux is the `ℤ/2` holonomy class. It survives every smoothing of the field and cannot be screened by a
  collar (`cob_restrict_eq_cob_restrict_compl`, conservation). Field size is smoothed away; holonomy is not.
* **Does conservation reduce the face sum? No (paper).** Conservation fixes the parity of boundary crossings
  (`even_card_fluxCells`), not the faces. In `d = 4` a centre sheet in the plane `(μ, ν)` meets a box's boundary in a closed curve
  on the faces `±μ, ±ν`: 2 to 4 faces per sheet piece. So the face sum of holonomy influence equals (2 to 4) times the number of
  sheet pieces through the box. The best case (2 faces each) needs the expected number of pieces `< 1/2`. Summed over the 6 plane
  orientations, with flip probability `p = 1/(1 + e^{F_tw})` per orientation: `p < 1/12`, i.e. `F_tw > log 11 ≈ 2.40`. The
  hand-over's twist branch gives `F_tw ≥ 0.881`, `p ≤ 0.29`. "Holonomy enters through one face and must leave through one face"
  holds in a chain. In a grid the exit is any face, and the count is what it is.
* **Reading.** The remnant is the carrier, not a source of suppression. Its suppression per box is the twist free energy, the
  same quantity as before.

## 3. "It runs": the shared formal statement (Lean, paper)

**The one-box statement in this form (paper).** Reflection positivity makes the transfer operator `T_L` of the blocked chain (step
one box of size `L`) a positive self-adjoint contraction on a positive Hilbert space: **it runs**, for free. The one-box statement
is the margin: on the neutral sector orthogonal to the vacuum, `‖T_L x‖ ≤ η ‖x‖` with `η < 1` uniform in the volume, and in the
lattice spacing at fixed physical `L` (`NEIGHBOURS.md` 3). Then `‖T_L^n x‖ ≤ ηⁿ ‖x‖` (`iterate_contraction`), and no neutral
mode is a phase (`no_phase_mode`). In spectral terms `η = e^{−m L}`, with `m` the neutral gap; the excess act `c(L)` of `HTF.md`
4 is the trace version of the same margin.

| statement | Lean name | mark |
|---|---|---|
| `‖T x‖ ≤ η ‖x‖` on `S` ⟹ eigenvalues with eigenvector in `S` have `‖μ‖ ≤ η` | `eig_norm_le_of_contraction` | Lean |
| `T S ⊆ S` as well ⟹ `‖Tⁿ x‖ ≤ ηⁿ ‖x‖` on `S` | `iterate_contraction` | Lean |
| `η < 1` ⟹ no eigenvector in `S` with `‖μ‖ = 1` | `no_phase_mode` | Lean |
| norm-nonincreasing `T` with a mirror pair: the pair lies on the circle (GRH), and its eigenvector is not in a strictly contracted `S` (Yang-Mills) | `runs_two_targets` | Lean (uses `ProofPhase.GRH.runs_and_mirror_on_line`) |

**The two open steps are complementary (reading).**
* *GRH:* the evolution is constructed from local data and preserves Weil's form. Whether that form is a **positive** norm on the
  functions that see the zeros is the open step (Weil positivity). Given positivity, the mirror pins every mode to the circle, and
  no margin is needed.
* *Yang-Mills:* positivity is built in (Haar measure times `e^{−S}`, Osterwalder-Seiler). The open step is the **margin**: a strict
  contraction `η < 1` on the neutral sector, uniformly in the volume, which is the one-box statement.

## 4. DMP reading (separate; not mathematics)

* **Two categories of proof lines.** The cheap lines are the small-field fluctuations (each pays its own plaquette cost). The new
  derivations are the block structures, sheets and flux, introduced once and reused. Duality between the two currencies exists
  exactly (`(1 + S_tw)(1 + S_e) = 2ⁿ`). But it is a product, not a sum, so it fixes the balance point, not a suppression. The
  "first true act" (two derivations used together) adds sectors here and moves the balance point up.
* **The remnant.** Smoothing to zero leaves the holonomy class, and that is what crosses a DB. It is the anchor in causality the
  owner names: conserved, unscreenable, the carrier of the certificate. It does not by itself make the certificate summable over a
  grid.
* **"It runs."** In Yang-Mills existence (positivity) is given; what has to be shown is that the run loses something at every
  step in the neutral sector, the margin. In GRH the margin is not the question; existence of the positive norm is. Same sentence,
  opposite open halves.

## 5. Status

| step | result | mark |
|---|---|---|
| two currencies = M1's split; disjoint regimes | known | Lean (`window_gap`) |
| multi-sector duality `(1 + S_tw)(1 + S_e) = 2ⁿ` | identity | paper ('t Hooft) |
| duality caps the smaller summed weight at `√(2ⁿ) − 1 ≥ 1` (`n ≥ 2`): no summable floor | closed (negative) | Lean |
| pairs across a DB add sectors: worse | | paper |
| requirement: `S_e(L) < 1` ⟺ `S_tw(L) > 2^{n−1} − 1` at one box (quantitative 't Hooft criterion) | **first open step** | Lean (equivalence), open (value) |
| holonomy: right carrier; face sum = (2 to 4) × sheet pieces; needs `F_tw > log 11` | no gain | paper |
| one-box statement = strict contraction on the neutral sector; shared "runs" form with GRH | closed (form) | Lean (abstract) |

## 6. Files

* `TRANSFER.md` (this note); `formal/ProofPhase/Crossover/Runs.lean` (new, 7 theorems); `axioms-dy.sh` extended,
  `axioms-dy.log` (44 theorems, standard axioms).
