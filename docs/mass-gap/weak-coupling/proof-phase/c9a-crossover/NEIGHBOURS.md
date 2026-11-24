# The summed influence over the 2d neighbours, and the rate in physical units (2026-11-23)

Task (owner: keep the computer checks as the third verification layer and push the proof's edges; via the coordinator). Doeblin
gives each DB a per-channel loss rate `η ≤ 1 − e^{−C β L^{d−1}}` for every outside (`Mixing/Doeblin.lean`, `Chain.lean`), and the
arrow of causality gives uniformity along a chain. But a box has `2d` neighbours, and contraction needs the **summed** influence
below 1 (`pnp/CHAIN.md` 4, the honest limit). Questions:
1. Do the hand-over (`max(F_tw, F_e) ≥ 0.881` per box) and the conserved-flux carrier turn the `2d`-channel problem into one channel?
2. Can the neutral part be bounded by a block decimation, using the strict flip bound and the measured conditional mass, with
   sum `< 1` at an explicit `L`?
3. Physical units: which scale-uniform statement is needed, and how does the M1 hand-over at `L_*` supply the tick?

Marks: **Lean** (built, standard axioms; `Crossover/Neighbours.lean`, 5 theorems; `axioms-dy.log` now 32 Crossover theorems),
**paper**, **sketch**, **numerical**, **citation**, **open**.

## 0. Verdict in plain words

* **1. No.** The flux carrier reduces the problem to one channel only in a chain, where flux has one way out. In a box grid the
  flux entering one face can leave by any of the other `2d − 1`, so the odd (centre-charged) influence has `2d` channels like
  everything else. The hand-over's per-box ratio `√2 − 1 ≈ 0.414` keeps a column sum below 1 for **at most two channels**
  (`handover_column_sum_iff`, Lean). That covers a chain (two faces), not a grid with `d ≥ 2`. What a grid needs is a per-box
  suppression `F > log(2d)` (`column_requirement`, Lean): `log 8 ≈ 2.08` in `d = 4`, more than twice the duality floor `0.881`.
  **This is the first step that does not close.**
* **2. Only numerically, at typical fields.** With the measured conditional mass (about 4 per block; `ROUTE3.md` 7), the summed
  boundary influence on a central region drops below 1 once the region is at least 7 cells (in `L₁` block units, heuristic
  `b = 8` transfer) from the boundary: shell terms 290, 9, 0.3, 0.007 at distances 5 to 8. So a box of side about **15 cells** would
  do. That is measured at typical block fields only; Lemma C needs the supremum. The strict flip bound gives a sign, not a rate,
  and adds nothing to the sum.
* **3. Stated exactly, with one Lean core.** The needed statement is a one-box contraction `η ≤ η₀ < 1` at a **fixed physical box
  size** `ℓ_* = L_* a`, uniform in the lattice spacing `a` (the blocked theory at the M1 hand-over coupling `g_*`, with uniformly
  small corrections), and with the summed version over the `2d` neighbours. Then `m_phys ≥ −log η₀ / ℓ_*`
  (`phys_rate_of_uniform`, Lean). Doeblin can never supply this: its mass per box is at most `e^{−K}/(1 − e^{−K})`,
  `K = C β L_*^{d−1}`, which goes to 0 as `a → 0` (`neg_log_one_sub_le`, `doeblin_mass_tendsto_zero`, Lean).

## 1. Does the flux carrier reduce `2d` channels to one? (paper, Lean, sketch)

**Decomposition (paper).** The boundary data of a box split into the flux pattern through its faces, a function of the outside
(`cob_restrict_eq_cob_restrict_compl`, Lean), and the neutral rest. A Dobrushin influence `C_ij` of neighbour `j` on box `i` splits
into an odd part (the change of `i`'s law when the flux through the shared face changes) and an even part (neutral changes). The
centre symmetry of each face separates the two sectors exactly, as in the electric/twist sectors `Z_e = (Z ± Z_tw)/2`.

**Conservation (Lean, Dichotomy and FluxRate).** The flux through a box's boundary has even parity (`even_card_fluxCells`), so an odd
change entering through one face must leave through the box: odd influence is **transmitted** through the box, face to face.

**Why this gives one channel in a chain and not in a grid (paper).**
* *Chain* (`d = 1` in the transverse sense, two faces): what enters by one face leaves by the other. The odd sector is a single
  channel, carried by the transfer matrix (`HTF.md` 4, `flux_superadd`), and the hand-over gives each box a ratio `≤ √2 − 1`.
  Column sum over the two faces: `2(√2 − 1) ≈ 0.83 < 1`.
* *Grid* (`2d` faces): flux entering by one face can leave by any of the other `2d − 1`. The odd sector has `2d` channels, like
  the even one. With the hand-over ratio per channel, the column sum is `2d (√2 − 1)`, which is `≥ 1` already for 3 channels
  (`handover_column_sum_iff`: `k (√2 − 1) < 1 ↔ k ≤ 2`). "Only the flux-carrying direction transmits a non-neutral influence" holds
  when there is one flux-carrying direction (a chain); in a grid every face can be one.

**What a grid would need (Lean core, sketch application).** `column_requirement`: `k e^{−F} < 1 ↔ F > log k`. With `k = 2d = 8`:
a per-box suppression of the odd influence `F > log 8 ≈ 2.08`, i.e. `max(F_tw, F_e) > 2.08` at one box size, not just the duality
floor `0.881`. (In the electric channel this is plausible at large `L` in a confining theory, where `F_e` grows with the box. That
is a statement about the confined regime at scale `L`, the same circle as before. The small-torus run of `ONEBOX-CHECK.md` 8
measures `F_e(L)` at `L = 2, 4, 6`; see its result section.)

**And the neutral (even) part** needs its own column sum `< 1 − (odd part)`: per face a neutral influence `≤ 1/(2d)` minus the odd
share. In transfer-matrix terms that is a neutral decay `e^{−m L}` (times the number of low neutral states) below `1/8`, the neutral
gap at scale `L` again (`HTF.md` 4: the excess act `c(L)`).

**Two caveats on the identification (sketch).** (i) The hand-over ratios are torus partition-function ratios (annealed), while
`C_ij` is a supremum over outsides (quenched): `RATE.md` 5'. (ii) A twist ratio across a whole face pair is not the same as the
influence of one neighbour through one face. Both stay open, and both sit behind the counting failure above.

## 2. The neutral part by block decimation (numerical, paper)

* **Input** (`c9b-adjoint/ROUTE3.md` 7; numerical): conditional mass about 4 per block at `b = 2` (4.1 resolved at β = 2.3, mid
  snapshots; `≥ 3.6` at β = 3.5), heuristically transferred to `b = 8` (`m L₁ ≈ 4`). The shell terms of the boundary-to-centre
  influence, over `c C_A`, at cell distances `d = 5, 6, 7, 8`: **290, 9, 0.3, 0.007**.
* **Summed influence** (arithmetic on these numbers): from distance 7 on, `0.3 + 0.007 + (tail)` ≈ 0.31 `< 1`; from distance 6 on,
  ≈ 9.3 `> 1`. So, in Dobrushin-Shlosman form (the boundary of a box against its central region), the sum is below 1 when the
  central region keeps **at least 7 cells** from the boundary: box side about `2 · 7 + 1 = 15` cells (`L₁` units). That is the
  explicit `L` the question asks for, at typical fields.
* **Why it is not a certificate.** (a) Typical (sampled) block fields only; Lemma C needs the supremum over coarse data (condition A
  for every well-defined outside, still open). (b) The `b = 2 → 8` transfer is heuristic. (c) The strict flip bound `Z_tw < Z`
  contributes no rate: it is a sign. So the decimation gives an explicit candidate scale, not a bound.

## 3. Physical units: the statement needed, and the tick (paper, Lean)

**Statement needed (paper).** There are `m_phys > 0` and `β₀` such that for all `β ≥ β₀` the lattice gap satisfies
`m_lat(β) ≥ m_phys · a(β)`, with `a(β)` the lattice spacing in physical units (asymptotic freedom: `a(β) Λ → 0` as `β → ∞`). The
rate per tick `m_lat` goes to 0; the rate per physical length must not.

**How the tick is supplied (paper).** The M1 hand-over runs the weak-coupling RG from the cutoff down to the scale `L_*(β)` at which
the effective coupling reaches a fixed `g_*`. So `L_*(β) a(β) = ℓ_*` is a **fixed physical length**, and the blocked theory at
`L_*` is a lattice theory at coupling `g_*` with corrections that are uniformly small in β (the M1 input). The tick of the one-box
statement is `ℓ_*`. If the one-box contraction (with the `2d`-neighbour sum) holds for that blocked theory with `η ≤ η₀ < 1`,
uniformly in β and in the outside, then `phys_rate_of_uniform` (Lean) gives `m_phys ≥ −log η₀ / ℓ_*`.

**Why Doeblin cannot be the tick (Lean).** A Doeblin floor on the fine box at `L_*` has exponent `K = C β L_*^{d−1}`, and
`L_* = ℓ_*/a → ∞`. The mass per box is `−log η = −log(1 − e^{−K}) ≤ e^{−K}/(1 − e^{−K})` (`neg_log_one_sub_le`), which tends to 0
(`doeblin_mass_tendsto_zero`). Per physical length that is `≤ e^{−K}/((1 − e^{−K}) ℓ_*) → 0`. The uniform `η₀` has to come from the
**blocked** theory at `g_*`, where the box has a fixed number of block sites, not from the fine-lattice floor.

**So the scale-uniform statement is:** at the fixed coupling `g_*` (fixed physical size `ℓ_*`), for the blocked theory with its
uniformly bounded corrections, `Σ_{j ∈ 2d neighbours} C_ij ≤ η₀ < 1` for every well-defined outside. Section 1 shows the odd part
of that sum needs a per-box suppression above `log(2d)`. Section 2 gives a numerical candidate for the neutral part at typical
fields.

## 4. Status

| step | result | mark |
|---|---|---|
| odd/even split of the influence by face centre symmetry; flux parity forces transmission through the box | | paper; Lean (parity) |
| chain: one odd channel; `2(√2 − 1) < 1` | closed | Lean (`handover_column_sum_iff`) |
| grid: `2d` odd channels; hand-over ratio sums `< 1` iff `k ≤ 2` | **fails for `d ≥ 2`; first open step** | Lean |
| requirement: per-box odd suppression `> log(2d)` (`2.08` in `d = 4`) | open (beyond the duality floor) | Lean (`column_requirement`), sketch |
| neutral part by decimation: sum `< 1` from 7 cells, box side about 15 (`L₁` units) | candidate | numerical (typical fields), heuristic transfer |
| neutral part, certificate | open (Lemma C needs the supremum; condition A) | open |
| physical units: uniform `η₀` at fixed `ℓ_*` gives `m_phys ≥ −log η₀/ℓ_*` | closed (arithmetic core) | Lean (`phys_rate_of_uniform`) |
| Doeblin's physical rate → 0 as `a → 0` | closed | Lean |
| uniform one-box statement for the blocked theory at `g_*`, with the `2d` sum | open | open |

## 5. Files

* `NEIGHBOURS.md` (this note); `formal/ProofPhase/Crossover/Neighbours.lean` (new, 5 theorems); `axioms-dy.sh` extended,
  `axioms-dy.log` (32 theorems, standard axioms).
