# R2 repaired: long-lived large-field regions paid by their own action (m1-tools, 2026-11-22)

Brief (coordinator, after `REGULAR.md`): attempt the repair named there.
1. A decomposition lemma for moderate irregular configurations (localised cores / conserved-flux sheets / growing
   parts): precise statement, proof or exact failure, uniqueness, measurability, oscillation.
2. Balaban's entropy induction (E8) extended to regions that live as long as their sheet is larger than a block, paid
   by their own action, with the counts in physical units and rigorous lower bounds for the suppression.
3. Every conserved-flux sheet ends correctly: released, or central and sent to the closed Z2 layer.

Read for this note: [16] pp. 272-274 ((67)-(71), now local), [V] (1.76)-(1.88) as recorded in `D-N.md`, `P2-PRIME.md`
Lemma F. Lean: `formal/ProofPhase/M1/Footprint.lean`. Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **The decomposition lemma, as posed, is not true in a useful form, and it is not needed.** The three classes are
   descriptions of how a configuration *behaves* under blocking, not a partition of configurations:
   * a configuration is in general a superposition (a sheet plus a core plus a growing background), so a split is a
     choice;
   * a sheet whose flux is near `ε` can drift in and out of irregularity as the background adds to it, so classes can
     alternate;
   * a measurable split would need thresholds and tie-breaks, exactly where earlier versions broke.
   
   What the bookkeeping needs is weaker, and it holds. Each irregular coarse cube is attributed to the large-field
   region whose physical support it meets (a function of the sequence of regions, which is a summation index in
   Balaban's representation, not of the configuration). Every attributed region then has a **summed footprint over its
   life** bounded by a constant times its size at birth, plus a polylogarithmic few-cube phase. Oscillation is
   allowed: a region that becomes regular is renormalised (released), and a later irregularity is a new birth with its
   own suppression, as in Balaban's own scheme.
2. **E8 extends.** Balaban's per-step cost is a sum over steps of the current domain sizes ([V] (1.81): `Σ O(1) M^d
   R_n^{d+1} d'_n`). His control "lifetime `≤ R_j`" serves only to bound that sum by `R_j` times the birth size. For a
   region with physical support of `n_s` sites at birth, the covering number `k` steps later is
   `N_k ≤ 3^d (2 n_s L^{-k} + 1)` (Lemma F of `P2-PRIME.md`). So the summed footprint over any life of `n` steps is
   `≤ 2·3^d n_s/(1 - 1/L) + 3^d n` (**Lean** `footprint_sum_le`). The extended phase lasts `≤ log_L n_s` steps, and
   `n_1` is the length of the few-cube phase (at most `2·3^d` cubes) that follows.
   That phase lasts `≤ log_L(C_d M R) + 0.4 log g^{-2}`: until the sheet is smaller than a block, then R1. This is
   polylogarithmic and `≤ R_j`, so the charge is at most Balaban's own bound. The suppression per irregular coarse
   plaquette is `exp(-¼ p0(g_s)²)`, **now read** in [16] (69)-(71): the action of the background in the four blocks
   around an irregular coarse plaquette is at least `¼ |V(∂p') - 1|²/g²`, given regularity of the finer field. Balaban's
   win condition pays the charge.
3. **Counts in physical units converge.** A region still extended at scale `k` (more than `2·3^d` cubes) was born with
   `n_s ≥ L^{k-s}/2` sites, hence suppression `exp(-c p0² L^{k-s})` against `L^{d(k-s)}` positions per scale-`k`
   cell. A region in its few-cube phase is at most `n_1` steps older than its extended phase: `L^{d n_1} e^{-c p0²} ≪ 1`
   because `p0² ≫ n_1 log L`. **No F1 trap.** (The few-cube phase is at most `2·3^d` cubes.)
4. **Endings are clean.** A sheet smaller than a block is closed. Its flux class `e^{iφ n·σ}` splits into a central part
   and a remainder:
   * a thin central part has bare `τ = −1` plaquettes: closed Z2 layer, decoder;
   * a thick central part is invisible in SO(3) (`Ad(−1) = 1`): erased;
   * the remainder is an SO(3) rotation by `2φ mod 2π`, moderate. With a gauge representative supported in its spanning
     3-ball it is a localised core: R1, regular, released.
   
   Open sheets end where the non-central flux spreads: localised (R1) or deep (excised, R3). **Nothing is left over.**
5. **Status: R2 closes on paper in the repaired form** (attribution plus footprint-weighted lifetime instead of
   "regular within the delay"), with one **Lean** step. It uses R1, R3 (excision of deep parts), Lemma F, [16] (71)
   (read), and Balaban's win condition. It modifies E8 in one place: the life control. That modification is a re-reading
   of [V] (1.80)-(1.85), not re-done line by line.

## 1. Why a partition is not the right object

* **Superposition.** In a moderate region, `a = a_core + a_sheet + a_smooth` (Lie algebra, relative to a regular
  reference) is one of many decompositions; the reference itself is a choice.
* **Instability:** a sheet with `φ ≈ ε_k` plus a background of size `ε_k` can be regular at one scale and irregular at
  the next (`ε_k` also runs).
* **Measurability:** a deterministic split would need thresholds on `φ`; ties at the thresholds are where the cut and
  the act broke earlier routes.
* **What is used instead:** Balaban's representation sums over admissible sequences of regions and restricts
  configurations by smooth characteristic functions (measurable, fuzzy, factor-2 thresholds). The attribution of a
  coarse cube to the region whose physical support it meets is a function of that summation index.

## 2. The extended entropy induction

* **Birth.** A region is born at scale `s` when `χ^c_s` holds on its cubes (some plaquette `> ε_s`), with the finer
  field regular there (otherwise it was born earlier). By [16] (69)-(71) (the proof uses only [12] (50), (53), valid in
  any dimension), each irregular coarse plaquette `p'` gives
  `(1/g_s²) A(U)|_{4 blocks of p'} ≥ ¼ p0(g_s)²`. Blocks are shared by at most `C_d` plaquettes, so the region's
  suppression is `≥ exp(-p0² N_s/(4 C_d))`, with `N_s` the number of its cubes (each cube holds an irregular plaquette).
* **Footprint.** The physical support of a connected region of `n_s` scale-`s` sites meets at most
  `N_k ≤ 3^d (2 n_s L^{-(k-s)} + 1)` cubes of scale `k` (Lemma F, cube side `L^{k-s}` in scale-`s` units).
  **Lean** `footprint_sum_le` (with `A = 2·3^d n_s`, `q = 1/L`, `B = 3^d`):
  `Σ_{k<n} N_k ≤ 2·3^d n_s/(1 - 1/L) + 3^d n`.
* **The few-cube phase** (`N_k ≤ 2·3^d`, support of diameter `≤ C_d M R_k`): at most `log_L(C_d M R_k)` steps until
  the support is smaller than a block, then at most `n_loc ≈ 0.4 log g^{-2}` steps of R1. So `n_1 ≤ log_L(M R) + 0.4 log g^{-2} ≤ R_j` (for `R_j ≥ log g^{-2}`, or
  with the retuned delay of `D-N.md`).
* **The charge** is `Σ_k O(1) M^d R^{d+1} N_k ≤ O(1) M^d R^{d+1} 3^d (2 n_s/(1 - 1/L) + log_L n_s + n_1)`,
  against `p0² N_s/(4 C_d)` with `n_s ≤ (M R)^d N_s`. Since `log_L n_s + n_1 ≤ 2R ≤ 2R N_s`, the win condition `A_1² p0² ≥ O(1) M^d L^{d+1} R^{d+2}` ([V] (1.82))
  covers it with room.
* **Insertion into [V] (1.80)-(1.85):** Balaban's factor controls a domain for `K ≤ n0 - j + R_j` steps only to bound
  `Σ_steps d'_n` by `R_j d'_j`. The footprint bound gives `Σ_steps d'_n ≤ C_d (1 + R_j) d'_j` for any lifetime,
  so the same factor controls the whole life. Paper (re-reading), not re-done line by line.

**Plainly:** the constant `3^d` per step of life is what makes the life length matter. The extended phase lasts
`≤ log_L n_s` steps, and the few-cube phase lasts `n_1` steps; both are paid by the birth suppression `p0² N_s`.

## 3. Counts in physical units (the F1 check)

* **Extended at `k`** (`N_k > 2·3^d`): by the contrapositive of Lemma F, `n_s ≥ (L^{k-s}/2)(N_k/3^d - 1) ≥ L^{k-s}/2`,
  so a region still extended `j` steps after birth has `N_s ≥ n_s/(MR)^d ≥ c L^j/(MR)^d`. Count per scale-`k` cell: `Σ_j L^{dj} C^{N_s} exp(-p0² N_s/(4C_d)) ≤
  Σ_j L^{dj} exp(-c p0² L^j)`, which converges.
* **Few-cube phase** (`N_k ≤ 2·3^d`: support of diameter `≤ C_d M R_k`): alive at most
  `n_1 = log_L(C_d M R) + n_loc` steps after leaving the extended phase:
  `Σ_{j ≤ n_1} L^{dj} exp(-p0²/(4C_d)) ≤ exp(d n_1 log L - p0²/(4 C_d)) ≪ 1`, since `p0² ≫ n_1 log L`.
* **Released regions:** Balaban's R-term bookkeeping ([III] (2.30)-(2.33)), as for all his regions.

## 4. Endings

A conserved-flux sheet's flux class is the conjugacy class of the holonomy around it, `e^{iφ n·σ}`, `φ ∈ [0, π]`.
* **`φ` moderate (`< r0`):** while extended, carried (section 2). When it is smaller than a block, its holonomy is
  carried by a gauge representative supported in a spanning 3-ball of radius `≤ 2`: a localised core, so R1 makes it
  regular and it is released.
* **`φ` deep but `π - φ` moderate** (near-central): in SO(3) the rotation is `2φ - 2π`, moderate, handled as above. The
  central part sits either in bare `τ` (thin: plaquettes past the equator, closed by the decoder, counted on the
  1-skeleton, `CLOSING.md`) or nowhere (thick: `Ad(−1) = 1`, erased, `BYPASS.md` 1).
* **`φ` deep and not near-central:** deep plaquettes, excised for one step (R3); what remains is moderate or regular.
* **Open sheets:** at its end a non-central flux is not conserved. The end region is localised (R1) or deep (R3).

Nothing remains outside these cases: every flux class is central, moderate, near-central, or deep.

## 5. Status

* Item 1: decomposition as a partition **not proved and not needed**; replaced by attribution (section 1).
* Item 2: **paper + Lean step**; the insertion into [V] (1.80)-(1.85) is a re-reading.
* Item 3: **paper**.
* R2 in `M1-PLAN.md`: closes in the repaired form, given R1, R3 and Lemma F.
* R5: [16] (71) read and pinned (section 2); `EXTERNAL.md` row 20 can cite it directly.
