# M1 at the stopping scale: the flat charged mode, and what M1 hands over (m1-tools, 2026-11-22)

Brief (coordinator): with the decision that reflection positivity of the bare measure suffices (`LimitRP` from
`rp_gaugeMeasure`; the block-law inputs `BlockGapBddW`, `LawGapBddW`, `ObsTransferPhysTW` are decay and transfer
statements), finish the bypass items: the flat charged mode of `MILESTONE-1.md`; the hand-over at the stopping scale,
checked against the form `BlockGapBddW` / `ObsTransferPhysTW` need. Read for this note: `formal/ProofPhase/Objects.lean`
(`RPBlocking`, `LimitRP`), `Assembly.lean` (`BlockingFamily`, `blockedLaw`), `V4/Gap.lean`, `V3/W1Route.lean`,
`OneBox/Torus.lean` (`OneBoxLaw`), `PROOF-BLUEPRINT.md` P3.5, P4. Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **The flat charged mode does not matter.** Before a sheet becomes irregular it is a regular background. There the
   charged mode is a long-wavelength mode, part of the block field, not a fluctuation at the current scale, and
   Balaban's Hessian on `ker Q` stays positive (Poincaré gap of order 1, spin term `O(ε)`). During its window the sheet
   is a large-field region, bounded by its action, never expanded around. After the window it is erased. (Sketch.)
2. **What M1 delivers at the stopping scale `L_*` (scale `K`, `g_K ≤ γ`):**
   * **(a) the law** of the block variables `(V_K, τ_K)` (SO(3) block field, closed Z2 layer) in Balaban's inductive
     form ([III] (2.18), with the records of the old design gone), with his bounds;
   * **(b) the ultraviolet transfer:** conditional on the block variables at `L_*`, fine observables of bounded physical
     extent decouple, with block approximants. This is the `L_*` half of `ObsTransferPhysTW`; it follows from Balaban's
     polymer representation of the fluctuation integrals below `L_*` (paper-level, not written out).
   
   It does **not** deliver `BlockGapBddW`. That is the infrared input at `L₁`, obtained through the one-box route
   (`OneBoxLaw`, a Dobrushin-type influence bound), which needs coupling of order one, the certified window of c3c. M1
   stops at `g_K ≤ γ` small. The segment `L_* → L₁` is the crossover, P4 of `PROOF-BLUEPRINT.md`, "open; the core",
   and is not M1's. This matches the blueprint's split (P3.5: lattice spacing `→ L_*`, small coupling;
   `L_* → L₁`, a fixed number of steps at coupling of order one).
3. **Two interface changes are needed in the formal assembly** (not in M1's folders; for the coordinator):
   * `BlockingFamily T` is `RPBlocking`, which requires `theta` (commutes with the reflection) and `half`
     (half-locality). M1's blocking with the global decoder has neither. Among the consumers of `BlockGapBddW` and
     `ObsTransferPhysTW`, only the RP theorem (`blocked_wilson_rp`) and the blocking constructions (`Noisy`,
     `MulNoise`, `RouteA/Blocking` composition) use these fields. So the gap and transfer statements can be restated
     for any measurable blocking.
   * The block field is SU(2)-valued in the assembly; M1's is SO(3) × Z2. An SU(2) encoding exists and is
     deterministic and measurable: lift each SO(3) bond canonically and multiply by `z_c ∈ Z2`, with `dz = τ` fixed by
     a Z2 axial gauge (and a fixed representative per twist class on the torus). Gauge-invariant local observables of
     the encoding are local functions of `(V, τ)`.

## 1. The flat charged mode (sketch)

* **Regular phase** (`k < s`, curvature `< ε_k`): the tube is part of Balaban's background `U_k(V)`. The fluctuation
  operator on `ker Q_{k+1}` is `Σ_p |DA(p)|² + O(ε)‖A‖² ≥ (c_P - O(ε))‖A‖²` (`POINCARE.md`, Lemma LP); the spin term
  `[F, ·]` of size `ε` cannot close the Poincaré gap. The charged lowest-Landau-level mode of `MILESTONE-1.md` lives on
  the tube's cross-section, `T_k ≫ 1` blocks wide. Its block averages do not vanish, so it is a mode of the block
  field, carried to the next scale, not integrated at this one.
* **Window** (`s ≤ k ≤ s + window`): the sheet's neighbourhood is a large-field region. Balaban bounds it by
  characteristic functions, positivity of the action, and group integrals bounded by the fibre mass (E7, E7.J). No
  Gaussian expansion around the tube is made, so a quartic direction is harmless.
* **After the window:** erased from the coarse state (`BYPASS.md` 1).

## 2. The hand-over, checked against the consumers

| consumer | what it needs | M1 provides | status |
|---|---|---|---|
| `LimitRP` | RP of the bare measures | — (bare `rp_gaugeMeasure`) | Lean, independent of M1 |
| `ObsTransferPhysTW` | conditional decoupling of fine observables given the block variables, block approximants with oscillation and Lipschitz bounds, uniform in the level | the `L_*` half: decoupling given `(V_K, τ_K)` from Balaban's polymer representation below `L_*`; the remaining fixed number of steps `L_* → L₁` belongs to P4 | paper-level claim, not written out; interface change 3 needed |
| `BlockGapBddW` / `LawGapBddW` via `OneBoxLaw` | a one-box influence bound for the law at `L₁` (strong coupling, certified window) | nothing directly: the law at `L_*` is weak-coupling, where one-box influences are not small | **not M1's**: the crossover P4 |
| `EnvelopeW` (P3.5, the `→ L_*` segment) | upper bounds of the effective potentials at `L_*` | Balaban's upper bounds for the law in inductive form | paper-level (as P3.5 already says: "plausible from Balaban") |

## 3. Status

Items 1 and 2 of the round are done at the levels stated; nothing failed inside M1. The hand-over makes plain that the
mass-gap theorem still needs the crossover (P4) and the two interface changes, both outside M1.

**Update (2026-11-22, `SKETCH-STEPS.md` 2):** the claim that M1 delivers the `L_*` half of `ObsTransferPhysTW` (0.2(b), table row 2) is withdrawn to **open**: it needs Balaban's induction with a permanent frozen region of arbitrary content, uniform over the number of steps; it is the `L_*` segment of blueprint P5.2.

**Update (REVIEW-2 G4, G5):** no SU(2) encoding is proposed (it is not gauge covariant). The block state is `(V_K, τ'_K)` with gauge-invariant observables. What M1 delivers is stated in `REVIEW2-RESPONSE.md` 5.
