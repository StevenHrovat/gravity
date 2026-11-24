# W2 narrow run: result (pre-registered part; W2-PREREG.md section 5, amendment A6), 2026-11-23

Run: 04:49:21-07:04:36, 6 fused launches (β = 2.3, 3.5; κ = 16; `ℓ = 6`; `θ = π`), 34 boxes (17 per β), 80 coupled pairs per box,
2.25 GPU-hours (projection 1.55 h, band 1.4-2.9 h; `PROJECTION.md` 8). Analysis: `py analyse_w2.py runs/narrow/launch_b*.json`
-> `runs/narrow/analysis.json` (CPU). Exploratory additions are reported separately (`EXPLORATORY-SETTLING.md`, and the proxy
below), not here.

## Verdicts, scored as written

| β | `WL-S` | `WL-Q` (this blocking) |
|---|---|---|
| 2.3 | **UNRESOLVED** (kill rule not triggered) | **not refuted** |
| 3.5 | **UNRESOLVED** (kill rule not triggered) | **not refuted** |

* **Kill rule** (`R_low_sub ≥ 1` at 2σ on the sampled boxes): not triggered. The largest observable-level column sum on any box,
  even without noise subtraction, is 0.65 (A2, a Haar-random block field); with the noise floor subtracted, at most 0.12.
* **`WL-Q`** (some adversarial box with `R_low_sub ≥ 1` at 2σ): no. Largest adversarial value 0.085 (A4, β = 3.5).
* **No pass verdict was possible** (amendment A6): the coupled-chain upper side saturates (the two chains disagree on 89-95 % of
  the box links at the plateau), and the photon gate G2 was not run (no U(1)).

## Numbers (start 0; per box, observable-level influence of one perturbed link, column sum over the shell, per box link)

| β | class (boxes) | `R_low` raw, max | mean `k_low` / noise floor | `R_low_diff` (unbiased, ± jackknife), range | `k_Y` above noise | disagreement plateau |
|---|---|---|---|---|---|---|
| 2.3 | sampled (8) | 0.38 | 0.172 / 0.168 | −0.009 to 0.029 (all within 2σ of 0) | 0.031 | 0.91 |
| 2.3 | A1-A6 (9) | 0.65 | | −0.079 to 0.037 | 0.008-0.030 | 0.91-0.95 |
| 3.5 | sampled (8) | 0.25 | 0.100 / 0.069 | **0.013 to 0.112**, 5 of 8 above 2σ, largest 0.112 ± 0.037 | 0.057 | 0.89 |
| 3.5 | A1-A6 (9) | 0.64 | | −0.071 to 0.078 | 0.015-0.031 | 0.89-0.93 |

Reading:
* At β = 2.3 the measured box influences are at the noise floor: perturbing one outside link or one block variable by `π` changes no
  box plaquette average detectably. At β = 3.5 the sampled boxes show a small influence above the noise (column sums about
  0.01-0.11): the box law is more sensitive to its boundary at the weaker coupling, which is the direction a longer conditional
  correlation length would give. Both are far below the kill threshold of 1.
* `k_low` is a **lower** estimate of the box influence (largest shift of one plaquette average, not the total-variation distance
  of the box law), so small values do not show that the box influence is small; they show only that this observable class does not
  see a large one.
* **Caveat on the noise floor for adversarial boxes:** the floor compares chain A of start 0 with chain A of start 1. For boxes
  whose block field or outside was modified (A1-A6), start 0 begins farther from the conditional law than start 1, so the two starts
  can differ systematically, the floor is inflated, and `R_low_diff` is biased low (several adversarial values are negative, e.g.
  A1, A2). The raw `R_low` (noise included, maximum 0.65) is the conservative number for the `WL-Q` test, and it is below 1
  everywhere.
* **Caveat on A3 (found by the exploratory adaptation check, `SETTLING-RESULT.md`):** the fine field did not follow the twisted
  block field (alignment with the flipped coarse links about 0 at `T/2`, against 0.96 elsewhere), so the A3 boxes did not carry a
  fine-level sheet. The `WL-Q` test through A3 is therefore weaker than intended: it tests a twisted block field, not a box
  containing a sheet. A6 (a sheet in the frozen outside, attached to the box) is the instance that does carry one.
* Not measured (amendment A6 and the saved data): the conditional-mass profile `m` (per-link disagreement maps were not saved),
  the adversarial column sums over box translates `C_low` (one box per instance; `R_low` stands in), the rarity cluster statistics
  on the full lattice, and the photon gate.

## What this means for (WL) and the crossover

The narrow run gives **no evidence against** the supported form of (WL) at β = 2.3 and 3.5 for this blocking (no observable-level
influence near 1, no adversarial failure), and **no evidence for it either**: the upper side was out of reach, as pre-registered.
The one quantitative signal is a small but resolved boundary sensitivity at β = 3.5 (column sums about 0.1 at the observable
level), absent at β = 2.3.

## Measured quantity -> the statement it would discharge (owner's reporting rule)

The owner: "What we want to get out has to be provable in its statement of existence, otherwise we can't get anything useful
out." The boundary conditions of every measurement here (the "DB" the system is measured against): a frozen outside = a window of
an equilibrium `16⁴` Wilson configuration at the same β (non-periodic frame of side 14 around the `6⁴` box), modified only as
stated; a block field `Y` on every coarse link whose blurred path meets the box (sampled given that outside, then modified for
A1-A4); soft constraint κ = 16 with the unprojected one-step good blocking; perturbation of one link by an SU(2) rotation of angle
π. Nothing in this run is a certified bound: a sampled lower estimate can only **refute** a statement (if it exceeds the threshold
at 2σ); discharging one needs an upper bound with error control (a certified computation), which this run does not give.

| measured quantity | statement it bears on (Lean name / `WL.md` condition) | direction it can act | boundary conditions | outcome here |
|---|---|---|---|---|
| `R_low` on sampled boxes (observable-level column sum) | good-box column condition: `WL.md` 2.2 (G), i.e. `CouplingDS.lean`'s (I)+(K) (`DSWeights`) on good boxes; and the one-box sum in `P4StarInv` (`IsInfluenceBoundOn`, `OneBoxSum`) | refute only (lower bound) | equilibrium outside; sampled `Y`; 32 sampled shell links | max 0.38 raw, ≤ 0.11 above noise: **refutes nothing** |
| `R_low` on adversarial boxes (stands in for `C_low`) | quenched form `WL-Q` (`WL.md` 2.1); the worst-case quantifier of `P4Star`/`P4StarInv` | refute only | A1-A4: modified `Y`; A6: outside with an attached centre-vortex sheet; pool variant: worst of 8 outsides | max 0.65 raw: **refutes nothing** (`WL-Q` not refuted for this blocking) |
| `k_Y` (block-variable influence) | quasi-locality of the projection: `V4.StageTwoW` clauses (a), (b) | refute only | as the sampled boxes; 8 block variables | 0.008-0.057 above noise: **refutes nothing** |
| coupled-chain disagreement plateau (`R_up` side) | (I)+(K) with the measured coupling (upper side) | would **support** (I) if well below the box size (an upper estimate, but statistical; a discharge needs a certified coupling bound) | all boxes | 89-95 % of links disagree: **saturated, discharges nothing** |
| conditional collar mass `m` | `WL.md` 10.2 (A), attenuation and collar width | would bound (A) | — | **not measured** (per-link disagreement maps not saved) |
| bad-cluster connectivity on the full lattice | `WL.md` 10.2 (B)/(C), subcriticality | would bear on (B)/(C) | — | **not measured** in the narrow run |
| single-link proxy `κ̃_b`, `D_b` (`lever_proxy.py`) | fine-bad classification of `INFLUENCE-BAD.md` (first-order, Pinsker; a single-site Dobrushin quantity, not the box influence) | **diagnostic** (not a bound on any stated hypothesis) | saved chain-A snapshots at `T/2` and the end, with their outside and `Y` | reported separately |
| box plaquette averages, MH acceptance | sampler health | **diagnostic** | all | equilibrium-consistent; acceptance 0.83-0.92 |
| run time per launch | projection rule (`PROJECTION.md` 8) | **diagnostic** | — | 2.25 h against 1.55 h |
| settling times (`EXPLORATORY-SETTLING.md`) | none | **diagnostic, exploratory** | — | reported separately |
