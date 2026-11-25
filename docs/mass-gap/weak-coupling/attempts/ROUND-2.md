# Attempt round 2: summary (2026-11-21)

Four attempts, run in parallel under `RULES.md` (with the round-2 additions), each aimed at one piece that round 1 left open. The
owner's α pointer (`../PREP.md`, last section) reached all four as context. Notes in each folder; Lean in `../../formal/Attempts/R2/`,
all verified by the coordinating session (builds, no `sorry`, standard axioms only; certificate entries re-run where named).

| attempt | folder | commit | Lean | one line |
|---|---|---|---|---|
| A, a certified worked example | `r2-2d/` | 630ce78 | `TwoD.lean`, 23 theorems | the reduction closes, end to end, in 2D compact U(1) |
| B, a reflection-positive coupling | `r2-coupling/` | 7d15cbd | `CouplingSwap`, `CouplingSplit`, 21 | a new torus-decay engine for strongly coupled theories; no weak-coupling window |
| C, H2 by curvature at L₁ | `r2-curvature/` | 961e081 | none (numbers) | the curvature window misses a stand-in for the blocked theory by a factor of about 2 |
| D, H1 by step scaling | `r2-stepscaling/` | 84dc986 | `StepScaling`, `StepScalingH1`, 24 | H1 reduces to one weak-coupling statement; exact coefficients are not needed |

## Verdict

**No attempt proves the open hypothesis, but the round turns round 1's single obstruction into a map with three named pieces**, and
for the first time the chain from "one box forgets its boundary" to "exponential decay" closes on a real example (A).

## What each attempt established

**A (2D compact U(1), β = 2).** An explicit flow coupling whose expected cost is enclosed by interval arithmetic gives the one-box
influence bound below 1 for every boundary flux at once: γ ≤ 0.9923, 0.9062, 0.8338 at box sides 10, 11, 12 (6.0–7.2 confinement
lengths). Lean (`twoD_U1_decay`, `_limit`) turns the certified numbers, its one hypothesis, into exponential decay on every even torus,
uniform in N, and in infinite volume. The bound is not sharp (the rate is about 70 times below the natural scale), it is one coupling
only, and nothing transfers to 4D (the 2D box law reduces to independent plaquettes; the Bianchi identity forbids that in 3D and 4D).
What it calibrates is where the method switches on: certified at about 6 confinement lengths, against a proven floor of about 4.2.

**B (reflection-positive replicas).** The swap identity and the transfer lemma (Lean) show that any swap argument recovers exactly the
covariance the coupling leaves unscreened. The **soft swap** keeps two replicas independent and labels each plaquette with the part of
its weight shared by both (a Nummelin-type split); the marginal is exact, reflection positivity holds, and swapping across a wall of
labelled plaquettes preserves the measure. Theorem S: torus decay for every compact group at strong coupling (SU(2) β < 0.0064),
re-proving the Osterwalder–Seiler gap by a new route; Theorem S′: the same for **any finite-range effective theory with nearly flat
positive local factors**. Optimality (Lean): no construction beats the label. At weak coupling no lattice-scale swap can work: the
obstruction is ultraviolet and the same for SU(2) as for three photons, so it would give light a mass.

**C (curvature at L₁).** In Wilson units the single-link W₁ condition, which is coarse Ricci curvature of the heat bath (Ollivier),
holds for β < 0.124 (proved) and never beyond π/16, i.e. α_s ≥ 16/π²; Bakry–Émery gives β < 1/12 (matching the Shen–Zhu–Zhu condition
under an inferred normalisation); the centre-blind channel allows β_A ≈ 0.29–0.39. This corrects the "tiny windows" of
`../H2-CURVATURE.md`. A two-coupling stand-in for the blocked theory at 3/√σ (fundamental coupling fixed by σ, adjoint by the glueball
mass) gives β_A ≈ 0.50: a factor of about 2 too large, closing at L₁√σ ≈ 3.3–3.9, where the 2D U(1) follow-up put the H1/H2 border.
The stand-in's own error is not quantified and probably dominates. The Z₂ test shows why σ must enter: a glueball-only match would
certify deconfined Z₂.

**D (step scaling).** With the scale set by a measured coupling (L₁ is where α_s reaches α*), H1 follows from bounded running plus a
control hypothesis (Lean: `effectiveConvergence_of_stepScaling`, `gap_of_stepScaling`). The exact one- and two-loop coefficients enter
only asymptotic scaling (`scaling_drift`), not H1 or the gap: round 1's sharp-coefficient obstruction binds only when the scale comes
from the bare law. The control hypothesis splits into a transport lemma (proved on paper: relative closeness of densities survives any
blocking and passes to every conditional law, uniformly in the boundary) and **one open statement W_p**: at a fixed weak-coupling scale,
the effective density converges in relative sup norm, large fields included. That is the Balaban programme's large-field step; the
OpenAI construction supplies the small-field half.

## The map after round 2

The full proof now has three pieces, each stated precisely:

| piece | statement | owner of the difficulty | status |
|---|---|---|---|
| **W_p** (quantum half, H1) | weak-coupling effective densities converge, large fields included | Balaban's large-field control; OpenAI covers small fields | open, known type of analysis |
| **Crossover** | the limit theory, blocked N times from weak coupling, lands in a strongly coupled window (Theorem S′ or the curvature window) at L₁ | nobody: α_s between about 0.5 and 3.5 is covered by no method | open, the true non-perturbative core |
| **Robustness on the torus** | H1 plus a strongly coupled effective theory (S′) gives decay of the full theory, without the boundary-uniform `LimitGDS_W` | ours | open, a finite lemma (B's next step) |

D moved the running through the crossover out of H1 and next to H2: it is a property of one theory, not of a limit. A, B and C each
place the switch-on where α_s reaches order one (A: about 6 confinement lengths in 2D; C: 3.3–3.9/√σ; B: strong coupling only).

## Leg B so far (interim, β 2.3–2.5; the pre-registered analysis follows after β 2.6 and 2.7)

The photon gate passes (evaluated early on its complete inputs, `../../lattice/PREREG-BOUNDARY.md`). The SU(2) decay length scales
from β 2.3 to 2.4 (ξ√σ = 0.403 ± 0.008, 0.406 ± 0.021) and not to 2.5 (0.225 ± 0.007), so Q1 as pre-registered currently fails. A
reading made after seeing the data, not pre-registered: at β 2.5 the decay has a fast lattice-scale part and a slower physical tail,
and the fixed fit window catches the fast part. If β 2.6 and 2.7 confirm it, the data show the same split as the map above: an
ultraviolet part (round 1's g² per link, W_p's territory) and a physical part (the crossover).

## The owner's α pointer, as the round read it

Every scheme in which the criteria can be expressed puts the switch-on at α_s of order one (C: threshold α_s* = 16/π² from lattice
geometry, crossing at α_s ≈ 1–2; D: per-doubling bookkeeping holds up to α_s ≈ 0.62; B: with aligned replicas α drops out and the swap
sees the coupling only through its running). No attempt found a deeper constant, and none claims one. Light's α = 1/137 is far below
every window and never runs towards one: in the owner's words, no path prescribed.

## Proposed next steps, from the attempts

1. B: prove the torus robustness lemma, so S′ at L₁ can serve as H2.
2. D: formalise the transport lemma and per-volume H1, so H1 is exactly W_p.
3. C: fit the blocked SU(2) action (fundamental and adjoint couplings) at L₁√σ ∈ {2, 3, 4} on the GPU, pre-registered, and evaluate
   both C's and B's criteria on it.
4. A: certify β = 3 at ℓ = 15, so the switch-on size is certified at two couplings.
