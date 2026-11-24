# Pre-registration: the adjoint half on Leg C's fitted blocked actions (cycle 2, workstream A, 2026-11-22)

**Status: written 2026-11-22 around 02:00 (WEST), before any SU(2) fit output of Leg C was read.** What I had seen of Leg C when writing
this: its PREREG and analysis code; the queue log (`queue_blocked.log`); the photon-gate log (`photon_gate.log`, U(1) β = 1.1, which
includes the U(1) fitted couplings: q1 ≈ 2.4, q2 ≈ −0.22 to −0.24 at f = 1/2); and the progress lines of the running SU(2) β = 2.3
log (coarse plaquette values at 10 of 80 measurements; no fits). I did not open `su2_*.npz`. The script `evaluate_adjoint.py` was
tested only on the CPU pipeline-test files (`../../attempts/r3-blocked/cpu-test/`, 6⁴, not physics) and on the U(1) GPU photon-gate run.
Any change after the first SU(2) evaluation is marked "after data" in this file.

## What is evaluated

Leg C (`../../attempts/r3-blocked/PREREG.md`) fits the blocked SU(2) action per plaquette p and 1×2 rectangle R as

  `S = Σ_p [β_F t_p + β_A (4t_p² − 1)/3 + β_T (2t_p³ − t_p)] + Σ_R β_R ½tr V_R`,  `t_p = ½ tr V_p`,

base fit {β_F, β_A}, extensions with β_T (spin 3/2), β_R (rectangles), or both; jackknife errors (≥ 20 blocks). Under the flip of one
link `V_l → −V_l` (the centre Z₂ of that link) `t_p → −t_p` on its plaquettes and `½tr V_R → −½tr V_R` on its rectangles. So every
fitted factor splits uniquely into

* a **centre-blind (adjoint) part** (invariant under every single-link flip; a function of the SO(3) images of the links):
  plaquette `f_e(t) = β_A (4t² − 1)/3`; rectangles: none;
* a **centre-charged part** (odd under the flip of any one link of the factor): plaquette `f_o(t) = β_F t + β_T (2t³ − t)`; rectangle
  `β_R ½tr V_R`.

This is the decomposition `V = V⁰ + V¹` of `NOTE.md` §1 (the centre average over Z₂^{supp x}), for the fitted factor families.

## The quantities (all per point, per fit, jackknifed)

1. **Adjoint half, sup (TV) form** (`NOTE.md` §1, Lean `ProofPhase.Adjoint.CentreSplit`):
   `a_TV(λ) = Σ_{pairs (n_P, n_R, d)} tanh(n_P o_e / 2) e^{λ d}`, `o_e = osc_{[−1,1]} f_e = (4/3)|β_A|`.
2. **Centre half, sup (TV) form:** `c_TV(λ) = Σ_{pairs} tanh((n_P o_o + n_R o_R)/2) e^{λ d}`, `o_o = osc_{[−1,1]} f_o`,
   `o_R = 2|β_R|`.
   Pair table `(n_P, n_R, d)`: Leg C's infinite-volume enumeration (`analyse_blocked.pairs()`, 62 neighbours, 18 sharing a plaquette).
   **Halves criterion** `H_TV(λ) = a_TV(λ) + c_TV(λ)`; by `limitDprime_of_halves` (Lean) `H_TV < 1` implies D′_λ (`LimitDprime`) for
   that action. Reported: `H_TV(0)`, `λ*_H = sup{λ : H_TV(λ) < 1}` (0 if none).
3. **Adjoint half, W₁ form (linearised, SU(2) sites, geodesic S³ cost)** (`NOTE.md` §2): `a_W = 18·(8/3)·k_A·|β_A|`,
   `k_A ∈ [0.0531, 0.0722]` (C's bracket, `../../attempts/r2-curvature/NOTE.md` §2.3; sharpened before data, see the amendment); **centre half, W₁:**
   `c_W = 18 (k_F |β_F| + k_T |β_T|) + 90 k_F |β_R|`, `k_F = 8/(9π)`, `k_T ∈ [0, 0.1443]` (Leg C's constants). `H_W = a_W + c_W`
   (hi: upper constants, lo: lower). This is C's W1 criterion split into its two halves; it is **linearised** (no proved bound at
   these couplings, `NOTE.md` §2.4).
4. **Windows and gap factor:** the largest adjoint coupling the measured centre half leaves room for:
   `β_A*_TV = (3/2) artanh((1 − c_TV(0))/18)`, `β_A*_W = (1 − c_W)/(18·(8/3)·k_A)` (bracket); and `Y/X = |β_A| / β_A*` (∞ if the
   centre half alone is ≥ 1).
5. **Consistency with the gap (dimension swap, `NOTE.md` §3.3):** D′_λ certifies the decay rate λ per coarse unit, i.e. λ/L in
   physical units; the true slowest rate of block observables is the 0⁺⁺ mass, so a certificate for the true blocked action must have
   `λ ≤ m₀₊₊ L` (O(4) symmetry of the limit turns the temporal gap into the spatial decay rate the Dobrushin bound controls). Reported
   per point: `λ*_H` against `m₀₊₊ L = 3.75·(L√σ)` (band 3.5 to 4.0). A violation (`λ*_H > 4.0·L√σ`) marks the fitted, truncated
   action as inconsistent with the gap (a truncation/fit artefact), not as a result about SU(2).

## Verdicts (same logic as Leg C, `analyse_blocked.decide`)

Per point, criterion (`H_TV`, `a_TV`, `H_W`, `a_W`) and fit: **NOT_EXCLUDED** if value_hi + 2·stat < 1; **EXCLUDED** if
value_lo − 2·stat > 1; else UNDECIDED. A point's verdict is NOT_EXCLUDED (EXCLUDED) only if the base fit **and every extension fit**
say so, otherwise UNDECIDED. Only points whose Leg C signal check PASSes count (Leg C's rule C4); deterministic f = 1/2 is primary,
the noisy variants (β_n = 16, 64) are reported and count only under their own photon gate (Leg C's C1, C5).

## Gates (must hold before any SU(2) reading)

* **Photon** (U(1), β = 1.1 and, when present, 1.3, Coulomb; each (f, noise) variant): `H_TV` and `H_W` EXCLUDED at every b. Note
  stated now: the U(1) adjoint half alone (`q2 cos 2θ`, centre-blind under θ → θ + π) is **not** required to be excluded; a
  centre-blind condition alone cannot see the photon (workstream 1, §1.3). The photon must be excluded by the centre half; reported:
  `c_TV`, `c_W` for U(1).
* **Z₂ deconfined** (β = 0.6): Z₂ factors have no centre-blind part (the only flip is the field itself), so `a = 0` and `H = c`:
  EXCLUDED at every b.
* **Deconfinement edge:** any NOT_EXCLUDED of `H_TV` or `H_W` at L√σ < 1.45 is flagged as a false positive of the method.

U(1) splitting: `cos θ`, `cos 3θ`, `cos θ_R` odd (centre-charged), `cos 2θ` even; TV oscillations on the circle; W₁ constants as Leg C
(2/π per unit coupling). Z₂: `c_TV = Σ tanh((n_P·2|β_P| + n_R·2|β_R|)/2)`, `c_W` as Leg C's Z₂ W1 (TV-based).

## Decision table (SU(2), counted primary points)

| outcome | meaning |
|---|---|
| `H_TV` NOT_EXCLUDED at L | the fitted truncated action satisfies the halves criterion, hence D′_λ (Lean): the strongest outcome; the remaining distance to a proof is H1Local + ObsTransfer + truncation |
| `H_TV` EXCLUDED, `H_W` NOT_EXCLUDED | the W₁ adjoint window is reached, the sup window is not: the proof route needs the W₁ form (`NOTE.md` §2: H1 in a Lipschitz norm, and a certified, non-linearised W₁ sup) |
| both EXCLUDED | report Y/X per form; entry scale = log-linear crossing of `H` = 1 between measured L (else "> 4.2") |
| centre half alone ≥ 1 | the obstruction at that L is not the adjoint channel; reported as such (expected only at L√σ ≲ 2, from C's proxy β_F ≈ 0.07) |

**Expectations, stated before data (not criteria):** from C's two-coupling stand-in (β_A ≈ 1.17, 0.50, 0.21 at L√σ = 2, 3, 4;
β_F ≈ 0.07, 5·10⁻⁴, 5·10⁻⁷): centre half small (`c_TV` ≈ 1.2, 0.01, 10⁻⁵); adjoint half `a_TV` ≈ 11.3, 5.9, 2.5 (EXCLUDED everywhere);
`a_W` (hi) ≈ 4.0, 1.7, 0.73. So expected: TV EXCLUDED at every L; W₁ EXCLUDED at 2.1 and 3.15, near or below 1 at 4.2. Gap factors
`Y/X_TV` ≈ 6 at L√σ ≈ 3. The measured action can differ from the stand-in in either direction and with f.

## Amendment before data (2026-11-22, about 02:20, no SU(2) fit read yet)

The linearised W₁ constant of the adjoint channel is sharpened analytically (`kA_bounds.py`, `NOTE.md` §2.3):
`k_A ∈ [2√2/(15π), 1/(5π)] = [0.0600, 0.0637]` (C's bracket was [0.0531, 0.0722]; a discretised transport LP, `kA_lp.py`,
gives 0.0625 ≈ 1/16). Item 3 and the W₁ verdicts use the sharpened bracket; the W₁ adjoint half with C's upper constant is
reported next to it (`a_W_hi_Cbracket`). The pure-adjoint linearised window is then `β_A* ∈ [0.327, 0.347]` (numerically 1/3).
Nothing else changes.

Second note before data (about 02:25, still no SU(2) fit read): a nonlinear check (`kA_bingham.py`) shows that at the aligned
configuration the W₁ adjoint column crosses 1 at β_A ≈ 0.28, below the linearised 1/3. The pre-registered W₁ verdicts stay
linearised; the report adds, per point, whether |β_A| is below 0.28 (the nonlinear ceiling of the W₁ window).

## What this cannot show

Everything in Leg C's "What this measurement cannot show" applies (fitted, truncated action; deterministic block variable not the
good blocking of workstream 1; range; volume; no continuum extrapolation). In addition: the halves split is exact only for the
fitted factor families (plaquettes up to spin 3/2, 1×2 rectangles); omitted factors add to both halves. The W₁ numbers are
linearised at the uniform point.
