# Refutation check of `F_e(L) > 2 c(L)` at small L, CPU only (plan fixed before any number), 2026-11-23

Owner's OK ("Yes, start both"), via the coordinator. The statement (`HTF.md` 4, `OPEN-QUESTIONS-DMP.md` 0): along a chain of
boxes of length `L` on a spatial torus `L_s³`, the per-box rate multiplies iff `F_e(L) > 2 c(L)`, where
`F_e(n) = log Z₀(n) − log Z₁(n)` (electric-flux free energy, flux `e_k` along one spatial axis `k`), `c(n) = log(Z₀(n)/λ₀ⁿ)` (neutral
excess act), `Z_e(n) = tr(P_e Tⁿ)`, `T` the transfer matrix, `λ₀` its vacuum eigenvalue. This check can only **refute** (provability
table, `c9b-adjoint/REDESIGN.md` 8).

## 1. What saved data can and cannot give (decided before computing)

* **`F_e(L)` and `c(L)` themselves: not estimable from saved data.** Both contain `λ₀^L`, the absolute normalisation of the
  transfer matrix, i.e. free-energy differences between tori of different time extent (thermodynamic integration over β at
  several time extents: new simulations). `F_e` also needs the twisted ensemble `Z_tw/Z`. Direct reweighting on the saved `16⁴`
  configurations would flip about 256 plaquettes, `⟨e^{−βΔS}⟩` with `βΔS` of order 700, hopeless; the snake algorithm needs new
  runs. **That part stops here.**
* **What saved data can give: a one-sided bound on the difference.** Exactly (paper):
  `F_e(L) − 2c(L) = −log(Z₀(L) Z₁(L) / λ₀^{2L}) = −c(L) − log(Z₁(L)/λ₀^L)`. With `Z₁(L)/λ₀^L = Σ_{e_k=1} e^{−L ΔE} ≥ e^{−L ΔE_f}`
  (`ΔE_f` the lowest flux energy) and `c(L) = log(1 + Σ_{neutral excited} e^{−L ΔE}) ≥ log(1 + Σ_{visible} e^{−L ΔE_i})`:

      F_e(L) − 2c(L) ≤ R(L) := L · ΔE_f^up − log(1 + S(L)),   S(L) = Σ_{visible neutral states i} e^{−L ΔE_i^up},

  where `ΔE^up` are **upper bounds** on energies. Those come from reflection-positive slice correlators: for an operator `O` on one
  time slice, `C(t) = Σ_i |⟨i|O|0⟩|² e^{−t ΔE_i}` is log-convex, so the effective mass `m_eff(t) = log(C(t)/C(t+1))` decreases in `t`
  and is `≥` the lowest energy that `O` reaches. So `m_eff(t)` is an upper bound on that lowest energy, for every `t`.
  **Refutation at `L`: a certified `R(L) < 0`.** A positive `R(L)` refutes nothing and establishes nothing; `R` is only an upper
  bound on `F_e − 2c`.

## 2. Data, geometry, estimators (fixed)

* **Configurations:** `w2/runs/conf_b2.3.npz`, `conf_b3.5.npz` (periodic `16⁴`, SU(2) Wilson, 4 independent configurations per β,
  300 heat-bath sweeps from a hot start). Each of the 4 axes is taken as "time" in turn (hypercubic symmetry of the torus), so per β
  there are 4 configurations x 4 orientations x 16 time origins; the 4 configurations are the independent units.
* **Not used:** the W2 conditional snapshots (`6⁴` boxes with a fixed outside, not tori: no transfer matrix), and the blocked lattices
  (blocked variables have no reflection-positive nearest-neighbour transfer matrix of Wilson form; and blocking does not change the
  physical torus size).
* **Geometry, and what it means:** the chain cross-section is the saved spatial torus, `L_s = 16`. The box length `L` along the chain
  is scanned over `L = 1, ..., 8` (lattice units) from the same energy bounds (`R(L)` is an explicit function of `L`). The cubic
  geometry `L_s = L` is **not** accessible from saved data. So the result concerns chains of cross-section `16³`, where `c(L)` is
  extensive (`HTF.md` 4), and a refutation at small `L` is expected there; the informative number is the largest `L` at which it is
  refuted (below that, the criterion cannot hold for this cross-section).
* **Neutral states:** for every spatial momentum `p` of the `16³` torus, `O_p(t) = Σ_x e^{i p·x} Σ_{spatial planes} q₀(t, x)` (`q₀` =
  ½ tr of the spatial plaquettes in slice `t`), connected correlator (vacuum subtracted at `p = 0`). States with different momenta are
  orthogonal, so each momentum contributes at least one distinct neutral excited state with `ΔE ≤ m_eff(t; p)`. Momenta are grouped
  into orbits of the cubic group (equal energies by symmetry); orbit multiplicities are exact; the correlator is averaged over each
  orbit.
* **Flux state:** `P_k(t) = Σ_{x_⊥} ½ tr(Polyakov loop along spatial axis k)`, zero transverse momentum, averaged over the 3 spatial
  axes. Odd under the centre transformation along `k`, so it reaches only `e_k = 1` states: `ΔE_f ≤ m_eff,P(t)`. Not vacuum-subtracted
  (`⟨P⟩ = 0` by centre symmetry on the torus).
* **Which `t`:** primary `t = 1` (`m_eff(1) = log(C(1)/C(2))`). If `C(2)` is not significantly positive (jackknife mean less than
  2σ above 0) for an operator, fall back to `t = 0` for that operator (a looser upper bound). Orbits for which neither works are
  dropped from `S` (conservative: `S` only gets smaller).
* **Finite-`T` contamination:** on the periodic time extent 16, backward terms are of relative size `e^{−(16 − 2t) ΔE}`, below `10⁻⁶`
  for `ΔE ≥ 1`; neglected and stated.

## 3. Error bars and the verdict (fixed)

* **Per operator:** `σ = max(σ_jk, σ_floor)`. `σ_jk` is the jackknife over the 4 independent configurations. `σ_floor` is the naive
  standard error over all (orientation, time-origin) samples: the error the data cannot go below, in the spirit of the derived floor
  of `c9b-adjoint/PILOT.md` and `w2/PROJECTION.md` 8 (the floor is not reduced by re-measuring the same unit).
* **Upper bounds:** `ΔE^up = m_eff + t_{3}(0.95) σ`, with `t_3(0.95) = 2.353` (Student, 3 degrees of freedom, one-sided 95 %).
  Each term of `S` uses its own upper bound, so every term is individually conservative at 95 %; no simultaneous (Bonferroni)
  coverage is claimed, and it is stated.
* **Verdict at each `L`:** **refuted** if `R(L) < 0` with all inputs at their one-sided 95 % bounds, and also reported at 99 %
  (`t_3(0.99) = 4.541`). Otherwise **not refuted by this bound, margin `R(L)`**. That margin is an upper bound on `F_e − 2c`, so it
  tells the proof nothing beyond "not excluded at this `L`".

Code: `w2/onebox_check.py` (written after this plan).

---

## 4. Result (computed after the plan; `w2/onebox_check.py`, CPU under a minute, `w2/runs/onebox_check.json`)

**Flux energy `ΔE_f` (spatial Polyakov loop, cross-section `16³`), mean correlator `C(0..3)`:**
* **β = 2.3:** `64.4, 3.9, −0.8, 2.4`; `C(1)` changes sign across the 4 configurations (`9.2, −4.2, 6.4, 4.3`). Not significant at
  `t = 1` or `t = 0` under the plan's 2σ rule: **no upper bound on `ΔE_f`, so `R(L)` cannot be formed; no test at β = 2.3.** The flux
  energy at this cross-section is large (the signal is gone after one step), which only makes `F_e` larger; it cannot refute.
* **β = 3.5:** `350, 281, 277, 261`: nearly flat. `m_eff(1) = 0.014`, `σ_jk = 0.007`, `σ_floor = 0.196`, so `σ = 0.196` by the
  plan's rule. The `e_k = 1` sector is almost degenerate with the vacuum: at β = 3.5 the `16³` torus is physically small and
  electric flux is nearly free.

**Neutral states (lower bound on `c(L)`, `log(1 + S(L))`):** orbits passing the 2σ rule: 98 of 165 (2745 momentum states) at
β = 2.3, 62 of 165 (1964 states) at β = 3.5. Lowest upper bounds are around `ΔE ≈ 1.3` to `2.2` (β = 2.3) and `2.6` to `3.0`
(β = 3.5, one noisy orbit at `0.10 ± 0.76`).

| β | L | `L·ΔE_f^up` (95 %) | `log(1+S)` (95 %) | `R(L)` 95 % | `R(L)` 99 % | verdict |
|---|---|---|---|---|---|---|
| 2.3 | 1 | n/a | 4.23 (99 %: 3.64) | n/a | n/a | no test (no flux bound) |
| 2.3 | 2 | n/a | 1.20 | n/a | n/a | no test |
| 2.3 | 3 | n/a | 0.10 | n/a | n/a | no test |
| 2.3 | ≥ 4 | n/a | ≤ 0.01 | n/a | n/a | no test |
| 3.5 | 1 | 0.47 | 3.58 | **−3.11** | **−1.86** | **refuted** (95 % and 99 %) |
| 3.5 | 2 | 0.95 | 0.94 | 0.01 | 1.65 | not refuted, margin 0.01 (95 %) |
| 3.5 | 3 | 1.42 | 0.16 | 1.26 | 2.70 | not refuted, margin 1.3 |
| 3.5 | 4 to 8 | 1.90 to 3.79 | ≤ 0.02 | 1.87 to 3.79 | 3.61 to 7.22 | not refuted |

**Robustness (exploratory, not part of the plan):**
* *Selection.* Requiring 4σ instead of 2σ for an orbit to enter `S` (guards against selecting upward fluctuations): β = 3.5 keeps
  4 orbits (168 states), and `L = 1` is still refuted (`R` = −1.19 at 95 %, −0.38 at 99 %). β = 2.3: `log(1+S)` 3.43 at `L = 1` (95 %).
* *Flux error.* With the jackknife error alone for the flux (`0.007`, not the plan's floor `0.196`), `R(L)` at 95 % would be
  negative up to `L = 3` at β = 3.5 (`L·ΔE_f^up ≈ 0.03 L` against `log(1+S)` = 3.58, 0.94, 0.16). The non-refutations at
  `L = 2, 3` come from the floor on the flux bound, not from the data favouring the criterion.

## 5. What this tells the proof (provability table: measurements only refute)

* **Refuted, in a geometry the proof does not use as stated.** For a chain of cross-section `16³` at β = 3.5, `F_e(1) > 2c(1)` is
  false (certified at 99 %). There `c(1)` is large because it is extensive (about 2000 momentum states within reach) and
  `F_e` is small because flux is nearly free in this physically small torus. This is the failure `HTF.md` 4 predicted for small `L`
  at large cross-section, now measured. It does not refute the statement: the criterion only has to hold at one scale.
* **Consistent with the hand-over.** At β = 3.5 on this torus the electric channel is weak (flux nearly free). By `su2_handover` the
  twist channel must then carry `F_tw ≥ 0.881`: this is the rarity side, where the transfer-matrix multiplication (an electric
  mechanism) does not operate. This is a reading, not a measurement of `F_tw`.
* **Not refuted elsewhere, and that says nothing positive.** `R(L) > 0` for `L ≥ 2` (β = 3.5) is an upper bound on `F_e − 2c`;
  the true value may be negative. At β = 2.3 no test was possible (no flux bound).
* **The cubic one-box geometry (`L_s = L`) is untested.** Neither `F_e(L)` nor `c(L)` is estimable from saved data (both need
  `λ₀^L`, a free-energy difference between tori of different length, and `F_e` needs the twisted ensemble).

## 6. Proposal (not run; would decide the cubic form at small L)

A CPU-only simulation of small periodic tori `L⁴` and `L³ × 2L`, `L = 2, ..., 6`, at β = 2.3 and 3.5:
* `c(L)` from the gluing ratio `Z₀(L)²/Z₀(2L) = e^{2c(L) − c(2L)}` (so `2c(L) ≥ log` of it, since `c(2L) ≥ 0`), with
  `Z₀ = (Z + Z_tw)/2` and `Z` from thermodynamic integration of the plaquette over β from 0;
* `Z_tw/Z` by the snake algorithm (`L²` single-plaquette-flip steps, each a reweighting ratio of order one);
* hence `F_e(L)` and `c(L)` directly, in the cubic geometry the one-box statement uses.

**Error bars (project rule, `attempts/RULES.md`, last section):** each quantity gets max(statistical floor, resolution floor).
The statistical floor is the jackknife over independent runs, or the delta method *with* covariances, whichever is larger. The
resolution floor for an energy read over time extent `T` is `1/T` (here `T = L` for `c` and `F_e` at length `L`, `2L` for the gluing
partner). `F_e(L)` and `c(L)` are not energies but log-ratios over extent `L` (`F_e ≈ L · ΔE`). My reading of the rule: the
analogous floor is `L · (1/L) = 1`, the same order as the hand-over's `0.881`. If that reading holds, the proposal can only refute
where `2c(L) − F_e(L)` exceeds about 1 plus the statistical error, and a smaller gap would be "unresolved". That reading is the
owner's call before any run.

The tori are tiny (at most `6³ × 12`), so this is CPU work. I have not estimated its cost and would time one unit before any run.
It would decide whether `F_e(L) ≤ 2c(L)` holds at every small cubic `L` (a refutation of the cubic criterion at those scales).
No GPU run is proposed.

## 7. POST-HOC re-score under the universal floor (`attempts/RULES.md`, last section; adopted after the result above)

Reported **beside** the pre-registered result of section 4, not in its place. Rule: error = max(statistical floor, resolution
floor); no ad-hoc floors. `w2/onebox_check.py --rule post` (CPU seconds); `w2/runs/onebox_check_post_sig2.json`,
`..._post_sig4.json`.

**What changes in the estimator.**
* *Energies* (flux and neutral orbits): `σ = max(σ_jk(m_eff), 1/T)`, with `T = 16` (observed Euclidean extent), so a resolution
  floor of `0.0625`. The statistical floor is the jackknife of `m_eff` itself. That equals the delta method *with* the
  covariance of `C(t)` and `C(t+1)`; the delta method without the covariance is reported in the JSON (`sigma_nocov`), not used.
* *Selection of orbits* (the plan's 2σ rule on `C(t)`, `C(t+1)`): the jackknife of `C` only, with the ad-hoc sample floor dropped.
* **Correction to section 4's description.** I described the flux error `0.196` as a naive-standard-error floor. The code actually
  took the larger of the jackknife and the naive error **at the level of `C`** and propagated it to `m_eff` without the covariance.
  For the flux the jackknife of `C` was the larger, so `0.196` is the no-covariance delta method. Here `C(1)` and `C(2)` move
  together across configurations (`C` ranges 267 to 441 between configurations, while their ratio agrees to `0.007`). That
  propagation is what the rule now drops. The pre-registered numbers stand as computed; only their label was wrong.

**Flux (β = 3.5):** `m_eff = 0.014`, `σ_jk = 0.007`, resolution floor `0.0625` → **σ = 0.0625** (plan: 0.196). β = 2.3: still
no significant flux signal, so no bound and no test. The floor does not create a signal.

| β | L | `R(L)` 95 % | `R(L)` 99 % | post-hoc verdict | pre-registered verdict (section 4) |
|---|---|---|---|---|---|
| 3.5 | 1 | −4.24 | −3.39 | refuted | refuted |
| 3.5 | 2 | **−2.13** | **−0.79** | **refuted** (95 % and 99 %) | not refuted (margin 0.01) |
| 3.5 | 3 | **−0.79** | +0.46 | **refuted at 95 % only** | not refuted (margin 1.3) |
| 3.5 | 4 | +0.08 | +1.08 | not refuted (margin 0.08) | not refuted |
| 3.5 | 5 to 8 | +0.58 to +1.27 | +1.46 to +2.38 | not refuted | not refuted |
| 2.3 | any | n/a | n/a | no test | no test |

With the stricter 4σ selection (exploratory, as in section 4): β = 3.5 refuted at `L = 1` (95 % and 99 %) and at `L = 2` at 95 % only
(`R = −0.06`), not refuted for `L ≥ 3`. Neutral lower bounds at β = 2.3 (95 %, 2σ selection): `c(1) ≥ 4.6`, `c(2) ≥ 2.0`,
`c(3) ≥ 0.65`.

**Does a verdict change? Yes, at β = 3.5 only.** The refuted range grows from `L = 1` to `L ≤ 2` (both levels) and `L = 3` (95 %).
With the 4σ selection it is `L = 1`, plus `L = 2` at 95 %. β = 2.3 stays untested. The change comes almost entirely from the flux
error dropping from 0.196 to the resolution floor 0.0625.

**What this bears on: nothing about the one-box statement, either way.** All of this is for chains of cross-section `16³`. There
`c(L)` is extensive and, at β = 3.5, electric flux is nearly free in the physically small torus. The one-box statement concerns
the cubic geometry (`L_s = L`), which saved data cannot reach (section 5). A larger refuted range here only says that, at this
cross-section and coupling, the electric multiplication needs box lengths `L ≥ 4` (or more).

---

## 8. PRE-REGISTRATION: the small-torus check in the cubic geometry (fixed before any simulation output; owner: "Yes, run the small-torus check")

**Question.** In the geometry the one-box statement uses (box length = cross-section = `L`), is `F_e(L) ≤ 2c(L)` (refutation at
that scale) certified at some small `L`?

### 8.1 Tori, couplings, simulation (fixed)

* Tori `L⁴` and `L³ × 2L`, periodic, SU(2) Wilson action with weight `exp(β Σ_p ½ tr U_p)`, **β = 2.3 and 3.5**.
* **`L = 2, 4, 6`.** Deviation from the requested `2, ..., 6`: the vectorised heat bath updates links in two checkerboard classes
  per direction, which needs even extents; odd `L` would need a different update scheme. Stated now, before any output.
* Update: per sweep, one Kennedy-Pendleton/Creutz heat-bath pass and two over-relaxation passes over all links. Cold start;
  200 thermalisation sweeps; **2000 measured sweeps per ensemble** (every sweep measured), errors by jackknife over 40 bins of
  50 sweeps. One process at a time, CPU only. Code: `w2/smalltorus.py` (written after this section).

### 8.2 Estimators (fixed)

* **`r = Z_tw/Z`** (twist in the plane `(0, k)`: the sign of the `L²` plaquettes of that plane at fixed `(t, x_k)` flipped) by the
  **snake**: `r = Π_{m=1}^{L²} Z_m/Z_{m−1}`, `Z_m` with the first `m` plaquettes flipped (in boustrophedon order, so the flipped set
  stays connected). Each factor comes from one ensemble in which plaquette `m` is **removed** from the action (coupling 0) and the
  first `m − 1` are flipped: `Z_m/Z_{m−1} = ⟨e^{−β q_m}⟩/⟨e^{+β q_m}⟩`, `q_m = ½ tr U_{p_m}` (both averages bounded in
  `[e^{−β}, e^{β}]`). `L²` ensembles per torus.
* **`F_e(L) = log((1 + r_L)/(1 − r_L))`** on `L⁴` (electric flux free energy, `Flip/Floor.lean` `elecF`, with
  `Z₀ = (Z + Z_tw)/2`, `Z₁ = (Z − Z_tw)/2`).
* **Gluing ratio `G(L) = Z(L)²/Z(2L)`** by thermodynamic integration in a cut parameter `α ∈ [0, 1]`. The link set of `L³ × 2L` is
  kept. The `(0, i)` plaquettes based at `t = L − 1` and `t = 2L − 1` (`6L³` plaquettes) enter with weight `(1 − α)` in their glued
  form (top link at `t + 1` mod `2L`) and `α` in their cut form (top link at `t = 0`, respectively `t = L`). At `α = 0` this is the
  `L³ × 2L` torus, at `α = 1` two independent `L⁴` tori. `log G = ∫₀¹ ⟨β (Q_cut − Q_glued)⟩_α dα`, `Q` the sum of `½ tr` over those
  plaquettes. **9 uniform nodes** `α = 0, 1/8, ..., 1`, Simpson's rule, one ensemble per node.
* **Lower bound on `c(L)`**: `Z₀(L)²/Z₀(2L) = e^{2c(L) − c(2L)}` and `c(2L) ≥ 0`, so
  `2c(L) ≥ 2c_lb(L) := log G + 2 log(1 + r_L) − log 2 − log(1 + r_{2L})` (with `r_{2L}` the snake ratio on `L³ × 2L`).
* **Tested quantity:** `D(L) = 2c_lb(L) − F_e(L)`. Since `2c ≥ 2c_lb`, **`D(L) > 0` certified ⟹ `F_e(L) < 2c(L)`: refuted at `L`.**

### 8.3 Error bars (universal floor rule, `attempts/RULES.md`, last section) and verdict (fixed)

* *Statistical:* jackknife within each ensemble (40 bins). Ensembles are independent, so variances add over the snake steps and the
  quadrature nodes. The delta method with these variances gives `σ_stat` for `log r`, `F_e`, `log G`, `2c_lb`, `D`. The
  quadrature error of Simpson's rule is estimated as `|Simpson − trapezoid|` on the same nodes and added in quadrature.
* *Resolution floor:* `F_e` and `2c_lb` are log-ratios over Euclidean extent `L`; an energy over extent `L` is resolved to `1/L`, so
  a log-ratio `≈ L · ΔE` is resolved to **1** (my reading of the rule for non-energies, section 6, stated again here). It is applied
  once, to the tested quantity: `σ_D = max(σ_stat(D), 1)`.
* **Verdict per `(L, β)`:** **refuted** if `D − 1.645 σ_D > 0` (one-sided 95 %; also reported at 99 %, `2.326`). Otherwise
  **not refuted, margin `D`** (with `σ_D`). Also reported, as secondary, the verdict with `σ_stat` only (no resolution floor).
* **Provability:** a refutation at some `L` excludes the multiplication criterion at that scale only. A non-refutation is a
  margin, not a proof. And because `c_lb` drops `c(2L)`, a non-refutation can also come from the bound being loose.

### 8.4 Sanity checks before production (fixed; results reported, not used for tuning)

(1) Identity configuration: all plaquettes 1. (2) Plaquette average at small β against the single-plaquette value
`I₂(β)/I₁(β)`, and at β = 2.3 on `6⁴` against the `16⁴` value 0.602 (a finite-size difference is expected; reported). (3) Every
snake factor positive, and `r ≤ 1` (Lean: `Z_tw ≤ Z`). (4) At `α` = 0 and 1 the gluing integrand is evaluated in the two pure
ensembles.

### 8.5 Timing and projection (fixed)

Short timings (sweep cost) on each torus size, then one full unit (one snake ensemble at `L = 4`, β = 2.3). Project the whole run
with `w2/PROJECTION.md` 8 (band `0.9×` to `1.9×`, central `1.33×`). If the band's upper edge exceeds about 6 CPU-hours: stop and
report the projection before running.

### 8.6 Sanity checks and timing (before production; no snake or gluing output looked at)

* Sanity (8.4): identity configuration gives plaquette 1. On `4⁴`, `⟨q⟩` = 0.1244 ± 0.0022 at β = 0.5 (single-plaquette value
  0.1237) and 0.2431 ± 0.0023 at β = 1.0 (0.2402; the small excess is the expected strong-coupling correction). On `6⁴` at β = 2.3,
  0.6038 (the `16⁴` value is 0.602). The gluing set-up has `2L³` boundary base sites per plane, as intended.
* Sweep cost (ms, standard action, β = 2.3): `2⁴` 6.7, `2³×4` 6.4, `4⁴` 8.4, `4³×8` 10.7, `6⁴` 17.7, `6³×12` 27.8. Content classes
  timed: snake `6⁴` 17.9, snake `6³×12` 26.7, glue `4³×8` 13.5, glue `6³×12` 32.2. **Unit** (snake ensemble, `L = 4`, β = 2.3,
  2200 sweeps): 19.7 s (9.0 ms per sweep).
* **Projection** (`PROJECTION.md` 8): 2 β × (L = 2: 281 s, L = 4: 987 s, L = 6: 4170 s) = 10 876 s = 3.0 h raw. Central
  `× 1.33` = **4.0 CPU-hours**, band `0.9×` to `1.9×` = **2.7 to 5.7 h**, inside the 6-hour limit. β = 3.5 was not timed separately
  (rule 3: factor 1.0 ± 0.3, inside the band). Run order: β = 2.3 (L = 2, 4, 6), then β = 3.5; resumable, one process.

## 9. Result of the small-torus check (computed after section 8; `w2/smalltorus.py run` + `analyse`, `w2/runs/smalltorus_result.json`)

**Run.** 278 ensembles (snake: `L²` per torus, both tori, both β; gluing: 9 nodes per `L` and β), 2000 measured sweeps each,
**11 782 s = 3.27 CPU-hours** against the projection of 4.0 h (band 2.7 to 5.7 h): inside the band. One simulation process
throughout. Deviations: the odd `L` were dropped, as pre-registered in 8.1. Lean builds of other rounds ran beside it at times; that
slowed some ensembles by up to about 25 % and does not affect the results. Sanity (8.4): every snake ratio `r ≤ 1` (`Z_tw ≤ Z`);
every factor positive; the hand-over `max(F_tw, F_e) ≥ 0.881` holds at every `(L, β)` (closest: β = 2.3, `L = 4`, `F_tw` 0.86 and
`F_e` 0.91).

**Estimates** (statistical errors; `D = 2c_lb − F_e`; refuted if `D − z σ_D > 0` with `σ_D = max(σ_stat, 1)`, `z` = 1.645 / 2.326):

| β | `L` | `r_L` | `r_{2L}` | `F_e(L)` | `log G` | `2c_lb(L)` | `D` | `σ_stat(D)` | verdict 95 % / 99 % (floor 1) | stat-only 95 % / 99 % |
|---|---|---|---|---|---|---|---|---|---|---|
| 2.3 | 2 | 0.116 | 0.394 | 0.233 ± 0.020 | 3.15 ± 0.10 | 2.35 | **2.12** | 0.11 | **refuted** / not refuted | refuted / refuted |
| 2.3 | 4 | 0.425 | 0.757 | 0.91 ± 0.18 | 1.82 ± 0.31 | 1.27 | 0.36 | 0.33 | not refuted / not refuted | not refuted / not refuted |
| 2.3 | 6 | 0.863 | 0.835 | 2.6 ± 1.8 | 0.87 ± 0.55 | 0.81 | −1.80 | 1.64 | not refuted / not refuted | not refuted / not refuted |
| 3.5 | 2 | 0.018 | 0.074 | 0.035 ± 0.005 | 4.59 ± 0.43 | 3.86 | **3.82** | 0.43 | **refuted** / **refuted** | refuted / refuted |
| 3.5 | 4 | 0.027 | 0.126 | 0.053 ± 0.014 | 2.30 ± 0.47 | 1.54 | 1.49 | 0.47 | not refuted / not refuted | refuted / refuted |
| 3.5 | 6 | 0.039 | 0.095 | 0.079 ± 0.030 | 2.56 ± 0.83 | 1.85 | **1.77** | 0.83 | **refuted** / not refuted | refuted / not refuted |

**Verdict (pre-registered rule, primary with the resolution floor).** In the cubic geometry the multiplication criterion
`F_e(L) > 2c(L)` is **refuted** at β = 2.3, `L = 2` (95 %); at β = 3.5, `L = 2` (95 % and 99 %); and at β = 3.5, `L = 6` (95 %). It
is **not refuted** at β = 2.3, `L = 4` (margin `D = 0.36`) and `L = 6` (margin `D = −1.8`, i.e. `F_e` above the lower bound `2c_lb`
centrally), nor at β = 3.5, `L = 4` (margin 1.49 against the floor; refuted on statistics alone).

**What this tells the proof (provability rule).**
* **The refutations exclude those scales only.** They lie where the boxes are physically small and weakly coupled (all of β = 3.5 up
  to `L = 6`, and β = 2.3 at `L = 2`). There electric flux is nearly free (`F_e` from 0.035 to 0.23) while the neutral excess act is
  large (`2c ≥ 1.5` to 3.9). This is the "outside" of `CONTAINMENT.md` (a): inside the container the criterion fails, as it must.
* **The non-refutations are margins, not proofs.** At β = 2.3, `L = 4` and `L = 6` the data do not exclude the criterion. At `L = 6`
  the central value even has `F_e > 2c_lb`, but `c_lb` is only a lower bound on `c` (it drops `c(2L)`), and the errors are large
  (`σ_stat(D)` = 1.6).
* **The pattern matches the containment picture.** The criterion is excluded on the weakly coupled side and left open where the twist
  saturates (`r_L` = 0.42 to 0.86 at β = 2.3, `L = 4` to 6). Read with `SATURATION.md` 4 and `EQUIDIST.md` 4: at β = 2.3 the
  crossover between the two regimes lies between `L = 2` and `L = 6`. At β = 3.5 it lies beyond `L = 6`.
