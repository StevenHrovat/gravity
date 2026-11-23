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

The tori are tiny (at most `6³ × 12`), so this is CPU work. I have not estimated its cost and would time one unit before any run.
It would decide whether `F_e(L) ≤ 2c(L)` holds at every small cubic `L` (a refutation of the cubic criterion at those scales).
No GPU run is proposed.
