# Cycle 3, workstream 3 (c3c): the adjoint half's constant as a theorem (2026-11-22)

Brief: make the adjoint half's constant a theorem by certified computation: the exact `k_A`; a certified supremum of the
per-neighbour W₁ coefficient over all Bingham conditional laws as a function of β_A at β_F = 0, the largest β_A* with a
column sum < 1, and a two-parameter window with small β_F; the certified numbers as one named Lean hypothesis whose
consequences are proved in Lean by `norm_num`.

Claim levels as in `../../attempts/RULES.md` and `../c2a-adjoint/NOTE.md`: **Lean** (machine-checked), **paper** (complete
argument here), **certified** (computer-assisted: interval arithmetic with outward rounding, every cell of the parameter
domain enclosed, not a scan), **numerical** (float), **conjecture**. Pre-registration: `PREREG.md` (written before any run).
Files: `bingham.py` (Bingham moments as power series), `checks.py`/`.log` (run 1), `explore.py`/`.log`,
`explore2.py`/`.log` (run 2, design, float), `cert_adjoint.py` + `cert_window.json` + `run_*.log` (run 3, certificate),
`window2.py`/`.json` (two-parameter window), `cert_ceiling.py`/`.json`/`.log` (run 4, certified ceiling); Lean:
`../../../formal/ProofPhase/Certified/AdjointW.lean`, built in `~/formal-c3c` (`setup-c3c.sh`, `build-c3c.sh`,
`axioms-c3c.sh`). All runs CPU, `CUDA_VISIBLE_DEVICES=-1`, each under 8 minutes, one process at a time except two short overlaps
(§0, item 7).

---

## 0. Results at a glance

1. **`k_A = 1/16` exactly (paper, §1).** The optimal 1-Lipschitz test function is the signed geodesic distance to the two
   walls `a^⊥ ∪ b^⊥`, `φ* = sign(u_a u_b) min(arcsin|u_a|, arcsin|u_b|)`, and an explicit transport along the great circles
   orthogonal to the walls (balanced ray by ray by the reflections) has the same cost; the integral is `1/16`. c2a's
   conjecture is a theorem; the linearised pure-adjoint W₁ window is **exactly β_A < 1/3**.
2. **Exact coefficient at every Klein-symmetric Bingham law (paper, §2):** `N_A = E_ρ[|u_a u_b| min(arcsin|u_a|,
   arcsin|u_b|)]` when `a, b` are eigenvectors of `Q` (reproduces c2a's aligned-configuration LP to its discretisation error).
3. **Certified window at β_F = 0 (§3):** for every staple configuration (every eigenvalue configuration of the adjoint staple
   matrix Q, every moved staple and direction) the per-neighbour W₁ coefficient is `≤ (8|β_A|/3)·B̄`, with certified suprema
   `B̄ = 0.07250, 0.08150, 0.09020, 0.09860` at β_A = 0.05, 0.10, 0.15, 0.20 and `0.07210, 0.07970, 0.08660, 0.09300` at
   −0.05, …, −0.20. **The 18-neighbour column is < 1 for −0.22 ≤ β_A ≤ 0.21** (certified: column ≤ 0.99997 at +0.21, ≤ 0.999998
   at −0.22). Against the sup form (`|β_A| < 0.0834`) the window is 2.5 times wider.
4. **Certified ceiling (§2):** the single-link W₁ criterion **fails** for β_A ≥ 0.275 and for β_A ≤ −0.29 (certified lower
   bound at an explicit symmetric configuration). So the true single-link W₁ window edge is in [0.21, 0.275) for β_A > 0 and
   in (−0.29, −0.22] for β_A < 0; c2a's numerical ceiling 0.281 (aligned configuration) is lowered to 0.275 and made rigorous.
5. **Two-parameter window (§4):** certified corners `(|β_A|, |β_F|) ≤ (0.21, 0), (0.20, 0.0020), (0.15, 0.0145),
   (0.10, 0.0265), (0.05, 0.0425), (0, 0.0685)`, each with a certified per-plaquette coefficient `k` and column `18k < 1`.
6. **Lean (§5):** `formal/ProofPhase/Certified/AdjointW.lean`: the two-coupling action as a local potential; the single named
   hypothesis `CertifiedAdjointW` (the certified per-plaquette W₁ bounds at the six corners); `cornerColumn_lt_one` by
   `norm_num`; from them `limitDprimeW_twoCoupling` (the W₁ form of D′, uniform in the volume; at β_F = 0 the W₁ adjoint half)
   and `twoCoupling_decay` (uniform exponential decay). The sup-form `AdjointHalf` of `CentreSplit.lean` is **false** on most
   of the window (exactly: it needs |β_A| < 0.0834), so no certificate can imply it there; the W₁ form replaces it, at the price
   of `H1LocalLip` (quantitative openness bound in §5).
7. **Run note (honesty):** two of my certification processes overlapped twice for a few minutes (a duplicate start of the
   +0.21 window run after a tool-level kill did not reach the Python child, and the queue's −0.22 run starting before the
   +0.21 rerun ended, because its wait loop did not detect the running process). The computations are deterministic and the
   duplicate results identical; the "one process" rule was briefly broken. An early +0.10 entry made with a looser
   eigenvalue bound (Gershgorin) was removed from `cert_window.json`; all reported numbers come from the final code.

## 1. `k_A = 1/16` exactly (paper; checked numerically)

**Setting** (c2a §2.3). `k_A = ‖h₂·Haar‖_KR` on the unit S³ with the geodesic metric, `h₂(u) = ⟨u,a⟩⟨u,b⟩`, `a ⊥ b` unit. It
is the per-unit W₁ sensitivity of the uniform single-link law to one moved staple (the linearised adjoint constant).

**Theorem 1.** `k_A = 1/16`. The optimal 1-Lipschitz test function is the signed distance to the two walls `a^⊥, b^⊥`:

  `φ*(u) = sign(u_a u_b) · min(arcsin|u_a|, arcsin|u_b|)`,  `u_a = ⟨u,a⟩, u_b = ⟨u,b⟩`,

and `k_A = E_Haar[|u_a u_b| min(arcsin|u_a|, arcsin|u_b|)]`.

*Proof.* (i) *φ\* is 1-Lipschitz.* `dist(u, v^⊥) = arcsin|⟨u,v⟩|` for a great 2-sphere, so `|φ*| = dist(u, Z)`,
`Z = a^⊥ ∪ b^⊥ = {h₂ = 0}`. A distance function is 1-Lipschitz; for `u, v` with `h₂(u) > 0 > h₂(v)` every path crosses `Z`,
so `d(u,v) ≥ dist(u,Z) + dist(v,Z) = φ*(u) − φ*(v)`. Hence `k_A ≥ ∫φ* h₂ dHaar = E[|h₂| dist(·, Z)]`.
(ii) *A transport with the same cost.* Split S³ (up to a null set) into `R_a = {|u_a| < |u_b|}` (nearest wall `a^⊥`) and
`R_b`. Foliate `R_a` by the great circles through `±a`: `p(t) = cos t·a + sin t·m`, `m ⊥ a` unit, `t ∈ (0, π)`; Haar is
`∝ sin²t dt dσ(m)`. On each circle, `R_a` is an interval symmetric about `t = π/2` (`|cos t| < sin t |m_b|`), and the
reflection `R_a: u ↦ u − 2u_a a` maps `p(t) ↦ p(π − t)`, preserves Haar and flips the sign of `h₂`. So on every ray the signed
mass `h₂ sin²t dt` is antisymmetric about `π/2`, positive on one side and negative on the other: it balances on the ray, and its
1D optimal transport (all mass moves across `π/2`) costs `∫ |h₂| |π/2 − t| sin²t dt`, and `|π/2 − t| = arcsin|u_a| = dist(p, Z)`
on `R_a`. The same on `R_b` with `b`. Summing: a transport plan of cost `E[|h₂| dist(·,Z)]`. So `k_A` equals it.
(iii) *The value.* The joint law of `(u_a, u_b)` under Haar on S³ is uniform on the unit disk. In the 45°-rotated coordinates
`y₁,₂ = (u_a ± u_b)/√2`: `|h₂| = |y₁² − y₂²|/2`, `dist(·,Z) = arcsin(||y₁| − |y₂||/√2)`; by the eightfold symmetry and polar
coordinates the integral reduces to `(4/π)∫₀^{1/√2} s(1 − 2s²) arcsin s ds = (1/π)∫₀^{π/4} t sin 4t dt = (1/π)(π/16) = 1/16`. ∎

Checks (`checks.log`): Monte Carlo 0.062516 ± 0.000039; disk quadrature 0.0625000000; `∫φ* h₂` (MC) 0.062516. c2a's LP
extrapolation 0.06249 and the conjecture 1/16 are confirmed; c2a's bracket `[2√2/(15π), 1/(5π)]` is superseded.

**Consequence.** The linearised pure-adjoint W₁ window `β_A* = 1/(48 k_A)` is **exactly 1/3** (c2a: bracket [0.327, 0.347]).

## 2. The exact coefficient at symmetric configurations, and the certified ceiling

**Theorem 2 (paper).** If `ρ` is any probability density on S³ invariant under both reflections `R_a`, `R_b` (for a Bingham
law `ρ ∝ e^{uᵀQu}`: `a` and `b` are eigenvectors of `Q`), then

  `‖(h₂ − E_ρh₂) ρ‖_KR = E_ρ[|u_a u_b| min(arcsin|u_a|, arcsin|u_b|)]`.

*Proof.* `E_ρh₂ = 0` (oddness under `R_a`). The proof of Theorem 1 uses of Haar only its invariance under `R_a`, `R_b` and that it
has a density on the rays: both hold for `ρ`. ∎

This makes c2a's aligned-configuration numerics exact (`checks.log`: 0.06767, 0.07374, 0.07511, 0.07439 at β_A = 0.1, 0.26,
1/3, 0.5; c2a's LP 0.06751, 0.07355, 0.07491, 0.07419, low by its discretisation error 0.0002 as at the uniform point). The
float search over symmetric configurations (`explore.log`) finds larger values than the aligned one: for β_A > 0 the
configuration `(s_a, s_b, s₃, s₄) = (3, 3, 0, 0)` (three staples along `a`, three along the move direction `b`), for β_A < 0 the
configuration `(1, 0, 2.5, 2.5)` (the moved staple, five staples spread evenly in the plane orthogonal to `a, b`).

**Certified ceiling (run 4, `cert_ceiling.py`, `cert_ceiling.json`, `cert_ceiling.log`).** Rigorous lower Riemann sums of
the exact formula of Theorem 2 (monotone integrands on a 3000 × 3000 polar grid of the quarter disk, relative margin 10⁻⁹
for libm rounding):

| β_A | configuration `(s_a, s_b, s₃, s₄)` | `N_A ≥` (float) | column `48|β_A| N_A ≥` |
|---|---|---|---|
| +0.270 | (3, 3, 0, 0) | 0.077027 (0.077182) | 0.99827 (undecided) |
| **+0.275** | (3, 3, 0, 0) | 0.077293 (0.077449) | **1.02027** |
| **−0.290** | (1, 0, 2.5, 2.5) | 0.072817 (0.072959) | **1.01362** |

Since the supremum over configurations is nondecreasing in |β_A| (§3.1), **the single-link W₁ criterion fails for every
β_A ≥ 0.275 and every β_A ≤ −0.29** (two-coupling action, β_F = 0). This is a limit of the single-link criterion, not of the
physics (block criteria can go further, r2-curvature §2.5).

## 3. The certified window at β_F = 0

### 3.1 The object

Single coarse link, conditional density on S³ `ρ ∝ exp(uᵀQu)`, `Q = κ Σ_{k≤6} a_k a_kᵀ`, `κ = 4β_A/3`; moving one neighbour by
geodesic distance δ moves one staple `a` along a geodesic with unit tangent `b ⊥ a`, and `∂_s log ρ = 2κ h₂ + const`. So the
W₁ Dobrushin coefficient of a neighbour sharing one plaquette is `≤ (8|β_A|/3) N_A`, `N_A = sup ‖(h₂ − E_ρh₂)ρ‖_KR` over all
configurations, and the column over the 18 neighbours is `48|β_A| N_A`. (Integrate the derivative along the geodesic: W₁ is a
norm on zero-mass measures.) The eigenvalues of `Σ a_k a_kᵀ` fill the simplex `Δ = {s ≥ 0, Σs = 6}` (Schur–Horn: the Gram
matrix with unit diagonal exists for every such spectrum), and `κΔ ⊂ κ'Δ` up to a shift of `Q` by a multiple of `I` (which does
not change the law) for `0 < κ < κ'`; same for negative κ. **So every supremum over configurations below is nondecreasing in
|β_A| at fixed sign, and a certificate at β_A* covers `[0, β_A*]`.**

### 3.2 Bound B1 (paper)

For a configuration with eigenbasis of `Q` and `M = sym(abᵀ)` (traceless, eigenvalues ±½), write `f = (uᵀMu − m)ρ` (density
w.r.t. Haar), so `N = ‖f·Haar‖_KR`. Then

  `N ≤ ‖h₂·Haar‖_KR + ‖(f − h₂)·Haar‖_KR ≤ 1/16 + ‖f − h₂‖_{Ḣ⁻¹}`,

using Theorem 1 and `‖g·Haar‖_KR ≤ ‖g‖_{Ḣ⁻¹}` for mean-zero `g` (`∫φg = ∫∇φ·∇ψ ≤ ‖∇φ‖₂‖∇ψ‖₂`, `|∇φ| ≤ 1`). `f − h₂` is even, so
it has spherical-harmonic degrees 2, 4, 6, … with Laplace eigenvalues `ℓ(ℓ+2) = 8, 24, 48, …`:

  `‖f − h₂‖²_{Ḣ⁻¹} ≤ ‖(f − h₂)₂‖²/8 + ‖f_{≥4}‖²/24`  (`h₂` is pure degree 2).

Both terms are explicit in Bingham moments of degree ≤ 2 (x = squared coordinates in the eigenbasis of `Q`, eigenvalues λ):
the degree-2 part of `f` is `uᵀS_f u` with `(S_f)_{ij} = 24 E_λ[x_ix_j] M_{ij}` (i ≠ j) and `diag S_f = 12 P C d`
(`d = diag M`, `C = Cov_λ(x)`, `P = I − J/4`), from `E_Haar[(uᵀSu)(uᵀTu)] = tr(ST)/12`; `‖f‖² = ζ E_{2λ}[(uᵀMu − m)²]` with
`ζ = Z(2λ)/Z(λ)²`; `‖f_{≥4}‖² = ‖f‖² − ‖f₂‖²`. In the eigenbasis the quadratic form in `M` is block diagonal (six off-diagonal
pairs, one diagonal block on `1^⊥`); **relaxing `M` to all traceless matrices with `‖M‖_F² = ½`** gives

  `N ≤ B1(λ) := 1/16 + √(½ max(max_{i<j} P_{ij}, λ_max(Q_d|_{1^⊥})))`,
  `P_{ij} = (w_{ij} − 1)²/96 + (2ζ E_{2λ}[x_ix_j] − w_{ij}²/12)/24`, `w_{ij} = 24 E_λ[x_ix_j]`,
  `Q_d = (12PCP − P)²/96 + P(ζ C₂ − 12 CPC)P/24`, `C₂ = E_{2λ}[(x − E_λx)(x − E_λx)ᵀ]`.

`B1 = 1/16` exactly at the uniform law. It is a function of the eigenvalues only, symmetric under permutations.

### 3.3 The certificate (`cert_adjoint.py`)

* **Moments.** `S_α(λ) = E_Haar[x^α e^{λ·x}]` with `x ~ Dirichlet(½,½,½,½)` (the squared coordinates of a uniform point of S³),
  as the power series `Σ_β λ^β/β! · Π(½)_{α_i+β_i}/(2)_{|α|+|β|}` with nonnegative terms (λ ≥ 0 after a shift), evaluated as a
  product of four univariate polynomials truncated at degree 48; a-priori relative rounding bound `1e−12` (needed `≤ 1e−13`) and
  the tail bound `L^{K+1}/(K+1)!/(1 − L/(K+2))` (`bingham.py`).
* **Cells.** Boxes in `(s₁, s₂, s₃)` covering the sorted simplex `s₁ ≥ s₂ ≥ s₃ ≥ s₄ = 6 − Σ ≥ 0` (B1 is permutation symmetric).
  Every quantity is carried as a mean-value form: centre value (interval), value over the cell and gradient over the cell
  (intervals; the base series and their λ-derivatives are monotone in λ, so their ranges over a cell lie between the corner
  values), propagated through +, −, ×, 1/x; the cell enclosure is `centre + Σ_k grad_k·[−r_k, r_k]` ∩ direct range. The top
  eigenvalue on `1^⊥` is bounded by Weyl's inequality around the midpoint matrix, whose own top eigenvalue is verified by
  Sylvester's criterion in interval arithmetic. All operations rounded outward (`nextafter`), as round 2's `tree_cert.py`.
* **Adaptive bisection** until every cell's upper bound satisfies `48|β_A| B1 < 1` (window mode) or `B1 < T` (supremum mode).
  The supremum is over every cell of the domain, not a scan. κ is taken `(1 + 10⁻¹²)` larger than `4β_A/3` (monotonicity covers
  the exact value).

### 3.4 Results

| β_A | mode | certified `sup B1` (`N_A ≤`) | column `48|β_A|·sup B1` | float sup B1 | cells | time |
|---|---|---|---|---|---|---|
| +0.05 | sup | 0.07250 | 0.174 | 0.07101 | 4158 | 90 s |
| +0.10 | sup | 0.08150 | 0.391 | 0.07971 | 6274 | 148 s |
| +0.15 | sup | 0.09020 | 0.649 | 0.08834 | 6942 | 158 s |
| +0.20 | sup | 0.09860 | 0.947 | 0.09662 | 7853 | 189 s |
| **+0.21** | window | 0.099203 | **0.99997** | 0.09821 | 9165 | 218 s |
| −0.05 | sup | 0.07210 | 0.173 | 0.07060 | 5466 | 130 s |
| −0.10 | sup | 0.07970 | 0.383 | 0.07813 | 8622 | 205 s |
| −0.15 | sup | 0.08660 | 0.624 | 0.08499 | 11907 | 287 s |
| −0.20 | sup | 0.09300 | 0.893 | 0.09116 | 14895 | 360 s |
| **−0.22** | window | 0.094697 | **0.999998** | 0.09342 | 18821 | 465 s |

(`cert_window.json`, `run_*.log`. "sup" mode certifies `B1 < T` with `T` ≈ 1.02 × the float supremum; "window" mode
certifies `48|β_A|·B1 < 1`. The float maxima all sit at the vertex `s = (6, 0, 0, 0)`.)

**Certified window (β_F = 0): the single-link W₁ adjoint column is < 1 for −0.22 ≤ β_A ≤ 0.21.**

Where it stands: linearised exactly 1/3; certified 0.21 (+) / 0.22 (−); certified ceiling 0.275 (+) / 0.29 (−); float
crossing of the symmetric configurations ≈ 0.272 (+) / ≈ 0.285 (−). The gap between 0.21 and the ceiling is the bound B1,
not the certificate (the certificate costs ≈ 2 % on B1): (i) the relaxation of `M` to all traceless matrices (the moved
staple must be one of the six, `Σ a_i²/s_i ≤ 1`; the float constrained bound gives ≈ 0.235, `explore2.log`); (ii) the triangle
inequality plus Ḣ⁻¹ for the deviation from the uniform point, which charges at first order what is partly second order (at
the aligned configuration at β_A = 0.22: B1 = 0.0998 relaxed, 0.0878 constrained, against the exact 0.0726 of
Theorem 2).

## 4. Small β_F > 0: the two-parameter window (paper bounds + certified suprema)

With `β_F ≠ 0` the conditional law is `ρ' ∝ exp(⟨A,u⟩ + uᵀQu)`, `|A| ≤ a := 6|β_F|`, and the derivative along the moved staple
is `β_F⟨u,b⟩ + 2κh₂` (minus means). Per plaquette: `k ≤ |β_F| N_F + (8|β_A|/3)(N_A + Δ_e + Δ_o)` with

* **Even/odd split** of `ν = (h₂ − m')ρ'` under `u ↦ −u`: `ρ'_e = ρ_Q cosh⟨A,u⟩/Z_A`, `ρ'_o = ρ_Q sinh⟨A,u⟩/Z_A`
  (`Z_A = E_Q cosh⟨A,u⟩ ∈ [1, cosh a]`). `‖ν_e − (h₂ − m_Q)ρ_Q‖_TV ≤ 2(cosh a − 1)`, so **`Δ_e = π(cosh a − 1)`** (KR ≤ (π/2)·TV for
  zero-mass measures on a space of diameter π). For the odd part a test function can be taken odd, hence `|φ| ≤ π/2`:
  **`Δ_o = (π/2) sinh a √((V_h + (cosh a − 1)²) σ₁)`** by Cauchy–Schwarz, `V_h = sup Var_Q(h₂)`, `σ₁ = sup max_i E_Q x_i`.
* **Fundamental part:** `N_F ≤ ‖(⟨u,b⟩ − m_F)ρ'‖_{L²}/√3` (mean zero, degrees ≥ 1), `ρ' ≤ e^a ρ_Q`, `|m_F| ≤ sinh a`:
  **`N_F = e^a √ζ (√σ₂ + sinh a)/√3`**, `σ₂ = sup max_i E_{2Q} x_i` (at the uniform point 0.2887 against the exact 8/(9π) = 0.2829).

The suprema ζ, σ₁, σ₂, V_h are certified with B1 (same cells). Every term increases in |β_A| and |β_F|, so a corner bounds
its rectangle. Corners (`window2.py`, `window2.json`; k rounded up, column `18k < 1`):

| corner `c` | `|β_A| ≤` | `|β_F| ≤` | `N_A` used | `k` (rounded up, 10⁻⁷) | column `18k` |
|---|---|---|---|---|---|
| 0 | 0.21 | 0 | 0.09920 | 0.0555539 | 0.99997 |
| 1 | 0.20 | 0.0020 | 0.09860 | 0.0551020 | 0.99184 |
| 2 | 0.15 | 0.0145 | 0.09020 | 0.0554286 | 0.99771 |
| 3 | 0.10 | 0.0265 | 0.08150 | 0.0547064 | 0.98472 |
| 4 | 0.05 | 0.0425 | 0.07250 | 0.0553026 | 0.99545 |
| 5 | 0 | 0.0685 | 1/16 | 0.0550391 | 0.99070 |

(For each |β_A| the larger of the two signs' certified suprema is used; the negative side alone reaches 0.22 at β_F = 0.
Arithmetic: `window2.py`, 50-digit mpmath, rounded up.) For comparison, Leg C's fitted values at L√σ = 3.15 and 4.2 (c2a §5.1:
β_F = 0.0089, β_A = −0.0017; β_F = −0.0016, β_A = −0.0011) lie inside corner 4; the one at 2.1 (β_F = 0.19) does not. (Leg C's
variable is near noise in the adjoint channel, c2a §5.1, so this is a consistency check, not evidence.)

The first-order dependence on β_F is crude (the true first-order effect of `A` on the adjoint coefficient vanishes by parity;
the bounds charge it at order `a`), so the β_F-direction of the window is conservative.

## 5. Lean (`formal/ProofPhase/Certified/AdjointW.lean`)

Built in `~/formal-c3c` against the current tree; no `sorry`, no `native_decide`, no new axioms; `axioms-c3c.sh` prints the
axioms of the 9 headline theorems: all `propext, Classical.choice, Quot.sound`.

**The hypothesis, exactly.** `CertifiedAdjointW : Prop` says: for each corner `c : Fin 6` of the table in §4
(`cornerA c`, `cornerF c`, `cornerK c`), every torus `(ℤ/Nℤ)⁴` with `N ≥ 2`, every two-coupling action `twoCoupling βF βA`
(plaquette factor `β_F t_p + (β_A/3)(4t_p² − 1)`, `t_p = ½ Re tr U_p`, SU(2) links) with `|β_A| ≤ cornerA c`,
`|β_F| ≤ cornerF c`, and every pair of distinct links `i, z`:
`IsInfluenceBoundW geodSU2 {i} (siteSpec (haarG SU2) plaqSupp (twoCoupling βF βA) i) z (cornerK c · common i z)`,
i.e. for every Borel `F` reading only link `i`, `L`-Lipschitz there for `geodSU2 a b = arccos(½ Re tr(ab⁻¹))`, and every
boundary configuration `σ` and new value `s` at `z`: `|∫F dq^σ − ∫F dq^{σ[z↦s]}| ≤ cornerK c · common(i,z) · L ·
geodSU2(σ_z, s)`, where `q^σ` is the single-link conditional law (Gibbs, Haar reference) and `common(i,z)` the number of
plaquettes containing both links. This is what §3–4 establish: the reduction (Theorems 1–2, B1, the β_F bounds, the
derivative-along-a-geodesic argument) is paper; the suprema are certified by `cert_adjoint.py`; the corner arithmetic by
`window2.py` (50-digit mpmath, rounded up to 10⁻⁵). It is a statement about the effective action only: no blocking, no H1.

**What is proved in Lean from it** (all `ProofPhase.Certified.*`):

| theorem | statement | mark |
|---|---|---|
| `decay_of_siteW` | Dobrushin's theorem with W₁ coefficients for the single-site specification of any local potential: column sums `≤ γ`, range `D₁`, `γe^{λD₁} < 1` ⇒ `|Cov(f,g)| ≤ D_c(1 − γe^{λD₁})⁻¹(Σv_a)L_g e^{−λR}` (f bounded, g Lipschitz) | substantive reduction (wrapper of `OneScale.BlockSpec.theoremA_W` with `Attempts.R3.factorSpec`) |
| `potential_twoCoupling`, `abs_twoCoupling_le` | the two-coupling action is a local potential, `|φ| ≤ |β_F| + |β_A|` | elementary |
| `cornerColumn_lt_one` | `18 · cornerK c < 1` for all six corners | `norm_num` (definitional arithmetic) |
| `column_le`, `dist_le_of_common` | column sum of `cornerK·common` ≤ `18·cornerK` (via `sum_common_le`); positive coefficients only between links of one plaquette, at `linkDist ≤ 1` | elementary |
| **`limitDprimeW_twoCoupling`** | `CertifiedAdjointW` ⇒ `LimitDprimeW (fun _ => twoCoupling βF βA)` for every action in the window: in every coarse volume the single-link W₁ influences have column sum `≤ 18·cornerK c < 1` and range 1 | assembly (composition); the content is the hypothesis |
| **`twoCoupling_decay`** | `CertifiedAdjointW` ⇒ uniform-in-`N` exponential decay `|Cov(f,g)| ≤ π(1 − 18k e^λ)⁻¹(Σv)L_g e^{−λR}` for every action in the window, every `λ` with `18k e^λ < 1` | composition |
| `exists_rate_corner` | such `λ > 0` exists at every corner | elementary |

**Relation to `AdjointHalf` of `CentreSplit.lean` (the brief's item 3).** The brief asked to prove that the certified numbers
imply `AdjointHalf`. That is impossible on most of the window, and the reason is exact: `AdjointHalf` is the sup (TV) form,
whose adjoint column for this family is exactly `18 tanh(2|β_A|/3)` (c2a §1.4: the supremum of the centre-blind pair
oscillation `4|β_A|/3` is attained), `< 1` iff `|β_A| < 1.5 artanh(1/18) = 0.0834`. For `0.0834 ≤ |β_A| ≤ 0.21` the sup-form
`AdjointHalf` is **false** for these actions while the W₁ criterion is certified. So the Lean statement is the W₁ analogue:
`LimitDprimeW` (single-link W₁ influences of the whole effective measure, uniform in the volume). At `β_F = 0` the
centre-charged part is zero and `LimitDprimeW` **is** the W₁ adjoint half; at `β_F ≠ 0` the W₁ coefficient does not split
into halves at the level of influence bounds (it splits only for the derivative of each conditional law, c2a §2.2), and the
certificate bounds the sum (§4), so the corners certify "adjoint half + centre half < 1" in W₁ form.

**How the W₁ route changes the assembly (paper; not yet in Lean).** The blocked route (`slabDecay_of_blockedRoute`,
`blockedTorusRoute_of_halves`) has three inputs: `H1Local`, `LimitDprime`, `ObsTransfer(Phys)`. In W₁ form:
1. `LimitDprime` → `LimitDprimeW` (this file; certified for the two-coupling family on the window).
2. **Openness needs `H1LocalLip`** (c2a §2.4), now quantitatively: if the level-k single-link log-density differs from the
   limit one by `δ` with `‖δ‖_∞ ≤ ε` and `Lip_z(δ) ≤ η` (geodesic metric), the W₁ coefficient moves by at most
   `πη + (3π/2) G (e^{2ε} − 1)` per neighbour, `G = sup|∂_z V_∞|` (the derivative changes by `∂_zδ`; the law by a density
   ratio in `[e^{−2ε}, e^{2ε}]`; KR ≤ (π/2)·TV for zero-mass measures). So `H1LocalLip` (`Σ_{x∋i,z}(‖V_k − V_∞‖_∞ + Lip_z(V_k − V_∞))
   e^{λd} → 0`) ⇒ the level-k theories satisfy the W₁ criterion with `(1 + γ)/2` from some `k₀` on (the W₁ analogue of
   `levelFlat_of_local`). `H1Local` (sup norm only) does not suffice: a sup-small, Lipschitz-large change can move W₁
   coefficients by O(1).
3. **Observables:** `decay_of_siteW` gives decay for `g` Lipschitz; bounded block observables follow by c2a §2.2's
   regularisation (one factor range lost), so `ObsTransfer(Phys)` is unchanged in form.
So the W₁ blocked route is: `H1LocalLip ∧ LimitDprimeW ∧ ObsTransferPhys ⇒ BlockedTorusRoute`; its Lean form needs the
W₁ openness lemma above and a W₁ version of `slabDecay_of_blockedRoute` (next step). `H1LocalLip` is the c3d-h1
workstream's business: what it must deliver for this route is Lipschitz (not only sup) control of the effective potentials.

## 6. Marks

| result | mark | substantive / definitional |
|---|---|---|
| `k_A = 1/16`, optimal test function and transport (Thm 1) | **paper** (complete proof here), checked by MC and quadrature | substantive (new; closes c2a's conjecture) |
| exact coefficient at Klein-symmetric Bingham laws (Thm 2) | **paper** | substantive |
| W₁ coefficient ≤ `(8|β_A|/3)·sup‖(h₂−m)ρ‖_KR`, configuration simplex, monotonicity in |β_A| | **paper** | substantive-elementary |
| bound B1 (KR ≤ 1/16 + Ḣ⁻¹ of the deviation, harmonic split, relaxation over M) | **paper** | substantive |
| `sup B1` and the extras at the listed β_A; the window `48|β_A| sup B1 < 1` at +0.21 and −0.22 | **certified** (`cert_adjoint.py`) | substantive (computer-assisted) |
| β_F bounds (Δ_e, Δ_o, N_F) | **paper** | elementary |
| two-parameter corners | **certified** suprema + 50-digit arithmetic (`window2.py`) | computer-assisted |
| ceiling (criterion fails beyond β_A ≈ 0.275 / −0.29) | **certified** (`cert_ceiling.py`) + Thm 2 | substantive |
| `decay_of_siteW` | **Lean** | substantive reduction (wrapper of Theorem A (W)) |
| `potential_twoCoupling`, `column_le`, `dist_le_of_common` | **Lean** | elementary |
| `cornerColumn_lt_one` | **Lean** (`norm_num`) | definitional arithmetic |
| `limitDprimeW_twoCoupling`, `twoCoupling_decay` | **Lean**, modulo the named hypothesis `CertifiedAdjointW` | composition; the content is in the hypothesis |
| W₁ openness under `H1LocalLip`; W₁ blocked route | **paper** (§5), not in Lean | substantive-elementary |
| true supremum of the W₁ coefficient lies in the gap between B1 and the ceiling | **open**; constrained-M B1 would give ≈ 0.235 (float, `explore2.log`) | — |

Weaker / equal / stronger than the mass gap (round-4 discipline): every theorem here is about one effective action (the
two-coupling family on the coarse torus) and is **much weaker** than the mass gap: it is the adjoint half of the crossover
criterion at L₁ for that family. Yang–Mills enters only through the open hypotheses (H1 in Lipschitz form, ObsTransfer).

## 7. Unit tests

* **Photon (4D U(1) at weak coupling).** The adjoint half alone passes the photon, and must: U(1) Wilson factors are odd under
  a single centre flip, so their centre-blind part is zero (`centreAvg_eq_zero_of_odd`) and γ_A = 0. That is fine because the
  adjoint half is never used alone: the photon is excluded by the centre (fundamental) part, whose W₁ single-link column for
  U(1) is `18·(2/π)·β`, ≥ 1 for β ≥ π/36 = 0.087 (r2-curvature §2.4), while weak-coupling U(1) has β = 1/e² ≈ 11 and does not
  run. In this note's window the fundamental coupling is certified only up to |β_F| ≤ 0.0685 (corner table), nowhere near a
  photon. Our certified statement is SU(2)-specific (Bingham laws on S³) and gives U(1) nothing. Passed.
* **Z₂.** No centre-blind part; gap-type statements only; the two-coupling window is a strong-coupling (disordered) regime
  and weak-coupling Z₂ is not in it. Passed (gap-type claims hold for Z₂ at strong coupling, as they should).
* **Finite subgroups.** The certificate uses the continuous geodesic metric and Bingham densities on S³; it does not apply
  to atomic conditional laws, and claims nothing for them. Passed (no claim).
* **Deconfinement.** The theorem is about a given effective action; which L₁ puts the true blocked action in the window is
  H1's business. The window is a high-temperature (strong effective coupling) region; a one-block-thick torus below 1/T_c has
  ordered Polyakov loops and its effective action has large centre-charged couplings, outside the corners. Consistent.
* **Triviality, Banks–Zaks.** No existence claim; a conformal-window theory never flows into a disordered effective action,
  so it never enters the window. Passed.

## 8. Blueprint changes (proposed for `PROOF-BLUEPRINT.md`, P4.1″; not edited here)

* P4.1″: `k_A = 1/16` (paper, exact; linearised pure-adjoint W₁ window exactly β_A < 1/3).
* P4.1″: **W₁ adjoint half certified** for the two-coupling family: β_F = 0, β_A ∈ [−0.22, 0.21] (certified), with the
  two-parameter corners of §4; it cannot exceed β_A ≈ 0.275 (β_A > 0) / −0.29 (β_A < 0) (certified ceiling). Against the
  sup form (|β_A| < 0.0834) a factor 2.5 wider. Lean: `ProofPhase/Certified/AdjointW.lean` (`limitDprimeW_twoCoupling`,
  `twoCoupling_decay` under the named hypothesis `CertifiedAdjointW`).
* P3 (H1): the W₁ route needs `H1LocalLip` (Lipschitz control of the effective potentials), with the quantitative openness
  bound of §5; this is the requirement to hand to c3d-h1.
* A measured β_A at L₁ (Leg C, c3b's good-blocking refit) can now be compared with a theorem: |β_A| ≤ 0.21 with β_F = 0
  (or within the corners) implies the W₁ criterion for the fitted two-coupling action.

## 9. Next step

Close the gap between the certified window (0.21) and the ceiling (≈ 0.275) for β_A > 0, and formalise the W₁ route:
(1) certify the **constrained** bound (the moved staple is one of the six staples, `Σ a_i²/s_i ≤ 1`; float ≈ 0.235) by adding
the staple direction to the cells (5 more dimensions, but only near the vertex `s = (6,0,0,0)` where B1 binds); (2) replace
the Ḣ⁻¹ treatment of the degree ≥ 4 part by an exact transport for the symmetric part (Theorem 2) plus Ḣ⁻¹ only for the
Klein-asymmetric remainder (whose true effect on the coefficient vanishes at first order by parity, while the Ḣ⁻¹ bound charges it at first order); (3) in Lean, the W₁ openness lemma under
`H1LocalLip` and the W₁ blocked route `H1LocalLip ∧ LimitDprimeW ∧ ObsTransferPhys ⇒ BlockedTorusRoute`, so that the
assembly can take this file's output directly.

## References (ideas only)

Kantorovich–Rubinstein duality and Beckmann flows (Villani, *Optimal Transport*, 2009); Dobrushin, Theory Probab. Appl. 15 (1970)
458 (metrics); Bingham, Ann. Statist. 2 (1974); the Schur–Horn theorem. Project: `../c2a-adjoint/NOTE.md`,
`../../attempts/r2-2d/NOTE.md` (certificate method), `../../attempts/r2-curvature/NOTE.md`.
