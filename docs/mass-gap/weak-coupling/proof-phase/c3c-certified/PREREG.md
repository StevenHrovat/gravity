# Pre-registration: cycle 3, workstream 3 (c3c): the adjoint half's constant as a theorem (2026-11-22, before any run)

Rules: `../../attempts/RULES.md` (proof phase). Numerics: CPU only, `CUDA_VISIBLE_DEVICES=-1`, one process, each run at most 30
minutes. Builds on `../c2a-adjoint/NOTE.md` §2 (the W₁ form of the adjoint half on SU(2) sites) and its scripts.

## Object

Single coarse link, conditional law on S³ (unit quaternions u) of the two-coupling plaquette action
`φ(t) = β_F t + (β_A/3)(4t² − 1)`, six staples `a_k`: `ρ(u) ∝ exp(⟨A, u⟩ + uᵀQu)`, `A = β_F Σ a_k`, `Q = κ Σ a_k a_kᵀ`,
`κ = 4β_A/3`. Moving one neighbouring link by geodesic distance δ moves one staple `a` by δ in a tangent direction `b ⊥ a`.
Per-neighbour W₁ coefficient (cost: geodesic distance on S³):

  `C = sup_config ‖∂ρ‖_KR ≤ β_F N_F + (8|β_A|/3) N_A`, `N_A = sup ‖(h₂ − E h₂)ρ‖_KR`, `h₂ = ⟨u,a⟩⟨u,b⟩`,
  `N_F = sup ‖(⟨u,b⟩ − E⟨u,b⟩)ρ‖_KR`; column sum over the 18 neighbours: `18 C < 1` is the single-link W₁ criterion.

## Analytic part (paper, written in NOTE.md; numerically checked)

1. `k_A = N_A(Haar) = 1/16` exactly, by an explicit 1-Lipschitz test function (signed distance to `a^⊥ ∪ b^⊥`) and an explicit
   transport along the great circles orthogonal to those walls (balanced ray by ray by the reflection symmetry).
2. The same formula for every Bingham law invariant under the reflections in `a^⊥` and `b^⊥` (a, b eigenvectors of Q):
   `N_A(Q, a, b) = E_ρ[|u_a u_b| min(arcsin|u_a|, arcsin|u_b|)]`. Gives a rigorous *lower* bound on the supremum (a ceiling for
   the window) at any symmetric configuration.
3. Bound B1 for all configurations: `N_A ≤ 1/16 + ‖f − h₂‖_{Ḣ⁻¹}`, `f = (h₂ − m)ρ` (density w.r.t. Haar), with the harmonic split
   (degree 2 exactly through the covariance operator, degrees ≥ 4 with eigenvalue 24), relaxed over all traceless M with
   ‖M‖_F² = 1/2 and all Q with eigenvalues in κ·{s ≥ 0, Σs = 6}. Everything reduces to Bingham moments of degree ≤ 2 at Λ and 2Λ.
4. β_F > 0: even/odd split under u ↦ −u; explicit bounds Δ_e ≤ π(cosh|A| − 1), Δ_o ≤ (π/2) sinh|A| √(V_h σ_max), N_F by the
   Ḣ⁻¹ bound with eigenvalue 3; |A| ≤ 6β_F.

## Runs

1. **Checks (float/MC, seconds; `checks.py`):** k_A = 1/16 (MC and 2D quadrature); the symmetric formula at the aligned
   configuration against c2a's LP (`kA_bingham.log`: 0.0736 at β_A = 0.26); B1 at Haar = 1/16 exactly.
2. **Design (float, `explore.py`, minutes):** B1 over the eigenvalue simplex for β_A ∈ {±0.05, …, ±0.3}; the symmetric formula
   over symmetric configurations (to choose the best ceiling configuration). Float only; chooses the β values for step 3.
3. **Certificate (`cert_adjoint.py`, ≤ 30 min per run):** interval arithmetic with outward rounding (as round 2's `tree_cert.py`):
   Bingham moments as power series in λ with exact rational Dirichlet moments, rigorous truncation tail; second-order Taylor
   models on cells of the eigenvalue simplex (value and gradient at the cell centre, Hessian enclosed over the cell by monotone
   corner bounds of the positive series), adaptive bisection until every cell's upper bound is below the target. Output: a
   certified `N̄_A(β)` (supremum over every configuration, not a scan), monotone in |β_A| because the configuration sets are nested.
   Target: the largest β_A* on the grid 0.005·ℤ with `48 β_A* N̄_A(β_A*) < 1`, for each sign of β_A. Then the two-parameter
   window (β_A, β_F) on a staircase of corner points.
4. **Ceiling (certified lower bound on the supremum):** the symmetric formula at the chosen symmetric configuration by interval
   quadrature over the unit disk (2D), giving β_A above which the single-link W₁ criterion is certified to fail.

## What would count as failure

* Step 1 disagreeing with 1/16 or with c2a's LP beyond its discretisation error: the analytic claims are wrong; stop and repair.
* B1's window below c2a's sup-form window 0.0834: B1 useless; report that.
