# Pre-registration: criterion constants and coupling matching (2026-11-21, before running)

Tiny exact computations (one- and two-dimensional quadrature on S³, Bessel functions, root finding). CPU, one process,
`CUDA_VISIBLE_DEVICES=-1`, expected runtime well under one minute. Script `criterion_numbers.py`, output `criterion_numbers.json`.
No lattice simulation. Nothing here re-verifies an established number; the quantities are new to this project.

Notation: S³ = SU(2) with the geodesic metric ρ (angle on the unit 3-sphere), Haar = normalised volume. For a mean-zero density g,
‖g‖_KR = sup over 1-Lipschitz f of ∫ f g dHaar (the W₁ norm of g·Haar). b ⊥ a unit vectors in ℝ⁴.

## Quantities

- **N1.** ‖h₁‖_KR, h₁(u) = ⟨u, b⟩: lower bound with the test f = arcsin⟨u, b⟩ (expected exact, 8/(9π) = 0.28294), upper bound
  (Poincare/H⁻¹: ‖g‖_KR ≤ (∫g²/λ)^{1/2} for an eigenfunction with Laplace eigenvalue λ; here λ = 3) 1/(2√3) = 0.28868.
- **N2.** ‖h₂‖_KR, h₂(u) = ⟨u, a⟩⟨u, b⟩: upper bound (λ = 8) (1/192)^{1/2} = 0.07217; lower bounds from the tests f = h₂ (gives
  1/24) and f = ½(arcsin|y₁| − arcsin|y₂|), y = ((⟨u,a⟩ + ⟨u,b⟩)/√2, (⟨u,a⟩ − ⟨u,b⟩)/√2). Report the best lower bound.
- **N3.** Nonlinear check of the adjoint coefficient at the aligned configuration (all six staples equal): density ∝ exp(6c x²),
  x = ⟨u, e⟩, c = 4β_A/3; lower bound on the per-neighbour W₁ coefficient (1/6)·(E x_e² − E x_b²) (test f = x_e x_b). Compare with
  the linearised value 2c‖h₂‖_KR for β_A ∈ {0.1, 0.25, 0.5, 1}.
- **N4.** Fundamental vMF check: tangential and radial W₁-Lipschitz lower bounds of vMF(r n) on S³ (tests arcsin⟨u,b⟩ and the exact
  1D radial transport), r ∈ [0, 3]; report whether the lower bounds stay ≤ their r = 0 value (indication only, not a proof that
  sup_r L(r) = L(0)).
- **N5.** Matching. u_F(β) = I₂(β)/I₁(β) (Wilson SU(2)); u_A(β_A) = ⟨χ_A⟩/3 for the single-plaquette weight exp((β_A/3)χ_A),
  χ_A = 4cos²θ − 1, Haar density (2/π)sin²θ. Invert: β_F from u_F = e^{−σL₁²}, β_A (and the Wilson-only β) from
  u = e^{−mL₁/4}, for L₁√σ ∈ {2, 2.5, 3, 3.5, 4, 5, 6, 8.4} and m/√σ ∈ {3.5, 3.75, 4.0}.
- **N6.** Thresholds (linearised single-link W₁ Dobrushin, d = 4, 18 neighbours): β_F* = 1/(18‖h₁‖), β_A* = 1/(48‖h₂‖), the
  smallest L₁√σ at which each matched coupling enters, and α conversions (α = 1/(πβ) for Wilson SU(2); for the adjoint term the
  naive tree-level equivalent β_eq = β_F + (8/3)β_A).

## Expectations (written before running)

- N1 lower ≈ upper (within 2 %). N2 bracket closes to within ≈ 30 %; β_A* between 0.29 and 0.5.
- N3: at β_A ≈ 0.5 the aligned configuration gives a coefficient comparable to or above the linearised one (the sup over
  configurations is worse than linearisation at the physical point).
- N5/N6: β_F from σ ≈ 5·10⁻⁴ at L₁√σ = 3; β_A ≈ 0.5 at L₁√σ = 3; the adjoint channel enters the linearised window between
  L₁√σ ≈ 3 and 4.5.

## What decides what

These numbers are the X side (criterion windows) and a model-dependent Y side (strong-coupling proxy). The note states the model
dependence; no verdict on H2 follows from them, only the size of the gap between criterion and proxy.
