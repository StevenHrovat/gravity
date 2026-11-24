# Pre-registration: one-loop self-energy of the blocked coarse plaquette (workstream 1, 2026-11-22)

Written before running `selfenergy.py`. One CPU process, `CUDA_VISIBLE_DEVICES=-1`, expected runtime under 5 minutes.

**Question.** Does the slice-smeared, time-decimated blocking of `formal/ProofPhase/RouteA/Blocking.lean` (iterated
`smearBlock w`) remove the linear (perimeter) self-energy divergence that makes plain decimation converge to pure noise at
fixed physical block size L₁ = ℓ a?

**Model (linearised, abelian, Feynman gauge; one-loop power counting made numerical).** At small fields the projection
`A ↦ A/√|det A|` of a path sum keeps the weighted mean phase, so a level-n coarse link carries the current
`J = (straight + w Σ staples)/(1 + w·#staples)` of level-(n−1) link currents (#staples = 4 for spatial, 6 for temporal
links in d = 4). The coarse plaquette (a closed loop of four coarse links in a spatial-temporal plane and in a spatial plane)
has flux variance `σ²(ℓ) = (1/V) Σ_{k≠0} Σ_μ |Ĵ_μ(k)|² / k̂²`, `k̂² = Σ 4 sin²(k_μ/2)`, on a periodic L⁴ lattice with
L = 4ℓ (L = 3ℓ at ℓ = 16). ⟨W⟩ ≈ exp(−g² σ²/2) for the coarse plaquette.

**Predictions (decision rule fixed now).**
1. Decimation (w = 0): σ²(ℓ)/ℓ approaches a positive constant (linear divergence): σ²(16)/σ²(8) ≥ 1.7.
2. Smeared (w = 0.5 and w = 1): σ²(ℓ) converges: σ²(16)/σ²(8) ≤ 1.15, and σ²(16) ≤ 0.5 · σ²_dec(16).
3. Both plane orientations (spatial-temporal, spatial-spatial) behave the same way (the time direction, smeared only by
   decimation for spatial links, costs no divergence: the power-counting claim of NOTE.md §2).
If 2 fails for both weights, the power-counting claim of NOTE.md §2 is withdrawn for this blocking (one smearing step per
level is not enough). With g²(a) ∝ 1/log ℓ the decimated plaquette then has g²σ² ∝ ℓ/log ℓ → ∞ (noise), the smeared one
g²σ² → 0 at fixed bare-coupling running; the physical non-triviality at L₁ is a non-perturbative question this test does
not address.
