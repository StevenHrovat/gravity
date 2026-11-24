# Pre-registration: round 2, attempt A (2D compact U(1), certified one-box bound) (2026-11-21, before any run)

Rules: `../RULES.md` (round 2 additions). CPU only, `CUDA_VISIBLE_DEVICES=-1`, one process, at most 15 minutes per run. Scripts and
outputs in this folder. Builds on `../../followups/` (PREREG-FOLLOWUPS.md, Experiment 2; `u1_2d_box.py`).

## What is certified, and in which form

Model: 2D compact U(1), Wilson action `β Σ_p (1 - cos θ_p)`, thin squares V_ℓ (links with both ends in x + {0..ℓ}², the Lean
`thinCube ℓ x`, d = 2), cost on U(1) = arc length (geodesic distance), W-form influence coefficients (Lean `IsInfluenceBoundW`).
Per link direction the GDS sum is (followups 2a; coverage ℓ(ℓ+1)):

  γ(ℓ) = [2 Σ_{i=0}^{ℓ-1} k(P_i) + 2(ℓ-1) k(D) + 4 k(P_0)] / (ℓ(ℓ+1)).

The exact reduction (followups 2a): modulo the interior gauge group the block law is that of N = ℓ² + 4ℓ i.i.d. von Mises(β) angles
conditioned on their sum ≡ Φ_b (mod 2π); the shell enters only through Φ_b and isometric translations. So every k is a supremum over
Φ_b ∈ [0, 2π) of a W₁ rate on this conditioned law, with the link metric of the quotient (face links: |δf|; inner plaquettes: earth
mover cost on the ℓ×ℓ grid, Manhattan).

### Upper bounds (new, deterministic; no Monte Carlo)

- **D (dangling link at a face-interior site).** The perturbation is a boundary gauge rotation; given u = y_l + y_r (the two outer
  plaquette variables at the site), the conditional law of y_l is von Mises(2β|cos(u/2)|) and is shifted rigidly. Coupling: move y_l,
  y_r and the inner link at the site together (3 links per unit). Rate of the optimal 1D circle flow for a rigid shift of a von Mises(κ)
  density = 2 P_κ(|x| < π/2) − 1 =: R(κ) (closed form). So

    k(D) ≤ 3 sup_Φ ∫ ρ_Φ(u) R(2β|cos(u/2)|) du,   ρ_Φ(u) = g_2(u) g_{N-2}(Φ − u) / g_N(Φ),

  g_m the density of a sum of m i.i.d. von Mises(β) angles (Fourier coefficients (I_n/I_0)^m).
- **P_i (parallel link at face position i; corner links = P_0).** An explicit **tree flow**: a binary tree over the N variables;
  at each node with children A, B and node sum S moving at unit rate, the 1D flow of Y_A given S, velocity a(y) = (G_S(y) + c(S))/ρ_S(y),
  G_S(y) = −∂_S ∫^y ρ_S (any constant c(S): every choice is a valid flow; c is chosen by float optimisation, which cannot bias a bound),
  child B gets 1 − a. Cost of the flow: face links |δf|, inner plaquette changes routed from the plaquette p0 at f_i along Manhattan
  paths (a valid, possibly loose, earth-mover bound). Expected cost = recursion over one-variable functions h_node(S):

    h(S) = ∫ ρ_S(y) [ |a| (h_A(y) + e_A) + |1 − a| (h_B(S − y) + e_B) ] dy,

  root = (x_i, Rest) with cost ∫ ρ_Φ |1 − a| (1 + h_Rest(Φ − x)). Tree shape (to be tuned in float before the certified run; the
  shape is a design choice and any shape gives a valid bound): Rest as a caterpillar over the Manhattan shells around p0, far shells
  first (the flux then stays in a ball of area ~1/σ), each shell a caterpillar over its variables.
- **Validity lemma** (to be written out in NOTE.md): for a flow satisfying the continuity equation, |d/dΦ E_Φ F| ≤ L · E Σ|link
  velocities| for F Lipschitz (constant L per link, arc length); integrate along the short arc; lift to the full link space with an
  independent Haar interior gauge (PROOF-NOTE §5, relative gauge invariance).

### Rigour (computer-assisted)

All quantities on cells of a uniform grid of the circle (S-cells × y-cells), enclosed by interval arithmetic in numpy with outward
rounding (every +, −, ×, ÷ widened by one ulp with `nextafter`); transcendental inputs (I_n(β)/I_0(β), cos/sin of grid angles)
computed with mpmath at 40 digits and rounded outward; Fourier tails bounded analytically (I_n(β) ≤ (β/2)^n e^{β²/4}/n!, I_0 ≥ 1);
variation over a cell bounded by derivative bounds from the Fourier coefficients. The supremum over Φ_b covers the whole circle (cells),
not a scan. Status label in the note: **computer-assisted proof** (floating point with outward rounding; trusts IEEE-754 basic
operations and mpmath).

## Run plan

1. Float version of the tree flow (same code path without intervals): β = 2, ℓ ∈ {8, 10, 12, 14}, to choose the tree shape and see
   k(P), k(D), γ.
2. **Independent check of the recursion (must hold, else repaired before any certified run):** a Monte Carlo simulation of the same
   tree flow (exact sequential sampling down the tree, velocities composed along the path) at β = 2, ℓ = 6, i = 0 and i = 2,
   Φ_b ∈ {0, π}: the deterministic cost lies within 3 standard errors of the MC mean. Also: new upper ≥ the rigorous lower bound
   `u1_2d_lower.json` per link class (sanity), and the float value lies inside the interval enclosure.
3. Certified run: β = 2, the smallest ℓ ≥ 8 (in steps of 1) at which the float γ is below 0.97, then that ℓ and the next one.
   Positions i = 0..⌈ℓ/2⌉−1 (mirror symmetry), D once per ℓ.
4. If time and the runtime rule allow: β = 3 and β = 4 at the float level only (reported, not certified).

## Criteria

- **A1 (main): pass** if some ℓ ≤ 18 at β = 2 gets a certified γ < 1 (interval upper end), with every k(P_i), k(D) certified as a
  supremum over all Φ_b. Expected (heuristic, written now): k(P) ≈ 2.5–3.5 (the old Monte Carlo coupling gave 3.8–5.8; the lower
  bound is 1.40–1.58), k(D) ≈ 2.8 (lower bound 2.32), certified ℓ* ≈ 11–14.
- **A2 (reported):** the gap γ_hi/γ_lo at ℓ*, and ℓ*·√σ.
- **A3 (Lean):** the certified per-class numbers enter `Attempts/R2/TwoD*.lean` as hypotheses (computational inputs, files referenced);
  γ < 1 checked by `norm_num`; the GDS sum from per-class bounds and the decay statement for d = 2, G = U(1), β = 2 proved. Pass if it
  builds with no `sorry` and standard axioms only.

## Unit tests (RULES)

- Photon test: the certificate is a 2D statement and uses flux wrapping (g_m flat for large m). For 4D U(1) there is no reduction to
  independent plaquettes (Bianchi identities on cubes) and no wrapping; the note says why nothing transfers.
- Z₂ test: not applicable as a claim (no 4D statement is made); stated in the note.
