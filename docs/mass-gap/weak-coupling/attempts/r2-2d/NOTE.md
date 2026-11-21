# Round 2, attempt A: the reduction closes in 2D compact U(1) (2026-11-21)

Pre-registration: `PREREG.md` (written before any run). Rules: `../RULES.md`. Lean: `../../../formal/Attempts/R2/TwoD.lean`.
Files here: `tree_float.py` (float design tool), `mc_check.py` + `mc_check.json` (independent check of the recursion),
`tree_cert.py` (the certificate, interval arithmetic), `cert_2_<l>.json` + `.log` (certified numbers), `shell_check.py` (shell
classification check).

## Result in one paragraph

For 2D compact U(1) with Wilson action at **β = 2** (σ = 0.360 per plaquette, confinement length 1/√σ = 1.67), the W-form
one-box bound holds for thin squares of side **ℓ = 11** with **γ ≤ 0.90617 < 1**, certified by interval arithmetic as a
supremum over every boundary condition (status: **computer-assisted proof**). The certified per-class numbers enter the Lean
chain as one hypothesis (`CertifiedInfluence`); everything else is proved in Lean: GDS for the 2D square family from the class
numbers, `γ < 1` by `norm_num`, and exponential decay of slab correlations on every even torus N ≥ 14, uniformly in N, at
every rate below log(1/γ)/12 ≈ 0.00821 per lattice spacing (`twoD_U1_decay`, `twoD_U1_decay_limit`; builds, no `sorry`,
standard axioms only). So in the one exactly solvable confining gauge theory the one-box hypothesis is true at one coupling
and the chain closes there; the reduction is not vacuous. **The smallest certified box is ℓ = 10** (γ ≤ 0.99230; 6.0
confinement lengths; added after the registered runs, see "Deviations"); ℓ = 9 is out of reach of this coupling (float
γ = 1.09), while the rigorous lower bound already allows ℓ = 7.

## 1. The coupling (what is certified)

Exact structure (followups, Experiment 2a): modulo the interior gauge group the block law of the thin square V_ℓ is that of
N = ℓ² + 4ℓ i.i.d. von Mises(β) angles (ℓ² inner plaquettes, 4ℓ outer plaquettes y_j = f_j + η_j of the face links) conditioned
on their sum ≡ Φ_b (mod 2π); the shell enters only through Φ_b and translations of the face links (isometries). Shell links
per direction: 2ℓ parallel links P_i (one outer plaquette: shift η_i, so Φ_b moves and f_i = y_i − η_i moves), 2(ℓ−1) dangling
links D (two outer plaquettes, shifted oppositely: a boundary gauge rotation), 4 corner links (one outer plaquette at a face end:
exactly the perturbation P_0). `shell_check.py` enumerates the shell of `thinCube` on tori N ≥ ℓ + 3 and confirms this
list (84, 92, 100 links for ℓ = 10, 11, 12). GDS per direction (coverage ℓ(ℓ+1)):
γ(ℓ) = [2 Σ_i k(P_i) + 2(ℓ−1) k(D) + 4 k(P_0)] / (ℓ(ℓ+1)).

**D links.** Given u = y_l + y_r the conditional law of y_l is von Mises(2β|cos(u/2)|) and the perturbation shifts it rigidly;
move y_l, y_r and the inner link at the site together (3 links per unit; the inner plaquettes stay fixed). The optimal 1D flow
for a rigid shift of a von Mises(κ) density costs R(κ) = 2P_κ(|x| < π/2) − 1 per unit (closed form; R increases with κ by
Chebyshev's covariance inequality). So k(D) ≤ 3 sup_Φ ∫ ρ_Φ(u) R(2β|cos(u/2)|) du, ρ_Φ(u) = g_2(u) g_{N−2}(Φ−u)/g_N(Φ).

**P links: a tree flow.** Root: (x_i, Rest); Rest: a single caterpillar over its variables sorted by routing cost (distance of
the variable's plaquette from the plaquette p0 at f_i, plus 1 for a face link), far first. At each node with children A (one
variable) and B (the rest of the node), node sum S moving at unit rate: velocity of Y_A a(y) = (G_S(y) + c(S))/ρ_S(y), G_S(y) =
−∂_S ∫_0^y ρ_S, ρ_S(y) = p(y) g_B(S−y)/g_{A+B}(S); B gets 1 − a. Any constant c(S) gives a valid flow (c is chosen as the weighted
median minimising the node cost, in float; this cannot bias the bound). Link cost: face links |δf|; plaquette changes routed from
p0 along Manhattan paths (a valid earth-mover bound); f_i itself moves by a_root − 1. Expected cost by the recursion
h(S) = ∫ [c_A |G + c| + h_B(S−y) |ρ − G − c|] dy (root: c_A = 0, h_B = 1 + h_Rest). The shape was chosen on float runs
(`tree_float.py`, ℓ = 11, i = 0/2/5: shells-caterpillar 2.55/2.46/2.46, balanced shells 2.56/2.49/2.49, single caterpillar
2.46/2.40/2.40); the single caterpillar is the KR order of the followups' first coupling, now with the optimal c and evaluated
exactly instead of by Monte Carlo.

**Validity lemma (W bound from a flow).** Let μ_η be the block laws along the short arc η from σ_z to s (smooth positive
densities on the link torus), V_η a measurable link-velocity field with d/dη ∫F dμ_η = ∫ ∇F·V_η dμ_η for smooth F (weak continuity
equation). Then for F Lipschitz with constant L in each link for the arc length, |E_{σ}F − E_{σ'}F| ≤ L · sup_η E Σ_l |V_{η,l}| ·
arc(σ_z, s). Proof: mollify F with a product kernel (keeps the per-link constants, |∂_l F_ε| ≤ L), integrate the identity in η, let
ε → 0. The weak identity holds for the tree flow by induction over the nodes: at a node, with ψ(y) = E[F | Y_A = y, S],
d/dS ∫ρ_S ψ = ∫∂_Sρ_S ψ + ∫ρ_S ∂_S ψ = ∫ρ_S a ∂_yψ + ..., using ∂_y(ρ a) = −∂_S ρ; c(S) may be any measurable function (no
continuity in S is used). Lift to the full link space: the routing is a fixed linear map from variable velocities to link
velocities; the block law is (quotient law) ⊗ (Haar on the interior gauge orbit) and the lifted field projects onto the
quotient field, so the continuity equation lifts (PROOF-NOTE §3.2–3.5, relative gauge group and alignment). Hence k^W(z) ≤ sup_Φ h_root(Φ).

**Independent check of the recursion (PREREG step 2): pass.** Monte Carlo of the same flow (exact sequential sampling down the
caterpillar, rates composed, S = 20000) at β = 2, ℓ = 6: i = 0: deterministic 2.4598, MC 2.4549 ± 0.0154 (Φ = 0) and
2.4611 ± 0.0145 (Φ = π); i = 2: 2.3976 against 2.4130 ± 0.0155 and 2.4084 ± 0.0149; all within 3 s.e. (`mc_check.json`).

## 2. The certificate (`tree_cert.py`)

- Interval arithmetic in numpy: every +, −, ×, ÷ in round-to-nearest, then widened outward by one ulp (`nextafter`); sums of many
  terms with the a-priori error bound n·2^-52·Σ|x|. Inputs from mpmath (40 digits), rounded outward: r_n^m = (I_n(β)/I_0(β))^m,
  cos and sin of the half-grid angles jπ/G, the cell width 2π/G, and R(κ) (alternating series, an upper partial sum). Fourier
  tails beyond n = 40 bounded by I_n(β) ≤ (β/2)^n e^{β²/4}/n!.
- Grid of G = 1024 cells on the circle. At each node and each S-cell K: (i) the cost at the cell centre s_K, integrated t-cell
  by t-cell in t = S − y (so the child's bound h_B ≤ HB[q] on t-cell q applies exactly): ∫|a + b(t−t_c) + R| ≤ w|a| +
  [|b|w²/4 if a may vanish] + w³/24 sup|F_tt|, with centre values as point enclosures and G at the centres by the midpoint rule
  with its error bound; (ii) a bound L_K of |h'(S)| on the cell (in y- or t-coordinates, the smaller), so h ≤ h(s_K) + (w/2)L_K
  on the cell. Second derivatives over boxes are bounded by the Leibniz rule from box enclosures of p^(k), g_B^(k) and
  (1/g_m)^(k). The root value is the maximum over all Φ-cells: **a supremum over every boundary flux, not a scan.**
- Convergence in G (ℓ = 4, i = 0): 2.5704 (G = 256), 2.5074 (512), 2.4822 (1024); float value of the same flow 2.4596. The
  remaining overestimate comes from taking the supremum over each cell at every level of the tree (first order in w); G = 1024
  leaves about +0.02 on k(P).

| ℓ = 11, β = 2 | certified upper bound | float value of the flow | rigorous lower bound (followups) |
|---|---|---|---|
| k(P_0) (also the 4 corner links) | 2.482483 | 2.482467 | 1.404 |
| k(P_1) | 2.421461 | 2.421446 | 1.55 |
| k(P_2) | 2.419398 | 2.419382 | 1.57 |
| k(P_3), k(P_4), k(P_5) | 2.419364 | 2.419348 | 1.577 |
| k(D) | 2.809849 | 2.804476 | 2.316 |

**γ(11) ≤ 0.90617** (exact rational arithmetic on the float bounds). Lower bound γ_lo(11) = 0.650; ratio γ_hi/γ_lo = 1.39.
Runtime: about 280 s per position i (165 nodes), 3 s for D.

Other box sizes at β = 2 (same G = 1024, all positions, `cert_2_10.json`, `cert_2_12.json`; certified k(D) ≤ 2.809849 at
every ℓ):

| ℓ | ℓ√σ | k(P_0) | k(P_1) | k(P_i), i ≥ 2 | **certified γ ≤** | float γ of the flow | lower bound γ_lo |
|---|---|---|---|---|---|---|---|
| 9 | 5.4 | – | – | – | – (not attempted) | 1.090 | 0.79 |
| 10 | 6.0 | 2.482370 | 2.421353 | ≤ 2.419289 | **0.99230** | 0.9865 | 0.709 |
| 11 | 6.6 | 2.482483 | 2.421461 | ≤ 2.419398 | **0.90617** | 0.9009 | 0.650 |
| 12 | 7.2 | 2.482605 | 2.421578 | ≤ 2.419515 | **0.83382** | – | 0.600 |

So the smallest box certified by this coupling is ℓ = 10 (ℓ = 9 is above 1 already in float). The certificate costs about
0.006 on γ at G = 1024 (float of the flow 0.9865 → certified 0.9923 at ℓ = 10).

**Other couplings (PREREG step 4, float only, not certified;** `float_beta.py`, `float_beta.json`; positions i ≥ 4 set to the
value at i = 3, which at β = 2 agrees to 10⁻⁵):

| β | σ | k(P_0), k(P_mid) | k(D) | first ℓ with float γ < 1 | its ℓ√σ |
|---|---|---|---|---|---|
| 2 | 0.360 | 2.48, 2.42 | 2.80 | 10 (γ = 0.987) | 6.0 |
| 3 | 0.211 | 4.14, 3.91 | 2.97 | 14 (γ = 0.972) | 6.4 |
| 4 | 0.147 | 5.86, 5.39 | 3.00 | 17 (γ = 0.997) | 6.5 |

The switch-on box of this coupling sits at ℓ√σ ≈ 6.0–6.5 confinement lengths at all three couplings (the rigorous lower bound
puts the true switch-on at ≥ 4.2√σ⁻¹ at β = 2 and 4); k(P) grows faster than 1/√σ here ((k−1)√σ = 0.85, 1.34, 1.68), so the
coupling is looser at weaker coupling, as the followups' Monte Carlo couplings were.

## 3. Lean (`formal/Attempts/R2/TwoD.lean`, built in `~/formal-att-a`; no `sorry`; axioms propext, Classical.choice, Quot.sound)

- `arc a b = |arg(a·b̄)|` on `Un 1`: `0 ≤ arc ≤ π`, inversion invariant, positive at (1, −1) (the cost hypotheses of the W chain).
- `kappa ℓ kP kD x z`: the class value of the shell link z of the square at x, written as a sum over relative offsets
  (P: (i, −1), (i, ℓ+1); D: (−1, s), (ℓ, s); corners: (−1,0), (−1,ℓ), (ℓ,0), (ℓ,ℓ)), so `sum_kappa`: Σ_x κ_x(z) =
  2Σ kP + 2(ℓ−1)kD + 4kP_0 with no geometry; `coverage_ge`: ℓ(ℓ+1) ≤ coverage (d = 2, ℓ + 1 ≤ N);
  **`gds_kappaT`: GDS(γ) for the 2D thin squares from the class numbers** (proved).
- `influence_of_shell`: bounds for shell links suffice (off the shell the zero coefficient is proved).
- `CertifiedInfluence N` (**the computational input, a hypothesis**): every shell link of every side-11 square has W influence
  ≤ its class value, numbers `kq` = the certified bounds rounded up to 4 decimals, `kDcert`. `gammaCert_lt_one` by `norm_num`.
- **`twoD_U1_decay`**: under `CertifiedInfluence N`, for every even N ≥ 14, slab observables Lipschitz in each link for `arc`:
  |Cov(F∘S_m, F∘Θ)| ≤ (Cov(0) + 2^{-r} C) e^{−λm} for every 0 ≤ λ < log(1/γ)/12, C = `cubeConstW 2 11 γ λ V L π` independent of N.
  **`twoD_U1_decay_limit`**: any limit h of the torus correlations along even N_j → ∞ has |h(t)| ≤ h(0) e^{−λt}.
  **`twoD_U1_decay_10`**: the same from the smallest certified box ℓ = 10 (`gammaCert10_lt_one`, N ≥ 13, rate < log(1/γ)/11
  ≈ 7·10⁻⁴).
- Not formalised: the certificate itself (numerics), the validity lemma of §1 (measure theory of flows), the reduction to
  conditioned von Mises angles, and the shell classification (checked by `shell_check.py`). An error there would make the
  hypothesis false, not the theorems.

## 4. How sharp is the chain (step 3)

- Certified rate: log(1/γ)/(ℓ+1) = 0.00821 per lattice spacing at ℓ = 11. Best possible from this coupling family: with γ(ℓ) ≈
  10.2/ℓ (k values saturate in ℓ), log(1/γ)/(ℓ+1) is maximal near ℓ ≈ 10e ≈ 28, about 0.035 (ℓ ≈ 28, assuming the k values stay at their ℓ = 11 size, as the float runs and the lower bounds show).
- Exact physics: σ = −ln(I₁(2)/I₀(2)) = 0.360 per plaquette, √σ = 0.600 (the only scale; Wilson loops have the exact area law
  (I₁/I₀)^{area}). In infinite volume the plaquettes are independent, so connected correlations of gauge-invariant local
  observables vanish beyond touching distance: the exact mass gap is infinite. On the torus (spatial size N) the transfer matrix
  gap is the lightest flux state, N·σ (electric flux around the spatial circle), again → ∞.
- So the chain is **not sharp**: against the natural scale √σ the certified rate is about 1/73 of it (best ℓ: about
  1/17); against the exact gap it is arbitrarily loose. That is expected: GDS is a Dobrushin-type contraction bound and sees only
  that a box of about 6.6 confinement lengths (ℓ√σ = 11 × 0.600) forgets its boundary by a factor γ; it cannot see the exact
  independence. What the 2D example calibrates is the **scale** at which the one-box bound switches on: certified at ℓ√σ = 6.6
  (and at ℓ√σ = 6.0 with γ ≤ 0.9923), lower bound ℓ*_lo√σ = 4.2 (followups); in between, the truth.

## 5. Photon test and Z₂ (RULES)

Nothing here transfers to 4D U(1). The certificate rests on two 2D facts: (1) the box law reduces exactly to independent
plaquettes conditioned on one boundary flux; in d ≥ 3 the plaquettes of a box are constrained by the Bianchi identity on every
cube, there is no independent-plaquette reduction and no single flux variable; (2) flux wrapping: the sum of m ≳ 1/σ plaquette
angles is nearly uniform on the circle (g_m flat up to (I₁/I₀)^m), so the boundary flux is absorbed within an area ~1/σ around
the perturbed link and k(P) saturates (≈ 2.4 here). In the 4D Coulomb phase (weak coupling) there is no σ, no wrapping, and the
boundary influence behaves like the free field, whose W coefficient is ≥ 1 at every box size (round 1, route (c), sum rule):
γ ≥ 1, so the claim fails for the photon, as the photon test demands. The certified statement is specific to a 2D model and makes
no 4D claim, so the Z₂ test has nothing to apply to (2D Z₂ gauge theory confines at every β by the same mechanism; 4D Z₂ at weak
coupling is not touched).

## 6. Status, honestly

- **Computer-assisted proof:** k(P_i), k(D) upper bounds and γ(11) < 1 at β = 2 (floating point with outward rounding; trusts
  IEEE-754 basic operations, numpy's summation within the stated a-priori bound, and mpmath).
- **Proved on paper (here, not in Lean):** the validity lemma and the lift (sketched in §1; standard), the exact reduction
  (followups 2a).
- **Proved in Lean:** GDS from the class numbers, γ < 1, the decay theorems, given `CertifiedInfluence`.
- **Numerical only:** the float γ at β = 3, 4 (switch-on of this coupling at ℓ√σ ≈ 6.4–6.5).
- **Not shown:** UniformGDS_W (uniform in the lattice spacing): we certify one coupling. The continuum limit of 2D U(1) needs
  β_k → ∞ with boxes ℓ_k ≈ L₀√(2β_k); the lower bound says ℓ*√σ ≈ 2.8–4.2 over β = 2–64 and this coupling switches on at about
  6–6.5 confinement lengths for β = 2–4, but its k(P) grows faster than 1/√σ, so at large β it needs larger boxes in
  confinement units (or a better coupling) and the certificate a finer grid.

## 7. The owner's pointer: α (no reply requested; noted)

In 2D, e² has mass dimension 2 and β = 1/(e²a²); with α := e²/4π (lattice units a = 1), β = 1/(4πα): β = 2 is α = 1/(8π) ≈ 0.040
(about 5.4 times 1/137; α = 1/137 is β ≈ 10.9). At weak coupling σ → e²/2 = 2πα (exactly σ = −ln(I₁/I₀)(1/(4πα))), so the only
dimensionless content of the switch-on scale is ℓ*√σ, a function of α through β alone: certified ℓ*√σ = 6.6 at α = 0.040;
lower-bound switch-on ℓ*_lo√σ = 4.20, 4.21, 3.62, 3.23, 3.02, 2.84 at α = 0.040, 0.020, 0.0099, 0.0050, 0.0025, 0.0012
(β = 2..64), slowly falling as α → 0 towards a constant of about 2.5–3 confinement lengths (in α: ℓ* ≈ c/√(2πα) lattice units
with c ≈ 3, i.e. the box must hold an area of about c² ≈ 9/σ). Nothing singles out α = 1/137 in 2D; the 2D
example says only that the existence boundary (the box where the one-box bound switches on) sits at a fixed small multiple of the
confinement length 1/√σ, and that in 2D U(1) the coupling that sets σ is α itself (σ = 2πα at weak coupling), the electric flux
being the only thing that can wrap.

## 8. Deviations from the pre-registration

1. **ℓ = 10 certified in addition.** The registered rule was "the smallest ℓ with float γ < 0.97, then that ℓ and the next"
   (ℓ = 11 and 12, both done). After the ℓ = 11 run showed the certificate costs only about 0.006 on γ, I also certified ℓ = 10
   (float 0.9865, not below the registered 0.97 threshold). Reported as an extra; it is the smallest certified box.
2. **The certificate's quadrature was redesigned before any certified number was produced** (development on ℓ = 4 and ℓ = 6,
   comparing with the float values): a first version with first-order cell enclosures overestimated by a factor 10 (the
   integrand's variation inside a cell compounded along the caterpillar); the final version integrates in t = S − y with the
   expansion of §2. This changes only how tight the enclosure is, not what is enclosed.
3. The tree shape was chosen on float runs, as registered (single caterpillar instead of the registered shell caterpillar, which
   was the stated default).
4. Step 4 (β = 3, 4) used an approximation (positions i ≥ 4 copied from i = 3) to stay well inside the runtime rule; stated
   above; these numbers are float only.

## 9. Single most promising next step

Certify a second coupling (β = 3 at ℓ = 15, float γ = 0.908, about 6.9 confinement lengths) to see the switch-on scale ℓ*√σ certified at two values of
α; then the same tree-flow certificate for 2D SU(2) (its plaquettes are also independent given the boundary holonomy, conditioned
on a group-valued product instead of a sum), where the centre and the adjoint part both appear and the 2D toy can test the
H1/H2 bookkeeping beyond the abelian case.
