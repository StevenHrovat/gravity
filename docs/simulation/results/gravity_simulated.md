# Gravity as a recorded frame against a quantised field, simulated

Workstream of *GUID v6: Our theory as simulated*. Written from one run of `docs/simulation/gravity_simulated.py`; every number below is also in `gravity_simulated.json`. Checks: **110 of 110 passed**. The run took 175 s on one core of a shared machine, with a peak resident memory of 1.1 GB. It is deterministic: seeds are fixed and BLAS is pinned to one thread. Only the wall-clock timings change from run to run.

```
python3 docs/simulation/gravity_simulated.py      # numpy 2.5.3, scipy 1.18.1, Python 3.13; exit 0 only if all checks pass
```

The theory under test (paper, Sections 4 to 6): gravity is a classical frame. It depends on matter only through records, and it acts back as a classical field, which makes it a measure-and-prepare channel and LOCC (Lemma "classical mediation is LOCC"). With Bridge B and the balance rule (trade-off at equality), each mass decoheres at lambda = G m^2/(hbar R). The alternative is a coherent, quantised Newtonian field, which gives every branch configuration the phase Σ G m^2 t/(hbar d_ij).

**Physical instance** (Bose et al. 2017; diamond, rho = 3510 kg/m^3). m = 1e-14 kg, Deltax = 250 um, d = 450 um, R = 0.879 um. That gives omega0 = G m^2/(hbar d) = 0.1406 rad/s, a BMV entangling rate of 0.1256 rad/s and lambda = G m^2/(hbarR) = 71.97 /s (coherence time 13.9 ms). The exact sphere rate is E_G/hbar = (G m^2/hbar)(6/5R - 1/Deltax) = 86.1 /s. All of these agree with `checks.py` Q5 and Q19.

## Verdict

- **G2, the main result.** Under the balance rule, the ratio of the entangling phase rate to the DP rate is rho = R[1/(d-Deltax) + 1/(d+Deltax) - 2/d]. It does not depend on the mass, and it is 1.74e-3 for the Bose geometry.
  - Its supremum over collinear BMV geometries with no overlap (d - Deltax >= 2R) is **1/2**. It is approached only as Deltax -> inf with the spheres' inner branches touching, and never attained.
  - Over any arrangement of two spheres it is **1** (parallel splits).
  - With Bose et al.'s Casimir gap (d - Deltax >= 200 um) it is 4.4e-3.
  - A coherent field plus independent dephasing at lambda per mass entangles the masses at some time **iff omega/lambda > 2**. This is exact: the threshold equals the Kafri-Taylor-Milburn minimum decoherence omega/2 of a classical channel.
  - **Implication:** if Diosi-Penrose decoherence at the Bridge-B rate is real, no BMV geometry of two solid spheres builds up any entanglement, even if gravity is quantum. The best case falls short of the threshold by a factor 2 (factor 4 for the collinear geometry).
  - With the exact DP rates this holds for any two bodies of any shape, because the Newton kernel is positive: omega <= 2sqrt(Gamma_A Gamma_B).
  - So a null BMV result does not separate GUID-with-Bridge-B from quantum gravity plus DP collapse. A positive result would refute both, and every classical mediator.
- **G1.** At scale the two pictures differ qualitatively.
  - The coherent field (statevector to N = 24) drives the half-chain entropy to the Page value and the X-basis output to Porter-Thomas (Z -> 2.002, third moment -> 6.02 at N = 24). Both take hours of physical time (tau ≳ 10^3-10^4).
  - Pairwise entanglement in the chain dies of monogamy after about 20 s (tau ~ 2.7). The coherent field's entanglement becomes multipartite.
  - The recorded frame runs 4000 masses at O(N^2) per step: 7.5 s for 16 trajectories x 200 steps, or 2.3 ms per trajectory-step. Every trajectory is a product state, the coherence decays as e^{-lambdat} (fitted rate 0.997 lambda), and the mean force equals the Newtonian sum. The X-basis output is a product distribution with Z = Π(1 + <sigmax>^2) -> 1.
  - The brute-force statevector would need at least 10^1198 s and 10^1205 bytes at N = 4000.
- **G3.** In the task's normalisation the classical-quantum toy is positive iff **D1^2 <= 4 D0 D2**. That is Oppenheim et al. Eq. (23) after mapping their moments, D1^OSSWD = D1/2 and D2^OSSWD = D2/2.
  - At 1% beyond the bound the blocks turn negative at exactly the predicted time t* = 1.00.
  - At equality the dynamics is the measurement-and-feedback unravelling. The classical variable is then a perfect record and every block rho(p) is pure; doubling D2 makes them mixed (4det/tr^2 = 1 - e⁻^2 at p = 0).
- **G4.** The quantum coupling -K x1 x2 entangles two oscillators (log-negativity 0.145 from vacuum, 2.96 from squeezed states). The KTM classical channel never does, at any measurement strength. Its mean dynamics and averaged covariance match the master equation. Its heating k + K^2/(4k) is minimal, hbarK, at k = K/2, as in KTM Eqs. (15) and (19).
  - Dephasing at 0.99 K added to the quantum coupling entangles the ground state, so the minimum is exactly the separability edge.
  - For the BMV qubits the classical-channel minimum is omega/2 = 0.063 /s. Bridge B is 1146 times that.

---

## G1. Many gravitating quantum masses

**Model.** N masses on a line with spacing d. Each is a two-level system, x_i = i d + (s_i - 1/2)Deltax with s_i ∈ {0, 1}, and Deltax/d = 5/9. Lengths are in d, time in 1/omega0 (tau = omega0 t). The branch energy Σ_{i<j} 1/|x_i - x_j| is written exactly as an Ising form, Ω(s) = const + Σ h_i s_i + Σ_{i<j} J_ij s_i s_j, with J_ij = -g(|i-j|) and g(n) = 2δ^2/(n(n^2-δ^2)). The nearest-neighbour coupling g(1) = 0.893 is the BMV entangling rate; it is checked against a direct sum over all 256 branches at N = 8 (agreement 1e-14).

### (a) Coherent field: |Ψ(t)> = 2^(-N/2) Σ_s e^{itauΩ(s)} |s>

The state is built exactly, by doubling, for N = 8 to 24. Measuring in the X basis after diagonal phases is an IQP circuit (Bremner, Jozsa and Shepherd 2011).

- **Half-chain entropy, N = 20, in bits.** At tau = pi/g(1) = 3.52 (t = 25 s, where an isolated pair is maximally entangled) it is exactly one ebit, the bond across the cut (1.009; 1.009 at N = 24). It then grows as more couplings wind past 2pi:

  | tau | 46 | 268 | 1550 | 8960 | 10^4 to 10⁷ |
  |---|---|---|---|---|---|
  | S (bits) | 2.1 | 3.9 | 6.6 | 9.35 | 9.28 mean, 9.0 to 9.4 (Page 9.279) |

  At N = 24 and tau = 10⁵ it is 11.27 bits; Page's value is 11.279. Couplings fall as 1/n^3, so at BMV-relevant times (t ≲ 100 s, tau ≲ 14) the state is close to area law.
- **Pairwise negativity.** All 120 pairs were computed at N = 16 from the statevector. They agree to 2e-14 with an exact two-body formula: the sum over the other masses factorises,

  rho_ij[(a,b),(a',b')] = ¼ e^{itau[e(a,b) - e(a',b')]} Π_{k≠i,j} (1 + e^{itau[J_ik(a-a') + J_jk(b-b')]})/2.

  The formula needs no statevector, so it runs at N = 4000 (all 3999 neighbour pairs in 0.7 s).
  - Bulk neighbours reach negativity **0.153** at tau = 1.27 (t = 9 s). Every pair of the 4000-chain is entangled there (minimum 0.1528; the end pair has 0.212).
  - In the bulk the pair is first separable at tau = 2.67 (19 s). It is separable at tau = pi/g(1), where an isolated pair would have 1/2.
  - No scanned pair is entangled beyond tau ~ 19.5 (scan to tau = 300), while an isolated pair keeps oscillating to 1/2.
  - At N = 16 the pairs entangled are 15 of 120 at tau = 1.3, 0 at tau_pi, 2 (the ends) at tau = 10, and 0 at tau = 10^3.
  - The coherent field's entanglement is multipartite. Pairwise negativity is the wrong witness at scale; the half-chain entropy is the right one.
- **Collision probability** Z = 2^N Σ_x p(x)^2, with Porter-Thomas giving Z = 2 and M3 = 2^{2N} Σ p^3 = 6.
  - At t = 0, Z = 2^N.
  - At tau_pi, Z = 1.39 to 1.41 for every N, flatter than Porter-Thomas (a near-cluster state).
  - At tau = 10, Z grows with N (1.74, 2.10, 2.78, 3.78, 5.16 for N = 8, 12, 16, 20, 24), so the output is not anticoncentrated.
  - From tau ~ 10^3 (2 h) it settles at 2. Averaged over 12 times in tau = 10^4 to 10⁷:

    | N | 12 | 16 | 20 | 24 |
    |---|---|---|---|---|
    | \|Z - 2\| | 0.113 | 0.069 | 0.012 | 0.002 |
    | \|M3 - 6\| | 1.35 | 0.79 | 0.11 | 0.02 |

    Porter-Thomas statistics emerge with N; at N <= 16 the structured (Toeplitz) circuit still deviates.
  - Reference: for IQP circuits with independent uniform angles, E[Z] = 2 - 2^(-N) exactly. (Proof: the phase average forces {s1, s3} = {s2, s4} bit by bit, and a quadratic term forbids mixing the two pairings, which leaves 2*4^N - 2^N quadruples.) The 60-instance means are 2.036 +- 0.018 at N = 10 and 1.9953 +- 0.0033 at N = 14.

### (b) Recorded frame (GUID): measurement and feedback

- **Model.**
  - Each mass's position is continuously measured, with Lindblad term kappa(Z rho Z - rho) and Z = 1 - 2s. The record is dY_j = 2sqrtkappa<Z_j>dt + dW_j.
  - The frame turns each record into a position estimate, ŝ_i dt = 1/2(dt - dY_i/(2sqrtkappa)).
  - Each mass feels the classical Newtonian field of the others' estimates: its branch-1 phase advances at h_j + Σ_i J_ij ŝ_i.
  - 2kappa = lambda = d/R = 511.7 omega0 (Bridge B, R = 0.879 um). This is the balance rule at equality: the record noise is the only diffusion (see G3).
  - Records are sampled exactly, branch first: s_i is drawn with Born probability 1/2, then Y_i = 2sqrtkappa z_i t + W_i, and the conditional state is a function of Y_i. A plain Euler integration of the joint 2^4 stochastic Schroedinger equation reproduces it, so the method rests on no ansatz.
  - The cost is three NxN matrix products per step.
- **N = 4000, 16 trajectories, 200 steps to t = 4/lambda (55.6 ms).** The time loop takes 7.5 s and building the matrices 1.7 s; the run holds 384 MB of matrices.
  - **Entanglement.** Each trajectory is a product state by construction. A joint Euler integration confirms it independently (largest second Schmidt coefficient 2e-15).
  - **Coherence.** The mean |rho01| over 64 000 mass-trajectories equals 1/2e^{-lambdat} within 5 standard errors at t = 1, 2 and 3/lambda, and the fitted rate is 0.997 lambda. The complex mean matches the closed form E[rho01] = 1/2e^{-lambdat} e^{-ih_j t} Π_i (1 + e^{-iJ_ij t})/2 * e^{-Σ_i J_ij^2 t/(32kappa)} to within 5 standard errors. Record noise adds Σ J^2/(32kappa) = 3.8e-7 lambda.
  - **Mean force.**
    - At the mean records the frame force equals a direct Newtonian double sum over branches, to 1e-13 of the pair-force scale. Newton's third law holds to 2e-14.
    - With noise, the mean impulse over trajectories equals T x the Newtonian sum for all 4000 masses: mean t^2 = 1.09 (Student t with 15 degrees of freedom gives 1.15). The end mass gives 1.13 +- 0.17 x Newton.
    - Momentum is conserved only on average. Per trajectory the record noise kicks the total momentum (standard deviation 0.40 against T Σ|F| = 0.15); this is the frame's diffusion.
  - **X basis.** Per trajectory p(x) = Π_j p_j(x_j), so Z = Π_j 2(p_j0^2 + p_j1^2) = **Π_j (1 + <sigmax>_j^2)**; this is checked against enumeration at N = 10. Mean log₂Z falls from 4000 at t = 0 to 1047, 315, 103 and 35 at t = 1, 2, 3 and 4/lambda, towards 0, the uniform distribution. Porter-Thomas statistics (log₂Z = 1 with an exponential profile) never appear.
- **Small N: the averaged state.** Every operator is diagonal, so the Wiseman-Milburn feedback master equation has a closed form:

  rho_ss'(t) = rho_ss'(0) exp(t[i(Ω(s) - Ω(s')) - Σ_k kappa(1 - z_k z'_k) - 1/2 Σ_i (F_i(s) - F_i(s'))^2]), with F_i(s) = Σ_j J_ij s_j/(4sqrtkappa).

  It reproduces the quantum commutator -i[H_Q, rho] exactly and adds dephasing at 2kappa + Σ_i J_ij^2/(32kappa), which is at least omega/2.
  - For N = 4 and 6, 13 measurement strengths (10⁻^3 to 10^3 times the optimum) and 25 times up to 50/omega0, the largest PT negativity over all bipartitions (7 and 31 cuts) and all pairs is 0.
  - For the same masses the coherent field's most negative partial-transpose eigenvalue reaches -0.5.
  - 40 000 exact trajectories average to the master-equation state (largest |z| = 2.5 over 256 elements). A joint Euler SSE with 8000 trajectories agrees to 0.005.
- **Cost.**

  | | statevector (coherent field) | recorded frame |
  |---|---|---|
  | N = 24 | 5.4 s (state + Z), 26 s for the half-chain entropy, 256 MB | - |
  | N = 4000 | >= 10^1198 s (x2 per mass from N = 24); the fitted 2^(1.21 N) gives 10^1454 s; 10^1205 bytes | 7.5 s for 16 x 200 trajectory-steps, 384 MB |

  The fitted exponent 1.21 includes the N*2^N transform and memory effects.

**Caveats.**
- (i) The 2^N figure is the brute-force cost. At BMV-relevant times the coherent chain is low-entangled (about 1 bit), so tensor networks would simulate it cheaply. It is hard only at late times, and the hardness argument for IQP sampling (BJS 2011; Bremner, Montanaro and Shepherd 2016) is a complexity-theoretic conjecture for typical circuits, not a statement about this structured one.
- (ii) In (b) each mass's own position record is measured independently. The inter-mass cross term of the DP kernel, of order omega/lambda = 1.7e-3, is not modelled.
- (iii) Branches are along the line; the ring and other orientations were not run.

## G2. BMV under the hypotheses

**Geometry.** Two masses with centres d apart, each split by Deltax along the line joining them. The coherent field gives the phases G m^2 t/(hbar d_ab), and the entangling rate is omega = (G m^2/hbar)|1/(d-Deltax) + 1/(d+Deltax) - 2/d| = 0.1256 rad/s.

**Hypotheses.**

| Label | Model |
|---|---|
| (Q) | Coherent field, no collapse. Pure state, negativity 1/2\|sin(omegat/2)\|. |
| (Q+DP) | Coherent field plus Diosi-Penrose dephasing. "Local" uses lambda = Gm^2/(hbarR) (the paper's Bridge-B rate) per mass. "Exact local" uses the uniform-sphere rate E_G/hbar. "Full" uses the joint DP master equation -(G/2hbar)∫∫[f(x),[f(y),rho]]/\|x-y\| on the total mass density, which adds an inter-mass cross term locked to omega: the (00,11) coherence decays at 2Gamma - omega and (01,10) at 2Gamma + omega. |
| (G) | GUID: recorded frame (measurement and feedback, as in G1b) with 2kappa = lambda. Also run at the KTM optimum kappa = omega/8. |

**rho.** Under the balance rule lambda = G m^2/(hbarR), so

rho = omega/lambda = R[1/(d-Deltax) + 1/(d+Deltax) - 2/d] = 2RDeltax^2/(d(d-Deltax)(d+Deltax)).

G, hbar and m cancel, so rho is fixed by geometry alone; numerically it is independent of m from 1e-18 to 1 kg to 4e-16. For the Bose geometry rho = **1.745e-3** (1.458e-3 with the exact sphere rate). This is also the entangling phase built up per coherence time.

**Supremum.** With u = d - Deltax >= 2R (no overlap) and 0 < Deltax < inf:
- rho = 2RDeltax^2/(u(u+Deltax)(u+2Deltax)). It increases with Deltax (the derivative's numerator is Deltax(2u^2 + 3uDeltax) > 0) towards R/u, and it decreases with u. So sup rho = **1/2**, approached as Deltax -> inf with the inner branches touching and never attained.
- With a Casimir gap u >= 200 um (Bose et al.: Casimir-Polder at a tenth of gravity), rho <= R/u = 4.4e-3.
- **Any arrangement of two spheres:** omega <= (G m^2/hbar)(1/r00 + 1/r11) <= G m^2/(hbarR), so rho <= 1. The bound is reached as Deltax -> inf by parallel splits side by side at 2R. 188 398 random non-overlapping geometries all lie below it (largest 0.446).
- **With the exact sphere DP rate** the supremum is 1/2 again for collinear splits, now as Deltax -> 0 at d = 2R + Deltax; 5/12 at Deltax -> inf. Over all geometries it is 5/6 (parallel, Deltax -> inf).

**The DP self-energy of displaced spheres** was checked by radial quadrature of G∫∫rho₁rho₂/|x-y| against the closed form (Howl, Penrose and Fuentes 2019, Eq. 23):

E_G(b) = (G M^2/R)(2lambda^2 - 3/2 lambda^3 + 1/5 lambda⁵) for lambda = b/2R <= 1, and G M^2(6/5R - 1/b) for b >= 2R.

The self-term is 6/5 (to 1e-12) and the maximum difference 2e-16. Beyond one diameter the mutual term is exactly G M^2/b (shell theorem). The inter-mass phases between non-overlapping spheres are therefore exactly point-like, and the paper's lambda = G m^2/(hbarR) differs from E_G/hbar only by the factor 6/5 - R/Deltax, between 0.7 and 1.2 (1.197 for the Bose split).

**The threshold (exact).** Take dephasing at lambda per mass, under which a coherence decays as e^{-lambdat}, together with an entangling Ising rate omega. Starting from |++> the smallest PT eigenvalue is (t/4)(2lambda - omega) + O(t^2), checked to 1e-4. So the masses are entangled immediately when omega > 2lambda. Conversely, for lambda >= omega/2 the generator equals the averaged KTM feedback generator at kappa = omega/8 (whose decoherence is omega/2) plus extra local dephasing lambda - omega/2 >= 0. Both generate LOCC semigroups, so by the Trotter product formula no separable input ever becomes entangled, at any time, even with a time-dependent geometry. Bisection over 40 s of evolution gives **omega/lambda = 2.0000**. With the full DP kernel the correlated term lowers it to **sqrt2** (1.41421 by bisection; at first order the PT eigenvalues are 2lambda +- sqrt2 omega). For spheres the supremum is 5/6 < sqrt2, so the full kernel changes nothing either.

**A general bound.** For any two bodies, the entangling rate is omega = |I(Deltaf_A, Deltaf_B)|/hbar and the DP rates are Gamma_A = I(Deltaf_A, Deltaf_A)/(2hbar). Here Deltaf is the change of mass density between branches and I(f, g) = G∫∫f g/|x-y|, whose kernel is positive (Fourier 4pi/k^2). Cauchy-Schwarz then gives omega <= 2sqrt(Gamma_A Gamma_B), with equality impossible for disjoint bodies. **DP-rate decoherence therefore always meets the classical-channel minimum omega/2.** Over the random geometries the largest omega/(2sqrt(Gamma_A Gamma_B)) is 0.22.

**Time series, Bose instance, 0 to 40 s.**

| | max negativity | max stabiliser witness <XZ> + <ZX> (separable bound 1) | min optimal PPT witness |
|---|---|---|---|
| Q | 0.5 at t = 25.0 s | 2.0 | -0.5 |
| Q+DP local (lambda = 72 /s) | 0 (1e-16) | 8e-7 | >= 0 |
| Q+DP exact local (86 /s) | 0 | 6e-7 | >= 0 |
| Q+DP full kernel | 0 | 6e-7 | >= 0 |
| G (Bridge B) | 0 | 8e-7 | >= 0 |
| G at the KTM minimum (0.063 /s) | 0 | 0.53 | >= 0 |
| control: Q + dephasing 0.99 omega/2 | 3.0e-4 at 1.55 s | 0.54 | -3e-4 |

Witnesses are evaluated in the local frame of the (Q) prediction. The optimal witness is |e><e|^{T_B} with e the negative eigenvector of the (Q) state's partial transpose.

**Implication for the paper.**
- Section 5.4's sentence "a Bose-Marletto-Vedral experiment sees decoherence and no entanglement" is right as GUID's prediction, but it is not a discriminator. If decoherence at the Bridge-B (DP) rate is real, quantum gravity predicts no entanglement in every two-sphere BMV geometry as well: at most 1 rad of entangling phase per coherence time, against the 2 needed.
- What discriminates is the decoherence itself. A measured mesoscopic decoherence at the DP rate supports Bridge B. A positive BMV result needs decoherence below omega/2, the minimum any classical channel needs; it would refute GUID (Lemma "classical mediation is LOCC") and DP-rate decoherence together.
- The Bose et al. witness as printed in the accepted manuscript, W = |<sigmax(x)sigmaz> - <sigmay(x)sigmaz>| > 1, is exceeded by product states: its maximum over product states is sqrt2, found numerically. Do not quote it with bound 1 without checking the published version. The variant |<sigmax(x)sigmaz> + <sigmay(x)sigmay>| has product maximum 1.

**Caveats.**
- DP conventions differ by factors of order one. The conclusion survives a factor 2 slower DP for spheres with the exact rate (sup 5/3 < 2), but it becomes marginal for the paper's lambda halved (sup -> 2, approached and never attained).
- With the full kernel and a rate half the size, extreme parallel geometries would reach 5/3 > sqrt2.
- Only uniform rigid spheres with two branches were scanned, and nuclear granularity is neglected (`checks.py` Q19 shows the bulk term dominates).

## G3. Classical-quantum dynamics and the balance rule

**Model (task normalisation).**

∂rho(p)/∂t = D0(sigmaz rho sigmaz - rho) - (D1/2)∂_p{sigmaz, rho} + (D2/2)∂^2_p rho.

Blockwise, rho00 drifts at +D1 and rho11 at -D1, both diffusing with D2. rho01 does not drift and decays at 2D0. From a Gaussian of width s0 times |+><+| the blocks stay Gaussian, and each block rho(p) ⪰ 0 iff e^{-4D0 t} <= e^{-D1^2t^2/(s0^2 + D2 t)}, independently of p. So:
- positivity holds for all t iff **D1^2 <= 4 D0 D2**;
- beyond the bound it fails from t* = 4 D0 s0^2/(D1^2 - 4 D0 D2).

**Mapping.** Oppenheim et al.'s Eq. (9) uses moments D_n that carry the 1/n!, and the back-reaction -∂(D1^{0α} L_α rho + h.c.). That gives D1^OSSWD = D1/2 and D2^OSSWD = D2/2, and their Eq. (23), D1 D0⁻¹ D1† ⪯ 2D2, becomes (D1/2)^2/D0 <= 2(D2/2), the same condition. The paper's Eq. (tradeoff) is quoted in OSSWD's normalisation and is right as written.

**Numerics.** Finite differences on p ∈ [-22, 22] with h = 0.01 (4401 points), evolved with expm_multiply to T = 3; parameters D0 = D2 = 1, s0 = 0.1. The maximum deviation from the exact solution is 1.1e-4 of the peak.

| D1^2/(4D0D2) | 0.5 | 1.0 (equality) | 1.01 | 2.0 |
|---|---|---|---|---|
| min block eigenvalue / peak | -2e-56 (0) | -3e-17 (rounding at t = 0) | -5.0e-4 | -0.239 |
| first negative time (grid step 0.05) | never | never | 1.00 (theory 1.00) | 0.05 (theory 0.01) |
| joint object: min eigenvalue / negative mass at T | 0 / 0 | 0 / 1e-18 | -8.3e-7 / 1.6e-5 | -8.9e-4 / 9.7e-4 |

The joint classical-quantum object is block-diagonal in p, so its spectrum is the union of the blocks' spectra.

**Minimal diffusion.** The smallest D2 that keeps positivity up to T = 50 (bisection) is 0.9998 = D1^2/(4D0) - s0^2/T. It tends to the balance-rule value as T grows.

**What equality is.**
- Measure sigmaz at strength D0 and drive p by the record, dp = α dY. That gives D1 = 2αsqrtD0 and D2 = α^2, exactly the equality case.
- 400 000 trajectories (s0 = 0, t = 1) reproduce ∫rho01 dp = 1/2e^{-2D0 t} and the branch drift D1 t (2.001 against 2).
- At equality p is a perfect record, so every block rho(p) is pure: 4det/tr^2 <= 8e-4, limited by the bin width.
- Adding independent noise (D2 doubled) mixes the blocks. At p = 0, 4det/tr^2 = 0.8646 against 1 - e^{-(4D0D2 - D1^2)t/D2} = 0.8647.
- The balance rule is therefore "the frame keeps every bit of the record": minimal diffusion for the given decoherence, or equivalently minimal decoherence for the given diffusion.

## G4. Two gravitationally coupled oscillators (exact Gaussian covariance)

**Model.** Units hbar = m = Ω = 1, with H = Σ(p^2 + x^2)/2 - K x1 x2 and K = 0.1. The covariance obeys dsigma/dt = Asigma + sigmaAᵀ + D, solved exactly by an augmented matrix exponential. Log-negativity is computed from the smallest symplectic eigenvalue of the partially transposed covariance.

**KTM channel.** Each x_j is measured at strength k, with Lindblad k(xrhox - 1/2{x^2, rho}), and the record x̂_i drives the force K x̂_i on the other mass. The averaged master equation is the quantum coupling plus momentum diffusion D(k) = k + K^2/(4k) per mass. This is KTM's Eq. (14) with Gamma = k, verified.

**Results.**
- **Quantum.** Maximum log-negativity 0.145 (vacuum, at t = 31) and 2.96 (squeezed r = 1).
- **KTM.** For 9 strengths k = (10⁻^2 to 10^2)K/2 and t <= 200, the smallest 2ν̃ is >= 1 to 1e-9, so the log-negativity is exactly 0, for both initial states.
- **The edge.** D(k) is minimal at k = K/2, with D = K (hbarK in SI): KTM Eq. (15), Gamma = K/2, and Eq. (19), D_grav = hbarK, reproduced. Quantum coupling plus dephasing at 0.99 K entangles the vacuum (1.3e-4), so the minimum is exactly the separability edge (KTM Eq. 18).
- **Trajectories.** 4000 trajectories with dt = 0.002 to T = 10 at k = K/2.
  - The conditional covariance stays block-diagonal (cross block exactly 0) and pure (4 det V₁ = 0.99995), so each trajectory is a product.
  - The trajectory-averaged means match the quantum mean dynamics from <x1>(0) = 1 (largest |z| = 2.1).
  - Covariance of means plus conditional covariance equals the master-equation covariance (largest |z| = 0.98).
- **Coherence.** Position coherence decays at D(x - x')^2/2 >= K(x - x')^2/(2hbar) (KTM Eq. 21).
- **Instance.** K = 2Gm^2/d^3 = 1.465e-28 N/m (KTM Eq. 5), so the minimal decoherence for Deltax = 250 um is 0.0434 /s. That equals the qubit minimum omega/2 = 0.0628 /s times (d^2 - Deltax^2)/d^2, the same physics, linearised. Bridge B's 72 /s is 1146 times the classical-channel minimum: GUID's balance rule ties diffusion to decoherence, but the decoherence itself is set by the self-term, not by the pair coupling.

---

## Citations

"Verified" means checked by web search or by reading the paper's text in this session. "Standard, not re-checked" means quoted from memory.

- J. Oppenheim, C. Sparaciari, B. Šoda, Z. Weller-Davies, "Gravitationally induced decoherence vs space-time diffusion: testing the quantum nature of gravity", *Nat. Commun.* 14, 7910 (2023), arXiv:2203.01982. **Verified**: the master equation, Eq. (9), and the trade-off, Eq. (23), were read in the arXiv text.
- D. Kafri, J. M. Taylor, G. J. Milburn, "A classical channel model for gravitational decoherence", *New J. Phys.* 16, 065020 (2014), arXiv:1401.0946. **Verified**: Eqs. (5), (9) to (16), (17) and (18), (19) and (21) were read in the arXiv text.
- A. Tilloy, L. Diosi, "Sourcing semiclassical gravity from spontaneously localized quantum matter", *Phys. Rev. D* 93, 024026 (2016), arXiv:1509.08705. **Verified** (bibliographic).
- M. J. Bremner, R. Jozsa, D. J. Shepherd, "Classical simulation of commuting quantum computations implies collapse of the polynomial hierarchy", *Proc. R. Soc. A* 467, 459 (2011), arXiv:1005.1407. **Verified** (bibliographic).
- M. J. Bremner, A. Montanaro, D. J. Shepherd, "Average-case complexity versus approximate simulation of commuting quantum computations", *Phys. Rev. Lett.* 117, 080501 (2016), arXiv:1504.07999. **Verified** (bibliographic; their anticoncentration statement was not re-read).
- S. Bose, A. Mazumdar, G. W. Morley, H. Ulbricht, M. Toroš, M. Paternostro, A. A. Geraci, P. F. Barker, M. S. Kim, G. Milburn, "Spin entanglement witness for quantum gravity", *Phys. Rev. Lett.* 119, 240401 (2017). **Verified**: the parameters (10⁻¹^4 kg, Deltax ~ 250 um, d ~ 450 um, d - Deltax ~ 200 um for Casimir-Polder at a tenth of gravity) and the witness were read in the accepted-manuscript text (arXiv:1707.06050).
- C. Marletto, V. Vedral, *Phys. Rev. Lett.* 119, 240402 (2017). Standard, not re-checked.
- L. Diosi, "A universal master equation for the gravitational violation of quantum mechanics", *Phys. Lett. A* 120, 377 (1987). **Verified** (bibliographic).
- R. Penrose, "On gravity's role in quantum state reduction", *Gen. Relativ. Gravit.* 28, 581 (1996). **Verified** (bibliographic, through a secondary listing only).
- R. Howl, R. Penrose, I. Fuentes, "Exploring the unification of quantum theory and general relativity with a Bose-Einstein condensate", arXiv:1812.04630. **Verified**: Eq. (23), E_G of displaced uniform spheres, was read in the arXiv text and is also re-derived here by quadrature. The journal reference, *New J. Phys.* 21, 043047 (2019), is standard, not re-checked.
- D. N. Page, "Average entropy of a subsystem", *Phys. Rev. Lett.* 71, 1291 (1993). Standard, not re-checked.
- C. E. Porter, R. G. Thomas, *Phys. Rev.* 104, 483 (1956). Standard, not re-checked.
- H. M. Wiseman, G. J. Milburn, "Quantum theory of optical feedback via homodyne detection", *Phys. Rev. Lett.* 70, 548 (1993); and *Quantum Measurement and Control* (CUP, 2010). Standard, not re-checked. The feedback master equation used here is re-derived and checked against trajectories.
- O. Guehne, G. Toth, "Entanglement detection", *Phys. Rep.* 474, 1 (2009), for the stabiliser and PPT witnesses. Standard, not re-checked.
- G. Vidal, R. F. Werner, *Phys. Rev. A* 65, 032314 (2002), for negativity; R. Simon, *Phys. Rev. Lett.* 84, 2726 (2000), for PPT of Gaussian states. Standard, not re-checked.
