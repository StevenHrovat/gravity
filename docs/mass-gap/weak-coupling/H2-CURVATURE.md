# (H2) and positive coarse Ricci curvature (2026-11-21)

Study for `PREP.md`, last section ("Tools for H2 from the existence half's language: curvature"). Question: how exactly is the
one-box bound (H2, `LimitGDS_W` in `../formal/OneScale/Effective/Physical.lean`) related to positive coarse Ricci curvature, and
what do curvature tools give. No simulations were run. Lean: `../formal/OneScale/Effective/Curvature.lean` (section 8).

Claim levels: **proved here** (complete argument in this note; **Lean** where marked), **literature, read** (statement checked in
the source during this session), **literature, recalled** (from memory, not re-checked), **heuristic** (argument with a named gap).

---

## 0. Result in one paragraph

H2 in W form is a statement about one kernel: the **random-block heat bath** K = M⁻¹ Σ_j P_{B_j} (pick one of the M blocks at
random and resample it from its specification). For the ℓ¹ cost distance d(σ, σ') = Σ_x c(σ_x, σ'_x) the precise relation is:
**W-GDS(γ) implies coarse Ricci curvature κ ≥ c₋(1 − γ)/M** (proved, Lean), and every curvature bound satisfies **κ ≤ c(x)/M** for
every x (proved, Lean), so in the natural normalisation (each site resampled at rate 1 in continuous time) the statement is
"normalised curvature ≥ 1 − γ", and the normalisation is sharp. The converse fails in general: curvature is equivalent (exactly,
for block partitions) to a **pointwise** W-GDS in which the supremum over boundary conditions is taken **outside** the sum over
blocks, which is strictly weaker than our GDS (explicit four-spin example, section 2.5). Theorem A itself goes through under the
pointwise condition, and its proof is literally "positive curvature in exponentially weighted ℓ¹ metrics". What curvature adds:
a volume-uniform spectral gap of the block dynamics, a block Poincare inequality (Var μ(f) ≤ (c₋(1 − γ))⁻¹ Σ_j μ(Var_j f)), and
Gaussian concentration (literature). What it does not add: Bonnet–Myers is vacuous for product spaces, and bounded reach is not a
diameter statement but positivity of the **tilted** curvature. As a route to proving H2, curvature is a restatement with one
real tool attached (Bakry–Emery: a pointwise Hessian test in place of an influence computation), which works only at strong
effective coupling. The photon test comes out sharp: for any Gaussian (non-compact U(1)) effective theory the curvature is
**exactly zero** along flat connections, at every scale (proved). The Z₂ test: curvature is boundary-uniform and therefore
stronger than a gap; deconfined Z₂ has a gap but no positive curvature (heuristic, consistent with Leg B's twist runs).

| statement | status |
|---|---|
| local-to-global: L-Lipschitz for d_w iff L_x(h) ≤ L w_x for every x | proved, Lean |
| W-GDS(γ), γE ≤ 1 ⇒ κ ≥ c₋(1 − γE)/M for d_w (weights w with the reach condition) | proved, Lean |
| pointwise W-GDS ⇒ the same | proved, Lean |
| κ ≤ c(x)/M for every curvature bound (sharpness of the normalisation) | proved, Lean (for a 1-Lipschitz test φ; κ ≤ c(x)/M needs c a metric) |
| block partitions: κ = (1 − γ_♭)/M exactly (γ_♭ the pointwise constant) | proved here (uses Kantorovich duality) |
| curvature does not imply W-GDS(γ < 1) | proved here (example, hand computation) |
| Theorem A holds under pointwise W-GDS | proved here (the Lean step lemma `lipBound_avg_at` is the only change; the covariance assembly not re-run in Lean) |
| spectral gap of the block dynamics ≥ c₋(1 − γ) (continuous time), block Poincare inequality | proved here from Ollivier's Lichnerowicz theorem (literature, read) and our DLR structure |
| Gaussian concentration | literature (Ollivier, read; Kuelske, recalled), constants not checked in our setting |
| Bonnet–Myers vacuous on product spaces; reach = tilted curvature | proved here (elementary) |
| Gaussian U(1): κ(σ, σ + φ) = 0 for every flat φ, every scale | proved here |
| compact U(1), Coulomb phase: no uniform κ > 0 at any scale | conditional (Froehlich–Spencer, recalled; pointwise Theorem A) |
| deconfined Z₂: no positive curvature, gap nevertheless | heuristic (Chatterjee-type argument, PROOF-NOTE §10.3; Leg B twist data) |
| Leg B coupled chains = pointwise influence estimates, not a curvature; cleaner measurement | section 6 |

---

## 1. Setting

As in `OneScale.Blocks` and `OneScale.Lipschitz`: finite index set ι (links, or cells of size L₁ for the effective theory),
single-coordinate space S (the group, or the block-variable space), cost c : S × S → [0, D_c] with c(a, a) = 0 (the bi-invariant
metric ρ in the gauge case), blocks B_j (j ∈ J, |J| = M) with specifications q_j^σ that depend on σ only off B_j, coverage
c(x) = #{j : x ∈ B_j} ∈ [c₋, c₊].

- **Distance.** d_w(σ, σ') = Σ_x w_x c(σ_x, σ'_x) for weights w ≥ 0; d = d_1. If c is a metric and w > 0, d_w is a metric.
- **Kernel.** K_σ = M⁻¹ Σ_j K_{j,σ}, where K_{j,σ} is the law of splice(B_j, σ, ξ), ξ ∼ q_j^σ. On functions, K h = `P.avg h`.
- **Coarse Ricci curvature** (Ollivier 2009, Def. 3, read): κ(σ, σ') = 1 − W₁(K_σ, K_σ')/d(σ, σ'); "κ ≥ κ₀" means for all pairs.
  Ollivier's Prop. 28 (arXiv v4 numbering, read) shows κ ≥ κ₀ iff K maps L-Lipschitz functions to (1 − κ₀)L-Lipschitz functions.
  We use this Lipschitz form as the definition (`CoarseRicciLB`); the equivalence with the transport form is Kantorovich–Rubinstein
  duality (needs c a metric, standard).
- **Influences.** k_j(z) is the W influence of PROOF-NOTE §1.6 (`IsInfluenceBoundW`), uniform in (σ, s). The **pointwise**
  influence k_j(z; σ, s) is the same quantity at one boundary condition σ and one new value s (`IsInfluenceBoundWAt`); its least
  value is W₁(q_{j,B}^σ, q_{j,B}^{σ^z})/c(σ_z, s), the transport distance of the two block laws for the ℓ¹ cost on the block.
- **Constants.** γ = sup_z c(z)⁻¹ Σ_{j ∌ z} sup_{σ,s} k_j(z; σ, s) (our GDS) and the **pointwise constant**
  γ_♭ = sup_{z,σ,s} c(z)⁻¹ Σ_{j ∌ z} k_j(z; σ, s). Always γ_♭ ≤ γ.

The curvature needs only the specifications, not a measure μ; the DLR identity enters only for the consequences in section 3
(stationarity, reversibility). So H2 for `qlim` can be phrased as curvature without knowing the limiting effective measure.

## 2. Question 1: the precise relation

### 2.1 Local to global (proved, Lean: `isLipW_of_lipBound`, `lipBound_of_isLipW`)

h is L-Lipschitz for d_w iff |h(σ) − h(σ^x)| ≤ L w_x c(σ_x, s) for every single-coordinate change. Proof: telescoping along the
path that changes one coordinate at a time; d_w is additive along that path (no triangle inequality for c is needed). This is
Ollivier's Prop. 19 (ε-geodesic spaces, read) in the product setting. Consequence: κ = inf over pairs differing in one coordinate.

### 2.2 W-GDS ⇒ positive curvature (proved, Lean: `coarseRicci_of_gds`, `coarseRicci_of_gdsAt`, `coarseRicci_of_gds_flat`)

**Theorem 2.2.** Let w ≥ 0 and E ≥ 0 satisfy the reach condition of Theorem A (w_y ≤ E w_x whenever y ∈ B_j and k_j(x) ≠ 0). If
W-GDS(γ) (or only the pointwise W-GDS(γ)) holds with γE ≤ 1, then

  κ_w(K) ≥ c₋(1 − γE)/M   for the distance d_w.

Unweighted (w ≡ 1, E = 1): κ ≥ c₋(1 − γ)/M.

*Proof.* Lemma 2.5 (W) of PROOF-NOTE at a fixed (σ, s): |P_j h(σ) − P_j h(σ^x)| ≤ (w_x + k_j(x; σ, s) E w_x) L c(σ_x, s) for
x ∉ B_j, and 0 for x ∈ B_j. Average over j and use the pointwise GDS: the Lipschitz constant at x becomes
(1 − c(x)(1 − γE)/M) L w_x. Then 2.1. In Lean the step lemma `lipBound_avg_at` is `lipBound_avg` with pointwise coefficients. ∎

**Normalisation.** In continuous time (each block rings at rate 1, generator L = Σ_j (P_j − I) = M(K − I)) the curvature rate is
M κ ≥ c₋(1 − γ). With uniform coverage c, the normalised rate (each site resampled at rate 1) is ≥ 1 − γ. This is the precise form
of "κ ≥ 1 − γ" in PREP.md.

### 2.3 The normalisation is sharp (proved, Lean: `coarseRicci_le_coverage`)

**Theorem 2.3.** If K has curvature ≥ κ for d, then for every x, every bounded measurable φ : S → ℝ with |φ(a) − φ(b)| ≤ c(a, b),
and all a, s: (1 − c(x)/M)|φ(a) − φ(s)| ≤ (1 − κ) c(a, s). With φ = c(·, s) (c a metric): **κ ≤ c(x)/M**.

*Proof.* Test h(τ) = φ(τ_x): blocks containing x forget x completely, the M − c(x) others keep it, so
K h(σ) − K h(σ^x) = (1 − c(x)/M)(φ(σ_x) − φ(s)). ∎

So for a product measure (γ = 0) with uniform coverage, κ = c/M exactly: Theorem 2.2 is tight at γ = 0 (also Ollivier's
tensorisation, Prop. 26, read: κ ≥ inf_i α_i κ_i with α_i = probability of moving factor i).

### 2.4 Exact formula for block partitions (proved here)

If the blocks partition ι (c ≡ 1, the "random block, exact resampling" dynamics), and c is a metric, then for every σ, x, s

  W₁(K_σ, K_{σ^x}) = M⁻¹ [ (M − 1) c(σ_x, s) + Σ_{j ∌ x} W₁(q_{j}^σ, q_{j}^{σ^x}) ],   hence   **κ = (1 − γ_♭)/M**.

*Proof.* "≤" is 2.2 at (σ, s). "≥": pick, for each j ∌ x, a test function F_j of the block B_j, 1-Lipschitz in each block
coordinate, attaining W₁(q_j^σ, q_j^{σ^x}) up to ε (Kantorovich duality), and F_{j₀}(τ) = c(τ_x, s) on the block j₀ ∋ x.
h = Σ_j F_j is 1-Lipschitz for d (disjoint supports, 2.1). Block j₀ contributes 0 to K h(σ) − K h(σ^x); every other block j
keeps F_{j₀} (contributing c(σ_x, s)) and resamples B_j (contributing ≥ W₁(q_j^σ, q_j^{σ^x}) − ε); the F_i, i ∉ {j, j₀}, do not
see x. So W₁(K_σ, K_{σ^x}) ≥ K h(σ) − K h(σ^x) ≥ right side − ε. Then κ = inf over single-site pairs (2.1). ∎

For overlapping families (our thin and thick cubes) only the bracket c₋(1 − γ_♭)/M ≤ κ ≤ c₋/M is proved; testing with additive
functions gives in addition κ ≤ M⁻¹[c(x) − c(σ_x, s)⁻¹ Σ_y ‖Σ_{j ∌ x, j ∋ y}(q_{j,y}^σ − q_{j,y}^{σ^x})‖_KR] (single-site
marginals only), which does not recover GDS.

### 2.5 Curvature does not imply W-GDS (proved here, by example)

Four Ising spins z, 1, 2, u, discrete metric (W₁ = total variation), single-site heat bath (blocks = sites, M = 4, c ≡ 1),
weight ∝ exp(H) with the three-body Hamiltonian

  H = J σ_z σ_1 (1 + σ_u)/2 + J σ_z σ_2 (1 − σ_u)/2,   t := tanh J.

Local fields: h_1 = Jσ_z(1 + σ_u)/2, h_2 = Jσ_z(1 − σ_u)/2, h_u = Jσ_z(σ_1 − σ_2)/2, h_z = Jσ_1(1 + σ_u)/2 + Jσ_2(1 − σ_u)/2;
the TV distance of two single-site laws with fields h, h' is |tanh h − tanh h'|/2. Flipping σ_z changes q_1 by t if σ_u = +1 (else 0),
q_2 by t if σ_u = −1 (else 0), q_u by t if σ_1 ≠ σ_2 (else 0). So the column of z has **sum of suprema 3t** but **pointwise sum
≤ 2t** (q_1 and q_2 never move together). The other columns: site 1 (and 2) pointwise and supremum 3t/2; site u pointwise and
supremum 2t. Hence γ = 3t and γ_♭ = 2t, and by 2.4, κ = (1 − 2t)/4. For 1/3 ≤ t < 1/2: **κ > 0 while GDS fails for every γ < 1**
(for this block family). ∎

Reading: GDS takes the worst boundary condition for each block separately; curvature takes the worst boundary condition once, for
all blocks together. When the worst cases of different blocks are incompatible (here: σ_u cannot be +1 and −1), curvature is
strictly weaker.

### 2.6 Theorem A is curvature in tilted metrics (proved here; Lean for the step)

The only place where `theoremA_W` (`OneScale.Lipschitz`) uses GDS is the contraction step `lipBound_avg` with the weight
w = e^{λ dist(·, S_g)} and E = e^{λD₁}. By 2.2 that step is exactly **κ_w(K) ≥ c₋(1 − γe^{λD₁})/M for the exponentially tilted
distance d_w**. The rest of Theorem A (block covariance identity, telescoping, t → ∞) uses only the conclusion. Hence:

- **Theorem A holds under the pointwise W-GDS** (replace `lipBound_avg` by `lipBound_avg_at`; the covariance assembly
  `cov_le_weighted_W` is unchanged). This is a free strengthening of Theorem A, and with 2.4 it shows that for partitions the
  natural hypothesis of Theorem A is exactly "positive tilted curvature".
- The reach D₁ enters only through the tilt: positivity of the curvature survives the tilt e^{λ dist} for λ < log(1/γ)/D₁. The
  largest such λ is the decay rate Theorem A gives.

### 2.7 Systematic scan (literature, recalled)

The Lean `iter` is the random-scan (averaged) operator, which is the natural object for curvature. A systematic sweep
P_{j_M} ⋯ P_{j_1} contracts under Dobrushin-type conditions on both rows and columns of the influence matrix (Dyer, Goldberg,
Jerrum, "Dobrushin conditions and systematic scan", recalled, not re-checked); with column sums alone (our GDS) a single sweep is
not shown to contract here. Not needed for H2.

## 3. Question 2: what curvature gives in our setting

Assume κ := c₋(1 − γ)/M > 0 for d (from W-GDS or pointwise W-GDS), and that the specifications come from a measure μ
(BlockSpec: DLR identity).

**(a) Contraction to equilibrium (proved, Lean: `CoarseRicciLB.iterate`).** ‖K^t h‖_Lip ≤ (1 − κ)^t ‖h‖_Lip; with μ(K h) = μ(h)
(`integral_avg`): |K^t h(σ) − μ(h)| ≤ (1 − κ)^t ‖h‖_Lip · N D_c. The block dynamics forgets its start; in continuous time at rate
c₋(1 − γ), uniform in the volume.

**(b) Spectral gap and block Poincare inequality (proved here from literature).** K is self-adjoint in L²(μ): P_j h is the
conditional expectation of h given the coordinates off B_j (DLR plus the pull-out Lemma 2.2), and μ(f P_j h) = μ(P_j f · P_j h)
(proved inside `integral_mul_sub_avg`, Lemma 2.6). Ollivier's Lichnerowicz theorem (Prop. 29/Cor. 30 of arXiv v4, read: reversible
kernel, κ > 0, finite spread σ) gives spectral radius ≤ 1 − κ on L²₀(μ). The Dirichlet form is
E(f, f) = ⟨f, (I − K)f⟩ = M⁻¹ Σ_j μ(Var_{q_j} f) (each P_j is an orthogonal projection), so

  Var_μ(f) ≤ (c₋(1 − γ))⁻¹ Σ_j μ(Var_{q_j} f),

the **block Poincare inequality** (approximate tensorisation of variance) with a volume-independent constant, and the continuous-time
block dynamics has spectral gap ≥ c₋(1 − γ). With Var_{q_j} f ≤ (b D_c²/4) Σ_{x ∈ B_j} L_x(f)² this gives an Efron–Stein-type bound
Var_μ(f) ≤ b c₊ D_c² Σ_x L_x(f)² / (4 c₋(1 − γ)) (sums of N local terms fluctuate on the scale √N).
Caution: this is the gap of a **dynamics**, not the transfer-matrix (Hamiltonian) gap. The physical gap comes from Theorem A plus
reflection positivity (Theorem C), not from Lichnerowicz.

**(c) Concentration (literature).** Ollivier Prop. 31/Thm. 32 (read): Var_μ f ≤ σ²/(nκ) for 1-Lipschitz f and Gaussian
concentration μ(f ≥ μf + t) ≤ exp(−t²/(6D²)) up to a range t_max, with D² = σ²/(nκ), σ the spread of one step and n the local
dimension, under a Lipschitz condition on x ↦ D_x². Here σ² ≤ 2b²D_c², n ≥ 1, so D² ≲ 2b²D_c² M/(c₋(1 − γ)) ∝ volume: Gaussian
tails for empirical averages on the √N scale. That Dobrushin-type uniqueness implies Gaussian concentration is also known
independently (Kuelske, Commun. Math. Phys. 239 (2003), recalled). The exact hypotheses of Thm. 32 in our setting were not checked.

**(d) Covariance decay.** Unweighted curvature alone gives (a)–(c), not spatial decay: a curvature bound does not know where the
observables sit. Spatial decay needs the tilt of 2.6, and then it is Theorem A. So exponential decay of covariances is **equivalent
in proof** to Theorem A, not new.

**(e) Bonnet–Myers (proved here: vacuous).** Ollivier Prop. 23 (read): diam ≤ 2 sup J/κ with the jump J(σ) = W₁(δ_σ, K_σ). Here
J ≤ M⁻¹ Σ_j |B_j| D_c ≤ c₊ N D_c/M and diam = N D_c (if D_c = diam_c S), so Bonnet–Myers reads κ ≤ 2c₊/M, which is weaker than the
trivial bound κ ≤ c₋/M of 2.3. The same holds for every weighted product metric (jump and diameter are both sums over sites). The
average form (Prop. 24, read) is likewise trivial. **Bounded diameter has no meaning on a product configuration space, and it does
not correspond to bounded reach.** Reach is the tilt: positive curvature in d_w with w = e^{λ dist}, λ > 0, uniformly in the
volume (2.6).

| consequence | relative to Theorem A |
|---|---|
| contraction of the block dynamics, rate c₋(1 − γ) | new statement, same proof step |
| spectral gap of the block dynamics, block Poincare | **new** (needs DLR/reversibility; a dynamical, not a physical gap) |
| variance and Gaussian concentration | new as statements; variance order also follows from summing Theorem A |
| exponential decay of covariances | equivalent (Theorem A = tilted curvature) |
| Bonnet–Myers diameter | vacuous |

## 4. Question 3: tools for proving H2 via curvature

**Tensorisation and products (literature, read).** Ollivier Prop. 26: κ(product) ≥ inf_i α_i κ_i. Gives κ = c/M at γ = 0 (2.3),
nothing for interacting blocks; the interaction is exactly the influence sum.

**Conditional measures.** For the exact block heat bath the "curvature inside a block" is 1 (exact resampling); what matters is the
boundary sensitivity of the block law, i.e. the influence. Curvature of the conditional measure enters only through Bakry–Emery
(below), as a tool to bound that sensitivity.

**Perturbation: Ollivier vs our robustness lemma.** (i) Lipschitz-level closeness: if ‖(K' − K)h‖_Lip ≤ δ‖h‖_Lip, then
κ' ≥ κ − δ (trivial). Our robustness lemma works one level lower, on the influence coefficients: `InfluenceDevW ≤ δ` on the shells
moves each W coefficient by ≤ δ (`IsInfluenceBoundW.of_devW`) and GDS(γ) to GDS(γ + rδ) (`gds_shellCoeff`), so by 2.2 the curvature
bound moves from c₋(1 − γ)/M to c₋(1 − γ − rδ)/M. So **our robustness lemma is stability of the curvature bound under C¹
(derivative-level) closeness of the specifications**, which is why (H1) in W form asks for convergence of boundary derivatives. (ii) Ollivier Section 6 (read, without proof there) loosens the
definition to W₁(K_σ, K_σ') ≤ (1 − κ)d + δ; this is stable under sup-W₁ closeness of kernels but only controls distances above
δ/κ. (Heuristic) A version of H1 in sup-W₁ form would then give decay up to an additive floor O(δ_k/κ) → 0, i.e. decay in the
limit but not uniformly at every level; not pursued. (iii) Stationary measures (proved here, two lines): if K has curvature κ and
stationary law μ, and K' has stationary law μ', then W₁(μ, μ') ≤ sup_σ W₁(K_σ, K'_σ)/κ (from W₁(μK, μ'K') ≤ W₁(μK, μ'K) +
W₁(μ'K, μ'K') ≤ (1 − κ)W₁(μ, μ') + sup_σ W₁(K_σ, K'_σ), using Ollivier's Prop. 20, read).

**Bakry–Emery (literature).** For a measure e^{−V} on a Riemannian manifold, Ric + Hess V ≥ K > 0 (CD(K, ∞)) gives log-Sobolev,
Poincare, and W₂-contraction e^{−Kt} of the Langevin dynamics (von Renesse–Sturm 2005, recalled); Ollivier's Example 11 (read)
identifies his coarse curvature of small-step diffusions with ½Ric − ∇^{sym}F (drift F = −½∇V), i.e. Bakry–Emery up to
normalisation. For a bi-invariant metric, Ric(X, X) = ¼ Σ_i ‖[X, E_i]‖² (Milnor 1976, recalled; for SU(N) with
⟨X, Y⟩ = −tr XY this is Ric = N/2, zero for U(1)). Shen–Zhu–Zhu (arXiv:2204.12737, Commun. Math. Phys. by its DOI 10.1007/s00220-
022-04609-1; abstract read) verify Ric + Hess S ≥ K > 0 on the whole lattice for SU(N) at |β| < 1/(16(d − 1)) (SO(N):
|β| < (N − 2)/(32(d − 1)N)), and obtain uniqueness, exponential ergodicity in a Wasserstein distance, log-Sobolev and a mass gap.
That is positive curvature of a **different dynamics** (Langevin) in a **different metric** (ℓ², W₂) from ours (block heat bath,
ℓ¹, W₁).

The bridge from Bakry–Emery to our influences (heuristic, standard technique, not proved here): if each block conditional satisfies
CD(K_B) uniformly in the boundary and the mixed Hessian of the block Hamiltonian in (block coordinates, z) is bounded by h_{jz},
synchronous coupling of the two block Langevin dynamics gives W₂(q_j^σ, q_j^{σ^z}) ≤ (h_{jz}/K_B) c(σ_z, s), hence
k_j(z) ≤ √b h_{jz}/K_B (ℓ² to ℓ¹ on the block). The single-site version with a matrix condition is the Otto–Reznikoff criterion
(J. Funct. Anal. 243 (2007), recalled). **This is the one genuine tool curvature adds:** a pointwise inequality on the Hessian of
the (effective) action, checkable locally (for instance by interval arithmetic), in place of a transport distance between
conditional laws, which requires solving the block. Its limit: on a compact group the action has maxima, so Hess V ≤ −Cβ somewhere,
and CD(K) with K > 0 needs Ric > Cβ: **strong (effective) coupling only** (selfcharge NOTE §5).

**Why curvature is swamped at weak coupling at the lattice scale (sharpened here).** Coarse curvature is bounded above along every
direction in which the dynamics is (nearly) equivariant (section 5.1: an exact symmetry τ with K_{τσ} = τ_#K_σ and a test function
that sees τ forces κ(σ, τσ) ≤ 0). At weak coupling the field is locally flat (selfcharge Lemma 2.1: ‖aka⁻¹k⁻¹ − 1‖ ≤ 2‖a − 1‖‖k − 1‖),
so multiplying the ν-links by a constant abelian element exp(itX) is a symmetry of the plaquettes up to O(t·g) commutator terms.
Hence (heuristic, quantitative form of route (d)) κ ≤ O(g) along those directions at the lattice scale, for every block family of
bounded size in lattice units: the group curvature Ric = O(1) never gets a chance, because the obstruction is a near-flat direction
of the action, not the geometry of G. The free-field sum rule (`attempts/admissible/NOTE.md`, Theorem 4.1: block GDS constant ≥ 1
at every block size) is the same fact in GDS language.

**Why that does not apply at L₁ (heuristic).** The near-symmetry needs the block variables to sit within O(g) of a flat
configuration. At L₁, where the running coupling is O(1), block holonomies are spread over G (the commutator of typical block
variables is O(1), Lemma 2.2 of the selfcharge note at first order), so there is no near-flat direction and no reason for κ ≤ 0. In
the confined phase centre twists are disordered (zero twist free energy), so the discrete near-symmetry (centre multiplication of a
slab) is also not an obstruction. **Absence of an obstruction is not a proof of positivity.** Whether the effective theory at L₁ is
inside a proven window is open: the windows by Hessian or single-link criteria are tiny (SZZ |β| < 1/48 in d = 4; our single-link
window (16d)²(1 − e^{−4n|β|}) < 1, i.e. β ≲ 3·10⁻⁵ for SU(2), d = 4), and the self-charge note's sharp-coefficient lemma says soft
constants cannot be traded across scales. The realistic curvature route to H2 is a **block** (Dobrushin–Shlosman type) certificate
at one scale, where the curvature formulation buys the pointwise constant γ_♭ (2.4–2.5) and the Hessian test above, nothing more.

## 5. Question 4: photon and Z₂ tests

### 5.1 Gaussian U(1): exactly flat at every scale (proved here)

Non-compact U(1), any Gaussian effective action depending on the field only through its curl, S = ½⟨dA, Q dA⟩ (Q > 0; this class is
closed under linear gauge-covariant blocking), any block family, ℓ¹ cost c(a, b) = |a − b|. Let φ be a flat connection (dφ = 0,
e.g. A_ν ≡ t). The conditional density of the block given the outside depends on d(splice(σ, ξ)), so q_j^{σ+φ} = (τ_φ)_# q_j^σ on
the block, and K_{σ+φ} = (τ_φ)_# K_σ. Then

  W₁(K_σ, K_{σ+φ}) = W₁(ν, (τ_φ)_#ν) = ‖φ‖₁ = d(σ, σ + φ),   ν = K_σ,

("≤" by the coupling Y ↦ Y + φ; "≥" by the 1-Lipschitz test h(A) = Σ_e sgn(φ_e) A_e, whose mean moves by Σ_e |φ_e|). So
**κ(σ, σ + φ) = 0 for every σ and every flat φ ≠ 0: the curvature is ≤ 0 at every scale, every β, every block family.** In the
gauge-quotient metric (alignment mod interior gauge, PROOF-NOTE §3) take φ = t·1_ν and the divergence-free test function 1_ν (the
sum-rule test function of the admissible note): same conclusion. This is the photon test passed sharply: flat group, flat
dynamics.

**Compact U(1), Coulomb phase (conditional).** The flat shifts U ↦ U e^{iφ} (dφ ∈ 2πℤ) are exact symmetries of the Wilson action,
and at weak coupling the block marginals are concentrated, so the same test gives κ(σ, σφ) ≤ o(1) as β → ∞ at fixed scale
(heuristic). Rigorous form, conditional: if some block family of bounded geometry had pointwise tilted curvature bounded below
uniformly in the volume, Theorem A (pointwise version, 2.6) would give exponential decay of block-observable covariances, contrary to
the massless Coulomb phase of 4D U(1) at weak coupling (Guth 1980; Froehlich–Spencer 1982; recalled, the precise observables there
not re-checked). So no uniform κ > 0 at any scale.

### 5.2 Z₂: a gap without positive curvature (heuristic)

For a finite group with the discrete metric, W₁ = total variation and coarse curvature of the single-site heat bath is Dobrushin's
TV contraction; Ollivier's Example 17 (read) states that for Ising Glauber dynamics positive curvature "amounts to" Dobrushin's
single-site criterion. At strong coupling Z₂ gauge theory has κ > 0 (Dobrushin), gap and area law. In the deconfined phase (weak
coupling) it has a gap but no confinement. Curvature is a **boundary-uniform** statement (inf over all σ), a gap is a property of
one state; the deconfined phase behaves like low-temperature Ising, where a boundary condition (here a centre twist) changes the
interior at every distance. Evidence and argument: (i) Leg B feasibility, Z₂ β = 0.6, twist BC: the loop deficit is 1.89–2.00 at
every R and depth and the vortex sheet costs action through the whole box (`../lattice/PREREG-BOUNDARY.md`), i.e. W₁ between the
twisted and untwisted block laws is of the order of the box; (ii) if κ > 0 uniformly (tilted, 2.6) held at some scale, decay under
all boundary conditions would follow, and with the unbroken centre Chatterjee's mechanism would give an area law, contradicting the
perimeter law of deconfined Z₂ (PROOF-NOTE §10.3; conditional there on Chatterjee's theorem for finite G). So: **κ ≤ 0 at every
scale in deconfined Z₂; gap without curvature.** H2 in curvature form is a confinement-strength statement, stronger than a gap.
(Leg B's single-flip coupled chain at calm BC, k̂ = 0.01, is consistent with this: one flip is absorbed; the worst case is a
different, "pivot", boundary condition.)

## 6. Question 5: what Leg B's coupled chains measure

`boundary.py couple` runs two single-link heat-bath chains inside one box V with boundary conditions τ and τ^y (one shell link
moved), shared random numbers (inverse CDF), running Landau re-alignment; it reports k̂(y) = Σ_e ρ(U_e, U'_e)/ρ(τ_y, τ'_y).

- **Object.** At stationarity the pair is a coupling of q_V^τ and q_V^{τ^y}, so k̂(y) is an **upper estimate of the pointwise W
  influence k_V(y; τ, ·)** (one entry, at one boundary condition), in the ℓ¹ ρ-metric modulo interior gauge. It is not itself a
  curvature. R_face = |∂V| k̂/|V| is a proxy for the pointwise column sum c(y)⁻¹ Σ_{j ∌ y} k_j(y; σ) of the random-cube dynamics at
  the calm configuration, so **1 − R_face is a proxy for the normalised coarse curvature of the random-cube heat bath, at one
  configuration, in the quotient ℓ¹ metric** (by 2.2 and 2.4, with c = ρ). Since a coupling overestimates W₁, it is a lower
  estimate there; H2 needs the infimum over all σ, which is lower still.
- **Why it is vacuous in rough regimes.** By 4 (iii) the stationary distance of two chains with different boundary data is
  ≈ (one-step perturbation)/(contraction rate of the **coupling**). The synchronous coupling contracts well only for near-Gaussian
  dynamics; in rough, confined regimes the coupling's own contraction rate is poor or negative, so k̂ blows up although the true W₁
  may be small. Leg B's U(1) confined (k̂ = 457) and Z₂ β = 0.3 (663) rows are this effect.

**Cleaner curvature measurements (designs, not run).**
1. **Exact lattice-scale curvature field, no coupling.** For the single-link heat bath, 2.4 gives
   κ(σ, σ^e) = N⁻¹(1 − Σ_{e'} W₁(q_{e'}^σ, q_{e'}^{σ^e})/ρ(σ_e, s)); each term is a W₁ distance between two explicit single-link laws
   (staple-dependent; one-dimensional integrals for U(1), a class-function computation for SU(2)), so the local curvature of the
   lattice-scale dynamics on equilibrium configurations is computable exactly. Prediction: negative at β = 2.3 (swamped), a check of
   section 4.
2. **Curvature upper bounds along near-flat directions at block scale (coupling-free, falsifying).** For a candidate block size L,
   move the boundary along a constant abelian shift or a boundary gauge rotation and record the change of the sum-rule test
   functional (straight lines across the box, already recorded by Leg B) divided by the distance moved: a **lower** bound on
   W₁/d, hence an **upper** bound on κ that no coupling artefact can fake. If it stays near 1 at the physical L₁, H2 fails at that
   scale; Leg B's paired observable differences are already of this type.
3. **Coalescing coupling for rough regimes.** Replace the synchronous coupling by a maximal (TV) coupling of each single-link update
   (the pair coalesces with probability 1 − TV), and measure the one-sweep contraction from two interior starts with the **same**
   boundary: a certified-direction lower bound on the interior curvature where the synchronous coupling is vacuous.

## 7. DMP reading (short)

The owner's reading "existence as positive curvature, light is flat" has a precise form here: **flat = an exact or near symmetry of
the effective dynamics along which nothing contracts** (5.1: κ = 0 exactly for any Gaussian photon theory), and **existence = the
absence of such directions at the node's scale**, made quantitative by the tilted curvature (2.6), whose positivity range in λ is the
reach. Precision: this uses the mathematics of curvature (optimal transport on configuration space), not the geometry of spacetime;
Bonnet–Myers (bounded diameter) does not carry over to product spaces and is not the reach (3e). Z₂ shows that positive curvature
(boundary-uniform forgetting) is stronger than a gap (5.2).

## 8. Lean: `OneScale/Effective/Curvature.lean`

Built in WSL `~/formal-att-a` with `sync-build.sh OneScale.Effective.Curvature`: "Build completed successfully (8928 jobs)", no
warnings, no `sorry`/`axiom`/`native_decide`; `#print axioms` of the main theorems: `propext`, `Classical.choice`, `Quot.sound` only.
Not yet imported by the root `OneScale/Effective.lean` (left unchanged).

- `wdist`, `IsLipW`, `wdist_update`; `isLipW_of_lipBound`, `lipBound_of_isLipW` (2.1).
- `CoarseRicciLB` (Ollivier's Lipschitz form), `CoarseRicciLB.iterate` (3a).
- `IsInfluenceBoundWAt`, `IsInfluenceBoundW.at`, `lip_blockAvg_of_not_mem_at`, `BlockSpec.lipBound_avg_at` (pointwise step).
- `BlockSpec.coarseRicci_of_gdsAt`, `BlockSpec.coarseRicci_of_gds`, `BlockSpec.coarseRicci_of_gds_flat` (2.2).
- `BlockSpec.coarseRicci_le_coverage` (2.3).

Not formalised: the transport (W₁) form and Kantorovich duality, 2.4 and the example 2.5, Theorem A under pointwise GDS (the
assembly, a copy of `cov_le_weighted_W`), the spectral and concentration consequences, section 5.

## 9. References

- Y. Ollivier, "Ricci curvature of Markov chains on metric spaces", J. Funct. Anal. 256 (2009) 810–864; arXiv:math/0701886.
  **Read** (arXiv v4 via ar5iv; proposition numbers are those of v4 and may differ in the journal): Def. 3, Prop. 19, 20, 23, 24,
  26, 28, 29, Cor. 30, Prop. 31, Thm. 32, Examples 11 and 17 (Ising Glauber, "Dobrushin's criterion using a single site"), Section 6.
- H. Shen, R. Zhu, X. Zhu, "A stochastic analysis approach to lattice Yang–Mills at strong coupling", arXiv:2204.12737 (DOI
  10.1007/s00220-022-04609-1). **Abstract read** (conditions on β, results).
- R. L. Dobrushin, "Prescribing a system of random variables by conditional distributions", Theory Probab. Appl. 15 (1970); Dobrushin
  1956 (ergodic coefficient, cited by Ollivier as [Dob56]); Dobrushin–Shlosman 1985 (constructive criterion). **Recalled.**
- D. Bakry, M. Emery (1985), Lott–Villani and Sturm (2006–2009, synthetic Ricci curvature), von Renesse–Sturm (Comm. Pure Appl.
  Math. 2005, W-contraction ⇔ Ricci bound). **Recalled**; LSV not used beyond naming the family.
- F. Otto, M. Reznikoff, J. Funct. Anal. 243 (2007) (Hessian matrix criterion). **Recalled.**
- C. Kuelske, Commun. Math. Phys. 239 (2003) (concentration under Dobrushin uniqueness). **Recalled.**
- M. Dyer, L. A. Goldberg, M. Jerrum, "Dobrushin conditions and systematic scan". **Recalled.**
- J. Milnor, Adv. Math. 21 (1976) 293 (curvature of bi-invariant metrics). **Recalled.**
- A. Guth, Phys. Rev. D 21 (1980) 2291; J. Froehlich, T. Spencer, Commun. Math. Phys. 83 (1982) 411 (4D U(1) Coulomb phase).
  **Recalled.**
- S. Chatterjee, arXiv:2006.16229 (decay under all boundary conditions + centre ⇒ area law). As used in PROOF-NOTE §5, §10.3.
- Search hits seen but not read: D. Paulin, "Mixing and concentration by Ricci curvature" (arXiv:1404.2802; multi-step curvature,
  Glauber via the Dobrushin matrix); Erbar, Henderson, Menz, Tetali, arXiv:1602.05414 (entropic curvature of weakly interacting
  chains).
