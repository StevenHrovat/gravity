# Route (c), admissible Yang–Mills: attempt note (2026-11-21)

Attempt round on the open hypothesis `UniformGDS` (`../../../formal/OneScale/CorollaryB.lean`; PROOF-NOTE §7, (OS_k)).
Route (c) of `../../PREP.md`: in Luescher's admissible theory (every plaquette's defect ‖1 − U_p‖ below a bound) the large
fields are absent by construction; examine whether one renormalisation step can then be controlled well enough to give a
recursion for the box influence, or a direct bound on the GDS coefficient at small coupling in small boxes.

Claim levels as in RULES.md: **proved** (complete proof here, Lean where marked), **proved with a stated gap**,
**heuristic**, **conjecture**, **numerical** (computed here, exact up to floating point), **literature (memory)** (not
re-read in this round).

---

## 0. Results at a glance

**Verdict: route (c) fails, at a precise place, and the failure is informative.** Admissibility removes large fields only
at the cutoff scale. The obstruction to a weak-coupling bound on the GDS coefficient is not large fields at all: it is
present in the free (Gaussian) theory, it is a sum rule forced by the boundary gauge freedom (open Wilson lines across the
box), and for d = 4 also the field-strength part of the influence exceeds 1. Only compactness effects (lines and fluxes
across the box wrapping the group) can bring the coefficient below 1, and none of them appears at any finite order of the
small-field expansion.

| # | statement | level |
|---|---|---|
| A1 | Wilson and admissible expectations differ by O(β^K e^{−βε}) at fixed lattice volume: identical perturbation theory to all orders (§2.1) | proved (sketch with standard Haar-ball bound) |
| A2 | In a fixed physical box, the Wilson measure has a diverging number of inadmissible plaquettes as a → 0, for every ε below a threshold: the constraint is active, universality is an RG assumption, not a rarity statement (§2.2) | heuristic (asymptotic-freedom counting) |
| A3 | Hard admissibility with small ε puts the theory at weak coupling at every β, β = 0 included; soft admissibility at fixed η₀ is a bounded change of the Wilson weight. The admissible theory has no strong-coupling end where our proven windows apply (§2.4) | heuristic (hard), proved (soft is in (Φ)) |
| B1 | **Blocking bound**: one 2 × 2 blocking step multiplies the admissibility bound by at most 4 (decimation blocking; any group with a conjugation-invariant subadditive defect, in particular ‖1 − U‖ on unitary matrices) (§3) | **proved, Lean** (`Blocking.lean`) |
| B2 | B1 is sharp (constant U(1) field); admissibility at any ε constrains no loop of side ≳ √(π/ε); Balaban's large-field threshold g p(g) is far below a fixed ε, so even at step 0 admissibility does not remove Balaban's large fields (§3) | proved (sharpness, Lean); comparison heuristic |
| C1 | **Sum rule**: in the Gaussian (perturbative) block measure, Σ_{y ∈ shell, dir ν} r^{(y)} = 1 on every ν-link, hence Σ_y k^W(y) ≥ #{ν-links}: γ_0 ≥ 1 for every block shape and size, every d (§4.1) | **proved** (exact linear algebra; verified numerically to 1e-15) |
| C2 | For every compact connected G (SU(2), U(1), admissible or not), at fixed box side ℓ and β → ∞ with cold boundary: Σ_{y dir ν} k^W(y) ≥ (1 − o(1))·#{ν-links}, i.e. γ_W ≥ 1 − o(1) (GDS*: ≥ 1 − 2/ℓ − o(1)) (§4.1) | proved with a stated gap (finite-dimensional Laplace concentration not written out); telescoping step **Lean** (`SumRule.lean`) |
| C3 | Gaussian GDS coefficients computed for thin cubes: d = 4, γ_0 ≈ 5.8 → 5.05 (ℓ = 3 … 7); field-strength-only part γ_full ≈ 0.98 → 1.14 (ℓ = 2 … 5), **growing**; d = 2: γ_full → 0.34 (gapped Gaussian), d = 3: γ_full → 0.95 rising (§4.2) | numerical |
| C4 | Hence: no box of fixed lattice size satisfies GDS at weak coupling; UniformGDS can hold only at a physical box size where the running coupling is O(1), and the contraction must come from disorder of lines/fluxes across the box (wrapping of the group), invisible at every order of the small-field expansion (§4.3–§4.4) | proved (fixed ℓ) / heuristic (where the input enters) |
| D1 | Hard admissibility: sectors appear in boxes larger than ρ_min(ε) ~ ε^{−1/2} lattice units, GDS = ∞ there (PROOF-NOTE C8 confirmed); for U(1) on boxes no sectors (admissible fillings form a convex set) (§5) | heuristic (SU(2) sector size), proved (U(1) convexity, given C5) |
| D2 | Soft admissibility removes the formal blow-up; it is in hypothesis (Φ), reflection positive (§5) | **proved, Lean** (`Soft.lean`) |
| E1 | Admissible U(1) with ε < π/3 has no monopoles at any β, β = 0 included (§6) | **proved, Lean** (`no_monopole`) |
| E2 | Hence admissible U(1) is in the Coulomb (massless) phase at every β (§6) | heuristic (standard; no monopoles + gradient-model masslessness) |
| E3 | Soft-admissible Z₂ *is* Wilson Z₂ at β' = β + ½ log(1/η₀); hard-admissible Z₂ is pure gauge (§6) | **proved, Lean** (`z2_softAdmissible_eq_wilson`) |

Photon/Z₂ test: passed by every claim above (they are obstructions or exact identities; none would give a reach for U(1)
or confinement for Z₂). Admissibility itself makes U(1) *more* massless (it kills the confined phase) and Z₂ more
deconfined, so "admissible ⇒ gap" or "admissible ⇒ confinement" is false in general and must use non-commutativity.

---

## 1. Setting

- Lattice, links, plaquettes, blocks, shells, specifications, seminorms, influence coefficients k^H, k^W, GDS, GDS*: as in
  PROOF-NOTE §1 and §3.7. Thin cube V_ℓ = links with both ends in {0,…,ℓ}^d; |V_ℓ| = dℓ(ℓ+1)^{d−1}; interior sites
  {1,…,ℓ−1}^d; K_V = gauge transformations at interior sites.
- Shortfall s(U) = n − Re tr U = ½‖1 − U‖_F². Hard admissible weight `admissibleWeight` (`Positivity/Admissible.lean`):
  e^{βx}·1[n − x ≤ ε]. Soft weight (PROOF-NOTE §9.1): e^{βx}(η₀ + (1−η₀)1[n − x ≤ ε]), 0 < η₀ ≤ 1 (`Soft.lean`).
- Defect δ(U) = ‖1 − U‖ (operator norm in `Blocking.lean`; ‖·‖_op ≤ ‖·‖_F ≤ √n‖·‖_op, so s ≤ ε ⇔ admissibility up to
  constants).
- Standard SU(N) one-loop data: b₀ = 11N/(48π²), β = 2N/g², a·Λ ≈ exp(−1/(2b₀g²)), hence log(1/a) ≈ β/(4Nb₀).

---

## 2. (i) Universality: what is known, what is assumed

### 2.1 Perturbation theory is identical (proved, fixed volume)

**Proposition 2.1.** On a fixed finite lattice with link set E, for every bounded F and ε > 0,
|⟨F⟩_Wilson − ⟨F⟩_adm| ≤ 2‖F‖_∞ · P_W(some s_p > ε) and P_W(some s_p > ε) ≤ (Cβ)^{dim G·|E|/2} e^{−βε} for β ≥ β₀(E).

*Proof.* Write the Wilson density as e^{−βS}/Z with S = Σ_p s_p ≥ 0 (up to the constant e^{βn|P|}). The admissible measure is
the Wilson measure conditioned on A = {all s_p ≤ ε}; for a conditioned measure |μ(F|A) − μ(F)| ≤ 2‖F‖ μ(A^c). On A^c,
S > ε, so ∫_{A^c} e^{−βS} ≤ e^{−βε}. And Z ≥ e^{−1}·Haar(S ≤ 1/β) ≥ e^{−1}·Haar(every link within c/√β of 1), since
s_p is bounded by a constant times the sum of the squared link distances of its four links; the Haar measure of a ball of
radius r in G is ≥ c_G r^{dim G}. ∎

So every coefficient of the 1/β expansion (perturbation theory) agrees; Λ-parameter ratios, which are fixed by one-loop
matching, agree. **Not uniform in the volume**: |E| sits in the exponent.

### 2.2 The constraint is active in every physical box (heuristic)

A local lattice excitation whose minimal Wilson action is σ (in units of β/N per plaquette shortfall, i.e. weight e^{−βσ/N})
has density ~ a^{−4} e^{−βσ/N} = Λ⁴ exp((β/N)(1/b₀ − σ)) per physical volume. It diverges as a → 0 iff
**σ < 1/b₀ = 48π²/(11N)** (SU(2): 21.5 in shortfall units, i.e. S_W < 48π²/(11N²) = 10.77 in the normalisation
S_W = Σ(1 − Re tr U/N); this is the dislocation threshold 12π²/11 of Pugh–Teper, literature (memory)). An excitation whose
largest plaquette has shortfall t costs σ_min(t) → 0 as t → 0. So for every small ε the Wilson measure has, in a fixed physical
box, a number of inadmissible plaquettes that diverges like a^{−4+4b₀σ_min(ε)}, although the fraction per plaquette falls like
a^{4b₀σ_min(ε)}.

Consequences:
- The admissible theory is **not** a restriction to a set of asymptotically full measure. "The rule is physically free"
  (PREP route 6, plan (b)) cannot mean that; it can only mean universality in the RG sense.
- Prediction for the planned GPU measurement (b): the per-plaquette violation fraction falls like e^{−βσ_min(ε)/N}·(poly);
  a fit gives σ_min(ε); the count per physical volume diverges if σ_min(ε) < 1/b₀. At β = 2.3–2.7 (SU(2), ⟨Re tr U_p⟩/2 ≈ 0.6–0.7,
  mean shortfall ≈ 0.6–0.8) Luescher-size ε (operator-norm defect ~0.03–0.1, shortfall ~10⁻³–10⁻²) is violated by almost every
  plaquette; the admissible theory at the same lattice spacing needs a very different β (literature: Bietenholz, Jansen, Nagai,
  Necco, Scorzato, Shcheredin, JHEP 03 (2006) 017, topology-conserving actions; memory).

### 2.3 What is assumed

- **Universality of the admissible theory** (same continuum limit as Wilson): standard expectation, used throughout the chiral
  gauge theory literature (Luescher, NPB 549 (1999) 295 for U(1); Hernandez–Jansen–Luescher, NPB 552 (1999) 363 for the ε-bound
  in SU(N); memory). Support: A1 (identical perturbation theory), the RG picture (a local change of the action at the cutoff
  scale), and numerics (Fukaya–Onogi, PRD 68 (2003) 074503, Schwinger model; Bietenholz et al. 2006, r₀ scaling; memory).
  **Not proved** anywhere I know of, and A2 shows it does not follow from rarity.
- Universality of θ-dependence / topological susceptibility in the hard theory (sector weights): assumed in the literature;
  not needed here.

### 2.4 Where the admissible theory sits (heuristic)

- **Hard, small ε**: every plaquette is within ε of 1 at every β, β = 0 included. At β = 0 the measure is uniform on the
  admissible set: fluctuations are bounded by ε at the lattice scale, an effective coupling g_eff² ~ ε. So the hard theory has
  **no strong-coupling end**; the continuum limit is approached as ε → 0 at any β. Our proven strong-coupling windows
  (Prop. 8.1/8.2, `AreaLaw`, `Clustering`) assume a near-product Haar measure at small β and do not apply to it.
- **Soft, fixed η₀ ∈ (0, 1]**: a bounded multiplicative change of the Wilson weight (η₀ ≤ φ/e^{βx} ≤ 1), inside hypothesis
  (Φ) (`posWeight_softAdmissible`, Lean). At small β it is in the strong-coupling windows exactly like Wilson (the windows'
  constants change by the factor η₀); at large β it is Wilson-like. Soft admissibility neither removes large fields nor
  moves the theory.

So neither version shortens the bridge: hard admissibility moves the whole theory to the weak-coupling side; soft
admissibility leaves it where it is.

---

## 3. Large fields are absent only at the cutoff scale (B1, B2)

**Lemma 3.1 (lattice Stokes, one blocking step; Lean `lasso_2x2`).** In any group, for the 2 × 2 square with links h_{ij},
v_{ij} and plaquettes P_{ij} = h_{ij} v_{i+1,j} h_{i,j+1}⁻¹ v_{ij}⁻¹,
the coarse plaquette (h₀₀h₁₀)(v₂₀v₂₁)(h₀₂h₁₂)⁻¹(v₀₀v₀₁)⁻¹ = (h₀₀P₁₀h₀₀⁻¹)·((h₀₀v₁₀)P₁₁(h₀₀v₁₀)⁻¹)·P₀₀·(v₀₀P₀₁v₀₀⁻¹).

**Proposition 3.2 (Lean `defect_coarse_le`, `admissible_coarse`, `unitaryDefect`).** For a defect δ (δ ≥ 0,
δ(gh) ≤ δg + δh, δ(ghg⁻¹) = δh), the coarse plaquette has δ ≤ δP₀₀ + δP₁₀ + δP₁₁ + δP₀₁. On the unitary group of any
C*-ring, δ(U) = ‖1 − U‖ is a defect. Hence ε-admissible fine plaquettes give a 4ε-admissible coarse plaquette, and after k
steps 4^k ε: the bound becomes vacuous after ≈ log₄(2/ε) steps.

**Sharpness (Lean `u1_constant_field`).** In U(1) the constant field strength θ = π/m per plaquette has fine defect ≤ π/m and
the m-fold product is −1 (maximal defect 2). So admissibility at any ε constrains no Wilson loop of side ≳ √(π/ε) (in the
constant-field example the m × m loop has phase m²θ).

(Balaban's blocking averages links instead of multiplying them; on small fields the average differs from the straight product
by the fluctuation, so the same bound holds up to O(ε) corrections. Heuristic, not needed below.)

**What this means for the route.**
1. In physical units admissibility bounds |gF| ≤ ε/a²: a bound that diverges as a → 0. It is a pure UV constraint.
2. Balaban's small-field region at RG step k is a defect below g_k·p(g_k), with p(g) growing slowly (a power of log(1/g);
   Balaban, Dimock's exposition arXiv:1108.1335; memory). For weak coupling g₀p(g₀) ≪ ε, so a **fixed** ε does not remove
   Balaban's large fields even at step 0: admissible ⊋ small field. A g-dependent ε(g) = g p(g) would remove them at step 0
   (with the universality question of §2.2 made worse), but by Proposition 3.2 the coarse fields at step k are then only
   bounded by 4^k g₀p(g₀) ≫ g_k p(g_k): **coarse large fields reappear at every step**, made of coherently aligned small fine
   fields. The large-field problem is scale-recurrent; admissibility removes its k = 0 instance only, the easiest one.
3. The configurations that matter for confinement are of exactly this kind: a **thick centre vortex** of thickness w lattice
   units has plaquette defects ~ π/w², so it is admissible once w ≳ √(π/ε), and physical vortices (w ~ 1/(aΛ) → ∞) are
   admissible. Every fine plaquette is in the small-field region, yet the configuration is far from any pure gauge (large
   loops ≈ −1): it is a large field at the coarse scale of its thickness. Admissibility keeps it (PREP's requirement "the MG3
   twists must be admissible" is met) and therefore cannot simplify its treatment.

---

## 4. (ii) The small-field expansion and the GDS coefficient

At weak coupling and fixed box size the block specification with smooth (e.g. cold) boundary condition concentrates on the
classical minimiser modulo K_V and is Gaussian to leading order: for SU(n), n² − 1 copies of the abelian quadratic form
(colours decouple at leading order). Admissibility (hard or soft) does not change this limit (the minimiser is strictly
inside the admissible set). So the leading-order GDS coefficient is that of the **free abelian Gaussian**, and the question
"can a small-field/one-step analysis give GDS" becomes a computable question about the free field.

### 4.1 The sum rule (C1, C2)

*Gaussian model.* Non-compact U(1), S = ½Σ_{p touching V}(dA)_p², block V, shell values η. The block law is Gaussian with
η-independent covariance and mean r(η) (the classical solution, defined mod K_V). A unit change of the shell link y moves the
mean by r^{(y)}. By alignment (PROOF-NOTE Lemma 3.3/3.4) and Kantorovich duality,
**k_0(y) = min_χ Σ_{e∈V} |r^{(y)}_e + (dχ)_e|** (χ on interior sites), the quotient ℓ¹ norm; its dual is
max ⟨w, r^{(y)}⟩ over currents w with |w_e| ≤ 1 and zero divergence at interior sites.

**Theorem 4.1 (sum rule).** For every block V (any shape), every direction ν: Σ_{y∈∂V, dir y = ν} r^{(y)} = 1_ν (the
indicator of the ν-links of V), and therefore
  **Σ_{y∈∂V, dir y = ν} k_0(y) ≥ #{e ∈ V : dir e = ν}**,   i.e. γ_0 ≥ 1.
Dropping the dangling links (GDS*): Σ_{y non-dangling, dir ν} k_0(y) ≥ #{ν-links} − #{dangling ν-links}, so
γ_0* ≥ 1 − 2(ℓ−1)^{d−1}/(ℓ(ℓ+1)^{d−1}) ≈ 1 − 2/ℓ for thin cubes.

*Proof.* The constant connection A_ν ≡ 1 (all other components 0) on V ∪ ∂V is flat, so it is the classical solution for the
shell data "1 on every ν-shell link"; by linearity this data is Σ_{y dir ν} e_y. Take w = 1_ν: it has zero divergence at every
interior site (one ν-link in, one out) and |w| ≤ 1, so k_0(y) ≥ ⟨1_ν, r^{(y)}⟩. Summing over y gives ⟨1_ν, 1_ν⟩ = #{ν-links}.
For GDS*, a dangling y (outward ν-link at a face-interior site x of a face normal to ν) has r^{(y)} = the gauge rotation at x
(PROOF-NOTE Lemma 3.5), and ⟨1_ν, r^{(y)}⟩ = 1 (one ν-link of V at x); subtract these. ∎
(Checked numerically: max |Σ_y r^{(y)} − 1_ν| ≤ 3·10⁻¹⁵ for (d, ℓ) = (2,4), (3,3), (4,3).)

**Corollary 4.2 (compact groups, weak coupling).** Let G be compact connected with a faithful unitary representation, ρ the
Frobenius distance, and X ≠ 0 in its Lie algebra. For the Wilson, hard- or soft-admissible weight, fixed ℓ, cold boundary
condition, and β → ∞:
  Σ_{y∈∂V, dir ν} k^W_V(y) ≥ (1 − o(1))·#{ν-links of V}.
*Proof (with a stated gap).* The boundary gauge transformation g_x = exp(c X x_ν) moves every ν-shell link by the same
ρ-distance |c|·‖X‖ (bi-invariance) and fixes the rest; by Lemma 3.2 of PROOF-NOTE the block law moves by g. Test with
F = Σ_{lines} ψ(holonomy of the open ν-line across V) (one straight line from face to face through each column; K-invariant;
1-Lipschitz per link since each link is in one line). Telescoping over the shell ν-links (`influence_telescopeW`, Lean)
gives Σ_y k^W(y)·|c|‖X‖ ≥ |E F∘g − E F|. Each line's holonomy W moves to W·exp(−ℓcX). *Gap:* at fixed ℓ and β → ∞ the law
of W concentrates at 1 (finite-dimensional Laplace method around the unique minimiser orbit), so a 1-Lipschitz ψ separates
W from W·exp(−ℓcX) by (1 − o(1))·ℓ|c|‖X‖. Summing over the #lines = #{ν-links}/ℓ lines and letting c → 0 gives the claim. ∎

So **GDS_W fails at weak coupling on every box of fixed lattice size, for every compact connected gauge group, admissible or
not** (γ_W ≥ 1 − o(1); with the numbers of §4.2, γ ≈ 4–6). The H form fails even faster (heuristic: single-link total-variation
distances → 1 as the laws concentrate, so k^H grows with β at fixed ℓ). Photon test: the statement is an
obstruction that holds for U(1) as well, as it must; it claims no reach.

### 4.2 Numbers (C3)

Script `gaussian_gds.py` (k_0(y) per shell link by sparse solve + LP, hypercubic symmetry classes), `full_quotient.py` (the
same modulo the gauge group of all cube sites, boundary sites included: field-strength content only; this is *not* the
coefficient Theorem A uses, PROOF-NOTE §10.2, it is a diagnostic). CPU, one process, seconds to two minutes per size.

| d | ℓ | γ_0 (GDS) | γ_0* (GDS*) | γ_full (field strength only) |
|---|---|---|---|---|
| 2 | 2, 4, 6, 8, 10 | 4.33, 3.49, 3.01, 2.73, 2.54 | 3.33, 2.59, 2.30, 2.15, 2.05 | 0.444, 0.375, 0.356, 0.347, 0.343 |
| 3 | 3, 5, 7, 9, 11 | 5.03, 4.46, 4.00, 3.65, 3.40 | 4.20, 3.57, 3.19, 2.94, 2.77 | 0.872 (ℓ=3), 0.917 (5), 0.947 (7) |
| 4 | 2, 3, 4, 5, 6, 7 | 5.51, 5.78, 5.70, 5.50, 5.27, 5.05 | 5.25, 5.19, 4.94, 4.67, 4.42, 4.21 | 0.984, 1.061, 1.108, 1.142 (ℓ = 2…5) |

Reading:
- γ_0 and γ_0* (the coefficients Theorem A uses) are far above 1 in every dimension and decrease only slowly with ℓ; the sum
  rule (≥ 1) is the floor, the rest is the flux-transport cost of injecting boundary flux (k_0(y) grows linearly in ℓ at edges:
  d = 3 edge outward link k = 4.26, 5.86, 7.32, 8.73, 10.12 for ℓ = 3 … 11).
- The field-strength part separates the dimensions as physics demands: **d = 2** (free U(1) has independent plaquettes: an exact
  gap) γ_full → ≈ 0.34 < 1; **d = 3** (massless) rises towards 1; **d = 4** (massless photon) exceeds 1 from ℓ = 3 on and
  **grows** with ℓ. This is the photon test at the Gaussian level, passed: even an influence that ignored all gauge directions
  would not contract for the free 4D field, and it does for the gapped 2D one.
- Even in d = 2, where the theory has an exact gap, γ_0 ≥ 1: GDS on boxes of fixed lattice size is blind to a gap that is not
  accompanied by disorder of the boundary's imprint (the flux injected by the boundary is conserved in the non-compact
  model). In compact 2D U(1) the flux wraps mod 2π once ℓ² ≫ β (PROOF-NOTE §10.2: influences ∝ t^{ℓ²}), and GDS should hold
  from the scale ℓ ~ √β ~ 1/(a√σ) on (heuristic): the GDS scale is the confinement scale.

### 4.3 Where the non-perturbative input must enter (C4)

- UniformGDS asks for GDS on boxes of side ℓ_k = ⌈L₀/a_k⌉ with β_k → ∞. By C2/C3 this is false for every fixed ℓ at large β;
  at level k the boxes have ℓ_k ≫ β_k (ℓ_k ~ exp(β_k/(4Nb₀))). In that joint limit fixed-order perturbation theory is not
  uniform: an open line across the box has holonomy variance ~ ℓ g² ≫ 1, so its law wraps the group and the sum-rule
  functional loses its grip. This UV disordering (the perimeter self-energy) also happens in U(1): it can remove the sum-rule
  floor, but it cannot make γ < 1 by itself (photon test: in d = 4 the field-strength part γ_full is already > 1 and growing).
- The remaining contraction must come from disorder of the **flux** through the box at the box scale: for SU(2), centre
  vortices of thickness ~ the box (the 't Hooft twist free energy); for U(1)₄ there is none (no monopoles at weak coupling,
  none at all when admissible, §6). This is the root swap of the lead route (PREP) and the twist route (a), in GDS language.
  It is a property of the coarse large fields of §3, at the scale where g(L) ~ 1, and it is absent at every order of the
  small-field expansion (each order is a polynomial correction to the massless Gaussian, with the same sum rule and the same
  growing γ_full).
- Consequently L₀ in UniformGDS must be a non-perturbative length (≳ a few times 1/√σ); boxes of physical size ≪ 1/Λ violate
  GDS. A "direct bound on the GDS coefficient at small coupling inside small boxes" does not exist: there, GDS is false.

### 4.4 One renormalisation step, and why it gives no recursion for κ

What a Balaban small-field step controls (literature, Dimock arXiv:1108.1335 for the structure; memory for the gauge case):
background field U(V) for the block field V, fluctuation integral with a covariance that is massive *in block units* (the
averaging constraint supplies the mass), local effective action, coupling recursion 1/g²_{k+1} = 1/g²_k − 2b₀ log L + O(g²_k),
remainders as polymer activities. In the admissible theory the k = 0 large-field gas is absent; nothing else changes.

This is a recursion for **couplings**, not for the influence. Mapped to GDS: the Gaussian part is a fixed point of blocking
(scale invariant up to the logarithmic running); its GDS coefficient is ≥ 1 by the sum rule at every scale, and its
field-strength part does not decrease with ℓ in d = 4 (§4.2). So the recursion κ(2ℓ) ≤ f(κ(ℓ)) at the Gaussian level has f
marginal or expanding at the free fixed point; corrections of order g²(L) cannot move a coefficient ≥ 1 below 1 while g(L) is
small. A contracting f can only come from the coarse large fields (flux disorder), i.e. exactly from the part of the RG that
Balaban's programme (and `balaban-lean`'s open blockers) cannot control, and that admissibility does not remove (§3).

### 4.5 A bookkeeping remark (H versus W)

PROOF-NOTE §7 states (OS_k) as GDS_W; the Lean `UniformGDS` uses `IsInfluenceBound`, which is the oscillation (H) form. Both
fail at fixed ℓ as β → ∞ (§4.1), the H form faster. Whichever form is kept, the W form (`IsInfluenceBoundW`,
`influence_telescopeW` in `SumRule.lean`) is the one in which the sum rule is sharp and the comparison with the Gaussian is
exact; the reduction's Lean side may want both.

---

## 5. (iii) Topological sectors at small ε

- **Hard admissibility.** Luescher (CMP 85 (1982) 39): for small ε an SU(2) lattice field defines a smooth bundle with integer
  charge, constant on connected components of the admissible set. In a box with fixed admissible boundary, two fillings have an
  integer relative charge (glue them along the boundary). An admissible instanton of size ρ has plaquette defects ~ (a/ρ)²,
  independent of g, so it needs ρ ≳ a·√(c/ε): **boxes with ℓ ≲ ρ_min(ε) ~ ε^{−1/2} hold one sector, larger boxes hold
  several** (heuristic). Single-link moves preserve the relative charge (PROOF-NOTE §9.3, sketch), so by PROOF-NOTE
  Lemma 9.1 k = ∞ in every box with ℓ ≳ ρ_min(ε) whose boundary changes reweight the sectors. Since ℓ_k → ∞, this is the
  generic case: hard admissibility is unusable for GDS (C8 confirmed). The measure itself is fine (a mixture over sectors,
  site RP proven), only local dynamics and single-link seminorms see the walls.
- **U(1) on boxes: no sectors.** With ε < π/3 there are no monopoles (§6), so on a box (simply connected) every admissible
  configuration lifts to a real 1-form A with dA = θ̄; the admissible fillings for a fixed boundary form the convex set
  {A : |(dA)_p + c_p| < ε}, which is connected. Lemma 9.1 does not apply (proved, given E1). On the torus, the sectors are the
  integer fluxes through 2-planes (Luescher 1999, memory).
- **Soft admissibility.** All configurations have positive weight, the single-link seminorms are sups over all pairs
  (admissible or not), and a function that separates "sectors" has per-link oscillation ≥ its jump across an inadmissible
  configuration. So the blow-up of Lemma 9.1 is gone; a sector indicator contributes at most its oscillation (≤ 1) per shell
  link, a surface-order effect O(|∂V|/|V|) = O(1/ℓ) in γ (heuristic: a general test function can mix sector and local
  content; not bounded in general). Soft weights are in (Φ) and RP (`Soft.lean`), so Theorem A, Theorem C and Corollary B
  apply verbatim. But at fixed η₀ soft admissibility is a bounded change of the Wilson weight and does not remove large fields
  (§2.4).
- **Small ε summary.** Hard: sectors frozen, GDS infinite, RG large fields only removed at k = 0. Soft: sectors connected,
  GDS finite, large fields not removed. Neither gives what route (c) needed.

---

## 6. Photon and Z₂ checks

**U(1).**
- *E1 (Lean `no_monopole`).* The DeGrand–Toussaint monopole number of a cube is (1/2π)Σ_{faces} ±θ̄_p ∈ ℤ. If every
  |θ̄_p| < π/3, the six-term sum has modulus < 2π, so it is 0. Admissible U(1) with ε < π/3 has **no monopoles at any β**,
  including β = 0.
- *E2 (heuristic, standard).* Without monopoles, on ℤ^d the field lifts to a real 1-form and the admissible measure is a
  gradient model for 1-forms with a convex constraint (plus the Wilson term): massless (Coulomb phase) at every β, as the
  Villain model without monopoles. So admissible U(1)₄ is massless everywhere, even at β = 0, where Wilson U(1) is confined.
  **Admissibility alone does not make a gap; it removes the U(1) gap.** Any argument "admissibility + small fields ⇒ GDS" that
  does not use non-commutativity proves a reach for admissible U(1) and is wrong.
- Our claims against it: C1/C2 are obstructions and hold for U(1) (consistent); C3 shows γ_full > 1 and growing in d = 4
  (photon), < 1 in d = 2 (gapped), the correct split; B1/B2 are kinematic. No claim here implies a reach for U(1). ✔
- Difference to SU(2): U(1) disorder (monopoles) is quantised at the plaquette scale (integer flux per cube), so a
  plaquette-scale bound kills it; SU(2) disorder relevant for confinement (centre vortices) can be thick and smooth, so the
  same bound keeps it (§3, point 3). This is where non-commutativity (π₁(SO(3)) = Z₂ carried by smooth fields) enters.

**Z₂.**
- *E3 (Lean `z2_softAdmissible_eq_wilson`).* For Z₂ (x = ±1, shortfall 0 or 2) and 0 ≤ ε < 2, the soft weight equals
  √η₀·e^{β'x} with **β' = β + ½ log(1/η₀)**: soft-admissible Z₂ is Wilson Z₂ at a larger coupling, deeper in the deconfined
  (perimeter-law, gapped) phase as η₀ → 0. Hard-admissible Z₂ (ε < 2) forces every plaquette to +1: pure gauge, all Wilson
  loops 1, every admissible configuration isolated under single-link moves (Lemma 9.1 in its most degenerate form).
- So "admissible ⇒ confinement" fails for Z₂ (as it must; Chatterjee's centre route also needs connected G, PROOF-NOTE C6).
  "Admissible ⇒ gap" is consistent with Z₂ (which has a gap at weak coupling) and proves nothing. Our claims make neither
  assertion. ✔

---

## 7. Where route (c) fails, and the most promising next step

**Failure point, precisely.** The route assumed that large fields are what blocks a weak-coupling bound. They are not:
(1) admissibility removes large fields only at the cutoff scale, and coarse large fields (thick vortices) reappear at every
blocking step (Proposition 3.2, sharp); (2) the GDS coefficient is already ≥ 1 in the free Gaussian theory on every box of
fixed size (sum rule, Theorem 4.1, Corollary 4.2), with the field-strength part > 1 and growing in d = 4; (3) the only
mechanisms that can lower it are compactness effects (lines and fluxes across the box wrapping the group), which are absent at
every order of the small-field expansion and are not affected by admissibility. A single Balaban step yields a coupling
recursion, not an influence recursion, and at the free fixed point the influence map is marginal or expanding.

**What survives as useful.**
- Soft admissibility is a legitimate member of hypothesis (Φ), RP-positive, and the Z₂ identity shows it is harmless; it can be
  carried along in any numerics as a variant, with no expected gain.
- The sum rule and the Gaussian table are a reusable **calibration of GDS**: any proposed proof or numerical estimate of a GDS
  coefficient must reproduce γ ≥ 1 − o(1) at fixed ℓ, β → ∞, and must show which wrapping mechanism brings it below 1.
- In the lead route's language: the sum-rule functional is exactly Leg B's "straight lines across the box from face to face";
  the theorem says these lines carry the whole obstruction at weak coupling. Their decorrelation across the box (and of the
  flux through it) is the quantity to bound, not the size of fields.

**Most promising next step (one).** Do the exactly solvable check of the mechanism: **2D compact U(1)** (plaquettes
independent given the boundary, character expansion), compute k^W(y) on thin squares exactly as a function of (ℓ, β) and
locate the crossover from γ ≥ 1 (ℓ² ≪ β, Gaussian, sum rule) to γ < 1 (flux wrapped). If it sits at ℓ ~ c/(a√σ) with
σ the exact 2D string tension, GDS is confirmed to switch on precisely at the confinement scale through flux wrapping, which
fixes what a 4D proof must deliver (the vortex/twist free energy at box size L₀ ~ a few/√σ) and calibrates L₀. It is cheap
(one CPU process, minutes), new, and checkable against the exact solution; the 4D counterpart is route (a)'s twist free energy.

---

## 8. Files

- `NOTE.md` (this note).
- `gaussian_gds.py`: γ_0, γ_0* for thin cubes, Gaussian model (`py gaussian_gds.py d lmax [lmin] [detail]`).
- `full_quotient.py`: γ_full (diagnostic, all-site gauge quotient).
- Lean, `../../../formal/Attempts/Admissible/` (built in WSL `~/formal-att-c`, Lean 4.34, Mathlib v4.34):
  - `Soft.lean`: `softAdmissibleWeight`, `posWeight_softAdmissible`, `plaqWeight_softAdmissible`,
    `z2_softAdmissible_eq_wilson`.
  - `Blocking.lean`: `Defect`, `lasso_2x2`, `defect_coarse_le`, `admissible_coarse`, `unitaryDefect`,
    `u1_constant_field`, `no_monopole`.
  - `SumRule.lean`: `influence_telescope` (H form), `IsInfluenceBoundW`, `influence_telescopeW` (W form).
  Build status: see §9.

## 9. Lean build status

All three files build in WSL `~/formal-att-c` (`sync-build.sh Attempts.Admissible.<Module>`, Lean 4.34, Mathlib v4.34),
"Build completed successfully", no `sorry`, no `axiom`. One harmless linter warning remains in `Soft.lean`
(`bracket_mem`: hypothesis `h0` unused). What is formal: B1 (`lasso_2x2`, `defect_coarse_le`, `admissible_coarse`,
`unitaryDefect`), the sharpness example (`u1_constant_field`), E1 (`no_monopole`), D2/A3-soft (`posWeight_softAdmissible`,
`plaqWeight_softAdmissible`), E3 (`z2_softAdmissible_eq_wilson`), and the telescoping step of C2 (`influence_telescope`,
`influence_telescopeW`). Not formal: the sum rule identity C1 (exact linear algebra, checked numerically), the Laplace
concentration in C2, the numbers C3, and everything marked heuristic.
