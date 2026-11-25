# Round 2, attempt C: H2 through curvature at the strong-coupling scale (2026-11-21)

Question: how far do curvature-type criteria for the one-box bound (H2, `LimitGDS_W`) reach, expressed as a window in the
**effective coupling at L₁**, and where does the physical SU(2) effective theory at L₁ ≈ 3/√σ sit? Inputs: `../RULES.md`,
`../../H2-CURVATURE.md` (W-GDS ⇒ positive coarse curvature; for partitions κ = (1 − γ_♭)/M exactly), `../../followups/` (2D U(1):
the one-box bound switches on at about 3 confinement lengths; SF one-loop running), `../selfcharge/NOTE.md` (curvature swamped at
the lattice scale), `../../../formal/OneScale/Effective/Curvature.lean`, `../../../results/ttl_summary.json`.

Files here: `PREREG.md` (written before running), `criterion_numbers.py`, `criterion_numbers.json`, `run.log`. One CPU process,
3 seconds. No Lean (section 8 says why).

Claim levels: **proved here** (complete argument in this note), **proved modulo** (a named standard fact, recalled), **numerical**
(exact quadrature, `criterion_numbers.json`), **literature, read** (checked in the source this session), **literature, recalled**,
**heuristic / proxy** (a model assumption is named).

---

## 0. Result in one paragraph

The best curvature-type criterion I can state and evaluate is the **single-link W₁ Dobrushin criterion**. For single-link blocks it
is exactly positive coarse Ricci curvature of the single-link heat bath (`H2-CURVATURE.md` 2.4). It beats Bakry–Emery. For an
effective SU(2) Wilson action in d = 4 its window is **proved for β < 0.1243 (α_s > 2.56)**, and it **cannot reach beyond
β = π/16 = 0.196, i.e. α_s = 16/π² = 1.62**. Numerically the window is about β < 0.19. Bakry–Emery (Shen–Zhu–Zhu, equivalently
Otto–Reznikoff by diagonal dominance) gives β < 1/12 (α_s > 3.8) in the same normalisation. **The record's "tiny windows" (SZZ 1/48,
β ≲ 3·10⁻⁵) are a normalisation and counting artefact. In Wilson units the curvature windows are β ≈ 0.08 to 0.2.**

The effective coupling at L₁ is **not one number**. A Wilson action matched to the string tension at L₁√σ = 3 has β = 5·10⁻⁴; one
matched to the glueball mass has β = 0.24. The effective theory is therefore not Wilson-like. The consistent two-coupling proxy
(fundamental coupling from σ, centre-blind adjoint coupling from m₀₊₊) gives β_F ≈ 5·10⁻⁴ and **β_A ≈ 0.50 (0.42 to 0.59)**. The
criterion's window in the adjoint channel is **β_A < 0.29 to 0.39** (linearised).

Gap statement: **H2 (single-link curvature criterion) holds if the adjoint-channel effective coupling at L₁ is below X ≈ 0.29 to
0.39, while the proxy value at L₁ = 3/√σ is Y ≈ 0.50, a factor 1.3 to 2.0 too large. The proxy enters the window at
L₁√σ ≈ 3.3 to 3.9.** The fundamental-only Wilson proxy enters at L₁√σ ≈ 3.0 to 3.4, and Bakry–Emery at 3.9 to 4.4. So the
criterion and the physics meet **at the scale where the round-1 follow-up placed the H1/H2 border** (2D U(1): 2.8 to 3.6
confinement lengths). That is within a factor of 2 in coupling, not orders of magnitude.

The Y side is a strong-coupling proxy whose model error (range and representation content of the true blocked action, choice of
block variable) is **not quantified**, and is likely larger than the factor 2. So the honest verdict is **"X ≈ Y within the proxy;
not decidable without the effective action"**, not "X ≥ Y". As α_s values: the single-link threshold sits at α_s* = 16/π² ≈ 1.6.
The SF coupling extrapolated to L ≈ 3/√σ is α_SF ≳ 1.3 (heuristic). Light's α = 1/137 is a factor 125 below the U(1) threshold
9/π² ≈ 0.91 and never runs into it (photon test passed). Deconfined Z₂ flows away from the window (Z₂ test passed). The proxy
passes the Z₂ test **only because it uses σ > 0**, which is the confinement input H2 needs.

---

## 1. Setting: what the criteria are about

The limiting effective theory `qlim` at scale L₁ (`Effective/Physical.lean`, H1 docstring) lives on block variables of cells of
size L₁. I model it as a **coarse lattice gauge theory with spacing L₁**. Links are V_b ∈ SU(2) (a Balaban-type averaged link,
projected to the group). The action is gauge invariant and short range. Blocks for GDS are single coarse links: the partition
case, with c ≡ 1 and M = number of links. Cost: the geodesic metric ρ on SU(2) = S³ (angle on the unit sphere, diameter π).

By `H2-CURVATURE.md` 2.4, for a partition **κ = (1 − γ_♭)/M exactly**, where γ_♭ is the pointwise W₁ Dobrushin column sum. By 2.2
any W-GDS(γ < 1) gives κ > 0. So "a curvature criterion for H2 at the single-link level" means "a bound on the W₁ sensitivity of
the single-link conditional law to one neighbouring link". Everything below bounds that quantity. Larger blocks (coarse cubes)
are discussed in 2.5.

Wilson normalisation throughout: weight exp(β Σ_p ½ Re tr V_p) for SU(2), so β = 4/g² and **α_s = g²/4π = 1/(πβ)**. Adjoint
term: exp((β_A/3) Σ_p χ_A(V_p)) with χ_A = (tr V)² − 1 ∈ [−1, 3]. In d = 4 each link lies in 6 plaquettes, and has **18
neighbours**, each sharing exactly one plaquette with it.

Single-link conditional. With unit quaternions u (the link) and a_k (the six staples), ½ tr(U S_k) = ⟨u, a_k⟩, and the density on
S³ is

  ρ(u) ∝ exp( Σ_{k=1}^{6} φ(⟨u, a_k⟩) ),   φ(t) = β_F t + (β_A/3)(4t² − 1).

Moving a neighbour link e' by ρ-distance δ moves exactly one staple a_k by the same S³-distance δ (left or right multiplication
is an isometry).

## 2. The criteria and their windows (the X side)

### 2.1 Bakry–Emery = Otto–Reznikoff by diagonal dominance (proved here; SZZ literature, abstract read)

On the unit S³, Ric = 2 (the metric of ρ). For F(u) = φ(⟨u, a⟩) and a tangent X:
Hess F(X, X) = φ''(t)⟨X, a⟩² − φ'(t) t |X|².

- **Single-site curvature.** Hess(−F) ≥ −(β_F + (8/3)β_A)|X|² per plaquette, using ⟨X, a⟩² ≤ (1 − t²)|X|². So the conditional law
  has Bakry–Emery curvature K_e ≥ 2 − 6(β_F + (8/3)β_A).
- **Mixed Hessian.** For two links of one plaquette, |∂_i∂_j F| ≤ |φ'| + |φ''|(1 − t²) ≤ β_F + (10/3)β_A, using
  max(|t| + 1 − t²) = 5/4.

The Otto–Reznikoff criterion (literature, recalled) with diagonal dominance, K_e − Σ_{e'} |∂_e∂_{e'}| > 0, reads

  **24 β_F + 76 β_A < 2**, pure Wilson: **β < 1/12 = 0.0833, α_s > 12/π = 3.82**.

In general d the same count gives 2 − 8(d − 1)β > 0, i.e. β < 1/(4(d − 1)). The SZZ abstract (arXiv:2204.12737, read) states
|β_SZZ| < 1/(16(d − 1)). The two agree exactly if β_Wilson = 4 β_SZZ, i.e. if SZZ's action is N β_SZZ Re tr with N = 2. **The
normalisation is inferred from this match, not read** (the paper body could not be extracted). So the record's "SZZ 1/48 in d = 4"
is **β_Wilson < 1/12**. Bakry–Emery gives an LSI for the Langevin dynamics, and its W₁ influence bounds go through the synchronous
coupling of `H2-CURVATURE.md` §4. The next criterion is better and is directly our object.

### 2.2 Single-link W₁ Dobrushin (coarse Ricci curvature of the heat bath): pure fundamental coupling

The conditional law is the von Mises–Fisher law vMF(A) on S³, A = β Σ_k a_k ∈ ℝ⁴, |A| ≤ 6β. Moving one staple by δ moves A by at
most β δ (chord ≤ arc). Let L(r) be the W₁-Lipschitz constant of A ↦ vMF(A) at |A| = r.

**Theorem 2.2 (window, proved modulo two standard facts).** For β < 0.1243 the single-link W₁ Dobrushin column sum is < 1. Hence
W-GDS with single-link blocks holds, the single-link heat bath has coarse Ricci curvature ≥ (1 − γ)/M, and Theorem A applies.

*Proof.* γ ≤ 18 β sup_{r ≤ 6β} L(r): the segment from A to A' stays in the ball |A| ≤ 6β, so integrate the derivative along it.
For the derivative in a direction δ, the density changes by g = ⟨u, δ⟩ − E⟨u, δ⟩ times ρ, and

  ‖gρ‖_KR ≤ ∫ ρ |∇ψ| ≤ (Var_ρ(g)/λ₁(ρ))^{1/2},   div(ρ∇ψ) = −gρ

(Beckmann's flow bound, then Cauchy–Schwarz and the Poincare inequality). Two standard facts:
- Var_ρ⟨u, δ⟩ ≤ ¼|δ|² for vMF on S³. The covariance eigenvalues are A'(r) and A(r)/r, with A = I₂/I₁ concave and A'(0) = ¼
  (Bessel-ratio facts, recalled). Checked numerically: max 0.2500 over r ∈ [0, 6].
- λ₁(ρ) ≥ max(2 − r, 3e^{−2r}): Bakry–Emery with Ric = 2 and Hess(−r⟨u, n⟩) ≥ −r, or Holley–Stroock from λ₁(S³) = 3.

So L(r) ≤ ½ max(2 − r, 3e^{−2r})^{−1/2}, and 18 β L(6β) < 1 for β < 0.1243 (0.9989 at β = 0.1243, 1.0062 at 0.125). ∎

**Proposition 2.3 (ceiling, proved here).** At a configuration with A = 0 (the six staples cancel, which is possible), the
derivative of the law in any direction is ⟨u, δ⟩·Haar. Its W₁ norm is exactly **8/(9π) = 0.28294**: the 1-Lipschitz test
arcsin⟨u, b⟩ attains it, and it equals the radial 1D transport. So every column entry is ≥ 0.28294 β, and the GDS constant
satisfies **γ ≥ (16/π) β**. The single-link criterion fails for **β ≥ π/16 = 0.19635, α_s ≤ 16/π² = 1.621**.

**Numerical (N4).** The tangential lower bound and the exact radial value of L(r) both decrease in r (0.283 at r = 0, 0.271 and
0.253 at r = 1). This **indicates** sup_r L(r) = L(0), i.e. a true window β < π/16 (not proved: the tangential value is only a
lower bound).

So for this criterion: **proved window [0, 0.124], ceiling 0.196, indicated ≈ 0.196.** That is 2.4 times the Bakry–Emery window.
The pointwise version (γ_♭, i.e. the curvature itself; supremum outside the sum) can only be better. It is not computed: it needs
the 18 neighbours' staple sums to cancel simultaneously.

### 2.3 The adjoint (centre-blind) channel (linearised; numerical)

At small couplings the derivative of the conditional law along one staple is (8β_A/3) h₂·Haar, with
h₂(u) = ⟨u, a⟩⟨u, b⟩, b ⊥ a: a rotating quadrupole. Bounds (N2):
- upper: Poincare/H⁻¹ with Laplace eigenvalue 8, ‖h₂‖_KR ≤ (1/192)^{1/2} = 0.0722;
- lower: the 1-Lipschitz test ½(arcsin|y₁| − arcsin|y₂|), with y the 45°-rotated coordinates, gives ‖h₂‖_KR ≥ 0.0531 (the test
  f = h₂ gives only 1/24).

Linearised column sum: γ ≈ 18[0.2829 β_F + (8/3)‖h₂‖_KR β_A]. Pure adjoint window: **β_A* ∈ [0.289, 0.393]**, i.e. adjoint
character coefficient u_A* = ⟨χ_A⟩/3 ∈ [0.034, 0.046].

Nonlinear check (N3). At the aligned configuration (six equal staples) the per-neighbour coefficient is ≥ 0.073 at β_A = 0.5,
against a linearised 0.071 to 0.096. So linearisation is the right order at the physical point. The supremum over configurations
was not computed. It is a finite optimisation (six staples on S³, one W₁ on S³), suitable for interval arithmetic.

### 2.4 Gauge groups of the unit tests (proved here, same method)

- **U(1):** von Mises conditional; per-neighbour derivative ‖sin‖_KR on the circle = 2/π. Window β_U(1) < π/36 = 0.0873. With
  β = 1/e² and α = e²/4π, that is **α > 9/π² = 0.912**.
- **Z₂** (discrete metric, W₁ = TV): per neighbour ≤ tanh β. Window **β < artanh(1/18) = 0.0556**.

### 2.5 What block criteria could add (heuristic)

The single-link criterion counts **every plaquette as an influence channel**: γ ~ 18 u. The true correlation decay of a
strong-coupling plaquette theory needs a **tube of four plaquettes per step** (m a ≈ −4 ln u). This loss is what places the
threshold at u* ≈ 0.04 to 0.05, where the actual decay is already e^{−12} per link. A block criterion (Dobrushin–Shlosman on
coarse cubes, or block Bakry–Emery with the cube's internal law treated exactly) whose influence scales like N_eff u^p with p > 1
moves the threshold to u* = N_eff^{−1/p} and the entry scale to L₁√σ ≈ (4/p) ln N_eff/(m/√σ): for p = 2 and N_eff ~ 10², to
L₁√σ ≈ 2.5.

This is the improvement to aim for if the single-link criterion falls short. Its cost is a finite computation per block, with no
new idea needed. (Recalled: block criteria are known to extend Dobrushin uniqueness substantially in spin systems; no gauge-theory
numbers recalled.)

## 3. The effective coupling at L₁ (the Y side)

### 3.1 Inputs

- L₁√σ ≈ 3. From the 2D U(1) follow-up: excluded below 2.8 to 3.6 confinement lengths, proved at 8.4 for β = 2. Used as a scan
  L₁√σ ∈ {2, ..., 8.4}.
- m₀₊₊/√σ from our TTL scan (`ttl_summary.json`): 3.44(12), 3.90(18), 3.95(7), 3.73(16), 3.73(19) at β = 2.3 to 2.7. Used:
  **3.75, band 3.5 to 4.0.** a√σ = 0.350, 0.258, 0.182, 0.140, 0.106.

### 3.2 Schroedinger-functional coupling (literature, read; extrapolation heuristic)

Luescher, Sommer, Weisz, Wolff, Nucl. Phys. B389 (1993) 247 (hep-lat/9207010, read via ar5iv): SU(2), ḡ² = 4.765 at L₈ with
**L₈√σ = 0.713 (up to 10 % error)**, and ḡ² = 3.550, 2.840, 2.380 at L/L₈ = ½, ¼, ⅛. So **α_SF = 0.379 at L√σ = 0.71**, β_SF = 0.84.
The step in 1/ḡ² per doubling is 0.068, 0.070, 0.072 (one loop: 0.064), slowly growing. Continuing it for two more doublings
(heuristic; the confining regime accelerates the growth) gives 1/ḡ² ≈ 0.06 at L√σ ≈ 2.85: **α_SF(≈3/√σ) ≳ 1.3, β_SF ≲ 0.25**. The
SF coupling is a free-energy response (the H1-type quantity of the follow-ups), not a coupling of the block specification. It
shows "order-one α at L₁". It is not the criterion's input.

### 3.3 Single-coupling Wilson proxies disagree by a factor 500 (heuristic, leading-order strong coupling)

In a Wilson theory at strong coupling, σa² = −ln u and m₀₊₊ a = −4 ln u with u = I₂(β)/I₁(β) (leading order, recalled). At
a = L₁ = 3/√σ:

| matched to | u | β_Wilson | α_s |
|---|---|---|---|
| σ L₁² = 9 | e^{−9} = 1.2·10⁻⁴ | 4.9·10⁻⁴ | 650 |
| m₀₊₊ L₁ = 11.25 (3.5 to 4.0: 10.5 to 12) | 0.060 (0.050 to 0.072) | 0.24 (0.20 to 0.29) | 1.32 (1.10 to 1.60) |

A Wilson action with a√σ = 3 has m/√σ = 4·3 = 12, against the physical 3.75. **The effective theory at L₁ is not Wilson-like.**
Centre-charged (fundamental) correlations are exponentially suppressed, area e^{−9} per coarse plaquette. The glueball correlations
are much stronger.

### 3.4 The consistent two-coupling proxy (heuristic)

Fundamental plus adjoint plaquette couplings. A pure adjoint action has a local Z₂ symmetry per link, so fundamental loops need
fundamental plaquettes tiling their area: u_F ≈ e^{−σL₁²}. The glueball runs in the centre-blind channel: u_A ≈ e^{−mL₁/4}.
Inverting the exact single-plaquette character coefficients (N5):

| L₁√σ | β_F (from σ) | β_A at m/√σ = 3.5 / 3.75 / 4.0 |
|---|---|---|
| 2 | 7.3·10⁻² | 1.30 / 1.17 / 1.05 |
| 2.5 | 7.7·10⁻³ | 0.88 / 0.77 / 0.67 |
| **3** | **4.9·10⁻⁴** | **0.59 / 0.50 / 0.42** |
| 3.5 | 1.9·10⁻⁵ | 0.40 / 0.32 / 0.26 |
| 4 | 4.5·10⁻⁷ | 0.26 / 0.21 / 0.16 |
| 5 | 5.6·10⁻¹¹ | 0.11 / 0.08 / 0.06 |
| 8.4 | ~10⁻³⁰ | 0.006 / 0.003 / 0.002 |

The naive tree-level equivalent coupling (expanding χ near 1: β_eq = β_F + (8/3)β_A) is 1.33 at L₁√σ = 3, i.e. α_eq = 0.24. This
number is **not** a physical α. An adjoint-dominated action is confining far beyond its naive weak-coupling region, because its
centre (Z₂ monopole/vortex) sector is disordered. α_eq is given only because the owner asked for α values (section 5).

### 3.5 Why the proxy must use σ (the Z₂ trap; proved-by-example reasoning)

Matching to the gap alone would fail the Z₂ test. Deconfined Z₂ has a gap, so an m-only proxy would assign it a small effective
coupling at large L₁ and the criterion would "certify" it. The resolution: in a deconfined (ordered) phase the gap grows with the
coupling (domain-wall cost), and the effective coupling flows to β → ∞. In a confined phase the gap grows as the coupling falls.
Only σ > 0 (area law) puts the effective theory on the strong-coupling branch. **The confinement input is not optional: it is what
makes H2 a confinement-type statement** (the round-2 rule).

## 4. The gap statement

| criterion | window (Wilson units) | as α_s | entry scale L₁√σ of the matched proxy (m/√σ = 3.5 to 4.0) |
|---|---|---|---|
| Bakry–Emery / SZZ / Otto–Reznikoff | β < 1/12 | α > 3.82 | Wilson-m proxy: 3.9 to 4.4 |
| W₁ single-link, proved | β < 0.124 | α > 2.56 | Wilson-m proxy: 3.5 to 4.0 |
| W₁ single-link, ceiling = indicated | β < π/16 = 0.196 | α > 16/π² = 1.62 | Wilson-m proxy: 3.0 to 3.4 |
| W₁ single-link, adjoint channel (linearised) | β_A < 0.29 to 0.39 | α_eq > 0.30 to 0.41 | two-coupling proxy: **3.1 to 3.9** (3.3 to 3.6 at 3.75) |

**Statement.** In the two-coupling proxy, H2 (via the single-link curvature criterion) holds at L₁ if the adjoint-channel effective
coupling is below **X = 0.29 to 0.39** (fundamental below 0.196, irrelevant at L₁√σ ≥ 2.5). The physical proxy value at
**L₁ = 3/√σ is Y = 0.50 (0.42 to 0.59)**: Y/X = 1.3 to 2.0. Since Y falls like e^{−mL₁/4}, **X ≥ Y from L₁√σ ≈ 3.3 to 3.9 on**.
H2 may be posed at any fixed L₁, and larger L₁ only helps the criterion. The cost is that H1 must then carry the flow further.

**Error bars, honestly.**
1. **Model error of the proxy: not quantified, dominant.** The blocked action at L₁ has unknown range and representation content,
   and inverse-MCRG studies (recalled) find several couplings of both signs. More couplings mean more Dobrushin neighbours (X
   shrinks) and possibly a lighter glueball for the same coupling (Y shrinks). Neither sign is known.
2. **Block variable choice.** Straight path products give a product (Haar) limit, which makes H2 vacuous and H1 fail. Heavily
   smoothed variables are correlated across cells by the smoothing. The criterion's input depends on this choice. Inverse
   problem: choose the variable that minimises γ subject to H1.
3. m₀₊₊/√σ ± 0.25 moves the entry scale by ± 0.3.
4. Leading-order strong coupling at u ≈ 0.05: corrections of relative order u in m a, i.e. a few per cent. Small next to 1.
5. Linearisation of the criterion at β_A ≈ 0.4: N3 says the same order. The supremum over configurations is not computed.

**Reading.** Within the proxy X and Y are of the same size, and they cross at the H1/H2 border scale found independently in 2D
U(1). The gap is not orders of magnitude. The record's "curvature windows are tiny" came from SZZ's normalisation, the
TV-and-animal counting of our proven window, and comparing with the bare β ≈ 2.3 instead of the blocked coupling. **Within reach of
a computer-assisted proof is the X side**: for any explicitly given finite-range effective action, the W₁ column sum is a finite
sup-of-integrals computation. **Not within reach is the Y side**: a rigorous effective action at L₁ is the output of H1, which
nobody has.

## 5. α_s reading (the owner's pointer)

- **Threshold.** The single-link criterion bites at **α_s* = 16/π² ≈ 1.6** (fundamental; proved ≥ 2.56 ⇒ certified; ≤ 1.62 ⇒
  never certified by this criterion). For U(1) the same construction gives **α* = 9/π² ≈ 0.91**. The constants are geometric:
  2(d − 1)·3 = 18 neighbours, and the transport constants 8/(9π) on S³ and 2/π on S¹. I see **no deeper α in them**, and claim
  none.
- **Correlation, stated with care.** Every SU(2) scheme in which the criterion's input can be expressed puts the crossing at
  **α_s ≈ 1 to 2**. Wilson-m-matched: Y ≈ 1.3 against X* ≈ 1.6. SF, extrapolated: α_SF(3/√σ) ≳ 1.3. The crossing also sits at the
  H1/H2 border scale. So "L₁ is where α_s reaches order one" and "L₁ is where the curvature criterion can first switch on" are the
  same statement, at the level of these proxies. That is the expected coincidence: the criterion needs a strongly coupled
  effective theory, and α_s ~ 1 is where that begins. It is not an independent numerical match.
- **Light.** α = 1/137 means β_U(1) = 137/(4π) = 10.9. That is 125 times above the U(1) window, and above the 4D compact U(1)
  confinement transition β_c ≈ 1.01 (recalled), i.e. α_c ≈ 0.079. Light sits a factor 11 below the transition, and with no
  running (b₀ = 0) it never moves (section 6).

## 6. Unit tests

- **Photon (4D U(1), weak coupling).** (i) The criterion's U(1) window is α > 0.91, and the photon's α never gets there: no running
  at one loop (`followups` E1.2: Δ = −0.0004 per doubling), and an infrared-free flow in the Coulomb phase. **Not certified at any
  L₁** ✓. (ii) Bakry–Emery is silent for U(1) (Ric = 0). (iii) The proxy side: a massless photon gives u_A ≡ 1 and no σ. The
  matching returns no strong-coupling point ✓. (iv) Consistency: confined compact U(1) (β < 1.01) has a gap and runs to strong
  coupling, so certification there is allowed and correct.
- **Z₂ (H2 is confinement-type; must fail at weak coupling).** The window is β < 0.056, against β > 0.4407 in the deconfined phase
  (self-dual point, recalled). Under blocking, the deconfined effective coupling grows (ordered phase, flows to β = ∞; recalled
  from duality and Migdal–Kadanoff), so it never enters ✓. The m-only proxy **would fail this test**. The σ-input repairs it
  (3.5) ✓. Confined Z₂ (β < 0.44) flows to β = 0 and is certified at large L₁. That is correct: it has an area law.

## 7. Verdicts

| statement | status |
|---|---|
| W₁ single-link criterion window β < 0.1243 (SU(2), d = 4, Wilson) | **proved modulo** two Bessel/Poincare facts (one checked numerically) |
| Its ceiling γ ≥ (16/π)β, so never beyond β = π/16, α_s = 16/π² | **proved here** (exact 8/(9π)) |
| Its true window ≈ π/16 | numerical indication (N4) |
| Bakry–Emery / Otto–Reznikoff: 24β_F + 76β_A < 2; Wilson β < 1/12 = 4·(1/48) | proved here; SZZ normalisation **inferred** |
| Adjoint channel window β_A < 0.29 to 0.39 | linearised, numerical bracket |
| U(1) window α > 9/π², Z₂ window β < artanh(1/18) | proved here (linearised for U(1) at the ceiling) |
| SU(2) SF: α_SF = 0.379 at L√σ = 0.71 | literature, read |
| α_SF(3/√σ) ≳ 1.3 | heuristic extrapolation |
| Effective theory at L₁ not Wilson-like (σ- vs m-matching differ 500×) | heuristic (leading-order strong coupling) |
| Two-coupling proxy β_A ≈ 0.50 at L₁ = 3/√σ, enters window at L₁√σ ≈ 3.3 to 3.9 | **proxy**, model error unquantified |
| m-only matching fails the Z₂ test; σ-input required | proved by the phase argument (heuristic RG flow for Z₂) |

## 8. Lean

Not done. The clean statements here are (a) the ceiling 2.3, which needs the W₁ norm of a signed measure on S³ (transport on
manifolds is not in our framework), and (b) the entry-scale inequality L₁ > 4 ln(1/u*)/m, a one-line monotonicity with no
content. Neither earns a file. The abstract part (single-link GDS ⇒ curvature ⇒ Theorem A) is already in `Curvature.lean`.

## 9. The single most promising next step

**Replace the proxy by a measurement of the effective action's couplings at L₁.** Run a Schwinger–Dyson (inverse Monte Carlo,
"demon") fit of the blocked SU(2) configuration ensemble to a fundamental + adjoint plaquette action (plus rectangles and chairs as
a range test), at L₁√σ ∈ {2, 3, 4}, with smeared cell links as block variables. The SD identities are linear in the couplings, so
the fit is cheap. Its residual measures the model error of section 4, item 1, and turns Y into a number with an error bar.

Cheapest stage: β = 2.0 to 2.1 (a√σ ≈ 0.6), blocks of 5a, lattice 20⁴. That is a GPU job, to be pre-registered and queued behind
Leg B. Then evaluate the criterion constants of section 2 exactly on the fitted action. If the measured couplings sit below X at
some L₁√σ ≤ 4, H2 reduces to a certified finite computation **for that action**, and the remaining gap is H1 (that the true
blocked theory is close to it in the W-influence sense, which is exactly `EffectiveConvergenceW` plus the robustness lemma).

## References

- Shen, Zhu, Zhu, arXiv:2204.12737 (abstract read: conditions |β| < 1/(16(d − 1)) SU(N), (N − 2)/(32(d − 1)N) SO(N)); action
  normalisation inferred (section 2.1).
- Luescher, Sommer, Weisz, Wolff, "Computation of the running coupling in the SU(2) Yang–Mills theory", Nucl. Phys. B389 (1993)
  247, hep-lat/9207010 (read: L₈√σ = 0.713, ḡ² table).
- Otto, Reznikoff, J. Funct. Anal. 243 (2007) (interaction-matrix LSI criterion), recalled. Holley–Stroock perturbation, Bakry–Emery,
  Beckmann's flow formulation of W₁, Bessel-ratio monotonicity/concavity (Amos 1974): recalled.
- Strong-coupling expansions (σa² = −ln u, m₀₊₊a = −4 ln u at leading order; Muenster 1981, Drouffe–Zuber review 1983): recalled.
- 4D compact U(1) transition β ≈ 1.01; 4D Z₂ self-dual point 0.4407: recalled.
- Ollivier 2009; `H2-CURVATURE.md` for the curvature/GDS dictionary.
