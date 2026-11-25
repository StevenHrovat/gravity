# Pre-registration: two cheap follow-ups of attempt round 1 (2026-11-21, before any run)

Source: `../attempts/ROUND-1.md`, "Cheap next experiments", items 1 (route (d)) and 2 (route (c)). Binding resource rules: CPU only,
`CUDA_VISIBLE_DEVICES=-1`, one process at a time, each run a few minutes (hard cap 15 minutes). Both experiments are exact
computations (linear algebra, one-dimensional Fourier integrals) plus, for one upper bound in experiment 2, a small Monte Carlo over
an explicit coupling. No lattice simulation. Scripts and outputs live in this folder.

Notation: σ(β) = −ln(I₁(β)/I₀(β)) (2D U(1) string tension per plaquette); b₀ = 11·2/(48π²) (SU(2)); the predicted one-loop drift
per doubling of the box in SU(2) Wilson units is 8 b₀ ln 2 = 0.2575.

| β | 2 | 4 | 8 | 16 | 32 | 64 |
|---|---|---|---|---|---|---|
| σ | 0.360 | 0.147 | 0.0670 | 0.0323 | 0.0159 | 0.00787 |
| 1/√σ (confinement length, lattice units) | 1.67 | 2.61 | 3.87 | 5.57 | 7.94 | 11.27 |

---

## Experiment 1 (route (d)): does an influence-defined coupling run by the exact asymptotic-freedom rate?

### 1a. What can and cannot be defined (stated before computing)

The lead route's box influence κ(ℓ) is built from the W-form coefficients k^W (PROOF-NOTE §1.6). At weak coupling, on a box of fixed
lattice size, the block law is Gaussian to leading order and k^W tends to the Gaussian (classical-response) value k_0, which does
**not depend on β** (route (c), Corollary 4.2 and table C3). So κ has no g² at tree level, and "g²_κ normalised to g² at tree level"
cannot be defined from κ itself; −log κ is not a coupling. Two cleaner candidates exist:
- the fluctuation-normalised (H-form or Fisher-information) response to a boundary rotation. It is ∝ β at tree level, but its tree
  coefficient is a local sum over boundary plaquettes (lattice-scale), so its one-loop correction is dominated by local constants;
  computing its one-loop part needs the full one-loop self-energy in a box. **Not run** (not cheap; not clean);
- the **free-energy response** of the box to a rotation of its boundary links, Γ'(η) = ∂_η(−ln Z), normalised by its tree value.
  This is the Schroedinger-functional (SF) coupling of Luescher, Narayanan, Weisz, Wolff (literature, memory; its one-loop running is
  known to be universal). It is computable **exactly at one loop** by our own code, in seconds. **This is what is run.**

Prediction (D): if the AF drift lives in a free-energy-type influence, the lead route's recursion must be stated for such a
quantity (or for the O(g²) deviation of κ from its Gaussian value), not for κ. Experiment 1 tests only the running part.

### 1b. Quantity

Lattice L³ × T, T = L, spatial directions periodic, time boundaries at x₀ = 0 and T. Spatial links at x₀ = 0 and x₀ = T are fixed to
the abelian background exp(i φ σ₃ / L) and exp(i φ' σ₃ / L) with φ = η, φ' = π − η (SU(2)); for U(1) the same phases with σ₃ → 1.
The classical solution is V₀ = 1, V_k(x₀) = exp(i θ(x₀) σ₃), θ(x₀) = [x₀ φ' + (T − x₀) φ]/(L T). Wilson action
S = β Σ_p (1 − Re tr U_p / N) (N = 2 for SU(2), β = 4/g₀²; N = 1 for U(1)), all plaquettes with at least one dynamic link,
weight 1 (no boundary improvement, c_t = 1).

  Γ(η) = β s_cl(η) + Γ₁(η) + O(1/β),   Γ₁ = ½ ln det(h + λ D Dᵀ) − ln det(Dᵀ D) (background gauge, ghosts),

with h the Hessian of s = S/β at the background in the coordinates U = e^{X} V, X = Σ_a q^a T_a (T_a = iσ_a/2), D the infinitesimal
gauge map at the sites 0 < x₀ < T (ghosts vanish on the boundaries), λ the gauge parameter. Zero modes that do not depend on η (the
constant neutral A₀ mode at zero spatial momentum) are removed. Influence coupling, normalised to β at tree level:

  β_κ(L) := β · s_cl'(η) / Γ'(η) at η = π/4  =  β − Γ₁'/s_cl' + O(1/β),   Δ(L) := β_κ(2L) − β_κ(L) = −[Γ₁'/s_cl'](2L) + [Γ₁'/s_cl'](L).

At one loop Δ does not depend on β (β = 8 to 64 all give the same Δ up to O(1/β)); the computation is exact at this order.

### 1c. Method and run sizes

Script `sf_oneloop.py`. Hessian of each plaquette from the exact second-order expansion of tr(e^{X₁}V₁ e^{X₂}V₂ V₃⁻¹e^{−X₃} V₄⁻¹e^{−X₄});
stencil built on a 3³ × (T+1) lattice and Fourier transformed in the spatial directions (the background is constant in space), giving
one complex Hermitian block per spatial momentum p = 2πn/L. η-derivative by tr(M⁻¹ ∂_η M) with ∂_η M from central differences
(h = 10⁻⁴). L = T ∈ {2, 3, 4, 6, 8, 12, 16, 24, 32}; groups SU(2) and U(1); λ ∈ {1, 2}.

Checks (must hold, else the run is void and repaired before any reading): gradient of s at the background ≤ 10⁻¹² ; ‖h D‖ ≤ 10⁻¹⁰ ;
h + λDDᵀ positive definite apart from the η-independent zero modes; Γ₁' independent of λ to 10⁻⁸ relative; the momentum-space result
equals a direct real-space computation (sparse, full lattice) for L = 3 and 4 to 10⁻⁸ relative.

### 1d. Expected outcome and criteria

- **E1.1 (SU(2), the test).** Expected: Δ(L) → −0.2575 with lattice corrections O(a/L). Fit Δ(L) = Δ_∞ + d/L over L ∈ {4, 6, 8, 12, 16}.
  **Pass** if |Δ_∞ + 0.2575| ≤ 0.013 (5 %) **and** |Δ(16) + 0.2575| ≤ 0.03. Otherwise **fail**.
- **E1.2 (U(1), the photon test).** Expected: Γ₁' ≠ 0 (compactness, a lattice constant) but no running. **Pass** if |Δ_∞| ≤ 0.01 and
  |Δ(16)| ≤ 0.01.
- **E1.3 (reported).** Δ(2), Δ(3) (smallest boxes, expected far from the asymptote); the constant part of β − β_κ.
- **E1.4 (reported, from experiment 2).** The W-form coefficient's β-independence at weak coupling: γ_lo and γ_hi of experiment 2 at
  fixed small ℓ for β = 10³ and 10⁴ agree to 2 %.

---

## Experiment 2 (route (c)): 2D compact U(1), box influence versus box size

### 2a. Exact structure used (derived before computing)

Thin square V_ℓ (links with both ends in {0..ℓ}²), shell ∂V_ℓ, specification q^η ∝ Π_{p∈P(V)} e^{β cos θ_p}, W-form coefficient k^W
(PROOF-NOTE §1.6) with ρ = arc length on U(1). Modulo the interior gauge group, the box configuration is equivalent to the 4ℓ face
links f_j and the ℓ² inner plaquette angles θ_p, subject to Stokes (Σ θ_p = signed sum of the f_j). Hence:

  **the box law is that of N = ℓ² + 4ℓ independent von Mises(β) angles conditioned on their signed sum ≡ Φ_b (mod 2π)**,

where Φ_b (the total boundary flux) is the only way the shell values η enter. Shell-link types: P (parallel to a face; one outer
plaquette; shifts the centre of one face variable; the two perpendicular corner links act like P at the corner), D (dangling,
perpendicular at a face-interior site s; a boundary gauge rotation at s; shifts the two face variables at s rigidly and oppositely).
The metric on the quotient is: Σ_j |δf_j| plus the earth-mover cost, on the ℓ × ℓ grid of inner plaquettes, of the plaquette changes not
supplied by face-link changes.

Per direction: γ(ℓ, β) = [2 Σ_{i=0}^{ℓ−1} k(P_i) + 2 Σ_{s=1}^{ℓ−1} k(D_s) + 4 k(P_0)] / (ℓ(ℓ+1)), each k the supremum over Φ_b.

### 2b. Bounds computed

- **Lower bound γ_lo (rigorous for k^W, exact numerics).** Test functions F = Σ_γ ψ_γ(Y_γ) over link-disjoint families, where Y_γ is a
  signed sum of link angles with each link used once (1-Lipschitz per link). Each Y is a sum over a subset T of the N variables, so its
  law and its derivative under the shell perturbation are one-dimensional Fourier integrals with coefficients (I_n/I₀)^{|T|}; the best
  ψ gives the circle W₁ rate min_c ∫ |∂_t F_Y − c|. Families: for P_i, the face link f_i alone, every other face link alone, and the
  nested cuts around f_i (Y_r = Σ_{θ in the ℓ¹-ball B_r of the plaquette grid around the plaquette at f_i} − (face links bordering
  B_r), r = 0, 1, ...); for D_s, the three paths ending at s (f_left, f_right, and the shortest path through the inner link at s,
  around one plaquette).
- **Upper bound γ_hi (an explicit coupling, valid at each scanned Φ_b).** D_s: the exact coupling of the two shifted face variables
  given the rest, cost 3 · E_u[W₁ rate of their two-variable conditional law] (≤ 3, the rigid gauge rotation). P_i: a Knothe–
  Rosenblatt flow, variables ordered by decreasing grid distance from the plaquette at f_i (f_i last), each step the optimal 1D circle
  velocity of its conditional law, flux routed to f_i along shortest grid paths (cost Σ_j |dx_j|·(distance_j + [face link])). Its
  expected cost is estimated by Monte Carlo over exact sequential samples (S samples, reported as mean + 2 standard errors, the value
  used for γ_hi).
- Φ_b ∈ {0, π/4, π/2, 3π/4, π}; k = maximum over the scan (the supremum over the continuum of Φ_b is approximated by the scan; stated).
- **Validation:** at β = 10⁴ (Gaussian regime) and ℓ = 2, 3, 4, γ_lo ≤ γ₀ ≤ γ_hi (MC error included) with γ₀ from route (c)'s
  `gaussian_gds.py` (d = 2: 4.33 at ℓ = 2, 3.49 at ℓ = 4), at Φ_b = 0.

Run sizes: β ∈ {2, 4, 8, 16, 32, 64}; ℓ from 2 up to the first ℓ with γ_hi < 1 at three consecutive sizes, capped at ℓ = 48 for γ_lo and
by the runtime rule for γ_hi (upper bound possibly only for β ≤ 32; if so, stated). Monte Carlo S = 200 to 400 per (ℓ, β, i, Φ_b).

### 2c. Expected outcome (heuristic estimate written before computing)

At ℓ² ≪ 1/σ the box is Gaussian: γ ≥ 1 (sum rule). Once the flux wraps, the nested cuts with area ≳ 1/σ stop contributing, so
k(P) ≈ 1 + c₁/√σ (two-dimensional spreading of the injected flux over a half-disc of area ~1/σ) and k(D) ≈ 3; γ ≈ (2k(P) + 2k(D))/ℓ.
Expected crossing ℓ* ≈ 2k(P) + 6, i.e. ℓ*·√σ ≈ 2 to 4 for β = 8 to 64, decreasing towards about 2 as β grows. At small ℓ and
Φ_b ≈ π (a frustrated boundary flux) k(P) may exceed its Gaussian value (two flux sectors compete); expected, reported.

### 2d. Criteria

Define ℓ*_hi(β) = the smallest ℓ from which γ_hi < 1 at all larger computed ℓ, and ℓ*_lo(β) = 1 + the largest ℓ with γ_lo ≥ 1. The true
crossing lies in [ℓ*_lo, ℓ*_hi].
- **E2.1 (mechanism).** For every β ∈ {4, 8, 16, 32} with an upper bound: γ_lo ≥ 1 at ℓ = 2 and γ_hi < 1 at some computed ℓ.
  **Pass / fail.**
- **E2.2 (scale: of order the confinement length).** With ℓ* = ℓ*_hi where available (else ℓ*_lo, said so): **pass** if, over
  β ∈ {8, 16, 32, 64}, (i) 0.5 ≤ ℓ*·√σ ≤ 6 at every β, (ii) ℓ* grows by more than a factor 1.5 from β = 8 to 64 (not a pure surface
  effect), and (iii) ℓ*·σ changes by more than a factor 2 over the same range (not 1/σ scaling). Otherwise **fail**, naming the clause.
- **E2.3 (reported).** The bracket [ℓ*_lo, ℓ*_hi] and ℓ*·√σ per β (the calibration L₀ ≈ c*/√σ); the ratio γ_hi/γ_lo (tightness); the
  Φ_b dependence; the Gaussian validation numbers.

### What the outcomes mean for the plan (written before computing)

- E1.1 pass and E1.2 pass: a free-energy-type box influence carries the exact AF coefficient; route (d) merges with the lead route
  **only if** the lead route's recursion is stated for such a quantity (κ itself has no tree-level coupling, 1a). Fail: the definition
  or the code is wrong (the running of this quantity is established in the literature), to be found before any reading.
- E2.1 and E2.2 pass: in the one exactly solvable confining gauge theory, GDS (W, thin boxes) switches on at a fixed multiple of the
  confinement length, through flux wrapping, and the multiple calibrates L₀. A fail of (ii) or (iii) says the GDS scale is not the
  confinement scale, which would weaken the H1/H2 split (the one-scale certificate would sit at a different length than the physics).

---

## Result (2026-11-21, after all runs; nothing above changed)

Files: `sf_oneloop.py` (+ `sf_oneloop.json`, `sf_oneloop_check.json`), `u1_2d_box.py` (+ `u1_2d_lower.json`, `u1_2d_upper.json`,
`u1_2d_upper_kr1.json`, `u1_2d_validate.json`, `up_b2.log`), `analyse_followups.py` (prints every number below). All runs CPU,
one process at a time, `CUDA_VISIBLE_DEVICES=-1`.

### Deviations from the registered text (stated before the verdicts)

1. **Experiment 1, a slip in the registered definition.** 1b writes β_κ := β·s_cl'/Γ' "= β − Γ₁'/s_cl'". The first expression equals
   1 (not β) at tree level, and the second is not its expansion. The registered intent, stated twice in the same paragraph
   ("normalised to β at tree level"; the SF coupling ḡ² = Γ₀'/Γ'), fixes the definition uniquely: β_κ = 4/ḡ² = Γ'/s_cl' =
   **β + Γ₁'/s_cl'**. The verdict uses this; the sign is not a free choice once β_κ = β at tree level is required. Under the literal
   (inconsistent) expansion every Δ below would change sign and E1.1 would fail. I noticed the slip only when reading the first
   numbers, so this is a correction made after seeing data; it is listed here so the reader can judge it.
2. **Experiment 2, upper bound.** The registered single-level Knothe–Rosenblatt (KR) coupling was run (validation; β = 8, ℓ = 6 and
   12 at Φ_b = 0). It is valid but very loose at moderate β and has heavy Monte Carlo tails (one position at β = 8, ℓ = 12 gave
   k = 449). I added a second coupling of the same kind (KR over the shell sums first, then inside each shell; `upper_P2`), which is
   better behaved, and used it for β = 4 (ℓ = 6, 10, 14, 18, Φ_b = 0 only) and β = 2 (ℓ = 10, 14, 18, Φ_b ∈ {0, π}). The registered
   Φ_b scan (five values) was cut to these for the upper bound by the runtime rule; no upper bound was computed for β ≥ 16 (the sizes
   needed exceed the 15-minute cap). The lower bounds use the full registered scan.
3. Extra sizes in experiment 1 (L = 5, 10, 20) and an extra β (β = 2) for the upper bound: reported, not used in the verdicts
   except where the registered criteria name them.
4. Experiment 1 builds the momentum-space stencil on a 4³ × (T+1) lattice, not 3³ as written in 1c (an assertion checks that no
   coupling reaches beyond one lattice spacing); the real-space cross-check confirms the result either way.

### Experiment 1: free-energy influence coupling, exact one loop

Checks (all hold): gradient at the background ≤ 1.4·10⁻¹⁶; ‖h D‖ ≤ 1.1·10⁻¹⁵; no negative mode; exactly one η-independent zero
mode (the neutral constant A₀ at p = 0); Γ₁' independent of λ (λ = 1 against 2) to 1.5·10⁻¹⁰ relative; momentum space equals the
direct real-space computation for L = 3, 4 (SU(2), U(1)) to 4·10⁻¹¹ relative; the symmetry-reduced momentum sum equals the full sum
(L = 3, 4, 6) to 5·10⁻¹¹.

β_κ − β = Γ₁'/s_cl' (exact at one loop and independent of β; β = 8 to 64 all give the same Δ up to O(1/β)):

| L | 2 | 3 | 4 | 6 | 8 | 12 | 16 | 24 | 32 |
|---|---|---|---|---|---|---|---|---|---|
| SU(2) | −0.9056 | −1.1272 | −1.2520 | −1.4169 | −1.5348 | −1.6993 | −1.8139 | −1.9727 | −2.0838 |
| U(1) | −0.2288 | −0.2293 | −0.2331 | −0.2383 | −0.2411 | −0.2441 | −0.2455 | −0.2470 | −0.2478 |

Δ(L) = β_κ(2L) − β_κ(L) (prediction −0.2575 for SU(2), 0 for U(1)):

| L → 2L | 2 | 3 | 4 | 5 | 6 | 8 | 10 | 12 | 16 |
|---|---|---|---|---|---|---|---|---|---|
| SU(2) | −0.3464 | −0.2897 | −0.2828 | −0.2831 | −0.2824 | −0.2791 | −0.2759 | −0.2734 | −0.2699 |
| U(1) | −0.0043 | −0.0089 | −0.0081 | −0.0068 | −0.0058 | −0.0044 | −0.0036 | −0.0030 | −0.0022 |

- **E1.1 (SU(2)): pass.** Registered fit Δ_∞ + d/L over L ∈ {4, 6, 8, 12, 16}: Δ_∞ = −0.2681 (|Δ_∞ + 0.2575| = 0.0106 ≤ 0.013);
  Δ(16) = −0.2699 (deviation 0.0123 ≤ 0.03). The pass on the fit is narrow and the fit is poor (L = 4, 6 lie on a plateau; max
  residual 0.003). A fit over L ≥ 8 alone (not registered) gives −0.2609 (1.3 % from the prediction). Reading: the approach to
  −0.2575 is slow, with lattice corrections of about 5 % at L = 16 (no O(a) boundary improvement, c_t = 1).
- **E1.2 (U(1)): pass.** Δ_∞ = −0.0004, Δ(16) = −0.0022, falling like 1/L. Compact U(1) has a one-loop correction (the cos
  expansion, a lattice constant ≈ −0.25) but no running.
- **E1.3 (reported).** Δ(2) = −0.346 (35 % off), Δ(3) = −0.290: the smallest boxes are dominated by lattice effects. The constant part
  of β_κ − β is negative and large (−0.9 at L = 2 for SU(2)).
- **E1.4 (reported, from experiment 2): holds.** The W-form coefficient at weak coupling does not depend on β: γ_lo = 4.3333, 3.8571,
  3.4875 (ℓ = 2, 3, 4) at both β = 10³ and 10⁴, γ_hi within 0.04 % of these; they equal route (c)'s Gaussian values per shell-link
  class (2.5000; 3.4762 and 3.2381; 4.4375 and 4.0625; dangling 3.0000). So κ has no tree-level coupling (1a confirmed).

Runtimes: checks 23 s; L = 2 to 16: 41 s; L = 5, 10, 20, 24: 127 s; L = 32: 315 s.

### Experiment 2: 2D compact U(1) box influence

**Validation: pass.** Gaussian regime (β = 10³, 10⁴, Φ_b = 0, ℓ = 2, 3, 4): γ_lo = γ₀ exactly (4.3333, 3.8571, 3.4875 against
`gaussian_gds.py`), γ_hi above by at most 0.0015 (Monte Carlo). Both bounds are exact in this limit, per link class.

**Lower bound γ_lo (rigorous for k^W; supremum over the Φ_b scan):**

| β | 1/√σ | γ_lo at ℓ = 2 (at Φ_b = 0) | ℓ*_lo | ℓ*_lo·√σ | ℓ*_lo·σ | k_lo(P) middle / corner (large ℓ) | (k_mid − 1)·√σ | k_lo(D) |
|---|---|---|---|---|---|---|---|---|
| 2 | 1.67 | 2.74 (2.68) | 7 | 4.20 | 2.52 | 1.58 / 1.40 | 0.35 | 2.32 |
| 4 | 2.61 | 5.76 (4.08) | 11 | 4.21 | 1.61 | 2.57 / 2.61 | 0.60 | 2.88 |
| 8 | 3.87 | 11.25 (4.32) | 14 | 3.62 | 0.94 | 3.77 / 4.24 | 0.72 | 2.99 |
| 16 | 5.57 | 21.6 (4.33) | 18 | 3.23 | 0.58 | 5.45 / 6.56 | 0.80 | 3.00 |
| 32 | 7.94 | 42.0 (4.33) | 24 | 3.02 | 0.38 | 7.84 / 9.91 | 0.86 | 3.00 |
| 64 | 11.27 | 82.5 (4.33) | 32 | 2.84 | 0.25 | 11.25 / 14.69 | 0.91 | 3.00 |

(ℓ*_lo = 1 + the largest ℓ with γ_lo ≥ 1; γ_lo decreases monotonically in ℓ at every β.) Two structural findings:
- **Saturation (flux wrapping).** k_lo(P) stops growing once ℓ ≳ 2/√σ and saturates at ≈ 1 + c/√σ, with c rising to 0.91 at
  β = 64 (the half-disc estimate in 2c gave √π/2 = 0.886). A boundary link's influence reaches a region of area ~1/σ and no further;
  in the Gaussian (non-compact) model it grows with ℓ instead. With k(P) and k(D) bounded, γ ≈ (2k(P) + 2k(D))/ℓ falls like 1/ℓ.
- **Frustrated boundary flux.** At small ℓ the supremum over boundary conditions is set by Φ_b = π (half a flux quantum): k(P) at
  ℓ = 2 grows like ≈ 0.95β (two flux sectors compete, and one boundary link tips them). At Φ_b = 0 the same box gives the Gaussian
  4.33. The effect is gone once the box wraps (β = 64, ℓ = 32: 0.9691 against 0.9689 at Φ_b = 0).

**Upper bound γ_hi (explicit couplings; Φ_b as listed in deviation 2):**

| β | ℓ | γ_hi | k_hi(P) range | γ_lo at the same ℓ | runtime |
|---|---|---|---|---|---|
| 8 (KR, registered) | 6 / 12 | 4.62 / 13.7 | 7.2–14.2 / 9.9–449 | 2.33 / 1.13 | 115 s (both) |
| 4 (KR2, Φ_b = 0) | 6 / 10 / 14 / 18 | 5.35 / 2.41 / 2.03 / 1.65 | 5.9–22.4 | 1.67 / 1.03 / 0.75 / 0.59 | 444 s |
| 2 (KR2, Φ_b ∈ {0, π}) | 10 / 14 / 18 | 1.52 / **0.987** / **0.815** | 3.8–5.8 | 0.71 / 0.52 / 0.41 | 696 s |

The couplings overestimate k(P) by a factor of about 3 (β = 2) to 3–6 (β = 4), with heavy Monte Carlo tails: the bracket is wide.
At β = 2 the coupling proves the one-box bound for ℓ = 14 and 18 at the two scanned fluxes (GDS with γ ≤ 0.99 and 0.82; ℓ = 14 is
8.4 confinement lengths), where the lower bound already allows it from ℓ = 7.

**Verdicts.**
- **E2.1: fail.** γ_lo ≥ 1 at ℓ = 2 holds at every β, but for the registered β ∈ {4, 8, 16, 32} no computed ℓ gives γ_hi < 1 (β = 4:
  1.65 at ℓ = 18, the largest size within the runtime rule; β = 8: two sizes only; β ≥ 16: no upper bound). Cause: the explicit
  couplings are too loose, not a sign against the mechanism (β = 2, outside the registered set, does reach γ_hi < 1). The mechanism
  is therefore established only through the lower bound plus β = 2.
- **E2.2: pass, on ℓ*_lo** (no ℓ*_hi exists for β ≥ 8, and the rule then says use ℓ*_lo): (i) ℓ*·√σ = 3.62, 3.23, 3.02, 2.84 for
  β = 8, 16, 32, 64, inside [0.5, 6]; (ii) ℓ* grows from 14 to 32 (factor 2.3 > 1.5); (iii) ℓ*·σ falls from 0.94 to 0.25 (factor 3.7
  > 2). The pre-registered expectation (ℓ*√σ ≈ 2 to 4, decreasing towards about 2) matches the trend, still above 2 at β = 64.
  Caveat: ℓ*_lo is the smallest box at which the rigorous lower bound no longer excludes GDS; the true crossing can be larger (by up
  to the factor between the bounds, about 2 at β = 2).
- **E2.3 (reported).** Calibration from the lower bound: L₀ ≳ 2.8 to 3.6 confinement lengths (1/√σ), slowly decreasing with β; from
  the upper bound at β = 2: L₀ ≤ 8.4/√σ. Tightness γ_hi/γ_lo ≈ 2 (β = 2) to 3 (β = 4). Φ_b dependence as above.

Runtimes: validation 203 s; lower bounds 59 s (β = 2, 4, 8) and 67 s (β = 16, 32, 64), ℓ = 2 to 48; upper bounds as in the table;
diagnostics about 1.5 minutes.

### What the results mean for the plan (H1/H2 split, lead route, curvature reading)

- **Experiment 1 and H1 (the quantum half).** The box's free-energy response to a boundary rotation carries the exact one-loop
  asymptotic-freedom coefficient (to the precision reachable at L ≤ 32), and U(1) carries none; the W-form box influence κ carries
  no coupling at all at tree level (E1.4). So the running that H1 must control, from where the OpenAI-type construction stops
  (g² ≈ 10⁻⁶) up to L₁, is visible to a free-energy (Schroedinger-functional-type) influence and invisible to κ. For the
  sharp-coefficient lemma this is good news in one form only: a per-doubling recursion with the exact coefficient exists for an
  SF-type coupling (the step-scaling function of the lattice literature, memory), not for κ. Route (d) merges with the lead route as
  "SF-type coupling recursion up to L₁ (H1), then κ at L₁ (H2)"; a recursion stated for κ itself below L₁ sits at the photon fixed
  point at leading order and cannot carry the running.
- **Experiment 2 and H2 (the classical half, positive coarse curvature).** In the one exactly solvable confining gauge theory the
  W-form one-box bound (equivalently, contraction of the block dynamics in Wasserstein distance) is excluded below about 3
  confinement lengths and not excluded above; at β = 2 it is proved at 8.4 confinement lengths. The switch is caused by flux
  wrapping: a boundary link's influence saturates at a reach of area ~1/σ, after which the box's own volume wins (γ ~ 1/ℓ). In the
  curvature language: the effective block dynamics acquires positive coarse curvature only at block sizes of a few confinement
  lengths, which calibrates L₁ ≈ 3/√σ (2D U(1)), consistent with the PREP reading "the first opportunity is the length where the flux
  cost reaches one quantum". Two cautions for 4D: (1) in 2D U(1) the plaquettes are independent, so wrapping is the only effect; in
  4D the same saturation of k(P) must come from flux disorder (centre vortices for SU(2)), and 4D U(1) has none (photon); (2) the
  worst-case boundary for a box is a frustrated flux (half a quantum), whose influence grows like β in small boxes; any H2
  certificate must handle these boundaries, and they become harmless only once the box wraps. That is the per-box form of the
  "worst boundary" issue of `H2-CURVATURE.md`.
