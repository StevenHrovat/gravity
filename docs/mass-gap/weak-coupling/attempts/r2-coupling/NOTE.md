# Round 2, attempt B: a reflection-positive coupling of two replicas (2026-11-21)

Status: mathematics plus two Lean files (`../../../formal/Attempts/R2/CouplingSwap.lean`, `CouplingSplit.lean`, both build clean
in `~/formal-att-b`, no `sorry`). Claim levels as in `../RULES.md` 3: **proved**, **proved modulo** (a named standard result),
**heuristic**, **conjecture**. "Lead" refers to `../lead/NOTE.md` (Theorem R, §2.3; the construction problem, §2.4 and §6),
"Pos" to `../positivity/NOTE.md`.

Conventions: Wilson weight φ(U_p) = e^{β Re tr U_p} as in the Lean files (`xp` = Re tr), so for SU(n) φ_max/φ_min = e^{2nβ} and
β = 2/g² (β_std = nβ); for U(1) β = 1/e² = 1/(4πα). Two replicas U, U' on the same torus; μ the Wilson measure; f, g bounded with
link supports T_f, T_g.

---

## 0. Results at a glance

| # | statement | level |
|---|---|---|
| G | **Swap identity for any coupling.** If ν couples μ with itself and S is a ν-preserving involution that, on an S-invariant event E, exchanges f between the replicas and leaves g in place, then Cov_μ(f,g) = CrossCov_ν(f,g) ± 2‖f‖‖g‖ν(Eᶜ), CrossCov_ν the symmetrised E_ν[f(U)g(U')] − E f E g. For independent replicas CrossCov = 0 | **proved**; product case **Lean** (`swap_cov_bound`) |
| A | **Agreement transfers the covariance.** In any coupling, \|E_ν[f(U')g(U)] − E_μ[fg]\| ≤ 2‖f‖‖g‖ν(f(U') ≠ f(U)). A coupling that agrees on T_f with high probability carries Cov_μ(f,g) in its cross term: the decorrelation must come from independence, not from the coupling | **proved, Lean** (`cross_transfer`) |
| N | **The brief's candidates.** Maximal / diagonal couplings, shared-field couplings (shared region, Nummelin split, shared Hubbard–Stratonovich field), dynamic Doeblin couplings, centre-symmetric couplings, Schroedinger-bridge reweightings: each one either has zero agreement for a continuous group, or carries Cov_μ in its cross term (by A), or loses reflection positivity through a non-local normaliser. Exact statements in §2 | **proved** case by case (RP failures: "no proof, non-local factor", not disproved) |
| S | **The soft swap (the construction).** Independent replicas plus one label t_p ∈ {0,1} per plaquette with weights κ_p = min over the 2⁴ link mixings of φ(U_p)φ(U'_p) and W_p − κ_p. Exact marginals (μ⊗μ), CrossCov ≡ 0, reflection positive, and any partial swap whose cut plaquettes all carry t = 0 is measure preserving. No agreement is needed, so it works for **every compact group** (SU(2), U(1), Z₂) at every β with positive probability | marginals, invariance **proved, Lean** (`splitW_*`); RP **proved modulo** the instantiation of `rp_abstract` (not formal) |
| S-decay | Torus decay from S: \|Cov_μ(f,g)\| ≤ 2‖f‖‖g‖·\|T_f\|·(2(d−1)/(4(2d−3)))·(4(2d−3)δ)^r/(1 − 4(2d−3)δ), δ = 1 − (φ_min/φ_max)², r = distance. Window d = 4: 20δ < 1, i.e. β < ln(20/19)/(4n): **SU(2) β < 0.0064, U(1) and Z₂ β < 0.0128**. Uniform in the torus size, no RP needed; a chessboard version (modulo FILS) replaces δ by a disseminated active probability | **proved** (deterministic version) / **proved modulo** FILS (chessboard version) |
| O | **Optimality.** No construction (any auxiliary variables) can make a given swap admissible with probability above 1 − TV(ν, S_*ν); the split attains it term by term | **proved, Lean** (`admissible_le_overlap`, `overlap_eq`) |
| W1 | **Unaligned swaps at weak coupling.** P(t_p = 0) ≤ J(2β)·(Z_{−p}/Z)² with J(s) = ∫e^{s Re tr h}dh (exact); with the standard small-fluctuation energy bound this is O(β^{−3/2}) for SU(2), O(β^{−1/2}) for U(1), ≈ 1/2 for Z₂ | inequality **proved**; asymptotics **heuristic** (energy bound for the measure with p removed not reproved) |
| W2 | **Aligned swaps at weak coupling.** For two independent Gaussian replicas, the best admissible probability of swapping a region D lies in [e^{−2I}/2, e^{−I}], I = mutual information between the field in D and outside (exact identity BC = e^{−I}). At leading order in g² this is β-independent, has an area law, and is **the same for SU(2) and U(1)³** | identity **proved**; area law and the SU(2) ≈ U(1)³ transfer **heuristic** |
| V | **Verdict for SU(2) at weak coupling.** The construction problem of Lead §2.4 is solved in its structural form (S), but every swap argument run on the lattice measure is decided at the lattice scale, where SU(2) cannot be told from three photons: no window at weak coupling. The swap has to act on an effective theory at the scale L₁ where it is strongly coupled; there S gives torus decay from a local, H2-type criterion | **proved** for the parts above; the conclusion is a **heuristic** reading (photon structure, as Lead D3) |

**Bottom line.** The question "is there a reflection-positive coupling of two SU(2) replicas, with exact marginals, in which a swap
argument runs with positive probability?" has a positive answer (S), and the answer is better than asked: exact agreement is not
needed, only that the cut plaquettes carry the mixing-invariant part of their weight. But the probability of that is fixed by the
ultraviolet: swapping two independent replicas across any surface of the lattice costs the mutual information of the lattice field
across it, which at weak coupling is β-independent and identical for SU(2) and U(1)³. So the soft swap is a strong-coupling (disorder)
mechanism, the companion of Theorem R's ordered (agreement) mechanism, and neither covers weak-coupling SU(2) on the lattice. Every
attempt to raise the agreement by correlating the replicas pays it back in the cross term (A). The usable output is a clean torus-decay
engine for a strongly coupled effective theory at L₁ (§3.4), which moves the problem to the H1/H2 split rather than solving it.

---

## 1. What a swap argument needs, and where decorrelation comes from

### 1.1 The four ingredients

Theorem R (Lead §2.3) uses: (M) a coupling ν of μ with itself; (I) the cross term E_ν[f(U)g(U')] = E f · E g (independence);
(S) a ν-preserving involution that swaps the replicas on a random region D around T_f, measure preserving on an event E that depends
only on variables the swap does not change; (P) a Peierls bound on ν(Eᶜ), via chessboard (needs reflection positivity of ν) or
directly. Agreement of the two replicas enters only through (S): it is one way to make the swap measure preserving.

### 1.2 Theorem G (swap identity, any coupling)

Let H = (f(U) − f(U'))(g(U) − g(U')). On E, H∘S = −H; S preserves ν and E, so ∫_E H dν = 0, and |∫_{Eᶜ} H dν| ≤ 4‖f‖‖g‖ν(Eᶜ). For
any coupling, ∫H dν = 2E_μ[fg] − E_ν[f(U)g(U')] − E_ν[f(U')g(U)]. Hence

  |Cov_μ(f,g) − CrossCov^{sym}_ν(f,g)| ≤ 2‖f‖‖g‖ν(Eᶜ),   CrossCov^{sym} = ½(E_ν[f(U)g(U')] + E_ν[f(U')g(U)]) − E f E g.

For independent replicas CrossCov ≡ 0 and this is |Cov_μ(f,g)| ≤ 2‖f‖‖g‖ν(Eᶜ). **Proved.** The product case, with an auxiliary
label space T and replica marginal μ⊗μ, is `Attempts.R2.swap_cov_bound` (with `replica_identity`: E_{μ⊗μ}[H] = 2Cov_μ(f,g), and
`setIntegral_eq_zero_of_antisymm`).

### 1.3 Lemma A (agreement transfers the covariance)

For any coupling ν with first marginal μ: E_ν[f(U')g(U)] − E_μ[f g] = E_ν[(f(U') − f(U))g(U)], which vanishes off {f(U') ≠ f(U)}.
So |E_ν[f(U')g(U)] − E_μ[fg]| ≤ 2‖f‖‖g‖ν(f(U') ≠ f(U)). **Proved, Lean** (`cross_transfer`).

**Consequence.** If a coupling agrees on T_f with probability ≥ 1 − ε (Theorem R needs this per block: by chessboard
ν(block bad) ≤ z), then CrossCov_ν(f,g) = Cov_μ(f,g) up to 2‖f‖‖g‖ε. The decay of the cross term is then the decay of μ itself, up
to an error that does not decay with distance. Theorem G turns this into nothing: it trades Cov_μ for CrossCov. **The only source of
"free" decorrelation is (I), independence**, and for independent replicas of a continuous group exact agreement has probability 0
(the conditional laws are atomless; Lead §2.3 tests). This is the precise form of the dilemma behind Lead's "wrong marginal or
non-local factor": correlating the replicas to make them agree imports Cov_μ into the cross term; keeping them independent forbids
agreement. §3 escapes it by keeping (I) and replacing agreement in (S).

---

## 2. The brief's candidates, one by one

For each: marginals, RP, agreement / admissibility, cross term, photon and Z₂ behaviour.

### 2.1 Maximal couplings and mixtures

- The maximal coupling of μ with itself is the diagonal U' = U: agreement 1, RP (it is μ on the diagonal), swap trivial, and
  CrossCov = Cov_μ: Theorem G is the tautology Cov = Cov. **Proved.**
- Mixtures ν_s = (1 − s)·diagonal + s·(μ⊗μ): exact marginals, RP (convex combination of RP measures), CrossCov = (1 − s)Cov_μ. The
  disseminated bad probability is z ≥ s^{1/R^d} → 1 (one global coin makes every block bad at once). So the chessboard sees no gain:
  the agreement must come from *local* randomness. **Proved.**
- The maximal coupling of two *conditional* laws (different boundary data) is disagreement percolation; it needs worst-case
  boundaries, the C2 obstruction (Lead §2.2).

### 2.2 Shared-field couplings (conditionally independent replicas)

ν = ∫P(dξ) μ_ξ⊗μ_ξ for a representation μ = ∫P(dξ)μ_ξ.

- **Covariance split** (proved): Cov_μ(f,g) = Cov_P(μ_ξ f, μ_ξ g) + E_P[Cov_{μ_ξ}(f,g)], and CrossCov_ν = Cov_P(μ_ξ f, μ_ξ g). Swap
  arguments can only remove the second term.
- **Atom lemma** (proved): ν(ω_b = ω'_b) = E_P[Σ_x μ_ξ(ω_b = x)²] ≤ E_P[max_x μ_ξ(ω_b = x)]. Exact agreement on a block needs atoms
  in the conditional law, i.e. ξ must determine the block's field with probability ≥ 1 − z. Then ξ is a (1 − z)-faithful copy of the
  gauge field and Cov_P(μ_ξ f, μ_ξ g) is Cov_μ up to O(z) (Lemma A).
- **Shared-region resampling (static Nummelin split).** Draw a random block set R independently (density 1 − q), set U' = U on R and
  resample U' on Rᶜ from μ(· | U_R), independently of U. Exact marginals; agreement on R exactly, so the bad density is q and can be
  made as small as one likes; the swap on any union of components of Rᶜ is measure preserving (Markov property). But CrossCov =
  Cov_μ − E[Cov(f,g | U_R)], and Theorem G reduces to "f and g are conditionally independent given a separating U_R": **the Markov
  property, a tautology.** RP: the conditional normalisers 1/Z(Rᶜ-component | U on its boundary) are non-local across a reflection
  plane; no proof of RP (this is Lead's "quenched" factor). **Proved** (except RP: open, not needed since R is independent).
- **Shared Hubbard–Stratonovich field.** For SU(2) (unit quaternions, Re tr(XY⁻¹) = 2x·y), with U_p = XY⁻¹, X = U₁U₂, Y = U₄U₃:
  e^{2βx·y} = e^{−2β}E_Z[e^{√(2β)Z·x}e^{√(2β)Z·y}] (Z standard Gaussian in ℝ⁴). Each half-factor is bilinear in its two links:
  Z·(u₁u₂) = u₁·L_Z u₂ with L_Z u = Z ū linear, |L_Z u| = |Z|; a second Gaussian layer, e^{c u₁·Lu₂} = e^{−c(1+|Z|²)/2}
  E_W[e^{√c W·(u₁ + Lu₂)}], linearises it. So **μ = ∫P(dξ)∏_ℓ vMF_{a_ℓ(ξ)}(dU_ℓ)** exactly (ξ = all Gaussians; von Mises–Fisher
  laws on S³), and the same for U(1) with ℝ². The conditional law is a product, so the quenched normaliser ∏_ℓ Z_vMF(a_ℓ(ξ)) is
  **local**: the conditionally independent duplicate is a local Gibbs measure on (ξ, U, U'), RP for a reflection whose split choices are
  mirrored (an equivariant choice for all planes at once was not checked). This removes Lead's non-local-factor problem, and shows why
  it does not help: vMF laws are atomless (agreement 0), and for disjoint supports **Cov_μ(f,g) = Cov_P(μ_ξ f, μ_ξ g) exactly**: the
  auxiliary field is precisely as long-ranged as the gauge field (for U(1) massless, conditional on FS). An exact rewrite, no gain.
  **Proved.**

### 2.3 Dynamic Doeblin / Nummelin couplings

The single-link heat-bath law has density ∝ e^{β Re tr(U_ℓ Σ)} (Σ the 2(d−1) staples), so it is ≥ ε·Haar with
ε = e^{−4(d−1)nβ} (SU(2), d = 4: e^{−24β}). Coupled heat baths with a shared Doeblin coin and Haar draw:
- with shared remainder too, the pair chain coalesces and its stationary law is the diagonal (2.1);
- with independent remainder, a link agrees iff its last update was a Doeblin draw: probability ε per link, so a block agrees with
  probability ≈ ε^{|V|}; at weak coupling z ≈ 1. CrossCov ≠ 0 (shared draws), and the stationary law of a coupled, non-reversible pair
  chain is not a local Gibbs measure: no RP known.
Photon: vacuous for U(1) at weak coupling (passes). This is Dobrushin-type high-temperature technology. **Proved** (the RP part:
"no proof").

### 2.4 Centre-symmetric couplings

If U'_ℓ = z_ℓ U_ℓ with central z_ℓ (any joint law: centre transformations, twists, the SO(3) × Z₂ split with shared SO(3) part), then
every adjoint-only observable (adjoint loops, |tr U_p|², glueball operators) takes the same value in both replicas
(`Attempts.Positivity.AdjointOnly.centre_invariant`), so CrossCov = Cov_μ **exactly** on the neutral channel. Such couplings can
decorrelate only centre-charged observables (confinement), not the gap channel. **Proved** (this is Lead §2.4's channel limitation as
a statement about couplings).

### 2.5 Common dominating measures and Schroedinger bridges

A coupling of the form ν = a(U)a(U')λ(dU, dU') with an RP reference λ (the entropic, Schroedinger-bridge coupling with marginals μ)
is RP if a is a product of local reflection-covariant factors. The Sinkhorn potential a = dμ/d(∫a λ) is local only when λ's
conditional law is a product (as in 2.2's HS case, then no agreement) or trivial. The annealed coupled replica of Lead §2.4 is the
case a ≡ 1 (wrong marginal), the quenched one the case a = 1/Z_V (non-local). **Heuristic** as a general statement; the two extreme
cases are proved in Lead.

---

## 3. The soft swap: independence kept, agreement replaced

### 3.1 Construction

Replicas U, U' independent, ν₀ = μ⊗μ, density ∝ ∏_p W_p with W_p = φ(U_p)φ(U'_p). For a plaquette p, the mixing group
M_p = (ℤ₂)^{∂p} acts on the pair (U, U') restricted to the four links of p by exchanging chosen links between the replicas. Put

  κ_p = min_{m ∈ M_p} W_p(m·(U,U')),   ν̂(t, U, U') ∝ ∏_p [κ_p if t_p = 0;  W_p − κ_p if t_p = 1].

Proved facts (Lean `CouplingSplit.lean`: `orbitMin_smul`, `splitW_nonneg`, `splitW_sum`, `splitW_false_inv`, `splitW_true_inv`):
1. both weights are ≥ 0 and sum to W_p, so the (U, U') marginal of ν̂ is exactly μ⊗μ (marginals exact, CrossCov ≡ 0);
2. κ_p is invariant under every mixing of p's links; W_p − κ_p under the full swap of p;
3. given (U, U'), the labels are independent with P(t_p = 0 | U, U') = κ_p/W_p ≥ (φ_min/φ_max)² (`orbitMin_ratio`).

**The swap.** Call links t-connected if they share a plaquette with t_p = 1, and let D(t) be the union of the t-clusters of the links
of T_f. S swaps U and U' on D(t) and keeps t. For each fixed t this is a permutation of Haar coordinates; a plaquette with t_p = 1
has all its links in D or none (fully swapped or untouched: weight invariant by 2), a plaquette with t_p = 0 is mixed arbitrarily
(weight κ_p invariant by 2). D depends only on t, so S is a ν̂-preserving involution and E = {D(t) ∩ T_g = ∅} is S-invariant. On E,
f moves to the other replica and g stays. These are exactly the hypotheses of `swap_cov_bound`.

Nothing here uses agreement, gauge fixing, plaquette variables or the torus topology (links are the coordinates; Theorem R's
exactness discussion does not arise). f and g need not be gauge invariant.

### 3.2 Theorem S (torus decay from the soft swap)

For any compact group, any class-function weight φ ≥ 0 with φ(g⁻¹) = φ(g), any finite torus, and f, g at link distance r:

  |Cov_μ(f,g)| ≤ 2‖f‖‖g‖ · ν̂(T_f ↔ T_g through active plaquettes) ≤ 2‖f‖‖g‖ · |T_f| · (2(d−1)/K) · (Kδ)^r / (1 − Kδ),

K = 4(2d − 3), δ = 1 − (φ_min/φ_max)². *Proof.* Theorem G; a connection needs a chain of r distinct active plaquettes starting at a
link of T_f, consecutive ones sharing a link (each plaquette moves link midpoints by ≤ 1); there are ≤ 2(d−1)K^{k−1} chains of length k
per starting link, and by 3 and conditional independence P(all k active) ≤ δ^k. ∎ **Proved.**

Window (d = 4, K = 20): 20(1 − e^{−4nβ}) < 1, i.e. **β < ln(20/19)/(4n)**: SU(2) β < 0.00641 (g² > 312), U(1) β < 0.0128
(e² > 78), Z₂ β < 0.0128. Mass in lattice units ≥ log(1/(20δ)). This re-proves the known strong-coupling gap (Osterwalder–Seiler) by a
new route, for every compact group at once; the constants are not competitive and were not optimised.

### 3.3 Reflection positivity and the chessboard version

ν̂ is a local Gibbs measure on (t, U, U') with one factor per plaquette. For a site reflection every plaquette lies in one closed half,
the reflection maps the mixing group of p onto that of θp, and Re tr is invariant under inversion, so the factor of θp at the reflected
configuration equals the factor of p: the weight has the form w(a, c)w(θb, c)v(c) and ν̂ is RP by the abstract lemma
(`Positivity.rp_abstract`, with the labels added to the half-space coordinates). **Proved modulo** the instantiation (not formal), the
same way as Lead C1₂. Hence the chessboard bound (FILS, modulo) applies: with z̃ the disseminated probability of "the block contains
an active plaquette", P(chain of m bad blocks) ≤ z̃^m and Lead's Lemma P gives decay once (3^d − 1)z̃ < 1. The chessboard version is
better than §3.2 only where the *typical* κ_p/W_p is much larger than the worst case; at strong coupling with unit blocks it is worse
(z̃ ≤ 1 − (1 − δ)^{24}). RP is therefore available but not decisive.

### 3.4 Generalisation S' (effective theories)

Everything above holds verbatim for any finite-range Gibbs measure on links with positive local factors ψ_X (X finite link sets of
bounded diameter): split each factor pair ψ_X(U_X)ψ_X(U'_X) over its own mixing group. Decay follows when active factors do not
percolate; deterministic criterion: (number of factors meeting a factor) × (1 − (ψ_min/ψ_max)²) < 1. This is a torus-decay engine for a
*strongly coupled effective theory*: local, single-scale, boundary-free (no confinement claim). **Proved** (the counting constant
depends on the factor geometry and is not written out).

### 3.5 Relation to Theorem R

Theorem R (finite abelian G, plaquette variables) is the same argument with the swap made admissible by **agreement** (ordered
mechanism: both replicas sit near the same ground state). S makes it admissible by **flatness** of the weights (disorder mechanism).
Both are instances of Theorem G with (I) = independence. In link variables without gauge alignment, S is blind to the ordered
mechanism (W1 below: about 1/2 for Z₂), so Z₂ at weak coupling is covered by R, not by S. A gauge-aligned soft swap (swap U' after a
gauge transformation h fitted to U) would unify them, but the alignment variables bring back the quenched/annealed dilemma for RP
(the normaliser of P(h | U, U') is non-local); not pursued, since §4 shows alignment cannot rescue weak-coupling SU(2) anyway.

---

## 4. Why there is no weak-coupling window on the lattice

### 4.1 Optimality (O)

If an event A has S(A) = A and S preserves the measure on A, then ν|_A ≤ ν and ν|_A ≤ S_*ν, so ν(A) ≤ ∫min(ν, S_*ν) =
1 − TV(ν, S_*ν). With auxiliary variables the same bound holds for the projection. The split attains it (κ = min(W, W∘S) is
S-invariant). Finite version: `admissible_le_overlap`, `overlap_inv`, `overlap_eq` (overlap = 1 − ½Σ|p − p∘S|). **Proved, Lean.**
So the question "how likely is a swap admissible" has a construction-independent answer: one minus the total variation between the
replica pair and its partially swapped image.

For independent replicas and a swap of the link set D, the first replica of S_*ν is (U'_D, U_{Dᶜ}) ~ μ_D⊗μ_{Dᶜ}, so
**ν(A) ≤ 1 − TV(μ, μ_D⊗μ_{Dᶜ})**: admissibility is bounded by how far the field inside D is from being independent of the field
outside. **Proved.**

### 4.2 W1: unaligned swaps (exact inequality)

Take one link ℓ of p (starting at site s) and the mixing σ that exchanges only ℓ. Then κ_p ≤ W_p∘σ, and

  P(t_p = 0) = E_{μ⊗μ}[κ_p/W_p] ≤ Z⁻² ∫ W_p(σ(U,U')) ∏_{q≠p} W_q.

Gauge-transform replica 2 at s by g (Haar, leaves ∏_{q≠p}W_q and the Haar measure invariant) and average over g: the two mixed
plaquettes become Re tr(gB) and Re tr(Cg⁻¹), and by Cauchy–Schwarz ∫φ(gB)φ(Cg⁻¹)dg ≤ ∫φ(h)²dh = J(2β). Hence, **exactly**,

  P(t_p = 0) ≤ J(2β)·(Z_{−p}/Z)² ≤ J(2β)·exp(−2β E_{−p}[Re tr U_p])   (Jensen; Z_{−p}, E_{−p}: plaquette p removed).

**Proved.** Asymptotics: SU(2): J(2β) = I₁(4β)/(2β) ~ e^{4β}/(4√(2π)β^{3/2}), so P(t_p = 0) ≲ e^{2βε_p}/(4√(2π)β^{3/2}) with
ε_p = E_{−p}[2 − Re tr U_p]; U(1): ≲ e^{2βε_p}/√(4πβ); Z₂: ≈ cosh(2β)/e^{2β} → 1/2. With the standard small-fluctuation behaviour
βε_p = O(1) (**heuristic** here: not reproved for the measure with p removed), the inactive probability goes to 0 like β^{−dim G/2}:
mixing links of two replicas in independent gauges makes the mixed plaquette Haar-random, and it lands within the fluctuation width
~g per group dimension only with probability ~g^{dim G}. Active plaquettes then percolate: no window.

### 4.3 W2: aligned swaps (Gaussian identity)

Alignment (gauge fixing, or a fitted relative gauge) removes the gauge part of the mismatch but not the gauge-invariant part: the
two replicas' field strengths are independent. At leading order in g² the gauge-fixed field is Gaussian. For two independent copies
of N(0, Σ) and the swap of the coordinates in D, the coordinates u = (a + a')/√2, v = (a − a')/√2 are independent N(0, Σ) and the swap
is v_D ↦ −v_D. So TV(ν, S_*ν) = TV(N(0, Σ), N(0, JΣJ)) (J = −1 on D), and the Bhattacharyya affinity is

  BC = det Σ^{1/2} / det(Σ_DD ⊕ Σ_{DᶜDᶜ})^{1/2} = e^{−I(X_D; X_{Dᶜ})},

I the Gaussian mutual information. With 1 − TV ≤ BC and 1 − TV ≥ BC²/2: **the best admissible probability of swapping D is between
e^{−2I}/2 and e^{−I}.** **Proved** (exact for any Gaussian).

Reading (**heuristic**, standard): (i) I is invariant under rescaling the field, so for the Gaussian approximant it is exactly
β-independent; (ii) for a local field I obeys an area law, I ≈ c|∂D| with c set by the lattice-scale coupling across the cut;
(iii) SU(2) at weak coupling is U(1)³ plus O(g²) (Cartan argument, Pos §4.2), so its admissibility probabilities equal those of
three photons up to O(g²). Any percolation statement about inactive surfaces that holds for SU(2) with a margin therefore holds for
U(1)³, which would give the photon a gap (contradiction with FS, conditional). So on the lattice the soft swap, aligned or not,
**cannot** separate SU(2) from U(1) at weak coupling: the decision sits at the lattice scale, which is the photon structure of Lead D3
in coupling language.

### 4.4 Where it can act

The UV cost is per lattice plaquette of the cut and does not care whether the theory is gapped at large scales. The swap therefore has
to cut an effective theory whose local factors are nearly flat, i.e. at the scale L₁ where the running coupling is of order one (S',
§3.4), never the lattice measure itself at weak coupling. Two honest gaps remain there: (a) the blocked measure is not exactly a
finite-range positive Gibbs measure (RG tails), so S' needs a polymer-type extension; (b) the effective-theory chain in Lean
(`OneScale.Effective.gap_of_effective_W`) consumes a boundary-uniform H2 (`LimitGDS_W`), while S' gives torus decay; feeding S' in
needs a torus version of the robustness lemma, which does not exist yet. Neither is attempted here.

---

## 5. Photon and Z₂ checks

| item | U(1) weak coupling | Z₂ weak coupling | verdict |
|---|---|---|---|
| G, A | identities, hold for every measure | same | pass (no claim) |
| §2 candidates | each fails for U(1) as for SU(2) (zero agreement, or Cov in the cross term) | Z₂: independent replicas agree (Theorem R) | consistent |
| S (construction) | exists, admissibility positive at every β | exists | no claim by itself |
| S-decay window | gives decay only for β < 0.0128, where compact U(1) is in its confined, gapped phase (true) | decay for β < 0.0128 (true, gapped); silent at weak coupling, where R applies | **pass**; a gap-only, torus claim, no area law |
| S' | U(1) effective theories stay weakly coupled at every scale (no running): criterion fails | effective Z₂ flows to the ordered side: S' fails, R applies | pass |
| W1 | P(t_p=0) → 0 like β^{−1/2} | ≈ 1/2 (gauge randomisation) | consistent: unaligned S is vacuous at weak coupling for all three |
| W2 | admissibility β-independent, identical to SU(2) at leading order | — | this *is* the photon test of the method: it is why no lattice window can exist for SU(2) |
| §2.4 | — (no adjoint action: neutral channel trivial) | — | neutral channel never decorrelated by centre couplings |

No statement here gives U(1) at weak coupling a gap or a reach, and none implies an area law for Z₂ at weak coupling.

---

## 6. The fine-structure constant (the owner's pointer)

Where α appears, and whether a natural value is singled out:
- **Strong-coupling window (S).** β < ln(20/19)/(4n): SU(2) g² > 312 (α_s = g²/4π > 24.8); U(1) e² > 78 (α > 6.2). Pure
  combinatorics (the 20 = 4(2d − 3) plaquette neighbours in d = 4) against the weight ratio; no natural α.
- **Unaligned admissibility (W1).** P(t_p = 0) ~ (const·α)^{dim G/2}: for U(1) ≲ e^{O(1)}/√(4πβ) = e^{O(1)}·√α (β = 1/(4πα));
  for SU(2) ∝ β^{−3/2} = (2πα_s)^{3/2}. This is the one place where α enters as such: the chance that two independently oriented
  replicas match within the quantum fluctuation width, one factor √α per group dimension. It reaches order one only at α_s of order
  one (ignoring e^{2βε_p}, the bound is 1 at α_s ≈ 0.74; a rough number, not a threshold). No sharp value.
- **Aligned admissibility (W2).** Exactly α-independent at leading order: the mutual information is scale invariant, so α drops out.
  Its α-dependence starts at O(g²), the same order as the one-loop running. In this reading the swap sees the coupling only through
  its running, i.e. only through H1, and the point where it can work is where α_s is of order one (L₁, PREP "Pointer"). That matches
  the owner's reading of L₁ but singles out no specific α value.

---

## 7. Lean (built in `~/formal-att-b`, Lean 4.34.0, Mathlib v4.34.0, 2026-11-21)

| file | content | status |
|---|---|---|
| `Attempts/R2/CouplingSwap.lean` | `nonempty_of_prob`, `integral_comp_mp`, `setIntegral_eq_zero_of_antisymm`, `integrable_of_abs_le`, `abs_setIntegral_le`, `replica_identity` (E_{μ⊗μ}[(f−f')(g−g')] = 2Cov), **`swap_cov_bound`** (Theorem G, product case, with auxiliary labels), **`cross_transfer`** (Lemma A) | builds clean, no `sorry`, no warnings |
| `Attempts/R2/CouplingSplit.lean` | `orbitMin`, `orbitMin_le`, `le_orbitMin`, **`orbitMin_smul`** (mixing invariance), `splitW`, `splitW_nonneg`, **`splitW_sum`** (marginal), `splitW_false_inv`, `splitW_true_inv`, `orbitMin_ratio` (κ/W ≥ a/b), **`admissible_le_overlap`**, `overlap_inv`, **`overlap_eq`** (optimality, overlap = 1 − TV) | builds clean, no `sorry`, no warnings |

Not formal: the lattice instantiation of S (the measure ν̂ on gauge connections, measurability of D(t), the chain counting), RP of
ν̂ (would reuse `Positivity.rp_abstract`), the chessboard theorem, W1 and the Gaussian identity W2.

---

## 8. Report (RULES.md 7)

- **Tried:** the brief's candidates (maximal couplings, Doeblin/Nummelin splits static and dynamic, a shared Hubbard–Stratonovich
  field, centre-symmetric couplings, common dominating measures), each against marginals, RP, agreement, cross term, photon, Z₂; then a
  coupling that keeps independence and replaces agreement by a mixing-invariant split of the cut weights.
- **Holds:** Theorem G and Lemma A (Lean); the case-by-case negatives of §2 (the HS field gives an exact, local, RP rewrite with zero
  agreement and the full covariance in the auxiliary field); the soft swap S with exact marginals, RP (modulo instantiation), positive
  admissibility for every compact group, and torus decay at strong coupling for all groups (SU(2) β < 0.0064, U(1)/Z₂ β < 0.0128);
  optimality O (Lean); the exact unaligned bound W1; the Gaussian identity W2.
- **Fails, and why:** exact agreement for continuous groups needs shared atoms, which put Cov_μ into the cross term (A); independence
  is the only free decorrelation; with independence the admissibility of any swap is 1 − TV(ν, S_*ν), a lattice-scale quantity that at
  weak coupling is β-independent and the same for SU(2) and U(1)³ (W2), or tends to 0 without alignment (W1). So no lattice window at
  weak coupling exists for any swap construction; the obstruction is the UV, not the infrared.
- **Single most promising next step:** use S' as the H2-side certificate at the scale L₁: state "the effective theory at L₁ has
  soft-swap-subcritical factors" as a torus-type H2 alternative and prove the missing torus robustness lemma (effective convergence in
  the sense of H1 plus subcritical active factors in the limit theory ⇒ `LevelDecay`). That lemma is single-scale and Lean-friendly; it
  would make the coupling route an exact restatement of the H1/H2 split with a boundary-free H2, and its numerical content (κ_X/W_X
  for blocked factors at L₁) is measurable on existing configurations.

---

## References (ideas only; nothing copied)

- Froehlich, Israel, Lieb, Simon, CMP 62 (1978) 1 (chessboard estimates; recalled).
- Osterwalder, Seiler, Ann. Phys. 110 (1978) 440 (RP and the strong-coupling gap of lattice gauge theories; recalled).
- van den Berg, Maes, Ann. Probab. 22 (1994) 749 (disagreement percolation; recalled).
- Edwards, Sokal, Phys. Rev. D 38 (1988) 2009; Chayes, Machta, Redner, J. Stat. Phys. 93 (1998) 17 (auxiliary-label / two-replica
  graphical representations; the idea of a split label; recalled, not re-read).
- Nummelin, Z. Wahrsch. 43 (1978) 309; Athreya–Ney (1978) (splitting of Markov kernels; recalled).
- Hubbard (1959), Stratonovich (1957) (Gaussian linearisation; standard).
- Wolf, Verstraete, Hastings, Cirac, PRL 100 (2008) 070502 (area laws for mutual information of classical Gibbs states; recalled,
  used only for the heuristic area law in W2).
