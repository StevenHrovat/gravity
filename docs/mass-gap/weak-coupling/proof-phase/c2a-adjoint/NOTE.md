# Cycle 2, workstream A: the adjoint half of D′ at L₁ (2026-11-22)

Brief: state the adjoint half of the refined Dobrushin condition precisely, in the weakest form that still feeds `LimitDprime`;
decide whether the W₁ (coarse-curvature) form can replace the sup form; formalise the two-site-type Dobrushin theorem; look for an
analytic handle on the adjoint coupling at L₁; evaluate Leg C's fitted actions with a pre-registered rule.

Claim levels as in `../../attempts/RULES.md` and workstream 1: **Lean** (machine-checked), **Lean (definitional)**, **paper**
(complete argument here), **paper modulo** (a named standard theorem), **heuristic**, **numerical**. Lean: two new files under
`../../../formal/ProofPhase/Adjoint/` (`CentreSplit.lean`, `TwoType.lean`), built in `~/formal-c2a` against the current tree
(including workstream C's assembly change, commit 6f5be85); `axioms-c2a.sh` prints the axioms of 22 headline theorems: all
`propext, Classical.choice, Quot.sound`; no `sorry`, no `native_decide`, no new axioms. Scripts here: `setup-c2a.sh`,
`build-c2a.sh`, `axioms-c2a.sh`; numerics: `kA_bounds.py`/`.log`, `kA_lp.py`/`.log` (CPU, seconds); Leg C: `PREREG.md`,
`evaluate_adjoint.py`, results in §5.

(Coordinator note: workstream C saw `CentreSplit.lean` fail at lines 122 and 179. That was my first draft, fixed within minutes;
the file builds, and was rebuilt against the current tree after the assembly change.)

---

## 0. Results at a glance

1. **The adjoint half, precisely, and the weakest form that feeds `LimitDprime` (Lean).** Split every limit potential at L₁ by
   the local centre action: `V = V⁰ + V¹`, `V⁰_A(U) = 2^{−|A|} Σ_{F⊆A} V_A(centre flip of F in U)` (the centre-blind part, a
   function of the adjoint images of the coarse links), `V¹ = V − V⁰` (centre-charged).
   **AdjointHalf(λ, γ_A):** the pair oscillations of `V⁰` satisfy D′_λ with `γ_A` in every volume. **CentreHalf(λ, γ_C):** the
   same for `V¹`. **`limitDprime_of_halves`**: `AdjointHalf γ_A ∧ CentreHalf γ_C ∧ γ_A + γ_C < 1 ⇒ LimitDprime`; hence
   `slabDecay_of_halves`, `massGap_of_goodBlocking_halves`, and `blockedTorusRoute_of_halves` (the first disjunct of the
   assembly's `OpenPieces.crossover`). This needs **no two-type theorem**, and it is **strictly weaker** than workstream 1's
   two-type D′_ref (paper, §1.3): in the two-coupling proxy it reads `18 tanh(2β_A/3) + 18 tanh β_F < 1` instead of D′_ref's two
   columns `18 tanh(β_F + 2β_A/3) + 18 tanh β_F + tanh 6β_F < 1` and `36 tanh β_F + tanh 6β_F < 1`.
2. **W₁ instead of sup for the adjoint half: yes on SU(2) sites, no on split sites** (§2). (a) In the two-type (split) form no
   section-independent metric on the adjoint sites works: every measurable section of SU(2) → SO(3) is discontinuous, and an
   arbitrarily short adjoint move across its cut is a centre flip, so the cross coefficient adjoint → centre is infinite as soon
   as the centre-charged couplings are non-zero (paper). (b) On unsplit SU(2) sites with the geodesic S³ cost, Dobrushin's theorem
   with metrics is valid; its coefficient splits additively into a centre-charged and an adjoint term (paper), and the Lean
   `OneScale.theoremA_W` already covers covariances with one Lipschitz observable. (c) **The price:** W₁ coefficients are not
   continuous in the sup norm of the potentials, so the openness step of the blocked route needs **H1 in a Lipschitz norm**
   (`H1LocalLip`, stronger than `H1Local`), and the window is only linearised until a certified sup is computed.
   (d) **Sharper constant:** the linearised adjoint W₁ constant is `k_A ∈ [2√2/(15π), 1/(5π)] = [0.0600, 0.0637]` (proved, new; C
   had [0.0531, 0.0722]); a transport LP gives `0.0625 ≈ 1/16`. Pure adjoint linearised window: **β_A < 1/3** (proved bracket
   [0.327, 0.347]). **Nonlinear ceiling (numerical):** at the aligned staple configuration the W₁ column already reaches 1 at
   **β_A ≈ 0.28**, so the certified W₁ window is at most ≈ 0.28; against the sup form's **β_A < 0.0834** that is still a
   factor ≈ 3.4 wider. Proxy entry scale: W₁ L₁√σ ≈ 3.7 (band 3.5–3.9), TV ≈ 4.8.
3. **Dobrushin's theorem with two site types, in Lean** (§3): `decay_twoType_blocks`: for any measurable split
   `S ≃ᵐ S_A × S_Z` carrying `ν` to `ν_A ⊗ ν_Z`, column sums `a` (adjoint → adjoint), `b′`, `b` (cross), `c` (centre → centre) of
   the **sharp** (mixed-second-difference) coefficients with weight `e^{λ d}`, and `a < 1`, `c < 1`, `b b′ < (1 − a)(1 − c)`,
   covariances of bounded observables decay at rate λ. Ingredients: `influence_site_sharp` (new, sharper than workstream 1's
   `influence_site`; it gives ws1's `tanh β_F` cross terms), `map_split`/`integral_gibbs_split` (the split preserves the
   measures), `schur_weights` and `twoType_criterion` (type weights through a quasi-metric). D′_ref is now a machine-checked
   sufficient condition for decay at one effective theory; the uniform-in-level route version is paper (§3.3), and by item 1 it is
   not needed.
4. **Analytic handle on the adjoint coupling at L₁: none that bounds it** (§4). What is proved or sharpened: (a) any bound
   implying the adjoint half (with the centre half) implies the gap of the blocked theory, so no handle can be weaker than the gap
   at L₁ (Lean composition); (b) the **dimension swap** gives a rigorous necessary condition: a D′_λ certificate for the true
   blocked theory has `λ ≤ m₀₊₊ L₁` (paper modulo O(4) of the limit and overlap of block observables with the 0⁺⁺ state);
   (c) the two halves are controlled by the two physical scales: centre half by `e^{−σL₁²}` (quadratic: switches on early), adjoint
   half by `e^{−m₀₊₊L₁/4}` (linear: switches on late) (heuristic, leading-order strong coupling). This matches the owner's
   reading "centre = root, adjoint = existence / self-charge", and in that proxy it makes the adjoint half the bottleneck
   (`m/√σ ≈ 3.75 < 4`). Leg C's path-product variable shows the opposite ordering (§5.1): its adjoint channel is suppressed far
   below the tube estimate (self-energy of the adjoint charge), so which half binds is a property of the block variable.
5. **Leg C** (§5): pre-registered (`PREREG.md`, before any SU(2) fit was read; amendments before data: sharpened `k_A`, the
   nonlinear W₁ ceiling flag). Photon gate passes for f = 1/2 (all noise variants). **SU(2), β = 2.3, primary f = 1/2:** the
   halves criterion is **NOT_EXCLUDED at L√σ = 3.15 and 4.2** (H_TV = 0.18, 0.04; adjoint half 0.021, 0.013; W₁ likewise) and
   EXCLUDED at 2.1, **where the centre half (β_F = 0.19), not the adjoint half, is the obstruction**; fitted β_A ≈ −0.002, a
   factor ~250 below C's proxy. **After-data caveat, decisive:** the adjoint coarse plaquette of this block variable is zero within
   two errors from L√σ = 3.15 on: the variable is close to Haar noise in the adjoint channel, so the click is the noise-limit
   trap (P7.3): D′ is cheap and the gap moves into `ObsTransfer`. It shows that the adjoint half binds or not depending on how
   much adjoint content the block variable keeps; the measurement that decides it uses the good blocking with a content check.

## 1. The adjoint half

### 1.1 The centre split (Lean, `CentreSplit.lean`)

Coarse potentials as in the assembly: `V_j : Finset(links) → (links → SU(2)) → ℝ`, one log-factor per link set `A`, depending
on `A` only. For a central `c` with `c² = 1` (SU(2): `c = −1`) and a link set `F`, `centreFlip c F U` multiplies the links of `F`
by `c`. Definitions and facts (all Lean, elementary):

* `centreAvg c V A U = 2^{−|A|} Σ_{F ⊆ A} V A (centreFlip c F U)` (the projection on the trivial character of `Z₂^A`);
  `centrePart = V − centreAvg`.
* `centreAvg_flip`: `centreAvg` is invariant under the flip of any single link (so it depends on the links only through
  their adjoint images: it is the "adjoint part of each coarse link" in the sense of the brief).
* `centreAvg_of_blind`: a centre-blind factor is its own centre-blind part. `centreAvg_centrePart`: the centre-charged part has
  centre-blind part 0.
* `centreAvg_eq_zero_of_odd`: a factor odd under the flip of one of its links has centre-blind part 0. This covers the
  fundamental SU(2) plaquette `½tr U_p`, the U(1) plaquette `cos θ_p` and the Z₂ plaquette.
* `pairOsc_add`, `flatW_add` (with `tanh((a + b)/2) ≤ tanh(a/2) + tanh(b/2)`): D′_λ is subadditive under a sum of
  potentials.

### 1.2 The statement

> **AdjointHalf(λ, γ_A)** (open). There are pair-oscillation bounds `S⁰_j(i, z)` of the centre-blind parts `V⁰_{∞,j}` of the
> limit potentials at L₁ (moving the coarse link `z` changes the summed centre-blind log-factors through `i` and `z` by at most
> `S⁰`) with `Σ_{i≠z} tanh(S⁰_j(i,z)/2) e^{λ·linkDist(z,i)} ≤ γ_A` for every `z` and every volume `j`.
> **CentreHalf(λ, γ_C)** (open; confinement-type). The same for the centre-charged parts `V¹ = V − V⁰` with `γ_C`.
>
> **Theorem (`limitDprime_of_halves`, Lean).** `AdjointHalf(λ, γ_A) ∧ CentreHalf(λ, γ_C) ∧ 0 ≤ γ_A + γ_C < 1 ⇒ LimitDprime λ`.

Composition with workstreams 1 and C (Lean): `slabDecay_of_halves` (`H1Local ∧ halves ∧ ObsTransfer ⇒ SlabDecay`),
`massGap_of_goodBlocking_halves` (on a line of constant physics, with the good blocking: `MassGap ∧ LatticeGap ∧ LimitRP`),
`blockedTorusRoute_of_halves` (`H1Local ∧ halves ∧ ObsTransferPhys ⇒ BlockedTorusRoute`, the torus disjunct of
`OpenPieces.crossover`), `blockedSlabRoute_of_halves`.

**Why this is the weakest useful form.** `LimitDprime` itself is weaker still (it uses the oscillation of the whole factor, which
can be smaller than the sum of the two parts), so "the adjoint half" is not a necessary condition; it is the cleanest sufficient
one that separates the physics: everything centre-charged (the fundamental string tension channel) goes into `γ_C`, everything
centre-blind (glueballs, the adjoint channel) into `γ_A`. For the fitted families of Leg C the split is explicit (`PREREG.md`):
plaquette `f_e = β_A(4t² − 1)/3`, `f_o = β_F t + β_T(2t³ − t)`, rectangles centre-charged only.

### 1.3 Comparison with workstream 1's two-type D′_ref (paper)

In D′_ref (two sites per link: SO(3) part `R_l`, centre part `σ_l`) the adjoint column is
`Σ_l [tanh(D^{AA}_{lm}/4) + (cross terms)]`, where `D^{AA}` is the mixed second difference of the factors when the SO(3) parts
of `l` and `m` move. A move of `R_m` with `σ_m` fixed covers (up to the closure of a fundamental domain, which the supremum over
the other links' configurations fills) every move of `U_m` within `σ_m F`; the supremum of the mixed second difference over such
moves equals that over all moves of `U_m` (for a plaquette: both are `2(f(1) − f(0))`-type values, attained in the limit at the
cut). So **D′_ref's adjoint column alone dominates the plain sharp D′ column**, and the halves criterion (subadditive split of
that column) is implied by D′_ref's adjoint column condition up to the cross terms. Hence:

  **D′_ref ⇒ halves criterion ⇒ LimitDprime**, with strict implications in the proxy (numbers in item 1 of §0).

The two-type structure is therefore not needed for sufficiency; its value is structural (the centre fibre, Route B's flux:
workstream 1, §3.4), and as the natural vehicle for a W₁/TV mixed criterion if one ever exists (§2.1 says: not with a
section-independent metric).

### 1.4 Numbers (two-coupling proxy, `r2-curvature` §3.4) and generators

Proxy at L₁√σ = 2, 2.5, 3, 4 (m/√σ = 3.75): `a_TV = 18 tanh(2β_A/3)` = 11.8, 8.5, 5.8, 2.5; `c_TV = 18 tanh β_F` = 1.31, 0.14,
0.009, 10⁻⁵. The centre half is negligible from L₁√σ ≈ 2.5; the adjoint half needs `β_A < 1.5 artanh(1/18) = 0.0834`, which the
proxy reaches near L₁√σ ≈ 4.8. Exact for plaquette-only two-coupling actions: the supremum in `S⁰` is attained (`t² ∈ [0, 1]`
is fully realised), so `a_TV = 18 tanh(2|β_A|/3)` is the exact sup-form adjoint half of that family.

**Workstream B's generators (coordinator item 2).** The halves (via `LimitDprime` and `decay_of_flatW`) give decay at rate λ of
all bounded block observables, in particular of the ≤ 3-plaquette block Wilson loops that generate the gauge-invariant
observables (B's `norm_pow_le_of_generators` then spreads the rate to the closed span). So the halves are a sufficient condition
for B's target. The converse fails (decay of generators does not give a Dobrushin condition). The refinement that does hold
at the generator level: centre-charged generators (fundamental loops) are the centre half's business; centre-blind ones
(adjoint loops, products of two fundamental loops) the adjoint half's. If B's target is the deliverable, the adjoint half is
stronger than needed; it is the strongest local (single-link, worst-case) form of it.

### 1.5 Unit tests

* **Photon.** U(1) Wilson `β cos θ_p` is odd under one flip: `V⁰ = 0` (`centreAvg_eq_zero_of_odd`), so `AdjointHalf` holds with
  `γ_A = 0`, and the photon is excluded by the centre half alone (its centre-charged coupling stays of order one at every scale;
  Leg C's U(1) fits: `c_TV ≈ 17.5` at f = 1/2). This is workstream 1's point: a centre-blind condition alone passes the photon,
  so the adjoint half must never be used alone. Passed for the halves criterion.
* **Z₂.** All Z₂ factors are odd: `V⁰ = 0`, halves = centre half = D′, confinement-type; fails for weak-coupling Z₂ (ordered,
  sharpening factors); conclusions are gap-type. Passed.
* **Finite subgroups** (binary icosahedral, order-12 binary dihedral; centre {±1}): the split is defined; frozen phases have
  sharp centre-charged and centre-blind factors and fail both halves; the gap-type conclusion is consistent. Passed.
* **Deconfinement.** The halves imply D′, which must fail for L₁ < 1/T_c; the centre half carries this (a one-block-thick torus has
  ordered Polyakov loops). The adjoint half alone, uniform over tori, must also fail at L₁ = 1/T_c (centre-blind correlations
  are critical there: workstream 1, §1.4), not below. Consistent.
* **Triviality, Banks–Zaks.** Nothing here is an existence claim; the halves at L₁ fail for conformal-window theories (no
  strong-coupling scale). Passed.

## 2. W₁ instead of sup for the adjoint half

### 2.1 Not on split sites (paper)

Two-type Dobrushin with metrics ρ_A on the SO(3) sites and the discrete metric on the Z₂ sites needs finite coefficients
`C_{(l,Z),(m,A)} = sup TV(law of σ_l at R_m, at R′_m) / ρ_A(R_m, R′_m)`. Every measurable section `s: SO(3) → SU(2)` is
discontinuous (the double cover is non-trivial: π₁(SO(3)) = Z₂), so there are `R_n → R` with `s(R_n) → −s(R)`. With σ_m fixed,
moving `R_m` from `R_n` to `R` flips the sign of `U_m = σ_m s(R_m)` up to a small move, so the conditional law of a neighbouring
`σ_l` changes by the influence of a centre flip, which is positive (about `tanh β_F`) whenever the centre-charged couplings are
non-zero, while `ρ_A(R_n, R) → 0` for any metric continuous on SO(3). So `C = ∞`. With the lifted metric `ρ_A(R, R′) =
d_{S³}(s(R), s(R′))` the coefficient is finite, but the adjoint sites then see the hemisphere-folded law, whose W₁ constants are
at least those of S³ (a test function on the closed hemisphere may separate the two antipodal equator points). Nothing is
gained over (2.2).

### 2.2 On SU(2) sites (paper; Lean for the Lipschitz half)

Dobrushin's theorem with a metric (Dobrushin 1970) on SU(2) sites with the geodesic cost of S³: the single-link conditional
law's W₁ sensitivity to a neighbouring link. For a potential `V = V⁰ + V¹` the derivative of the conditional law along a
neighbour move is `(g⁰ + g¹ − E(g⁰ + g¹))ρ`, so by the triangle inequality for the KR norm at each `ρ` the coefficient is at
most the sum of a centre-charged and a centre-blind term: **the W₁ adjoint half is the column sum of the centre-blind terms**,
`a_W = sup Σ_l sup_ρ ‖(g⁰_l − E g⁰_l)ρ‖_KR e^{λd}`; for the proxy, linearised at the uniform point, `a_W = 18·(8/3)·k_A·|β_A|`.

What is in Lean: `OneScale.theoremA_W` gives `|Cov(f, g)| ≤ …e^{−λR}` for `f` bounded and `g` Lipschitz under W-influence bounds
(finite range). For bounded `g` the standard regularisation applies (paper): with `B` the support of `g` and `supp f ∩ B = ∅`,
`Cov(f, g) = Cov(f, ĝ)`, `ĝ = E[g | outside B]` (DLR), and `ĝ` is Lipschitz in the boundary links of `B` with constant
`≤ ‖g‖_∞ · Σ_{x ∋ z, x ∩ B ≠ ∅} Lip_z(V_x)` (TV bound `tanh(D/4)`, `D ≤ 2 Lip·ρ`), at the cost of one factor range in the
distance. So **W₁ D′ at one effective theory with Lipschitz potentials ⇒ decay of all bounded block observables**: the
replacement holds at fixed effective theory.

### 2.3 The constant k_A (proved bracket, numerical value)

`k_A = ‖h₂·Haar‖_KR` on the unit S³, `h₂(u) = ⟨u, a⟩⟨u, b⟩` (`a ⊥ b`), the per-neighbour constant of the adjoint channel.
In coordinates `(y₁, y₂) = ρe^{iψ}`, `(y₃, y₄) = √(1 − ρ²)e^{iχ}` (y the 45°-rotated frame): `h₂ = ρ² cos 2ψ / 2`, Haar has
`q = ρ²` uniform and ψ, χ uniform.

* **Upper bound `1/(5π) = 0.06366` (proved).** Transport inside every circle {q, χ fixed} along ψ: arc length `ρ|Δψ|` bounds
  the geodesic distance, and the 1D optimum on that circle is `ρ ∫|G| dψ = ρq/(2π)` (G the cumulative mass `q sin 2ψ/(8π)`);
  `∫₀¹ q^{3/2} dq/(2π) = 1/(5π)`.
* **Lower bound `2√2/(15π) = 0.06002` (proved).** Test function `(|y₁| − |y₂|)/√2`: Euclidean gradient of norm 1 a.e., so
  1-Lipschitz for the chordal and hence the geodesic metric; `∫ φ h₂ = (E|y₁|³ − E|y₁|y₂²)/(2√2)·2 = 2√2/(15π)` with
  `E|y₁|³ = 8/(15π)`, `E|y₁|y₂² = 4/(15π)` on S³. (MC check: 0.06005 ± 0.00004.)
* **Numerical value 0.0625.** Exact transport LP on the χ-quotient (the measure is χ-invariant, so W₁ equals that of the quotient
  with `d = arccos(ρρ′cos Δψ + √(1−ρ²)√(1−ρ′²))`): 0.06159, 0.06209, 0.06227, 0.06235 at 8×32 … 20×80 cells; h² extrapolation
  0.06249. **Conjecture: k_A = 1/16.**

Pure adjoint linearised window `β_A* = 1/(48 k_A)`: **[0.327, 0.347], numerically 1/3** (C's bracket gave [0.289, 0.392]).

**Nonlinear check (numerical, `kA_bingham.py`).** At the aligned configuration (six equal staples, `β_F = 0`: the conditional law
is the Bingham law `∝ exp(6κ⟨u,a⟩²)`, `κ = 4β_A/3`) the per-unit coefficient `‖(h₂ − E h₂)ρ‖_KR` grows with the coupling:
0.0624 (β_A = 0), 0.0675 (0.1), 0.0736 (0.26), 0.0740 (0.28), 0.0749 (1/3), 0.0742 (0.5). The column `48 k β_A` crosses 1 at
**β_A ≈ 0.281**. Since the criterion is a supremum over configurations, **the certified W₁ window of the pure adjoint
two-coupling action is at most ≈ 0.28** (a ceiling, as C's π/16 for the fundamental channel); its true value needs the full
Bingham supremum (§2.4). With the proxy (m/√σ = 3.75) the W₁ adjoint half enters at **L₁√σ ≈ 3.7** (linearised 1/3: 3.45), the
TV adjoint half near 4.8.

### 2.4 The price, and verdict

* **Openness needs H1 in a Lipschitz norm (paper).** The route needs the level-k theories to satisfy the criterion from some `k₀`
  on (`levelFlat_of_local`). TV coefficients move by at most `tanh` of sup-norm changes; W₁ coefficients do not: adding
  `η·w(U_z)` with `|w| ≤ 1` and Lipschitz constant `L_w` to a factor changes the W₁ coefficient of `z` by up to order `η·L_w`,
  unbounded for fixed `η`. So the W₁ route needs `H1LocalLip`: closeness of the local potentials in sup **and** Lipschitz norm,
  `Σ_{x∋i,z} (‖V_k − V_∞‖_∞ + Lip_z(V_k − V_∞)) e^{λd} → 0`. Physically plausible for the good blocking (smeared variables,
  smooth effective action) but strictly stronger than `H1Local`.
* **Linearised vs certified.** The window above is at the uniform point. The supremum over configurations is a low-dimensional
  problem in the adjoint channel: at `β_F = 0` the single-link conditional law is a **Bingham law** `∝ exp(uᵀQu)` on S³ with
  `Q = (4β_A/3)Σ_k a_k a_kᵀ` (PSD, trace `8β_A`), so the worst case is a supremum over the eigenvalues of Q (a 3-simplex) and the
  direction of the moved staple: a certified computation is in reach (not done here).
* **Verdict.** The W₁ form can replace the sup form for the adjoint half, on SU(2) sites, at the price of `H1LocalLip` and a
  certified Bingham supremum; it cannot be combined with the two-type split. It widens the adjoint window by a factor 4
  (0.0834 → 1/3 linearised).

## 3. Dobrushin's theorem with two site types (Lean, `TwoType.lean`)

### 3.1 Statements

* `influence_site_sharp`: for a Gibbs system with local potentials, if `Δ(τ) = Σ_{x∋i,z}(V_x(τ) − V_x(τ with z moved))` has
  oscillation `≤ D_{iz}` as a function of the value at `i`, then `tanh(D_{iz}/4)` is an influence bound of `z` on `i`, for every
  boundary condition. `pairDiff_of_pairOsc`: never worse than workstream 1's oscillation form (`D ≤ 2S`). It is what gives
  ws1's `tanh β_F` for the cross terms (the adjoint part cancels in the centre site's conditional law).
* `decay_of_sharpW`: Theorem A (weighted, quasi-local) from the sharp coefficients.
* `map_split`: for `e : S ≃ᵐ S_A × S_Z` with `ν.map e = ν_A ⊗ ν_Z`, `split e` (adjoint part of link `l` from site `inl l`,
  centre part from `inr l`) maps `(ν_A ⊗ ν_Z)^{⊗(ι⊕ι)}` to `ν^{⊗ι}`; `integral_gibbs_split`: the Gibbs measure of `V` is the
  image of the two-type Gibbs measure of `V ∘ split e`.
* `typeDist` (link distance + type shift κ, a quasi-metric), `schur_weights` (`a, c < 1`, `bb′ < (1−a)(1−c)` ⇒ ∃ `r > 0`,
  `a + rb′ < 1`, `b/r + c < 1`), `twoType_criterion` (the block column sums give D′_λ on the two-type system with
  `γ = max(a + e^{λκ}b′, e^{−λκ}b + c)`).
* **`decay_twoType`**: under D′_λ on the two-type system, `|Cov_μ(f, g)| ≤ (1−γ)⁻¹ (2Σ_{a∈A} v_a) L_g e^{−λ(R − |κ|)}` for bounded
  observables of the original links. **`decay_twoType_blocks`**: the same from the block (Schur) condition, `λ > 0`.

### 3.2 What it settles

Workstream 1's D′_ref (`ws1-routeA/NOTE.md` §1.4) is a machine-checked sufficient condition for decay of coarse block observables
at one effective theory, for any measurable split of the single-link space (for SU(2) the hemisphere section gives one; its
existence is elementary and not formalised). The block form adds the weights workstream 1 did not use: only `a < 1`, `c < 1` and
`bb′ < (1−a)(1−c)` are needed, not two separate column conditions with weight 1.

### 3.3 The uniform-in-level version (paper)

As `levelFlat_of_local`, on the two-type system: `H1Local` transfers to it (`|V_k∘split − V_∞∘split| ≤ η`; mixed second
differences move by at most `4Ση`), except for the same-link pairs `(inl l, inr l)`, which involve the single-link factors
`V_{{l}}`; these need one more hypothesis (single-link factors converge uniformly; automatic for gauge-invariant potentials,
whose single-link factors are constant). Not formalised: by §1.3 the halves route (Lean) is weaker in hypotheses and already in
the assembly.

## 4. An analytic handle on the adjoint coupling at L₁?

**(a) No shortcut below the gap (Lean composition).** `blockedTorusRoute_of_halves`/`massGap_of_goodBlocking_halves`: any
analytic bound implying the adjoint half (with the centre half, `H1Local`, `ObsTransfer(Phys)`) implies the mass gap. Even at a
single effective theory, the halves imply uniform exponential decay of the blocked theory in every volume. So a bound on the
adjoint coupling at L₁ is at least gap strength for the blocked theory, and strictly stronger (worst case over boundaries).
There is no "easier" analytic handle hiding here; the adjoint half is the crossover.

**(b) Dimension swap: an upper limit on what any certificate can give (paper modulo O(4) and overlap).** D′_λ at L₁ gives decay
of block observables at rate `λ/L₁` in the spatial directions of the coarse lattice, with the same constant in every direction.
In the continuum limit (O(4) invariant: external, P6.4) the slowest decay of a block observable with non-zero overlap with the
0⁺⁺ state is `m₀₊₊` in every direction (the temporal gap rotated into a spatial correlation length: the owner's "switching
dimensions", `PREP.md`). Hence **λ ≤ m₀₊₊ L₁** for any D′_λ certificate of the true blocked theory; for nearest-neighbour
columns (`col(λ) = col(0)e^{λ}`) this means `col(0) ≥ e^{−m₀₊₊L₁}`. It is a consistency bound (it cannot prove the adjoint half),
and `evaluate_adjoint.py` checks it on the fitted actions (a violation marks a fit artefact).

**(c) Two halves, two scales (heuristic, leading-order strong coupling).** Centre-charged couplings need fundamental plaquettes
tiling the area of a fundamental loop: `u_F ≈ e^{−σL₁²}` (quadratic in L₁). The centre-blind (adjoint) channel carries the
glueball through a tube of four plaquettes per step: `u_A ≈ e^{−m₀₊₊L₁/4}` (linear in L₁). So the centre half ("the root",
confinement) switches on early and fast, the adjoint half ("existence / self-charge") late and slowly, and the entry scale of
the adjoint half is `L₁* ≈ (4/m₀₊₊) ln(1/u_A*)`. At strong coupling `m a = 4σa²`, i.e. `m/√σ = 4a√σ` (= 12 at a√σ = 3); the
physical `m/√σ ≈ 3.75` is a factor 3.2 below that: **the adjoint half is the bottleneck because the physical glueball is light
compared with the strong-coupling tube**. This is the owner's ROUND-1 split made quantitative, not a bound.

**(d) Running of the adjoint channel once in the window (paper modulo the high-temperature cluster expansion).** Once the halves
hold at L₁ with room, blocking further keeps them (u_A(2L) ≲ C u_A(L)^p, p > 1, classical): the condition is self-improving
upward, never downward. This orients H1: the RG must carry the theory to the first L₁ where the halves hold; beyond, strong
coupling takes over.

**(e) What a real handle would need.** A rigorous upper bound on the centre-blind single-link influence of the blocked measure
at L₁, i.e. control of the Bingham-type conditional laws of the good blocking's coarse links through the crossover. Its exact
SD identities (Leg C's fit equations) relate `β_A` to coarse expectation values (`⟨χ_A(V_p)⟩/3`, the smeared adjoint plaquette
of size L₁, measured by Leg C as `obs[1]`), so the measurable proxy for the adjoint half is the adjoint coarse plaquette and its
fluctuations; turning that into a bound needs H1.

## 5. Leg C (`PREREG.md`, `evaluate_adjoint.py`)

**Pre-registration.** Written about 02:00 before any SU(2) fit was read (what I had seen of Leg C is listed there); amended once
before data (sharpened `k_A`, 02:20). Quantities: TV halves `a_TV`, `c_TV`, `H_TV = a + c`, `λ*_H`; linearised W₁ halves
`a_W`, `c_W`; windows `β_A*` and gap factors `Y/X`; the dimension-swap consistency check. Verdicts as Leg C (NOT_EXCLUDED /
EXCLUDED / UNDECIDED, base and all extension fits agreeing, signal check required); gates: photon (`H` EXCLUDED at every b), Z₂
deconfined, deconfinement edge.

**Photon gate (U(1), β = 1.1, run of 01:29):** f = 1/2 deterministic and both noisy variants: `H_TV`, `H_W` EXCLUDED at
b = 6, 9, 12, with centre half `c_TV ≈ 17.5` and the U(1) adjoint half alone also EXCLUDED; f = 1/4: EXCLUDED; f = 0: fails
(NOT_EXCLUDED at b = 9, 12), as in Leg C's own gate (f = 0 disqualified).

**SU(2):** §5.1.

### 5.1 SU(2), β = 2.3 (run finished 02:45; evaluated 02:46; `eval_b2.3.log`, `eval_b2.3.json`)

Pre-registered quantities, primary blocking f = 1/2 (signal check PASS at all three L), base fit; every extension fit agrees on
every verdict below.

| L√σ | β_F | β_A | a_TV (adjoint) | c_TV (centre) | H_TV | H_W (lin.) | verdict H_TV / H_W | Y/X (TV) |
|---|---|---|---|---|---|---|---|---|
| 2.10 | 0.1863(4) | −0.0053(4) | 0.063 | 3.32 | 3.38 | 0.965 | EXCLUDED / UNDECIDED | (centre half ≥ 1) |
| 3.15 | 0.0089(6) | −0.0017(8) | 0.021 | 0.161 | 0.181 | 0.051 | **NOT_EXCLUDED / NOT_EXCLUDED** | 0.025 |
| 4.20 | −0.0016(11) | −0.0011(12) | 0.013 | 0.030 | 0.043 | 0.012 | **NOT_EXCLUDED / NOT_EXCLUDED** | 0.014 |

Noisy variants (β_n = 16, 64): the same verdicts at 3.15 and 4.2; at 2.1 H_TV EXCLUDED, H_W NOT_EXCLUDED (β_n = 16) or
UNDECIDED (64). Entry scale (log-linear crossing of H_TV = 1): **L√σ ≈ 2.54**; first counted NOT_EXCLUDED: 3.15. Dimension-swap
consistency: λ*_H = 1.5 (3.15), 2.6 (4.2) coarse units, far below m₀₊₊L = 11.8, 15.8: no flag. Deconfinement flags: none.
Photon gate (β = 1.1): passed for f = 1/2 (all variants). Z₂ deconfined gate (β = 0.6, run finished 02:55): **passed**,
H_TV and H_W EXCLUDED at b = 6, 9, 12 (Z₂ has no centre-blind part; centre half ≈ 7.8 at b = 6). β = 2.4, the second Coulomb β and the
volume check: not yet run (Leg C's queue, expected after 04:00); command at the end of this section.

**Reading, by the pre-registered table:** "H_TV NOT_EXCLUDED at L" from L√σ = 3.15: the fitted, truncated action of this block
variable satisfies the halves criterion, hence D′_λ (Lean: `limitDprime_of_halves`, then `decay_of_flatW`). The adjoint half
is far inside its window (Y/X ≈ 0.01–0.03, i.e. a factor 40–70 of room in sup form); at L√σ = 2.1 the obstruction is the
**centre half** (β_F = 0.19), not the adjoint half. This is the opposite of C's proxy (β_A ≈ 0.5 at L√σ = 3).

**What the data say beyond the table (marked: after data).** The measured coarse expectation values (jackknife over 20 blocks):

| L√σ | ⟨½tr V_p⟩ | ⟨χ₁(V_p)⟩/3 |
|---|---|---|
| 2.10 | 4.64(1)·10⁻² | 8.6(5)·10⁻⁴ |
| 3.15 | 2.2(2)·10⁻³ | −1.9(9)·10⁻⁴ |
| 4.20 | −4(3)·10⁻⁴ | −1.2(13)·10⁻⁴ |

The adjoint coarse plaquette of this block variable is ~10⁻³ at 2.1 and **zero within two errors from 3.15 on**: neighbouring
coarse links are nearly independent in the adjoint channel. So the small β_A is not a strong glueball channel that happens to
fit a window; it is a **block variable close to Haar noise** in that channel (the 9×9 and 12×12 flowed path products lose
their adjoint correlation; C's tube estimate u_A ≈ e^{−mL/4} ≈ 0.05 at 3.15 is off by more than two orders for this variable,
most likely through the perimeter (self-energy) suppression of adjoint loops, which grows with the Casimir). This is exactly the
noise-limit trap of the record (P7.3: pure noise satisfies `SlabDecay`; workstream 1 §2 for decimation): for a near-noise block
variable, D′ at L₁ is cheap and **the whole gap moves into `ObsTransfer(Phys)`** (conditional decoupling of fine observables
given nearly uninformative coarse variables is the fine theory's own decay). So the click is real as a statement about the fitted
action, and it is **not** evidence that the crossover is solved. What it does establish:

1. The pre-registered adjoint-half verdict for Leg C's primary variable: NOT_EXCLUDED at L√σ = 3.15 and 4.2 (sup and W₁ forms),
   with the centre half the binding constraint below ~2.5.
2. The adjoint half is not intrinsically the hard part: whether it binds depends on how much adjoint correlation the block
   variable keeps. The hard part is the pair (adjoint half, ObsTransfer) **for one block variable that keeps content** (the good
   blocking, whose smearing grows with the level; workstream 1's power counting says it is not noise).
3. The relevant measurement is therefore Leg C's fit **with the good blocking as block variable** (workstream 1's next step),
   reported together with the adjoint coarse plaquette (the content check). A pre-registration for it should require
   `⟨χ₁⟩/3` to be resolved (≥ 3σ) before a NOT_EXCLUDED counts.

Command for the remaining runs (CPU, seconds): `py evaluate_adjoint.py ../../attempts/r3-blocked/runs-gpu/*.npz --out
eval_all.json > eval_all.log`.

## 6. Headline theorems

| theorem | statement | mark | Yang–Mills in hypotheses |
|---|---|---|---|
| `centreFlip_centreFlip` | flips compose by symmetric difference (`c² = 1`) | definitional-elementary | no |
| `centreAvg_flip` | the centre average is invariant under every single-link flip | elementary (Fourier on Z₂^A) | no |
| `centreAvg_of_blind`, `centreAvg_centrePart` | centre-blind factors are fixed; the centre-charged part has zero average | elementary | no |
| `centreAvg_eq_zero_of_odd` | factors odd under one flip have no adjoint part (unit-test actions) | elementary | no |
| `pairOsc_add`, `flatW_add` | D′ is subadditive under sums of potentials | elementary | no |
| `limitDprime_of_halves` | AdjointHalf ∧ CentreHalf ∧ γ_A + γ_C < 1 ⇒ LimitDprime | substantive-elementary | SU(2) limit potentials at L₁ (the halves are open) |
| `slabDecay_of_halves`, `massGap_of_goodBlocking_halves`, `blockedTorusRoute_of_halves`, `blockedSlabRoute_of_halves` | the blocked routes and the assembly disjuncts with the halves | assembly (composition) | yes (Wilson measure, its blocked laws, good blocking, tuning) |
| `influence_site_sharp`, `pairDiff_of_pairOsc` | Dobrushin coefficient `tanh(D/4)` from mixed second differences; never worse than the oscillation form | substantive (standard) | no |
| `decay_of_sharpW` | weighted Theorem A from sharp coefficients | substantive reduction (to `theoremA_w`) | no |
| `map_split`, `integral_gibbs_split` | the split `S ≃ S_A × S_Z` preserves product and Gibbs measures | substantive measure theory | no |
| `schur_weights`, `twoType_criterion` | block (2×2 Schur) condition ⇒ D′_λ on the two-type system with type weights | elementary | no |
| `decay_twoType`, `decay_twoType_blocks` | Dobrushin's theorem with two site types | substantive (standard theorem, new formalisation) | no (group-blind: passes no unit test by itself) |

Paper/numerical results: D′_ref ⇒ halves (§1.3); W₁ impossible on split sites (§2.1); W₁ on SU(2) sites with regularisation
(§2.2); `k_A ∈ [2√2/(15π), 1/(5π)]` (§2.3, proved), `k_A ≈ 1/16` (numerical); W₁ openness needs `H1LocalLip` (§2.4); the
dimension-swap bound λ ≤ m₀₊₊L₁ (§4b).

## 7. Blueprint status changes

* **P4.1′:** `LimitDprime` ⇐ `AdjointHalf ∧ CentreHalf` (Lean). The open core is now named: **`AdjointHalf`** (centre-blind part
  of the limit potentials, D′_λ, proxy factor ~6 short in sup form at L₁√σ = 3, ~1.5 short in linearised W₁ form) and
  `CentreHalf` (proxy: holds from L₁√σ ≈ 2.5). D′_ref's two-type theorem: paper → **Lean** (single theory). W₁ form: valid on
  SU(2) sites (paper), needs `H1LocalLip` instead of `H1Local`.
* **P7 (assembly):** `blockedTorusRoute_of_halves` discharges `BlockedTorusRoute` from `H1Local ∧ AdjointHalf ∧ CentreHalf ∧
  ObsTransferPhys`.
* **P2:** new Lean: sharp (mixed-second-difference) Dobrushin coefficients; two-type Dobrushin theorem.
* **P4.1′ numerics (Leg C, β = 2.3):** the halves hold on the fitted action of Leg C's flowed path-product variable from
  L√σ ≈ 2.5 (gates passed), but that variable is near noise in the adjoint channel (§5.1): numerical, not a discharge; the
  decisive measurement is with the good blocking and a content check.

## 8. Next step

**First:** refit with the good blocking as block variable (workstream 1's smeared, reflection-positive variable) at L₁√σ ∈ {2.5,
3, 4}, pre-registered with a content check (adjoint and fundamental coarse plaquettes resolved at ≥ 3σ) before any
NOT_EXCLUDED counts, and evaluate the halves with `evaluate_adjoint.py`. Leg C's β = 2.3 data (§5.1) say the halves are easy for
a near-noise variable; the open question is whether they hold for a variable that keeps content, which is where `ObsTransfer`
becomes cheap. **Second:**
Certify the W₁ adjoint half for the two-coupling family: the supremum over Bingham conditional laws (eigenvalues of Q in a
3-simplex, one moved staple) of the KR norm of the adjoint derivative, with interval arithmetic or a verified transport bound
(the fibre-transport construction of §2.3 generalises to a computable upper bound for each Q). That turns "β_A < 1/3, linearised"
into a proved window, so that a measured `β_A` at some L₁ (Leg C, or a fit with the good blocking as block variable) can be
compared with a theorem; in parallel, state `H1LocalLip` for the good blocking and check whether workstream C's
`ObsTransferPhys` analysis already gives the needed Lipschitz control of the effective potentials.

## References (ideas only)

Dobrushin, Theory Probab. Appl. 13 (1968) 197; 15 (1970) 458 (uniqueness; metrics). Georgii, *Gibbs Measures* (1988), ch. 8.
Mack, Petkova (1979, 1982) (SO(3) × Z₂). Kotecký, Preiss, CMP 103 (1986). Ollivier, J. Funct. Anal. 256 (2009). Bingham, Ann.
Statist. 2 (1974) (antipodally symmetric laws on spheres). Project: `ws1-routeA/NOTE.md`, `../../attempts/r2-curvature/NOTE.md`,
`../../attempts/r3-robust/NOTE.md`, `../../attempts/r3-blocked/PREREG.md`, `../../PREP.md`, workstreams B and C of cycle 2.

### 5.2 SU(2), β = 2.4, and all runs (evaluated 2026-11-22 after BLOCKED DONE; `eval_all.log`, `eval_all.json`; coordinator)

Command as above (17 s). Primary blocking f = 1/2, base fit, signal check PASS at all three L:

| L√σ | β_A | a_TV (adjoint) | c_TV (centre) | H_TV | H_W (lin.) | verdict H_TV / H_W | Y/X (TV) |
|---|---|---|---|---|---|---|---|
| 1.55 | −0.0568(6) | 0.682 | 10.8 | 11.5 | 3.71 | EXCLUDED / EXCLUDED | — |
| 2.32 | −0.0020(10) | 0.024 | 2.42 | 2.44 | 0.695 | EXCLUDED / NOT_EXCLUDED | — (centre half ≥ 1) |
| 3.10 | 0.0037(12) | 0.044 | 0.26 | 0.304 | 0.085 | **NOT_EXCLUDED / NOT_EXCLUDED** | 0.060 |

Noisy variants (β_n = 16, 64): same verdicts. Entry (H_TV = 1 crossing): L√σ ≈ 2.65 (β = 2.3: 2.54); first counted
NOT_EXCLUDED: TV 3.10, W₁ 2.32. Adjoint half NOT_EXCLUDED at every L with signal; the centre half binds below ~2.6, as at β = 2.3.
Every fitted |β_A| is below the certified W₁ ceiling (c3c: 0.275). Gates: photon and Z₂ deconfined passed; positive controls
NOT_EXCLUDED; flags: none.

**Caveat:** Leg C's pre-registered scaling check (β = 2.4 against β = 2.3 at equal L√σ) failed (`../../attempts/r3-blocked/PREREG.md`,
Result), so these numbers are indicative only; and the reading of §5.1 (block variable close to Haar noise in the adjoint channel,
the noise-limit trap) applies unchanged. The adjoint coarse plaquette ⟨χ₁⟩/3 was not re-measured at β = 2.4.
