# Proof note: the reduction "one bound at one scale" (companion to `BLUEPRINT-REDUCTION.md`, its §7)

Status: mathematics, 2026-11-21. No Lean. This note writes out the proofs that the blueprint sketches (its §2.3, §3.2–§3.4, §3.7,
§4.3), checks them adversarially, and records where the blueprint must change. Section numbers "B§x" refer to the blueprint.
Framework names (`productHaar`, `LinkDep`, `posHalfLinks`, `thetaConn`, `rp_plaquette_weight_gram`, `tv_single_link_le_tanh`, ...)
refer to `../formal/`.

---

## 0. Results at a glance

**Proved here (complete proofs, under the stated standing assumptions):**
- the elementary lemmas (DLR identity, propagation of oscillations, a covariance identity);
- the alignment lemma, in coupling form and in dual form (§3);
- **Theorem A** (§4) for every finite system: the torus, and boxes with frozen boundary conditions. It has an H (oscillation) and a W
  (Lipschitz) version, explicit constants, and constants independent of the volume, the boundary condition, and the number of blocks;
- **Theorem C** on the finite periodic lattice: a Cauchy–Schwarz doubling inequality (§6.4), its prefactor-free limit for limit points
  of torus correlations (§6.5), and the spectral statement in infinite volume (§6.6, modulo the standard Osterwalder–Seiler reconstruction);
- **Corollary B** at the lattice level (§7), and the continuum part under stated conditions;
- **non-vacuity** at strong coupling, in H and W form (§8).

**Corrections to the blueprint (each is argued below):**

| # | blueprint | correction |
|---|---|---|
| C1 | B§3.2 proof sketch (freeze the set S, contract on S^c, "geometric series on S") | Gap: rows near A with 0 < c_A(x) < c(x) do not contract either, and the S/S^c feedback loop is not controlled. The proof is replaced by a covariance telescoping over *all* blocks (§4.1). There is no S-set, and the constants improve: rate λ < log(1/γ)/D₁ with D₁ = ℓ + 1 for cubes (not ℓ + 2), no factor \|S_g\|. |
| C2 | B§3.2 "for every cube with every allowed boundary condition", Corollary A′ | Not implied by GDS for cube blocks: near the boundary of the box the blocks stick out. What is needed is GDS for the *truncated* family {V ∩ Ω} (hypothesis GDS^∂, §1.7). Single links and the torus are unaffected. |
| C3 | B§2.3 "the remaining obstruction is physical" | Alignment removes gauge freedom only at *interior* sites. A shell link that is the only outside link at its endpoint ("dangling", e.g. the outward link at every face-interior site of the thin cube) acts on the box by an exact boundary gauge rotation. Its coefficient is ≥ 2(d−1)·κ_β, with κ_β → 1 at weak coupling (§3.6), which forces ℓ ≳ 4(d−1)/γ. Fix: for gauge-invariant observables these links can be dropped from the shell (Lemma 3.6, Theorem A*), or use thick cubes (§3.8). |
| C4 | B§3.3 "spectrum ... lies in [0, e^{−λ}]" | Site RP (any φ, including admissible) gives spec(T) ⊂ [−e^{−λ}, e^{−λ}] on the vacuum complement, i.e. a gap for T². The bound [0, e^{−λ}] also needs T ≥ 0, which follows from link RP (proven for Wilson crossing plaquettes, β ≥ 0). On a finite periodic lattice the correlations are thermal traces, not vacuum matrix elements; the prefactor-free inequality is a statement about limit points (§6.7). |
| C5 | B§3.4 gap ≥ log(1/γ)/(L₀ + 3a) | log(1/γ)/(L₀ + 2a) for thin cubes. The continuum statement holds for observables with regular lattice approximants (§7). |
| C6 | B§1.2, B§3.2 Corollary A′, B§4.2 | Chatterjee 2021 assumes G a **closed connected** subgroup of U(n) and the Wilson action. So Corollary A′ holds for connected G under GDS_H^∂. The Ising-gauge test (Z₂, disconnected) is **not** a theorem as stated; it needs Chatterjee's Theorem 2.4 extended to finite groups. |
| C7 | B§4.1 "theorem, given Theorem A + Froehlich–Spencer" | A perimeter law alone does not contradict a gap (Z₂ has both). The rigorous photon test needs either a proof that U(1)₄ at weak coupling has no exponential clustering (not verified in FS82), or the Chatterjee route, which needs GDS_H^∂ and a perimeter law for the *Wilson* action (FS/Guth: Villain action). |
| C8 | B§3.7(1) admissible variant, fix (a) | With hard admissibility and topological sectors, the indicator of a sector has zero single-link oscillation. Then k_B(z) = ∞ whenever a boundary change reweights the sectors, so GDS fails for reasons unrelated to physics. Fix (c), a soft admissibility weight, is the one that works: φ > 0, and Theorem A applies verbatim (§9). |
| C9 | B§4.1 witness 2 (flux Φ ≈ π, odd witness F̄) | At Φ = π the interior sectors ±π are degenerate, so E[F̄] = 0 under both boundary conditions and the odd witness is blind. Use Φ ≈ π/2, or an even witness such as F̄² (§10.3). |
| C10 | B§1 citations | See §11 (Tomboulis–Yaffe title and pages; Martinelli–Olivieri part titles; Stroock–Zegarlinski titles; Chatterjee 2021 setting; FS action status). |

Verdicts are in §12.

---

## 1. Setting and definitions

### 1.1 Lattice

- 𝕃 is either the torus (ℤ/Nℤ)^d (as `FinLatticeSites d N`) or ℤ^d, with d ≥ 2.
- E is the set of positively oriented links (`LatticeLink`: a site and a direction), and P is the set of plaquettes (`LatticePlaquette`:
  a site and directions μ < ν). The plaquette holonomy is U_p = U_{l₀}U_{l₁}U_{l₂}^{−1}U_{l₃}^{−1}, as in `plaquetteHolonomy`.
- The midpoint of the link e = (x, μ) is m(e) = x + ½e_μ.
- dist(e, e') = ‖m(e) − m(e')‖_∞. On the torus each coordinate difference is taken mod N in [−N/2, N/2]. This is a metric on links,
  and dist(A, S) = min over A × S.
- Two distinct links are **neighbours** if they lie in a common plaquette.

  *Fact (N ≥ 3 or ℤ^d):* two distinct links lie in at most one common plaquette, and each link has exactly 6(d−1) neighbours. Proof:
  a plaquette is determined by two of its sides; each link lies in 2(d−1) plaquettes, each of which contributes 3 other links, and these
  are distinct. For N = 2 this fails: (x, μ) and (x + e_ν, μ) are opposite sides of two plaquettes. **Standing assumption: N ≥ 3.**

### 1.2 Group, representation, weight

- (G1) G is a compact, second-countable topological group with normalised Haar measure λ (`haarG`). λ is invariant under left and right
  translation and under inversion.
- (G2) `rep : G → U(n)` is a continuous unitary representation, and χ(g) = Re tr rep(g) ∈ [−n, n] (`gaugeReTr`). χ is a class function
  and χ(g^{−1}) = χ(g) (`gaugeReTr_inv_of_unitary`).
- (G3) For the W variant, ρ is a bi-invariant metric on G, continuous, with diam_ρ(G) < ∞. Example: ρ(a, b) = ‖rep(a) − rep(b)‖_F
  for a faithful representation, with diam ≤ 2√n. Bi-invariance implies ρ(a^{−1}, b^{−1}) = ρ(b, a). For the H variant, ρ is the
  discrete metric 1[a ≠ b].
- (Φ) The weight φ : ℝ → ℝ is measurable, with 0 < φ_min ≤ φ ≤ φ_max on [−n, n]. This covers Wilson φ(x) = e^{βx} (any real β), the
  Villain weight for U(1) (an even function of θ_p, hence a function of cos θ_p = χ(U_p)), and soft admissibility weights. Hard
  admissibility (φ = 0 allowed) is treated separately in §9. Note that (Φ) is stronger than `PlaqWeight`, which allows φ = 0.

### 1.3 Finite systems

A **finite system** (Ω, τ) consists of:
- a finite set Ω ⊂ E of *free* links;
- a frozen configuration τ ∈ G^{E∖Ω}.

Let P(Ω) be the plaquettes containing at least one free link. The measure on G^Ω is

  μ_{Ω,τ}(dσ) = Z^{−1} W(σ) λ^{⊗Ω}(dσ),   W(σ) = ∏_{p∈P(Ω)} φ(χ(U_p(σ, τ))),

with 0 < φ_min^{|P(Ω)|} ≤ Z. The torus is the case Ω = E, with τ empty; then μ is the normalised version of the measure in
`rp_plaquette_weight` (density ∏_p φ(xp p U) against `productHaar`). A box with a boundary condition is the case 𝕃 = ℤ^d, Ω finite.
We write μ for μ_{Ω,τ}; Cov is the covariance under μ.

### 1.4 Blocks, shells, specification, block averages

- For B ⊂ Ω nonempty, the **shell** ∂B is the set of links outside B that are neighbours of a link of B. Its links may be free or frozen.
- Write P(B) for the plaquettes touching B. For η ∈ G^{∂B}, the **specification** is

    q_B^η(dξ) = Z_B(η)^{−1} ∏_{p∈P(B)} φ(χ(U_p(ξ, η))) λ^{⊗B}(dξ),   ξ ∈ G^B.

  Every plaquette in P(B) has its links in B ∪ ∂B, so the density depends on the outside only through η, and Z_B(η) ≥ φ_min^{|P(B)|} > 0.
- The **block average** of a bounded measurable h : G^Ω → ℝ is

    P_B h(σ) = ∫ h(σ_{Ω∖B}, ξ) q_B^{σ_{∂B}}(dξ),

  where σ_{∂B} means σ on the free shell links and τ on the frozen ones. By Tonelli, P_B h is bounded and measurable, with
  ‖P_B h‖_∞ ≤ ‖h‖_∞.

### 1.5 Seminorms

For h : G^Ω → ℝ bounded and x ∈ Ω (write σ ∼_x σ' if σ and σ' agree off x):

- (H) δ_x(h) = sup{ |h(σ) − h(σ')| : σ ∼_x σ' };
- (W) L_x(h) = sup{ |h(σ) − h(σ')| / ρ(σ_x, σ'_x) : σ ∼_x σ', σ_x ≠ σ'_x } (possibly +∞);
- osc_B(h) = sup{ |h(σ) − h(σ')| : σ = σ' off B };
- h *depends only on* A ⊂ Ω (`LinkDep h A`) if h(σ) = h(σ') whenever σ = σ' on A. Then δ_x(h) = L_x(h) = 0 for x ∉ A.

For functions F on G^B (a block), δ_y(F) and L_y(F) for y ∈ B are defined the same way.

### 1.6 Boundary-influence coefficients (dual form)

For a block B and a free link z ∈ ∂B ∩ Ω:

- (H) k^H_B(z) = sup{ |q_B^η(F) − q_B^{η'}(F)| : η, η' ∈ G^{∂B} equal off z; F : G^B → ℝ bounded measurable with δ_y(F) ≤ 1 for all
  y ∈ B };
- (W) k^W_B(z) = sup{ |q_B^η(F) − q_B^{η'}(F)| / ρ(η_z, η'_z) : η, η' equal off z with η_z ≠ η'_z; F bounded measurable with
  L_y(F) ≤ 1 for all y ∈ B }.

The supremum runs over **all** η ∈ G^{∂B}, including values on links that are frozen in the given system. So k_B(z) depends only on
(B, z, φ, G). It does not depend on Ω or τ, and this is the whole mechanism of uniformity in the boundary condition. The definition
puts no gauge-invariance condition on F; by Lemma 3.4 adding one changes nothing.

*Homogeneity.* If k_B(z) < ∞, then for every bounded measurable F on G^B:
`|q^η F − q^{η'} F| ≤ k^H_B(z) · max_{y∈B} δ_y(F)`. If the max is m > 0, apply the definition to F/m. If m = 0, F is constant by
Lemma 2.3, and both sides vanish. The W case is the same with ρ(η_z, η'_z) on the right.

### 1.7 Block families and the hypotheses

A **block family** for (Ω, τ) is a finite indexed family ℬ = (B_i)_{i∈I} of nonempty subsets of Ω (repetitions allowed). Write:
- c(x) = #{i : x ∈ B_i} for the coverage, with c_− = min_{x∈Ω} c(x) and c_+ = max c(x). **We require c_− ≥ 1** (ℬ covers Ω).
- b = max_i |B_i|, D₀ = max_i diam(B_i), and D₁ = max{ dist(x, y) : i ∈ I, y ∈ B_i, x ∈ ∂B_i ∩ Ω }.
- M = |I|.

**Hypothesis GDS(ℬ, γ)** (H or W, according to the coefficient used): for every z ∈ Ω,

  Σ_{i : z ∈ ∂B_i} k_{B_i}(z) ≤ γ · c(z),   with 0 ≤ γ < 1.

**Where the families come from.**
- *ℤ^d families.* Let 𝒱 be a translation-invariant family of finite link sets in ℤ^d. Main cases: the **thin cubes** V_ℓ (all links with
  both ends in {0,…,ℓ}^d) and their translates; the **thick cubes** V_ℓ^+ (all links with at least one end in {0,…,ℓ}^d); the single
  links 𝒱₁ = {{e}}. GDS(𝒱, γ) means the inequality on ℤ^d for every link z, with c(z) = #{V ∈ 𝒱 : z ∈ V}.
- *Torus.* If N ≥ ℓ + 3, every V ∪ ∂V and every plaquette touching V embeds injectively into the torus (they use sites in
  {−1, …, ℓ+1}^d). So q_V^η and k_V(z) are the same on the torus as on ℤ^d, and GDS(𝒱, γ) on ℤ^d gives GDS(ℬ, γ) for ℬ = 𝒱 mod N.
- *Boxes with a boundary condition.* For finite Ω ⊂ E(ℤ^d), use the truncated family ℬ_Ω = (V ∩ Ω)_{V∈𝒱, V∩Ω≠∅}. Then c is unchanged
  on Ω. **Hypothesis GDS^∂(𝒱, γ)**: GDS(ℬ_Ω, γ) holds for every finite Ω, or for every Ω in a stated class (e.g. Chatterjee's cubes).
  For 𝒱₁, V ∩ Ω ∈ {V, ∅}, so GDS^∂ = GDS. For cubes, GDS^∂ is a genuinely stronger hypothesis: it is GDS for all box shapes that arise
  near faces, edges and corners. GDS does not imply it, because k_{V∩Ω} is a conditioned version of k_V and conditioning can increase
  influences.

**Cube constants.** For thin cubes V_ℓ: every link lies in c = ℓ(ℓ+1)^{d−1} translates, b = |V_ℓ| = dℓ(ℓ+1)^{d−1}, D₀ = ℓ, D₁ = ℓ+1.
(V-link midpoints have coordinates in [0, ℓ] and shell midpoints in [−1, ℓ+1].) For thick cubes: c = (ℓ+2)(ℓ+1)^{d−1},
b = d(ℓ+2)(ℓ+1)^{d−1}, D₀ = ℓ+1, D₁ ≤ ℓ + 3/2. For single links: c = b = 1, D₀ = 0, D₁ = 1.

**Per-link versus per-box form.** For a translation family generated by one shape V, GDS reads, for each direction μ:
Σ_{y∈∂V, dir y = μ} k_V(y) ≤ γ · #{y ∈ V : dir y = μ}. If the shape and the weight are invariant under the hypercubic group, the
d directional sums are equal, so the condition is equivalent to B§3.1's Σ_{y∈∂V} k_V(y) ≤ γ|V|. (The weight ∏φ(χ(U_p)) is
hypercubic-invariant: reversed links enter through g ↦ g^{−1}, and χ, λ, δ, L are invariant under inversion of a coordinate.)

---

## 2. Elementary lemmas

**Lemma 2.1 (factorisation and DLR).** For B ⊂ Ω and h bounded measurable: μ(P_B h) = μ(h).

*Proof.* Split λ^{⊗Ω} = λ^{⊗(Ω∖B)} ⊗ λ^{⊗B} (Fubini for the finite product). Write W(σ) = W_B(σ_B, σ_{∂B}) · R(σ_{Ω∖B}), where W_B is
the product over P(B) and R the product over P(Ω)∖P(B). R does not depend on σ_B, because a plaquette not touching B has no link in
B. Then

  Z·μ(P_B h) = ∫ R(σ') [∫ P_B h(σ') W_B(ξ', σ'_{∂B}) dξ'] dσ' = ∫ R(σ') P_B h(σ') Z_B(σ'_{∂B}) dσ'
       = ∫ R(σ') [∫ h(σ', ξ) W_B(ξ, σ'_{∂B}) dξ] dσ' = Z·μ(h),

with σ' ∈ G^{Ω∖B}. All integrands are bounded and measurable, and the measures are finite. ∎

**Lemma 2.2 (pull-out).** If f does not depend on the links of B, then P_B(f·h) = f·P_B h. In particular P_B f = f. *Proof:* f is
constant in ξ. ∎

**Lemma 2.3 (telescoping).** For σ, σ' ∈ G^Ω: |h(σ) − h(σ')| ≤ Σ_{x : σ_x ≠ σ'_x} δ_x(h) and
|h(σ) − h(σ')| ≤ Σ_x L_x(h) ρ(σ_x, σ'_x). Hence osc_B(h) ≤ Σ_{x∈B} δ_x(h) ≤ diam_ρ(G) Σ_{x∈B} L_x(h), and
sup_σ |h(σ) − μ(h)| ≤ Σ_x δ_x(h).

*Proof.* Change the differing coordinates one at a time. The last claim holds because μ(h) is an average of the values h(σ'). ∎

**Lemma 2.4 (oscillation against total variation).** For probability measures μ, ν and bounded measurable F:
|μF − νF| ≤ osc(F) · tv(μ, ν), where tv(μ, ν) = sup_A (μ(A) − ν(A)) as in `Influence.tv`.

*Proof.* μF − νF = ∫ (F − inf F) d(μ − ν) = ∫₀^{osc F} (μ − ν)({F − inf F > s}) ds ≤ osc(F)·tv(μ, ν). Exchanging μ and ν gives
the bound with tv(ν, μ) = tv(μ, ν) (probability measures). ∎ (Not yet in `Influence`; blueprint L4 asks for it.)

**Lemma 2.5 (propagation).** Assume (Φ). Let B ⊂ Ω be a block with k_B(z) < ∞ for every z ∈ ∂B ∩ Ω, and h bounded measurable. For
every x ∈ Ω:

  (H) δ_x(P_B h) ≤ 1[x ∉ B]·δ_x(h) + 1[x ∈ ∂B]·k^H_B(x)·max_{y∈B} δ_y(h);
  (W) L_x(P_B h) ≤ 1[x ∉ B]·L_x(h) + 1[x ∈ ∂B]·k^W_B(x)·max_{y∈B} L_y(h).

*Proof.* Take σ ∼_x σ'.
- If x ∈ B, then P_B h(σ) = P_B h(σ'), since P_B h does not read σ_B.
- If x ∉ B ∪ ∂B, the kernels agree (q^{σ_{∂B}} = q^{σ'_{∂B}}), so |P_B h(σ) − P_B h(σ')| ≤ ∫ |h(σ_{Ω∖B}, ξ) − h(σ'_{Ω∖B}, ξ)| dq
  ≤ δ_x(h).
- If x ∈ ∂B, write η = σ_{∂B}, η' = σ'_{∂B} and F(ξ) = h(σ'_{Ω∖B}, ξ). Then

    P_B h(σ) − P_B h(σ') = ∫ [h(σ_{Ω∖B}, ξ) − F(ξ)] q^η(dξ) + [q^η(F) − q^{η'}(F)].

  The first term is ≤ δ_x(h). F is bounded and measurable (a section of a measurable function), with δ_y(F) ≤ δ_y(h) for y ∈ B. By
  homogeneity (§1.6) the second term is ≤ k^H_B(x) max_{y∈B} δ_y(h). For W the same two terms are each bounded by a multiple of
  ρ(σ_x, σ'_x). ∎

**Lemma 2.6 (block covariance identity).** For bounded measurable f, h and any block B:
μ(f·(h − P_B h)) = μ((f − P_B f)·(h − P_B h)).

*Proof.* We need μ(P_B f·(h − P_B h)) = 0. P_B f does not depend on σ_B, so by Lemmas 2.1 and 2.2,
μ(P_B f·h) = μ(P_B(P_B f·h)) = μ(P_B f·P_B h). ∎

(Lemma 2.6 is the only place where the self-adjointness of P_B in L²(μ) enters, and it needs no L² theory.)

---

## 3. Gauge structure and the alignment lemma

### 3.1 Gauge group and its action

A gauge transformation g ∈ G^{sites} acts by (g·U)_e = g_{s(e)} U_e g_{t(e)}^{−1} (`gaugeTransformConnection`). Then U_p ↦ g_x U_p g_x^{−1},
where x is the base corner of p, so χ(U_p) is invariant. For a finite system, 𝒢_Ω is the group of g with g_x = 1 at every site x
incident to a frozen link. These g fix τ, act link-wise on G^Ω by Haar-preserving maps (ξ ↦ aξb), and preserve W. So μ_{Ω,τ} is
𝒢_Ω-invariant. On the torus, 𝒢_Ω is the full gauge group.

### 3.2 Relative gauge group of a block

For a block B, let int(B) be the set of sites all of whose 2d incident links lie in B, and K_B = G^{int(B)} (g = 1 off int(B)).

**Lemma 3.1.** K_B acts on G^B link-wise, fixes every link outside B, and q_B^η is K_B-invariant for every η.

*Proof.* A link e ∉ B has no endpoint in int(B), since otherwise e would be an incident link of an interior site, hence in B. So
k ∈ K_B fixes the shell. On a link e ∈ B, k acts as ξ_e ↦ k_{s(e)} ξ_e k_{t(e)}^{−1}, independently of η. The product Haar measure is
invariant (left and right invariance per coordinate), and every plaquette weight is invariant (class function). ∎

### 3.3 Covariance under the full gauge group

**Lemma 3.2.** For any gauge transformation g (on all sites), q_B^{g·η} = (g|_B)_* q_B^η, where g|_B acts on G^B link-wise. Hence
|q^{gη}(F) − q^{gη'}(F)| = |q^η(F∘g) − q^{η'}(F∘g)|, with δ_y(F∘g) = δ_y(F), L_y(F∘g) = L_y(F) and ρ((gη)_z, (gη')_z) = ρ(η_z, η'_z).
So the supremum defining k_B(z) is a supremum over orbits of pairs (η, η') under the *diagonal* action of the full gauge group.

*Proof.* Substitute ξ = g·ζ in q^{gη}(F): the Haar measure is preserved and W_B(gζ, gη) = W_B(ζ, η). For the seminorms: g acts
link-wise and bijectively, so pairs differing at y correspond to pairs differing at y; ρ is bi-invariant. ∎

### 3.4 The alignment lemma (coupling form)

Let X = G^B with ρ_B(U, U') = Σ_{e∈B} ρ(U_e, U'_e), and let ρ̄_B(U, U') = min_{k∈K_B} ρ_B(k·U, U'). K acts by ρ_B-isometries
(bi-invariance), so ρ̄ is a pseudometric: symmetric because ρ_B(kU, U') = ρ_B(U, k^{−1}U'), and satisfying the triangle inequality by
composing minimisers. The minimum exists: K is compact and k ↦ ρ_B(kU, U') is continuous.

For a lower semicontinuous cost c, W_c(μ, ν) = inf over couplings π of μ and ν of ∫ c dπ.

**Lemma 3.3 (alignment).** Assume (G1), and that ρ is continuous and bi-invariant. Let μ, ν be K_B-invariant Borel probability measures
on X. Then W_{ρ_B}(μ, ν) = W_{ρ̄_B}(μ, ν).

*Measurability conditions used:*
1. K is compact, second countable and metrizable, so it has a countable dense subset {k_j}.
2. The action K × X → X is continuous.
3. ρ̄_B = inf_j ρ_B(k_j ·, ·) is Borel, since k ↦ ρ_B(kU, U') is continuous.

*Proof.* "≥" holds because ρ̄ ≤ ρ_B.

"≤": fix ε > 0 and a coupling π of (μ, ν). Define κ(U, U') = k_{j*}, where j* is the least j with ρ_B(k_j U, U') < ρ̄_B(U, U') + ε. Such
j exists by density and continuity, and κ is Borel: each event {j* = j} is defined by countably many Borel inequalities. No
measurable-selection theorem is needed. Let ĥ be Haar-distributed on K, independent of (U, U') ∼ π, and set X₁ = ĥκ(U, U')·U and
X₂ = ĥ·U'.

- *X₁ ∼ μ.* For bounded Borel F: E F(X₁) = E[∫_K F(hκ(U,U')U) dh] = E[∫_K F(hU) dh] = ∫_X ∫_K F(hU) dh μ(dU) = μ(F). The second
  equality uses right invariance of Haar on K for the fixed element κ(U, U'), the third Fubini, the last K-invariance of μ.
- *X₂ ∼ ν.* Same argument without κ.
- *Cost.* ρ_B(X₁, X₂) = ρ_B(κU, U') < ρ̄_B(U, U') + ε, since ĥ acts by an isometry.

So W_{ρ_B}(μ, ν) ≤ ∫ ρ̄ dπ + ε. Take the infimum over π and let ε → 0. ∎

*Gribov copies.* Neither proof uses uniqueness of the minimiser, and the dual form below uses no gauge fixing at all. Multiple global
minimisers, or local minima found numerically, can only make a *measured* ρ̄ larger. That is an upper bound, the safe direction for
"GDS holds" (B§5.1).

### 3.5 Alignment in dual form

**Lemma 3.4.** For F : X → ℝ bounded measurable, let F̄(U) = ∫_K F(k·U) dk. Then:
1. F̄ is bounded, measurable and K-invariant;
2. q_B^η(F̄) = q_B^η(F) for every η;
3. δ_y(F̄) ≤ δ_y(F) and L_y(F̄) ≤ L_y(F) for every y ∈ B.

Consequently k^H_B(z) and k^W_B(z) are unchanged if the supremum is restricted to K_B-invariant F. So "relatively gauge-invariant"
may be added to or dropped from the definition (B§3.1).

*Proof.*
1. Measurability by Fubini; invariance by right invariance of dk.
2. Fubini and Lemma 3.1.
3. k acts link-wise, so U ∼_y U' implies kU ∼_y kU' and ρ((kU)_y, (kU')_y) = ρ(U_y, U'_y). Hence
   |F̄(U) − F̄(U')| ≤ ∫ |F(kU) − F(kU')| dk ≤ δ_y(F) (respectively L_y(F) ρ(U_y, U'_y)). ∎

**Relation to the coupling coefficient.** A function F on X has L_y(F) ≤ 1 for all y iff it is 1-Lipschitz for ρ_B (by Lemma 2.3 for
one direction; the other is trivial). It is moreover K-invariant iff it is 1-Lipschitz for ρ̄_B. So

  k^W_B(z) ≤ sup_{η∼_zη'} W_{ρ_B}(q^η, q^{η'}) / ρ(η_z, η'_z) = sup_{η∼_zη'} W_{ρ̄_B}(q^η, q^{η'}) / ρ(η_z, η'_z),

and equality holds by Kantorovich duality (compact metric space). The middle expression is the Dobrushin–Shlosman coefficient. Any
coupling, in particular a coupled heat-bath pair after relative Landau alignment, gives an upper bound on k. This confirms B§5.1.

### 3.6 What alignment does not remove: boundary sites

K_B contains only *interior* sites. Call a free link z ∈ ∂B **dangling** (for B) if one of its endpoints x has all its other 2d − 1
incident links in B. Then x ∉ int(B), because z ∉ B.

**Lemma 3.5 (a dangling link acts by a boundary gauge rotation).** Let z be dangling at x, and let η, η' ∈ G^{∂B} differ only at z. Let
g_x ∈ G be the element with (g_x·η)_z = η'_z: g_x = η'^{−1}_z η_z if z ends at x, and g_x = η'_z η_z^{−1} if z starts at x. Let g be the
gauge transformation equal to g_x at x and 1 elsewhere. Then g·η = η', and q_B^{η'} = (g|_B)_* q_B^η.

*Proof.* Among the links at x, only z lies outside B, so g changes η only at z. Apply Lemma 3.2. ∎

So the influence of a dangling z is that of rigidly rotating the B-links at x. Rotating the link from x to an interior site is absorbed
by K_B (its law is invariant under the interior end), but links from x to other *boundary* sites are not.

**Example (exact, Z₂, d = 2, thin square ℓ = 2, β = ∞).** Take the face-interior site x = (0,1), with z the outward link
(−1,1) → (0,1), and the cold boundary condition. At β = ∞ every plaquette touching B must equal +1. The plaquette (−1,0; 1,2) has three
cold shell links and the face link (0,0) → (0,1), so that face link is +1; likewise (0,1) → (0,2). With z flipped, both face links are −1.
For F = (σ_{(0,0)→(0,1)} + σ_{(0,1)→(0,2)})/2 (so δ_y(F) ≤ 1), |q^η F − q^{η'} F| = 2. K_B is generated by the single interior site
(1,1) and does not touch these links. So k^H_B(z) ≥ 2 = 2(d−1).

**General lower bound.** Let x be a face-interior site of the thin cube, so there are 2(d−1) face links at x, both ends on the face.
F(ξ) = Σ_{face e at x} ψ_e(ξ_e) with ψ_e 1-Lipschitz is K_B-invariant. By Lemma 3.5, q^{η'}(F) − q^η(F) is a sum of terms
q^η(ψ_e(g_x^{±}ξ_e)) − q^η(ψ_e(ξ_e)). Each such term is at most W₁(law ξ_e, law g_x^± ξ_e) ≤ ρ(g_x, 1) = ρ(η_z, η'_z), and the bound
is attained in the limit where the law of ξ_e concentrates. So

  k^W_B(z) ≥ 2(d−1)·κ_β,   κ_β = inf over the face links of W₁(law ξ_e, law g ξ_e)/ρ(g, 1) for small g (sup over η).

As β → ∞ with cold η, the face links are pinned by plaquettes whose other three links are frozen, so κ_β → 1. The same holds for the H
variant, with total variation in place of W₁.

**Quantitative consequence.** The thin cube has 2d(ℓ−1)^{d−1} face-interior sites, each with one dangling z. Their contribution alone
gives Σ_{y∈∂V} k(y) ≥ 4d(d−1)κ_β(ℓ−1)^{d−1}, against the budget γ|V| = γdℓ(ℓ+1)^{d−1}. So GDS needs, roughly, ℓ ≳ 4(d−1)κ_β/γ:
**ℓ ≳ 24 at d = 4, γ = ½, weak coupling**, from a pure-gauge term. This is a surface effect, not a failure of the criterion, but it
matters for the numerics of B§5 (planned ℓ = 8) and contradicts B§2.4's claim that only physics remains.

### 3.7 Dangling links are invisible to gauge-invariant observables

**Lemma 3.6.** Let h : G^Ω → ℝ be bounded measurable and 𝒢_Ω-invariant. Then:
1. P_B h is 𝒢_Ω-invariant;
2. if z is dangling for B, P_B h does not depend on σ_z: δ_z(P_B h) = L_z(P_B h) = 0.

*Proof.*
1. For g ∈ 𝒢_Ω, (P_B h)(gσ) = ∫ h(gσ_{Ω∖B}, ξ) q^{gσ}(dξ) = ∫ h(g·(σ_{Ω∖B}, ζ)) q^σ(dζ) = P_B h(σ), by Lemma 3.2 and invariance of h.
2. All links at x are free (z and B-links), so the g of Lemma 3.5 lies in 𝒢_Ω. With σ' = σ except at z, the configuration
   (σ'_{Ω∖B}, g ζ) equals g·(σ_{Ω∖B}, ζ). So P_B h(σ') = ∫ h(σ'_{Ω∖B}, gζ) q^σ(dζ) = ∫ h(g·(σ_{Ω∖B}, ζ)) q^σ(dζ) = P_B h(σ). ∎

Let ∂*B = ∂B ∖ {dangling links}. **Hypothesis GDS\*(ℬ, γ)**: Σ_{i : z ∈ ∂*B_i} k_{B_i}(z) ≤ γc(z) for all z ∈ Ω. GDS* is weaker than
GDS, and it removes the pure-gauge surface term of §3.6. By Lemma 3.6, for invariant h Lemma 2.5 holds with ∂*B in place of ∂B: for
dangling x, δ_x(P_B h) = 0 ≤ δ_x(h).

### 3.8 Thick cubes

For V_ℓ^+ (links with at least one end in C = {0,…,ℓ}^d): int(V^+) = C. Every outside site y adjacent to C has exactly one V^+-link and at
least 2(d−1) ≥ 2 shell links, since (y, μ) and (y − e_μ, μ) for μ ≠ the normal direction are both in the shell. So V^+ has **no dangling
links**, and every V^+-link has an interior endpoint. The rigid rotation of §3.6 is absent. A partial, physical response to a single
shell change remains. Chatterjee's free set for a cube (edges of B not on its boundary, §5) is of this thick type.

---

## 4. Theorem A

### 4.1 Statement and proof

**Theorem A.** Assume (G1), (G2), (Φ), and, for W, (G3). Let (Ω, τ) be a finite system, ℬ a block family with c_− ≥ 1, and assume
GDS(ℬ, γ) with γ < 1. Let λ ≥ 0 with ρ_λ := γe^{λD₁} < 1. Let f be bounded measurable depending only on A ⊂ Ω, and g depending only on
S_g ⊂ Ω. Put κ(f) = Σ_{i : B_i ∩ A ≠ ∅} osc_{B_i}(f). Then κ(f) ≤ c_+ Σ_{a∈A} δ_a(f) ≤ 2c_+|A|·‖f‖_∞, and:

  (H) |Cov(f, g)| ≤ b/(c_−(1 − ρ_λ)) · κ(f) · max_{x∈S_g} δ_x(g) · e^{−λ(dist(A,S_g) − D₀)};
  (W) |Cov(f, g)| ≤ b·diam_ρ(G)/(c_−(1 − ρ_λ)) · κ(f) · max_{x∈S_g} L_x(g) · e^{−λ(dist(A,S_g) − D₀)}   (g Lipschitz in each link).

No constant depends on Ω, τ, N or M. Any rate λ < log(1/γ)/D₁ is allowed.

*Proof* (H; W is identical with L in place of δ and the factor diam_ρ(G) from Lemma 2.3). Let P = M^{−1} Σ_i P_{B_i}, put
v_s(x) = δ_x(P^s g) for x ∈ Ω, w(x) = e^{−λ dist(x, S_g)} > 0, and N_s = max_x v_s(x)/w(x).

*Step 1 (contraction).* By Lemma 2.5 and subadditivity of δ_x under convex combinations:

  v_{s+1}(x) ≤ (1 − c(x)/M) v_s(x) + M^{−1} Σ_{i : x ∈ ∂B_i} k_{B_i}(x) max_{y∈B_i} v_s(y).

The first term counts the M − c(x) blocks not containing x; x ∈ ∂B implies x ∉ B. For x ∈ ∂B_i and y ∈ B_i, dist(x, y) ≤ D₁, so
w(y) ≤ e^{λD₁} w(x) by the triangle inequality. With v_s ≤ N_s w and GDS:

  v_{s+1}(x) ≤ N_s w(x) [1 − c(x)/M + γ e^{λD₁} c(x)/M] ≤ N_s w(x) (1 − c_−(1 − ρ_λ)/M).

So N_{s+1} ≤ θN_s with θ = 1 − c_−(1−ρ_λ)/M ∈ [0, 1). Initially v₀ = 0 off S_g and w = 1 on S_g, so N₀ = max_{x∈S_g} δ_x(g). This
step is where **c_− ≥ 1** enters: it is the contraction rate. With an uncovered link, c(x) = 0, there is no contraction at x (B§7, point 2).

*Step 2 (convergence).* By Lemmas 2.1 and 2.3, sup_σ |P^t g(σ) − μ(g)| ≤ Σ_x v_t(x) ≤ N_t |Ω| ≤ θ^t N₀|Ω| → 0. So
μ(f P^t g) → μ(f)μ(g).

*Step 3 (telescoping the covariance).* Cov(f, g) = Σ_{s≥0} μ(f(P^s g − P^{s+1} g)). By Lemma 2.6, each term equals
M^{−1} Σ_i μ((f − P_{B_i} f)(h_s − P_{B_i} h_s)) with h_s = P^s g. Since f depends only on A, f − P_B f = 0 unless B ∩ A ≠ ∅, and
|f − P_B f| ≤ osc_B(f). Also |h_s − P_B h_s| ≤ osc_B(h_s) ≤ Σ_{y∈B} v_s(y) ≤ N_s Σ_{y∈B} w(y). For y ∈ B with B ∩ A ∋ a,
dist(a, S_g) ≤ D₀ + dist(y, S_g), so w(y) ≤ e^{−λ(dist(A,S_g) − D₀)}. Hence

  |Cov(f, g)| ≤ (Σ_s N_s / M) · κ(f) · b · e^{−λ(dist(A,S_g) − D₀)},   Σ_s N_s ≤ N₀/(1 − θ) = N₀ M/(c_−(1−ρ_λ)).

*Step 4 (bounding κ).* κ(f) ≤ Σ_{B∩A≠∅} Σ_{a∈A∩B} δ_a(f) ≤ c_+ Σ_a δ_a(f), by Lemma 2.3. ∎

*Remarks.*
- The block count M cancels, so nothing depends on the system size.
- The proof never freezes coordinates, never conditions, and uses no couplings: it is Lemmas 2.1–2.6 plus finite sums and one
  geometric limit. In Lean the limit can be avoided by keeping the remainder ‖f‖θ^tN₀|Ω| and concluding by `le_of_forall_pos_le_add`.
- *Sanity checks.*
  - Product measure: k ≡ 0, so γ = 0 and λ may be arbitrary; the bound then forces Cov = 0 when dist(A, S_g) > D₀. Correct.
  - Single links: D₀ = 0, D₁ = 1, b = c = 1, giving Dobrushin's estimate |Cov| ≤ Σ_a δ_a(f) max δ(g) e^{−λ dist}/(1 − γe^λ).

### 4.2 Instances

1. **Torus.** If GDS(𝒱, γ) holds on ℤ^d and N ≥ ℓ + 3, the bound holds on every such torus with the same constants. For thin cubes:
   b/c_− = d, κ(f) ≤ ℓ(ℓ+1)^{d−1} Σ_a δ_a(f), and e^{λD₀} = e^{λℓ} ≤ γ^{−ℓ/(ℓ+1)} ≤ 1/γ.
2. **Boxes with a boundary condition.** Under GDS^∂(𝒱, γ), the bound holds for every finite Ω ⊂ E(ℤ^d) and every τ, uniformly.
   Under plain GDS this is **not proved** (C2): links near ∂Ω lie in blocks that stick out of Ω, and the contraction in Step 1 needs
   *every* block containing x to be resampled. For 𝒱₁ (Dobrushin) there is no difference.
3. **Single links** (§8).

### 4.3 Gauge-invariant version

**Theorem A\*.** Under GDS*(ℬ, γ) instead of GDS, the bounds of Theorem A hold for every bounded measurable f and every 𝒢_Ω-invariant g.

*Proof.* The class of bounded measurable 𝒢_Ω-invariant functions is preserved by every P_B (Lemma 3.6.1). For such h, Lemma 2.5 holds with
∂*B (Lemma 3.6.2). Steps 1–4 apply to h_s = P^s g, all of which are invariant. f enters only through Lemma 2.6 and osc_B(f). ∎

### 4.4 Which observables, and how uniformity enters

- **Under GDS:** all bounded measurable f, g (H), or bounded f and per-link Lipschitz g (W). There is no gauge invariance condition, and
  no locality beyond finite supports; the constant grows with κ(f), i.e. with the support of f. The roles of f and g can be exchanged
  to put the smaller support in κ.
- **Under GDS\*:** g must be invariant under 𝒢_Ω (globally gauge invariant on the torus; for a box, invariant under transformations
  trivial at sites touching the frozen boundary). Examples: Wilson loops, plaquette functions, smeared field strengths. On a box,
  open Wilson lines between frozen-boundary sites are also 𝒢_Ω-invariant.
- **Uniformity** in the volume and in the boundary condition enters only through k_B(z), which is a supremum over all of G^{∂B}, and
  through the family constants. The proof never sees τ except inside kernels covered by that supremum.

### 4.5 What was wrong with the blueprint sketch

B§3.2 restricted the average to blocks avoiding A and set S = A ∪ {links in no such block}. A link x with 0 < c_A(x) < c(x) is not in
that S, but its row has diagonal 1 − c_A(x)/M and off-diagonal mass up to γc(x)e^{λD}/M. So it contracts only if
c_A(x) > γe^{λD}c(x), which fails near A. Enlarging S to {c_A < c} keeps the diagonal ≥ 1 on S. Then v grows on S by inflow from blocks
in ℬ_A that contain S-points, and S^c rows are fed back by those same blocks. A crude bound grows like (1 + O(1/M))^t, which is
unbounded. The claim "geometric series on S" would need an argument the sketch does not give. The proof above avoids freezing
altogether.

---

## 5. Corollary A′ (Chatterjee's Definition 2.3)

Checked in arXiv:2006.16229v5 (§2.1, §2.4):
- **Setting.** G is a closed connected subgroup of U(n), with the Wilson action e^{β Σ Re Tr ω_p} on ℤ^d.
- **Local functions.** f is *supported on an edge e* if f depends only on ω_u for u neighbours of e.
- **Distance.** dist(f, g) is the Euclidean distance between the midpoints of the supporting edges.
- **Cubes and boundaries.** A cube is a translate of {0,…,N}^d; a boundary condition δ assigns G-values to the boundary edges of B.
- **Definition 2.3.** There are K₁, K₂ depending only on G, β, d such that |⟨fg⟩_{B,δ} − ⟨f⟩⟨g⟩| ≤ K₁e^{−K₂dist(f,g)} for every cube,
  every δ, and every local f, g with values in [−1, 1]. Gauge invariance is not required.
- **Theorem 2.4.** Definition 2.3 implies unbroken centre symmetry, and the area law for every Gibbs measure if π acts nontrivially
  on the centre.

**Corollary A′.** Let G be a closed connected subgroup of U(n), with the Wilson weight. If GDS_H^∂(𝒱, γ) holds for the class of free sets
of cubes, then Definition 2.3 holds with K₂ = λ/√d for any λ < log(1/γ)/D₁, and

  K₁ = 4(6d−5)·b c_+/(c_−(1−ρ_λ)) · e^{λ(D₀+2)}.

*Proof.* Theorem A(H) with (Ω, τ) = (free edges of B, δ). A local f has |A| ≤ 1 + 6(d−1) = 6d−5, δ_a(f) ≤ 2 and δ_x(g) ≤ 2. Supports
lie within ∞-distance 1 of their edge midpoints, so dist(A, S_g) ≥ dist(f,g)/√d − 2. ∎

Then Theorem 2.4 gives unbroken centre symmetry and the area law **for connected G**. I read Chatterjee's "boundary edges" as edges with
both ends on the cube's surface; Theorem A holds for any Ω, so the reading does not matter as long as GDS^∂ is stated for the right Ω.
For **finite G (Z₂)**, Theorem 2.4 is not stated. Chatterjee's §2.4 applies his Theorem 2.2 to finite groups informally ("If this is
true ..."). This affects the Ising-gauge test (§10.3).

GDS_W does not give Definition 2.3, which asks for bounded rather than Lipschitz functions; this matches B§3.6.

---

## 6. Theorem C (reflection positivity: decay ⇒ gap, no prefactor)

### 6.1 Setting

- Torus (ℤ/Nℤ)^d with N even and N ≥ ℓ + 3, direction 0 is time, and μ = μ_N satisfies (Φ).
- Θ is the site reflection t ↦ −t (`thetaConn`): (ΘU)(l) = tw_l(U(mir l)), with tw = inversion on temporal links.
- S_j is time translation: (S_j U)(l) = U(l + je₀).
- 𝒜_{[0,s]} is the set of bounded measurable F depending only on spatial links with 0 ≤ t ≤ s and temporal links from t to t+1
  with 0 ≤ t < s. For F ∈ 𝒜_{[0,s]} and s ≤ N/2, F depends on `posHalfLinks`.
- F_j = F∘S_j depends on the slab [j, j+s].

**Facts used.**
- (i) μ is Θ-invariant: `measurePreserving_thetaConn`, plus W∘Θ = W (reindex the plaquettes by `mirrorPlaq` and use `xp_thetaConn`).
- (ii) μ is S_j-invariant: S_j permutes coordinates (`MeasureTheory.measurePreserving_piCongrLeft`), and W∘S_j = W by reindexing
  plaquettes. *This is not yet in the framework; it is a new small lemma.*
- (iii) S_k∘Θ = Θ∘S_{−k}. Check: mir(l + ke₀) = mir(l) − ke₀ for spatial links (t ↦ −t) and for temporal links (start t ↦ −t−1), and
  tw depends only on the direction.
- (iv) **Site RP** (`rp_plaquette_weight_gram`, valid for every `PlaqWeight` φ, including admissible): for F₁, …, F_m depending on
  `posHalfLinks` and real z_i, Σ z_i z_j μ(F_i·(F_j∘Θ)) ≥ 0 (divide the theorem by Z > 0). With (i), the form
  ⟨F, G⟩ := μ(F·(G∘Θ)) is symmetric and positive semidefinite, so it satisfies Cauchy–Schwarz.

### 6.2 Hankel structure

For F ∈ 𝒜_{[0,s]}, define F̊ = F − μ(F) and H(m) = μ(F̊_m·(F̊∘Θ)) = Cov(F_m, F∘Θ), for m ≥ 0.

**Lemma 6.1.** For j, k ≥ 0 with j + s ≤ N/2 and k + s ≤ N/2: ⟨F̊_j, F̊_k⟩ = H(j+k). In particular H(2j) ≥ 0.

*Proof.* By (iii), F_k∘Θ = F∘Θ∘S_{−k}, so μ(F_j·(F_k∘Θ)) = μ([F∘S_{j+k}·F∘Θ]∘S_{−k}) = μ(F_{j+k}·(F∘Θ)) by (ii). The constants are
handled by μ(F_m) = μ(F) (ii) and μ(F∘Θ) = μ(F) (i). F̊_j and F̊_k depend on the closed positive half, so (iv) applies. ∎

### 6.3 Doubling

**Lemma 6.2.** If r ≥ 1 and 2^{r−1}m + s ≤ N/2, then |H(m)| ≤ H(0)^{1−2^{−r}} · H(2^r m)^{2^{−r}}.

*Proof.* Cauchy–Schwarz for ⟨·,·⟩ with Lemma 6.1 gives H(j+k)² ≤ H(2j)H(2k). With (j, k) = (0, 2^i m), for 0 ≤ i ≤ r−1:
|H(2^i m)| ≤ H(0)^{1/2} H(2^{i+1}m)^{1/2}. Every right-hand factor is H at an even argument, hence ≥ 0. Composing the r inequalities
gives the exponents ½ + ¼ + … + 2^{−r} = 1 − 2^{−r} on H(0). ∎

### 6.4 Theorem C on the finite periodic lattice

**Theorem C.** Assume GDS_H(𝒱, γ) on ℤ^d (or GDS_W with F Lipschitz in each link). Let λ < log(1/γ)/D₁ and F ∈ 𝒜_{[0,s]}. Put
C_F = b/(c_−(1−ρ_λ)) · c_+ Σ_a δ_a(F) · max_x δ_x(F) · e^{λD₀}, with δ in place of L·diam for W. Then for every even N ≥ ℓ + 3,
every m ≥ 1 and every r ≥ 1 with N ≥ 2^{r+1}m + 2s:

  |H_N(m)| ≤ H_N(0)^{1−2^{−r}} · C_F^{2^{−r}} · e^{−λm}.

*Proof.* Lemma 6.2 applies, since 2^{r−1}m + s ≤ N/2. Bound H_N(2^r m) = Cov(F_{2^r m}, F∘Θ) by Theorem A on the torus, with f = F_{2^r m}
and g = F∘Θ. The time gap between the slabs [2^r m, 2^r m + s] and [−s, 0] is 2^r m, and the wrap-around gap N − 2^r m − 2s is
≥ 2^r m. So dist(A, S_g) ≥ 2^r m. The seminorm sums of F_{2^r m} and F∘Θ equal those of F, since translation and reflection act
link-wise and bijectively. ∎

C_F carries the support of F, the lattice spacing (through b, c_±, D₀) and the box size. It enters only as C_F^{2^{−r}}.

### 6.5 Removing the prefactor (limit points; real analysis only)

**Corollary C1.** Let N_k → ∞ (even) be a sequence along which H_{N_k}(m) → h(m) and H_{N_k}(0) → h(0). Such subsequences exist
because |H_N| ≤ 4‖F‖²_∞. Then |h(m)| ≤ h(0)·e^{−λm}.

*Proof.* Fix r. For large k, Theorem C applies; pass to the limit, using continuity of x ↦ x^a on [0, ∞) for a > 0, to get
|h(m)| ≤ h(0)^{1−2^{−r}} C_F^{2^{−r}} e^{−λm}. Let r → ∞: if C_F > 0 then C_F^{2^{−r}} → 1; if C_F = 0 the bound is 0. ∎

This is the prefactor-free inequality. It is pure real analysis and the right Lean target (blueprint L9): it needs no measure-theoretic
limit, no spectral theorem, and no infinite volume.

### 6.6 The spectral statement (infinite volume)

**Lemma 6.3 (limit states).** For a finite link set Λ ⊂ E(ℤ^d), the marginal of μ_N on Λ (for N large) has density ≤ (φ_max/φ_min)^{|P(Λ)|}
with respect to λ^{⊗Λ}. This follows from Lemma 2.1 applied to B = Λ, since q_Λ^η has that density bound. Bounded densities are weak-*
precompact in L^∞(λ^{⊗Λ}). A diagonal subsequence N_k and Kolmogorov extension then give a probability measure μ_∞ on G^{E(ℤ^d)} with
μ_{N_k}(F) → μ_∞(F) for every bounded measurable local F. (Standard; sketched, not formalised.)

μ_∞ is translation- and Θ-invariant and site-RP (limits of (i), (ii), (iv)). For Wilson weights with β ≥ 0 it is also link-RP
(`rp_plaquette_weight_link` in the limit).

**Osterwalder–Seiler reconstruction** (standard; stated, not reproved):
- ℋ is the completion of 𝒜₊^{loc}/𝒩 under ⟨F, G⟩ = μ_∞(F·(G∘Θ)), where 𝒜₊^{loc} is the bounded local functions of t ≥ 0.
- T(F̂) := (F₁)^ is well defined and is a self-adjoint contraction. The norm bound ‖(F₁)^‖² = μ(F₂·ΘF) ≤ ‖F̂‖² is Lemma 6.2 for the
  non-connected form with r → ∞. Symmetry follows from (ii) and (iii).
- Ω = 1̂ satisfies TΩ = Ω, and ⟨Ω, F̂⟩ = μ_∞(F).

**Theorem C2.** Assume GDS_H(𝒱, γ) on ℤ^d (or GDS_W). For every limit state μ_∞ of Lemma 6.3:
1. spec(T|_{Ω^⊥}) ⊂ [−γ^{1/D₁}, γ^{1/D₁}];
2. ker(T − 1) = ℂΩ (unique vacuum);
3. if moreover link RP holds (Wilson weight, β ≥ 0), T ≥ 0 and spec(T|_{Ω^⊥}) ⊂ [0, γ^{1/D₁}].

So the lattice Hamiltonian H = −½ log T² has gap ≥ log(1/γ)/D₁ in lattice units (−log T under link RP).

*Proof.* For F ∈ 𝒜_{[0,s]}, ψ = (F̊)^ ∈ Ω^⊥, and ⟨ψ, T^m ψ⟩ = h(m), which satisfies |h(m)| ≤ ‖ψ‖²e^{−λm} by Corollary C1 applied in the
limit state. (Theorem A passes to the limit term by term, because its constants do not depend on N.) Let ν_ψ be the spectral measure of
ψ on [−1, 1]. Then ∫x^{2m} dν_ψ ≤ ‖ψ‖²e^{−2λm} for all m, which forces ν_ψ({|x| > e^{−λ}}) = 0. Such ψ are dense in Ω^⊥. For the H
variant this holds by construction; for W, Lipschitz local functions are L²(μ_∞)-dense and ‖F̂ − Ĝ‖ ≤ ‖F − G‖_{L²(μ_∞)} by
Cauchy–Schwarz and Θ-invariance. The spectral projection E({|x| > e^{−λ}}) is bounded and vanishes on a dense subset of Ω^⊥, so it
vanishes on Ω^⊥. Let λ ↑ log(1/γ)/D₁ to get (1). For (2), the eigenvalue 1 is excluded on Ω^⊥.

For (3): with Θ_L = Θ∘S_{−1} (the reflection t ↦ −1−t, checked as in (iii)), ⟨F̂, TF̂⟩ = μ_∞(F₁·ΘF) = μ_∞(F·Θ_L F) ≥ 0 for F
supported in [0, s]. This is the link-positive half (`posLinksL`), which contains the slice t = 0. Such F̂ are dense. ∎

### 6.7 What "transfer matrix" means here (finite periodic lattice)

On the finite torus the correlation is a thermal trace, H_N(m) ∼ Tr(T^{N−m} A T^m B)/Tr T^N − (…). It is **not** a vacuum matrix element,
and Theorem C bounds it only with the factor (C_F/H_N(0))^{2^{−r}}, with r ≈ log₂(N/2m). A spectral statement needs one of two routes:
- (a) **infinite volume** (C2 above);
- (b) **an anisotropic torus** (ℤ/N_t) × (ℤ/N_s)^{d−1} with N_t → ∞ at fixed N_s. Then H_{N_t}(m) → ⟨Ω₀, A(T_{N_s}/λ₀)^m A Ω₀⟩_c,
  provided the top eigenvalue is simple. Under (Φ) the transfer kernel is strictly positive, so this follows by Jentzsch. The same
  argument gives gap(T_{N_s}) ≥ log(1/γ)/D₁, **uniformly in N_s**. Theorem A's proof applies verbatim on anisotropic tori, but the
  framework's RP files are isotropic (`ZMod N` in every direction), so (b) needs a generalisation. Stated, not proved here.

Site RP alone controls |T| (equivalently T²). This is enough for a gap and for vacuum uniqueness, and it is all that is available for
admissible weights (`admissible_rp`).

---

## 7. Corollary B (one physical scale)

**Setting.**
- A sequence (a_k, β_k) with a_k → 0, a physical length L₀, and γ < 1.
- Thin cubes with ℓ_k = ⌈L₀/a_k⌉, so D₁ = ℓ_k + 1 and D₀ = ℓ_k.
- Hypothesis (OS_k): GDS_W(𝒱_{ℓ_k}, γ) holds on ℤ^d for the weight at β_k, for every k.

**Corollary B.**
1. **(Lattice, each k.)** Every limit state of Lemma 6.3 at level k has transfer-operator gap (−½ log T²) at least
   log(1/γ)/(ℓ_k + 1) in lattice units. In physical units this is
   m_k := log(1/γ)/((ℓ_k+1)a_k) ≥ log(1/γ)/(L₀ + 2a_k), since (ℓ_k+1)a_k ≤ L₀ + 2a_k. Also m_k → m := log(1/γ)/L₀, since
   (ℓ_k+1)a_k ≥ L₀ + a_k. The vacuum is unique at each k. For thick cubes the bound is log(1/γ)/(L₀ + 2.5a_k).
2. **(Continuum.)** Take lattice observables F^{(k)} ∈ 𝒜_{[0, s_k]}, Lipschitz in each link, supported at physical times
   [0, s_k a_k] ⊂ [0, s]. Assume the renormalised connected correlations S_k(t) = Z_k² h^{(k)}(t/a_k) (for t ∈ a_kℤ, with Z_k > 0)
   converge along t_k → t to a continuum S(t), together with S_k(0) → S(0). Then S(t) ≤ S(0)e^{−mt}. If the continuum OS Hilbert space
   is generated by such limits and RP passes to the limit, the reconstructed Hamiltonian has gap ≥ m on the vacuum complement and the
   vacuum is unique.
3. **(Centre.)** If G is connected with nontrivial centre, π acts nontrivially on it, the weight is Wilson, and GDS_H^∂ holds at each
   k, then the area law holds at each k (Corollary A′ and Chatterjee's Theorem 2.4). No uniform string tension follows.

*Proof of 2.* By Corollary C1 at level k, |h^{(k)}(n)| ≤ h^{(k)}(0)e^{−λn} for every λ < log(1/γ)/(ℓ_k+1), hence also at the endpoint.
At n = t_k/a_k: S_k(t_k) ≤ S_k(0)e^{−m_k t_k}. Multiplying by Z_k² preserves the inequality, and additive renormalisations cancel in a
covariance. Let k → ∞, using m_k → m.

The spectral conclusion is the same argument as in C2, in the continuum OS space: Θ-symmetric, with t ∈ ℝ₊ and a contraction semigroup.
∎

**a-dependence (the honest bookkeeping).**
- The family constants grow: b_k = dℓ_k(ℓ_k+1)^{d−1} and c_k = ℓ_k(ℓ_k+1)^{d−1}. Only b/c = d and ρ_λ stay bounded.
- Theorem A's constant grows like ℓ_k^d·(support of F^{(k)}) and is unusable as a → 0.
- Corollary C1 removes it at each k. This is why Corollary B needs Theorem C, and why the decay rate, not the constant, is what
  scales: e^{λ_k D₀} ≤ 1/γ is uniform.
- The hypothesis (OS_k) is an infinite family of box statements, one for each k. It is the open problem, not something this note
  reduces (B§3.8).
- Not checked here: how this plugs into the OpenAI `Schedule` interface (`SURVEY-LEAN.md` §4).

---

## 8. Non-vacuity at strong coupling (single links)

**Proposition 8.1 (H).** Let φ(x) = e^{βx} with β ≥ 0, ℬ = 𝒱₁ (single links) and N ≥ 3. Then k^H_{{x}}(z) ≤ tanh(nβ) for every
neighbour z of x. So GDS_H(𝒱₁, γ) holds with γ = 6(d−1)·tanh(nβ), and Theorem A applies when 6(d−1)tanh(nβ) < 1, with rate
λ < log(1/γ).

*Proof.*
- q_{{x}}^η is `gibbs λ (ξ ↦ β Σ_{p∋x} χ(U_p))`.
- If η and η' differ only at z, exactly one plaquette p₀ contains both x and z (§1.1). So the log-weights are βf_i + ψ, with
  f_i = χ(U_{p₀}) (|f_i| ≤ n) and ψ the common bounded part. `tv_single_link_le_tanh` gives tv ≤ tanh(nβ).
- For F with δ_x(F) = osc(F) ≤ 1, Lemma 2.4 gives |q^η F − q^{η'} F| ≤ tanh(nβ).
- The neighbour relation is symmetric, so #{x : z ∈ ∂{x}} = 6(d−1) and c(z) = 1. ∎

The final arithmetic step is exactly `Influence.dobrushin_single_link`, with a_j = k_{{x_j}}(z) ≤ tanh(nβ). In Lean the instance
`gds_single_link` needs three pieces: Lemma 2.4, the identification of the single-link specification with `gibbs` (one changed term),
and the lattice lemma "6(d−1) neighbours, one common plaquette" (N ≥ 3).

*Windows (d = 4).* 18·tanh(nβ) < 1 means nβ < artanh(1/18) ≈ 0.0556, in the normalisation e^{β Re tr}. For U(1) (n = 1) this is
β < 0.0556. For SU(2) (n = 2) it is β < 0.0278, i.e. β_std = 2β < 0.0556. B§4.3's "0.056 (SU(2), U(1))" is right in these respective
normalisations. Both windows lie deep in the confined phase (U(1) Wilson β_c ≈ 1.0; Z₂ β_c ≈ 0.44), as they must.

**Proposition 8.2 (W).** With ρ the Frobenius distance of a faithful representation (diam ≤ 2√n): k^W_{{x}}(z) ≤ nβ. So GDS_W(𝒱₁, γ)
holds with γ = 6(d−1)nβ.

*Proof.* Replacing one factor of a product of unitaries changes χ by at most √n‖R − R'‖_F, and ‖R^{−1} − R'^{−1}‖_F = ‖R − R'‖_F. So the
log-weights differ by a function with values in [−ε, ε], where ε = β√n ρ(η_z, η'_z). `tv_gibbs_le_tanh` with D = 2ε gives
tv ≤ tanh(ε/2) ≤ ε/2. Lemma 2.4 with osc(F) ≤ L(F)·diam ≤ 2√n gives |q^η F − q^{η'} F| ≤ 2√n·ε/2 = nβρ(η_z, η'_z). ∎

The window is the same as in the H case up to tanh versus identity. This is the "small new lemma" of B§4.3.

---

## 9. The admissible variant and topological sectors

1. **Soft admissibility (recommended).** Take any φ with φ_min > 0, e.g. φ(x) = e^{βx}·(η₀ + (1−η₀)1[n − x ≤ ε]) with 0 < η₀ ≤ 1.
   - Everything in §2–§8 applies verbatim.
   - Site RP holds by `rp_plaquette_weight`, since `PlaqWeight` allows any measurable bounded φ ≥ 0.
   - Sectors are not frozen; tunnelling between them is merely suppressed.
   - B§3.7's gains are kept, quantitatively: rough boundary conditions are penalised, large fields suppressed.
2. **Hard admissibility** (φ = 0 when n − x > ε, the framework's `admissibleWeight`).
   - Needed: allowed boundary values (Z_B(η) > 0) and seminorms over allowed pairs.
   - Use the *open* condition n − x < ε, so that every allowed configuration has an open, hence positive-Haar-measure, fibre. The
     closed and open conditions differ by a null set of plaquette values.
   - The proof of Theorem A then uses single-link connectivity of the allowed set in three places: Lemma 2.3 inside blocks (Step 3),
     the global telescoping (Step 2), and homogeneity (§1.6).
3. **Sectors break the single-link definitions.**

   **Lemma 9.1.** Suppose that for some block B and allowed η, the allowed fillings split into two nonempty classes C₁, C₂ with no
   allowed single-link move between them. Suppose also q^η(C₁) ≠ q^{η'}(C₁) for some allowed η' ∼_z η. Then k^H_B(z) = k^W_B(z) = ∞.

   *Proof.* F = t·1_{C₁} has δ_y(F) = L_y(F) = 0 for all y (on allowed pairs), and |q^η F − q^{η'} F| = t·|Δ| → ∞. ∎

   - For small ε, Luescher's sectors give such classes inside large blocks: the relative charge of fillings with fixed boundary.
   - Single-link moves cannot change the sector. *Sketch, not a full proof:* for small ε, the allowed values of one link given its
     neighbours form an intersection of small geodesic balls, which is convex, so every single-link move extends to a continuous path
     of admissible fields, along which the charge is constant.
   - A boundary change generically reweights the sectors. So **GDS fails for hard-admissible weights with large blocks, for a reason
     that is an artefact of the single-link seminorms**, not physics.
   - Block telescoping (fix b) would require replacing the per-link seminorms in Lemma 2.5 by block quantities, and is not developed.
   - Conclusion: use (1). B§3.7's fix (a) is true only if blocks are too small to hold two sectors, which is useless for Corollary B,
     where ℓ = L₀/a → ∞.
4. **Theorem C** needs only site RP, which holds for both soft and hard weights. Link RP fails for hard weights on crossing plaquettes,
   since the indicator is not a positive-definite kernel (end of `Positivity/General.lean`). So for admissible theories only |T| is
   controlled (C4).

---

## 10. Adversarial self-check

### 10.1 Step by step

| step | what could be wrong | attempt to break it | outcome |
|---|---|---|---|
| DLR (2.1) | W does not factor; shell misidentified | plaquettes not touching B have no B-link, so R is B-free; plaquettes touching B have links in B ∪ ∂B by definition of ∂B | holds. For N = 2, plaquettes wrap, but V ∪ ∂V still injects for N ≥ ℓ + 3 |
| Propagation (2.5) | the k-term needs F = h(σ'_{Ω∖B}, ·) to be admissible in the sup | k is defined with a sup over *all* F (no gauge condition), all η (frozen links included) | holds. The earlier worry that F is not gauge invariant is resolved: the definition does not need it, and Lemma 3.4 shows nothing is lost |
| Homogeneity | F with all δ_y = 0 but non-constant | impossible under (Φ) (Lemma 2.3) | holds. Fails under hard admissibility with sectors (Lemma 9.1): then k = ∞ and GDS fails, so no false theorem results |
| Contraction (Step 1) | c(x) = 0; D₁ underestimated; torus wrap | c_− ≥ 1 required; D₁ uses the periodic metric, and the triangle inequality holds for it | holds |
| Covariance telescoping (Step 3) | sign or adjointness error | Lemma 2.6 is a two-line identity from 2.1 and 2.2 | holds. Checked on product measures (Cov = 0 beyond D₀) and on single links (Dobrushin's estimate) |
| Constants independent of M | M appears in θ | Σ_s N_s ≤ N₀M/(c_−(1−ρ)), and the prefactor 1/M cancels it | holds |
| Boundary version | blocks near ∂Ω | see C2 | not proved under GDS; proved under GDS^∂ |
| Alignment (3.3) | measurable selection; non-unique minimiser (Gribov) | countable dense subset of K and ε-minimiser; uniqueness never used | holds |
| Alignment (dual) | averaging could increase δ_y | K acts link-wise and by ρ-isometries | holds |
| "Only physics remains" | boundary-site gauge | Lemma 3.5 and the Z₂ example | **false as stated** (C3); repaired by GDS* or thick cubes |
| Small groups (Z₂, U(1)) | alignment trivial for single links | K_{{e}} is trivial (no interior sites) | consistent: single-link Dobrushin has no gauge freedom |
| RP Hankel (6.1) | sign conventions of Θ and S | mir(l + ke₀) = mir(l) − ke₀ checked for both link types; tw depends only on the direction | holds |
| Doubling (6.2) | odd H may be negative | only even arguments are raised to fractional powers | holds |
| Finite N | wrap-around distance | N ≥ 2^{r+1}m + 2s makes the wrap gap ≥ 2^r m | holds |
| Spectral (C2) | T not positive under site RP | claim only spec ⊂ [−e^{−λ}, e^{−λ}]; positivity from link RP | corrected (C4) |
| Corollary B | constants blow up as a → 0 | removed at each k by C1; only m_k scales | holds at the lattice level. Continuum needs the stated regularity |
| Topological sectors | single-link telescoping | Lemma 9.1 | hard admissibility unusable; soft works |
| Degenerate tori | N = 2 neighbour count | N ≥ 3 standing; N ≥ ℓ + 3 for blocks | holds |

### 10.2 Photon test (4D U(1), weak coupling)

**What the proofs give.** Assume GDS_W(𝒱, γ) for some weight φ in our class: Wilson, or Villain, which is a function of cos θ_p.
Then by Theorem A, C1 and C2, every infinite-volume limit state of torus measures has exponential clustering of all per-link Lipschitz
local observables, and a gap ≥ log(1/γ)/D₁. Under GDS_H^∂ (Corollary A′, Wilson action, U(1) connected), every Gibbs measure also
satisfies the area law.

**What would contradict it.**
- (a) A theorem that U(1)₄ at large β has some local Lipschitz correlation without exponential decay (the massless photon).
- (b) A perimeter law for the **Wilson** action, contradicting the GDS_H^∂ consequence.

What I could verify (§11):
- Guth 1980 (secondary: APS abstract) and Froehlich–Spencer 1982 (secondary: Garban–Sepulveda 2021, Theorem 1.2) prove the
  **perimeter law for the Villain action**.
- Whether FS82 also proves absence of exponential clustering, i.e. (a), or treats the Wilson action, I could not verify. A search
  snippet suggests FS leave the Wilson formulation open.

So the photon test is a theorem in the form "GDS_H^∂ fails for Villain U(1)₄ at large β" only if Chatterjee's Theorem 2.4 extends to the
Villain weight. His proof is stated for the Wilson Hamiltonian and was not re-read. Otherwise it holds conditionally on (a). B§4.4's
table entry "theorem, given Theorem A + Froehlich–Spencer" should read "theorem given Theorem A and [FS masslessness, to be checked] or
[Chatterjee 2.4 for Villain]".

**Do the proofs accidentally imply GDS for U(1) at weak coupling?** No.
- The only unconditional GDS statements are Propositions 8.1 and 8.2: β < 0.0556 for U(1), the confined phase.
- GDS* removes only the dangling-link term, which is pure gauge; the Coulomb response of non-dangling links is untouched.
- No step uses an influence measured only on absolutely gauge-invariant observables of an inner box (B§2.2, formulation 3). Theorem A*
  still takes the supremum over all F on the block. Gauge invariance is imposed only on the *global* function g, and its use (Lemma
  3.6) is an exact identity.

**Witness 2 (B§4.1).** Fix the cross-section flux Φ mod 2π by the boundary condition. In 4D the interior sectors Φ + 2πm have energies
≈ β(Φ+2πm)²/2, independent of ℓ: uniform flux over ℓ² plaquettes per (1,2)-slice and ℓ² slices.
- At Φ = π the sectors m = 0 and m = −1 are degenerate, so the interior field is ±b with equal weights and E[F̄] = 0 under both boundary
  conditions: the odd witness is blind.
- Use Φ ≈ π/2 (sector m = 0 favoured by e^{−β·π²}) or the even witness F̄². With Φ = π/2, b = π/(2ℓ²) and the Gaussian estimate
  gives KL ≈ βπ²/128, still independent of ℓ.
- *In d = 2 the analogous constraint is harmless.* There is one cross-section, the sector energies βΦ²/(2ℓ²) → 0, and wrapping wins.
  An exact Z₂ computation (i.i.d. plaquettes conditioned on their product) gives Cov ≈ −t^{ℓ²}(1−t²)²/t² with t = tanh β: decay in ℓ²,
  no violation. I first expected a violation here, and the computation refuted it.

### 10.3 Ising-gauge test (4D Z₂, weak coupling)

- **Logical form.** GDS_H^∂ ⇒ Definition 2.3 ⇒ (Theorem 2.4) area law, against the perimeter behaviour at large β ⇒ GDS_H^∂ fails.
- **Gaps in that chain.**
  1. Chatterjee's Theorem 2.4 assumes G connected (checked), and Z₂ is not.
  2. Chatterjee 2020 gives leading-order asymptotics of ⟨W_γ⟩ with an additive error. That does not by itself prove a perimeter law
     uniformly in the loop size at fixed β. A classical low-temperature perimeter law for Z₂ in d ≥ 3 exists (memory, not verified
     here).
  3. The argument concerns GDS^∂. For torus-only GDS there is no contradiction with anything proven: Z₂ at weak coupling *has* a gap
     (Adhikari–Cao). So torus GDS failing for Z₂ is heuristic (B§4.2's pinned sheets).
- **Quantitative torus check (heuristic).** For Polyakov loops P_x, P_y of length N at spatial distance N/2, Theorem A gives
  ⟨P_xP_y⟩ ≤ C·N·e^{−λN/2}. In the deconfined phase ⟨P_xP_y⟩ ≳ e^{−2f(β)N}, with f(β) → 0 as β → ∞. So torus GDS at large β would need
  λ ≤ 4f(β), i.e. ℓ + 1 ≳ log(1/γ)/(4f(β)). This is consistent: no contradiction, only a size requirement.
- **Do the proofs accidentally imply GDS for Z₂ at weak coupling?** No. The only unconditional window, tanh β < 1/18, is in the confined
  phase.

### 10.4 Is Theorem A plausibly too strong?

Theorem A gives decay **uniform in the boundary condition** (under GDS^∂), hence it implies confinement for connected G with a centre.
That is the intended strength. The two tests say this hypothesis must fail for U(1) Coulomb and for Z₂ deconfined. I found no step that
weakens the hypothesis below what Theorem A uses: the supremum over all η and all F, with the per-link normalisation.

---

## 11. Citations: what was checked

Read by me:
- Chatterjee, arXiv:2006.16229v5, §2.1–§2.4: setting (G closed connected ⊂ U(n), Wilson action), Definition 2.1, Theorem 2.2,
  Definition 2.3 (local = depends on the neighbours of one edge; K₁, K₂ depend on G, β, d only; dist = Euclidean), Theorem 2.4, the
  Dobrushin–Shlosman remark, and the finite-group discussion. **Correction:** the blueprint omits "connected".
- Garban–Sepulveda, arXiv:2107.04021v2, §1: attributes the perimeter law (their Theorem 1.2) to Guth80 and FS82 **for the Villain model**.

Checked by a search subagent (secondary listings; I verified Tomboulis–Yaffe and Chatterjee myself):

| item | status |
|---|---|
| Tomboulis–Yaffe, CMP 100 (1985) | **corrected:** title "Finite temperature SU(2) lattice gauge theory", pages 313–341 (blueprint: 313–329) |
| Martinelli–Olivieri, CMP 161 (1994) | confirmed; part I "… I: The attractive case" (447–486), part II "… II: The general case" (487–514) |
| Martinelli–Olivieri–Schonmann, CMP 165 (1994) 33–47 | confirmed ("For 2-D lattice spin systems weak mixing implies strong mixing") |
| Stroock–Zegarlinski | confirmed; CMP 144 (1992) 303–323 "The equivalence of the logarithmic Sobolev inequality and the Dobrushin–Shlosman mixing condition"; CMP 149 (1992) 175–193 "The logarithmic Sobolev inequality for discrete spin systems on a lattice" |
| Dobrushin 1968, 1970 (TVP 13, 15) | confirmed (DOIs 10.1137/1113026, 10.1137/1115049); Mathnet lists a variant English title for the 1968 paper (tvp839), to be copied from there before quoting |
| Dobrushin–Shlosman 1985 (Birkhaeuser), 1987 (JSP 46) | volume confirmed; page pairing 347–370 / 371–403 not confirmed; **spin-space generality not verified** |
| Foellmer, JFA 46 (1982) 387–395 | confirmed |
| van den Berg–Maes, Ann. Probab. 22 (1994) 749–763 | confirmed |
| Osterwalder–Seiler, Ann. Phys. 110 (1978) 440–471 | confirmed |
| Froehlich–Spencer, CMP 83 (1982) 411–454 | citation confirmed; **action (Villain vs Wilson) and the masslessness statement not verified** |
| Guth, PRD 21 (1980) 2291 | confirmed; Villain form (APS abstract) |
| Goepfert–Mack, CMP 82 (1982) 545–606 | confirmed |
| Chatterjee, CMP 377 (2020) 307–340 | confirmed (secondary) |
| Cao 2020 | arXiv:2001.05627, DOI 10.1007/s00220-020-03912-z; volume and pages not found |
| Durhuus–Froehlich, CMP 75 (1980) 103–151 | confirmed; exact uniform condition not read |
| Mack–Petkova, Ann. Phys. 123 (1979) 442–467; 125 (1980) 117 | confirmed; end page 134 not confirmed |
| Borgs–Seiler, CMP 91 (1983) 329–380 | confirmed: "Lattice Yang–Mills theory at nonzero temperature and the confinement problem" |
| Kovacs–Tomboulis, PRL 85 (2000) 704–707 | confirmed: "Computation of the vortex free energy in SU(2) gauge theory" |
| 't Hooft, NPB 153 (1979) 141 | "A property of electric and magnetic flux in non-abelian gauge theories" (single source) |
| Dobrushin–Kolafa–Shlosman, CMP 102 (1985) 89–103 | confirmed |
| Zegarlinski, JFA 105 (1992) 77–111 | confirmed |
| Weitz, RSA 27 (2005) | DOI confirmed; pages 445–475 not confirmed |

Still open before quoting: FS82's action and masslessness, Dobrushin–Shlosman 1985's spin-space generality, and the Z₂ perimeter law
reference.

---

## 12. Verdicts and Lean-readiness

### 12.1 Verdicts

| statement | verdict |
|---|---|
| Lemma 2.3 / 3.3–3.4 (alignment, coupling and dual) | **proved** |
| Lemma 3.5–3.6 (dangling links) | **proved** (new; not in the blueprint) |
| Theorem A, torus, H and W | **proved**, with explicit constants |
| Theorem A, boxes with boundary conditions | **proved under GDS^∂**; **not proved under plain GDS** (gap, C2) |
| Theorem A* (gauge-invariant g, GDS*) | **proved** |
| Corollary A′ (Chatterjee Definition 2.3) | **proved** under GDS_H^∂ for the setting of Chatterjee (connected G, Wilson); the consequence for finite G is not available |
| Theorem C, finite torus (doubling form) | **proved** |
| Corollary C1 (prefactor-free, limit points) | **proved** |
| Theorem C2 (spectral gap, unique vacuum, infinite volume) | **proved modulo** standard OS reconstruction and the existence of limit states (Lemma 6.3, sketched). [0, e^{−λ}] only with link RP (Wilson, β ≥ 0) |
| Corollary B.1 (lattice, uniform in a) | **proved** (given the hypothesis (OS_k), which is open) |
| Corollary B.2 (continuum) | **proved with a stated gap**: needs convergence of the chosen correlations, and that the continuum OS space is generated by them |
| Corollary B.3 (area law at each k) | proved under GDS_H^∂, connected G, Wilson action |
| Non-vacuity (single links, H and W) | **proved** |
| Admissible variant | proved for soft weights; hard weights: GDS generically infinite with sectors (Lemma 9.1, sector claim sketched) |
| Photon test as a theorem | **conditional** (§10.2) |
| Ising-gauge test as a theorem | **conditional** (§10.3: needs Chatterjee 2.4 for finite G and a Z₂ perimeter-law reference) |

### 12.2 Lean-readiness (against blueprint §6)

| lemma | Lean-ready? | notes |
|---|---|---|
| L0 blocks, shells, c, D₀, D₁; neighbour fact (N ≥ 3) | yes | the 6(d−1) neighbour count and "one common plaquette" are new lattice lemmas |
| L1 specification, Lemma 2.1 (DLR) | yes | Fubini split of `Measure.pi` along a Finset; under (Φ) Z_B ≥ φ_min^{\|P(B)\|}, so no "allowed τ" hypothesis is needed |
| L2 seminorms, Lemma 2.3 | yes | |
| Lemma 2.4 (osc × tv) | yes | new, small, add to `Influence` |
| L3 Lemma 2.2, 2.5 (propagation) | yes | |
| Lemma 2.6 (block covariance identity) | yes | new, two lines from 2.1 and 2.2 |
| L5 contraction | yes, **simpler than planned** | no S-set; a weighted max over a Finset and a geometric bound |
| L6 Theorem A | yes | the remainder term avoids limits |
| L7 alignment | dual form yes; coupling form moderate (countable dense subset of K, ε-minimiser) | **off the critical path**: Theorem A uses the unrestricted k and needs no L7 |
| Lemma 3.6 / Theorem A* | yes | needs the gauge action on `GaugeConnection` (exists) and invariance of `productHaar` under link-wise multiplication (as in `TwistVanish`, `CentreSymmetry`) |
| L8 boundary version | yes, under GDS^∂ | as a `Prop` hypothesis; Chatterjee's Definition 2.3 as a `Prop` |
| L9 Theorem C (finite N) and Corollary C1 | yes | needs the new lemma "time translation preserves `productHaar` and the weight", plus S_k∘Θ = Θ∘S_{−k}. C1 is pure real analysis |
| Theorem C2 (spectral) | no | infinite-volume limit, OS reconstruction, spectral theorem; keep it in prose |
| L10 Corollary B lattice part | yes (interface) | the hypothesis stays named and open |
| Corollary B continuum | no | depends on a continuum framework |
| L4 / §8 non-vacuity H | yes | `tv_single_link_le_tanh` + Lemma 2.4 + neighbour lemma + `dobrushin_single_link` |
| §8 non-vacuity W | yes | `tv_gibbs_le_tanh` + a Frobenius Lipschitz bound for Re tr |
| L11 Chatterjee Theorem 2.4 | no (unchanged: hard) | and it covers only connected G |
| L12 admissible | soft weight: yes (special case of (Φ)); hard weight: not recommended (Lemma 9.1) | |

**Changes to the blueprint's Lean plan:** L5 becomes simpler (no S-set); L7 moves off the critical path; the instances need two new
lattice lemmas (neighbour count, time-translation invariance); and L12 should use the soft weight. The first milestone (L0–L6 plus the
single-link instance) no longer depends on any gauge-specific file.
