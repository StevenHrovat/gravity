# Lead route: a flow for the box influence, and the chessboard step (attempt, 2026-11-21)

Status: mathematics plus two Lean files (`../../../formal/Attempts/Lead/Recursion.lean`, `Persistence.lean`). Claim levels follow
RULES.md 3: **proved**, **proved modulo** (a named standard result, cited), **heuristic**, **conjecture**. Section references
"PN§x" are to `../../PROOF-NOTE.md`, "B§x" to `../../BLUEPRINT-REDUCTION.md`, "PREP" to `../../PREP.md`.

---

## 0. Results at a glance

| # | statement | level |
|---|---|---|
| D1 | A level-uniform recursion "GDS with c at side ℓ ⇒ GDS with f(c) at every side in [ℓ, 2ℓ]" above a physical scale L₁, an entrance value x₀ at L₁, and f^[N](x₀) ≤ γ give `UniformGDS` at L₀ = 2^N L₁, and with it Corollary B | **proved, Lean** (`uniformGDS_of_recursion`, `corollaryB_of_recursion`) |
| D0 | The entrance cannot sit at a fixed lattice side: a recursion with β-independent f whose basin contains the (universal) small-ℓ values would give a lattice-unit gap uniform in β | **proved** as an implication; that the conclusion is false is **heuristic** for SU(2) (asymptotic freedom), conditional for U(1) (PN§10.2) |
| D2 | Persistence: GDS^∂ at one side ℓ with γ < 1 controls every larger box: k_W(z) ≤ K^∂(ℓ)/(1−γ), hence κ(L), κ^∂(L) ≤ σ_L K^∂(ℓ)/(1−γ) with σ_L ≈ 2d/L. Below 1 a contracting recursion exists automatically | abstract comparison theorem **proved, Lean** (`comparison`); the gauge instance **proved** on paper (not formal) |
| D3 | Photon structure: any recursion f built from properties U(1) shares (Markov, gauge invariance, RP, compactness) has a basin that excludes every U(1) Coulomb value of κ; SU(2) values at scales ≪ ξ differ from free (abelian) values only at O(g²). So f must resolve the O(g²) non-abelian drift per doubling: tracking κ does not escape tracking the coupling | first half **proved** (given Theorem A and U(1) masslessness, PN§10.2); second half **heuristic** (perturbation theory) |
| C1 | Chessboard inequality for our measure and for two independent replicas | **proved modulo** the standard chessboard theorem (FILS; Biskup's review); ingredients partly formal |
| C2 | Obstruction: κ (a supremum over boundary conditions) cannot be bounded by torus bad-event probabilities; the conversion factor is (φ_max/φ_min)^{2|P_∂V|} = e^{4nβ|P_∂V|} (Wilson) | **proved** (the inequality); "no other route" is a **heuristic** reading, sharpened by the Z₂ test |
| R | Torus decay from chessboard (replica swap): for finite abelian G, \|Cov(f,g)\| ≤ 2‖f‖‖g‖·3^d\|T_f\|·((3^d−1)z₂)^r, with z₂ the disseminated probability that the two replicas disagree on a plaquette in every block | **proved modulo** C1 |
| R-tests | R is vacuous for U(1) and SU(2) (z₂ = 1: continuous replicas never agree), gives decay for Z₂ at large β (true; no confinement claimed), vacuous for Z₂ at strong coupling | **proved** (U(1), SU(2): exact); size of z₂ for Z₂ **heuristic** (leading order) |
| A | The owner's anchoring-line event, read as a 1-dimensional line cost, **fails the photon test** (perimeter law: long lines are randomised in U(1) too). Read as a 2-dimensional twist/vortex event it passes both tests, but it controls only centre-charged transmission (confinement), not the centre-neutral glueball channel (the gap) | **heuristic** (standard physics of perimeter/area laws); the channel split is exact for the mechanism (the random linking phase is 1 on centre-neutral observables) |
| P | Plausibility at weak coupling: every correct single-block estimate found here is as strong as a known open statement (uniform one-scale DS condition; 't Hooft vortex free energy decay) and lives at a physical scale ~ several ξ, beyond any rigorous weak-coupling tool | **assessment** |

**Bottom line.** The deterministic part is clean and formal: once GDS (boundary version) holds at one scale with any γ < 1, all
larger scales follow (D2), and a recursion with an entrance gives `UniformGDS` (D1). The whole difficulty sits in the entrance (getting
below 1, from values ≥ 1 that the photon shares). The chessboard engine cannot reach κ (C2); what it can reach is torus decay directly,
and the one rigorous mechanism found (R, exact replica agreement) is an "ordered phase" mechanism: it reproves torus decay for Z₂ at large β
and is blind for continuous groups. Recommendation: retarget the lead route from `UniformGDS` to torus decay (the input Corollary B
actually consumes), and look for a soft, reflection-positive replica coupling for continuous groups (§2.4, §6).

---

## 1. The quantity and the recursion (deliverable 1)

### 1.1 Definitions

Fixed level k (torus (ℤ/N_kℤ)^d, weight φ_k, spacing a_k). Thin cubes V_ℓ (links with both ends in a translate of {0,…,ℓ}^d),
k^H_V(z) the dual-form influence (PN§1.6). Translation family 𝒱_ℓ; c_ℓ = ℓ(ℓ+1)^{d−1} (cubes containing a link), and
s_ℓ = max over directions μ of #{shell links of V_ℓ of direction μ} (cubes having a given link in their shell).

- **Box influence** κ_k(ℓ): the least γ with GDS(𝒱_ℓ, γ) on the level-k torus, i.e.
  κ_k(ℓ) = max_z Σ_{V : z ∈ ∂V} k_V(z) / c_ℓ (with hypercubic symmetry: Σ_{y∈∂V_ℓ} k(y)/|V_ℓ|). In Lean: `GDSAt d G n Nk φ k ℓ c`
  says "κ_k(ℓ) ≤ c, witnessed by influence bounds"; `UniformGDS` = `∀ k, GDSAt … k ⌈L₀/a_k⌉ γ` (`uniformGDS_iff`, by `Iff.rfl`).
- **Boundary version** κ^∂_k(ℓ): the least γ with GDS^∂(𝒱_ℓ, γ) (PN§1.7: GDS for the truncated family {V ∩ Ω} of every finite Ω).
- **Frozen-link influence** K^∂_k(ℓ) := sup over finite Ω and z ∉ Ω of Σ_{V : z ∈ ∂(V∩Ω)} k_{V∩Ω}(z) / c_ℓ. It includes the
  blocks V ∋ z that stick out of Ω through z, so it is an O(1) response, not a small quantity. Crude universal bound (H):
  k_B(z) ≤ |B| (osc ≤ |B|, tv ≤ 1), so K^∂(ℓ) ≤ (1 + s_ℓ/c_ℓ)|V_ℓ|.
- Shell ratio: σ_L := s_L/c_L ≤ (L+2)(L+3)^{d−1}/(L(L+1)^{d−1}) − 1 (every shell link has both ends in {−1,…,L+1}^d), so
  σ_L = 2d/L + O(L^{−2}). d = 4: σ_8 ≤ 1.28, σ_16 ≤ 0.57, σ_32 ≤ 0.27.

### 1.2 Theorem D1 (Lean: `Attempts/Lead/Recursion.lean`)

**Hypotheses.**
- (Rec) `DoublingRecursion f L₁ a`: for every level k and sides ℓ ≤ ℓ' ≤ 2ℓ with ℓ a_k ≥ L₁: κ_k(ℓ) ≤ c ⇒ κ_k(ℓ') ≤ f(c). One f for all
  levels. (The window ℓ' ∈ [ℓ, 2ℓ] absorbs the rounding of ⌈L/a⌉: ⌈L/a⌉ ≤ ⌈2L/a⌉ ≤ 2⌈L/a⌉, `side_le_side_two_mul`, `side_two_mul_le`.)
- (Ent) κ_k(⌈L₁/a_k⌉) ≤ x₀ for every k.
- f^[N](x₀) ≤ γ.

**Conclusion.** `UniformGDS` at L₀ = 2^N L₁ with constant γ (`uniformGDS_of_recursion`); if f maps a set T ⊆ (−∞, γ] into itself
and f^[N](x₀) ∈ T, at every scale 2^m L₁, m ≥ N (`uniformGDS_of_recursion_all`); and the physical-units Corollary B through the
existing chain (`corollaryB_of_recursion`, which calls `OneScale.CubeChain.corollaryB_of_uniformGDS`). Basin lemmas:
`exists_iterate_le_of_tendsto` (a fixed point x* < γ attracting x₀), `iterate_contract` (global contraction), and the quadratic
(chessboard-type) map f(x) = Cx²: f^[m](x) = (Cx)^{2^m}/C (`iterate_sq`), basin 0 ≤ Cx₀ < 1 (`exists_iterate_sq_le`).

*Proof* (also the Lean proof). Chain ℓ_m = ⌈2^m L₁/a_k⌉: ℓ_m ≤ ℓ_{m+1} ≤ 2ℓ_m and ℓ_m a_k ≥ 2^m L₁ ≥ L₁, so (Rec) applies at each
step; induction gives κ_k(ℓ_m) ≤ f^[m](x₀); GDS is monotone in its constant (`gds_mono`). ∎

### 1.3 Proposition D0: the entrance must be at a physical scale

*Statement.* Suppose (Rec) held with L₁ replaced by a fixed lattice side ℓ₀ (i.e. for all ℓ ≥ ℓ₀ at every level), and the
basin of f contained x̄(ℓ₀) := (s_{ℓ₀}/c_{ℓ₀})|V_{ℓ₀}| (which bounds κ_k(ℓ₀) at every β, H variant). Then GDS holds with γ at the
fixed lattice side 2^N ℓ₀ at every level, so by Theorem A + C + C1 the lattice-unit decay rate is ≥ log(1/γ)/(2^Nℓ₀ + 1) at every
β, and the physical mass m_k ≥ log(1/γ)/((2^Nℓ₀+1)a_k) → ∞.

*Level.* The implication is **proved** (it is D1 with L₁ = ℓ₀a_k replaced by a lattice constant, plus the universal bound on
κ(ℓ₀)). The conclusion is false: for U(1) at large β by masslessness (conditional, PN§10.2); for SU(2) by asymptotic freedom (the
lattice correlation length diverges as β → ∞), which is **heuristic** (universally expected, not a theorem).

*Consequence.* A valid recursion localises the one-scale hypothesis at the smaller physical scale L₁ with a weaker constant x₀; it
does not remove it. The gain is real only if x₀ may be ≥ γ (ideally ≥ 1), i.e. if f contracts in a region where Theorem A does
not yet apply.

### 1.4 Theorem D2: persistence (below 1 the recursion is automatic)

**Lemma D2 (comparison for a box).** Assume GDS^∂(𝒱_ℓ, γ) with γ < 1. Let W be any finite link set, z ∉ W, and η, η' boundary
conditions differing only at z. Then for every F on G^W with δ_y(F) ≤ 1 (y ∈ W):

  |q_W^{η'}(F) − q_W^{η}(F)| ≤ (Σ_{V : z ∈ ∂(V∩W)} k_{V∩W}(z)) / (c_ℓ(1−γ)) ≤ K^∂(ℓ)/(1−γ).

So k_W(z) ≤ K^∂(ℓ)/(1−γ), for boxes of **any** size and shape.

*Proof.* System (W, η) and (W, η'), block family ℬ = (V ∩ W)_{V ∈ 𝒱_ℓ, V∩W ≠ ∅}, coverage c_ℓ on W (every V ∋ x gives a block ∋ x).
Specifications q_B^{σ,η} and q_B^{σ,η'} (PN§1.4) coincide unless z ∈ ∂B; when z ∈ ∂B their boundary values differ only at z, so for
every h, |P'_B h − P_B h| ≤ k_B(z) max_{y∈B} δ_y(h) (definition of k, homogeneous form PN§1.6). GDS^∂ on Ω = W is the contraction
hypothesis of Step 1 of Theorem A for μ = q_W^η with weight w ≡ 1: δ(P^s F) ≤ θ^s with θ = 1 − c_ℓ(1−γ)/M. Telescoping under μ':
μ'(F) − μ'(P^t F) = Σ_{s<t} μ'(P' P^s F − P P^s F) (DLR for μ', Lemma 2.1), each term ≤ M^{−1}(Σ_{z∈∂B} k_B(z)) θ^s, and
|μ'(P^t F) − μ(F)| = |μ'(P^tF) − μ(P^tF)| ≤ |W|θ^t → 0. Sum the geometric series: M^{−1}/(1−θ) = 1/(c_ℓ(1−γ)). ∎

The abstract core (two measures, block specifications over the same blocks, differing by K_j·max δ on block j) is **formal**:
`Attempts.Lead.comparison` in `Persistence.lean`: |μ'(F) − μ(F)| ≤ (Σ_j K_j)·L/(c₋(1−γ)). Not formal: the instantiation (the
truncated-family block specification of a box measure with frozen boundary, i.e. the DLR identity for sub-blocks of
`gaugeSpec n φ W η`; `OneScale.Product.productBlockSpec` covers the torus, not boxes).

**Theorem D2 (persistence).** Under GDS^∂(𝒱_ℓ, γ), γ < 1, for every L:
- κ(L) ≤ σ_L · K^∂(ℓ)/(1−γ) (torus or ℤ^d family of side L);
- κ^∂(L) ≤ σ_L · K^∂(ℓ)/(1−γ);
- K^∂(L) ≤ (1 + σ_L) · K^∂(ℓ)/(1−γ).

*Proof.* For z of direction μ, the side-L blocks W with z ∈ ∂W number s_L^{(μ)} ≤ s_L; apply Lemma D2 to each and divide by c_L.
For the truncated family on Ω and z ∈ Ω: z ∈ ∂(W∩Ω) forces z ∉ W and z ∈ ∂W, same count; Lemma D2 for the box W∩Ω. For z ∉ Ω
also W ∋ z may occur, adding c_L blocks. ∎

**Reading.** (i) "Further doublings keep it there" is a theorem, in a stronger form (one step to every larger L, no dyadic
chain): κ(L) decays like 2d K^∂/((1−γ)L). (ii) In the brief's form, on {κ^∂ < 1} the recursion holds with
f_L(x) = σ_L K/(1−x) (K a bound for K^∂), which contracts for L large. (iii) The rate log(1/κ(L))/(L+1) of Theorem A *decreases*
with L (like log L/L): persistence does not improve the mass, it only transports the hypothesis. (iv) Everything hinges on the
entrance κ^∂(ℓ) < 1 with K^∂(ℓ) controlled. If K^∂ ~ ξ/a (the W-variant Coulomb-type response cut off at ξ, B§3.6, heuristic),
the entrance at ℓ ~ ξ/a gives κ(L) ≤ γ' at L ~ (2d/γ')·const·ξ/a: a fixed physical multiple, consistent with D1/D0.

*Tests.* D2 is an implication whose hypothesis fails for U(1) Coulomb (GDS^∂ < 1 would give decay; conditional, PN§10.2) and for Z₂
deconfined (GDS^∂ ⇒ Chatterjee's Definition 2.3 ⇒ area law; conditional on the finite-group extension, PN§10.3). It proves nothing
about them: passes both tests.

### 1.5 D3: what the photon test says about any recursion for κ

1. *(Proved, given Theorem A and U(1) masslessness.)* For U(1) in the Coulomb phase, κ^∂(ℓ) ≥ 1 at every ℓ (otherwise D2 + Theorem
   A give decay). So for any f valid for U(1), no orbit starting at a U(1) value enters [0, 1): the basin of [0,1) excludes all U(1)
   Coulomb values. Any f derived only from the Markov property, gauge invariance, reflection positivity and compactness is valid
   for U(1).
2. *(Heuristic, perturbation theory.)* At scales ℓ ≪ ξ/a, SU(2) is three weakly coupled photons: as β → ∞ at fixed ℓ, the conditional
   measures concentrate on the classical minimiser and the W-influence is the linear (Gaussian) response, the same as for the free
   abelian theory, up to O(g²(ℓa)). So SU(2) entrance values at small scales lie within O(g²) of values that the basin must exclude.
3. Hence f cannot be a function of κ alone that is blind to non-commutativity: it must resolve a per-doubling drift of relative size
   ~ b₀g² log 2 (the one-loop running), i.e. carry a second variable (the coupling, or the "self-charge" of PREP's guiding principle).
   This is PREP §1's "10⁻⁵ to 10⁻¹³ per layer" in κ-language: tracking κ instead of the coupling does not avoid resolving the coupling's
   flow at small scales; it only helps once κ^∂ < 1 (D2), where it is automatic.

---

## 2. The chessboard step (deliverable 2)

### 2.1 C1: the chessboard inequality for our measure

*Setting.* Torus (ℤ/Nℤ)^d with N = Rℓ, R even. Closed blocks Q_t = ℓt + {0,…,ℓ}^d (t ∈ (ℤ/Rℤ)^d), sharing faces; the block link
set is the thin cube V_t. For a function F of the links of V_0, ϑ_t F is its image in block t under the composition of the site
reflections through the planes x_μ = ℓ, 2ℓ, … (translation by ℓt composed with a reflection in each direction with t_μ odd).
Disseminated value z(F) := μ(∏_t ϑ_t F)^{1/R^d} (≥ 0 by RP for F ≥ 0).

**C1 (chessboard).** If μ is reflection positive for the site reflection through every pair of planes {x_μ = jℓ, x_μ = jℓ + N/2},
every μ, then for block functions F_t ≥ 0 (or real, with |·|), |μ(∏_t ϑ_t F_t)| ≤ ∏_t z(F_t).

*Level.* **Proved modulo** the standard theorem (Froehlich–Israel–Lieb–Simon 1978; proof by iterated Cauchy–Schwarz, e.g. Biskup,
"Reflection positivity and phase transitions in lattice spin models", Thm 5.8; reference only). Our measure qualifies:
- site RP through t = 0 in direction 0, any `PlaqWeight` φ: **formal** (`rp_plaquette_weight_gram`; `OneScale.TorusRP.rpForm`);
- translation invariance (moving the plane to jℓ): **formal** in direction 0 (`OneScale.TimeShift`);
- other directions by the hypercubic symmetry of the weight: **not formal** (permutation of directions);
- the iterated chessboard argument itself: **not formal**.

**C1₂ (two replicas).** μ₂ = μ ⊗ μ is reflection positive: for F(U,U') = Σ_i a_i(U)b_i(U'), μ₂(F·ΘF) = Σ_{ij} ⟨a_i,Θa_j⟩⟨b_i,Θb_j⟩ ≥ 0
(Schur product of two PSD Gram matrices); general bounded F by L²-density of such sums and continuity of the form. **Proved** (not
formal). So C1 holds for μ₂.

**Lemma P (Peierls form).** For a block event A (indicator 1_A) and r distinct blocks t₁,…,t_r: μ(∩_i ϑ_{t_i}A) ≤ z(A)^r (C1 with
F = 1 elsewhere, z(1) = 1). There are at most (3^d − 1)^r self-avoiding *-paths of r blocks from a given block, so
P(some *-path of r A-blocks starts next to a set of m blocks) ≤ m·3^d·((3^d−1)z(A))^r. Threshold: z(A) < 1/(3^d − 1) = 1/80 in d = 4.
**Proved modulo C1.**

### 2.2 C2: why the chessboard cannot bound κ

κ is a supremum over boundary conditions η of the box specification q_V^η; C1 bounds μ-probabilities, i.e. μ-typical η. The only
link between the two is the specification identity and the density ratio:

  **C2.** For every event A of the V-links and all η: q_V^η(A) ≤ (φ_max/φ_min)^{2|P_∂(V)|} μ(A),

where P_∂(V) is the set of plaquettes with links in both V and ∂V. *Proof:* μ(A) = ∫ q_V^{η̃}(A) μ(dη̃) (Lemma 2.1), and
dq_V^η/dq_V^{η̃} ≤ (φ_max/φ_min)^{2|P_∂|} (the interior weights cancel; each boundary plaquette changes the numerator and the
normaliser by at most φ_max/φ_min). ∎ **Proved.**

For Wilson, φ_max/φ_min = e^{2nβ} and |P_∂(V_ℓ)| is of order ℓ^{d−1} (each of the 2d faces carries O(d·ℓ^{d−1}) boundary
plaquettes), so the conversion costs e^{4nβ|P_∂|} = e^{O(βℓ^{d−1})}, while a chessboard
gain is at best e^{−ℓ^d Δf} with Δf the free-energy cost density of the disseminated event (in lattice units, tiny at weak coupling).
No useful bound on κ results. **Z₂ sharpening (heuristic):** for Z₂ at weak coupling every local event that is unlikely under the
torus measure has tiny z, yet GDS fails (pinned sheets, B§4.2). So any argument "κ ≤ Φ(z(A))" must use an A that is *not* rare for Z₂;
it cannot be a generic "the block is atypical" event.

**Consequence.** The chessboard engine gives torus (typical-boundary) statements. The natural target is therefore **torus decay
itself** (`LevelDecay`, the input that Corollary B consumes, `OneScale.CubeChain.levelDecay_of_uniformGDS`), not `UniformGDS`. For
torus decay the Z₂ test changes sign: Z₂ at weak coupling *has* torus decay (Adhikari–Cao; Forsstroem), so a torus-decay argument must
fail for U(1) but may (and should) succeed for Z₂. It must not claim a boundary-uniform conclusion (that would imply confinement).

### 2.3 Theorem R: torus decay from a chessboard bound (replica swap)

**Setting.** G finite abelian, Wilson-type weight (any `PlaqWeight` φ that is a function of the plaquette value), torus as in C1. Two
independent replicas (U, U') ~ μ₂. Plaquette fields ω = dU, ω' = dU'. Block event (bad): B_t = {ω_p ≠ ω'_p for some plaquette p ⊂ Q_t}.
On the contractible closed block this is "U and U' are not gauge equivalent on V_t". B_t is swap-symmetric, gauge invariant, and
reflection-covariant (ϑ_t B_0 = B_t). Single-block quantity: **z₂ := z_{μ₂}(1_{B}) = μ₂(every block has a disagreeing plaquette)^{1/R^d}.**

**Theorem R.** Let f, g be bounded, gauge invariant, with supports in the block sets T_f, T_g (contractible), and let r be such that every
*-path of blocks from T_f to T_g has at least r blocks outside T_f, with r + diam(T_f) < R/4 (no wrapping). Then

  |Cov_μ(f, g)| ≤ 2‖f‖_∞‖g‖_∞ · 3^d|T_f| · ((3^d − 1) z₂)^r.

If (3^d−1)z₂ < 1 this is exponential decay at rate log(1/((3^d−1)z₂))/ℓ in lattice units, uniform in N.

*Proof.* Cov(f,g) = ½E₂[(f(ω)−f(ω'))(g(ω)−g(ω'))] (gauge-invariant local functions are functions of ω on contractible supports). Let C be
T_f together with all blocks reached from T_f by *-paths of bad blocks. Every block outside C that is *-adjacent to C is good. On
E = {C stays within block distance < r of T_f}, C ∩ T_g = ∅ and C lies in a ball. Fix C₀ and define the swap T on {C = C₀}: exchange ω and
ω' on every plaquette of the blocks of C₀.
- *T preserves exactness.* ω̃ is closed: every unit 3-cube lies in a closed block b; if b ∈ C₀ all its plaquettes are swapped; if b is a
  good neighbour, ω = ω' on all its plaquettes and the swap changes nothing there; otherwise b shares no plaquette with C₀. Periods
  over 2-cycles of the torus are unchanged (a 2-cycle can be moved off the ball containing C₀). So ω̃ = dŨ, and the same for ω̃'.
- *T preserves μ₂.* For abelian G the law of ω is ∝ ∏_p φ(ω_p)·1[ω exact] (each exact ω has the same number of preimages U); T permutes
  the factors φ(ω_p)φ(ω'_p) plaquette by plaquette.
- *T preserves {C = C₀}.* Blocks in C₀ stay bad (swap symmetry); boundary good blocks are unchanged (ω = ω' there); the event depends
  only on the statuses of C₀ and its *-boundary.
- *Signs.* f reads only plaquettes of T_f ⊂ C₀: f(ω̃) = f(ω'). g reads plaquettes of T_g; those shared with C₀-blocks lie in good
  boundary blocks, where ω = ω': g(ω̃) = g(ω).

T is a measure-preserving involution of {C = C₀} that flips (f−f')(g−g'), so its expectation on {C = C₀} vanishes. Summing over C₀:
|Cov| ≤ ½·2‖f‖·2‖g‖·μ₂(E^c), and E^c implies a *-path of r distinct bad blocks starting next to T_f; Lemma P for μ₂ (C1₂). ∎
**Proved modulo C1** (the chessboard theorem; the rest is above).

**Tests.**
- *U(1) (photon):* G is continuous, so P(ω_p = ω'_p) = 0 for independent replicas: B_t has probability 1, z₂ = 1, R is vacuous. Passes
  (proves nothing false). The same holds for any continuous G, **including SU(2): R says nothing about SU(2).**
- *Z₂ at weak coupling:* replicas agree except on rare excitations. The cheapest disagreement is one flipped link in one replica
  (2(d−1) = 6 plaquettes, weight e^{−12β} for the weight e^{βσ_p}); in the disseminated event one such excitation can serve up to
  2^{d−1} = 8 blocks, so at leading order z₂ ≤ c·e^{−12β/8} with a combinatorial c (**heuristic**). So z₂ → 0 as β → ∞ and R gives
  torus decay at large β (the explicit threshold depends on c and is not computed here). This is **true** (Adhikari–Cao 2025,
  Forsstroem 2022, by other methods), and R claims no boundary uniformity and no area law. Consistent.
- *Z₂ at strong coupling:* replicas disagree everywhere, z₂ ≈ 1: vacuous (strong-coupling decay comes from a different mechanism).

**What R teaches.** Replica agreement is an *ordered-phase* mechanism (rare excitations, like low-temperature Ising). Confinement at
weak coupling is a *disordered* (magnetic-condensate) phase: in SU(2), centre vortices are abundant, so even a centre-projected
"replica agreement" is not rare there. The right SU(2) mechanism is mixing by disorder, not agreement.

### 2.4 The owner's bad event: anchoring lines, and the twist

The reading (PREP "root swap"): a block is bad if an anchoring line (colour carried from the outside root into the node) passes it.
Two precise readings:

1. **Line cost per unit length (1-dimensional).** Bad = the face-to-face transporter of the block, given its boundary, is not close to
   Haar (it carries the outside frame through). Photon check: in 4D U(1) the Coulomb phase obeys a perimeter law, so a line of length ℓ
   has phase variance ∝ ℓ/β and is randomised for ℓ ≫ β. The bad event is therefore **rare for U(1)** at large ℓ, and a chessboard
   argument on it would "prove" decay for U(1). **Fails the photon test** (heuristic, but the perimeter law is the standard Coulomb-phase
   behaviour, Guth/FS for Villain). The reason: U(1)'s long-range correlations are carried by the field strength (the photon), not by
   frames; "anchoring at infinity is cheap" means a finite self-energy, which still costs per unit *time-length*. What distinguishes the
   phases is the cost per unit *separation* from the root, an area-type quantity.
2. **Area / twist (2-dimensional).** Bad = the block is magnetically ordered: no centre flux (vortex) of the block's size pierces its
   2-faces, i.e. the block's twist sector is pinned. Disseminated: z = (Z_{no twist in every block}/Z)^{1/R^d}, a vortex free energy.
   - U(1): a flux-2π sheet through a block costs ~ 4π²β, independent of ℓ (scale invariance): twists stay costly, "ordered" is the norm,
     **not rare**: passes the photon test.
   - Z₂ deconfined: a sheet costs ~ βℓ²: ordered is the norm, not rare: passes the Z₂ test (no confinement claimed).
   - SU(2) confined: the twist free energy F_v(ℓ) → 0 ('t Hooft; Kovacs–Tomboulis 2000 numerically), so twist sectors are nearly free.
     But "ordered" is then not *rare*, it has probability ~ 1/2 per plane: the per-block gain is O(1), below the Peierls threshold
     1/(3^d−1) only with many independent planes or sub-blocks, and the relevant quantity is the *bias* e^{−F_v}-type expectation, not a
     probability.
   - **Channel limitation.** The decorrelation mechanism of this event is the random linking phase z^{link} (z in the centre) that a
     piercing vortex gives a loop; that phase is identically 1 on centre-neutral observables (adjoint loops, glueball operators,
     plaquette correlations), so the mechanism decorrelates only centre-charged ones (Wilson and Polyakov loops of nonzero N-ality).
     (Exact for the mechanism; that no other use of the event reaches the neutral channel is **heuristic**.) So this event can at best give **confinement** (Tomboulis–Yaffe 1985 use reflection positivity
     to bound loops by twist free energies; reference only), not the **gap** in the neutral channel, which is what `UniformGDS` and
     `LevelDecay` must cover. Chatterjee's implication runs decay ⇒ confinement, not back.

**The precise remaining estimates.** Depending on the target:
- for `UniformGDS` (via D1/D2): the entrance κ^∂(ℓ) < 1 with K^∂(ℓ) = O(ℓ) at one physical scale. Not reachable by chessboard (C2).
- for torus decay via R: z₂ < 1/(3^d−1) for a replica coupling that is (a) reflection positive, (b) has the right marginals, (c)
  agrees exactly on a block with positive probability for continuous G. Independent replicas fail (c). The annealed "coupled replica"
  on H = {(u, u') ∈ SU(2)²: u' = ±u} with weight e^{β(Re tr u_p + Re tr u'_p)} satisfies (a) (Wilson weight in the representation
  ρ ⊕ ρ of H) and (c) on the SO(3) part, but fails (b) (its U-marginal is tilted by Σ_r ∏_p e^{β r_p Re tr U_p}); the quenched version has
  the right marginals but a non-local factor 1/Z_V that breaks RP. **This is the missing idea**, stated as a construction problem.
- for confinement only (twist route): F_v(ℓ) → 0 fast enough at one physical scale (the classical open problem; Tomboulis 2007's attempt
  and Ito–Seiler's objection, PREP §2).

---

## 3. Is the single-block estimate provable at weak coupling? (deliverable 3)

Honest assessment: **not with any tool known to me, and not in this round.**
- Every correct form found (κ^∂ < 1 with controlled K^∂; a soft replica z₂; the twist free energy) is a statement at a *physical* scale
  of a few correlation lengths (D0, D3), i.e. at ℓ ~ ξ/a ~ e^{β/(2b₀)}·const lattice spacings for SU(2). Rigorous weak-coupling control
  (Balaban's small-field RG, PREP §2) holds only while the running coupling g(ℓa) is small, i.e. strictly *below* that scale. The
  estimate sits in the middle range, which is the Bridge itself (PREP §1).
- Each form is as strong as a known open statement: the uniform one-scale Dobrushin–Shlosman condition (B§3.8), or 't Hooft's vortex
  free energy decay (confinement only).
- What it would need, concretely: (i) Balaban-type control from the lattice scale up to a scale where g ~ 1 (UV, partly literature);
  (ii) at that scale, a certified (computer-assisted or bootstrap) bound on κ^∂ or on a soft replica z₂ for the *effective* blocked
  theory, uniform over the UV remainder; (iii) for the twist route, a decoupling lemma covering the centre-neutral channel, which no
  known argument supplies.
- What is realistic: numerics. The quantities are measurable at bounded size (κ by coupled chains, B§5; the twist free energy is
  standard; Leg B's face-to-face lines measure reading 1 of §2.4, which the photon test above predicts to be uninformative on its own).

---

## 4. Photon and Z₂ check, collected

| item | U(1) weak coupling | Z₂ weak coupling | verdict |
|---|---|---|---|
| D1 | hypothesis (entrance below the basin) fails: D3.1 | GDS^∂ fails, so the chain cannot reach γ < 1 | passes (implication only) |
| D0 | conclusion (lattice gap uniform in β) false: hypothesis fails | same | consistent |
| D2 | needs κ^∂ < 1: fails (conditional on FS) | needs κ^∂ < 1: fails (conditional on Chatterjee for finite G) | passes |
| C2 | — | GDS fails while torus events are tame: forces non-generic A | consistent |
| R | vacuous (z₂ = 1) | proves torus decay (true), no boundary uniformity | passes; Z₂ rule read for torus decay (§2.2) |
| §2.4 reading 1 | event rare in U(1): would prove false decay | — | **fails the photon test** |
| §2.4 reading 2 | not rare (twist costs ~β) | not rare (sheet costs ~βℓ²) | passes; controls confinement only |

**Note on RULES.md 2 for Z₂.** "Must fail for Z₂" is right for every boundary-uniform (reach / GDS / area-law) claim. For a torus-decay
claim the correct test is the opposite: it must hold for Z₂ at weak coupling (true gap) and must not imply an area law. Theorem R is of
this second kind.

---

## 5. Lean (built in `~/formal-att-lead`)

| file | content | status |
|---|---|---|
| `Attempts/Lead/Recursion.lean` | `gds_mono`, `GDSAt`, `uniformGDS_iff`, `DoublingRecursion`, `gdsAt_chain`, `uniformGDS_of_recursion`, `uniformGDS_of_recursion_all`, `exists_iterate_le_of_tendsto`, `iterate_contract`, `iterate_sq`, `exists_iterate_sq_le`, `corollaryB_of_recursion` | builds clean (Lean 4.34, Mathlib v4.34.0), 2026-11-21 |
| `Attempts/Lead/Persistence.lean` | `theta_nonneg`, `osc_iter_const`, `comparison` (block Dobrushin comparison theorem) | builds clean, 2026-11-21 |

No `sorry`, no new axioms. The recursion, the entrance, GDS^∂ and the box instantiation of `comparison` are hypotheses or prose.

---

## 6. Report (RULES.md 7)

- **Tried:** the brief's route: κ(ℓ) and a recursion κ(2ℓ) ≤ f(κ(ℓ)); the deterministic consequences; the chessboard engine with a
  bad event; the owner's anchoring-line reading; a replica swap as the decoupling mechanism.
- **Holds:** D1 (formal), D2 (abstract core formal, instance on paper), D0, C1 (modulo FILS), C2, Theorem R (modulo FILS), the
  channel limitation of centre events.
- **Fails, and why:** bounding κ by chessboard (C2: κ is a worst-case quantity; conversion costs e^{O(βℓ^{d−1})}); a κ-only recursion
  that is blind to non-commutativity (D3: the photon shares the small-scale values); the 1-dimensional anchoring-line event (photon
  test: perimeter law); replica agreement for continuous groups (z₂ = 1).
- **Single most promising next step:** retarget the lead route from `UniformGDS` to torus decay (`LevelDecay`), and work on the
  construction problem of §2.4: a reflection-positive coupling of two SU(2) replicas with the correct marginals that agrees exactly on
  a block with positive probability (the soft replica swap). If it exists with z₂ < 1/80 at one physical scale, Theorem R's argument
  (with the coupling in place of μ₂) gives the gap without passing through GDS, and the photon test is built in (U(1) replicas cannot
  agree on a block: the photon's soft modes).
