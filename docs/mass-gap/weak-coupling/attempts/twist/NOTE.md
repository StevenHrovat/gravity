# Route (a): the centre twist and the box influence (attempt round, 2026-11-21)

Status: mathematics plus Lean, 2026-11-21. Not committed. Claim levels: **[Lean]** proved and built, **[proved]** complete proof on
paper here, **[conditional]** proved from stated physics inputs, **[heuristic]**, **[conjecture]**. Rules: `../RULES.md`. Notation and
definitions follow `../../PROOF-NOTE.md` (§1.6 coefficients k^H, k^W; §1.7 GDS) and `../../../formal/OneScale/CorollaryB.lean`
(`UniformGDS`).

---

## 0. Results at a glance

**Verdict.** The twist route, as briefed, does not reach `UniformGDS`. It fails at a precise place, and the reason is structural, not
technical: a centre twist sees only the response of the box to *central jumps* of a boundary link. The hypothesis is dominated by the
response to *continuous* boundary rotations, which no centre argument can see. What the route does give is an exact split of the
influence, an exact vortex representation of the central part, a no-go for "twist free energy" recursions that pins down what
non-abelian input any such recursion must contain, and a side finding about the form of `UniformGDS` in Lean.

| # | statement | level |
|---|---|---|
| T1 | **Split.** k^H(z) ≤ k_coset(z) + 2(1 − 1/\|Z\|)·k_twist(z), and max(k_coset, k_twist) ≤ k^H. For a finite group with Z = G (e.g. Z₂ gauge theory) k_coset = 0, so the whole influence is a twist response (k^H = k_twist for Z₂). | [Lean] `Attempts/Twist/Split.lean` |
| T2 | **Relabelling (vortex representation).** For any Haar-preserving map T (here the twist of a set S′ of block links), q^{σ′}(F) = q^σ((F∘T)·R)/q^σ(R), R = W(σ′\|Tξ)/W(σ\|ξ); for central jumps at z and T = twistAt c S′, R is the weight of the vortex sheet bounded at z. If F∘T = F, \|response\| ≤ sup\|F − a\|·q^σ(\|R/q^σ(R) − 1\|). | [Lean] abstract identity and bound, `Relabel.lean`; [proved] the gauge instantiation (§2.3) |
| T3 | **Layer lemma.** \|μF − νF\| ≤ Σ_r 2τ_r·\|A_r∖A_{r+1}\|·L for nested regions A_r and marginal total variations τ_r. | [Lean] `Layer.lean` |
| T4 | **Scalar obstruction.** From a block-level quantity (total variation, twist free energy via Pinsker) the best possible bound is k(z) ≤ \|V\|·TV_z, so GDS would need Σ_{z∈∂V} TV_z ≤ γ. The layer lemma with exponentially decaying marginals loses a factor (ξ/a)^{d/2−1}. Only a per-link coupling (Hamming transport) has the right scaling, and that is not a twist quantity. | [proved] arithmetic; [heuristic] the scaling estimates |
| T5 | **No-go for structural twist recursions.** A recursion t(2ℓ) ≤ g(t(ℓ)) for the 't Hooft flux free energy, proved from properties shared by U(1) and Z₂ (locality, reflection positivity, Haar invariance, a central element of order 2), cannot have g(x) < x anywhere on the range swept by U(1) in its Coulomb phase or by Z₂ at weak coupling. SU(2) at weak coupling starts inside that range. So in that range a valid proof must use both connectedness (fails for Z₂) and non-commutativity (fails for U(1)). | [conditional] on two standard physics facts (§4.2) |
| T6 | **Where the non-abelian input sits.** In the twist language it is (i) the running of the twist coupling (b₀ > 0, about 0.26 in β per doubling for SU(2): not a tiny effect) and (ii) the manifold of minimal paths from 1 to the centre element (empty for Z₂, two isolated paths for U(1) and c = −1, a 2-sphere for SU(2), CP^{N−1} for SU(N)): the colour orientation of a thick vortex, which is itself charged. | [heuristic] |
| S1 | **Side finding.** Lean `UniformGDS` uses the H-form (`IsInfluenceBound`, single-link *oscillation*); `PROOF-NOTE.md` §7 states (OS_k) in the W-form (GDS_W, per unit distance). By T1 the H-form contains the central-jump part, which the W-form does not. Heuristically the H-form also carries an extra factor ~√β_k (fluctuation width 1/√β), which grows like √log(1/a) along an asymptotically free sequence. The H-form may therefore be false at fixed L₀ where the W-form is true. | [proved] the mismatch; [heuristic] the √β factor |

Photon and Z₂ checks: §5. Tomboulis / Ito–Seiler: §4.3. Most promising next step: §7.

---

## 1. The question in the brief, made precise

The brief: (i) express a shell link's influence on a cube through the cube's response to a centre twist of its boundary; (ii) bound
that response by a twist free energy F(ℓ); (iii) look for F(2ℓ) ≤ g(F(ℓ)).

Objects. B = V is a thin cube, z ∈ ∂B a shell link, q^η = q_B^η the block specification, G compact with a finite central subgroup Z
(SU(2): Z = {±1}). For F on G^B with single-link oscillations δ_y(F) ≤ L (H-form), the response function of z is

  h_{η,F}(g) = q^{η[z ↦ g]}(F),   g ∈ G,

and k^H(z) is the least k with |h(g) − h(g′)| ≤ kL for all η, F, g, g′. Define

- the **twist part** k_twist(z): least k with |h(g) − h(cg)| ≤ kL for all c ∈ Z (the response to a *central jump* of the single link z;
  a centre twist of the boundary along a "ring" of shell links is a product of such jumps, so its response is at most the sum of the
  ring's k_twist values);
- the **coset part** k_coset(z): least k with |P₀h(g) − P₀h(g′)| ≤ kL, where P₀h(g) = |Z|⁻¹ Σ_{c∈Z} h(cg) is the response averaged over
  the centre coset of the boundary value.

These are `IsTwistInfluenceBound` and `IsCosetInfluenceBound` in `Split.lean`.

## 2. What a centre twist sees

### 2.1 T1: the split [Lean]

**Proposition T1.** If 1 ∈ Z, then k^H ≤ k_coset + 2(1 − 1/|Z|)·k_twist. Conversely k_twist ≤ k^H and k_coset ≤ k^H.

*Proof.* |h(g) − P₀h(g)| = |Z|⁻¹|Σ_{c≠1}(h(g) − h(cg))| ≤ (1 − 1/|Z|)k_twist·L; then the triangle inequality through P₀h(g) and P₀h(g′).
The converse: a central jump is a special boundary change, and the coset average of differences is at most their maximum. ∎

Lean: `isInfluenceBound_of_split`, `twist_le`, `coset_le`.

**Corollary T1′ (finite group, Z = G).** P₀h is constant (reindex c ↦ c·g·g′⁻¹), so k_coset = 0 and k^H ≤ 2(1 − 1/|G|)·k_twist. For
Z₂: k^H = k_twist. Lean: `cosetInfluence_univ`, `isInfluenceBound_of_twist_univ`.

**Reading.**
- *Z₂ gauge theory:* the influence is entirely a twist response. Step (i) of the brief holds exactly.
- *U(1):* every element is central. With Z = Z_N ⊂ U(1) the coset part is the response to changes within a coset of Z_N, i.e. all
  small rotations. Averaging over the whole compact centre U(1) (Haar in place of the finite sum) makes the coset part vanish, and the
  whole influence is again a "twist" response, by a *continuous* centre. This is the formal version of the brief's remark "for U(1)
  there is no discrete centre twist, and its continuous flux must pass".
- *SU(2):* the twist part is the response to η_z ↦ −η_z only. **Every small boundary rotation η_z ↦ e^{iθ n·σ}η_z lies in the coset
  part.** So the perturbative (spin-wave, gluon) response of the box, which dominates at weak coupling, is invisible to every centre
  argument. Step (i) holds for central jumps and fails for the rest.
- *W-form.* The note's hypothesis (OS_k) is GDS_W: response per unit ρ(η_z, η′_z). Its supremum is governed by small changes, which are
  all coset part, while a central jump has a fixed ρ(1, c) > 0. So for the W-form hypothesis the twist route contributes nothing; for
  the H-form (Lean `UniformGDS`) it contributes exactly the central-jump part (side finding S1, §6).

Leg B already measures the coset part. Its coupled chains rotate one face link by e^{iθσ₃} with θ = 0.5, and the SU(2) estimate is
"independent of θ (0.05 gives the same)" (`../../../lattice/PREREG-BOUNDARY.md`, feasibility). That is W-type, coset-part behaviour.
The twist BC (Q2) measures a whole-boundary twist, which is bounded by a sum of single-link twist parts (above). It gives a *lower* bound
on Σ_{ring} k_twist, not an upper bound on anything in GDS.

### 2.2 T2: the relabelling identity [Lean, abstract]

For boundary conditions σ, σ′ and any map T of configurations that preserves the product Haar measure,

  q^{σ′}(F) = q^σ((F∘T)·R) / q^σ(R),   R(ξ) = W(splice(σ′, Tξ)) / W(splice(σ, ξ)).

*Proof.* Write both sides as density integrals against π; substitute ξ ↦ Tξ in ∫F·W(σ′|·) dπ and in Z_B(σ′). ∎
Lean: `relabel`. With F∘T = F, ∫(R/m − 1)dq = 0 gives `relabel_response_le`:
|q^{σ′}(F) − q^σ(F)| ≤ sup|F − a| · q^σ(|R/m − 1|), m = q^σ(R).

### 2.3 Gauge instantiation [proved, paper]

Take σ′ = twistAt c {z} σ with c central, z ∉ B, and T = twistAt c S′ with S′ ⊆ B (Haar-preserving: `measurePreserving_twistAt`).
Link by link, splice(twistAt c {z} σ, twistAt c S′ ξ) = twistAt c (S′ ∪ {z}) (splice(σ, ξ)). By `pathHol_twistAt`, each plaquette
holonomy is multiplied by c^{t_p}, with t_p the signed count of passages of p through S′ ∪ {z}, and `plaquetteHolonomy_twistAt_of_zero`
cancels every factor with t_p = 0. So

  R = ∏_{p ∈ P(B), t_p ≠ 0} φ(χ(c^{t_p} U_p)) / φ(χ(U_p)):

**the central jump at z is the insertion of a vortex sheet bounded at z, and S′ moves the sheet anywhere inside the block**, at the price
of composing F with the twist of S′. This is MG3 / `twist_term_vanish` again: the sheet is invisible to every F that does not read S′
and to every plaquette with t_p = 0. It is visible only through R.

- *Dangling z* (PROOF-NOTE §3.6): S′ = the B-links at the dangling endpoint removes every vortex plaquette (R = 1), and the response is
  exactly F ↦ F∘T, a rigid central rotation. This is Lemma 3.5 for central g.
- *Non-dangling z* [sketch]: the endpoints of z are joined by shell paths avoiding z. A sheet-free choice of S′ would make e_z + S′ a cocycle on
  the block complex, hence a coboundary of a central 0-cochain h, with h jumping across z but constant along every shell path: a
  contradiction. So the sheet cannot be removed, only moved. (Sketch: it uses H¹ = 0 of the box complex, true for the thin cube.)

## 3. Twist response versus twist free energy (step (ii))

### 3.1 What a free energy controls

The twist free energy of the block is ΔF = −log q^σ(R) (`R` as above, sheet anywhere). Exactly
KL(q′‖q) + KL(q‖q′) = ∫₀¹ Var_{q_t}(log R) dt along the interpolation q_t ∝ R^t q, and TV ≤ √(KL/2). So a free energy controls at best
the **total variation of the whole block measure**. But k(z) is a *per-link* (Hamming) transport cost.

**Proposition T4 (scalar obstruction) [proved].** For F with δ_y(F) ≤ 1, osc F ≤ |B| (PROOF-NOTE Lemma 2.3), so
|q F − q′ F| ≤ |B|·TV(q, q′), and this is attained for some pairs (point masses differing on every link). So from TV_z alone, GDS in
per-box form (Σ_{z∈∂V} k(z) ≤ γ|V|) follows only if **Σ_{z∈∂V} TV_z ≤ γ**, i.e. an average TV per shell link of order
γ/(2d²ℓ^{d−1}). [heuristic] TV_z is a local quantity that does not decrease with ℓ: for a worst-case η (a "pivot" BC, where a link next to
z has a balanced field), a single change decides that link's value. Leg B's Z₂ coupled pair shows the same: "one flip is absorbed; the
worst case needs a pivot BC". So no statement about a block free energy, of any size, can give GDS.

### 3.2 Spatial resolution: the layer lemma and its loss

**Proposition T3 (layer lemma) [Lean].** For nested A₀ ⊇ A₁ ⊇ … ⊇ A_R = ∅ with marginal TVs τ_r:
|μF − νF| ≤ Σ_r 2τ_r·|A_r ∖ A_{r+1}|·L.
*Proof.* Telescope F_r = F(reference outside A_r); F_r − F_{r+1} depends on A_r and is bounded by |A_r ∖ A_{r+1}|·L (Lemma 2.3). ∎

With A_r = block links at distance ≥ r from z, the influence is bounded by the decay with depth of the joint marginal response.
Combined with T2 (S′ = ∅), the A_r-marginal response is a covariance in the box, Cov_{q^η}(F, R/q(R)), between an observable at depth r
and the vortex weight at z. **Bounding it is decay of correlations in the box: the hypothesis itself.** The twist relabelling moves the
sheet but cannot make it uncorrelated, so step (ii) is circular unless an outside input supplies the decay.

Even with that input the layer lemma is too lossy. [heuristic] Let ξ be the correlation length in lattice units. At weak coupling a
one-link change acts like a point source, and the per-link response at lattice distance ρ falls like ρ^{−(d−1)}e^{−ρ/ξ} (the Poisson-kernel
power of a UV-small source). Then:
- **per-link sum** (what k really is, via the best coupling): Σ_ρ ρ^{d−1}·ρ^{−(d−1)}e^{−ρ/ξ} ~ ξ. Against the GDS budget
  γ|V|/|∂V| ~ γℓ/(2d), this gives the condition ξ_phys ≲ γL₀/(2d): **plausible at fixed L₀**, and failing for the photon (ξ = ∞), as it
  must;
- **layer lemma** (joint-marginal TV of a Gaussian shift beyond depth r, τ_r ~ √β·r^{−d/2}): Σ_r r^{d−1}τ_r ~ √β·ξ^{d/2}, which is
  (ξ/a)² in d = 4 against a budget ~ L₀/a. **Fails as a → 0.**

So the only instrument with the right scaling is a per-link coupling (Σ_y P(ξ_y ≠ ξ′_y), or its Wasserstein analogue). That is what Leg B's
coupled chains estimate, and it is not a twist quantity. Step (ii) fails as posed. T3 is kept because it is correct and records exactly
which loss an influence argument through marginals incurs.

## 4. The recursion (step (iii))

### 4.1 The twist free energy is a step-scaling coupling

Let t(ℓ) = −log(Z_tw/Z) on the ℓ⁴ torus with one unit of 't Hooft flux (central element c through one plane). At small ℓ (in units of
the confinement scale) it is the classical twisted action divided by g²: t ∝ 1/g²(ℓ). Twisted boundary conditions are a standard way to
define a running coupling on the lattice; to my memory the SU(2) step-scaling papers listed in `../../PREP.md` include twisted-BC schemes
(not re-checked here). So **F(2ℓ) ≤ g(F(ℓ)) is a bound on the step-scaling function of a twisted coupling.** Route (a) merges with
route 1 of PREP §4 ("one bound at one scale" via step scaling).

Perturbatively, 1/g² falls by 2b₀ln2 per doubling (b₀ = 11N/(48π²)). For SU(2) that is Δβ ≈ 0.26 per doubling, consistent with the
asymptotic-scaling shift of β per factor 2 in a. **In this variable the non-abelian drift per layer is of order one**, unlike the
10⁻⁵ to 10⁻¹³ of the Migdal–Kadanoff tree picture (README §5). [heuristic, one loop]

### 4.2 T5: no-go for structural recursions [conditional]

*Inputs (standard physics, not proved here):*
(U1) 4D U(1) in its Coulomb phase: t_U(ℓ) → t*_U(β) ∈ (0, ∞) as ℓ → ∞ (flux π spread over the cross-section costs about π²/(2e_R²),
independent of ℓ; PROOF-NOTE §10.2 finds the same ℓ-independence for its witness 2).
(Z2) 4D Z₂ at large β: t_{Z₂}(ℓ) ≈ 2β·ℓ² (one rigid sheet of area ℓ²), increasing in ℓ.

**Proposition T5.** Suppose a proof gives t(2ℓ) ≤ g(t(ℓ)) for all ℓ ≥ ℓ₁ and all weak couplings, with one function g, from properties
that also hold for U(1) and Z₂ with c = −1 (locality, reflection positivity, Haar invariance, a central element of order two, the
decimation structure), so that the same g applies to all three theories. Then g(x) ≥ x on
X_U = {t*_U(β) : β > β_c^{U(1)}} by (U1), and g(x) ≥ x along every Z₂ trajectory by (Z2). So g is **not contracting** on X_U, which
contains [t*_U(β_c⁺), ∞) if t*_U is continuous in β and grows like β (both assumed with (U1)): a range that covers all weak couplings. SU(2) at weak coupling starts in that range, at t ≈ classical twisted action, large.

*Proof.* Apply the hypothetical inequality to U(1) and to Z₂, and pass to the limit ℓ → ∞ in (U1); (Z2) gives t(2ℓ) ≈ 4t(ℓ) > t(ℓ). ∎

**Consequence.** On the range that matters, any valid recursion must use a property that is false for U(1) (non-commutativity) **and**
one that is false for Z₂ (connectedness of G, so the central element can be unwound). A twist argument built only on "a centre element
exists and the measure is RP" proves too much. It is the photon test made sharp for step (iii). Chatterjee's theorem needs connectedness
for the same reason (PROOF-NOTE C6).

### 4.3 Tomboulis 2007 and Ito–Seiler, against this attempt

Read: Ito–Seiler arXiv:0711.4930 (full text) and 0803.3019 (§3–4). Tomboulis (arXiv:0707.2179) runs Migdal–Kadanoff decimations, which
give *upper* bounds on Z. He makes them exact by interpolation parameters, α(t) for Z and α⁺(t) for Z⁺ = ½(Z + Z⁻) (Z⁻ with a centre
vortex), and needs a common t* with **α(t*) = α⁺(t*)** so that the vortex ratio Z⁻/Z is carried unchanged to the coarse lattice.
Ito–Seiler:
1. the existence of t* reduces to an inequality A(α) > A⁺(α) between derivatives of the free energies, which is shown only at strong
   coupling ("not clear where and how his claim is proven for large β");
2. the MK flow goes to strong coupling for U(N) as well as SU(N) in D ≤ 4, so "this proof seems to work even for G = U(1)"; for U(1) at
   large β and r = 1 such a t* does not exist;
3. the extra parameter r < 1 that keeps α away from 1 changes the MK flow: for large β it goes to the *weak*-coupling fixed point
   (their figure: SU(2), r = 0.9, critical β ≈ 4.8);
4. the implicit-function step needs a contraction that is not shown.

The lesson for us is T5 in Tomboulis's language. The step "carry the twisted ratio to the coarse lattice with the same effective
parameters as the untwisted one" is assuming that the twist is invisible at the coarse level, which is the conclusion. Neither the MK
bounds nor the interpolation know about non-commutativity.

**Does this attempt repeat the gap?** No, because it claims no recursion. T1–T4 are identities and inequalities valid for every G
(U(1) and Z₂ included). They claim no reach, so they cannot fail a test. T5 is a no-go that *requires* the missing non-abelian input to
be named. The test for any future recursion along this route: point to the line that is false for U(1) and the line that is false for Z₂.
If neither exists, the argument proves too much.

### 4.4 T6: where the non-abelian input sits [heuristic]

Classically a thick SU(2) vortex is an embedded U(1) flux tube (a geodesic from 1 to −1), with the same action π²/(g²w²) per unit
sheet area at width w. The differences are quantum:
- **running:** g²(w) grows with w (b₀ > 0, antiscreening) and t falls by O(1) per doubling (§4.1); for U(1), b₀ = 0 and t stays put;
- **unwinding manifold:** the minimal paths from 1 to the centre element form a manifold M_c: empty for Z₂ (disconnected: the sheet
  stays thin and pinned), isolated paths for U(1) (one for generic c, two for c = −1; flux conserved: the Coulomb field), a 2-sphere for SU(2) and c = −1,
  CP^{N−1} for SU(N) and c = e^{2πi/N}. A thick vortex's colour orientation is a point of M_c that can vary along the sheet. That
  orientation is itself colour-charged, so this is the non-abelian freedom that disorders it (vortex condensation).

DMP reading (the owner's root swap, PREP "Lead route"): the twist is the change of the colour root's frame; for SU(2) the frame can be
re-chosen continuously and locally (dim M_c > 0, a self-charged choice), for U(1) it cannot (one path), for Z₂ only by a sharp jump. "Each
confined node is its own root" corresponds to M_c being explored independently by each region. This is a reading, not a proof step.

## 5. Photon and Z₂ checks (RULES 2)

| statement | U(1), 4D, weak coupling | Z₂, 4D, weak coupling | verdict |
|---|---|---|---|
| T1 split | holds; with the full compact centre the coset part vanishes, everything is "twist" by a continuous centre | holds; k^H = k_twist exactly | identity, claims no reach: cannot fail a test |
| T2 relabelling | holds (U(1) twists by any angle) | holds | identity |
| T3 layer lemma | holds | holds | inequality between quantities, no reach |
| T4 obstruction | consistent: Coulomb response not resolved by a scalar | consistent: Leg B "pivot BC" | negative statement |
| T5 no-go | U(1) is the input (U1) that makes g non-contracting | Z₂ is the input (Z2) | built from the two tests |
| a twist-only bound on k_twist ⇒ GDS (what the brief hoped) | would give GDS for U(1) (all influence is twist by the continuous centre), contradicting Theorem A + masslessness | would give GDS for Z₂ (T1′), contradicting the pinned-sheet/Polyakov argument (PROOF-NOTE §10.3, heuristic) | **must fail for both; this is why the route stops** |

Leg B feasibility agrees. U(1) Coulomb k̂ grows like ℓ with R_face flat. Z₂ twist at β = 0.6 is long range (D_deep ≈ 2 at every depth). The
SU(2) thin twist at ℓ·a√σ = 2.8 is still seen deep in the box (plateau ten times the random-vortex value). The question for the 4.2
box is whether that plateau falls.

## 6. Side finding S1: H-form versus W-form of the open hypothesis

- `OneScale.CorollaryB.UniformGDS` uses `IsInfluenceBound` (`OneScale/Blocks.lean`), the **H-form**: F with
  |F ξ − F(ξ[y ↦ t])| ≤ L for all t (oscillation, discrete metric). `PROOF-NOTE.md` §7 states (OS_k) as **GDS_W** (Lipschitz, per unit
  ρ). `OneScale/Lipschitz.lean` has the W-form (`IsInfluenceBoundW`, `theoremA_W`). Both chains are valid theorems, but they have
  different open hypotheses. [proved: by reading the definitions]
- By T1 the H-form contains the central-jump part. For SU(2) that part is a thin vortex stub at z (T2), whose influence at weak coupling
  is a non-perturbative object. The W-form does not contain it.
- [heuristic] In the linear-response regime an H-observable can resolve shifts on the scale of the fluctuation width 1/√β, so
  k^H/k^W ~ √β. Along an asymptotically free sequence β_k ~ log(1/a_k), so the H-form budget would need L₀ ≳ 2d√β_k·ξ_phys/γ, which grows
  without bound. **The H-form `UniformGDS` may be false at every fixed L₀ even if the W-form holds.** This should be settled before
  anyone tries to prove the H-form.

Recommendation: state the Lean open hypothesis in the W-form (`IsInfluenceBoundW` with `theoremA_W`), as PROOF-NOTE §7 does, or record
explicitly why the H-form is intended.

## 7. Most promising next step

**One small, new measurement that separates the two parts of the influence.** Add coupled pairs with a **central jump**,
y → y·e^{iπσ₃} = −y, to Leg B's coupled-chain runs: SU(2), one β (2.3), ℓ = 4, 6, 8, calm and typical BC, same aligned heat bath. Compare
k̂_twist(ℓ) with the existing θ = 0.5 coset estimate.
- If the central-jump response decays into the box at least as fast as the coset response, T1 says the twist part adds nothing. The
  hypothesis is then the coset part alone, and the effort belongs to routes (b) and (d), which handle continuous rotations.
- If it stays long-range (a pinned thin stub, as Z₂ and the thin twist BC suggest at these sizes), the H-form `UniformGDS` is strictly
  harder than the W-form, and S1's recommendation becomes urgent.

This is CPU-sized at ℓ ≤ 8 (the feasibility pairs were). It tests something new, not an established number. I did not run it: the queue
belongs to Leg B. Formal companion: if wanted, state `UniformGDS_W` next to `UniformGDS` and prove the W-chain version of
`corollaryB_lattice` (the pieces exist in `Lipschitz.lean`).

## 8. Lean

New files (no existing file changed), built only in WSL `~/formal-att-a`:
- `docs/mass-gap/formal/Attempts/Twist/Split.lean`: `IsTwistInfluenceBound`, `cosetAvg`, `IsCosetInfluenceBound`,
  `isInfluenceBound_of_split` (T1), `twist_le`, `coset_le`, `cosetInfluence_univ`, `isInfluenceBound_of_twist_univ` (T1′).
- `docs/mass-gap/formal/Attempts/Twist/Layer.lean`: `restrictTo`, `layer_bound` (T3).
- `docs/mass-gap/formal/Attempts/Twist/Relabel.lean`: `relabelRatio`, `relabel` (T2), `relabelRatio_bm`, `relabel_response_le`.

All three build in `~/formal-att-a` (Lean 4.34, Mathlib v4.34.0) with no `sorry` and no warnings:
`lake build Attempts.Twist.Split`, `Attempts.Twist.Layer` and `Attempts.Twist.Relabel` each report "Build completed successfully"
(2026-11-21). Not formalised: the gauge instantiation of T2 (§2.3; it needs the splice/twist commutation and
`plaquetteHolonomy_twistAt_of_zero` on the `touching B` product, routine but long), the non-dangling sketch, and T4 to T6
(arithmetic, heuristics and a conditional no-go, not suited to Lean).

What T1 to T3 do *not* contain: no bound on any influence. They are exact bookkeeping, valid for every group, and they cannot pass or
fail the photon test by themselves (§5).
