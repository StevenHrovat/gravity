# Blueprint: the lattice mass gap from one bound at one scale (design study, 2026-11-21)

Status: mathematics design, no Lean yet. It sets out what is a theorem in the literature, what we propose, and what
stays open. Companions: `PREP.md` (route 1, "one bound at one scale"; route 6, admissibility), `SURVEY-LEAN.md`, README §3.2 (photon test) and §4.C (Bridge).
Our formal tools are in `../formal/` (`Influence`, `AreaLaw/Clustering`, `AreaLaw/Reach`, `Positivity`, including the new
`Positivity/General.lean` and `Positivity/Admissible.lean`).

---

## 0. Summary (one page)

**The question.** Spin systems have "one bound in one box" theorems. Dobrushin–Shlosman (1985) is the main one: if, in one finite box, the boundary
condition's influence on the box is small enough (for every boundary condition), then the Gibbs measure is unique and correlations decay
exponentially at all scales. Can this be made gauge invariant for lattice Yang–Mills?

**The answer, in five points.**

1. **The gauge obstruction is real only for the wrong formulations.** Three formulations do fail for gauge reasons:
   - total variation of the joint law of all box links;
   - single-link Dobrushin coefficients;
   - influence measured only on absolutely gauge-invariant observables. These are blind to Wilson lines that run from boundary to
     boundary, so they cannot be iterated.

   The Dobrushin–Shlosman coefficient is an *infimum over couplings*. The box measure is invariant under gauge transformations at
   the box's interior sites, so that infimum already contains the best gauge alignment. **Alignment lemma (§2.3, ours,
   elementary):** the coefficient is unchanged if it is computed on the relative orbit space. That space is configurations modulo
   gauge transformations that are trivial on the boundary. So the classical criterion, applied to link variables, *is*
   gauge-invariant once it is read correctly.
2. **The proposed theorem (§3).** Hypothesis GDS(𝒱, γ): for a family 𝒱 of boxes of side ℓ, the summed boundary influences satisfy
   `Σ_{y∈∂V} k_V(y) ≤ γ·|V|` with γ < 1. Here `k_V(y)` is the worst-case effect of changing the single shell link `y`, measured by
   relatively gauge-invariant Lipschitz (or bounded) observables of the box. **Theorem A:** covariances decay like
   `exp(−λ·dist)` for every `λ < log(1/γ)/(ℓ+2)`, uniformly in the volume and in the boundary condition. The proof is a dual
   Dobrushin comparison: no couplings, no conditional measures, only finite sums and block averages. That makes it well suited to
   Lean. **Theorem C:** reflection positivity turns this into a transfer-matrix gap with no prefactor. **Corollary B (one physical
   scale):** suppose GDS holds in boxes of fixed *physical* size L₀ (ℓ = L₀/a), with the same γ for every lattice spacing a. Then
   the gap in physical units is at least `log(1/γ)/(L₀+3a)`, and it survives every continuum limit of the Schwinger functions,
   including the OpenAI subsequential limits. Vacuum uniqueness comes with it.
3. **The price (honest).** GDS is stronger than a mass gap, in three ways:
   - It controls *every* boundary condition, so by Chatterjee's Theorem 2.4 (arXiv:2006.16229) it also implies unbroken centre
     symmetry and the area law when the centre is nontrivial.
   - It therefore **fails for theories that have a gap but do not confine**: 4D Z₂ at weak coupling, which has a gap
     (Adhikari–Cao 2025) and a perimeter law (Chatterjee 2020). We call this the second unit test, the "Ising-gauge test".
   - For uniformity in the lattice spacing, only the Lipschitz (Wasserstein) variant can work. The total-variation variant must
     fail as a → 0 (heuristic in §3.6).

   For spin systems, conditions of this kind are equivalent to complete analyticity (Dobrushin–Shlosman 1987). For Ising,
   Shlosman (2025) shows that boxes reach all the way to T_c. So the criterion is plausibly sharp, but **as hard as the problem**.
   It localises the difficulty in one box at one physical scale; it does not reduce it.
4. **Tests.**
   - **Photon test, passed in the required sense.** If Theorem A is true, GDS must fail for 4D U(1) at weak coupling, by Froehlich–Spencer. The mechanism is
     the Coulomb response to a boundary change. After alignment, the potentials fall off like `r^{−(d−1)}`, so `k_V(y) ≈ c·ℓ` and
     `Σ k/|V|` does not decrease with ℓ (or with β). Two witnesses: the single-link change, and a boundary condition with constant
     magnetic flux read by the interior smeared flux (scale invariant). A theory with a mass gap gives `Σ k/|V| ≈ C·ξ/ℓ → 0`.
   - **Strong coupling, holds.** With single-link blocks, GDS is exactly Dobrushin's condition `6(d−1)·tanh(nβ) < 1`. That is
     our `Influence.dobrushin_single_link`, so GDS is non-vacuous in our proven window.
   - **The admissible theory** (`Positivity/Admissible.lean`) is a good host. Its worst-case boundary conditions are restricted
     to smooth ones, and site-reflection positivity is proven. It must still fail for admissible U(1). One technical point is
     open: topological sectors (§3.7).
5. **Measurable, not certifiable at β ≈ 2.3.**
   - **Numerics:** coupled heat-bath chains with relative Landau alignment give *upper* estimates of `k_V(y)`, and witness
     observables give *lower* bounds. The supremum over boundary conditions becomes a stated list of classes plus an adversarial
     search.
   - **Rigorous certification:** possible at strong coupling (single links, small blocks, interval arithmetic). At β ≈ 2.3 no
     known method certifies the supremum over all boundary conditions; a bootstrap could rigorously *refute* GDS for given
     boundary conditions, not confirm it. One β in one box would give at most a gap for that single lattice theory.

**Lean (§6):** about 3,500–6,000 lines over 12 lemma groups. Most are standard: the Dobrushin comparison, and the Osterwalder–Seiler
reflection-positivity doubling. New: the alignment lemma, the block-family normalisation, the physical-units interface, and the
admissible variant. Uniform GDS stays a named hypothesis, reported as open, with non-vacuity shown at strong coupling.

**What is literature and what is ours.**
- Literature: the box criterion for spin systems (Dobrushin–Shlosman 1985); the dual comparison technique (Dobrushin 1970,
  Foellmer 1982); the reflection-positivity step (Osterwalder–Seiler 1978); the centre-symmetry consequence (Chatterjee 2021).
- Proposed here: the gauge formulation (relative orbit space, alignment lemma, block-family normalisation); the uniform-spacing
  corollary in this form; the scaling analysis (TV variant against Lipschitz variant); both unit tests applied to the criterion;
  the measurement design.
- I found no gauge-theory finite-size criterion in the literature beyond the remark in Chatterjee 2021 that Dobrushin–Shlosman
  methods give his hypothesis at small β.

---

## 1. Literature: what exists (precise citations)

"Read" means I read the statement in the source today; "memory" means the citation is from memory and must be checked before it is quoted.

### 1.1 Spin systems: one bound in one box

- **R. L. Dobrushin**, "The description of a random field by means of conditional probabilities and conditions of its regularity",
  Theory Probab. Appl. 13 (1968) 197–224; "Prescribing a system of random variables by conditional distributions", Theory Probab.
  Appl. 15 (1970) 458–486. The single-site uniqueness condition (column or row sums of the influence matrix < 1), for general
  metric spin spaces with a Kantorovich (Wasserstein) metric (1970). Memory, standard.
- **R. L. Dobrushin, S. B. Shlosman**, "Constructive criterion for the uniqueness of Gibbs field", in *Statistical Physics and
  Dynamical Systems: Rigorous Results* (Birkhaeuser, 1985) 347–370; "Completely analytical Gibbs fields", same volume, 371–403;
  "Completely analytical interactions: constructive description", J. Stat. Phys. 46 (1987) 983–1014. **Condition C_V** (read in
  Shlosman 2025, below), for a finite-range interaction and a finite box V:
  - The dependence coefficient is `k_{V,y} = max_{σ_{∂V∖y}, σ_y ≠ σ'_y} d_K(q_V(·|σ_{∂V∖y}σ_y), q_V(·|σ_{∂V∖y}σ'_y)) / ρ(σ_y, σ'_y)`.
  - `d_K` is the Kantorovich distance for the metric `ρ_V = Σ_{x∈V} ρ(σ_x, σ̄_x)`.
  - C_V means `Σ_{y∈∂V} k_{V,y} < |V|`. When |V| = 1 it is Dobrushin's condition.
  - Consequence (Dobrushin–Shlosman 1985): a unique Gibbs state with exponentially decaying correlations.
  - The 1987 paper shows that complete analyticity is equivalent to a list of conditions, several of them checkable in one finite
    box (memory: finite spin space, "regular" volumes).
- **R. L. Dobrushin, J. Kolafa, S. B. Shlosman**, "Phase diagram of the two-dimensional Ising antiferromagnet (computer-assisted
  proof)", Commun. Math. Phys. 102 (1985) 89–103. C_V was verified by computer in boxes; this is the model for a rigorous certificate.
  Read (citation).
- **S. Shlosman**, "The critical temperature T_cr(Ising) is DS-computable", arXiv:2505.24750 (v2, Dec 2025). Theorem 4: `sup_V
  β_V(d) = β_cr(d)`. The box conditions C_V reach the whole uniqueness region of the d-dimensional Ising model, so the Dobrushin–Shlosman
  conjecture holds for Ising. Read (abstract and statement summary). The point for us: a one-box criterion can be *sharp*.
- **F. Martinelli, E. Olivieri**, "Approach to equilibrium of Glauber dynamics in the one phase region I, II", Commun. Math. Phys.
  161 (1994) 447–486, 487–514. A finite-size strong-mixing condition at one scale (cubes) implies strong mixing at all scales and a
  uniform log-Sobolev inequality. **F. Martinelli, E. Olivieri, R. H. Schonmann**, Commun. Math. Phys. 165 (1994) 33–47: in d = 2,
  weak mixing implies strong mixing. Memory.
- **D. W. Stroock, B. Zegarlinski**, Commun. Math. Phys. 144 (1992) 303–323 (Dobrushin–Shlosman mixing ⇔ log-Sobolev, finite spins) and 149
  (1992) 175–193. **B. Zegarlinski**, "Dobrushin uniqueness theorem and logarithmic Sobolev inequalities", J. Funct. Anal. 105
  (1992) 77–111 (read: citation confirmed). Memory for the content.
- **H. Foellmer**, "A covariance estimate for Gibbs measures", J. Funct. Anal. 46 (1982) 387–395: the dual (oscillation) form of
  Dobrushin's comparison that §3.2 uses. Memory.
- **J. van den Berg, C. Maes**, "Disagreement percolation in the study of Markov fields", Ann. Probab. 22 (1994) 749–763. **D.
  Weitz**, "Combinatorial criteria for uniqueness of Gibbs measures", Random Structures Algorithms 27 (2005) 445–475 (path
  coupling, general graphs; read: abstract only). Memory for details.
- **F. Otto, M. G. Reznikoff**, "A new criterion for the logarithmic Sobolev inequality and two applications", J. Funct. Anal. 243
  (2007) 121–157. A two-scale criterion: decay of correlations implies a log-Sobolev inequality uniform in the volume, for continuous
  spins. **G. Menz**, "The approach of Otto–Reznikoff revisited", Electron. J. Probab. 19 (2014) no. 107. Read (citations and
  abstract).

### 1.2 Lattice gauge theory: probabilistic, strong-coupling side

- **K. Osterwalder, E. Seiler**, "Gauge field theories on a lattice", Ann. Phys. 110 (1978) 440–471: reflection positivity, transfer
  matrix, gap and confinement at strong coupling. **E. Seiler**, *Gauge Theories as a Problem of Constructive Quantum Field Theory and
  Statistical Mechanics*, Lecture Notes in Physics 159 (Springer, 1982). Memory; I recall no finite-size criterion in it (not
  re-read).
- **S. Chatterjee**, "A probabilistic mechanism for quark confinement", Commun. Math. Phys. (2021), DOI 10.1007/s00220-021-04086-y,
  arXiv:2006.16229 (read: §2 in full). The details we need:
  - **Definition 2.3:** the theory "satisfies exponential decay of correlations under arbitrary boundary conditions" if there
    are `K₁, K₂` (depending only on G, β, d) such that for any cube B, any boundary condition δ on B (G-values on the boundary edges)
    and any local functions f, g supported on edges in B with values in [−1, 1]:
    `|⟨fg⟩_{B,δ} − ⟨f⟩_{B,δ}⟨g⟩_{B,δ}| ≤ K₁ e^{−K₂ dist(f,g)}`. The local functions are **not** required to be gauge invariant.
  - **Theorem 2.4:** under Definition 2.3, centre symmetry is unbroken. If the representation acts nontrivially on the centre,
    every Gibbs measure satisfies the area law.
  - The text adds that Definition 2.3 "can be shown to hold for essentially any lattice gauge theory when β is small enough,
    using the methods of Dobrushin and Shlosman". It is "not clear whether" the mass-gap belief "includes the strong version".
    Theories with finite groups are believed gapped but not confining, so for them centre symmetry must break.
- **H. Shen, R. Zhu, X. Zhu**, "A stochastic analysis approach to lattice Yang–Mills at strong coupling", Commun. Math. Phys. 400
  (2023) 805–851, arXiv:2204.12737: Langevin dynamics, Bakry–Émery, log-Sobolev and Poincaré inequalities, uniqueness, mass gap;
  SO(N), SU(N); β < 1/(16(d−1)) in their normalisation. Read (citation).
- **S. Cao, R. Nissim, S. Sheffield**, "Dynamical approach to area law for lattice Yang–Mills", arXiv:2509.04688 (2025): verifies
  the "mass gap condition of [DF80]" by the Shen–Zhu–Zhu dynamics, which gives the area law in the 't Hooft regime; U(N), SU(N), SO(2N).
  Read (abstract). **B. Durhuus, J. Froehlich**, "A connection between ν-dimensional Yang–Mills theory and (ν−1)-dimensional,
  non-linear σ-models", Commun. Math. Phys. 75 (1980) 103–151 (memory): confinement follows from decay in a (d−1)-dimensional σ-model,
  uniformly in external fields. This is another "uniform over boundary data" hypothesis, close to ours.
- **`mrdouglasny/lgt`** (Lean): the single-site Dobrushin gap for U(n), β < 1/(32n(d−1)) (`SURVEY-LEAN.md` §3). This is condition C_V with |V| = 1,
  in Lean.

### 1.3 Weak coupling: the test cases

- **A. Guth**, Phys. Rev. D 21 (1980) 2291; **J. Froehlich, T. Spencer**, "Massless phases and symmetry restoration in abelian gauge
  theories and spin systems", Commun. Math. Phys. 83 (1982) 411–454: the 4D U(1) Coulomb phase (Villain action; whether FS cover
  Wilson's action as stated must be checked in the paper). **M. Goepfert, G. Mack**, Commun. Math. Phys. 82 (1982) 545: 3D U(1) has a
  gap at all couplings (no photon test in 3D).
- **S. Chatterjee**, "Wilson loops in Ising lattice gauge theory", arXiv:1811.09770 (Commun. Math. Phys., 2020; volume from memory
  377, 307–340): the Wilson loop in 4D Z₂ at weak coupling to leading order (perimeter behaviour), and exponential decay of correlations there.
  Read (abstract). **S. Cao**, "Wilson loop expectations in lattice gauge theories with finite gauge groups", Commun. Math. Phys.
  (2020) (memory).
- **M. P. Forsstroem**, "Decay of correlations in finite Abelian lattice gauge theories", Commun. Math. Phys. 393 (2022) 1311–1346,
  arXiv:2104.03752. Read (Theorem 1.1, method):
  - Free boundary conditions, Z⁴, finite abelian G.
  - `|Cov(f₁(dσ), f₂(dσ))| ≤ C₁‖f₁‖‖f₂‖(30 α(β))^{dist}`, with `α(β) = Σ_{g≠0} φ_β(g)²`.
  - The method is a coupling on **plaquette configurations ω = dσ**, which are the gauge-invariant variables in the abelian case
    (Lemma 2.7: the weight ratio of a plaquette pattern is its activity). This is the abelian form of "work on the orbit space".
- **A. Adhikari, S. Cao**, "Correlation decay for finite lattice gauge theories at weak coupling", Ann. Probab. 53 (2025) 140–174,
  arXiv:2202.10375. Exponential decay for a wide class of gauge-invariant functions (including any function of Wilson loops), finite
  possibly non-abelian G, weak coupling (read: abstract). These theories have **a gap without confinement**: the reference cases for
  the Ising-gauge test (§4.2).

### 1.4 Finite-volume criteria for *confinement* (gauge-invariant, at one scale)

- **G. Mack, V. B. Petkova**, Ann. Phys. 123 (1979) 442–467 (comparison of Z₂ and SU(2)); "Sufficient condition for confinement of static
  quarks by a vortex condensation mechanism", Ann. Phys. 125 (1980) 117–134 (memory). A bound on thick-vortex free energies at one
  scale implies confinement. **G. 't Hooft**, Nucl. Phys. B 153 (1979) 141 (twisted boundary conditions, flux free energies). **E. T. Tomboulis,
  L. G. Yaffe**, Commun. Math. Phys. 100 (1985) 313–329 (rigorous inequalities between vortex free energy and Wilson/Polyakov loops). **C.
  Borgs, E. Seiler**, Commun. Math. Phys. 91 (1983) 329–380 (finite temperature, confinement problem). **T. G. Kovács, E. T.
  Tomboulis**, Phys. Rev. Lett. 85 (2000) 704 (vortex free energy computed numerically for SU(2)). All memory. These are the
  closest existing "one bound at one scale" statements for gauge theories, and they concern confinement, not the gap. The twisted
  boundary condition reappears below as the natural worst case (§4, §5).

### 1.5 Renormalisation group, gauge-covariant blocking

T. Bałaban:
- "Propagators and renormalization transformations for lattice gauge theories I, II", Commun. Math. Phys. 95 (1984) 17–40 and
  96 (1984) 223–250.
- "Averaging operations for lattice gauge theories", Commun. Math. Phys. 98 (1985) 17–51.
- "Renormalization group approach to lattice gauge field theories I, II", Commun. Math. Phys. 109 (1987) 249–301 and 116 (1988) 1–22.
- "Large field renormalization I, II", Commun. Math. Phys. 122 (1989) 175–202 and 355–392.

J. Dimock's expositions: arXiv:1108.1335, 1212.5562, 1304.0705. P. Federbush's phase-cell papers (Commun. Math. Phys. 107 (1986) onwards).
Magnen–Rivasseau–Sénéor (1993). All memory except as in `PREP.md`. Gauge-covariant block variables give a third way to state the
hypothesis (§3.7, variant 3); our main formulation does not need them.

### 1.6 What I did not find

Searches on 2026-11-21 (web, arXiv; queries on Dobrushin–Shlosman and complete analyticity for gauge theories, gauge-invariant mixing,
finite-size criteria for gauge theories) found:
- no paper that states a box criterion (Dobrushin–Shlosman, Martinelli–Olivieri or Stroock–Zegarlinski type) for lattice gauge
  theories and addresses the gauge redundancy;
- no gauge version of disagreement percolation for continuous groups.

The only hits were unrefereed Zenodo preprints (2026) that invoke "Dobrushin–Shlosman complete analyticity" for truncated SU(2), not
checked. Chatterjee's remark (§1.2) is the only refereed statement linking Dobrushin–Shlosman and gauge theory that I found.

---

## 2. Where the gauge redundancy bites, and where it does not

### 2.1 Setting and notation

- Lattice (ℤ/Nℤ)^d (or a cube with a boundary condition); links E with an orientation; plaquettes P; compact group G with normalised Haar
  measure λ; a unitary representation with `|Re tr| ≤ n`.
- Plaquette weight `∏_p φ(Re tr U_p)` with φ measurable, nonnegative and bounded on [−n, n]. This covers Wilson
  (`φ = exp(β·)`) and admissible Wilson (`φ = exp(β·)·1[n − x ≤ ε]`), as in `Positivity/General.lean`.
- For a link set V: the **shell** ∂V is the set of links outside V that share a plaquette with a link of V.
  The **conditional law** is `q_V^τ(dU_V) ∝ ∏_{p touches V} φ(Re tr U_p) · λ^{⊗V}(dU_V)`, for a boundary configuration τ ∈ G^{∂V}.
  It is explicit, so no disintegration is needed. For the admissible weight, τ is *allowed* if the normaliser is positive.
- Markov property: under the full measure μ, the conditional law of U_V given everything else depends only on U_{∂V} and equals
  `q_V^{U_{∂V}}`.
- **Relative gauge group** `K_V = G^{int(V)}`, where int(V) is the set of sites all of whose incident links lie in V. A gauge
  transformation k ∈ K_V maps `U_e ↦ k_{s(e)} U_e k_{t(e)}^{−1}` (with k = 1 off int(V)). It fixes the shell. `q_V^τ` is
  K_V-invariant (Haar bi-invariance; the plaquette weights are class functions).

### 2.2 Three naive formulations that fail for gauge reasons

1. **Total variation of the joint law of all box links, for boundary conditions that are gauge related.** Let τ' = h·τ with h a
   gauge transformation at the box's boundary sites. Then `q^{τ'} = h̃_* q^τ`, where h̃ extends h by 1 inside. The links adjacent to the
   boundary sites are rotated by h. At weak coupling their joint law is concentrated, so the total variation is ≈ 1, although nothing physical changed.
   This is the obstruction named in the brief. Note that the *deep* interior (links touching no boundary site) has exactly the same law
   under τ and h·τ. So even this failure is a surface effect, not a bulk one.
2. **Single-link Dobrushin (|V| = 1).** At weak coupling the conditional law of one link has width ~β^{−1/2}. Changing one staple moves its
   peak by O(1/(2(d−1))), so the influence is ≈ 1. That failure is physical (the coupling is weak at the lattice scale), not a gauge
   artefact. It is why `lgt` and `Influence` stop near β ≈ 0.01–0.13.
3. **Influence measured on absolutely gauge-invariant observables of an inner box only** (the total variation of the laws of Wilson
   loops in the inner box). This is invariant under everything, but too weak to iterate. Gluing the inner box to the shell needs
   the *relative* invariants. These are the open Wilson lines (parallel transporters) between boundary sites, as matrices, and
   Chatterjee's "vertical chain variables". Knowing that inner-box loops agree in law says nothing about how the inner region is
   oriented relative to the boundary. I know no counterexample in which (3) holds and decay fails, and no proof that (3) suffices.
   I treat it as insufficient by default.

### 2.3 The alignment lemma (proposed; elementary)

Let ρ be a bi-invariant metric on G (geodesic distance, Frobenius distance ‖a − b‖, or the discrete metric 1[a ≠ b]). Let
`ρ_V(U, U') = Σ_{e∈V} ρ(U_e, U'_e)` and the **relative orbit distance** `ρ̄_V(U, U') = min_{k∈K_V} ρ_V(k·U, U')`.

**Lemma 2.3 (alignment).** For K_V-invariant probability measures μ, ν on G^V:

  `d_K(μ, ν; ρ_V) = d_K(μ, ν; ρ̄_V)`,

and the dual (oscillation or Lipschitz) form of `d_K` can be restricted to K_V-invariant test functions without changing its value.

*Proof.* "≥" holds because ρ̄ ≤ ρ. "≤": take a coupling (U, U') and a measurable near-minimiser k* = k*(U, U'), plus an independent
Haar element ĥ ∈ K_V. Set X = ĥk*·U and Y = ĥ·U'. Then ρ_V(X, Y) = ρ_V(k*U, U') by bi-invariance. Y ~ ν by K-invariance. Given (U, U'),
ĥk* is Haar distributed, so X ~ μ. For the dual form, average a test function f over K_V. The link-wise oscillations do not
grow, because k acts on each link separately: `δ_e(f∘k) = δ_e(f)`. ∎

**Consequence.** The Dobrushin–Shlosman coefficient computed from the link variables equals the coefficient computed on the relative
orbit space. It depends on (τ, τ') only through their joint gauge class under the full gauge group. So the criterion *is* gauge
invariant once it is read correctly. What remains is the choice of metric (§3.6) and the physics.

### 2.4 Consequence: the remaining obstruction is physical

With alignment, what the box criterion sees is the **physical response** of the box to a boundary disturbance:
- **Massless response.** Below the correlation length, a weakly coupled gauge field responds like a Coulomb field: field strength
  `~ r^{−d}`, aligned potentials `~ r^{−(d−1)}`. The summed influence of one boundary link grows like the box side. The criterion
  then holds only once ℓ ≫ ξ, and never for U(1) in the Coulomb phase.
- **Pinned extended objects.** In a deconfined theory with a centre (Z₂ at weak coupling), a boundary condition can pin a vortex
  sheet whose position flips when one boundary link changes. The criterion fails at every ℓ (§4.2).

Both are physics, and both are exactly what a valid criterion must see.

---

## 3. The proposed theorem

### 3.1 Definitions

- **Block family** 𝒱: a finite family of link sets on the torus, invariant under the lattice translations and the hypercubic
  rotations (main case: all translates and rotations of the cube link set `V_ℓ` = all links with both ends in {0,…,ℓ}^d; minimal case:
  all single links). `D(𝒱) = max_{V} diam_∞(V ∪ ∂V)` (≤ ℓ + 2 for cubes). `c(z) = #{V ∈ 𝒱 : z ∈ V}`.
- **Oscillation and Lipschitz seminorms** of f on configurations:
  - (H) `δ_x(f) = sup{|f(σ) − f(σ')| : σ, σ' differ only at x}`;
  - (W) `L_x(f) = sup{|f(σ) − f(σ')| / ρ(σ_x, σ'_x) : σ, σ' differ only at x}` (ρ a bi-invariant Riemannian distance on G).

  For the admissible theory the suprema run over pairs of allowed configurations (§3.7).
- **Boundary influence of a shell link** z ∈ ∂V, in dual form (Kantorovich duality is not needed; this definition is what the proof
  uses):
  - (H) `k_V(z) = sup{ |q_V^τ(f) − q_V^{τ'}(f)| : τ, τ' allowed, equal off z; f relatively gauge-invariant, δ_x(f) ≤ 1 ∀x ∈ V }`;
  - (W) `k_V(z) = sup{ |q_V^τ(f) − q_V^{τ'}(f)| / ρ(τ_z, τ'_z) : …, L_x(f) ≤ 1 ∀x ∈ V }`.

  By Lemma 2.3, "relatively gauge-invariant" can be added or dropped without changing k. With the coupling definition (Dobrushin–Shlosman)
  `k_V(z)` is at most the Dobrushin–Shlosman coefficient, so our hypothesis is the weaker one.
- **Hypothesis GDS(𝒱, γ):** for every link z,

  `Σ_{V ∈ 𝒱 : z ∈ ∂V} k_V(z) ≤ γ · c(z)`,   with γ < 1.

  For the cube family with hypercubic symmetry this reads `Σ_{y∈∂V_ℓ} k_{V_ℓ}(y) ≤ γ |V_ℓ|`, which is Dobrushin–Shlosman's C_V with γ in
  place of 1. For single links it reads `Σ_{x : z ∈ ∂{x}} k_{{x}}(z) ≤ γ`, which is Dobrushin's condition.

### 3.2 Theorem A (decay from one box)

**Theorem A (proposed form; a Dobrushin–Shlosman / Foellmer-type statement, adapted).** Assume GDS(𝒱, γ). Let λ > 0 satisfy
`ρ_λ := γ·e^{λ D} < 1`, with D = D(𝒱). For every torus with N ≥ 2D + 2, and for every cube with every allowed boundary condition, take
f bounded and supported on a link set A, and g on S_g:
- (H) `|Cov(f, g)| ≤ ‖f‖_∞ · ‖g‖_∞ · C_H(A, S_g) · e^{−λ (dist(A, S_g) − 2D)}`;
- (W) the same with `‖g‖_∞` replaced by `max_x L_x(g) · diam_ρ(G)`.

Here `C_H ≤ 2 |S_g| |N_D(A)| / (1 − ρ_λ)`, where N_D(A) is the set of links within distance D of A. Nothing depends on N or on the
boundary condition. The rate is any `λ < log(1/γ)/D`.

**Proof sketch (dual form; no couplings).**
- Let 𝒱_A be the blocks disjoint from A. For V ∈ 𝒱_A define the block average `P_V h(σ) = ∫ h(σ_{V^c}, ξ) q_V^{σ_{∂V}}(dξ)`, and
  `P = M^{−1} Σ_{V∈𝒱_A} P_V`.
- Because f does not depend on V-coordinates, `P_V(fh) = f·P_V h`, and μ(P_V h) = μ(h) by the Markov property. So
  `Cov(f, g) = μ(f·(P^t g − μ(g)))` for every t.
- The seminorms satisfy:
  - `δ_x(P_V h) = 0` for x ∈ V;
  - `δ_z(P_V h) ≤ δ_z(h)` for z ∉ V ∪ ∂V;
  - `δ_z(P_V h) ≤ δ_z(h) + k_V(z)·max_{x∈V} δ_x(h)` for z ∈ ∂V. This is the definition of k_V, applied to ξ ↦ h(σ_{V^c}, ξ).
- Let S = A ∪ (links in no block of 𝒱_A) ⊂ N_D(A), and weight w(x) = e^{−λ·dist(x, S_g)}. On S^c the weighted sup-norm `‖δ(h)/w‖` contracts:
  `δ_x(Ph) ≤ w(x)‖δ/w‖ [1 − (c(x)/M)(1 − γ e^{λD})]`. This uses GDS and `max_{V} w ≤ e^{λD} w(z)` for z ∈ ∂V.
- On S the seminorms grow by at most a geometric series. So as t → ∞, `δ_x(P^t g) → 0` off S and
  `δ_x(P^t g) ≤ 2‖g‖ e^{λD} w(x)/(1 − ρ_λ)` on S.
- Finally `|P^t g(σ) − μ(P^t g)| ≤ Σ_x δ_x(P^t g)`, by changing one link at a time. ∎

For (W), replace δ by L and add a factor diam_ρ(G) in the last step. Everything is finite linear algebra on the torus plus Fubini for P_V.
Literature status: this is Dobrushin's comparison theorem in Foellmer's dual form, with blocks and averaging (Dobrushin–Shlosman 1985,
Weitz 2005 for the coupling version). The gauge-specific content is §2.3 and the block-family normalisation. Dobrushin–Shlosman's paper
should be checked for whether it already covers compact metric spin spaces; we do not depend on it, since the proof above is self-contained.

**Corollary A′ (arbitrary boundary conditions; centre).**
- GDS_H gives Chatterjee's Definition 2.3, with K₂ = λ in lattice-distance units.
- If the centre of G is nontrivial, Chatterjee's Theorem 2.4 then gives unbroken centre symmetry and the area law.
- Hence GDS_H *cannot* hold for a theory with a centre that deconfines.

### 3.3 Theorem C (reflection positivity: from decay to a gap, with no prefactor)

Let Θ be the site reflection t ↦ −t on the torus (N even); RP holds for every φ (`rp_plaquette_weight`). Take F depending on links in
the time slab [1, s] and let F_j be its translate by j in time. By translation and reflection invariance, `⟨Θ F_j · F_k⟩_c = h(j+k)`.
RP Cauchy–Schwarz (`rp_plaquette_weight_gram`) gives `h(j+k)² ≤ h(2j) h(2k)`, hence by induction

  `h(k) ≤ h(0)^{1−2^{−r}} · h(2^r k)^{2^{−r}}`   whenever 2^{r+1}(k+s) < N.

If Theorem A gives `|h(m)| ≤ C e^{−λ m}`, then `h(k) ≤ h(0)^{1−2^{−r}} C^{2^{−r}} e^{−λ k}`. As N → ∞ and then r → ∞:
`h(k) ≤ h(0) e^{−λ k}`. The constant C, which depends on the support of F and on the lattice spacing, disappears. In transfer-matrix
language (Osterwalder–Seiler 1978): the spectrum of the transfer matrix on the vacuum-orthogonal space lies in [0, e^{−λ}], so the
lattice Hamiltonian has gap ≥ λ in lattice units (Lipschitz local F are dense). Standard; the doubling form avoids the spectral
theorem in Lean.

### 3.4 Corollary B (one physical scale; uniform in the lattice spacing)

**Corollary B (proposed).** Take a scaling sequence (a_k → 0, β_k), for instance the OpenAI `Schedule` family (`SURVEY-LEAN.md` §4).
Fix a physical length L₀ and γ < 1. If **GDS_W(𝒱_{ℓ_k}, γ) holds for every k, with ℓ_k = ⌈L₀/a_k⌉**, then:
1. for every k and every volume, the transfer-matrix gap in physical units is at least `log(1/γ)/(L₀ + 3a_k)`
   (Theorems A and C, with D ≤ ℓ_k + 2);
2. every continuum limit of the renormalised Schwinger functions satisfies `⟨ΘF, e^{−tH}F⟩_c ≤ e^{−m t}⟨ΘF, F⟩_c` with
   m = log(1/γ)/L₀. The inequality has no prefactor, so it passes to limits of both sides. So the reconstructed Hamiltonian has a
   gap ≥ m, and clustering gives a **unique vacuum**, which the committee lists as open for the OpenAI construction;
3. if the centre is nontrivial and GDS_H also holds at each k: the area law at each k (no uniform string tension follows).

This is README §4.C's Bridge in a form that **needs no blocking and no RG map**. The fine-lattice box of side L₀/a plays the role of the
block, and the hypothesis is stated directly on the fine-lattice conditional measure. The cost: the box has (L₀/a)^d links, and
uniformity as a → 0 is exactly the physics nobody controls.

### 3.5 Theorem A at one β is already worth something

At a single β (no limit): GDS at ℓ = 8, γ = 0.5 would give a rigorous lattice gap ≥ log 2/10 in lattice units for that theory. That
would be a new theorem at β ≈ 2.3 (the proven windows stop near 0.08–0.13, or 0.42 in unrefereed claims). It says nothing about the
continuum.

### 3.6 Scaling heuristics: why only the Lipschitz (W) variant can be uniform in a

These are heuristics in the Gaussian (perturbative) picture below the correlation length ξ (physical units), in lattice units r.
A single shell link changed by θ produces, after alignment:
- potential responses `|A(x)| ~ θ r^{−(d−1)}` out to r ~ ξ/a, then exponential decay;
- field strengths `~ θ r^{−d}`.

- **W variant.** `k_V(z) ≈ Σ_x |A(x)|/θ ~ c·ξ/a` (half ball; the sum of `r^{d−1}·r^{−(d−1)}` is linear in the radius). With
  `|∂V|/|V| ≈ 2(d−1)·2/ℓ`, GDS_W reads roughly `c′ ξ/L₀ ≤ γ`: **independent of a**. So L₀ of a few ξ/γ is the natural scale.
- **H variant.** Exact agreement (Hamming) of a perturbative response is expensive. Confining the disagreement to radius R fails with
  probability ~ √β θ R^{−(d−2)/2} (the energy of the remaining response). Optimising over scales gives `k_V(z) ~ (ξ/a)^{d²/(d+1)}`
  (up to powers of β), against a budget `γ ℓ/(2(d−1)) ∝ L₀/a`. So GDS_H fails as a → 0 at fixed L₀. **Conclusion:** use GDS_W for
  Corollary B, and GDS_H at one β (it matches Chatterjee's bounded observables and our total-variation tools).
- **U(1), no ξ.** `k_V(z) ≈ c ℓ` with c independent of β, so `Σ k/|V|` is a fixed number as ℓ → ∞. By Theorem A and Froehlich–Spencer,
  this number must be ≥ 1 in the Coulomb phase (§4.1). For a massless *scalar* field the analogous identity is exact: harmonic measure
  sums to one, so Σ k = |V|, marginal. For the gauge field I have no closed form; only the logic of §4.1 fixes the inequality.

### 3.7 Variants

1. **Admissible theory** (route 6; `Positivity/Admissible.lean`). Theorem A's proof is unchanged, with one exception. The last step
   ("change one link at a time") and the definition of δ_x need paths of allowed configurations differing in single links. For small
   ε, Luescher's admissible space splits into **topological sectors**, so single-link paths do not connect everything. Fixes, in
   order of preference: (a) state δ_x over allowed pairs and assume single-link connectivity of allowed configurations inside each
   block (true for ε large enough; to be checked); (b) replace single-link telescoping by block telescoping; (c) use a soft
   admissibility weight. The gains:
   - "for all τ" shrinks to admissible τ (smooth at the lattice scale), which removes the lattice-scale-rough boundary
     conditions that are irrelevant to physics and hardest for numerics;
   - large fields are absent;
   - site RP is proven (`admissible_rp`), which is all Theorem C needs.

   The photon test is unchanged: admissible U(1) is still massless, so GDS must fail for it. Whether topology freezing at small ε
   (fixed sectors) causes genuine long-range memory under fixed boundary conditions is a physics question to watch.
2. **Axial or maximal-tree gauge in the box.** Fixing K_V completely by a forest rooted at the boundary sites turns q_V^τ into a
   spin system with no gauge freedom. Any fixed gauge is one particular alignment, so its coefficients are ≥ the aligned ones.
   In axial gauge a local field change shows up along whole axial strings, inflating Σ_x by a factor ~ℓ. Valid but lossy;
   use alignment instead.
3. **Bałaban's gauge-covariant block averages.** Applying the Dobrushin–Shlosman condition to the blocked theory needs the blocked
   specification, which is non-local and not explicit. That is the README Bridge as originally stated. Not needed for the
   reduction; probably needed for any *proof* of GDS at small a.
4. **Martinelli–Olivieri form** (strong mixing in one cube for boundary conditions differing on a set Y, observed at distance ≥ ℓ/2). By
   K_V-invariance its raw and relative-invariant versions coincide (Lemma 2.3). It is a natural *measurement* target (§5) and implies
   the same conclusions for spin systems; we do not prove the gauge version here.

### 3.8 How strong is GDS? (the honest frame)

- **It implies more than the gap.** Corollary A′ gives confinement too. It is **not necessary** for a gap: Z₂ at weak coupling has a
  gap and violates it (§4.2). For SU(N), confinement and a gap are both believed at all β, so GDS is plausible but unproven.
  Chatterjee: "not clear whether" the gap belief includes the boundary-uniform version.
- **It is plausibly sharp.**
  - For finite-spin systems, one-box conditions are equivalent to complete analyticity (Dobrushin–Shlosman 1987), and boxes exhaust
    the Ising uniqueness region (Shlosman 2025).
  - For continuous spins, conditions of this kind are equivalent to a uniform log-Sobolev inequality (Stroock–Zegarlinski,
    Zegarlinski, Otto–Reznikoff, Menz).
  - Shen–Zhu–Zhu prove such a log-Sobolev inequality for lattice Yang–Mills at strong coupling.

  The expected picture is the triangle: GDS at some scale ⇔ uniform log-Sobolev for the Yang–Mills Langevin dynamics ⇔ strong mixing
  under all boundary conditions. None of the gauge-theory arrows is proven; they are a target.
- **It localises, it does not reduce.** Corollary B needs GDS_W at L₀/a for *all* a, an infinite family of box statements. This is
  the README §4.C caveat, now with a precise, gauge-invariant, measurable hypothesis.

---

## 4. Tests

### 4.1 The photon test (4D U(1), weak coupling): GDS must fail, and does

- **Logic (rigorous, given Theorem A).** If GDS_H or GDS_W held for 4D U(1) at some β in the Coulomb phase, Theorems A and C would give
  exponential decay and a gap, contradicting Guth and Froehlich–Spencer. So for every box family and every γ < 1, GDS fails there. Any
  "version" that would pass for U(1) contradicts a theorem, and must therefore be an invalid version of Theorem A (this is how the test
  sorts proposals).
- **Mechanism (heuristic, §3.6).** One shell link changed: an aligned Coulomb response with `|A| ~ r^{−(d−1)}` through the whole box.
  `k_V(z) ≈ c ℓ`, so `Σ k/|V|` is constant in ℓ and in β. Nothing improves with the box size.
- **Witness 1 (single link, numerics):** `R(ℓ) = Σ_{y∈∂V} k̂_V(y)/|V|` from coupled chains (§5.1). Prediction: flat or rising in ℓ, ≳ 1,
  in the Coulomb phase; falling like ξ/ℓ in the confined phase (β < 1).
- **Witness 2 (boundary flux, gauge-invariant, Martinelli–Olivieri form):**
  - Boundary conditions: τ₀ trivial, against τ_b, which carries a constant magnetic field b in the (1,2) planes (links
    `e^{i b x₁}` on direction-2 boundary links), total flux Φ = bℓ² ≈ π through a cross-section.
  - Interior observable: the smeared flux `F̄ = mean of sin θ_p` over the (1,2)-plaquettes of the inner half-box.
  - In the Coulomb phase the interior carries the field b. The Gaussian Kullback–Leibler divergence between the two interior laws
    is `≈ (β/2) b² |inner| ≈ β π²/32`, *independent of ℓ*, so the influence stays ≈ 1 − e^{−cβ} at every ℓ (scale invariance).
  - In a confining theory the flux is screened (SU(2): a centre-flux boundary condition is the 't Hooft twist, whose free energy
    vanishes exponentially in ℓ when the theory confines), so the influence → 0.

  This is the probe that Shot 2 (`../dobrushin/README.md`, typical walls, local energy) lacked. That probe could not tell the
  Coulomb phase from the confined one because it only read the energy, which couples to *pairs* of photons. The flux witness reads the
  odd, flux-carrying part.
- **Admissible U(1):** unchanged (smooth flux boundary conditions are admissible for small b).

### 4.2 The Ising-gauge test (4D Z₂, weak coupling): gap present, GDS must still fail

- **Logic.** Z₂ at large β has exponential decay for gauge-invariant observables (Adhikari–Cao, Forsstroem: free boundary conditions)
  and a perimeter law (Chatterjee 2020). GDS_H ⇒ Chatterjee's Definition 2.3 ⇒ area law (Theorem 2.4), a contradiction. So GDS fails
  for Z₂ at weak coupling, although the theory is gapped.
- **Mechanism (heuristic).** Take a boundary condition whose twist (the boundary curve of a vortex sheet) is balanced, so that two
  minimal sheets through the box have equal action. Flipping one boundary link y decides which sheet the interior carries, so
  `k_V(y) ≳ ℓ²` (the sheet area). Each y has its own worst τ, so `Σ_y k_V(y) ≳ ℓ^{d−1}·ℓ² ≫ |V| = ℓ^d` in d = 4.
- **For SU(N)** the same twist boundary conditions are harmless if vortices are condensed (zero vortex free energy: confinement).
  This links GDS to PREP route 5 (twist free energy) and to Mack–Petkova and Tomboulis–Yaffe: twisted boundary conditions belong in the
  worst-case list of §5.2.
- **Lesson.** GDS is a criterion for gap *and* confinement. A pure-gap criterion would have to restrict the boundary conditions (to
  typical or thermalised ones, as in weak mixing), and for that no finite-size theorem is known in d ≥ 3 (Martinelli–Olivieri–Schonmann
  is d = 2, spin systems).

### 4.3 Strong coupling: GDS holds, in our proven window

- **Single-link family**, H variant:
  - for V = {x}, `k_{{x}}(z) ≤ TV(q^τ, q^{τ'})·1` (osc ≤ 1);
  - `Influence.tv_single_link_le_tanh` gives `TV ≤ tanh(nβ)` (β multiplying Re tr; `LGT-NOTE.md` §2);
  - each link z lies in the shell of 6(d−1) single links;
  - so GDS holds with γ = 6(d−1)·tanh(nβ) < 1. That is `Influence.dobrushin_single_link`.

  For d = 4: standard β < 0.056 (SU(2), U(1)); with the exact single-link influence (numerical, `LGT-NOTE.md` §4) about 0.131 (SU(2))
  and 0.087 (U(1)). For U(1) this is the confined phase, as it must be.
- **W variant:** a Lipschitz version of the same lemma (the density of q changes by at most β n ρ(τ_z, τ'_z)·const) gives
  `k^W ≤ C nβ diam(G)` and a window of the same kind. That is a small new lemma.
- **`Clustering`:** our two-copies theorem is for the periodic torus. Its exchange argument should go through unchanged with a fixed
  boundary condition (boundary plaquettes are bounded weights), which would give Chatterjee's Definition 2.3 directly in the window
  (16d)²(1 − e^{−4n|β|}) < 1. This is expected, not checked. The GDS route gives a larger window.
- **Larger blocks at strong coupling:** C_V in cubes of side 2–3 with computer-assisted bounds (Dobrushin–Kolafa–Shlosman style). An
  unrefereed 2026 preprint claims β ≈ 0.42 for SU(2) this way (`../dobrushin/README.md`).

### 4.4 Test table

| theory | gap? | confines? | GDS (some ℓ) | status of the GDS entry |
|---|---|---|---|---|
| any G, β small | yes | yes (centre) | holds | theorem (single links; §4.3) |
| 4D U(1), β > β_c | no (photon) | no | fails | theorem, given Theorem A + Froehlich–Spencer |
| 4D Z₂, β large | yes | no | fails | theorem, given Theorem A + Chatterjee 2021 + 2020 |
| 3D U(1), any β | yes | yes | expected to hold at ℓ ≫ ξ | conjecture (no photon test in 3D) |
| 4D SU(N), β ≈ 2.3 (one a) | believed | believed | ? | open; measurable (§5) |
| 4D SU(N), ℓ = L₀/a, all a | the Clay problem | believed | ? | open = Corollary B's hypothesis |

---

## 5. Measurement and certification

### 5.1 What to measure

- **Upper estimates of k_V(y)** (the direction GDS needs). Run two heat-bath chains on the box, with boundary conditions τ and τ' that
  differ only at y, using common random numbers (synchronous coupling). Before measuring, **align**: minimise
  `Σ_{e∈V} (1 − Re tr(k_{s(e)} U_e k_{t(e)}^† U′_e^†)/n)` over k ∈ K_V. This is a relative Landau gauge fixing, with standard
  over-relaxation code, using U′ as the reference instead of 1. Any k gives an upper bound on ρ̄, so imperfect gauge fixing only
  makes the estimate conservative.
  - W variant: record `Σ_e ρ(U_e, U′_e)/ρ(τ_y, τ′_y)` after equilibration of the *coupled* pair.
  - H variant: record `#{e : U_e ≠ U′_e}`. This needs a coupling that can make links coincide (maximal-coupling heat bath); not
    worth doing at weak coupling, see §3.6.

  A coupling estimate is an upper bound on the coupling distance, which is ≥ our dual k. So measured values *overestimate* k, which
  is the safe direction for "GDS holds".
- **Lower bounds on k_V(y)** (to refute GDS). For a witness f with `L_x(f) ≤ 1` (or δ_x ≤ 1), `|q^τ f − q^{τ'} f|` is a lower bound.
  - Use relatively invariant witnesses: open Wilson lines between boundary sites, normalised by their length; Wilson loops; smeared
    flux in the plane of the disturbance.
  - Multi-site versions (§4.1 witness 2) test the Martinelli–Olivieri form.
- **Linear response (cheap screening).** For small θ, the W-response is approximately `β·Cov(aligned interior links, ∂S/∂τ_y)`,
  from one ensemble per τ. It is a screening tool only: Gribov copies make the fixed-gauge mean response a heuristic.

### 5.2 "For all boundary conditions" in practice

The exact supremum is over G^{|∂V|} (thousands of links). In practice:
1. **Symmetry reduction of y:** by the hypercubic symmetry of the cube, y ranges over one face, modulo the face's symmetry group
   (≈ ℓ³/48 classes in 4D); sample corners, edges and the face centre.
2. **Classes of τ:**
   - cold (τ = 1);
   - hot (Haar random);
   - thermalised (cut from a periodic ensemble at the same β);
   - smooth abelian backgrounds (constant field strength in one or two planes, several magnitudes, including the flux-π witness);
   - 't Hooft twisted (centre flux through the box; the Ising-gauge worst case);
   - instanton-like boundary data (SU(2));
   - "balanced" boundary conditions near a pivot (two competing interior minima);
   - admissible versions of all of the above (route 6).
3. **Adversarial search:** maximise k̂_V(y) over τ by stochastic gradient or cross-entropy updates of τ, starting from each class.
4. **What is reported:** max over tested τ, the class that attains it, and its stability under the search. Never "for all τ".

### 5.3 Runs (to pre-register before computing; GPU code in `../lattice/`)

| group | β | ℓ | prediction |
|---|---|---|---|
| U(1) Wilson | 0.9 (confined) | 4, 6, 8, 12 | R(ℓ) falls ~ 1/ℓ; below 1 by ℓ ≈ 6–8 |
| U(1) Wilson | 1.1, 1.5 (Coulomb) | 4, 6, 8, 12 | R(ℓ) flat or rising, ≳ 1; flux witness ≈ 1 at every ℓ |
| SU(2) Wilson | 2.0, 2.3, 2.5 | 4, 6, 8, 12, 16 | R(ℓ) ~ C ξ/ℓ (ξ ≈ 1 lattice unit at 2.3 from a m₀₊₊ ≈ 1.4; to recheck); flux and twist witnesses → 0 |
| SU(2) Wilson | 2.7 | 8–24 | the same at larger ℓ; the ratio ℓ_needed/ξ should be roughly constant in β (scaling, Corollary B) |
| Z₂ | large β | 4–12 | the twist or pivot witness gives R(ℓ) growing with ℓ (Ising-gauge test) |

**Decision value.** If U(1) Coulomb shows R(ℓ) < 1 at some ℓ, either the measurement is broken (alignment, equilibration, or a too-weak τ
search) or Theorem A as stated is false. Both must be resolved before any SU(2) number is believed. This is the photon test as a
numerical unit test.

### 5.4 What measurement cannot establish

- The supremum over all τ (only the tested classes).
- The infinite family over a → 0 (only a few β).
- Monte Carlo error and equilibration of the *coupled* pair (slower than either chain alone).
- The difference between our coupling (synchronous heat bath) and the optimal one. This errs on the safe side for GDS holding, and
  on the unsafe side for refutation, which needs the witnesses instead.

At best it gives evidence that GDS holds at β ≈ 2.3 with ℓ of order 8, with an identified worst-case class. That is a sharp,
falsifiable claim, not a proof.

### 5.5 What can be certified rigorously

- **Strong coupling, small blocks:** yes. Single links in closed form (`Influence`); cubes of side 2–3 by interval arithmetic over a
  discretisation of G with Lipschitz error control, in the Dobrushin–Kolafa–Shlosman style. The supremum over τ ∈ G^{|∂V|} is tractable
  only because at strong coupling the bound is uniform in τ by a simple estimate.
- **β ≈ 2.3:** not with known methods. A certificate needs a bound on `sup_τ sup_f |q^τ f − q^{τ'} f|`, a supremum over thousands of
  continuous boundary variables with no monotonicity: gauge theories have no FKG. Convexity (Bakry–Émery in an aligned chart) cannot
  help on its own: in the admissible small-field region the measure is approximately Gaussian and *massless* (the photon again),
  so any certificate must carry the non-abelian effect.
- **The bootstrap** (Kazakov–Zheng; our running bootstrap) gives rigorous bounds on translation-invariant infinite-volume expectations,
  not on conditional laws under arbitrary boundary conditions. Two uses remain:
  1. **Refutation:** a fixed-boundary bootstrap (loop equations with the boundary links as *known* matrices) gives rigorous
     two-sided bounds on `q^τ(f)` for one given τ. With witnesses it can rigorously certify that GDS **fails** for a given (τ, τ′, f).
     Useful for the photon and Ising-gauge tests.
  2. **A boundary-agnostic bootstrap** (research idea, not a plan): treat loops that touch the boundary as free variables, and bound
     interior expectations uniformly over τ by semidefinite programming. That bounds Martinelli–Olivieri-type influences for finitely
     many witnesses, not the supremum over all Lipschitz f that GDS needs. It is possibly a route to *necessary* conditions.
- **One β, one box, certified:** at best a rigorous lattice gap for that single theory (§3.5), not a continuum statement.

---

## 6. Lean formalisation plan

Framework: `AreaLaw.Lattice` (links, plaquettes, `GaugeConnection`, `productHaar`, `LinkDep`), `Influence` (total variation,
single-link tanh), `Positivity` (site and link RP, `General`, `Admissible`), `AreaLaw.Reach` (`HasReach`). New folder proposal:
`formal/OneScale/`. In the list below, "standard" means a known theorem formalised by us; "new" means a statement proposed in this blueprint.
Line estimates are rough, by analogy with our files (Clustering 743, TwistAreaLaw 619, Reflection 413).

| # | file / content | builds on | kind | estimate | difficulty and risks |
|---|---|---|---|---|---|
| L0 | `OneScale/Block.lean`: block families 𝒱 on (ℤ/Nℤ)^d, `shell V`, `c z`, translation and rotation invariance, `diam`; cubes and single links as instances | `AreaLaw.Lattice`, plaquette graph | new (bookkeeping) | 400–700 | medium: lattice geometry in `ZMod N`, as in `Positivity/Reflection` |
| L1 | `OneScale/Specification.lean`: explicit `condLaw φ V τ` (normalised density on G^V); positivity of the normaliser (Wilson: bounded φ > 0; admissible: an *allowed τ* hypothesis); **Markov/DLR identity** μ(f) = μ(P_V f) by Fubini on G^V × G^{V^c} | `productHaar`, `Positivity/Product` (splits), `Influence.Gibbs` | standard | 600–1,100 | medium-hard: the Fubini split of the product Haar measure along a link subset; integrability; the weight factorisation over plaquettes touching V |
| L2 | `OneScale/Oscillation.lean`: `osc x f` (δ_x), Lipschitz `lip x f` (L_x); telescoping `|f σ − f σ'| ≤ Σ_x δ_x f` on finite E; `osc` of functions not depending on x vanish | `LinkDep` | standard | 200–350 | easy; the admissible version needs single-link connectivity, kept as a hypothesis |
| L3 | `OneScale/BlockAverage.lean`: `P_V`; the three oscillation inequalities of §3.2; `P_V (f*h) = f * P_V h` for f not depending on V | L1, L2 | standard | 300–500 | medium: measurability of h ↦ P_V h, sup bounds |
| L4 | `OneScale/Influence.lean`: `boundaryInfluence V z` (dual definition, H and W); `GDS 𝒱 γ`; the single-link instance from `Influence.tv_single_link_le_tanh` (`gds_single_link`, non-vacuity) | L1, L3, `Influence` | new definition; standard instance | 250–450 | easy-medium; needs the lemma `|μf − νf| ≤ osc(f)·TV(μ,ν)` (add to `Influence`) |
| L5 | `OneScale/Contraction.lean`: averaged P over 𝒱_A; weighted sup-norm contraction on S^c, geometric bound on S; finite linear algebra with e^{−λ dist} | L3, L4 | standard (Dobrushin–Foellmer), new normalisation | 400–700 | medium: weights and distances; choose the ℓ^∞ link distance to keep proofs simple |
| L6 | `OneScale/Decay.lean`: **Theorem A** (H and W), `Cov(f,g) = μ(f(P^t g − μ g))`, limit t → ∞; corollary `gds_has_reach : GDS → HasReach` | L5, `AreaLaw.Reach` | standard (with gauge setting) | 300–500 | medium; the limit in t is a monotone or ε argument, no measure-theoretic limit needed |
| L7 | `OneScale/Alignment.lean`: relative gauge group K_V; `condLaw` is K_V-invariant; **Lemma 2.3** (dual form: averaging over K_V does not increase δ_x or L_x; the boundary influence is unchanged when restricted to K_V-invariant f); gauge covariance `condLaw (h·τ) = h̃_* condLaw τ` | `productHaar` invariance (as in `TwistVanish`, `CentreSymmetry`), L1 | **new** (elementary) | 400–700 | medium: product Haar invariance under link-wise left/right multiplication; Haar on K_V and Fubini |
| L8 | `OneScale/Boundary.lean`: Theorem A for a cube with a fixed boundary condition (Chatterjee's Definition 2.3 as a `Prop`) | L6 with A ⊇ boundary | standard | 200–300 | easy once L6 exists |
| L9 | `OneScale/RPGap.lean`: **Theorem C**, Hankel doubling `h(k) ≤ h(0)^{1−2^{−r}} h(2^r k)^{2^{−r}}`; constant-free decay from Theorem A | `rp_plaquette_weight_gram`, translation invariance of μ on the torus, Θ ∘ τ_t = τ_{−t} ∘ Θ | standard (Osterwalder–Seiler) | 500–900 | medium-hard: time translations against the reflection slabs; connected version via Θ-invariance of μ |
| L10 | `OneScale/Physical.lean`: **Corollary B** interface: `structure OneScaleBound` (sequence a_k, β_k, L₀, γ, hypothesis GDS_W at ⌈L₀/a_k⌉ for all k) ⇒ uniform lattice gap ≥ log(1/γ)/(L₀ + 3a_k); non-vacuity *at one a* (strong coupling) | L6, L9 | **new** (interface) | 100–200 | easy; per the `SURVEY-LEAN` warning, the hypothesis is reported as open and is not inhabited along a → 0 |
| L11 | optional `OneScale/Centre.lean`: Chatterjee's Theorem 2.4 (Definition 2.3 ⇒ unbroken centre ⇒ area law) | L8, `CentreSymmetry`, `TwistVanish` | standard (port of ~15 pp.) | 1,000–2,000 | hard: infinite slabs in his proof need a finite-volume rewrite; low priority (we already have the twist area law at strong coupling) |
| L12 | optional `OneScale/Admissible.lean`: GDS and Theorem A for the admissible weight under a single-link connectivity hypothesis; site-RP Theorem C via `admissible_rp` | L1–L9, `Positivity/Admissible` | new | 300–600 | medium; the connectivity hypothesis must be checked for non-vacuity (large ε) |

**Proof order:** L0 → L1 → L2 → L3 → L4 → L5 → L6 (Theorem A with single-link non-vacuity: the first milestone, about 2,500–4,000
lines) → L7 (gauge content) → L8 → L9 → L10. Total without the options: about 3,500–6,000 lines. The hardest parts are L1 (the Fubini
split) and L9 (bookkeeping of translations and reflections).

**What Lean will and will not say.**
- **Will:** for every compact group and every plaquette weight, GDS at one scale implies volume-uniform and boundary-uniform decay and a
  transfer-matrix gap. GDS holds at strong coupling. Together with the RP doubling, a uniform-in-a GDS would give a uniform physical gap.
- **Will not:** prove GDS anywhere outside strong coupling. Corollary B's hypothesis stays a named, open hypothesis. The photon and
  Ising-gauge tests are argued in this document, not formalised (Froehlich–Spencer and the Z₂ perimeter law are far outside our framework).
  A small formal sanity check is possible: a 2-site toy where a "naive TV" coefficient exceeds the aligned one, illustrating Lemma 2.3.

---

## 7. Open points and risks

1. **Original-source checks before any claim:**
   - Dobrushin–Shlosman 1985 (spin-space generality; the exact form of their decay conclusion);
   - Froehlich–Spencer (Wilson action covered?);
   - Chatterjee 2020 (journal data);
   - Cao 2020 (journal data);
   - Durhuus–Froehlich (the exact uniform condition).
2. **Theorem A's dual proof** has been checked here only as a sketch. Before Lean, write it out in full in a short note (2–3 pages), in
   particular the S-set bookkeeping and the role of c(x) ≥ 1.
3. **The W variant's last step** uses diam_ρ(G) per link: fine for compact G, but it enters the constant, not the rate.
4. **The admissible variant's** single-link connectivity and topological sectors: an open technical point, and possibly physical.
5. **Is GDS_W (worst case over τ) true for SU(2) at β ≈ 2.3 with ℓ ≈ 8?** This is the first *numerical* question of the route, and it
   is falsifiable. The U(1) control must come first (§5.3).
6. **Scope discipline:** GDS is a gap-and-confinement criterion. Reporting a measured "GDS holds" as evidence for the *gap alone* is fine;
   as evidence for the Clay problem it is not, because the a → 0 family is the problem.

---

## Sources (web, read on 2026-11-21)

- Chatterjee, arXiv:2006.16229 (v5, §1–§3 read): https://arxiv.org/abs/2006.16229
- Adhikari, Cao, arXiv:2202.10375 / Ann. Probab. 53 (2025): https://arxiv.org/abs/2202.10375 , https://projecteuclid.org/journals/annals-of-probability/volume-53/issue-1/Correlation-decay-for-finite-lattice-gauge-theories-at-weak-coupling/10.1214/24-AOP1702.short
- Forsstroem, arXiv:2104.03752 / Commun. Math. Phys. 393 (2022): https://ar5iv.labs.arxiv.org/html/2104.03752
- Shlosman, arXiv:2505.24750: https://arxiv.org/abs/2505.24750 , https://arxiv.org/html/2505.24750v2
- Shen, Zhu, Zhu, arXiv:2204.12737 / Commun. Math. Phys. 400 (2023) 805–851: https://arxiv.org/abs/2204.12737
- Cao, Nissim, Sheffield, arXiv:2509.04688: https://arxiv.org/abs/2509.04688
- Otto, Reznikoff, J. Funct. Anal. 243 (2007); Menz, Electron. J. Probab. 19 (2014): https://arxiv.org/abs/1309.0862
- Zegarlinski, J. Funct. Anal. 105 (1992) 77–111 (citation confirmed via search)
- Chatterjee, arXiv:1811.09770: https://arxiv.org/abs/1811.09770
- Dobrushin–Shlosman 1985 chapter (Springer listing): https://rd.springer.com/chapter/10.1007/978-1-4899-6653-7_21
- Weitz 2005 (abstract via search): https://zendy.io/title/10.1002/rsa.20073
