# Attempt (b): the positivity route (2026-11-21)

Route (b) of the attempt round (`../RULES.md`, `../../PREP.md` "Decision rule" and "Lead route"): use the "two witnesses" machinery
(reflection positivity, multiple reflections / chessboard estimates, the transfer matrix) to compare scales, i.e. to relate the
boundary influence or the decay of reflected correlations at lattice spacing a/2 to that at spacing a, at fixed physical size, towards
the open hypothesis `UniformGDS` (`../../../formal/OneScale/CorollaryB.lean`). Lean: `../../../formal/Attempts/Positivity/*.lean`.

## 0. Results at a glance

**Outcome: documented failure of the route as a proof of the layer inequality, with the reason made precise, plus three proved
lemmas and one conjecture.** The reason in one sentence: reflection positivity is a property of *one* measure; it transports bounds
inside one measure, and only *inward* (from large distances to small ones) or *across observables*, while the layer step a → a/2
compares *two* measures and, in lattice units, asks for *outward* transport. The non-abelian input cannot enter through RP; it has to
enter through the cross-scale map, and the cleanest place to put it is the adjoint action of the link variables (§5).

| # | statement | status |
|---|---|---|
| P1 | RP cannot carry decay outward: a sequence with the full RP Hankel structure can decay at rate λ on [0, M] and not decay at all beyond (`rp_no_outward`) | **proved, Lean** |
| P2 | one distance suffices **in ratio form**: a ratio bound H(M + 2j) ≤ εH(2j) at one distance M, uniform over time shifts, gives \|H(m)\| ≤ H(0)ε^{m/M} for all m, no prefactor (`one_distance_ratio`); the shift-uniformity cannot be dropped (`twoLevel_not_ratio`) | **proved, Lean** |
| P3 | a functional that reads links only through their adjoint action is blind to centre multiplication and **constant** for abelian groups (`AdjointOnly.*`) | **proved, Lean** (elementary) |
| R1 | UniformGDS ⇒ UniformRatio ⇔ uniform physical gap ≥ log(1/ε)/L₀ (§3.2) | ⇒: proved modulo the standard OS reconstruction (as PROOF-NOTE C2); ⇔: P2 one way, spectral theorem the other |
| N1 | (i) transfer matrices: no RP inequality between the gaps at a and a/2; the only robust statement (blocked observables decay at least as fast as the fine gap) points the wrong way (§4.1) | proved (elementary) / structural |
| N2 | (ii) chessboard: three independent obstructions (disseminated = global free energy; RP sees symmetric states, GDS needs worst-case boundaries; couplings are not RP), and the classical cost of a "line passes" event is identical for SU(2) and U(1) (§4.2) | the Cartan identity proved (elementary); the rest structural / heuristic as marked |
| N3 | (iii) RP free-energy monotonicities (Bachas concavity, bond moving) all point inward or hold verbatim for U(1) (§4.3) | literature, recalled |
| C1 | conjecture: adjoint disorder at one gradient-flowed physical scale L₀ **and** a non-critical centre sector imply UniformRatio (§5.3) | **conjecture**; passes the photon test by construction (P3) |

The photon and Z₂ checks are in §6, the remark for the lead route in §7, the next step in §8.

## 1. What reflection positivity provides (our formal tools)

- Site RP for every plaquette weight φ ≥ 0 (`Positivity.rp_plaquette_weight_gram`, admissible weights included), link RP for Wilson
  crossing plaquettes with β ≥ 0 (`rp_plaquette_weight_link`): the reflected form ⟨F, G⟩ = μ(F · ΘG) is positive semidefinite on the
  positive half.
- Time translation and the Hankel identity (`OneScale.TimeShift.hankel_corr`): ⟨F̊_j, F̊_k⟩ = Z · H(j + k), H(m) = Cov(F_m, ΘF).
- Hence H(j + k)² ≤ H(2j)H(2k) and H(2j) ≥ 0 (`OneScale.TorusRP.hankel_cs`), doubling and Theorem C (`OneScale.doubling`,
  `doubling_decay`), the prefactor-free limit (`OneScale.prefactor_free`).
- In infinite volume (PROOF-NOTE §6.6, prose): the OS Hilbert space, the transfer operator T (a self-adjoint contraction, T ≥ 0 under
  link RP), H(m) = ⟨ψ, T^m ψ⟩ with a positive spectral measure.

In the abstract, real-analytic form used below: `RPHankel H` := (∀ j k, H(j+k)² ≤ H(2j)H(2k)) ∧ (∀ j, 0 ≤ H(2j)), the infinite-volume
version of the hypotheses of `OneScale.doubling`.

## 2. RP transports decay inward only (P1)

**Theorem P1** (`Attempts.Positivity.rp_no_outward`). For every λ > 0 and M ∈ ℕ there is H : ℕ → ℝ with `RPHankel H`, H(0) = 1,
|H(m)| ≤ H(0)e^{−λm} for all m ≤ M, and for every prefactor C and every rate λ' > 0 some m with H(m) > C e^{−λ'm}.

*Proof.* q = e^{−λ}, η = q^M(1 − q), H(m) = (1 − η)q^{2m} + η, the moment sequence of (1 − η)δ_{q²} + ηδ_1. The Hankel inequality is
Cauchy–Schwarz: RHS − LHS = (1 − η)η(q^{2j} − q^{2k})² ≥ 0. For 1 ≤ m ≤ M, η ≤ q^m(1 − q^m), so H(m) ≤ q^{2m} + q^m(1 − q^m) = q^m.
H ≥ η > 0 everywhere, so no exponential decay. ∎

**Reading.** Every RP inequality on a single correlation is a consequence of the positivity of a spectral measure, and positive
mixtures of exponentials are log-convex: the effective decay rate m_eff(t) = −log(H(t+2)/H(t))/2 (even steps) is non-increasing in t.
Consequences:
- finite-distance data bound the gap from **above** (gap ≤ m_eff(t) for every t), never from below;
- a decay bound at a large distance propagates to all smaller distances (Theorem C), never to larger ones (P1);
- the same shape appears for Wilson loops: RP gives concavity of the static potential (Bachas 1986), so V(R)/R is non-increasing: a
  string-tension lower bound at large R propagates inward, not outward.

**Why this is fatal for a direct layer step.** At fixed physical size L₀, halving the spacing doubles the number of lattice steps:
ℓ = L₀/a becomes 2ℓ. Any statement of the form "decay over ℓ steps at spacing a ⇒ decay over 2ℓ steps at spacing a/2" needs, inside the
fine theory, decay at lattice distances the coarse data do not reach, i.e. outward transport. P1 says the RP structure alone does not
supply it, whatever the coupling between the two theories. The atom at 1 in the model is exactly the photon's role: a mode that never
decays and is invisible at short range if its weight is small.

## 3. One distance suffices, in ratio form (P2), and the weakest RP-natural hypothesis

### 3.1 The lemma

**Theorem P2** (`Attempts.Positivity.one_distance_ratio`). Let `RPHankel H`, p ≥ 1, 0 < ε ≤ 1, and assume the **shift-uniform ratio
bound** H(2(p + j)) ≤ ε H(2j) for every j ≥ 0. Then |H(m)| ≤ H(0) ε^{m/(2p)} for every m.

*Proof.* (`even_bound`) induction along shifts: H(2i) ≤ ε^{⌊i/p⌋} C with C = Σ_{r<p} H(2r). Doubling (`OneScale.doubling`) at
distance m with 2^r m: |H(m)| ≤ H(0)^{1−2^{−r}} H(2^r m)^{2^{−r}} ≤ H(0)^{1−2^{−r}} (C/ε)^{2^{−r}} ε^{m/(2p)}. Let r → ∞
(`OneScale.prefactor_free`). ∎

**The uniformity over shifts is essential** (`twoLevel_not_ratio`): the model of P1 satisfies the one-distance bound for the observable
itself up to M, but for every ε < 1 and p some shift j violates H(2(p+j)) ≤ εH(2j) (the ratio tends to 1 along shifts).

**Lattice instance.** For G = F_j (a time translate of F, again a positive-half observable), H_G(m) := Cov(G_m, ΘG) = H_F(m + 2j).
So the hypothesis of P2 with M = 2p is: Cov(G_M, ΘG) ≤ ε Cov(G, ΘG) for all time translates G of F. It holds if the ratio bound holds
for **all** positive-half local observables at the one distance M. P2 is the spectral-theorem statement ‖T^M|_{Ω⊥}‖ ≤ ε ⇒
‖T^m|_{Ω⊥}‖ ≤ ε^{m/M}, proved without spectral theory and without infinite volume.

### 3.2 UniformRatio

**Definition (UniformRatio(L₀, ε)).** Along the scaling sequence (a_k, β_k): for every k and every bounded local positive-half F,
Cov_k(F_{M_k}, ΘF) ≤ ε Cov_k(F, ΘF), with M_k = 2⌈L₀/(2a_k)⌉, in every limit state of the level-k torus measures.

**R1.** (a) UniformGDS(L₀, γ) ⇒ UniformRatio(L₀', ε) for suitable L₀', ε < 1: Theorem A + Corollary C1 + Theorem C2 give
spec(T|_{Ω⊥}) ⊂ [−γ^{1/D₁}, γ^{1/D₁}], and ⟨ψ, T^M ψ⟩ ≤ ‖T|_{Ω⊥}‖^M ‖ψ‖² (proved modulo OS reconstruction, as C2).
(b) UniformRatio(L₀, ε) ⇒ physical decay rate ≥ log(1/ε)/L₀ at every level for every local observable, with no prefactor (P2), i.e.
exactly the conclusion of `corollaryB_lattice`. (c) Conversely a uniform physical gap E ≥ E₀ gives UniformRatio with ε = e^{−E₀L₀}
(spectral theorem). So **UniformRatio is the uniform gap, stated at one physical distance.**

What this buys and what it does not:
- It is the weakest hypothesis that still gives Corollary B.1, and it is natural for RP (torus states, no boundary conditions). It
  does not give confinement (B.3 needs GDS_H^∂). That is right for a gap statement: G₂ Yang–Mills (trivial centre) is expected to
  have a gap and no asymptotic area law, so a gap proof must not need the centre.
- It is not a reduction: it is equivalent to the gap. Its value is diagnostic: once the hypothesis is put in this form, the layer step
  a → a/2 is literally a comparison of the physical gaps of two different measures (β_k and β_{k+1}), and RP, a property of each measure
  separately, contains no map between them.
- Numerics cannot certify it either: a finite operator basis (GEVP) gives the sup over a subset, a lower bound on ‖T^M|_{Ω⊥}‖, i.e.
  an upper bound on the gap. This is P1's direction again.

## 4. The three ideas of the brief

### 4.1 (i) Transfer matrices T_a and T_{a/2}

- **Time decimation is exact and empty.** T_{a/2}² is the transfer operator of the fine theory over physical time a; its gap per unit
  physical time equals that of T_{a/2}. No information.
- **Spatial blocking.** A block map b from fine spatial configurations to coarse ones (coarse link = product of the two fine links along
  it, transverse links integrated out) pulls back to an isometry J : L²(coarse Haar) → L²(fine Haar), since the product of independent
  Haar elements is Haar. The compression J*T_{a/2}²J is a positive contraction on the coarse space, but it is not T_a (not even the
  transfer operator of a local action); identifying it with some T_{β'} is the renormalisation-group problem. Interlacing for
  compressions gives λ_k(J*T²J) ≤ λ_k(T²): an upper bound on the compressed spectrum by the fine one, which cannot bound the fine gap from
  below.
- **The robust statement points the wrong way.** If b is reflection covariant (blocks do not straddle the reflection plane), the
  push-forward of an RP measure is RP (pull back positive-half observables), so the blocked theory has its own OS space, a subspace of
  the fine one. Correlations of blocked observables decay at least at the fine gap: gap(blocked) ≥ gap(fine), with equality iff the
  lowest state overlaps blocked observables. This bounds the coarse quantity by the fine one, the opposite of what the layer step needs.
- **Verdict (i):** no RP inequality between gap(T_a) and gap(T_{a/2}) in physical units exists in this generality, because RP gives no
  relation between the two measures. (Structural; the elementary facts above are proved.)

### 4.2 (ii) Chessboard estimates

Statement used (Froehlich–Israel–Lieb–Simon 1978 for spin systems; used in lattice gauge theory e.g. by Borgs; recalled, not re-read):
on a torus tiled by reflected copies of a block B₀, for block observables A_t, |⟨∏_t A_t⟩| ≤ ∏_t p(A_t) with the **disseminated**
quantity p(A) = ⟨∏_{all tiles s} ϑ_s(A)⟩^{1/#tiles}. With bad events A and a deterministic screening lemma ("an influence crossing the
box needs a chain of bad blocks"), a Peierls sum gives decay once p(bad) < 1/(connective constant). This is the engine the lead route
proposes. Three obstructions, each independent of the others:

1. **p(bad) is a global free energy, not a single-block probability.** p(A) = exp(−|B₀| Δf_A), where Δf_A is the free-energy density
   cost of imposing A periodically in every tile. Bounding it uniformly in a is a statement about the whole torus at all scales between
   a and L₀: the cross-scale problem returns inside p.
2. **RP sees symmetric states; GDS needs worst-case boundaries.** k_B(z) is a supremum over all boundary conditions η; RP and chessboard
   bounds control expectations in reflection-symmetric torus states. They can at best give a torus (typical-boundary) version of GDS,
   which is UniformRatio (§3), not GDS^∂.
3. **The screening object is a coupling, and couplings are not RP.** Boundary influence is controlled by couplings of two conditional
   measures (disagreement percolation, Dobrushin–Shlosman). Events of a coupling are not functions of one configuration; for two
   independent copies (μ⊗μ, which is RP for the diagonal reflection) the copies never agree on a block (continuous group), so "the
   coupling succeeded" is not available as an RP event. Configuration-level "good" events do not screen at weak coupling: the natural
   one, small field, is exactly where perturbation theory holds and the gluon propagates like a photon.

**The classical cost is abelian (proved, elementary).** For the Cartan subgroup {diag(e^{iθ}, e^{−iθ})} ⊂ SU(2), Re tr = 2cos θ and
plaquette angles add, so the SU(2) Wilson weight e^{β Re tr U_p} restricted to Cartan-valued configurations is the U(1) Wilson weight at
β' = 2β. Every disseminated "a line passes" configuration of U(1) is therefore an SU(2) configuration with the same action. An
energy (Peierls) estimate of p(bad) gives the same number for SU(2) and U(1) and must fail (photon). The difference is entropic, from
the off-Cartan fluctuations. *Heuristic addendum:* at one loop a constant chromomagnetic field is not even suppressed: its effective
energy has a minimum at nonzero field and an unstable mode (Savvidy 1977, Nielsen–Olesen 1978, recalled), which is the perturbative
shadow of the disorder that produces confinement. So the smallness of p(bad) for SU(2), if true, is non-perturbative.

**Verdict (ii):** chessboard estimates reduce "influence crosses a box" to the disseminated free energy of a bad event at the block
scale plus a screening lemma; neither is supplied by RP, and both are where the cross-scale physics sits.

### 4.3 (iii) Free-energy monotonicity in the scale

- **Bachas concavity** (RP in a spatial direction): V(R) concave, V(R)/R non-increasing. Inward again (§2).
- **Bond moving / Hoelder decimation bounds** (Kadanoff, Migdal; made into inequalities on partition functions and twist ratios by
  Tomboulis 2007, arXiv:0707.2179): inequalities between the free energy at spacing a and decimated quantities at 2a. They use only
  Hoelder/RP and positivity of the character coefficients of the plaquette weight, which U(1) and Z₂ share. Ito–Seiler (arXiv:0711.4930,
  0803.3019, recalled; README §5) show the argument would equally confine U(1). This is P1's lesson in another form: an inequality whose
  proof uses only group-blind positivity holds for U(1).
- **Griffiths/Ginibre monotonicity in β** (the one classical comparison between two couplings) is an abelian tool; no general
  non-abelian analogue is known to me.
- **Twist free energy.** RP chessboard inequalities bound Wilson and Polyakov loops by the electric-flux (twist) free energy
  (Tomboulis–Yaffe 1985, CMP 100, recalled). This is the RP + centre combination done right, and it is a single-scale statement within
  one measure; its input (the twist free energy at size L₀, uniformly in a) is the open, dynamical part, and its output is confinement,
  not the gap.

**Verdict (iii):** no RP monotonicity runs outward in the scale; the ones that compare scales hold verbatim for U(1).

## 5. Where the non-abelian input must enter

### 5.1 Not through RP

RP of the lattice measure follows from positivity of the character expansion of the plaquette weight against Haar measure on any
compact group. It is blind to commutativity. Every consequence of RP (§2–§4) therefore holds for U(1), and an RP-only scale comparison
would prove the photon massive. The non-abelian input has to come from the dynamics of the measure, and between scales it has to come
from the map that relates them.

### 5.2 The adjoint action: self-charge without the centre (P3)

The gluon carries the charge it transmits: its own fluctuations are parallel-transported by the **adjoint** action x ↦ U x U⁻¹ of the
link variables (around any background, the fluctuation operator is the adjoint covariant Laplacian; for U(1) it is the free Laplacian
whatever the background, because the photon is neutral). Lean (`Attempts/Positivity/Adjoint.lean`):
- `conj_trivial_iff_mem_center`: conjugation by g is trivial iff g is central; `conj_eq_conj_iff`: the adjoint image of a link is the
  link modulo the centre (SU(2) → SO(3) = SU(2)/Z₂).
- `AdjointOnly.centre_invariant`: a functional reading links only through their adjoint action is blind to centre twists.
- `AdjointOnly.const_of_comm`: for an abelian group such a functional is **constant**.

So any bound whose contraction factor is built from adjoint transport is identically trivial for U(1) and Z₂: the photon and Z₂ tests
pass by construction. And it is blind exactly to the centre sector, which has to be handled separately. This splits the problem along
the known SO(3) × Z₂ decomposition (Mack–Petkova; Tomboulis 1981, recalled):

| theory | adjoint action | centre | expected | consistent with "gap ⇐ adjoint disorder + non-critical centre" |
|---|---|---|---|---|
| U(1)₄ weak coupling | trivial | U(1), continuous | massless photon | yes (hypothesis fails: adjoint trivial) |
| Z₂ weak coupling | trivial | Z₂ | gap (by discreteness), no confinement | yes (statement silent; gap from another mechanism; no continuum limit at weak coupling) |
| SU(2), T = 0 | SO(3) | Z₂, disordered | gap, confinement | yes |
| SU(2) at the deconfinement point T_c | SO(3); spatial string tension nonzero | Z₂, critical (3D Ising, Svetitsky–Yaffe) | no gap in the spatial transfer matrix | yes, and it shows the centre clause is needed |
| G₂ | non-trivial | trivial | gap, no asymptotic area law | yes (centre clause empty) |

In the owner's terms: the adjoint part is the self-charge ("existence"); the centre part is the frame of the root (the MG3 twist, the
root swap). The gap needs existence plus a root sector that is not critical; confinement needs a root sector that is disordered.

### 5.3 Conjecture C1 (single-scale, a-uniform by construction)

Let V^{(t)} be the gradient-flowed links at flow time t = c L₀² (c fixed), W^{(t)}(L₀) the flowed L₀ × L₀ Wilson loop, and
θ_Ad(L₀) = ⟨χ_Ad(W^{(t)}(L₀))⟩ / dim Ad. **Conjecture:** there are θ_* > 0 and a function ε(θ, ·) < 1 such that, if θ_Ad(L₀) ≤ θ_* and
the centre-projected blocked theory at scale L₀ is non-critical (uniformly in a), then UniformRatio(C·L₀, ε) holds.

- **Why a-uniformity is inherited, not proved by a layer step:** flowed observables at fixed physical flow time are UV finite
  (Luescher 2010; renormalisability to all orders, Luescher–Weisz 2011, recalled), so θ_Ad(L₀) has a continuum limit and its uniformity
  in a is a property of the continuum limit, not of an a → a/2 inequality.
- **Photon/Z₂ by construction:** θ_Ad ≡ 1 for abelian groups (P3), so the hypothesis fails for U(1) and Z₂.
- **Room:** with Casimir scaling (σ_Ad/σ_F = 8/3 for SU(2)) an L₀ × L₀ adjoint loop at √σ L₀ = 2 is of order e^{−32/3} ≈ 2·10⁻⁵ before
  perimeter and smearing factors, against exactly 1 for U(1): a separation of four to five orders of magnitude, against the
  10⁻⁵–10⁻¹³ per layer drift of the tree picture.
- **Where RP enters:** to pass from a torus-averaged block quantity to decay at one distance uniformly over observables (P2): the
  hypothesis is an expectation in the symmetric state, which is the regime RP handles.
- **Status:** conjecture. The implication is not proved; the screening problem of §4.2(3) is its core.

## 6. Photon and Z₂ checks

| item | U(1)₄ weak coupling | Z₂ weak coupling |
|---|---|---|
| P1 (no outward transport) | consistent: its counterexample is the photon's spectral weight | consistent |
| P2 (ratio ⇒ decay) | hypothesis fails: sup of the ratio is 1 when the spectrum reaches 0 (massless photon; FS82 status as in PROOF-NOTE §10.2) | hypothesis holds at fixed β (gap); allowed, since P2 is a gap statement and implies no confinement |
| R1 / UniformRatio | fails for U(1) (no gap): passes the photon test | holds formally for any fixed-β sequence (gap in lattice units), and is meaningless there (no scaling limit); it does not imply confinement, so rule 2's Z₂ clause (which targets reach/confinement bounds, GDS^∂) is not violated. **Flag:** a gap-only claim cannot be required to fail for Z₂; it must instead not contradict Z₂'s gap |
| N1–N3 | the inequalities examined hold for U(1), which is the reason they cannot give the layer step | same |
| P3 / C1 | adjoint quantity ≡ 1: C1's hypothesis fails, no claim | adjoint quantity ≡ 1: no claim |
| Cartan identity (§4.2) | used as the photon test of energy estimates | not applicable |

No bound proved here applies to U(1) at weak coupling, and none implies confinement.

## 7. A remark for the lead route (heuristic)

The lead route seeks κ(2ℓ) ≤ f(κ(ℓ)) with f contracting. At weak coupling and for boxes much smaller than the correlation length,
SU(2) is, to leading order in g²(ℓ) and for near-trivial boundary data, three copies of the photon. So f evaluated on SU(2) data equals
f on U(1)³ data up to O(g²(ℓ)), and for U(1) κ does not contract. Hence either f must depend on more than κ (at least on the running
coupling or on an adjoint quantity such as θ_Ad), or its contraction per doubling is of order g²(ℓ), i.e. tiny in the perturbative
region and accumulating only over ~1/(b₀g²) doublings. The anti-screening coefficient b₀ = 11N/(48π²) (spin/self-charge paramagnetism
12/3 minus the charged-particle diamagnetism 1/3, in units of N) is where the self-charge sits in that accumulation. This does not
refute the route; it constrains the form of f.

## 8. Most promising next step

**Attack C1's implication in its first, deterministic piece: an adjoint random-path domination with a disorder gain.** For a fixed
gauge configuration, the adjoint covariant lattice Green's function is a sum over paths of κ^{|ω|} Ad(U_ω); by ‖Ad‖ = 1 it is
dominated entrywise by the free (photon) one (a lattice diamagnetic, Kato-type inequality), with equality for abelian groups (P3).
Prove the quantitative version: the gain factor for paths crossing a block of side L₀ is bounded by the block's adjoint disorder
(a deterministic function of the flowed links). This is a single-configuration, single-scale, Lean-friendly lemma in which the
self-charge enters quantitatively and the photon test is built in. Combined with P2 (one distance, ratio form) it isolates the
remaining probabilistic step (the torus measure puts enough weight on adjoint-disordered blocks, i.e. θ_Ad small) as a clean,
numerically checkable, a-uniform-by-continuum-limit hypothesis. A cheap check that can run alongside, if the owner's resources allow
later: θ_Ad(L₀) on already saved SU(2) configurations at two β with the flow at fixed physical radius (CPU, minutes); for U(1) no run is
needed (≡ 1).

## 9. Lean

Files (new, ours): `formal/Attempts/Positivity/Inward.lean` (P1, P2, `twoLevel_not_ratio`), `formal/Attempts/Positivity/Adjoint.lean`
(P3). Built in WSL `~/formal-att-b` with `sync-build.sh Attempts.Positivity.<Module>`. Build status: see the end of this section.

Not formalised: R1 (needs the OS reconstruction and limit states, prose in PROOF-NOTE §6.6), the chessboard estimate, the Cartan
identity (one line of algebra, not worth a file), C1.

**Build status (2026-11-21):** both modules build cleanly (Lean 4.34.0, Mathlib v4.34.0, no `sorry`, no warnings shown):
`Attempts.Positivity.Inward` (135 s), `Attempts.Positivity.Adjoint` (304 s, mostly the shared Mathlib load on a busy machine).

## 10. References (ideas only; nothing copied)

- Osterwalder–Seiler, Ann. Phys. 110 (1978) 440 (RP for lattice gauge theory; checked in PROOF-NOTE §11).
- Froehlich, Israel, Lieb, Simon, CMP 62 (1978) 1 (chessboard estimates; recalled).
- Bachas, Phys. Rev. D 33 (1986) 2723 (concavity of the static potential from RP; recalled, title not checked).
- Tomboulis–Yaffe, CMP 100 (1985) 313 (RP bounds by the twist free energy; title and pages checked in PROOF-NOTE §11, content
  recalled).
- Tomboulis, arXiv:0707.2179; Ito–Seiler, arXiv:0711.4930, 0803.3019 (decimation inequalities and why they fail the photon test;
  recalled, see README §5).
- Mack–Petkova, Ann. Phys. 123 (1979) 442; Tomboulis, SO(3) × Z₂ formulation (1981) (recalled).
- Savvidy, Phys. Lett. B 71 (1977) 133; Nielsen–Olesen, Nucl. Phys. B 144 (1978) 376 (constant chromomagnetic field; recalled).
- Svetitsky–Yaffe, Nucl. Phys. B 210 (1982) 423 (deconfinement universality; recalled).
- Luescher, arXiv:1006.4518 (gradient flow); Luescher–Weisz, arXiv:1101.0963 (renormalisability of the flow; recalled).
- Bali, Phys. Rev. D 62 (2000) 114503 (Casimir scaling; recalled).
- G₂ lattice gauge theory: Holland, Minkowski, Pepe, Wiese, Nucl. Phys. B 668 (2003) 207 (recalled).
