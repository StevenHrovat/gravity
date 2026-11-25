# Cycle 6, workstream 3 (c6c-floor): where could a floor on the flip probability come from? (2026-11-22)

Task: literature on vortex free energies and one-box-to-all-volumes criteria (exact citations); the cleanest candidate statement that
would give the floor or the gap from a one-box condition, with known/open parts and unit tests (photon, Z₂ both phases,
deconfinement, mixture, 2I); the owner's readings as mathematics. Two coordinator messages arrived during the work and are folded in:
c6b-flipdata's finding (a constant floor does not separate SU(2) from the photon or the finite subgroups; what separates is p → ½) and
the owner's cycle-6 reading "Why the floor holds" (super-additivity of the act), section 4.

Claim levels: **read** (checked in the source this session, full text or the named section), **abstract** (only the abstract or
listing read), **recalled** (from memory, not re-read), **exact** (closed formula or brute force here), **paper** (argued here),
**reading** (an interpretation), **SPECULATIVE**.

Files: this note; `PREREG.md` (written before the one computation); `superadd_check.py`, `superadd_check.log`, `superadd_check.json`
(numpy, 7 seconds). No Lean (c6a owns `formal/ProofPhase/Flip/`; statements proposed in section 5). Nothing else edited.

---

## 0. In plain words

1. **Tomboulis' failing step, as one inequality.** Tomboulis (2007) needs, on each decimated lattice, A(α) > A⁺(α) for all α in
   (0, 1): the α-derivative of the decimated free energy of the untwisted ensemble beats that of the vortex-averaged ensemble (Ito–Seiler
   (3.5); Tomboulis (5.15)). He proves it only where the strong-coupling expansion converges. Its consequence would be the comparison
   **Z₋/Z (fine, β) ≥ Z₋⁽ⁿ⁾/Z⁽ⁿ⁾ (Migdal–Kadanoff upper-bound couplings after n steps)**, i.e. p(L) at least the flip probability of
   the MK-flowed model, which flows to strong coupling for every group, U(1) included (Ito 1985). So the inequality, if true as used,
   would make U(1) confine; it cannot hold group-blind. It is the "floor by comparison" in exactly the shape we would want, and it fails
   for exactly the reason c5e found: nothing in it sees what U(1) and 2I lack.
2. **What is proved about vortex free energies:** p ≤ ½ (Z₋ ≤ Z, strict on a finite lattice); Tomboulis–Yaffe: ⟨W(C)⟩ ≤
   2[½(1 − Z₋/Z)]^{A_C/(L_μL_ν)} in one volume, so an area law follows if 1 − Z₋/Z ≤ e^{−ρL_μL_ν}, i.e. **½ − p decays at the area
   rate**; Borgs–Seiler: 't Hooft string tension ≤ Wilson string tension; Muenster: the area-rate decay holds at strong coupling;
   Kanazawa: the spin-system version "a box insensitive to boundary conditions has a gap", with the flip heuristic (1 − 2p)^L written
   out; Mack–Petkova: SU(2) confines whenever the comparison Z₂ model does; Chatterjee (2021): for a **connected** gauge group with
   non-trivial centre, decay of correlations under arbitrary boundary conditions implies area law. Nothing proves any decay of the
   twist free energy outside strong coupling.
3. **One-box-to-all-volumes tools exist in two kinds, neither yet for SU(2) gauge observables:** (i) **positivity** (Simon–Lieb, Lieb,
   Aizenman–Barsky–Fernandez, Duminil-Copin–Tassion; for gauge models only Z₂/Potts in codimension two, Duncan–Schweinhart 2025, and
   3D plaquette percolation, Aizenman–Chayes–Chayes–Froehlich–Russo 1983); (ii) **worst case over boundary conditions**
   (Dobrushin–Shlosman's constructive criterion, Martinelli–Olivieri). I found no Simon–Lieb inequality for Wilson loops, vortex
   variables or glueball correlators of a non-abelian theory; Tomboulis himself notes the abelian comparison inequalities come from
   Griffiths' inequalities and that "all such known methods fail" for non-abelian groups.
4. **The floor, restated (agreeing with c6b):** a constant floor p(L) ≥ p_min > 0 in 't Hooft's geometry is the "not Higgs"
   statement (r3's Conjecture B); the photon and 2I satisfy it. What the tools need is **p → ½ at a rate** (Tomboulis–Yaffe needs the
   area rate) or, in the other geometry, **a per-cell floor at one fixed scale, uniform over the outside, plus "only the binary datum
   crosses"**. The cleanest candidate I can state with known parts is a **comparison through the centre layer** (section 2.3):
   decompose the blocked SU(2) field into Z₂ block variables and an SO(3) remainder; by Ginibre's inequality and Griffiths' second
   inequality, |⟨W⟩_{SU(2)}| ≤ ⟨W⟩_{Z₂ with couplings J̄}, where J̄ is the **worst-case (over the SO(3) background) effective centre
   coupling** at that scale. If J̄(ℓ) is in the proved area-law region of 4D Z₂ gauge theory at one block scale ℓ, SU(2) has an area
   law in all volumes. Known: the two inequalities, the decomposition (it always exists). Open: J̄(ℓ) small (this is where continuity
   enters: a thick vortex of SU(2) costs less as it widens, a 2I vortex does not), and the 4D Z₂ area-law region beyond strong
   coupling. It gives confinement (the flux act z_e), not the vacuum gap; the vacuum gap still needs the stateless adjoint layer.
5. **What 2I lacks:** not the centre, not "−1 is a commutator", but **connectedness / continuity** (used explicitly by Chatterjee,
   Lemma 4.1: bounded-speed paths in G) and, at weak coupling, a **stateless quotient layer** (A₅ orders). Every centre-only argument
   must route through one of these.
6. **Owner's readings:** "inward assertion" is the opposite of ½: at small L asymptotic freedom puts p near **0** (F_tw ~ (3/2)log(1/g²),
   heuristic), so it supplies a positive start, not the floor; "the possibility space" is, made uniform over the outside, exactly the
   worst-case per-cell floor (section 3.2), which is the right shape but needs the binary-channel property to mean anything; "the
   assertion reflects, ≤ 50 %" is p ≤ ½ (proved, upper side only), and "50 % minus entropy" is exact: ½ − p = ½ tanh(F_tw/2), with
   F_tw purely entropic at weak coupling for SU(2) (r3). Relabelling, but a correct one.
7. **Super-additivity (owner's cycle-6 reading), checked:** z(L) = L·E₀(L) super-additive forces E₀(L) ≤ m for every L (Fekete:
   the limit is the supremum). That is false for SU(2) in small boxes (Luescher: z₀ ~ g(L)^{2/3}, so E₀ → ∞ as L → 0) and false in
   every exactly gapped model I checked: 2D Ising strips (brute force, periodic and free, both sectors: the box gap approaches m from
   above, 25 of 25 pairs violate) and the Dirichlet massive field (all pairs). Persistence fails the photon; exact super-additivity
   fails honest gapped theories. The repaired form that keeps the idea: **super-additivity up to a bounded defect**,
   z(2L) ≥ 2z(L) − c, which gives m ≥ (z(L₀) − c)/L₀ from one box (one-box criterion z(L₀) > c). It passes the photon (c → 2π = sup z₀,
   criterion fails), the ordered Ising flip sector (fails), and holds for the gapped Ising cases with c ≈ 0.5 from L₀ = 2. It is c5e's
   D-T with summable loss in another form; its open content is again the cross-volume step. Reflection positivity gives
   sub-additivity (Bachas concavity of the static potential: wrong side) and chessboard gives the right side in the wrong volume. The
   flux act z_e ≈ σL² − π/3 (c6b fit: (L√σ)² − 0.88) is super-additive with a large margin: the owner's statement fits the
   **existence (flux) act** better than the vacuum act.

---

## 1. Literature

### 1.1 Tomboulis (2007) and Ito–Seiler (2007): the failing step (read)

* E. T. Tomboulis, "Confinement for all values of the coupling in four-dimensional SU(2) gauge theory", arXiv:0707.2179 (v1, 15 July
  2007, 49 pp., no journal reference) — **read** (sections 2–5, 7, footnotes 10–11).
* K. R. Ito and E. Seiler, "On the recent paper on quark confinement by Tomboulis", arXiv:0711.4930 (30 Nov 2007) — **read** (full).

Setup (Ito–Seiler section 2, Tomboulis sections 2–4). Plaquette weight f({c_j}, U) = 1 + Σ_{j≠0} c_j d_j χ_j(U), c_j ≥ 0. Z₋ flips the
sign of the half-integer characters on a vortex sheet V (plaquettes (−1)^{2j}c_j). A Migdal–Kadanoff (potential-moving) decimation gives
upper-bound coefficients c^U_j(n); a lower bound with c^L_j = 0 is trivial. An interpolation parameter α ∈ (0, 1] (and t, h(α, t)) makes
the decimated partition function exact: Z = [F₀]^{h(α(t),t)|Λ⁽¹⁾|} Z⁽¹⁾({c̃_j(α(t))}) (Ito–Seiler (3.1a)), and similarly Z⁺ = ½(Z + Z₋)
with its own α⁺(t) ((3.1b)). Claim 2.1 / (3.2): **there is a t* with α(t*) = α⁺(t*)**, so that Z₋/Z equals the coarse ratio at a common
effective coupling ((3.3)), and by induction at every level.

The step. Tomboulis reduces (3.2) to
**A(α) > A⁺(α) for 0 < α < 1** (Ito–Seiler (3.5); Tomboulis (5.15), equivalently A ≥ A⁽⁻⁾, his (5.16)), where
A(α) = (1/(log F₀ |Λ⁽¹⁾|)) ∂_α log Z₁({c̃_j(α)}) and A⁺ the same with Z₁⁺ (Ito–Seiler (3.4a,b); Tomboulis (4.22)). It is a comparison
between derivatives of logarithms of large partition functions of the twisted and untwisted decimated ensembles. Tomboulis (p. 27):
under the assumption that the coefficients flow into the convergence region, one needs it "only at strong coupling", where it is a
cluster-expansion exercise. Ito–Seiler: the assumption is used as if (3.2) were proven at every level; if A⁺ > A somewhere, the
implicit-function continuation t(λ) diverges before λ = 1 ((3.9)–(3.11)); "It is not clear where and how his claim is proven for
large β". Section 4: such a t* "does not exist in the case of G = U(1)"; the MK recursion cannot tell abelian from non-abelian groups,
only the speed of c_j(n) → 0 differs.

What the step would have delivered, in flip language (Tomboulis V.2, (5.23), read): the upper-bound coefficients give a **lower bound
on the ratio**, Z₋/Z ≥ Z₋⁽ⁿ⁾/Z⁽ⁿ⁾ evaluated at {c^U_j(n)}. With F_tw = −log(Z₋/Z): **F_tw(fine lattice) ≤ F_tw(MK-flowed lattice after
n steps)**, and the MK flow reaches strong coupling for every compact group in d ≤ 4 (K. R. Ito, PRL 55 (1985) 558, recalled; quoted
as Theorem 2.1 by Ito–Seiler). So p(L) would be bounded below by the flip probability of a strong-coupling model: a floor, in fact
p → ½ at the area rate, for every group. **That is the one inequality, and it is false as a group-blind statement** (U(1) has a
Coulomb phase: A. Guth, PRD 21 (1980) 2291; J. Froehlich and T. Spencer, CMP 83 (1982) 411; recalled).

A detail worth recording: Tomboulis' footnote 10 says that for abelian systems comparison inequalities of the type (5.15) follow from
Griffiths' inequalities, and that "all such known methods fail in the non-Abelian case". Taken with Ito–Seiler's remark that t* does
not exist for U(1), the abelian version cannot hold on the whole α-range at weak coupling (otherwise the argument would confine U(1)).
I did not locate which link breaks for U(1); it is a cheap exact test case for anyone who revisits the argument (U(1) in d = 4 with
Villain action, where both sides are computable).

### 1.2 Vortex free energies: what is proved

| result | statement | status here |
|---|---|---|
| positivity, p ≤ ½ | Z₋ ≤ Z for c_j ≥ 0, strict on a finite lattice (Tomboulis 2007, IV.1, (4.5)); transfer-matrix form Z_tw/Z = (1 − ρ)/(1 + ρ), ρ ∈ [0, 1] (r3-monotone B1) | read |
| Tomboulis–Yaffe (CMP 100 (1985) 313) | ⟨W(C)⟩ ≤ 2[½(1 − Z₋/Z)]^{A_C/(L_μL_ν)}, C in the μν-plane, any one-plaquette action (site RP). Area law if 1 − Z₋/Z ≤ e^{−ρL_μL_ν} | read, as stated in Kanazawa (Theorem 1) |
| Kanazawa, arXiv:0808.3442 (v3, 2009) | SU(N) version (Theorem 2, each k ∈ Z_N); spin systems (Theorem 5): |Γ(n)| ≤ 2Γ(0)[…]^{n/L}(1 − ∫dg O(g))^{n/L}, "a system in a box sufficiently insensitive to boundary conditions has a non-zero mass gap"; heuristic (97): independent wall crossings with probability p give (1 − 2p)^L, m = −log(1 − 2p) | read (statements) |
| Borgs–Seiler (CMP 91 (1983) 329) | Lemma II.8: Polyakov-loop correlator vs electric flux free energy; 't Hooft string tension ≤ Wilson string tension (Mack–Petkova's conjecture) | via Ito–Seiler and Kanazawa; recalled |
| Mack–Petkova (Ann. Phys. 123 (1979) 442) | an inequality between Wilson loops of SU(2) and of a Z₂ model: SU(2) confines whenever the corresponding Z₂ model does | abstract (INSPIRE) |
| Mack–Petkova (Ann. Phys. 123 (1980) 117) | sufficient condition for confinement by vortex condensation | recalled (title via Ito–Seiler) |
| Muenster (Nucl. Phys. B180 (1981) 23) | strong coupling: 1 − Z₋/Z ~ e^{−ρL²}, ρ = Wilson string tension to all orders | via Kanazawa |
| Tomboulis (PRL 50 (1983) 885) | the MK-upper-bound lower bound on Z₋/Z, first stated | via Tomboulis fn 11; recalled |
| Kovacs–Tomboulis (PRL 85 (2000) 704) | numerical: SU(2) vortex free energy decays at β = 2.3–2.5 | abstract (via r3) |
| Chatterjee, "A probabilistic mechanism for quark confinement", CMP 385 (2021), arXiv:2006.16229 | G a **closed connected** subgroup of U(n), centre non-trivial. Th. 2.2: unbroken centre symmetry (slab, every boundary condition) ⇒ |⟨W_ℓ⟩| ≤ e^{−V(R)T}, V(R) → ∞. Th. 2.4: exponential decay of correlations **under arbitrary boundary conditions** (uniform constants over all cubes and boundary conditions) ⇒ unbroken centre symmetry ⇒ area law. The proof uses Lemma 4.1 (bounded-speed piecewise-smooth paths between any two elements of G), i.e. connectedness. He notes finite-group theories are believed gapped but not confining at weak coupling, which does not contradict 2.4 because their decay holds only for special boundary conditions; some have multiple Gibbs measures | read (sections 1–2, 4) |

Reading of the table: every proved implication runs **from a statement in one volume** (the twist ratio of that torus, or decay in
every cube) **to confinement or the gap in that volume or all volumes**. None supplies the input. The required input in the 't Hooft
geometry is **½ − p(L) ≤ e^{−ρL²}** (area rate), not a constant floor.

### 1.3 One-box-to-all-volumes criteria

**Positivity (Simon–Lieb family).** B. Simon, CMP 77 (1980) 111; E. H. Lieb, CMP 77 (1980) 127 (refinement); V. Rivasseau, CMP 77
(1980) 145 (plane rotators); M. Aizenman, D. Barsky, R. Fernandez, J. Stat. Phys. 47 (1987) 343; H. Duminil-Copin and V. Tassion,
CMP 343 (2016) 725; H. Duminil-Copin, A. Raoufi, V. Tassion, Ann. Math. 189 (2019) 75 (random-cluster q ≥ 1, Potts) — all recalled.
Form (Ising ferromagnet): for a finite S ∋ 0, φ_β(S) = Σ_{x∈S, y∉S} J_xy ⟨σ₀σ_x⟩_S; Lieb's inequality ⟨σ₀σ_z⟩ ≤ Σ_{x∈S,y∉S}
⟨σ₀σ_x⟩_S J_xy ⟨σ_yσ_z⟩ iterates to ⟨σ₀σ_z⟩ ≤ φ_β(S)^{⌊|z|/R⌋}, so **one box with φ < 1 gives exponential decay in all volumes**, rate
≥ −log φ(S)/R. Sharpness (DCT): β_c = sup{β : some finite S has φ_β(S) < 1}, so the one-box criterion is also necessary. The engine is
Griffiths/GKS positivity: the big-volume correlation is dominated by small-box data. In act language: the transmission act
−log⟨σ₀σ_x⟩ is super-additive up to the per-box term −log φ (section 4).

For gauge models: Griffiths/Ginibre inequalities hold for Z₂ (and U(1)) lattice gauge theory (J. Ginibre, CMP 16 (1970) 310,
recalled), so Wilson loops are monotone in the couplings. Sharp transitions: plaquette percolation in 3D (Aizenman, Chayes, Chayes,
Froehlich, Russo, CMP 92 (1983) 19, recalled); P. Duncan and B. Schweinhart, "A sharp deconfinement transition for Potts lattice gauge
theory in codimension two", arXiv:2308.07534, CMP (2025), **abstract**: (d−2)-dimensional Potts lattice gauge theory on Z^d,
unconditional for Ising — this covers ordinary Z₂ gauge theory in 3D and 2-form theories in 4D, **not ordinary (1-form) Z₂ gauge
theory in 4D**. For 4D Z₂ gauge theory the area law is proved at strong coupling (K. Osterwalder and E. Seiler, Ann. Phys. 110 (1978)
440, recalled) and the weak-coupling Wilson loop is computed (S. Chatterjee, CMP 377 (2020) 307, arXiv:1811.09770; S. Cao, CMP 380
(2020); Forsstroem–Lenells–Viklund for finite abelian groups, arXiv:2001.07453); an area law up to the self-dual point I did not find.
**I found no Simon–Lieb-type inequality for Wilson loops, centre-vortex variables or glueball correlators of SU(2)**, and Tomboulis
(fn 10) states that the known methods fail for non-abelian groups.

**Worst case (Dobrushin–Shlosman family).** R. L. Dobrushin and S. B. Shlosman, "Constructive criterion for the uniqueness of Gibbs
field" and "Completely analytical Gibbs fields", in *Statistical Physics and Dynamical Systems* (Birkhaeuser, 1985) 347–370 and 371–403;
J. Stat. Phys. 46 (1987) 983; F. Martinelli and E. Olivieri, CMP 161 (1994) 447 and 487 — recalled. A condition on one finite box,
checked **for all boundary conditions** (the influence of the boundary on the box marginal is small in total), implies uniqueness and
exponential decay in every volume, and (complete analyticity) the same at every larger scale. Chatterjee states that these methods give
his Definition 2.3 for essentially every lattice gauge theory at small β. No positivity needed; the price is the worst case.

**Contour/cluster methods at the extremes.** Osterwalder–Seiler (strong coupling), Guth and Froehlich–Spencer (U(1) Coulomb phase:
the photon test is a theorem), C. Borgs and J. Imbrie, CMP 123 (1989) 305 (Pirogov–Sinai for field theory), finite-group frozen phases
(Borgs 1984, Cao 2020; via Chatterjee's references) — recalled. They reach the strong- and weak-coupling ends, never the crossover.

## 2. The floor, stated

### 2.1 Two geometries, and why a constant floor is the wrong target

(G1) **'t Hooft's geometry**: the twist through a whole symmetric torus of side L, p(L) = 1/(1 + e^{F_tw(L)}). 't Hooft's
classification as L → ∞: confinement F_tw → 0 (½ − p ~ e^{−σL²}), Coulomb F_tw → finite (p → p* ∈ (0, ½)), Higgs/frozen Z₂ F_tw → ∞
(p → 0). So a floor p ≥ p_min excludes only the third. c6b (RESULT.md) confirms with data: the photon has p bounded away from 0 at every
size; the finite subgroups at β = ∞ have exactly constant p (Q8 0.115, 2T 0.016, 2O 0.020, 2I 0.0063) and no confinement; SU(2) on
L√σ ∈ [2.1, 4.2] has ½ − p falling like e^{−(x² − 0.88)}. **What the proved theorems consume is the rate**: Tomboulis–Yaffe needs
1 − Z₋/Z = (1 − 2p)/(1 − p) ≤ e^{−ρL²}; Kanazawa's spin version needs 1 − ⟨O⟩ ≤ e^{−mL}. A floor gives a "string tension"
≥ log(…)/L² → 0: nothing.

(G2) **Fixed cells, many crossings** (the coordinator's binary channel): cells of one fixed side ℓ, a signal passing n cell faces. A
**per-crossing** flip probability bounded below by p_min **uniformly over everything outside the cell**, plus the property that only the
binary datum crosses (Markov in the flux sector), gives (1 − 2p_min)^n: a rate −log(1 − 2p_min)/ℓ, in every volume. Here a floor at
one scale is enough, and "not fading with L" means "not fading with the volume at fixed ℓ". This is the Dobrushin shape, and the
content sits in the uniformity over the outside and in the Markov property, both worst-case statements.

So the honest candidates are: **growth** (G1: F_tw(L) → 0 at the area rate along a tuning; Tomboulis' actual target, c6b's "act grows",
the owner's super-additivity applied to z_e) or **a worst-case per-cell floor plus a channel property** (G2). The literature's
one-box-to-all-volumes tools deliver the second kind (Dobrushin–Shlosman) or need positivity (Simon–Lieb), and a positivity route
delivers the first kind through a comparison (2.3).

### 2.2 The four candidate forms, known and open parts

| form | statement | known | open |
|---|---|---|---|
| F1 vortex criterion (G1) | ½ − p(L) ≤ C e^{−ρL²} for L ≥ L₀, uniformly along a tuning | ⇒ area law (Tomboulis–Yaffe); ⇒ 't Hooft ≤ Wilson tension consistency (Borgs–Seiler); true at strong coupling (Muenster) | everything at the crossover; it is not a one-box statement |
| F2 centre comparison (2.3) | at one block scale ℓ, the worst-case effective centre couplings J̄(ℓ) lie in the proved area-law region of 4D Z₂ gauge theory | the reduction (Ginibre + GKS II), the decomposition | J̄(ℓ) small; the 4D Z₂ area-law region beyond strong coupling; locality of J |
| F3 worst-case cell floor (G2) | decay under arbitrary boundary conditions in one cell (Dobrushin–Shlosman condition) at scale ℓ | ⇒ all volumes (DS); ⇒ area law and unbroken centre symmetry for connected G (Chatterjee 2.4) | the condition at weak coupling for SU(2) (worst case: Chatterjee doubts the mass-gap belief includes it) |
| F4 act growth (section 4) | z(2L) ≥ 2z(L) − c with z(L₀) > c, for z₀ or z_e | ⇒ floor m ≥ (z(L₀) − c)/L₀ (one line); equals D-T with summable loss | the inequality itself (cross-volume) |

### 2.3 F2 in detail: the "positive effective Z₂ couplings" candidate made exact (paper)

Let a centre-respecting blocking at scale ℓ produce block links U_b ∈ SU(2), and write U_b = σ_b V_b with σ_b ∈ {±1} and V_b in a fixed
section of SU(2) → SO(3). For any measure of the blocked field, the conditional law of σ given V has a density on {±1}^{links}, and
every function on {±1}^n is a multilinear polynomial, so **log density = Σ_A J_A(V) σ_A** with σ_A = Π_{b∈A} σ_b. Gauge invariance
restricts to A that are Z₂-gauge invariant (unions of closed surfaces' boundaries etc.). A fundamental Wilson loop is
W_C = σ_C · w_C(V) with |w_C| ≤ 1. Then

  |⟨W_C⟩| ≤ E_V |⟨σ_C⟩_{J(V)}| ≤ E_V ⟨σ_C⟩_{|J(V)|} ≤ ⟨σ_C⟩_{J̄},  J̄_A := sup_V |J_A(V)|,

the middle step by Ginibre's inequality (|⟨σ_C⟩_J| ≤ ⟨σ_C⟩_{|J|} for arbitrary-sign multi-spin couplings: expand both Boltzmann
factors of two replicas in (σ_B ± τ_B); recalled, standard), the last by GKS II (monotonicity in the couplings). At the bare level with
the Wilson action, J_p(V) = β·|½ tr V_p| with frustration signs, J̄_p = β, and this is (my reconstruction of) the Mack–Petkova
comparison: SU(2) at β is dominated by Z₂ at β.

**Candidate statement.** *If at one block scale ℓ the worst-case effective centre couplings J̄(ℓ) are local and lie in a region where
4D Z₂ gauge theory with couplings J̄ has an area law, then SU(2) has an area law in all volumes, with p → ½ at the area rate.* No
cross-volume step: the bound holds in every volume at once, because Ginibre and GKS are volume-free.

Known: the decomposition (always), the two inequalities (theorems for Ising-type multi-spin models), the Z₂ area law at strong
coupling. Open: (i) **J̄(ℓ) small**: the supremum includes block-flat SO(3) backgrounds, where a block-level vortex is a fine-level
thick vortex of thickness ~ℓ; (ii) locality/decay of J_A in the size of A after blocking (needed to apply any Z₂ result); (iii) the area
law of 4D Z₂ gauge theory with general local positive couplings beyond the convergent expansion (Duncan–Schweinhart do not cover it).
The sign problem of c5e 5.4 ("averaging over an SO(3) law that depends on the vortices can destroy positivity") **disappears** in this
form: Ginibre's absolute-value bound does not need positive couplings, only the worst case of |J|. The price moves to the supremum.

**Unit tests of F2** (paper):

| test | J̄(ℓ) | verdict |
|---|---|---|
| photon U(1) = Z₂ × U(1)/Z₂ | a block vortex is a π flux spread over a block; 4D Maxwell is scale invariant, cost ~ β_R π²/2 per block plaquette at every ℓ (the frozen act, r3 4.2) | J̄ frozen at weak coupling, no claim: **correct** |
| Z₂, both phases | J̄ = β (no SO(3) layer) | the statement is the Z₂ result itself: correct in both phases |
| deconfinement (one short direction) | temporal plaquettes: the centre layer orders (Polyakov loop), J̄ stays large there | no claim for Polyakov loops: correct |
| mixture / Heller endpoint | confinement intact | F2 may claim the area law (true there) and says nothing about the 0⁺⁺ mass: correct, and a reminder that F2 is confinement, not the vacuum gap |
| 2I at weak coupling | a block vortex needs a fine holonomy −1 around each meridian; with a discrete group some fine plaquette per meridian is ≠ 1, costing ≥ c·β per unit sheet area at every thickness | J̄ ≥ cβ, no claim: **correct**. SU(2): a thick vortex of thickness d spreads the angle, classical cost ~ β π²/d² per fine plaquette, so per block plaquette O(β_eff(ℓ)), falling with the running coupling. This is where **continuity** enters |

### 2.4 What an argument must use that 2I lacks

| ingredient | SU(2) | 2I | U(1) | used by |
|---|---|---|---|---|
| centre Z₂, binary flux | yes | yes | no (flux continuous) | TY, Kanazawa, F2 |
| −1 a commutator (twist eaters) | yes | yes | no | r3 (Lean) |
| **connected / continuous** | yes | **no** | yes | Chatterjee Lemma 4.1; thick-vortex cost ~1/d²; b₀ > 0 |
| stateless quotient layer at weak coupling | SO(3) disordered at scale (measured 0.0036 at L√σ = 2.80) | **A₅ orders** | — | c5e (L-A) |

Conclusion: a centre-only argument that would give 2I a gap at weak coupling is wrong; the two places a correct argument can pick up
the difference are continuity (thick vortices get cheap; Chatterjee's paths) and the stateless quotient layer. Continuity alone admits
U(1); binary flux alone admits 2I; only the combination (binary flux + continuity) or (binary flux + stateless quotient) separates
SU(2) from both. Chatterjee's theorem is the one proved result that already combines centre and continuity.

## 3. The owner's readings as mathematics

### 3.1 "Inward assertion has to be possible"

At small L (L ≪ 1/Λ) asymptotic freedom makes the SU(2) twist free energy grow: F_tw ≈ (3/2) log(1/g²(L)) + c (r3-monotone 4.3,
heuristic; the classical cost is zero by the twist eater, the rest is the missing flat directions). So **p(L) → 0 as L → 0**, roughly
like g(L)³: inward, the binary existence is almost never flipped (the small box is "deconfined", below 1/T_c; c6b has no data there,
the self-dual level p = 0.293 sits near 1/T_c). The reading therefore puts p near 0, not ½, inward.

As a statement: "inward assertion is possible" = **p(L) > 0 for every finite L** (strict positivity of Z_tw; on the lattice trivial,
Z_tw > 0; in the small-volume continuum p ~ C g³ > 0, heuristic). It supplies a **start** (D-UV of c5e: a positive act at a small box),
not a floor: it fades as L → 0, and the passage from p ≈ 0 inward to p ≈ ½ outward is r3's no-fixed-point statement (NFP), open.
Lower bound: pointwise only.

### 3.2 "The possibility space" ("might happen, but does not have to")

Precise version: **insertion tolerance (finite energy)**: for every outside configuration, the conditional probability of either flux
value of a cell lies in [ε, 1 − ε]. For a bounded action this holds with ε(ℓ) ~ e^{−(max action in the cell)}, for every group, photon
and 2I included, and ε shrinks with the cell volume and with β. So the plain version is true and group-blind (a relabelling). Made
**uniform** (ε independent of β along the tuning, at one fixed physical cell size), it is exactly the worst-case per-cell floor of
(G2)/F3, the right shape for Dobrushin–Shlosman. It still needs the binary-channel property (only the flux datum crosses), else the
photon passes it (a π flux through a cell is O(1)-likely for the photon, yet light carries continuous information across). Supplies:
the lower-bound **shape**; no proof.

### 3.3 "The assertion at a boundary reflects (≤ 50 %, minus entropy)"

p ≤ ½ ⇔ Z_tw ≤ Z ⇔ F_tw ≥ 0: proved (character positivity / RP, B1). The "50 % minus entropy" is exact as an identity:
**½ − p = ½ tanh(F_tw/2)**, and for SU(2) at weak coupling F_tw is purely entropic (zero classical cost, r3), so the deficit from 50 %
is set by an entropy in the literal sense. In the channel picture, p ≤ ½ means 1 − 2p ≥ 0: crossings never anti-correlate (positivity
of the transfer matrix). **Upper side only.** The reflection is reflection positivity; a correct relabelling, no lower bound.

### 3.4 "Why the floor holds": causality, accumulated acts, most efficient existence (cycle 6)

See section 4. In short: persistence alone fails the photon; exact super-additivity fails honest gapped theories; super-additivity up to
a bounded defect is the form that works, and it is the cross-volume step in a new coat. The "most stable state achievable" is the Gibbs
variational principle (the vacuum minimises the free energy density); the gap as the stability margin of that minimum is a reading,
not a step (a stable minimum can be gapless: the photon's vacuum is the Gibbs state too).

## 4. Super-additivity of the act (coordinator's request)

### 4.1 What it implies

If z(L₁ + L₂) ≥ z(L₁) + z(L₂) for all L₁, L₂ ≥ L₀, Fekete gives z(L)/L → sup_{L≥L₀} z(L)/L. Two consequences: (a) E₀(kL₀) ≥ E₀(L₀)
(the useful floor); (b) **E₀(L) ≤ m for every L ≥ L₀** (the box gap never exceeds the infinite-volume gap). (b) is a free by-product
and the place where it fails.

### 4.2 Known-false and known-true cases

* **Exact counterexamples (this note, `superadd_check.log`).** 2D Ising strips of width L = 2–12, brute-force transfer matrix, check:
  periodic E_odd(12) = 0.90683 against Onsager's m = 2(K* − K) = 0.906829 at K = 0.25. High temperature (gapped): E_odd decreases to m
  **from above** (1.040, 0.947, 0.920, …), periodic and free; E_even decreases to 2m from above. **All 25 pairs violate
  super-additivity in all four gapped cases** (pre-registered E1, E2: fail; E2's sign was not predicted: from above). Dirichlet massive
  scalar z = √(m²L² + π²): all 1128 pairs violate (E5). Free boundary conditions: GKS makes correlations grow with the width, so
  E(L) ≥ m always, and super-additivity fails whenever the inequality is strict.
* **SU(2) small boxes** (recalled: M. Luescher, Nucl. Phys. B219 (1983) 233; van Baal's small-volume work): E₀(L) ≈ ε g(L)^{2/3}/L, so
  z₀ → 0 only like g^{2/3} and **E₀(L) → ∞ as L → 0**: super-additivity is false for small L. c5e already noted D-T is false there.
* **SU(2) intermediate boxes**: the lowest centre-even state is a torelon pair (recalled), z₀ ≈ 2(σL² − π/3) − binding: convex in L,
  super-additive on that branch. Large L: the sign of the finite-size shift (Luescher 1986, recalled) decides, not fixed in general.
  No measured z₀(L) exists here (c5e PREREG-JOINT not run).
* **The flux act** z_e = L·E_e: c6b's fit z ≈ (L√σ)² − 0.88 on [2.1, 4.2] is super-additive with a large margin (defect
  c − 2x₁x₂ < 0 for x₁x₂ > 0.44). The owner's statement matches the **existence (flux) act**: the flux sheet's area is
  super-additive. Super-additivity of z_e gives E_e(kL) ≥ E_e(L), a confinement statement, not the vacuum gap.
* **Unit tests**: photon z₀ ↑ 2π: fails (correct; c5e's `bounded_violates_doubling`); 2I at fixed β: the frozen lattice theory is gapped
  in lattice units (finite-group decay results, special boundary conditions), so z₀ may be linear and super-additive at fixed β (no
  continuum claim, as c5e 6); 2I flux act at weak coupling: topological, bounded, fails (correct, deconfined); Heller endpoint: z₀
  bounded, fails (correct) while z_e grows.
* **Free energies**: log Z(Λ) is additive up to boundary terms (thermodynamic limit). For abelian positive-coefficient models,
  Z(Λ₁ ∪ Λ₂) ≥ Z(Λ₁)Z(Λ₂) (GKS/Ginibre super-multiplicativity); not known for SU(2) (Tomboulis fn 10). Vortex free energy: positive and
  decreasing in confinement, so F(2L) < 2F(L): not super-additive, and should not be.

### 4.3 What reflection positivity gives

* **Bachas** (C. Bachas, PRD 33 (1986) 2723, recalled): RP makes the static potential V(R) concave (⟨W(R)⟩² ≤ ⟨W(R−a)⟩⟨W(R+a)⟩),
  hence **sub-additive** (V(R₁ + R₂) ≤ V(R₁) + V(R₂) − V(0)): an upper bound on the big by the small. Wrong side, as always for RP across
  scales. (Torelon energies σL − π/(3L) are concave in L too.)
* **Chessboard**: −log⟨Π_i A_i⟩_Λ ≥ Σ_i (1/|Λ|)(−log⟨A_i^{tiled}⟩_Λ): a super-additivity of the insertion act, the **right side**, but
  every term is measured in the same big torus. Turning the tiled big-torus quantity into small-box data is the cross-volume step (c5e
  4.1). RP gives the right side in the wrong volume; decimation gives the wrong side across volumes.
* No RP inequality compares E₀ of two box sizes (r3-monotone section 2).

### 4.4 The repaired form

**Super-additivity up to a defect**: z(2L) ≥ 2z(L) − c for L ≥ L₀ (dyadic suffices). Then z(2^k L₀) ≥ 2^k z(L₀) − (2^k − 1)c, so
**E₀(2^k L₀) ≥ (z(L₀) − c)/L₀ for every k**: a floor from the one-box criterion z(L₀) > c. A summable defect φ(L) (Σ φ(2^k L₀)/2^k <
∞, de Bruijn–Erdős/Hammersley type) works the same way. It is c5e's D-T with loss η(L) = c/(2z(L)), summable when z grows linearly.
Checks (pre-registered E6): high-temperature Ising c = 0.48 / 0.67 (odd, periodic / free) and 3.15 / 2.67 (even), criterion holds
from L₀ = 2; ordered Ising, flip sector: criterion fails at every L₀ (no gap, correct); ordered Ising, even sector (gapped): criterion
holds (c = 4.07 / 3.06), correct — the analogue of "Z₂ at weak coupling is gapped but not confining"; photon: c on L ≤ 12 is 5.40 and the criterion is fooled from L = 5,
but on dyadic L up to 4096 c = 2π = sup z₀ and it fails (as pre-registered: a finite-range c is only a lower estimate). The defect is
"the boundary term": what two halves lose by sharing a face. The owner's "no sharing across a spanned boundary" is the statement c is
bounded; proving it is the two-sided step again.

## 5. Proposals for Lean (to c6a, not written here)

* `floor_of_superadd_defect`: `(∀ n, 2 * z n - c ≤ z (n+1)) → c < z 0 → ∀ n, (z 0 - c) / L₀ ≤ z n / (2^n * L₀)`; and the unit test
  `bounded_violates_superadd_defect`: a bounded z with `sup z ≤ c` never meets the criterion. Real analysis, a few lines, next to
  `floor_of_doubling`.
* `half_minus_p`: `1/2 - 1/(1 + exp F) = tanh (F/2) / 2` (the "50 % minus entropy" identity), next to the existing p ≤ ½.
* `ginibre_abs` (larger, optional): for Ising multi-spin measures on a finite set, |⟨σ_C⟩_J| ≤ ⟨σ_C⟩_{|J|}. It is the one new
  inequality F2 needs, finite and combinatorial.

## 6. Next step

1. **Measure J̄ at one scale** (F2's open part (i)), cheapest form: on stored blocked configurations, the conditional cost of a
   block-level centre vortex given the SO(3) block background, worst case over the sampled backgrounds and on the flat background,
   against the 4D Z₂ critical coupling; with the 2I control at large β (must stay ≥ cβ). A pre-registration of its own; not written.
2. **Reading** (one session): Mack–Petkova 1979 full text (confirm the comparison mechanism reconstructed in 2.3); the status of the
   area law of 4D Z₂ gauge theory beyond strong coupling; Ginibre 1970 for the multi-spin form.
3. When c5e's PREREG-JOINT runs: add the defect reading ĉ = max(2z₀(L) − z₀(2L)) and the one-box criterion z₀(L₀) > ĉ, for z₀ and z_e.

## 7. Not checked

Tomboulis–Yaffe 1985, Borgs–Seiler, Muenster, Mack–Petkova (both), Simon, Lieb, Ginibre, Dobrushin–Shlosman, Martinelli–Olivieri,
Osterwalder–Seiler, Bachas, Luescher not read in full; statements as cited in Kanazawa / Ito–Seiler / abstracts or recalled. The
Mack–Petkova mechanism in 2.3 is my reconstruction. Tomboulis 2007 read in the relevant sections only (not Appendices A–C in detail).
The F2 unit-test costs (thick vortex ~β π²/d², 2I ≥ cβ, U(1) frozen) are classical estimates, not proofs. The finite-group "decay under
special boundary conditions" is taken from Chatterjee's remark.
