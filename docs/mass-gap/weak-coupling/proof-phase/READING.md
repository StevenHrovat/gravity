# Reading pack for the proof phase (2026-11-22)

Scope: the open pieces of `../PROOF-BLUEPRINT.md` (P3.2-P3.3, P4.1-P4.7, P5.1-P5.2, P6.2-P6.6, with P3.4/P6.1 as background). Names are
transliterated (Luescher, Froehlich, Uensal). No other file was touched.

## How to read this pack

Every entry ends with a verification line. What I did: looked each citation up in INSPIRE, arXiv or the journal page in this session.

- **Verified: yes (record)**: the paper exists with exactly this citation (authors, title, journal or arXiv id, year), seen in INSPIRE, arXiv or the
  publisher. I did not read its content. The "what it gives" lines for such entries are standard knowledge or taken from the project's earlier
  notes, and are marked "(recalled)" when they go beyond the title.
- **Verified: yes (abstract)**: record plus the abstract was read in this session. The summary is limited to what the abstract says.
- **Verified: yes (text, partial)**: part of the full text was read in this session (named in the entry).
- **Verified: no**: I could not find or open the paper in this session. Treat the citation as a pointer from memory or from an earlier project note.

I read no paper in full. Claims about proofs inside papers that I did not open are not mine; where an earlier project note read the paper (for
example `r3-monotone/NOTE.md` read Ito-Seiler in full), the entry says so.

**Excluded on purpose.** arXiv:2605.02156 ("Lattice Gauge Theory and Wilson-Loop Confinement: A Statistical-Mechanical Survey", Zhou, Reed, Hayes)
came up in a search. arXiv shows it withdrawn for unverifiable authorship; it is not cited anywhere below. arXiv:2606.19362 (Faizal and Shabir,
Fortsch. Phys. 74 (2026) e70097) claims a reflection-positive construction of 4D SU(N) Yang-Mills with mass gap and confinement. I read only its
abstract and metadata (the PDF text was not extractable). It is an unvetted claim that follows the same two-route strategy as our blueprint
(strong-coupling route plus asymptotically free route). It is not relied on anywhere here; a worker may read it as an adversarial check, but
should treat every step as unverified.

## 1. The three most important reads per open piece

| piece | read first | why |
|---|---|---|
| P3.2-P3.3 (Lemma T, per-volume gap) | Dimock, Balaban III (arXiv:1304.0705); Balaban CMP 119 (1988) 243; Dobrushin-Shlosman finite-volume criterion (section 4.3) | the form of "uniform bounds on conditional laws of block variables" that the cluster expansions actually deliver; the finite-size criterion that turns boundary-insensitive finite-volume statements into decay |
| P4.1 (D' at L1 for every limit) | Dobrushin-Shlosman / Martinelli-Olivieri (section 4.3); Adhikari-Cao (arXiv:2202.10375); Chatterjee (arXiv:2006.16229) | D' is "decay uniform under arbitrary boundary condition", the same object as complete analyticity and as Chatterjee's hypothesis; Adhikari-Cao is the only rigorous weak-coupling decay result for non-abelian (finite) groups I found |
| P4.2 (act number z(L) grows) | Gonzalez-Arroyo and Martinez, NPB 459 (1996) 337 (hep-lat/9507001); Koller-van Baal, NPB 273 (1986) 387; Bergner, Gonzalez-Arroyo, Soler (arXiv:2505.10396) | the same observable in a twisted box from semiclassics through to confinement, with the small-volume formulas and the 2025 vortex-gas data |
| P4.3 (minimal action 4 pi^2/g^2) | Garcia Perez, Gonzalez-Arroyo, Snippe, van Baal, NPB 413 (1994) 535 (hep-lat/9309009); 't Hooft, CMP 81 (1981) 267; van Baal, CMP 85 (1982) 529 | the solution found numerically and the analytic twisted-torus solutions; certification must start from these |
| P4.4 (prefactor (L/a)^{11/3}) | 't Hooft, PRD 14 (1976) 3432; Luescher-Muenster, NPB 232 (1984) 445; Tanizaki-Uensal (arXiv:2201.06166) with Hayashi-Tanizaki-Uensal (arXiv:2505.07467) | the one-loop fluctuation determinant in the half-instanton background, the small-torus weak-coupling expansion, and the modern semiclassical treatment of flux sectors on small tori |
| P4.5 (order of limits, T before doubling) | Koller-van Baal, Ann. Phys. 174 (1987) 299; Luescher, NPB 219 (1983) 233; Kanazawa (arXiv:0805.2742) | spectral (T -> infinity) versus finite-T partition functions in the twisted box; the exact relation between vortex free energies on lattices of different size |
| P4.6 (no IR fixed point) | Luescher-Sommer-Weisz-Wolff, NPB 389 (1993) 247 (hep-lat/9207010); Luty-Polchinski-Rattazzi (arXiv:1204.5221); Dymarsky-Komargodski-Schwimmer-Theisen (arXiv:1309.2921) | the non-perturbative SU(2) running coupling; what is and is not proven about "gapped or scale invariant" |
| P4.7 (assumption U) | Tomboulis (arXiv:0707.2179) with Ito-Seiler (arXiv:0711.4930) and Kanazawa (arXiv:0805.2742) | the one place in the literature where "the blocked layer is the original action at another coupling, for the twisted ratio" was attempted, and exactly where it fails |
| **P5.1 (flux sector to vacuum gap)** | **Kanazawa, Annals Phys. 324 (2009) 1634 (arXiv:0808.3442); Tomboulis-Yaffe, CMP 100 (1985) 313; Chatterjee, CMP 385 (2021) 1007** | **the only rigorous statements I found that go from twist (boundary-condition) insensitivity to decay of a gauge-invariant correlation; Chatterjee is the converse. See section 4 and "possible clicks" C1, C2** |
| P5.2 (block observables to local observables) | Dimock III; Balaban CMP 122 (1989) 355; OpenAI construction README (section 2.4) | which observables the constructions control |
| P6.2 (non-triviality, uniqueness along line of constant physics) | OpenAI README (`nonfree`); Aizenman-Duminil-Copin (arXiv:1912.07973); LSSW 1993 | what "not free" is proved in their limit; the model of a rigorous non-triviality/triviality argument; the physical line of constant physics |
| P6.3-P6.5 (RP, rotations, reconstruction) | OpenAI README (`reconstruction`, Poincare covariance); Osterwalder-Schrader I and II; Seiler, Lect. Notes Phys. 159 | the claim that their limit already has Wightman reconstruction with Poincare covariance; the axiom framework |
| P6.6 (line of constant physics inside hypotheses) | Ramos, JHEP 11 (2014) 101 (arXiv:1409.1445); Luescher, JHEP 06 (2014) 105 (arXiv:1404.5930); LSSW 1993 | a non-perturbative coupling definition in the twisted box itself |

## 2. P3 and P4.4: constructive renormalisation

### 2.1 Balaban's series (Commun. Math. Phys.)

Taken together these construct the renormalisation-group flow for 3D and 4D lattice gauge theories. The 3D ultraviolet stability is complete (CMP 102
(1985) 255). In 4D the series gives small-field control, the coupling-constant renormalisation and the large-field renormalisation operation; the
abstract of CMP 122 (1989) 175 (per the project's earlier note, `r3-wp/NOTE.md`) says the R operation "removes the main obstacle to proving ultraviolet
stability". I did not read these papers; the project's own reading (`r3-wp/NOTE.md`, `H1-OPENAI.md`) is that the programme gives upper and lower
bounds e^{+-E|Lambda|} on partition functions and bounded effective actions uniformly in the cutoff, in finite volume, and is not complete as a
published construction of the continuum limit. Limits for our use: it controls the flow only from the cutoff down to weak coupling, not through the
crossover (P4); bounds are on partition functions and effective actions, with correlation functions and the sector (twist) structure not stated.

- Balaban, "Propagators and renormalization transformations for lattice gauge theories. I", CMP 95 (1984) 17-40. DOI 10.1007/BF01215753.
  https://doi.org/10.1007/BF01215753. Verified: yes (record).
- Balaban, "Propagators and renormalization transformations for lattice gauge theories. II", CMP 96 (1984) 223. DOI 10.1007/BF01240221.
  https://doi.org/10.1007/BF01240221. Verified: yes (record).
- Balaban, "Averaging operations for lattice gauge theories", CMP 98 (1985) 17-51. https://doi.org/10.1007/BF01211042. Verified: yes (record).
  Gives: the blocking (averaging) operation used instead of decimation (relevant to P1.6: reflection positivity of averaging blockings, still open).
  (recalled)
- Balaban, "Spaces of regular gauge field configurations on a lattice and gauge fixing conditions", CMP 99 (1985) 75.
  https://doi.org/10.1007/BF01466594. Verified: yes (record).
- Balaban, "Propagators for lattice gauge theories in a background field", CMP 99 (1985) 389. https://doi.org/10.1007/BF01240355. Verified: yes (record).
- Balaban, "The variational problem and background fields in renormalization group method for lattice gauge theories", CMP 102 (1985) 277-309.
  https://doi.org/10.1007/BF01229381. Verified: yes (record). Gives: the minimiser (background field) that carries the classical configurations.
  This is the part to read for P4.3/P4.4: background fields in a finite volume are where a flux or twist sector would enter. (recalled)
- Balaban, "Ultraviolet stability of three-dimensional lattice pure gauge field theories", CMP 102 (1985) 255-275.
  https://doi.org/10.1007/BF01229380. Verified: yes (record).
- Balaban, "Renormalization group approach to lattice gauge field theories. I. Generation of effective actions in a small field approximation and a
  coupling constant renormalization in four dimensions", CMP 109 (1987) 249. https://doi.org/10.1007/BF01215223. Verified: yes (record).
- Balaban, "Renormalization group approach to lattice gauge field theories. II. Cluster expansions", CMP 116 (1988) 1-22. DOI 10.1007/BF01239022
  (DOI from nLab, not checked at the publisher). Verified: yes (record) through several secondary citation lists (MaRDI portal, nLab, Springer reference
  lists); it did not appear in INSPIRE's author listing.
- Balaban, "Convergent renormalization expansions for lattice gauge theories", CMP 119 (1988) 243-285. https://doi.org/10.1007/BF01217741.
  Verified: yes (record).
- Balaban, "Large field renormalization. I. The basic step of the R operation", CMP 122 (1989) 175-202. https://doi.org/10.1007/BF01257412.
  Verified: yes (record).
- Balaban, "Large field renormalization. II. Localization, exponentiation, and bounds for the R operation", CMP 122 (1989) 355-392.
  https://doi.org/10.1007/BF01238433. Verified: yes (record).
- Balaban, Imbrie, Jaffe, "Effective action and cluster properties of the abelian Higgs model", CMP 114 (1988) 257. https://doi.org/10.1007/BF01225038.
  Verified: yes (record). Gives: a complete multiscale cluster expansion for a gauge model (abelian), the template for what a non-abelian version
  must do.

### 2.2 Dimock's expositions and related

- J. Dimock, "The renormalization group according to Balaban. I. Small fields", Rev. Math. Phys. 25 (2013) 1330010, arXiv:1108.1335.
  https://arxiv.org/abs/1108.1335. Verified: yes (abstract). Expository, scalar model (phi^4_3 in the project's reading); gives the architecture
  (block-averaging, background field, small-field expansion) without the gauge machinery.
- J. Dimock, "The renormalization group according to Balaban. II. Large fields", J. Math. Phys. 54 (2013) 092301, arXiv:1212.5562.
  https://arxiv.org/abs/1212.5562. Verified: yes (abstract). The large-field mechanism: a cube is large-field if a Gaussian, gradient or potential
  condition fails at a threshold, each costs a Gaussian-type small factor (project reading, `r3-wp/NOTE.md`). This is the template for our P3.1
  large-field lower bound.
- J. Dimock, "The renormalization group according to Balaban. III. Convergence", Ann. Henri Poincare 15 (2014) 2133-2175, arXiv:1304.0705.
  https://arxiv.org/abs/1304.0705. Verified: yes (abstract). Completes the expansion and convergence; read for the form of the final bounds
  (what norm, uniform in what), which decides how P3.2 (Lemma T) can be phrased.
- J. Dimock, "Ultraviolet stability for QED in d=3", arXiv:2009.01156 (2020, revised 2021). https://arxiv.org/abs/2009.01156.
  Verified: yes (abstract). Balaban's framework applied to a gauge theory (abelian) on a fine torus lattice with full control of the weak-coupling
  flow and ultraviolet stability in fixed finite volume. A nearer model than the scalar expositions for the gauge-field bookkeeping (gauge fixing,
  background fields).
- Bauerschmidt, Brydges, Slade, "Introduction to a renormalisation group method", Lecture Notes in Mathematics 2242 (Springer, 2019),
  arXiv:1907.05474. https://arxiv.org/abs/1907.05474. Verified: yes (record). A cleaner modern RG method (scalar/hierarchical models); a
  possible alternative framework for controlling the flow past weak coupling, not for gauge fields (recalled).
- Chandra, Chevyrev, Hairer, Shen, "Langevin dynamic for the 2D Yang-Mills measure", Publ. Math. IHES 136 (2022) 1-147, arXiv:2006.04987.
  https://arxiv.org/abs/2006.04987. Verified: yes (record).
- Chandra, Chevyrev, Hairer, Shen, "Stochastic quantisation of Yang-Mills-Higgs in 3D", Invent. Math. 237 (2024) 541-696, arXiv:2201.03487.
  https://arxiv.org/abs/2201.03487. Verified: yes (record). Both: a different (stochastic) route to existence in 2D and 3D; it uses a gauge-covariant
  flow, relevant to the gradient-flow click C6. Not 4D.
- Cao, Chatterjee, "A state space for 3D Euclidean Yang-Mills theories", arXiv:2111.12813 (2021). https://arxiv.org/abs/2111.12813.
  Verified: yes (abstract). Defines a state space of random distributional gauge orbits on the 3D torus, conditional on GFF-like short-distance
  behaviour that is assumed, not proved. 3D only.
- Cao, Chatterjee, "The Yang-Mills heat flow with random distributional initial data", arXiv:2111.10652. https://arxiv.org/abs/2111.10652.
  Verified: yes (record).
- Chatterjee, "Yang-Mills for probabilists", arXiv:1803.01950 (2018). https://arxiv.org/abs/1803.01950. Verified: yes (abstract). Frames the
  continuum-limit problem in probability terms and surveys the literature; use as an entry point to the constructive literature.

### 2.3 Federbush and Magnen-Rivasseau-Seneor

- Federbush, "A phase cell approach to Yang-Mills theory. I. Small field modes", CMP 107 (1986) 319-329. https://doi.org/10.1007/BF01209397.
  Verified: yes (record).
- Federbush, Williamson, "A phase cell approach to Yang-Mills theory. II. Analysis of a mode", J. Math. Phys. 28 (1987) 1416-1419.
  https://doi.org/10.1063/1.527495. Verified: yes (record).
- Federbush, "A phase cell approach to Yang-Mills theory. III. Stability, modified renormalization group transformation", CMP 110 (1987) 293-309.
  https://doi.org/10.1007/BF01207369. Verified: yes (record).
- Federbush, "A phase cell approach to Yang-Mills theory. IV. The choice of variables", CMP 114 (1988) 317-343. https://doi.org/10.1007/BF01225039.
  Verified: yes (record).
- Federbush, "A phase cell approach to Yang-Mills theory. V. Analysis of a chunk", CMP 127 (1990) 433-457. https://doi.org/10.1007/BF02104497.
  Verified: yes (record).
- Federbush, "A phase cell approach to Yang-Mills theory. VI. Nonabelian lattice-continuum duality", Ann. Inst. H. Poincare Phys. Theor. 47 (1987)
  17-23. Verified: yes (record). A parallel (non-Balaban) programme using phase cells; a second opinion on how the weak-coupling flow is organised.
  Not completed (the series stops at V-VI). (recalled)
- Magnen, Rivasseau, Seneor, "Construction of YM_4 with an infrared cutoff", CMP 155 (1993) 325-384. https://doi.org/10.1007/BF02097397.
  Verified: yes (record). The title says a finite (infrared-cut-off) 4D Yang-Mills construction; I did not read it. It is the only published
  statement I found that covers the continuum limit in a finite region, which is what the per-volume order of limits (mesh, then volume) of P3.3
  needs. Limits: infrared cutoff, not the gap, and the treatment of the crossover must be checked in the text. (recalled beyond title)
- Magnen, Rivasseau, Seneor, "Rigorous results on the ultraviolet limit of non-abelian gauge theories", Phys. Lett. B 283 (1992) 90-96.
  https://doi.org/10.1016/0370-2693(92)91433-A. Verified: yes (record). Short announcement of the above (recalled).

### 2.4 The OpenAI construction (continuum Yang-Mills, 2026)

What I could confirm in this session, and what comes from the project's earlier study (`../H1-OPENAI.md`, which read the Lean source):

- Shepherding Committee (Douglas, Gross (Chair), Jaffe, Klebanov, Nekrasov), "Proof by OpenAI of the existence of Quantum Yang-Mills Theory, 3rd
  Statement, Nov. 9, 2026". https://www.kitp.ucsb.edu/sites/default/files/3rd-Statement-About-Quantum-YangMills-Theory_Nov-9.pdf. Verified: yes
  (text, partial: the whole one-page statement was read). It announces the Lean code submitted on 28 Oct 2026 and a validation document, saying the
  check was that it "proves the existence of pure Yang-Mills theory according to the problem statements which are standard in physics and
  mathematics". It says nothing about a mass gap.
- yang-mills-group, "OpenAI-YM-20261028", Lean 4 project, README (pushed 10 Nov 2026). https://github.com/yang-mills-group/OpenAI-YM-20261028.
  Verified: yes (abstract; README read through a summarising fetch). Per the README: `YangMills.jointExistence` for every closed matrix group with a
  simple non-abelian Lie algebra; a Wilson lattice family; four properties: Wilson origin (lattice limits of finite moments, along subsequences of
  volumes), Wightman reconstruction (vacuum, fields, positive energy, Poincare covariance, locality), all-orders separated OPE with uniform
  coefficient bounds, and a non-freeness test (a two-point function of a centred stress trace that no finite sum of specified Wick profiles
  matches). It states a positive mass gap is outside the scope. It lists a verification of 100,168 declarations with only the standard three axioms.
- yang-mills-group, "YM" repository, `docs/assessment-1.pdf` (committee validation, 10 Nov 2026), 642 KB.
  https://github.com/yang-mills-group/YM/blob/main/docs/assessment-1.pdf. Verified: no for the content (the file exists; I could not extract its
  text in this session). Its content (no evidence for or against a gap; open: convergence and uniqueness of the volume limit, uniform gap)
  comes from `../H1-OPENAI.md` (earlier read) and press summaries, so treat as reported.
- Independent summary of the above timeline (OpenAI's natural-language proof 9 Sep 2026, Lean complete 16 Oct, delivery 28 Oct): news coverage
  only (e.g. https://explainx.ai/blog/openai-yang-mills-gross-group-lean-validation-november-2026). Secondary, not relied on.

What this gives the pieces, from `../H1-OPENAI.md` (marked [Lean] there when the statement was read in source):
- **P3.4 / P6.1**: control of the flow from the cutoff up to a unit scale where beta is about 9 x 10^5, as a stochastic blocking kernel with a
  small-field/large-field split of activities (the `Healthy` mask, E and K activities, exponential tails, per-level budgets independent of volume).
- **P6.2 (partial)**: the `nonfree` property is a statement that the limit is not a finite sum of free massive profiles. It does not exclude
  a pure-noise-type limit in our sense, and it holds for their family with beta_{N,p} chosen existentially.
- **P6.3 / P6.4 / P6.5 (a lead worth checking first)**: if the `reconstruction` property as stated in the README holds for the limit family, then the
  subsequential limit already satisfies Wightman axioms including Poincare covariance, which would give rotation invariance of the limit
  (P6.4) and an OS/Wightman reconstruction (P6.5) for *their* limit. The blueprint lists P6.4 as open and P6.3 as open for the limit. What needs
  checking: the statement is for smeared renormalised local insertions in the "selected phase", along subsequences, with the bare coupling
  chosen by the construction. Whether our hypotheses (P6.6, a line of constant physics fixed in our terms) pick out their limit is open.
- Limits for us: nothing about the crossover, nothing about the gap, no control of large-field outsides (`H1-OPENAI.md` section 3).

## 3. Twisted boxes, fractional instantons, flux energies (P4.2-P4.5)

### 3.1 't Hooft and van Baal

- 't Hooft, "On the phase transition towards permanent quark confinement", Nucl. Phys. B 138 (1978) 1-25. https://doi.org/10.1016/0550-3213(78)90153-0.
  Verified: yes (record). Order and disorder parameters (loops); the Z_N duality that P1.4 formalises.
- 't Hooft, "A property of electric and magnetic flux in non-abelian gauge theories", Nucl. Phys. B 153 (1979) 141-160.
  https://doi.org/10.1016/0550-3213(79)90595-9. Verified: yes (record). The twisted boundary conditions, the flux sectors and the cocycle condition;
  the base reference for P1.3 and for the Fourier transform between twist and electric flux.
- 't Hooft, "Some twisted self-dual solutions for the Yang-Mills equations on a hypertorus", CMP 81 (1981) 267-275. https://doi.org/10.1007/BF01208900.
  Verified: yes (record). The constant-field-strength abelian solutions on T^4 with fractional topological charge; the explicit configuration behind
  "attainment on the symmetric torus" in `r4-conjw/NOTE.md`.
- 't Hooft, "Topology of the gauge condition and new confinement phases in non-abelian gauge theories", Nucl. Phys. B 190 (1981) 455-478.
  https://doi.org/10.1016/0550-3213(81)90442-9. Verified: yes (record). Classification of phases by the behaviour of the twist free energies.
- van Baal, "Some results for SU(N) gauge fields on the hypertorus", CMP 85 (1982) 529. https://doi.org/10.1007/BF01403503. Verified: yes (record).
  Gives the fractional charge Q = -n.n~/N mod 1 (as quoted in `r4-conjw/NOTE.md`) and the structure of twisted sectors.
- van Baal, van Geemen, "A simple construction of twist-eating solutions", J. Math. Phys. 27 (1986) 455. https://doi.org/10.1063/1.527242.
  Verified: yes (record). Twist eaters, the objects behind "-1 is a commutator" (P4.2 and `su2_twist_eater`).
- van Baal, "Gauge theory in a finite volume", Acta Phys. Polon. B 20 (1989) 295-312. Verified: yes (record). A lecture-level review of the
  finite-volume programme; a compact start for a new worker. (recalled)
- Hansson, van Baal, Zahed, "Chromomagnetic energy of SU(2) gauge fields on a torus", Nucl. Phys. B 289 (1987) 628-644.
  https://doi.org/10.1016/0550-3213(87)90398-1. Verified: yes (record).

### 3.2 Small-volume analytic results

- Luescher, "Some analytic results concerning the mass spectrum of Yang-Mills gauge theories on a torus", Nucl. Phys. B 219 (1983) 233-261.
  https://doi.org/10.1016/0550-3213(83)90436-4. Verified: yes (record). Small-volume expansion of the low energy levels in the Hamiltonian
  formulation, with the effective Hamiltonian for the constant modes. The route by which both the 0+ mass in vacuum sector and the flux
  energies are computed in the same small-volume effective theory. (recalled)
- Luescher, Muenster, "Weak coupling expansion of the low lying energy values in the SU(2) gauge theory on a torus", Nucl. Phys. B 232 (1984) 445.
  https://doi.org/10.1016/0550-3213(84)90038-5. Verified: yes (record).
- Koller, van Baal, "A rigorous nonperturbative result for the glueball mass and electric flux energy in a finite volume", Nucl. Phys. B 273 (1986)
  387-412. https://doi.org/10.1016/0550-3213(86)90252-X. Verified: yes (text, partial: title page and first two pages read from the Leiden scan,
  https://www.lorentz.leidenuniv.nl/research/vanbaal/DECEASED/HOME/JOUR/NPB273_387.pdf). **Reading note for P5.1.** The abstract says the paper
  gives "the final result for the short-distance expansion of the energy of 't Hooft-type electric flux, in units of the glueball mass", plus a
  non-perturbative correction to the glueball mass and mass ratios, already significant at z = M(0+)L = 1 (their z is the glueball mass times L,
  not our act number). Introduction: the tunnelling that removes an 8-fold degeneracy labelled by electric flux gives the flux energy, and the
  excited-level glueball masses arise "through the same channel", so both are affected by the same tunnelling mode for z < 1. "Rigorous" here
  means a controlled short-distance expansion, not a theorem of mathematical physics. Limits: only z < 1, SU(2) on T^3, the bridge to
  large L is by comparison with Monte Carlo data (Berg and Billoire).
- Koller, van Baal, "QCD on a torus and electric flux energies from tunneling", Ann. Phys. 174 (1987) 299. https://doi.org/10.1016/0003-4916(87)90032-7.
  Verified: yes (record). Tunnelling calculation of flux energies, the semiclassical formula behind B1/B2 in the small-volume regime. (recalled)

### 3.3 Fractional instantons and cooling

- Garcia Perez, Gonzalez-Arroyo, Snippe, van Baal, "Instantons from over-improved cooling", Nucl. Phys. B 413 (1994) 535-552, hep-lat/9309009.
  https://arxiv.org/abs/hep-lat/9309009. Verified: yes (abstract). The abstract (read) says: modified lattice actions use discretisation errors
  to find the largest instantons in a periodic spatial box with long time extent; the largest instanton is a tunnelling through a sphaleron; with
  twisted boundary conditions in time, instanton solutions with at least eight parameters must exist. The claims quoted in `r4-conjw/NOTE.md`
  ("minimal action 4 pi^2", "solutions cannot fall through the lattice", eq. 19 with c = 1/5) are from the text, which I did not re-read; check
  them before certifying B1.
- Garcia Perez, Gonzalez-Arroyo, Martinez, et al., "Instanton-like contributions to the dynamics of Yang-Mills fields on the twisted torus",
  Phys. Lett. B 305 (1993) 366-374, hep-lat/9302007. https://arxiv.org/abs/hep-lat/9302007. Verified: yes (record). (Earlier read in summary by
  `r4-actnumber/NOTE.md`: lattice instanton actions 37.49, 38.64, 39.00 tending to 4 pi^2, very long autocorrelations.)
- Gonzalez-Arroyo, Martinez, "Investigating Yang-Mills theory and confinement as a function of the spatial volume", Nucl. Phys. B 459 (1996)
  337-354, hep-lat/9507001. https://arxiv.org/abs/hep-lat/9507001. Verified: yes (abstract; full text read by `r4-actnumber/NOTE.md`). Electric flux
  energies against volume in twisted SU(2); smooth interpolation from semiclassics to confinement; proposes confinement from non-dilute
  multi-instanton configurations. **Correction to a project note:** `r4-actnumber/NOTE.md` calls this paper "how the string tension is built up".
  That is the title of the Lattice 1993 proceedings hep-lat/9312066 (Nucl. Phys. B Proc. Suppl. 34 (1994) 228); the NPB 459 paper has the title above.
- Garcia Perez, Gonzalez-Arroyo, Martinez, "From perturbation theory to confinement: how the string tension is built up", Nucl. Phys. B Proc.
  Suppl. 34 (1994) 228-230, hep-lat/9312066. https://arxiv.org/abs/hep-lat/9312066. Verified: yes (record).
- Gonzalez-Arroyo, "Yang-Mills fields on the four-dimensional torus. Part 1: classical theory", Peniscola 1997 school, pp. 57-91, hep-th/9807108.
  https://arxiv.org/abs/hep-th/9807108. Verified: yes (record). The review of classical twisted-torus solutions (recalled); first place to look for
  the existence of smooth self-dual solutions and the moduli spaces (relevant to B1).
- Gonzalez-Arroyo, Montero, "Self-dual vortex-like configurations in SU(2) Yang-Mills theory", Phys. Lett. B 442 (1998) 273-278, hep-th/9809037.
  https://arxiv.org/abs/hep-th/9809037. Verified: yes (record).
- Gonzalez-Arroyo, "Constructing SU(N) fractional instantons", JHEP 02 (2020) 137, arXiv:1910.12565. https://arxiv.org/abs/1910.12565.
  Verified: yes (record).
- Tanizaki, Uensal, "Center vortex and confinement in Yang-Mills theory and QCD with anomaly-preserving compactifications", PTEP 2022 (2022)
  04A108, arXiv:2201.06166. https://arxiv.org/abs/2201.06166. Verified: yes (abstract). Compactifies on T^2 with 't Hooft flux so as to preserve the 4d
  anomaly; gives a semiclassical centre-vortex description of confinement; conjectures (does not derive) adiabatic continuity from small T^2 x
  R^2 to R^4. Limits: weak coupling on a small T^2 only; the link to R^4 is a conjecture.
- Hayashi, Tanizaki, Uensal, "Center-vortex semiclassics with non-minimal 't Hooft fluxes on R^2 x T^2 and center stabilization at large N", JHEP 02
  (2026) 126, arXiv:2505.07467. https://arxiv.org/abs/2505.07467. Verified: yes (record).
- Bergner, Gonzalez-Arroyo, Soler, "A T_2 x R^2 roadmap to confinement in SU(2) Yang-Mills theory", JHEP 10 (2025) 087, arXiv:2505.10396.
  https://arxiv.org/abs/2505.10396. Verified: yes (abstract). SU(2) on a twisted T^2 times R^2: semiclassics at small torus, a 2D gas of vortex-like
  fractional instantons with growing size and density as the torus grows, the scale where the gas stops being dilute, string tension matching a
  2D centre-vortex gas at low density, and a regime where boundary conditions become irrelevant and all scales are set by Lambda. Numerical,
  with semiclassical predictions; no proof. The closest modern data for z(L), for B2's growth, and for the "large end" of the act-number run.
- Bergner, Gonzalez-Arroyo, Soler, "Identifying topological structures with adjoint mode filtering", JHEP 05 (2024) 048, arXiv:2401.16913.
  https://arxiv.org/abs/2401.16913. Verified: yes (record).
- Anber and Poppitz on multi-fractional instantons on the twisted T^4: not found in INSPIRE in this session. Verified: no.
- Simon, Ann. Math. 120 (1984) 89 and Helffer-Sjoestrand (1984), cited in `r4-conjw/NOTE.md` for the semiclassical tunnelling splitting: not looked up
  here. Verified: no.

### 3.4 What the pieces can take from this block

- P4.2: the numerical picture (Gonzalez-Arroyo and Martinez 1996; Bergner et al. 2025) is that flux energies interpolate from semiclassics to
  confinement; a theorem for z(L) is not in this literature. The free-photon marginality (z = 2 pi alpha frozen, proved by the project) is the
  consistency check.
- P4.3: the existence of the self-dual solution is numerical (cooling) and, for explicit abelian configurations, analytic ('t Hooft 1981).
  I did not find a published rigorous proof that the minimum of the action in the (1,1,1) twisted T^3 x R sector is exactly 4 pi^2/g^2.
- P4.4: the standard prefactor computations are 't Hooft (1976) for instantons and Luescher-Muenster (1984) in the weak-coupling torus Hamiltonian;
  the half-instanton prefactor along a line of constant physics needs the regularisation-independent definition of the coupling, for which the
  gradient-flow coupling in a twisted box (section 7) is now available.
- P4.5: Koller-van Baal and Luescher treat the Hamiltonian (T -> infinity) limit; Kanazawa (section 4.1) relates twisted and untwisted partition
  functions at finite T exactly, with a coupling mismatch.

## 4. Vortex free energy and confinement criteria (P4.6, P5)

### 4.1 The rigorous core

- Tomboulis, Yaffe, "Finite temperature SU(2) lattice gauge theory", CMP 100 (1985) 313-341. https://doi.org/10.1007/BF01206134. Verified: yes
  (record; a search result describes it as using reflection positivity to bound 't Hooft loops, Wilson loops and flux free energies). Wilson loop
  bounded in terms of the vortex free energy (see Kanazawa's form below; project reading in `r3-monotone/NOTE.md`: <W(C)> <= 2 {1/2 (1 -
  Z_-/Z)}^{A_C/(L_mu L_nu)}). It works inside one volume: it turns input about F_m(L) into output.
- **Kanazawa, "Generalizing the Tomboulis-Yaffe inequality to SU(N) lattice gauge theories and general classical spin systems", Annals Phys. 324
  (2009) 1634-1665, arXiv:0808.3442.** https://arxiv.org/abs/0808.3442. Verified: yes (text, partial: the first 100,000 characters of the HTML
  version were read through a summarising fetch). **The only rigorous statement I found from twist insensitivity to decay of a correlation, i.e.
  the closest published object to P5.1.** What it states (Theorem 5 for spin systems, with the lattice-gauge analogue Theorem 2): for a
  gauge-invariant observable Gamma_mu(x; n) at separation n along direction mu, with a wall V perpendicular to mu and a wall-creation operator
  O(g)[V] for a twist g in G (g need not be central),
  |<Gamma(n)>| / <Gamma(0)> <= 2 {<Gamma(0)^2> / <Gamma(0)>^2}^{n/L_mu} {1 - Int dg <O(g)[V]>}^{n/L_mu}.
  Hypotheses: reflection positivity, symmetry of the measure under G, zero group average of the observable, and a dyadic box L_mu = 2^k n. The
  logic (as summarised): split the correlator with the trivial-representation wall operator, apply the Schwarz inequality in a reflection plane,
  iterate doubling the separation. When the wall free energy is insensitive to the boundary condition (the integral of <O> tends to 1) the
  correlator decays exponentially with distance, and the author reads this as a mass gap in the disordered phase.
  **Limits and what is not in the excerpt:** (i) an upper bound on a correlator of a gauge-invariant observable *inside one finite periodic box*;
  the passage to a vacuum-sector spectral gap needs the limit L -> infinity and positivity, which the excerpt does not carry out (the excerpt
  does not say the gap is that of the untwisted vacuum sector); (ii) the exponent: with n/L_mu in the exponent, a decay rate m requires
  (moment ratio)(1 - <F>) < e^{-m L_mu}, so what is needed is that the twist non-insensitivity 1 - <F> decays at least exponentially in the
  *linear* size L (my reading of the formula; check against the text); (iii) the second moment ratio <Gamma^2>/<Gamma>^2 must be controlled;
  (iv) positivity of <Gamma(n)> for odd n is not guaranteed. The geometry of the twist (which hyperplane or plane, which box shape, T equal to L)
  must be read from the paper before any use.
- Kanazawa, "A theorem concerning twisted and untwisted partition functions in U(N) and SU(N) lattice gauge theories", Phys. Lett. B 670 (2009)
  421-427, arXiv:0805.2742. https://arxiv.org/abs/0805.2742. Verified: yes (abstract). Derives an exact relation between a linear combination of
  vortex free energies on a lattice and the same on a smaller lattice, with a coupling discrepancy argued to vanish in the thermodynamic limit;
  compares with Tomboulis and has an appendix on loopholes in Tomboulis's proof. This is the cleanest exact statement of the "compare two
  different volumes" step the blueprint calls the one-sided step (see click C4).
- Chatterjee, "A probabilistic mechanism for quark confinement", CMP 385 (2021) 1007-1039, arXiv:2006.16229. https://arxiv.org/abs/2006.16229.
  Verified: yes (abstract). Rigorous definition of centre symmetry for lattice gauge theories; proves that unbroken centre symmetry implies
  confinement; proves that if the gauge group has non-trivial centre and correlations decay exponentially under arbitrary boundary conditions,
  centre symmetry is not broken. The decay hypothesis is not established for any particular theory (as far as the abstract shows). This is the
  converse direction of P5.1: gap-type decay for all boundary conditions implies the flux-side statement.
- Cao, Nissim, Sheffield, "Expanded regimes of area law for lattice Yang-Mills theories", arXiv:2505.16585 (2025). https://arxiv.org/abs/2505.16585.
  Verified: yes (abstract). Area law for pure U(N) lattice Yang-Mills in parameter regimes beyond Osterwalder-Seiler's, using the master loop
  equation; a search result states this extends the previously only area-law regime in 4D, Osterwalder-Seiler's strong coupling. U(N), not SU(2).
- Osterwalder, Seiler, "Gauge field theories on the lattice", Annals Phys. 110 (1978) 440. https://doi.org/10.1016/0003-4916(78)90039-8.
  Verified: yes (record). Reflection positivity for lattice gauge theory, and (recalled) the strong-coupling cluster expansion with area law
  and a mass gap. The base of P2.5.
- Adhikari, Cao, "Correlation decay for finite lattice gauge theories at weak coupling", arXiv:2202.10375 (2022). https://arxiv.org/abs/2202.10375.
  Verified: yes (abstract). Exponential decay of correlations for gauge-invariant functions (including functions of Wilson loops) for finite
  (possibly non-abelian) gauge groups at weak coupling. (A search snippet says it appeared in the Annals of Probability; not confirmed.) The
  requested "Adhikari-Cao on Wilson loops at strong coupling": I found no such paper in this session; the Adhikari-Cao paper that exists is
  this one, at weak coupling. Verified: no for the strong-coupling title.
- Basu, Ganguly, "SO(N) lattice gauge theory, planar and beyond", arXiv:1608.04379. https://arxiv.org/abs/1608.04379. Verified: yes (record).
  Strong-coupling large-N Wilson loops (recalled).

### 4.2 Mack-Petkova, Yaffe, Borgs-Seiler, Tomboulis, Ito-Seiler

- Mack, Petkova, "Comparison of lattice gauge theories with gauge groups Z(2) and SU(2)", Ann. Phys. 123 (1979) 442.
  https://doi.org/10.1016/0003-4916(79)90346-4. Verified: yes (record).
- Mack, Petkova, "Sufficient condition for confinement of static quarks by a vortex condensation mechanism", Ann. Phys. 125 (1980) 117.
  https://doi.org/10.1016/0003-4916(80)90121-9. Verified: yes (record). A sufficient condition on the vortex free energy (recalled, and as read in
  abstracts by `r3-monotone/NOTE.md`).
- Mack, Petkova, "Z2 monopoles in the standard SU(2) lattice gauge theory model", Z. Phys. C 12 (1982) 177. https://doi.org/10.1007/BF01548615.
  Verified: yes (record). The SO(3) x Z_2 split used in `r3-monotone/NOTE.md`.
- Yaffe, "Confinement in SU(N) lattice gauge theories", Phys. Rev. D 21 (1980) 1574. https://doi.org/10.1103/PhysRevD.21.1574. Verified: yes (record).
- Borgs, Seiler, "Lattice Yang-Mills theory at nonzero temperature and the confinement problem", CMP 91 (1983) 329. https://doi.org/10.1007/BF01208780.
  Verified: yes (record).
- Borgs, Seiler, "Quark deconfinement at high temperature: a rigorous proof", Nucl. Phys. B 215 (1983) 125-135.
  https://doi.org/10.1016/0550-3213(83)90270-5. Verified: yes (record). The deconfinement unit test (twist free energy nonzero at high T) is rigorous
  here.
- Tomboulis, "Confinement for all values of the coupling in four-dimensional SU(2) gauge theory", arXiv:0707.2179. https://arxiv.org/abs/0707.2179.
  Verified: yes (abstract). Claims, with decimation transformations made into inequalities, that SU(2) is confining at all couplings, via the
  vortex free energy. Not accepted as a proof (see Ito-Seiler); no journal reference listed.
- Ito, Seiler, "On the recent paper on quark confinement by Tomboulis", arXiv:0711.4930. https://arxiv.org/abs/0711.4930. Verified: yes (record; full
  text read by `r3-monotone/NOTE.md`, which reports that the claim needs a parameter t* with alpha(t*) = alpha+(t*), reduces it to an inequality
  that is not proved, and that no such t* exists for U(1)).
- Ito, Seiler, "Further discussion of Tomboulis' approach to the confinement problem", arXiv:0803.3019. https://arxiv.org/abs/0803.3019.
  Verified: yes (record).
- Kovacs, Tomboulis, "Computation of the vortex free energy in SU(2) gauge theory", Phys. Rev. Lett. 85 (2000) 704-707, hep-lat/0002004.
  https://arxiv.org/abs/hep-lat/0002004. Verified: yes (record).
- Kovacs, Tomboulis, "Vortex waistlines and long range fluctuations", Phys. Rev. D 65 (2002) 074501, hep-lat/0108017.
  https://arxiv.org/abs/hep-lat/0108017. Verified: yes (abstract). Uses exact relations and inequalities between the Wilson loop and the vortex and
  electric flux order parameters; only vortices thick compared with the loop can produce a strictly linear potential; the long-range
  fluctuations form an effective strongly coupled Z(N) theory. A search summary says its mass-gap link is an assumption (exponential
  transverse spreading of the flux); I did not verify that statement.
- de Forcrand, von Smekal, "'t Hooft loops, electric flux sectors and confinement in SU(2) Yang-Mills theory", Phys. Rev. D 66 (2002) 011504,
  hep-lat/0107018. https://arxiv.org/abs/hep-lat/0107018. Verified: yes (abstract). Free energies in fixed-electric-flux sectors against volume and
  temperature; they report evidence for a mass gap. Numerical.
- von Smekal, de Forcrand, "Electric flux sectors and confinement", hep-ph/0205002 (proceedings, 2002). https://arxiv.org/abs/hep-ph/0205002.
  Verified: yes (record).

### 4.3 Statistical-mechanics side of "boundary insensitivity implies decay"

- Dobrushin, Shlosman, "Completely analytical Gibbs fields" and "Constructive criterion for the uniqueness of Gibbs field" (in Statistical Physics
  and Dynamical Systems, Birkhaeuser, 1985; further "Completely analytical interactions: constructive description", J. Stat. Phys. 46 (1987) 983).
  Verified: no for page numbers and details. A search in this session confirmed the 1985 chapter title and the notion: complete analyticity is a
  finite-region condition on total-variation distances between Gibbs measures with different boundary conditions, equivalent (Dobrushin-Warstat)
  to several other conditions; the finite-volume uniform form is strictly stronger than the infinite-volume notion (a search summary of
  Martinelli-Olivieri). This is the classical theorem that boundary-condition insensitivity in finite regions is equivalent to exponential
  mixing; our D' and P2.3 are of this type.
- Martinelli, Olivieri, "Approach to equilibrium of Glauber dynamics in the one phase region. I, II", CMP 161 (1994) 447 and 487.
  Verified: no (recalled; seen only as a reference tag in search results). Complete analyticity restricted to regular domains, the version
  adapted to renormalisation-group problems.

## 5. Infrared fixed points and the conformal window (P4.6)

- Banks, Zaks, "On the phase structure of vector-like gauge theories with massless fermions", Nucl. Phys. B 196 (1982) 189-204.
  https://doi.org/10.1016/0550-3213(82)90035-9. Verified: yes (record). The infrared fixed point of asymptotically free theories with enough
  flavours (the Banks-Zaks fixed point, recalled); the unit test of the blueprint.
- Luescher, Sommer, Weisz, Wolff, "Computation of the running coupling in the SU(2) Yang-Mills theory", Nucl. Phys. B 389 (1993) 247-264,
  hep-lat/9207010. https://arxiv.org/abs/hep-lat/9207010. Verified: yes (record). The non-perturbative step-scaling running of the
  Schroedinger-functional coupling in pure SU(2) (recalled): the lattice evidence that pure SU(2) has no fixed point in the range probed. A
  numerical result over a finite range, not a proof of absence of an IR fixed point.
- Luescher, Narayanan, Weisz, Wolff, "The Schroedinger functional: a renormalizable probe for non-abelian gauge theories", Nucl. Phys. B 384 (1992)
  168-228, hep-lat/9207009. https://arxiv.org/abs/hep-lat/9207009. Verified: yes (record).
- de Divitiis, Frezzotti, Guagnelli, Petronzio, "A definition of the running coupling constant in a twisted SU(2) lattice gauge theory", Nucl. Phys. B
  422 (1994) 382-396, hep-lat/9312085. https://arxiv.org/abs/hep-lat/9312085. Verified: yes (record; abstract read earlier by `r4-actnumber/NOTE.md`).
- de Divitiis, Frezzotti, Guagnelli, Petronzio, "Nonperturbative determination of the running coupling constant in quenched SU(2)", Nucl. Phys. B
  433 (1995) 390-402, hep-lat/9407028. https://arxiv.org/abs/hep-lat/9407028. Verified: yes (record).
- Polchinski, "Scale and conformal invariance in quantum field theory", Nucl. Phys. B 303 (1988) 226-236. https://doi.org/10.1016/0550-3213(88)90179-4.
  Verified: yes (record).
- Komargodski, Schwimmer, "On renormalization group flows in four dimensions", JHEP 12 (2011) 099, arXiv:1107.3987. https://arxiv.org/abs/1107.3987.
  Verified: yes (record). The a-theorem (recalled).
- Luty, Polchinski, Rattazzi, "The a-theorem and the asymptotics of 4D quantum field theory", JHEP 01 (2013) 152, arXiv:1204.5221.
  https://arxiv.org/abs/1204.5221. Verified: yes (abstract). Using a generalised Komargodski-Schwimmer argument, flows that approach neither a CFT in
  the UV nor in the IR are ruled out in the following sense: if the asymptotic behaviour is perturbative, beta functions must vanish faster than
  (1/|ln mu|)^{1/2}, so the only perturbative endpoint is a CFT; perturbative scale invariance without conformal invariance (limit cycles) is
  excluded; a separate non-perturbative argument works only if the stress tensor is non-trivial in a technical sense they define. Limits: physics-level
  arguments (unitary Lorentz-invariant QFT), not rigorous constructive statements.
- Dymarsky, Komargodski, Schwimmer, Theisen, "On scale and conformal invariance in four dimensions", JHEP 10 (2015) 171, arXiv:1309.2921 (first
  posted Sep 2013). https://arxiv.org/abs/1309.2921. Verified: yes (abstract). Under unitarity, scale invariance forces infinitely many matrix
  elements to vanish in a certain kinematic configuration, a necessary condition for conformality; an argument (not a proof) that it is also
  sufficient. Limit: sufficiency is an expectation with unspecified possible exceptions.
- Nakayama, "Scale invariance vs conformal invariance", Phys. Rept. 569 (2015) 1-93, arXiv:1302.0884. https://arxiv.org/abs/1302.0884.
  Verified: yes (record). The review of the field.
- Gaiotto, Kapustin, Seiberg, Willett, "Generalized global symmetries", JHEP 02 (2015) 172, arXiv:1412.5148. https://arxiv.org/abs/1412.5148.
  Verified: yes (abstract). q-form symmetries; 1-form symmetry acting on Wilson lines, coupling to backgrounds, spontaneous breaking, 't Hooft
  anomalies and anomaly matching. The abstract does not discuss confinement; the connection (centre symmetry, twist = background for the 1-form
  symmetry) is the standard reading (recalled), and the same background fields are the twisted boundary conditions of section 3.

**Is a "gapped or scale-invariant" dichotomy proven anywhere?** Not rigorously, in what I found. LPR and DKST are physics-level arguments with stated
assumptions (perturbative asymptotics; stress tensor non-trivial; sufficiency only argued). The project's act number z(L) = E_e L has a natural
reading here (click C5): in a scale-invariant theory on T^3 x R every energy scales as 1/L, so z is constant; z unbounded is exactly scale-dependent
behaviour. Nothing rigorous found that turns "something must run" into a theorem for pure SU(2).

## 6. Existence and axioms (P6)

- Osterwalder, Schrader, "Axioms for Euclidean Green's functions", CMP 31 (1973) 83-112. https://doi.org/10.1007/BF01645738. Verified: yes (record).
- Osterwalder, Schrader, "Axioms for Euclidean Green's functions. II", CMP 42 (1975) 281-305. https://doi.org/10.1007/BF01608978. Verified: yes (record).
  Reconstruction of a Wightman theory from Euclidean Schwinger functions with reflection positivity (the OS axioms; recalled). Note in the
  literature that the first paper's linear growth condition was repaired in the second.
- Luescher, "Construction of a selfadjoint, strictly positive transfer matrix for Euclidean lattice gauge theories", CMP 54 (1977) 283.
  https://doi.org/10.1007/BF01614090. Verified: yes (record). The lattice transfer matrix of P1.3.
- Seiler, "Gauge theories as a problem of constructive quantum field theory and statistical mechanics", Lecture Notes in Physics 159 (Springer, 1982),
  1-192. Verified: yes (record). The standard lecture notes on the lattice setup, reflection positivity, strong-coupling expansions and the
  state of the constructive programme at the time (recalled).
- Aizenman, Duminil-Copin, "Marginal triviality of the scaling limits of critical 4D Ising and phi^4_4 models", Annals of Math. 194 (2021) 163,
  arXiv:1912.07973. https://arxiv.org/abs/1912.07973. Verified: yes (abstract). Scaling limits of spin fluctuations at and near criticality in 4D
  nearest-neighbour Ising models are Gaussian; same for lattice-regularised phi^4_4 in the joint limit of infinite volume and vanishing spacing.
  Method: random current representation, deviations from Wick's law as intersection probabilities, a logarithmically improved tree-diagram
  bound by multiscale analysis. Gives: a model of a rigorous limit argument that decides what the limit *is* (non-trivial or not), the template for
  P6.2; the triviality unit test of the blueprint.
- Duminil-Copin, Kozlowski, Krachun, Manolescu, Oulamara, "Rotational invariance in critical planar lattice models", arXiv:2012.11672.
  https://arxiv.org/abs/2012.11672. Verified: yes (abstract). Rotational symmetry of large-scale correlations in 2D random-cluster models with
  cluster weight in [1,4] and in critical Potts models with 2, 3, 4 colours. The model of how rotational invariance is proved in a lattice limit.
  Planar statistical models, not gauge theory.
- **Rotation-invariance restoration in 4D lattice gauge limits:** I found no rigorous result in the literature search apart from the claim, in the
  OpenAI README, of Poincare covariance of the limit (section 2.4); Symanzik-type arguments are perturbative.

## 7. Gradient flow

- Luescher, "Properties and uses of the Wilson flow in lattice QCD", JHEP 08 (2010) 071 (erratum JHEP 03 (2014) 092), arXiv:1006.4518.
  https://arxiv.org/abs/1006.4518. Verified: yes (record). Defines the flow and the scale t_0 from <t^2 E(t)>; the flow smooths gauge fields and
  needs no renormalisation of flowed observables (recalled).
- Luescher, Weisz, "Perturbative analysis of the gradient flow in non-abelian gauge theories", JHEP 02 (2011) 051, arXiv:1101.0963.
  https://arxiv.org/abs/1101.0963. Verified: yes (record). The perturbative expansion and the flow coupling at one loop.
- Luescher, "Step scaling and the Yang-Mills gradient flow", JHEP 06 (2014) 105, arXiv:1404.5930. https://arxiv.org/abs/1404.5930.
  Verified: yes (record). The gradient flow coupling as a non-perturbative running coupling and its step scaling (recalled).
- Fodor, Holland, Kuti, Nogradi, Wong, "The Yang-Mills gradient flow in finite volume", JHEP 11 (2012) 007, arXiv:1208.1051.
  https://arxiv.org/abs/1208.1051. Verified: yes (record).
- Ramos, "The gradient flow in a twisted box", PoS LATTICE2013 (2014) 053, arXiv:1308.4558. https://arxiv.org/abs/1308.4558. Verified: yes (record).
- Ramos, "The gradient flow running coupling with twisted boundary conditions", JHEP 11 (2014) 101, arXiv:1409.1445. https://arxiv.org/abs/1409.1445.
  Verified: yes (record). A non-perturbative coupling defined in a twisted box, which is the setting of the act number.
- Dasilva Golan, Garcia Perez, Ramos, "The SU(N) running coupling in the twisted gradient flow scheme and volume independence", PoS LATTICE2021
  (2022) 310, arXiv:2111.13092. https://arxiv.org/abs/2111.13092. Verified: yes (record).
- Dalla Brida and others: not looked up. For the project's gradient-flow candidate 2 (scout) the pieces above are the basis; I did not look for any
  rigorous (existence or monotonicity) statement about the flow coupling. Verified: no for any such statement.

## 8. P5.1 in one place: what exists

Searches run for "electric flux energy mass gap relation", "twist free energy mass gap", "'t Hooft loop and spectral gap", and "reflection
positivity twisted boundary conditions free energy mass gap". Result, in order of how much they give:

1. **Kanazawa (0808.3442) and Tomboulis-Yaffe (1985)**: rigorous reflection-positivity inequalities from the twist-insensitivity of a box to the
   decay of a gauge-invariant correlation (with the restrictions listed in section 4.1). The twist insensitivity needed is
   "1 - <F> small", i.e. the vortex (magnetic) free energy F_m tending to zero. Kanazawa's version removes the requirement that the twist be
   central. I did not find a paper that says what to do about the vacuum-sector spectral gap beyond the correlator decay.
2. **Chatterjee (2006.16229)**: the converse direction: exponential decay for arbitrary boundary conditions implies unbroken centre symmetry,
   which implies confinement.
3. **Koller-van Baal (1986)**: a controlled small-volume expansion in which flux energy and glueball mass share the same tunnelling channel.
   Physics-level rigorous, only z < 1.
4. **Numerical**: de Forcrand-von Smekal (2002), Gonzalez-Arroyo-Martinez (1996), Bergner et al. (2025).
5. Nothing found of the form "growth of the electric flux energy E_e(L) L implies a gap of the vacuum sector" as a theorem.

The blueprint's own duality (P1.4: F_e = dual(F_m), exact) is the missing link to item 1 on paper, because "E_e L large" (our z growth) says the
non-trivial electric flux partition function is small, which by duality says F_m is small, which is the input Kanazawa needs. Two things
are between that and a proof, and they are the real content of P5.1 (my reading, not a literature claim): (a) E_e is a T -> infinity energy while the
inequality is a finite-box statement with T of the order of L, so the order-of-limits step B3 reappears (the finite-T trace carries a count of
excited states that the spectral gap in the flux sector does not control); (b) the exponent counting above (1 - <F> must decay like e^{-mL}).
These are worth a precise check by a worker who reads the proof of Theorem 2 of Kanazawa.

## 9. Possible clicks

Each is a lead, not a claim, in the spirit of "sniff out what seems related and see what clicks".

- **C1 (P5.1). Three statements that look like the same structure seen three times.** (i) Kanazawa/Tomboulis-Yaffe: insensitivity of a box to a
  twist (a particular boundary condition) gives decay of correlations. (ii) Dobrushin-Shlosman complete analyticity: insensitivity of finite
  regions to *all* boundary conditions is equivalent to exponential decay. (iii) The project's D' and P2.3: uniform conditional laws of block
  observables, decay from uniqueness. A twist is one special boundary condition; the question is whether the twist alone is enough, i.e.
  whether centre-twist insensitivity implies insensitivity to the other boundary conditions (a reflection-positivity analogue of the
  "weak mixing to strong mixing" step in the Ising case; Martinelli-Olivieri). If it does, P5.1 becomes a statement inside the P2 machinery.
- **C2 (P5.1, P4.1). Chatterjee's hypothesis is our hypothesis.** "Correlations decay exponentially under arbitrary boundary conditions" is, in
  words, D' (and our GDS for block observables). Chatterjee's theorem then reads: our P2.3 conclusion implies unbroken centre symmetry and
  confinement. Together with C1 the picture is a loop: gap (in his sense) implies confinement (Chatterjee), insensitivity to the twist implies
  the gap (Kanazawa), growth of z is insensitivity to the twist via duality (P1.4). Whether the loop closes is exactly what is open.
- **C3 (P4.4, P6.6). One box, three couplings.** The twisted box carries the act number z(L), the twisted gradient-flow coupling g^2_TGF(L)
  (Ramos), and the twisted-Polyakov-loop coupling (de Divitiis et al.). A z(L) measured against g^2_TGF(L) removes the need to define the
  line of constant physics separately: both are functions of the same L and the same box. The volume-independence result of
  Dasilva Golan-Garcia Perez-Ramos is the Eguchi-Kawai-type statement that the twisted box coupling is a function of L only.
- **C4 (P4.7, P1.5). Tomboulis's decimation is our decimation.** Tomboulis carries Z_-/Z through decimations with interpolation parameters; the
  project proves the flux partition functions pass through decimation unchanged (`act_conserved_per_layer`). Ito-Seiler's gap (the matching
  condition alpha = alpha+) and Kanazawa's coupling discrepancy are the same obstruction as the project's one-sided step (compare blocked
  measure and original on the same box) and assumption (U). Three groups hit the same step from different sides; a formulation that proves it
  in one language proves it in all three.
- **C5 (P4.6, P4.2). z(L) as a conformality gauge.** In a scale-invariant theory on T^3 x R every energy scales as 1/L, so z = E_e L is constant,
  as the free photon shows exactly; z unbounded is scale-dependent behaviour. The dichotomy of DKST/LPR (a scale-invariant 4D unitary theory is
  conformal, endpoints of flows are CFTs) then reads in the twisted box as z -> const or z -> infinity, giving a concrete observable for the
  "gapped or scale-invariant" statement. The Banks-Zaks unit test is z -> const.
- **C6 (P3, P4.4). Blocking as gradient flow.** The OpenAI blocking is a stochastic kernel with heat-kernel-like noise; Luescher's flow smooths with
  the (deterministic) Yang-Mills heat flow; Chandra-Chevyrev-Hairer-Shen use the same flow in their stochastic quantisation and Cao-Chatterjee
  use it to define a state space. Flow time t corresponds to block size about sqrt(t). A flow-time version of "blocked theory at L1" would let
  the project's P1.5 (act conserved per layer) be read as a statement about the flow.
- **C7 (P3.1, P3.4). Small-field / large-field is one structure in four places.** Balaban's R operation (large-field regions with
  Gaussian cost), Dimock II's large-field cubes, the OpenAI `Healthy` mask with E (smooth) and K (sup-only) activities, and the project's P3.1
  large-field lower bound. Reading them against each other should say which direction of bound each gives and where a lower bound on the large-field
  activity (the gap in Stage A of `H1-OPENAI.md`) is missing in all of them.
- **C8 (P4.4, P4.2). Fractional instantons as the common mechanism.** Koller-van Baal (same tunnelling channel for flux energy and glueball mass
  for z < 1), Tanizaki-Uensal and Hayashi-Tanizaki-Uensal (centre-vortex semiclassics at small T^2), and Bergner-Gonzalez-Arroyo-Soler
  (gas of vortex-like fractional instantons growing with torus size) look like the same object in three regimes, with the project's (B1)-(B2)
  as the common estimate. If that is so, B2's prefactor may already be computable in the Tanizaki-Uensal setting (small T^2, controlled),
  with the transfer to T^3 x R as the extra step.
- **C9 (P6.2, P4.6). Triviality and asymptotic freedom as the two signs of one log.** Aizenman-Duminil-Copin's logarithmic improvement of the
  tree bound for phi^4_4 and asymptotic freedom of Yang-Mills are both a one-loop beta-function statement with opposite sign; the multiscale
  random-current method is a rigorous version of the sign for phi^4_4. A parallel for Yang-Mills would be a rigorous version of the other sign
  (non-trivial limit), which is what P6.2 needs.
- **C10 (P6.3-P6.4). OpenAI covers the axioms it was asked for.** If the `reconstruction` property holds as the README states it, P6.3 to P6.5 may
  be closed for their limit, and the open point moves to identifying their limit with ours (P6.6). This is an observation about a statement I
  could only read at README level, so a worker should check `Hierarchy.Properties` in the Lean source first.
- **C11 (P5.1). Anishetty-Sreeraj (2018) electric-loop gap.** Their dual description of (2+1)-dimensional SU(2) lattice gauge theory as
  interacting closed electric loops with Schwinger bosons obtains a mass gap in the weak coupling limit (Phys. Rev. D 97, 074511,
  arXiv:1802.06198; verified: yes (abstract)). A flux-line picture of the vacuum gap is the same kind of object as a flux-sector energy; read it for
  how a flux-sector quantity becomes a vacuum quantity. 2+1 dimensions only; physics-level.

## 10. Unverified items and corrections, in one list

- Not verified: Dobrushin-Shlosman (1985, 1987 page details); Martinelli-Olivieri (1994); Simon (1984) and Helffer-Sjoestrand (1984);
  Anber-Poppitz; the content of the OpenAI assessment PDF (file exists); any rigorous gradient-flow existence result; Adhikari-Cao "strong
  coupling" (only the weak-coupling paper exists in my searches).
- Content not read, only record or abstract: all Balaban, Federbush, Magnen-Rivasseau-Seneor papers; Dimock's papers (abstract only); Tomboulis
  (abstract only); Kanazawa 0808.3442 (about half of the text).
- Corrections: `r4-actnumber/NOTE.md` row "how the string tension is built up | hep-lat/9507001": the title of hep-lat/9507001 is "Investigating
  Yang-Mills theory and confinement as a function of the spatial volume" (that title belongs to hep-lat/9312066). `r3-monotone/NOTE.md` lists
  Borgs-Seiler (1983) and Yaffe (1980) as "recalled"; both are now verified records above. Dymarsky-Komargodski-Schwimmer-Theisen was posted
  in 2013 (arXiv:1309.2921) and published in JHEP 2015.
- Excluded: arXiv:2605.02156 (withdrawn); arXiv:2606.19362 (unvetted claim, abstract only).
