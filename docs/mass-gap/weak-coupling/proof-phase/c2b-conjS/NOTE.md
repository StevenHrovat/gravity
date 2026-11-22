# Cycle 2, workstream B: Conjecture S, the sector transfer for simple groups (2026-11-22)

Brief: the owner's reading after cycle 1 (`../../PREP.md`, last two sections): every neutral excitation of pure Yang–Mills with a simple
group is built from closed flux (Giles), so flux confinement (an area law, or a growing act number) should imply the mass gap; and
"switching the dimensions" is Euclidean rotation ('t Hooft duality proper, `tHooft_rotation`). Tasks: literature, a precise statement
with the unit tests built in, the proof attempt as far as it goes with the exact obstruction, Lean for what is proved.

Lean: `../../../formal/ProofPhase/SectorS/{GeneratorRate,Loops,Mixture,ConjS}.lean`, built in `~/formal-c2b` (Lean 4.34.0, Mathlib
v4.34.0) with `build.sh <module>`; `axioms.sh` builds all four, greps for `sorry`/`native_decide`/`axiom` (none) and prints the axioms of
22 headline theorems: all `propext, Classical.choice, Quot.sound`. No numerics were run. Nothing outside this folder and
`formal/ProofPhase/SectorS/` was edited.

Claim levels: **Lean**, **Lean (definitional)**, **paper** (complete argument here), **standard** (textbook or classical literature,
cited, not re-read), **read** (checked in the source this session), **numerical** (others' data), **open**, **heuristic**.

---

## 0. Result in plain words

1. **Literature (section 1).** "Area law implies mass gap" is **not a known theorem** in any lattice gauge theory, and nobody claims it.
   The proved implication runs the other way (Chatterjee 2021: decay for all boundary conditions + unbroken centre ⇒ area law). Where
   both properties are known (strong coupling, 2D, 3D Z₂ through duality, 3D U(1)), they come from separate proofs. There is a
   **numerical counterexample with a simple group and no matter**: SU(3) with a fundamental–adjoint action, at the endpoint of its bulk
   transition line the string tension stays finite (√σ ≈ 0.47 in lattice units) while the 0⁺⁺ glueball mass goes to zero (Heller 1995,
   read). So Conjecture S cannot be a theorem about "a simple group" alone; it needs the Wilson action, or at least the continuum limit
   along the line of constant physics.
2. **Conjecture S, stated (section 2, Lean definitions):** `AreaLaw T` (one physical string tension, uniform in volume and spacing, all
   planes) and `ConjectureS T := AreaLaw T → MassGap T` on the assembly's objects (SU(2) Wilson along a tuning). The act-number version
   is the assembly's existing `SectorTransfer`.
3. **The first half of the owner's reading is right and is now precise (section 3).** "Every neutral excitation is built from closed
   flux": for SU(2) the linear span of single Wilson loops is already an algebra (Lean, from the Mandelstam identity
   `tr A tr B = tr AB + tr AB⁻¹`), and it is dense in the gauge-invariant observables (paper, standard). And the gap is decided on any
   generating set by rates alone: if every generator decays at rate `m` with its own constant, every vector in the closed span decays at
   rate `m` with no prefactor (Lean, `norm_pow_le_of_generators`).
4. **The second half, "and pays the flux cost", is where it breaks, and the break is exact (section 4).** The generators can be taken
   to be loops built from **at most three plaquettes** of flux (SU(2), Sibirskii's theorem on 2×2 matrix invariants), and the area law
   says nothing about loops of bounded size: in Lean, `AreaLaw` is equivalent to its restriction to loops of physical area at least any
   `A₀` (`areaLaw_iff_large`). So the hypothesis is silent on a generating set, and the conclusion is decided on that set. The neutral
   sector is built from flux, but from **small** flux, and small flux does not pay the confinement price. Two independent witnesses that
   no argument can bridge this without Yang–Mills dynamics: a rigorous one (a reflection-positive, gauge- and Euclidean-invariant
   mixture of two SU(2) states has an area law and no gap; the algebra in Lean, `not_expDecay_mix`) and a numerical one (the
   fundamental–adjoint endpoint: a single local action, confining, with a massless 0⁺⁺).
5. **The dimension swap explains the break instead of closing it (section 4.4).** Rotating a spatial closed loop into the time direction
   turns it into an open flux line between two static charges: the area law **is** the energy `V(R) ≥ σR` of a Gauss-charged sector.
   That is the same charged-versus-neutral wall workstream 2 found for twists. And the rotation puts the scale where the area law starts
   to say anything at `R ≳ 1/√σ ≈ 1/T_c`: below the deconfinement length the hypothesis is empty, which is exactly the window Route A's
   crossover (P4.1) has to cover.
6. **Verdict:** Conjecture S is open for the Wilson action and false (numerically) for general simple-group actions; no route from the
   area law to the gap exists that does not pass through a two-point (decay) statement at the crossover scale, i.e. through Route A.
   What this workstream adds to Route A is the generator reduction: the gap needs decay only on generators and only as a rate.

---

## 1. Literature (task 1)

| item | what it says | level |
|---|---|---|
| Chatterjee, "A probabilistic mechanism for quark confinement", CMP 385 (2021) 1007, arXiv:2006.16229 | compact connected group with non-trivial centre: exponential decay **under arbitrary boundary conditions** ("strong mass gap") ⇒ unbroken centre ⇒ area law. Stresses that the usual gap (one boundary condition) is weaker and does not by itself give confinement. Direction gap ⇒ confinement, the converse of Conjecture S | read (ws2 read sections 2–3; abstract and summary this session) |
| Chatterjee, "Yang–Mills for probabilists", arXiv:1803.01950 | frames the area law (all couplings) and the gap as separate open problems | read (abstract/summary) |
| Osterwalder–Seiler, Annals Phys. 110 (1978) 440; Seiler, LNP 159 (1982) | strong coupling, any compact group: area law **and** gap, both from the cluster expansion (one expansion, two conclusions; neither derived from the other) | standard (record verified in `../READING.md`) |
| this project, `AreaLaw.Assembly.wilson_area_law(_rect)`, `AreaLaw.Concrete.wilson_clustering_explicit` | the same two strong-coupling facts in Lean, finite volume, uniform in the volume | Lean (existing) |
| 2D lattice gauge theory | area law at every coupling and independent plaquettes (infinite gap, free boundary) | standard |
| 3D Z₂ gauge theory ↔ 3D Ising (Wegner duality) | confined phase ↔ Ising ordered phase. Area law ↔ positive interface tension (Lebowitz–Pfister 1981, recalled); gap ↔ exponential decay of truncated correlations in the ordered phase, proved for all β > β_c by Duminil-Copin–Goswami–Raoufi, CMP 374 (2020) 891, arXiv:1808.00439 (read: abstract and summary). Both hold on the same region, by **independent** proofs. Remark in the same paper: the spin-flip-symmetric state has non-decaying truncated correlations, the mixture phenomenon of section 4.1 | read (DGR), recalled (duality dictionary for even observables, Lebowitz–Pfister) |
| Goepfert–Mack, CMP 82 (1982) 545 | 3D U(1) Villain: positive string tension at all couplings (read: record and a 2026 summary by Chatterjee, arXiv:2602.00436). That they also prove the photon mass (Polyakov) is my recollection, not verified | read (area law) / recalled (gap) |
| Heller, "More on SU(3) lattice gauge theory in the fundamental–adjoint plane", hep-lat/9509010, Nucl. Phys. B Proc. Suppl. 47 (1996) 262 | action `β_f Σ(1 − Re tr U/3) + β_a Σ(1 − |tr U|²/9)`; first-order bulk line ending at `(β_f, β_a) = (4.00(7), 2.06(8))` (from Blum et al., NPB 442 (1995) 301). Along the N_t = 4 thermal line towards the endpoint `√σ` stays ≈ 0.37–0.55 (lattice units; Table 1) while `m_{0⁺⁺}` falls to 0.20(4); fit `m_{0⁺⁺} = A(β_a* − β_a)^p`, `p` compatible with mean field 1/2; "at the critical endpoint at least one mass in the 0⁺⁺ channel has to vanish"; conjectured continuum limit there: trivial φ⁴. Phase diagram from Greensite–Lautrup PRL 47 (1981) 9 and Bhanot PLB 108B (1982) 337 | **read** (full text, 4 pages) |
| Lacagnina et al., arXiv:1212.0635 | SU(2) analogue: scalar mass decreases only slightly; order of the endpoint disputed | read in ws2 (conclusion) |
| Greensite–Matsuyama, PRD 96 (2017) 094510, arXiv:1708.08979 | with matter, area law, "C-confinement" and massive colour-singlet spectrum are inequivalent (gauge-Higgs) | read (abstract) |
| Giles, "Reconstruction of gauge potentials from Wilson loops", PRD 24 (1981) 2160 | Wilson loop variables subject to the Mandelstam constraints reconstruct the gauge potential (continuum, U(N)) | read (INSPIRE record/abstract) |
| Durhuus, "On the structure of gauge invariant classical observables in lattice gauge theories", Lett. Math. Phys. 4 (1980) 515 | the lattice version (title and keywords verified on a catalogue; content and page numbers recalled, **not verified**) | record only |
| Procesi, Adv. Math. 19 (1976) 306 (announced Bull. AMS 82 (1976) 891); Sibirskii (1968) | invariants of tuples of n×n matrices under simultaneous conjugation are generated by traces of words; for 2×2: by `tr Xᵢ`, `tr XᵢXⱼ` (i ≤ j), `tr XᵢXⱼXₖ` (i < j < k) | read (Bull. AMS record; Sibirskii's statement as quoted by Drensky–Sadikova, arXiv:math/0503146) |
| Fredenhagen–Marcu (1983, 1986) | charged-state confinement criteria with matter; nothing on the gap | standard |
| Kanazawa, Tomboulis–Yaffe, 't Hooft | twist/flux ⇒ charged-sector decay only | ws2 (read) |

**Verdict.** Open as a theorem for every model where it is not trivially true; no source states or proves "area law ⇒ gap", and every
case where both hold has two separate proofs. Refuted, at the numerical level, for pure gauge theory with a simple group once the action
is allowed to vary (Heller's endpoint). Rigorous counterexamples exist only outside the class: non-simple groups (ws2's SU(2) × U(1)),
non-extremal states (section 4.1), matter (Banks–Zaks, adjoint QCD). I found no rigorous counterexample for a single local action of a
simple group, and no published heuristic argument that the implication should hold beyond "glueballs are closed strings".

---

## 2. Conjecture S, stated (task 2)

**Lean definitions** (`SectorS/ConjS.lean`), on the assembly's objects (SU(2) Wilson measure `T.ym k j` on the torus of side `2(j+1)ℓ_k`,
spacing `a_k = L₁/ℓ_k`):

```
rectW T k j μ ν R R' = ∫ W_{R×R'}(origin, plane μν) d(T.ym k j)
physArea T k R R'   = (R a_k)(R' a_k)
AreaLaw T  := ∃ σ > 0, ∃ C, ∃ k₀, ∀ k ≥ k₀, ∀ μ ≠ ν, ∀ R R', ∀ limit point h (j → ∞) of rectW T k j μ ν R R',
                |h| ≤ C · exp(−σ · physArea T k R R')
ConjectureS T := AreaLaw T → MassGap T
```

Uniform in volume (limit points as `j → ∞`) and in spacing (one `σ`, one `C` for all `k ≥ k₀`), physical area, every plane (so the
spatial and the temporal loops, the two readings of section 4.4). The act-number form `FluxGrowth T → MassGap T` is
`ProofPhase.SectorTransfer` (unchanged). Both are statements, not results.

**The conjecture with its scope built in (paper).** *For the Wilson action of a compact simple group G, without matter, along a line of
constant physics: if the area law holds uniformly in volume and spacing, the continuum limit has a mass gap.* The scope clauses are each
forced by a unit test:

| clause | forced by |
|---|---|
| simple group | SU(2) × U(1): SU(2) area law, photon (ws2 2.3, rigorous by citation) |
| no matter | Banks–Zaks / adjoint QCD (centre intact, area law, gapless); fundamental matter breaks the area law anyway |
| a single local action, extremal (Gibbs) state | the mixture (section 4.1): RP, invariant, area law, no gap; rigorous |
| the Wilson action / continuum limit, not "any action" | the fundamental–adjoint endpoint (section 1): local, simple, pure, confining, massless 0⁺⁺; numerical |
| uniform in volume and spacing | finite-volume statements are vacuous (finite boxes always have a gap) |

The other direction is not claimed: deconfined Z₂ (and 3D/4D gauge theories at high temperature) have a gap without area law, which is
consistent with S. Finite subgroups of SU(2) are not simple Lie groups; the Lean results below are blind to the difference (section 6).

---

## 3. The proof attempt, step (i): generation (task 3)

### 3.1 The gap is decided on generators, by rates only (Lean, `GeneratorRate.lean`)

Setting: a real inner product space `E` and a symmetric bounded operator `T` (`⟨Tx, y⟩ = ⟨x, Ty⟩`). No positivity, no completeness,
no spectral theorem.

* `sq_le_mul_pow_two_mul`: `‖Tⁿx‖² ≤ ‖x‖ ‖T²ⁿx‖` (symmetry + Cauchy–Schwarz: the Hankel inequality).
* `le_of_doubling`: a sequence `a ≥ 0` with `a(k)² ≤ a(0)a(2k)` and `a(k) ≤ C e^{−mk}` for **some** `C` has `a(n) ≤ a(0)e^{−mn}`.
  Proof: `b = a/a(0)` has `b(n)^{2^j} ≤ b(2^j n)`, so `(b(n)e^{mn})^{2^j}` stays below `C/a(0)` for all `j`, which forces
  `b(n)e^{mn} ≤ 1`.
* **`norm_pow_le_of_generators`**: if every `s ∈ S` has `‖Tᵏs‖ ≤ C_s e^{−mk}`, then every `v` in the closure of `span S` has
  `‖Tⁿv‖ ≤ e^{−mn}‖v‖`. (The decaying vectors form a submodule; the doubling lemma removes the constant; the bound is closed.)
* `inner_pow_le_of_generators`: `|⟨w, Tⁿv⟩| ≤ e^{−mn}‖w‖‖v‖`; `generators_of_uniform`: the converse (trivial).

**Reading.** In the OS Hilbert space of a limit theory (`T` the one-step transfer matrix, `E = Ω^⊥`), take `S` = the centred Wilson-loop
vectors. Then **`MassGap` with rate `m` ⟺ each single loop's connected autocorrelation decays at rate `m`, with any loop-dependent
constant** (paper, given OS reconstruction of the limit, standard, and 3.2's density). This is the rigorous form of "the neutral sector
is built from loops, so it suffices to look at loops". It is also new content for P5.3 ("one rate for all truncated correlations"):
one rate per generator suffices; uniform constants come free. It is the operator form of Theorem C (`corr_le_of_decay`).

### 3.2 Loops generate (Lean for the algebra, paper for density; `Loops.lean`)

* `su2_mandelstam` (**Lean**): `Re tr A · Re tr B = Re tr(AB) + Re tr(AB⁻¹)` on SU(2), via `B + adj B = (tr B)·1` and `B⁻¹ = B* = adj B`.
* `wilsonLoop_mul` (**Lean**): `W_p W_q = W_{pq} + W_{p q̄}` (`pathRev`, `pathHol_rev`); `wilsonLoop_double`: `W_{pp} = W_p² − 2`;
  `wilsonLoop_lasso`: a loop at `y` reached by a path `c` from `x` equals the loop `c q c̄` at `x`.
* **`loopAlgebra x`** (**Lean**): the linear span of the Wilson loops based at `x` contains `1` and is closed under products, so it is a
  subalgebra; `gauge_of_mem_loopAlgebra`: all its elements are gauge invariant. For SU(2), *no products of loops are ever needed*.
* **Density (paper, standard).** On a connected lattice region, fix a base point and a maximal tree; gauge-invariant functions are
  functions of the tuple of fundamental-cycle holonomies modulo simultaneous SU(2) conjugation. Two tuples with equal traces of all
  words define two unitary representations of a free group with equal characters, hence equivalent, hence (unitary) conjugate by U(2),
  hence by SU(2). So loop traces separate the orbit space; it is compact; by Stone–Weierstrass `loopAlgebra` is uniformly dense in the
  continuous gauge-invariant functions, hence dense in L² and in the OS space (whose norm is bounded by the sup norm). Not formalised.

### 3.3 Small flux already generates (paper, standard inputs)

In a box (simply connected as a plaquette complex), every closed walk at the root is a product of **lassos** `t P t⁻¹` (tree path `t`,
plaquette `P`) and their inverses (the plaquettes normally generate the free group of cycles; discrete non-abelian Stokes). So every
gauge-invariant function of the box is a conjugation-invariant function of the lasso tuple `(L₁, …, L_K)`. By Sibirskii's theorem
(section 1), the invariants of 2×2 tuples are generated by `tr Lᵢ`, `tr LᵢLⱼ`, `tr LᵢLⱼLₖ` (inverses are not needed: `L⁻¹ = (tr L)·1 − L`).
Each of these is a Wilson loop whose holonomy is a product of **at most three** conjugated plaquettes ("three-plaquette loops"; their
paths can be long, their flux content is three plaquettes). With the density argument of 3.2: **every gauge-invariant local observable
of SU(2) lattice gauge theory is a uniform limit of polynomials in three-plaquette Wilson loops.** (For SU(N) the same holds with words
of bounded length, Razmyslov–Procesi bound `N²`.)

---

## 4. Step (ii) and where it breaks (task 3): the exact obstruction

The natural line: (ii) a closed loop of extent R costs at least σ·(something) by the area law, via RP and the transfer matrix; (iii)
small loops need something else. Result: (ii) fails as stated for **every** loop, and (iii) is all there is.

### 4.1 A one-point hypothesis cannot give a two-point conclusion (rigorous; algebra in Lean, `Mixture.lean`)

The area law bounds **expectations of single loops** (one-point functions). The gap is a property of **connected two-point functions**.
Mixtures separate the two:

* Lean: `abs_integral_mix_le` (expectation bounds survive mixing), `integral_mix_nonneg` (reflection positivity survives), `cov_mix`
  (`Cov_mix = ½Cov₁ + ½Cov₂ + ¼ΔfΔg`), **`not_expDecay_mix`**: if both components cluster and an observable has different expectations in
  them, the mixture admits no bound `C e^{−mn}`, `m > 0`.
* Instance (paper; inputs cited): `μ₁` = SU(2) Haar measure (β = 0; every non-trivial loop has expectation 0, so it has an area law with
  any σ; independent plaquettes), `μ₂` = the infinite-volume SU(2) Wilson measure at small β > 0 (Osterwalder–Seiler: area law, gap; the
  plaquette has `⟨W_p⟩ = β + O(β²) > 0` by the strong-coupling expansion (the slope at β = 0 is `∫(tr U)² dU = 1`), and Haar gives 0). The mixture is reflection positive, gauge,
  translation and rotation invariant, has an area law, and its plaquette autocorrelation tends to `⟨W_p⟩₂²/4 > 0`: **no gap**.

So no argument that uses only RP, symmetries and the area law can reach the gap: it must use that the state is the extremal Gibbs state
of one local action. And even that is not enough (4.2).

### 4.2 Even one local action of a simple group is not enough (numerical, read)

Heller's endpoint (section 1): a pure SU(3) gauge theory with a local, reflection-positive (fundamental plus adjoint) action, extremal
and confining (`√σ ≈ 0.47` in lattice units), whose 0⁺⁺ correlation length diverges. The large-flux sector is confined; the smallest
closed flux (the plaquette, 0⁺⁺ channel) becomes free. This is the owner's distinction turned around: the light excitation **is** built
from flux, but from the smallest flux, and that flux is not the confined one. Conjecture S must therefore use the Wilson action (or the
continuum limit along the line of constant physics, where the endpoint's influence disappears).

### 4.3 The exact obstruction (Lean + paper)

* **What the hypothesis sees.** `areaLaw_iff_large` (**Lean**): for every `A₀`, `AreaLaw T ⟺ AreaLawFrom T A₀` (the same bound for loops
  of physical area `≥ A₀` only). Proof: `|W| ≤ 2` under a probability measure, and `2 ≤ 2e^{σA₀}e^{−σA}` when `A ≤ A₀`. The area law is a
  statement about large loops only.
* **What the conclusion needs.** By 3.1 and 3.3 the gap is decided by the decay **rates** of polynomials in three-plaquette loops.
* **The gap between them.** The hypothesis is silent on a generating set, and the conclusion is decided on it. Moreover what the area law
  could at best control for large loops is a **weight** (how much of a large loop's state lies at low energy, heuristically `≲ e^{−σA}`,
  which is what happens in the mixture: the second vacuum appears in a large loop with weight `⟨W⟩₂²/4 ≤ C²e^{−2σA}`), never a **rate**:
  a vector with a tiny weight at a low energy still has that low energy as its rate, and 3.1 needs rates. So step (ii) fails even for the
  largest loops, as a matter of kind (weight versus rate), and step (iii) is the whole problem.

In the owner's words: the neutral sector is built from closed flux (true, 3.2–3.3), but the pieces it is built from are the smallest
closed fluxes, and their cost is the glueball mass itself; the confinement cost σ·area is charged only on large pieces, which are not
needed. "How existence is built" is right; "what it costs" is decided at the bottom of the scale, not by the confinement of large loops.

### 4.4 The dimension swap: what it does (paper, standard steps)

* **Rotation.** On the symmetric torus the lattice rotation `(0 2)(1 3)` (the map behind `tHooft_rotation`) maps a spatial `R × R'` loop
  to a temporal one, and the Wilson measure is invariant: `rectW` is the same in every plane (standard; the Lean bookkeeping of
  `Duality.lean` would carry it, not done here). That is why `AreaLaw` quantifies over all planes at no extra cost.
* **A closed loop in space is an open string in time.** For a temporal `R × t` loop the transfer matrix gives
  `⟨W⟩ = Σ_k |c_k(R)|² e^{−t E_k(R)}` over the states of the sector with a static quark at 0 and an antiquark at `R` (Gauss law modified at
  two sites: a **charged** sector). So the area law in the time reading is `V(R) ≥ σR − c`: linear energy of an open flux line between
  external charges. The area law, although stated with gauge-invariant observables, is a charged-sector statement; rotated, it meets the
  same wall as workstream 2's twists (charged ⇒ neutral has no inequality).
* **Where the hypothesis starts to bite.** A loop of physical size `R` has area-law suppression `e^{−σR²}`; at `R ≈ 1/T_c ≈ 1.4/√σ` this is
  `e^{−2}`, no information. The same rotation turns a box of side `L` into temperature `1/L`, deconfined below `L = 1/T_c`. So the
  dimension swap places the onset of the area law's content at the deconfinement length, and everything below it (where the generators
  of 3.3 live, at every lattice spacing) is out of its reach. That is precisely the window Route A must cover at `L₁`.
* **What it closes:** no step. It explains the obstruction (closed in space = charged in time) and fixes its scale (1/T_c).

### 4.5 A heuristic that survives (heuristic, not a claim)

A closed flux of size `r` costs about `σr` when large (confinement) and about `c/r` when small (asymptotic freedom: a short-distance
excitation carries momentum `~1/r`); the minimum `~2√(cσ)` is the glueball scale. The photon has no `σr` branch (no area law), the product
theory's U(1) payload has no `σr` branch either, and the fundamental–adjoint endpoint breaks the `c/r` branch at the lattice scale. The
gap needs both branches **and the gluing at the crossover `r ~ L₁`**, where neither branch is controlled: the inward reach (P3, the tie
to G0) and the outward reach (P4.2, confinement) meet at P4.1. In this picture Conjecture S is "outward reach ⇒ gap" with the inward
branch and the gluing silently assumed; the assumed parts are the hard parts.

---

## 5. Headline theorems (exact statements in the Lean files; marks)

| theorem | statement (short) | mark | Yang–Mills inside? |
|---|---|---|---|
| `le_of_doubling` | `a(k)² ≤ a(0)a(2k)`, `a ≤ Ce^{−mk}` ⇒ `a(n) ≤ a(0)e^{−mn}` | Lean, real analysis | no |
| `norm_pow_le_of_decay` | one vector: prefactor removed, `‖Tⁿx‖ ≤ e^{−mn}‖x‖` | Lean, any symmetric operator | no |
| **`norm_pow_le_of_generators`**, `inner_pow_le_of_generators` | rate `m` on generators (any constants) ⇒ `‖Tⁿv‖ ≤ e^{−mn}‖v‖` on the closed span | Lean, substantive (abstract); group-blind | no (use: OS space, paper) |
| `generators_of_uniform` | converse | Lean (definitional) | no |
| `su2_mandelstam` | `Re tr A Re tr B = Re tr AB + Re tr AB⁻¹` on SU(2) | Lean, substantive but elementary; SU(2)/SL(2)-specific, holds on finite subgroups | SU(2) |
| `wilsonLoop_mul`, `wilsonLoop_double`, `wilsonLoop_lasso`, `pathHol_rev`, `pathChain_rev` | loop products as sums of loops; lassos; reversal | Lean, elementary | SU(2) lattice loops |
| **`loopAlgebra`**, `mul_mem_loopSpan`, `gauge_of_mem_loopAlgebra` | span of SU(2) loops at a site is a gauge-invariant subalgebra | Lean, substantive but elementary | SU(2), any lattice `(ℤ/N)^d` |
| density of `loopAlgebra`; three-plaquette generation | uniform density in gauge-invariant functions; generation by three-plaquette loops | paper, standard inputs (character theory, Stone–Weierstrass, Sibirskii) | SU(2) |
| `abs_integral_mix_le`, `integral_mix_nonneg`, `cov_mix` | bounds and positivity survive mixing; covariance of a mixture | Lean (definitional, linearity) | no |
| **`tendsto_cov_mix`, `not_expDecay_mix`** | mixtures of clustering states with different expectations do not cluster | Lean, elementary | no (instance: paper with cited OS) |
| `abs_rectW_le` | `|⟨W_{R×R'}⟩| ≤ 2` under the Wilson measure | Lean | SU(2) Wilson |
| **`areaLaw_iff_large`** | `AreaLaw T ⟺ AreaLawFrom T A₀` for every `A₀` | Lean, substantive but elementary | SU(2) Wilson, along a tuning |
| `conjectureS_of_slabDecay` | `OnLCP T → SlabDecay T → ConjectureS T` | Lean (definitional) | via the assembly |
| `conjectureS_of_massGap` | `MassGap T → ConjectureS T ∧ SectorTransfer T` | Lean (definitional) | via the assembly |
| `AreaLaw`, `AreaLawFrom`, `ConjectureS` | the statements | definitions | SU(2) Wilson |
| mixture no-go (4.1) | no implication "area law ⇒ gap" for RP gauge-invariant SU(2) measures | paper, rigorous given Osterwalder–Seiler | — |
| endpoint (4.2) | a confining simple-group pure gauge action with massless 0⁺⁺ | numerical (Heller, read) | SU(3), fundamental–adjoint |

None of the Lean results is a step towards `MassGap` by itself; the substantive ones are the generator reduction (3.1, useful for any
route) and the precise form of the obstruction (`areaLaw_iff_large` with 3.3).

---

## 6. Unit tests

| test | what happens | verdict |
|---|---|---|
| photon (U(1) weak) | no area law (Coulomb), so `AreaLaw` fails: S is silent. `GeneratorRate` holds for U(1) with `m = 0` and claims nothing more. Mandelstam is not used for U(1) (abelian: `W_pW_q = W_{pq}` already) | pass |
| Z₂ (weak, 4D) | gap without area law: the other direction, consistent; S claims nothing | pass |
| Z₂ (3D, confined) | area law and gap both hold, by independent proofs (duality, DGR); consistent with S, gives no mechanism | pass (consistency) |
| SU(2) × U(1) | SU(2) area law, no gap: excluded by "simple"; not representable on the SU(2)-only Lean objects | pass |
| finite subgroups (Q8, 2T, 2O, 2I, order-12 binary dihedral) | Mandelstam and `loopAlgebra` hold verbatim (subsets of SU(2)); `GeneratorRate`, `Mixture`, `areaLaw_iff_large` are group-blind. No result here separates them from SU(2); said so. At weak coupling they have a gap and no area law (S silent) | pass, nothing separating |
| deconfinement (`L < 1/T_c`) | `AreaLaw` is an infinite-volume, zero-temperature statement; section 4.4 shows it is empty below `1/T_c`, which is the test's content | pass |
| triviality (φ⁴₄) | no existence claim; the endpoint's continuum limit (conjecturally trivial φ⁴) is a reason the Wilson action is needed, not a claim | pass |
| Banks–Zaks | fundamental matter: perimeter law, `AreaLaw` fails; adjoint matter keeps the area law and is gapless: excluded by "no matter" | pass |
| mixtures / first-order points | `MassGap` quantifies over every limit point, so a periodic limit at a first-order bulk point (e.g. SU(N ≥ 5) Wilson, numerically) would fail it at that `β`; along a line of constant physics only `k → ∞` matters | noted |
| "−1 is a commutator" | not used | — |

---

## 7. Blueprint changes (proposed; `PROOF-BLUEPRINT.md` not edited)

* **P5.1**: add "Conjecture S (area-law form): stated in Lean (`SectorS/ConjS.lean`: `AreaLaw`, `ConjectureS`). Not proved. Obstruction
  exact: the area law is silent on loops of bounded area (`areaLaw_iff_large`, Lean) while three-plaquette loops generate the neutral
  sector (paper, Sibirskii); a mixture no-go (Lean core) and the fundamental–adjoint endpoint (numerical, Heller 1995) show it needs
  Wilson-action dynamics. Lands on Route A (`conjectureS_of_slabDecay`)." Status stays **open**; recommendation as ws2: no independent
  route.
* **P5.3**: "one rate for all truncated correlations" → partly **Lean (abstract)**: one rate per generator, with any constants, gives one
  rate with prefactor `‖v‖` on the closed span (`norm_pow_le_of_generators`); with OS reconstruction (standard) and loop density (paper),
  `MassGap` ⟺ each Wilson loop decays at rate `m`. Uniqueness of the vacuum remains open (the mixture shows it is a real condition).
* **P1 (new line, structure)**: "SU(2) loop algebra: the span of Wilson loops at a site is a gauge-invariant subalgebra (Lean,
  `SectorS/Loops.lean`); density in gauge-invariant functions (paper, standard)".
* **Unit tests**: add the **mixture test** (any claimed "hypothesis ⇒ gap" whose hypothesis is a family of one-point bounds plus RP must
  fail for the Haar/strong-coupling mixture) and the **endpoint test** (a claim about "pure gauge theory with a simple group" must not
  apply to the SU(3) fundamental–adjoint endpoint, confining with a massless 0⁺⁺).
* **P1.4′ reading**: the rotation turns the spatial area law into the static potential (a Gauss-charged sector); recorded in 4.4.

---

## 8. Next step

Drop Conjecture S as a route of its own (its hypothesis cannot carry the conclusion, section 4) and keep its useful remainder for Route A:
the generator reduction. Concretely, the Lean target is an **OS version of `SlabDecay` with observable-dependent constants**: build, at a
fixed level, the RP pre-Hilbert space of the infinite-volume limit state with the one-step time shift as a symmetric contraction, apply
`norm_pow_le_of_generators`, and conclude `LatticeGap` from decay of each Wilson loop (or each block observable) with its own constant. That
weakens what P4.1 has to deliver (no uniform constant, only a rate per generator) and makes "Route A at L₁ for three-plaquette block
loops" a precise target. The physics content (a rate at the crossover scale) is untouched; the reduction only removes bookkeeping from it.

---

## Build

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2b-conjS/build.sh ProofPhase.SectorS.ConjS
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2b-conjS/axioms.sh
```

## Sources (this session)

Heller, hep-lat/9509010 (full PDF, read); arXiv abstract pages of hep-lat/9509010, hep-lat/0409067 (Hasenbusch–Necco; abstract only,
nothing on the endpoint), 1708.08979 (Greensite–Matsuyama), 2602.00436 (Chatterjee 2026, 3D central U(1)); search summaries for
Chatterjee 2006.16229 / 1803.01950, Giles PRD 24 (INSPIRE), Durhuus 1980 (catalogue entry), Procesi (Bull. AMS record) and Sibirskii (via
Drensky–Sadikova math/0503146), Duminil-Copin–Goswami–Raoufi 1808.00439, Goepfert–Mack (CMP 82, record). Not verified: Lebowitz–Pfister
1981, the gap half of Goepfert–Mack, Durhuus's content, the SU(N ≥ 5) bulk transition.
