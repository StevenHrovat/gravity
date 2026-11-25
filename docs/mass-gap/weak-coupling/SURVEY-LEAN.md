# Survey: existing Lean work on the weak-coupling / RG region of 4D lattice Yang-Mills

Date of survey: 2026-11-21. Reference material only; nothing is copied or reused. "Verified in code" means I cloned the repository
and scanned the sources (textual scan for `sorry`/`axiom`, reading the headline files); I did **not** build any of them. "README
claims" means I only read documentation. Line counts are my own `cat | wc -l` over `*.lean`.

**One-paragraph answer.** No Lean project formalises the intermediate-coupling "bridge", and none formalises Balaban's gauge-theory
RG. The only complete weak-coupling object is OpenAI's construction (a subsequential continuum limit at fixed physical volume, then a
subsequential infinite-volume limit; no gap). The only large formalisation of Balaban's *method* (`balaban-lean`) treats the O(N)
spin model, is unfinished, and has its two main theorems as `sorry`. The Eriksson programme carries the weak-coupling input as a
named hypothesis (`hRpoly`) and has not produced it. `lgt` has an abstract "scale transfer" lemma whose real content is two
hypotheses. Several other repositories claim more than their code shows.

## 1. `scottnarmstrong/balaban-lean`

- Licence Apache-2.0 (GitHub). Lean `v4.35.0-rc2`. Last commit 2026-10-22 (pushed 10-23). 3,715 `.lean` files, 1,087,586 lines
  (README: "about 1,088,000", 861,000 without comments).
- **Goal.** Balaban's low-temperature RG for the **classical O(N) spin model** on Z^d, d >= 3, N >= 2, hard spins, weak external field
  nu*h. This is *not* gauge theory. It follows Balaban's O(N) series (P1-P9: CMP 167 (1995) through Balaban-O'Carroll CMP 199
  (1999)) and uses his gauge-theory papers (1984-1989: propagators, small-field effective actions, cluster expansions, large-field
  R operation) as methodological ancestors (`docs/PAPERS.md`, keys E4-E10). Dimock's three expositions are used to check readings.
- **Headline statements (both frozen, both `sorry`, verified in code: exactly 2 `sorry` in the repo, in
  `Balaban/Frozen/Roots/LogPartitionMultiscale.lean:73` and `LowTemperatureCorrelations.lean:65`).**
  - Root-F `Balaban.logPartition_multiscale`: there is delta > 0 such that for every kappa > 0, c9 > 0 there are block size L, cube size
    M, threshold beta0 with, for beta >= beta0, every nu in (0,1], every unit h: `log(Z(g)/Z(0)) = <g,h> + sum_{j=1}^{k_f+1} sum_x sum_{X
    ∋ x} <g(x), T_j(x,X;g)>`, with T_j supported on connected polymers at scale j, depending only on g|X, analytic on the unit l1-ball,
    bounded by `c9 * L^{-j((d-2)/2+delta)} * exp(-kappa|X|/(M L^j)^d)`, and torus-independent when X does not wind.
  - Root-C `Balaban.lowTemperature_correlations`: Balaban-O'Carroll Theorem 1.1 (infinite-volume 1-/2-point functions, m(nu) = 1 +
    O(beta^{-1+rho1}), transverse/longitudinal decay `(1+|x|)^{-(d-2)} e^{-c' sqrt(nu)|x|}`).
- **Assumed vs proved.** README claims no axioms and no other `sorry`; verified: zero `axiom`/`opaque` declarations. Root-F is
  reduced by a complete Lean proof to seven intermediate results, **not yet proved**; `docs/BLOCKERS.md` lists seven "blockers", six open.
  Estimates: first renormalisation step about 21,000 lines still missing, blocker 3 about 9,000, blocker 4 5,000-7,500, blocker 5
  small-field half about 4,000 plus about fourteen large-field pieces, blockers 6-7 open at the last scale. Progress is tracked in
  `docs/PROGRESS.md`. A `frozen/manifest.json` plus `scripts/check_frozen_anchors.py` pins the statements; there is an `Inhabited/` folder
  (non-vacuity witnesses for definitions) and a `review/` folder with per-paper reviews and an `notes/ERRATA.md` of misprints/gaps.
- **Noteworthy honesty points (README).** In seven places the papers as printed do not supply what the next step needs (a step without
  reconstructible proof, or an estimate weaker than the one used later). One required estimate "in the form first stated is false" and
  the definitions were changed (with the author's approval) so that the statement was no longer needed. Several Lean transcriptions
  differed from the printed definitions and were corrected.
- **Relation to the bridge.** It covers the *weak-coupling* side of a spin model: smooth-field (Gaussian-like) region plus large-field
  polymer gas, scale by scale, down to a fixed cube size. It never reaches an intermediate-coupling or strong-coupling regime and has no
  gap statement. For YM it is a reference for the *architecture* (background field, localisation, fluctuation integral, large-field
  gas, torus independence), and a cost calibration: roughly one million lines and an unfinished state for the easier model. Its
  docs say the Yang-Mills first step ("item 17 addendum") and the Sussman-Alpoge account guided parts (below).

## 2. `lluiseriksson/THE-ERIKSSON-PROGRAMME`

- Licence AGPL-3.0. Lean `v4.29.0-rc6`. Last commit 2026-11-20. 503 `.lean` files, 181,119 lines (repo also holds many logs, papers,
  dashboards). The README and dashboard are written with heavy status language; read the scoping notes, not the badges.
- **Core (`YangMillsCore`).** README claims, and the CI description states, every headline `#print axioms` is
  `[propext, Classical.choice, Quot.sound]`. Verified by scan: no `axiom` outside `YangMills/Experimental/` (15 there: Lie generators,
  Dirichlet contraction, Hille-Yosida, variance decay, a log-Sobolev claim `sun_haar_satisfies_lsi`), and `YangMillsCore.lean` does not
  import it (one matching line, a comment). No code-level `sorry` found by textual scan (the 233 raw matches are doc comments "no
  sorry").
- **Proved (strong coupling only).** Volume-uniform Wilson-loop area law for SU(N_c), both linearised and exact activity
  (`normalized_wilson_loop_area_law`, `normalized_exp_wilson_loop_area_law`, `finite_volume_area_law_exp`), via a formalised
  volume-restricted cluster expansion (Kotecky-Preiss/Mayer engine in `YangMills/KP`), plus 2D results (Bessel-Amos). Windows are
  small and explicit.
- **The "mass-gap" assembly is not a gap statement.** The README itself corrects this (scope correction 2026-10-14):
  `lattice_mass_gap_of_exp_clustering_uniform` is a lemma about two arbitrary real sequences `covIR, covUV : N -> R` with
  `|covIR k| <= C1 e^{-eps k}`, `|covUV t| <= C2 e^{-c0 t}`; no gauge group, measure or Hamiltonian appears. "No transfer-matrix or
  Hamiltonian spectral gap for SU(N), not even on the lattice."
- **What the mass-gap branch is conditional on (verified in `YangMills/RG/UVMassGap.lean`, `MarginalUVMassGap.lean`).**
  `lattice_mass_gap_of_cluster_and_coupling` takes as hypotheses (a) `hIRbound : |covIR k| <= C1 e^{-eps k}`, (b) `hRpoly : forall t k,
  |Rsc t k| <= A e^{-c0 t} g_k^{kappa0}` (the per-scale remainder activity bound), (c) `hg : g_k <= C r^k`. The honest 4D variant
  `lattice_mass_gap_of_cluster_and_marginal_coupling` replaces the geometric coupling profile by the marginal recursion `g_{k+1} =
  g_k (1 - beta g_k)` (asymptotic freedom: summable, not geometric). The "activity-decay input" is `hRpoly`: the concrete
  Yang-Mills cluster-expansion-with-holes remainder activity bound for the physical RG operator. Status (`docs/HRPOLY-STATUS.md`, 6 Sept):
  20/41 terminal producers, `TermSource = 0` constructed inhabitants, uniform physical `B0, delta0` open, draft PR #29. Everything
  built around it (`YMActivityBudget`, `RawYMActivityDecomposition`, many `Actual*` oracle files in `RG/`, 252 files) is bookkeeping that
  turns a source-shaped activity plus defect bounds into the exponential decay; the README states this does not replace the
  Appendix-F/H renormalised-activity theorem. The `lattice_mass_gap_*` conclusion is exponential decay of `covIR t + covUV t`, nothing more.
- **OS / transfer-operator work.** `YangMills/OS/` (about 35 files): reflection splitting, Perron/PSD kernels, spatial Birkhoff,
  transfer gap files, physical Wilson cylinder and square, Z2/ZN toy substrates, SU(2) reflection endpoint. README status line:
  "R1/R2 geometry and measure verified; positivity and transfer open"; no transfer-matrix gap for SU(N). `HYPOTHESIS_FRONTIER.md`
  lists continuum limit, OS/Wightman and gap as "open mathematics", Clay distance "~0%".
- **Relation to the bridge.** It states the *shape* the bridge would take in its assembly: per-scale remainder `R_{t,k}` with decay
  in the IR index and a summable profile in the scale index, UV covariance as the sum over scales. That is a useful target format, but
  the substantive step is carried as `hRpoly`. It also relies on a "Balaban section 6.3" single-scale bound that is only transcribed
  (`docs/BALABAN-SOURCE-BOUNDS.md`, `SOURCE-CLAIM-AUDIT.md` list contradicted/source-pending claims).

## 3. `mrdouglasny/lgt`

- Licence Apache-2.0. Toolchain file `leanprover/lean4:v4.30.0` (README says v4.29.0; the file wins). Last commit 2026-07-21.
- **Goal / headlines (README, confirmed in files).** Strong-coupling lattice YM gap by Dobrushin uniqueness: `ym_mass_gap_exponential_decay`,
  `ym_mass_gap_rate_exists` in `LGT/MassGap/StrongCoupling.lean`, U(n), d >= 2, beta < 1/(32 n (d-1)), `|<Re Tr U_p Re Tr U_q>_c| <= 32
  n^2/(1-alpha) alpha^{(plaqDist-1)/2}`. Verified by scan: zero `axiom`, zero code `sorry` (the word appears only in stale docstrings
  of `LGT/Bridge/ScaleTransfer.lean`, lines 14, 24, 236, 391, which is a documentation inconsistency).
- **The "RG scale-transfer bridge" (`LGT/Bridge/ScaleTransfer.lean`, 534 lines).** `correlation_decay_transfer` is a pure arithmetic lemma:
  coarse covariance decays as `C alpha^{d_coarse}`, blocking compresses distances (`d_fine / scale <= d_coarse + overhead`), and
  `|cov_fine| <= |cov_blocked|`, hence fine decay `C/alpha^overhead * alpha^{d_fine/scale}` and rate `m/scale`. The two real inputs are
  fields of `RGBlockingData` / `RGCovarianceData`: `dist_compression` and `cov_transfer`. **Hypotheses, not constructed for any model.**
  `Bridge/O3MassGap.lean` and `TensorDobrushin.lean` assume an "EKR certificate" (tensor-RG contraction lambda < 1) as input. It is aimed at
  2D tensor RG (Levin-Nave), not gauge theory; for 4D YM, `cov_transfer` (blocking preserves covariances up to a bound) is exactly the
  unproved statement. The project's own TRG blocking construction (`TRGSetup`) is stated, not proved for geometry beyond the docstring.
- **Relation to the bridge.** It is the cleanest statement of what the bridge must deliver at the level of covariances: a blocking map
  with a uniform scale `L_0`, a coarse-grid Dobrushin-type contraction, and a covariance comparison. It does not supply any of them.

## 4. The OpenAI construction (2026-10-28), validated 2026-11-10

- **Sources.** `yang-mills-group/YM` (Apache-2.0, pushed 2026-11-15; contains the committee's `docs/assessment-1.pdf`, a copy of the
  submission under `submissions/openai-20261028/submission/`, and group checks); original distribution in
  the `yang-mills-group` repository of the 28 October 2026 OpenAI submission. Lean 4.32.0, pinned Mathlib, 9,477 `.lean` files in the submission (my count; gravity notes: about
  988k lines, 250,319 imported project declarations, 100,168 reached by the 17 audited headline theorems). Licence Apache-2.0 plus
  retained third-party notices (the group's checks derive from `mrdouglasny/lgt` and `xiyin137/OSreconstruction`).
- **Verified in code.** Zero `axiom`; the only `sorry` is the reference theorem in `Challenge.lean` (by design, for Comparator).
  Committee: clean rebuild, axiom audit (only `propext`, `Classical.choice`, `Quot.sound`), Comparator checks (with limitations noted
  in assessment section 9.2; no external kernel replay).
- **What it constructs (assessment PDF, parts I-II; theorem names from the repo).** `YangMills.jointExistence` proves `JointExistence`:
  for each closed matrix subgroup of U(m) with simple nonabelian Lie algebra, a Wilson lattice family such that for every strictly
  increasing volume sequence there is a subsequence and a continuum hierarchy with Wightman reconstruction, an all-orders separated
  OPE with bounds, and a non-freeness test (centred trace two-point function with leading `3 dim(g)/pi^4 / (r^8 log^2(1/r))`). The
  detailed form is `YangMills.constructed` (`Construction.lean`).
- **The sequence.** Step 1 (`Theorem 4.1`, fixed-volume UV limit): a spacing sequence `a_N -> 0` built from a `Schedule` (odd block sizes
  >= 3, periods divisible by 4; `YM/Lattice/Scale.lean`: `denominator`, `side m p = period p * denominator m`), physical period
  `L_p`, couplings with `beta_{N,p} / log(1/a_N) -> b` uniformly in p (`WilsonRegularity.running`; the assessment gives `b = 2 b0 =
  11 C_g/(24 pi^2)`, text extraction of the PDF is garbled at that point). For every fixed `p` and label list, smeared renormalised
  correlations `C_{N,p}(v;f)` converge as N -> infinity (Cauchy in N), with C^infinity kernels off coincidences. The proof "defines an
  explicit RG map for the leading (marginal) terms in the action, following the general approach of Balaban but with many
  improvements such as a gauge fixing invariant under discrete lattice symmetries", agrees with one-loop RG, and propagates bounds on
  irrelevant terms. Convergence is only along the chosen sequence; no universality. Step 2 (Theorem 5.1): subsequential infinite-volume
  limit by Arzela-Ascoli from local bounds and equicontinuity uniform in p >= p0(K), derived by "reflection positivity, chessboard
  estimates, transfer-operator representation, and Cauchy estimates" from the UV control. Step 3: decomposition into pure phases, each
  OS-axiom satisfying (independently re-checked by the group against the Douglas-Mei-Yin spec), OS reconstruction to Wightman. Observables
  are abstract labels (gauge-invariant polynomials in F and D), not Wilson loops.
- **What it says about the gap.** Nothing positive: "The construction provides no evidence for or against a mass gap" (assessment sections
  2, 8). Open per the committee: uniqueness/convergence of the infinite-volume limit, continuum measure, uniform mass gap with spectral
  gap, Wilson loops and area law, single-particle states. Vacuum uniqueness is not proved (clustering of S_mix fails to follow).
- **Relation to the bridge.** This is the short-distance end of the bridge, proved with a Balaban-type RG on marginal terms, with the
  coupling driven by asymptotic freedom. It exposes where the middle range is *avoided*: local observables in fixed boxes are controlled
  uniformly in the volume through RP and chessboard estimates, which gives compactness but no contraction and no decay. From the
  documents I could not determine how the effective coupling at physical scale `L_p` (large in lattice units, large coupling in
  physical units unless p is tied to the scale) is controlled; the assessment says the infrared limit is not controlled enough for
  uniqueness, which is consistent with the middle range being bypassed. This should be read in the source (`YM/RG08/...`, `WilsonFamily`)
  before any claim. Companion: `ethanwsussman/Yang--Mills-LLM-experiment` (informal, LLM-written, explicitly unvetted account of
  Balaban's YM programme; `balaban-lean` uses it as a reading guide, not as a proof).

## 5. Other projects found

| Repository | Licence / last push | What it is, verified |
|---|---|---|
| `xiyin137/OSreconstruction` | not read / 2026-11-03 | OS reconstruction in Lean; the group's OS checks derive from it. Not inspected. |
| `math-commons/yang-mills` | 404 via `gh` (private or renamed) | Named in the YM repo NOTICE as source of OS declarations. Not inspected. |
| `stalex444/yang-mills-conformal-current` | Apache-2.0 / 2026-11-14 | Add-on to OpenAI's release: conformal-Killing divergence of the stress current (`conformal_divergence`). Axioms standard per README. Downstream of OpenAI; nothing on the middle range. |
| `Qamarbajwa/yang-mills-lean4` | Apache-2.0 / 2026-11-21 | 94 files, 9,665 lines, no code `sorry` or `axiom` by scan; "finite-volume cluster expansions, Lie-algebraic rigidity, conditional continuum reduction hypotheses". Read README only. Modest, finite-volume. |
| `navindutta/yang-mills-lean4` | Apache-2.0 / 2026-09-10 | Kotecky-Preiss, Bessel bounds, SU(2) infrastructure; README: "not a proof". Read README only. |
| `umpolungfish/yang-mills-lean4` | NOASSERTION (badge says Apache) / 2026-11-21 | Claims "unconditional" Clay existence and strict gap with 0 `sorry`. **Not credible, verified:** `ContinuumClosure.lean` has 21 code `sorry` in the repo (e.g. lines 308, 318-320 inside the canonical construction), the headline `clay_yang_mills_strict` is the conditional `..._from_balaban_and_os` applied to a "canonical" structure instance, and that instance is built from a fixed strong coupling (`standardBeta0 = 1/300`); the "Balaban hypothesis" is a structure of the conclusion's own fields. Treat as not a weak-coupling work. |
| `Cloudhabil/yang-mills-lean4` | not read | Not inspected. |
| Zenodo "Lean 4 Yang-Mills" records | n/a | Appear in web search, several claiming axiom-free proofs; unvetted, not used. |

Web search found no Lean formalisation of Balaban's gauge-theory RG or of the asymptotic-freedom/flow of the Yang-Mills coupling beyond the
OpenAI submission. GitHub repository search for "asymptotic freedom lean" and "renormalization group Lean 4" returned nothing relevant.

## 6. What a weak-coupling attack could use as reference

Ideas and structures (all as references to check ours against; central parts are ours to build):

1. **Target format for the bridge.** Eriksson's assembly (per-scale remainder `R_{t,k}`, summable profile in the scale index because the
   coupling is marginal, UV covariance as the scale sum) and `lgt`'s transfer data (blocking map, distance compression, covariance
   comparison) are both the right shape. The contraction we want at one block scale `L_0`, uniformly in the spacing and the volume,
   is exactly "`dist_compression` + `cov_transfer` + a coarse Dobrushin/Clustering contraction", with the second hypothesis the substantive one.
2. **Architecture of a rigorous multiscale step.** `balaban-lean`: frozen statement, polymer decay `exp(-kappa|X|/(M L^j)^d)`
   at scale j, locality (depends only on g|X), analyticity in the source on an l1 ball, torus independence, separate large-field
   gas. Root-F's form (log Z as a sum of local terms with scale-dependent decay) is also what a "blocked theory has a cluster-expansion
   representation" statement would look like.
3. **OpenAI's gauge-theory step.** The only formal gauge-fixed RG map for the marginal terms, with irrelevant-term propagation and a
   `Schedule` of odd block sizes. The relevant pieces to read are the RG map and the bounds on irrelevant terms: they are what must keep
   holding as the coupling rises. Also the RP/chessboard/transfer route to uniform local bounds, which is the existing formal way to
   get compactness without a contraction.
4. **Known obstacles and traps.**
   - Printed Balaban estimates can be incomplete or false as stated (`balaban-lean`: seven gap places; one estimate false; transcription
     mismatches). A Lean attack should expect to restate lemmas, with an errata log.
   - Scale: about 1.09M lines unfinished for the O(N) model; OpenAI's gauge construction about 1M lines. Perturbative-sized control is a
     large project; our one-bound-at-one-scale route is deliberately smaller.
   - Dressing a hypothesis as a theorem hypothesis does not cross the bridge (Eriksson `hRpoly`, `lgt` `cov_transfer`); a named hypothesis
     structure is acceptable only if its non-vacuity is checked (the `Inhabited` pattern in `balaban-lean`) and it is reported as open.
   - Conclusion-shaped lemmas about free real sequences are not gap statements (Eriksson's own correction); state the gap about the
     measure/transfer operator.
   - Photon test: none of the Lean projects test a purported bridge against 4D U(1); nothing in them rules out an argument that would
     also prove a gap for U(1).
5. **Infrastructure we could check against.** Eriksson's KP/Mayer engine for the strong side; `lgt`'s Dobrushin chain; the YM
   group's `PhaseAndOS`, `TranslationWard`, and OS-axioms bridge for what "continuum theory" means formally.

## 7. Open gaps nobody covers

- No Lean statement or proof that the lattice theory at **intermediate coupling** (beta around 2-3 for SU(2), g^2 ~ 1) has any
  uniform property; no formal control of the RG flow past the perturbative region.
- No formalised Balaban **gauge-theory** RG (small/large field, 1984-1989), in any repository; `balaban-lean` is O(N), unfinished.
- No formal **connection between the OpenAI-constructed theory and a coarse-grid strong-coupling object** (Wilson loops, a blocked
  Gibbs measure, a Dobrushin or reflection-positive contraction); the construction uses abstract labels, not Wilson loops, and the
  assessment lists loops/area law as open.
- No **uniform-in-volume, uniform-in-spacing** clustering or transfer-matrix gap for non-abelian lattice gauge theory in 4D at any
  coupling above the tiny strong-coupling windows.
- No Lean treatment of the **step-scaling** / gradient-flow picture (numerical bridges exist only outside Lean).
- No formal **non-triviality of the mass scale**: OpenAI's assessment says the construction does not establish a nonzero intrinsic continuum
  reference mass (assessment A5).
- Not inspected, worth a later look: `YM/RG08`, `WilsonFamily` and the RG-map modules inside the OpenAI submission (how the IR end of
  the flow is controlled at `L_p`), `xiyin137/OSreconstruction`, and `math-commons/yang-mills`.
