# Claims incoming: Part VI, Navier-Stokes (`draft/06-part-VI-navier-stokes.md`)

Draft 2, 2026-11-24. Rows in the format of `../CLAIMS.md` (ID, claim, status, source, upgrade), for the coordinator to merge. The status
column holds one primary mark; a row with two parts of different status is split or carries the weaker status first. Lean paths are
relative to `docs/mass-gap/formal/`; notes are relative to `docs/unified/` (`NAVIER-STOKES.md` is cited as NS, `BLOWUP.md` as BL).
Not verified by this writer: external and classical references are cited as the notes cite them and were not re-read; Lean files were
not rebuilt. Lean names were checked by script against declarations (`theorem`, `def`, `structure`, `inductive`) in the cited files.

## Part VI. Navier-Stokes

### VI.0 State

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VI.0a | Clay's statement (Fefferman): (A) smooth global solutions on R^3 with zero force, (B) the same on the torus, (C) breakdown on R^3 with a force, (D) the same on the torus | classical | Fefferman's official statement; NS 1.1 | none |
| VI.0b | (C) and (D) allow a force; an unforced blowup disproves (A) or (B) and so proves (C) or (D) with f = 0 | classical | NS 1.1 | none |
| VI.0c | OpenAI, 2026-09-08: blowup with a smooth compactly supported force and zero initial data; unrefereed, not checked here | external | NS 1.5(b); the paper and its Lean repository | independent rebuild, refereeing |
| VI.0d | Alpoge and Buckmaster, 2026-11-20: unforced blowup on R^3 and the torus; unrefereed, unverified here; the certificate is unreleased (hash only) | external | NS 1.5(a), 6.1, 6.2 | release of the certificate and an independent check (VI.5.4) |
| VI.0e | This part proves no statement about the real Navier-Stokes equations; the Lean modules contain no Navier-Stokes object | (statement of scope) | NS, header and 2.6 | none |
| VI.0f | (A) and (B) are open in this paper; an external claim (VI.0d) asserts they are false | open | NS 0, 7 | a proof, or the audit of VI.5.4 |

### VI.1 The problem, the no-go results, the model

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VI.1.1a | Leray: a singularity at T* forces sup abs(u) >= c (nu/(T* - t))^{1/2} and norm(grad u)_{L^2} >= c (T* - t)^{-1/4} | classical | Leray 1934 (recalled); NS 1.2 | none |
| VI.1.1b | No nonzero backward self-similar solution at the Leray scaling in `L^3` (Necas-Ruzicka-Sverak), `L^p` and under local energy bounds (Tsai) | classical | Acta Math. 176 (1996); Arch. Ration. Mech. Anal. 143 (1998) (recalled); NS 1.2 | none |
| VI.1.1c | The singular set of a suitable weak solution has zero one-dimensional parabolic measure | classical | Caffarelli-Kohn-Nirenberg 1982 (recalled); NS 1.2 | none |
| VI.1.1d | A solution bounded in `L^infinity_t L^3_x` is smooth; at a singular time the `L^3` norm tends to infinity | classical | Escauriaza-Seregin-Sverak 2003; Seregin 2012 (recalled); NS 1.2 | none |
| VI.1.1e | No axisymmetric Type I blowup | classical | Chen-Strain-Tsai-Yau; Koch-Nadirashvili-Seregin-Sverak (recalled); NS 1.2 | none |
| VI.1.1f | Smooth backward discretely self-similar solutions obey the Type I bound; nonzero ones need a period bounded below | classical | Chae-Wolf; Pineau-Vicol (as cited by Alpoge-Buckmaster); NS 1.2 | none |
| VI.1.1g | The no-go results leave open discretely self-similar, asymptotically self-similar and Type II blowup | classical | NS 1.2 | none |
| VI.1.2 | Tao's averaged equations keep the energy identity and the standard estimates and blow up in finite time | classical | Tao, J. Amer. Math. Soc. 29 (2016) 601-674; NS 1.3 | none |
| VI.1.3 | Hou's axisymmetric numerical scenario: vorticity growth about 10^7 at nearly self-similar Leray-type rates; numerical evidence by others, not a proof | external | Hou, arXiv 2107.06509; NS 1.4 | a proof, or a refutation |

### VI.2 The card

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VI.2.1 | The statements of the external tie (certificate exists; profile exists; Fefferman's (A); (B)) are named, not defined: the library has no Navier-Stokes object | paper (observation) | `ProofPhase/Unified/NavierStokesAPI.lean`, `ABInterface`; NS 6.3 | audit item 1 (real definitions) |

### VI.3 What is proved (skeleton; no statement about the equations)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VI.3.1a | The viscous term in the zoomed frame has weight (T* - t)^{1 - 2 alpha}; the local energy scales like (T* - t)^{5 alpha - 2} | classical | scaling computation; BL 4.2; NS 2.2 | none |
| VI.3.1b | The viscous floor: constant at alpha = 1/2, at most nu below it, summable below it, unbounded above it, bounded exactly when alpha <= 1/2 | Lean | `ProofPhase/Unified/NavierStokes.lean`, `nsViscous_half`, `nsViscous_le`, `nsViscous_summable`, `nsViscous_tendsto_atTop`, `nsViscous_bounded_iff` | none |
| VI.3.1c | Local energy bounded exactly for alpha >= 2/5; the Type I bound exactly for alpha >= 1/2 | Lean | `ProofPhase/Unified/NavierStokes.lean`, `ns_energy_window`, `ns_typeI_iff` | none |
| VI.3.1d | The window: bounded viscous floor and bounded local energy together exactly for 2/5 <= alpha <= 1/2 | Lean | `ProofPhase/Unified/NavierStokes.lean`, `ns_window` | none |
| VI.3.1e | Above the window no one-scale certificate covers all steps | Lean | `ProofPhase/Unified/NavierStokes.lean`, `ns_no_uniform_certificate` | none |
| VI.3.1f | The window decision runs on rational exponents and is proved right for the real statement | Lean | `ProofPhase/Unified/NavierStokesAPI.lean`, `windowQ`, `windowQ_admissible_iff`, `windowQ_leray_iff`, `windowQ_half`, `windowQ_correct` | none |
| VI.3.2a | A route I certificate has a non-steady profile (no exact self-similarity is used) | Lean | `ProofPhase/Unified/NavierStokes.lean`, `LerayDSSCertificate`, `LerayDSSCertificate.not_steady` | none |
| VI.3.2b | The free flow pays S/4 per period at floor 0; a period factor 0 < rho < 1 is a cost -log rho above floor 0 for one step type | Lean | `ProofPhase/Unified/NavierStokes.lean`, `ns_free_flow_pays`, `ns_dss_costAboveFloor` | none |
| VI.3.2c | The free flow contracts the rescaled `H^1` norm by e^{-s/4}, because `H^1` is subcritical by 1/4 | classical | NS 2.3; Alpoge-Buckmaster 1.1 (as read in the notes) | none |
| VI.3.2d | From the period-map inequality (hypothesis), the perturbation decays geometrically, the periods sum to the finite time 1, the `H^1` amplitude tends to infinity, the profile is not steady | Lean | `ProofPhase/Unified/NavierStokes.lean`, `ns_dss_converge`, `ns_period_hasSum`, `nsPeriodLength`, `ns_dss_amplitude`, `ns_blowup_of_dss` | none (the PDE inputs are VI.5.1) |
| VI.3.2e | Route I card: from the period contraction (open step) the perturbation settles onto the profile, with an explicit period count, and the three consequences of VI.3.2d hold | Lean | `ProofPhase/Unified/NavierStokesAPI.lean`, `routeI`, `system`, `contracting`, `settles_by` | none (the open step is VI.5.1) |
| VI.3.3a | Route II: from the Chen-Hou certificate with trapping condition (1 - q)^2 >= 4 C (epsilon + nu) and 2/5 <= alpha < 1/2: trapped perturbation, finite T*, unbounded amplitude; the same as a cost above a floor | Lean | `ProofPhase/Unified/NavierStokes.lean`, `EulerProfileCertificate`, `ns_blowup_of_euler_profile`, `ns_euler_gap_of_costAboveFloor` | none |
| VI.3.3b | Viscosity as a transported uncertainty: bounded below the Leray scaling even at cost = floor; constant and unbounded at the Leray scaling | Lean | `ProofPhase/Unified/NavierStokes.lean`, `ns_viscous_transport_bounded`, `ns_viscous_transport_unbounded_at_leray` | none |
| VI.3.3c | The API bounds the route II perturbation: M(n) <= M(0) + 2 (epsilon + nu)/(1 - q) | Lean | `ProofPhase/Unified/NavierStokesAPI.lean`, `eulerUncertainty`, `routeII_bounded` | none |
| VI.3.3d | No route II profile is known | open | NS 2.4 | a profile and its certificate |
| VI.3.4a | A summable budget never pays a uniform positive cost; shares whose partial sums stay below the start energy are such a budget | Lean | `ProofPhase/Unified/NavierStokes.lean`, `ns_energy_budget_not_costAboveFloor`, `ns_energy_identity_not_costAboveFloor`; `ProofPhase/Unified/NavierStokesAPI.lean`, `energy_cannot_fill` | none |
| VI.3.4b | Per dyadic scale the energy-only transfer bound K 2^{5k/2} overtakes the viscous cost nu 4^k at some scale, for every nu and K > 0 | Lean | `ProofPhase/Unified/NavierStokesAPI.lean`, `dyadic_supercritical` | none |
| VI.3.4c | The scalings behind VI.3.4b (Bernstein), and that the same count is critical in two dimensions, which is why 2D is regular | classical | NS 5.2(b) | none |
| VI.3.4d | Regularity card: from a uniform cost per dyadic scale above the transfer floor (open step), the carried quantity decays at a positive rate and is summable | Lean | `ProofPhase/Unified/NavierStokesAPI.lean`, `DyadicInput`, `regularity` | none (the open step is VI.5.2) |
| VI.3.5a | Chen-Hou: stable nearly self-similar finite-time blowup for 2D Boussinesq and 3D axisymmetric Euler with smooth data and a wall, computer-assisted; not Navier-Stokes | external | Chen-Hou, arXiv 2210.07191, 2305.05660; BL 1 | none needed for this paper |
| VI.3.5b | One-step trapping: (1 - q)^2 >= 4 C r and a start in the ball keep the perturbation in the ball forever; the threshold is sharp | Lean | `ProofPhase/Unified/Blowup.lean`, `trap`, `trap_radius`, `trap_of_gap`, `escape_of_below`, `escape_pos` | none |
| VI.3.5c | The one-step certificate is `CostAboveFloor` of 1 - q over 2 sqrt(C r) for one step type | Lean | `ProofPhase/Unified/Blowup.lean`, `gap_of_costAboveFloor` | none |
| VI.3.5d | Under a focusing margin the durations are summable, T* is finite, the amplitude is unbounded; assembled certificate | Lean | `ProofPhase/Unified/Blowup.lean`, `durations`, `durations_pay`, `arrival`, `amplitude_unbounded`, `blowup_of_certificate` | none (the step inequality is a hypothesis) |
| VI.3.5e | Each rescaled step adds one fixed quantum to the Beale-Kato-Majda count | Lean | `ProofPhase/Unified/Blowup.lean`, `boundary_quantum` | none |
| VI.3.5f | The BKM integral is infinite exactly when smooth continuation fails | classical | Beale-Kato-Majda; BL 3.2 | none |

### VI.4 What is borrowed

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VI.4.1a | Alpoge-Buckmaster Theorem 1.1: one backward discretely self-similar viscous profile gives unforced blowup from smooth data at the rate (T - t)^{-1/4} in `H^1`, stable in finite codimension; unverified here | external | NS 1.5(a), 6.2 | refereeing, independent audit |
| VI.4.1b | Alpoge-Buckmaster Theorem 7.1 and Corollary 7.2: a certificate (explicit inequalities, Appendix B) gives an exact profile nearby; unverified here | external | NS 1.5(a), 6.2 | release and independent check of the certificate |
| VI.4.1c | The candidate profile: not axisymmetric, 19-fold symmetry about one axis and a half-turn about another, period about 0.36 | external | NS 1.5(a), 6.2 | the released certificate |
| VI.4.1d | The certificate is not released; only its SHA-256 hash, 3f7a335b84b6c7631742cacc5343dfcd11cf72f5221ff79b2b9268790b4b22c5, is public; the 128-bit interval check is outside their formalisation | external | NS 1.5(a), 6.1; the paper | release, hash check, independent interval check |
| VI.4.1e | Their Lean library (about 2,270 files, Lean 4.33) was patched on 2026-11-20 and not rebuilt; its formal Theorem 1.1 has no rate; the prose no longer follows the Lean proof | external | NS 1.5(a), 6.2 (their README and section 1.6) | rebuild and axiom audit (audit items 2, 3) |
| VI.4.1f | Tao (blog, 2026-11-20): technically human-readable, a clear strategy, a professional write-up still needed; no referee report | external | NS 1.5(a), 6.1 | a referee report |
| VI.4.1g | Their profile avoids the no-go results (depends on zoomed time; weak `L^3` but not `L^3`; not axisymmetric; period above the lower bound, constant not checked here) | external | NS 2.3, 6.2 | the released certificate and the constants |
| VI.4.1h | The external tie in the API: three `External` fields, one open-step card (the certificate), the paper's route gives the same conclusion; plumbing only | Lean | `ProofPhase/Unified/NavierStokesAPI.lean`, `ABInterface`, `abProblem`, `ab_paper_route` | none (content is VI.4.1a to VI.4.1e) |
| VI.4.2a | OpenAI: a smooth compactly supported force, zero initial velocity, bounded energy, sup norm unbounded as t -> 1, for every nu > 0; addresses (C) and (D) | external | NS 1.5(b) | refereeing |
| VI.4.2b | An independent build record of its Lean proof reports only the three standard axioms, no `sorry`, and a match to a public formalisation of (C) and (D); not rebuilt here | external | NS 1.5(b) | independent rebuild |
| VI.4.2c | Lemma-level departures of its Lean proof from the written proof are shown, with no claim about the written proof's correctness | external | arXiv 2610.08144; NS 1.5(b) | resolution by the authors |
| VI.4.3 | Smaller programmes: a computer-search target for unforced blowup (Petrillo-Glimm); cascade blowup in dyadic shell models (Cheskidov-Dai-Palasek); neither is Navier-Stokes blowup | external | arXiv 2609.23868, 2609.26790; NS 1.5(c) | none |
| VI.4.4a | Goedel completeness: if ZFC plus "some smooth datum blows up" is consistent, a model exists | classical | Goedel; NS 4 | none |
| VI.4.4b | A completeness model may be nonstandard and settles nothing about the real equations; only a proof settles the Clay question | classical | NS 4 (recalled absoluteness facts) | none |
| VI.4.4c | Whether regularity is independent of ZFC | open | NS 4 | a proof either way |

### VI.5 The one open step

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VI.5.1 | **Route I open step:** one period of the zoomed flow from a non-steady periodic profile contracts the perturbation on the complement of finitely many directions, in a real norm, with rho + C delta < 1; in the tie, the Alpoge-Buckmaster certificate satisfies their Appendix B | open | `ProofPhase/Unified/NavierStokesAPI.lean`, `PeriodContraction`, `abProblem`; NS 5.2(c), 6.3 | the released and independently verified certificate |
| VI.5.2 | **Regularity slot:** every dyadic scale dissipates a uniform cost above the transfer floor from the true nonlinearity; the energy identity cannot supply it; false if VI.0d holds | open | `ProofPhase/Unified/NavierStokesAPI.lean`, `regularity`; NS 5.2(b) | a proof from the true nonlinearity |
| VI.5.3 | What continues past T* for a blowup solution (uniqueness of weak continuation) | open | BL 3.2, 6.3 | a theorem |
| VI.5.4 | The audit list has twelve items, none done; five are named in the draft (real statements, rebuild, certificate check, Lean-only steps, mapping of Appendix B onto `LerayDSSCertificate`) | paper | NS 6.4 | the audit |
| VI.5.5 | An independent construction of the profile and certificate from scratch is beyond reach now | reading | NS 3 | none |

### VI.6 Validation: Poincare, and SU(N)

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VI.6.1a | Ricci flow on a closed 3-manifold with positive scalar curvature has a singularity by T <= 3/(2 R_min(0)) | classical | Hamilton; BL 6.1 | none |
| VI.6.1b | The W-entropy is non-decreasing and gives kappa-noncollapsing at every scale | classical | Perelman, arXiv math/0211159; BL 6.2 | none |
| VI.6.1c | Each surgery removes a definite volume and volume is bounded, so finitely many surgeries on a finite interval | classical | Perelman, arXiv math/0303109; BL 6.2 | none |
| VI.6.1d | Blowup limits are kappa-solutions, classified in 3D; the canonical neighbourhood theorem; surgery along necks | classical | Perelman, arXiv math/0303109; BL 6.2, 6.3 | none |
| VI.6.1e | Finite extinction for simply connected closed 3-manifolds, which certifies the 3-sphere | classical | Perelman, arXiv math/0307245; Colding-Minicozzi 2005; BL 6.4 | none |
| VI.6.1f | Singular Ricci flows through singularities exist without choices and are unique and stable | classical | Kleiner-Lott; Bamler-Kleiner, arXiv 1709.04122; BL 6.3 | none |
| VI.6.1g | The ledger fit of Perelman's proof: steps, monotone quantity (no uniform positive cost), one estimate at all scales, quantum per step, boundary, act, end | reading | BL 6.2 | none (a reading stays a reading) |
| VI.6.2 | Verdict: the restatement matches Perelman's proof as a description, not as a mechanism; nothing new is claimed | reading | BL 6.5 | none |
| VI.6.3a | The unit sphere of C^2 is in bijection with SU(2) | Lean | `ProofPhase/Unified/BlowupSUN.lean`, `su2Mat_mem`, `su2_form`, `sphereEquivSU2` | none |
| VI.6.3b | That bijection is a diffeomorphism, so SU(2) is the 3-sphere | classical | BL 7.1 | Lean topology statement |
| VI.6.3c | The bi-invariant metric on SU(N) shrinks as g(t) = (1 - N t) g(0), extinct at 1/N, with the Einstein constant growing as lambda' = 2 lambda^2 | Lean | `ProofPhase/Unified/BlowupSUN.lean`, `shrink_hasDerivAt`, `shrink_unique`, `shrink_pos`, `shrink_extinct`, `einstein_hasDerivAt`, `einstein_unbounded`, `sun_extinction` | none |
| VI.6.3d | Ric = (N/2) g for the metric -tr(XY) on SU(N) | classical | Killing form; BL 7.2 | none |
| VI.6.3e | The constants of VI.6.3d checked for N = 2, 3, 5, 11 (error below 5e-15) | numerical | `blowup_sun_check.py`, `blowup_sun_check.log` | none |
| VI.6.3f | The extinction of VI.6.3c holds for every positive Einstein manifold, so it carries no topological information about SU(N) | classical | BL 7.2 | none |
| VI.6.3g | Positive-Ricci metrics on a closed 3-manifold flow to constant curvature, so SU(2) attracts | classical | Hamilton 1982; BL 7.3 | none |
| VI.6.3h | For N >= 3 the first Laplace eigenvalue N - 1/N lies strictly inside the Cao-He window; for N = 2 it sits exactly on the lower edge | Lean | `ProofPhase/Unified/BlowupSUN.lean`, `sun_window`, `su2_window_edge` | none |
| VI.6.3i | Cao-He's criterion and verdict (SU(N), N >= 3, linearly unstable) and Kroencke's dynamical instability | external | Cao-He, arXiv 1304.2697 (Crelle 2015); Kroencke (recalled); BL 7.3 | none |
| VI.6.3j | "Poincare for SU(N)" (homotopy equivalent to SU(N) implies homeomorphic or diffeomorphic) for N >= 3: no theorem found, possibly false smoothly, not reached by Ricci flow; N = 2 is Poincare | open | BL 7.4 (a negative literature search) | a surgery-theory computation |
| VI.6.4 | The side-by-side table of Perelman, Chen-Hou and the claimed route I | reading | BL 6.5; NS 2.3 | none |

### VI.7 and VI.8 Readings and closure

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VI.7a | A blowup is a certificate that infinitely many steps fit in finite time; T* is the DB, the profile crosses it; the hand-over run in reverse | reading | BL 3.3 | none |
| VI.7b | One theorem (`summable_of_gap`) gives the finite correlation length in Yang-Mills and the finite T* here | reading (Lean for both uses: `ProofPhase/Unified/Ledger.lean`, `summable_of_gap`) | BL 2.5 | none |
| VI.7c | Scale invariance reads as the arrow of causality: the outside set has one element | reading | BL 2.4 | none |
| VI.7d | "Not DMP-complete, hence blows up": a reading of supercriticality that names the side the 2026 claims assert; it proves nothing | reading | NS 4(6); `PREP.md`, 2026-11-24 entries | none |
| VI.7e | Whether DMP-completeness has a precise statement that Navier-Stokes violates and from which blowup follows | open | NS 4(6) | a statement and a proof |
| VI.7f | "Settle" means the carried quantity dies out: regular on the regularity card, blowup on the route I card | reading | NS 5.2 | none |
| VI.8 | If the certificate verifies, the route I open step is discharged and one row, one verdict line and one abstract item change; if not, the card is unchanged | paper | NS 5.2(d), 6.4 | the audit of VI.5.4 |
