# Open claims: triage and closures (2026-11-24, overnight round)

*Coordinator, 2026-11-24: applied to `CLAIMS.md` and the chapters after an independent rebuild (the five `ProofPhase/Closures/`
modules: 81 declarations, standard axioms only; IM: arsenal 100 declarations, `proof/` 59 theorems, merged as im#10 and pinned).
Not applied: **VI.6.3j** ("Poincare for SU(N)"), which rests on this round's own surgery-theory argument and waits for an
independent read. III.9.5 includes the decision that O1's one Lean form is `FineOneBox`; that choice is listed for the owner.*

The owner's rule for this round: O1, each card's one open step, stays open, because the paper needs it as its one assumption
(Part X 4.4, claim X.64). Every other open row whose openness conflicts with the paper's goals is closed where it honestly can
be. Nothing here claims a problem solved.

Scope: the 60 rows of `CLAIMS.md` whose status column starts with "open" (read 2026-11-24 05:25; the audit thread was editing the
ledger at the same time, so row IDs are used, not line numbers). This file edits neither `CLAIMS.md` nor any chapter; every
change is written below as a ready row for the coordinator.

**Counts.** (a) O1-type: 40 (31 the open step or a restatement, 9 a route to or a strengthening of the card's open problem).
(b) closable: 15, all closed below (6 with new Lean, 1 with Lean that already existed, 8 by correction or citation). (c) the owner's decision: 2, plus one
remainder split off by a (b) closure (III.9.5b, whether the one assumption's "running system" includes the scale-uniform lower
edge). (d) genuinely open and not O1-type: 3, plus two remainders split off by (b) closures (VI.6.3j smooth N = 3, VIII.1.3g).

**By construction.** Following the owner's strategy (a bound excised by identity as a fact of construction), four closures are
marked "by construction" where they appear: the per-box non-triviality (III.9.5a), the running clause on the one-loop line
(III.9.5a), the counts of one curve (VII.3.6d) and attenuation as intersection (I.10e). None is applied to an O1-type row.

All new Lean builds and passes its axiom gate (section 3): 81 declarations here, 16 theorems in IM `proof/`, the arsenal file
in IM `arsenal/`; the IM files are in an uncommitted worktree, so the rows citing them apply after IM merges them.

---

## 1. Triage

Classes: **a1** the card's open step or a restatement of it; **a2** a route to, or a strengthening of, the card's open problem
(closing it would settle or advance the Millennium-type problem itself); **b** closable (Lean, citation or correction);
**c** the owner's decision; **d** genuinely open, not O1-type.

| Row | Class | Evidence |
|---|---|---|
| I.10e | b (Lean, IM) | The attenuation theorem is a short statement about a narrowing operation; written in `im/proof/Im/Attenuate.lean` (section 3.2). |
| III.5.2b | a1 | F_e(L) >= 0.881 at some L is implied by O1 (F_e > 1.91 at one box); a weaker form of III.5.6, nonperturbative at fixed physical size. |
| III.5.6 | a1 | O1 itself. |
| III.5.7 | b (correction, Lean exists) | Needed only if O1 is stated with an annealed torus number. In the per-outside Lean form (`FineOneBox`, every boundary condition) the composition over boxes is the theorem `fineDecayInv_of_fineOneBox`; nothing annealed is used. |
| III.5.8 | b (Lean, model) | "Not written down": now written. In the transfer-matrix model the two criteria are independent, and the joint form gives both (`Closures/ChainJoint.lean`). |
| III.5.9 | b (Lean link) | One form chosen (`FineOneBox`); the other forms linked or shown unneeded; the link to the assembly re-exported (`Closures/OneBoxForm.lean`). Decision recorded in section 2. |
| III.6.8 | a1 | Y2 to Y5 are labelled "pieces of O1" in the row and in `OPEN-QUESTIONS-DMP.md` 2. |
| III.6.9 | a1 | The missing part is the supremum certificate over outsides, i.e. O1's quantifier ("uniformly over every outside"); the implication is already Lean. |
| III.9.5 | b (Lean split) | The gap assembly uses of `OnLCP'` only the resolution clause and passes `NonTrivial` through (`yang_mills_assembly_onebox`'s proof). Split three ways: the gap part (Lean); the per-box parts of non-triviality and the running clause (Lean, by construction); the scale-uniform parts (the lower bound on the correlation, the scheme clause), shown separate from O1 in the spectral model and left as a (c) remainder, III.9.5b. |
| IV.0c | a1 | GRH beyond Dirichlet is the GRH card's open step. |
| IV.1.5b | b (correction) | The explicit formula for Dirichlet L-functions, the C^2 test class and Weil's criterion are classical theorems; only the formalisation is missing. "open" means "not settled by anyone", which is not the case. |
| IV.2.5c | a2 | An arithmetic Hodge index on Spec Z x Spec Z would give the GRH sign: a route to the open step. |
| IV.4.1 to IV.4.8 | a1 (8 rows) | The eight faces are equivalent forms of the GRH open statement (Part IV 4, Part X 4.1 table: "eight faces"). |
| V.1.9 | b (correction) | On paper the results are classical (Dobrushin for general single-site spaces; hard constraints; systematic scan); only the Lean is conditional. The chapter already says "[classical] on paper"; audit row V.1.9 asks the same. |
| V.3.11 | b (correction) | The row states what is *known*: no superpolynomial bound for AC^0[p]-Frege, Frege, EF. That statement about the literature is classical. The bounds themselves are open problems outside the card, whose open step is V.4.10. |
| V.4.10 | a1 | The NP card's open step. |
| V.6.N1 | a2 | "Is the irreducible core of every refutation polynomial?" is NP vs coNP itself. |
| V.6.N3 | a2 | Frege lower bounds beyond n^3: a stronger system than the card's (CP). |
| V.6.N4 | a2 | From the certified class to all inputs: P vs NP, through a barrier-passing argument. |
| VI.0f | a1 | (A) and (B) open: the NS card's open step (regularity or blowup). |
| VI.3.3d | a2 | A route II profile would give blowup by the second route. |
| VI.4.4c | d | Independence of ZFC is a meta-question the card does not need (VI.4.4 is classical without it). Closed only by a proof of regularity, of blowup, or of independence. |
| VI.5.1 | a1 | The route I card's open step (`PeriodContraction`). |
| VI.5.2 | a1 | The regularity card's open step. |
| VI.5.3 | d | Continuation past T* (uniqueness of weak continuation) is a separate PDE question; the card ends at T*. Closed by a uniqueness theorem for the continuation class, not in reach. |
| VI.6.3j | b (paper correction, partial) | A classical surgery computation settles N >= 4 (false topologically) and N = 3 topologically (true); smooth N = 3 stays open as a (d) remainder. The row's "possibly false smoothly" is corrected. |
| VI.7e | c | Whether DMP-completeness has a precise statement that NS violates needs a formal definition of DMP-completeness, which is the owner's (DMP is the owner's framework). Once defined, the question becomes a2 (a route to blowup). |
| VII.1.2a | a1 | No bound rank <= order beyond order 1: the BSD card's open step (VII.5.1). |
| VII.1.2b | a2 | Finiteness of Sha in general is part of the refined conjecture, a strengthening of the card's open problem. |
| VII.3.6d | b (Lean + correction) | The counts can be tied to a curve by construction; done (`Closures/EulerCurve.lean`). The remaining link to Mathlib's local factor is a formalisation item of a classical definition, split off as VII.3.6e (classical, not linked). |
| VII.5.1 | a1 | The BSD card's open step. |
| VII.5.2 | a2 | The ledger form implies BSD and, by Goldfeld, RH for L(E, s): a strengthening that also contains part of GRH's open step. |
| VII.5.3 | a2 | The refined formula: a strengthening of the card's open problem. |
| VIII.1.3c | a1 | The Hodge type in characteristic p is the `weilCard`'s open step `StandardHodge` (VIII.5.2), restated. |
| VIII.1.3d | b (split) | One row, two statuses: C is a theorem (Katz-Messing 1974); B and D in general are open. Split: the C half classical, the B/D half a (d) remainder VIII.1.3g. |
| VIII.1.4a | b (fold) | After the audit's fix it repeats VIII.1.3c (a1) and the B/D half of VIII.1.3d; a duplicate row need not stay open. Fold. |
| VIII.5.1 | a1 | The Hodge card's open step. |
| VIII.5.2 | a1 | The `weilCard`'s open step. |
| VIII.6g | a1 | The reach of the positivity route ends at the Hodge type in characteristic p: VIII.5.2 restated. |
| IX.5e | a1 | No DMP theorem selects Z_6: the GU card's open step (a checkable consequence supplied by DMP) restated. |
| IX.5f | c | The row itself says: the owner's decision. |
| IX.6h | b (correction) | The row reports a search that found no link; the chapter places it under IX.6's all-[reading] header (audit row IX.6h). An observation of absence, not an open mathematical claim. |
| IX.7a | a2 | Route 1, a DMP principle selecting the maximal gluing: a route to the GU card's open step. |
| IX.7b | b (Lean) | Anomaly cancellation is elementary algebra on five rationals; done in Lean (`Closures/Anomaly.lean`). |
| IX.7c | d | Twist sectors of a lattice SU(3) x SU(2) x U(1) with Z_6-invariant vector-like matter: a large extension of the `SUNTwist` chain; not needed by the card. Closed by that extension. |
| IX.7d | b (correction) | The row's own upgrade says "beyond the paper's scope": a scope statement, not an open claim of the paper. |
| X.7g | a1 | The Yang-Mills bridge hypothesis (`SeamTransport`): O1. |
| X.7i | a1 | The GRH bridge hypothesis: GRH beyond Dirichlet. |
| X.7k | a1 | The NP bridge hypothesis (`LiftCPConst`): the constant-gadget lifting. |
| X.64 | a1 | The paper's one assumption. |
| X.9 | a1 | GRH's demand on the tick distance beyond the finite model: the GRH open step. |
| X.14 | a1 | "No known result supplies either edge": the GRH and O1 open steps, side by side. |
| X.46 | a1 | "Which bound is the open step of each card": the two open steps by name. |

---

## 2. Closed rows, ready to apply

Format: the new row (or rows) as they would stand in `CLAIMS.md`, then a note. "Lean" rows cite files added in this round
(section 3); the coordinator applies them after the build log is in. Citations marked "(recalled)" were not re-read for this
round, the ledger's convention for classical references.

### 2.1 Lean closures in this repository

**III.5.9** (decision: O1's one Lean form is `FineOneBox`, the form the one-box assembly consumes; it is per outside, so it
carries III.5.6's quantifier exactly):

| III.5.9 | O1 in one Lean form: `FineOneBox` (one box of the SU(2) Wilson measure at the physical cell scale, influence bounds under every boundary condition, uniform in level and volume). `WilsonOneBox` (the actual DLR kernel) and `FineOneBoxSplit` imply it; it feeds `yang_mills_assembly_onebox`. `BlockGapBddW` is the separate blocking route's decay input and `FineOneBoxPat` an alternative criterion with its own assembly; neither is needed | Lean | `ProofPhase/Closures/OneBoxForm.lean`, `O1Form`, `o1Form_of_wilson`, `o1Form_of_split`, `decay_of_o1Form`, `gap_of_o1Form` | none; reading the number F_e(L) > log mu_4 of III.5.6 as `FineOneBox`'s one-box sum is path counting, paper |

**III.5.7**:

| III.5.7 | Per-box costs multiply over the lattice: with O1 in its per-outside Lean form (III.5.9) the composition of the per-box influences is a theorem, and no annealed quantity enters; the annealed-to-quenched identification is needed only to read a torus measurement of F_e as evidence about O1 (III.7) | Lean | `ProofPhase/OneBox/Fine.lean`, `fineDecayInv_of_fineOneBox`; `ProofPhase/Closures/OneBoxForm.lean`, `decay_of_o1Form`; in the API chain model `ProofPhase/Unified/YangMills.lean`, `pathSum_eq` | none (the open content is O1, III.5.6) |

**III.5.8**:

| III.5.8 | In the transfer-matrix model the chain criterion F_e(L) > 2c(L) and the tube threshold F_e(L) > log mu are independent (examples both ways); the joint form F_e(L) - 2C > log mu, with C bounding the excess act on the multiples of L and mu >= 1 continuations, gives both, and the multiplied path sum mu^k e^{-F_e(kL)} decays at rate F_e(L) - 2C - log mu and is summable | Lean (model) | `ProofPhase/Closures/ChainJoint.lean`, `joint_gives_both`, `tube_not_chain`, `chain_not_tube` | none for the model; turning paths in the cubic geometry are carried by O1's per-outside form (III.5.9), not by the model |

**III.9.5** (split three ways, following the coordinator's reading of the owner's lead):

| III.9.5 | The gap needs of the line of constant physics only its resolution clause (l_k -> infinity): with O1 in its one form it gives torus decay, the gap in both orders of limits and reflection positivity; the running clause, the scheme clause and non-triviality are not used | Lean | `ProofPhase/Closures/OneBoxForm.lean`, `tendsto_a_of_resolution`, `gap_of_o1Form`, `yang_mills_assembly_onebox_of_resolution` | none |
| III.9.5a | Per box, by construction: at every level and volume the reflected correlation at even lattice time is the reflection-positivity square of the centred translate, Z wcorr(2m) = rpForm(F_m - c, F_m - c), hence >= 0; a scale-uniform lower bound c > 0 at a fixed physical time gives `NonTrivial` ("non-trivial" in the project's sense, a non-vanishing correlation, weaker than "not a Gaussian field"); the running clause holds by construction on the one-loop line beta_k = (11/(6 pi^2)) log l_k. Strict per-box positivity (non-degeneracy of the reflection form on the centred translates) is not claimed | Lean (by construction for the per-box parts) | `ProofPhase/Closures/NonTrivialSplit.lean`, `wcorr_even_eq_rpForm`, `wcorr_even_nonneg`, `UniformLower`, `nonTrivial_of_uniformLower`, `oneLoopTuning`, `running_oneLoop` | none |
| III.9.5b | The scale-uniform halves of O2: a lower bound c > 0 on one slab correlation at a fixed physical time, uniform in the cutoff (spectral form: weight >= delta below a mass M, uniformly), and the scheme clause of the line of constant physics. In the spectral model this is the lower edge of the window whose upper edge is O1's gap: not implied by O1 (a gap at every rate with vanishing correlation), not implying it, compatible with it (a state at m <= E < M) | open (relation to O1: Lean, model) | `ProofPhase/Closures/NonTrivialSplit.lean`, `lower_of_spectral_weight`, `gap_not_lower`, `gap_and_lower_compatible`; `ProofPhase/Bridge/Spectral.lean`, `corr_ge`; `ProofPhase/Assembly.lean` (`NonTrivial`, `OnLCP`) | a proof, or the owner's decision to read the one assumption (X.64, "a running system") as including it (class c of the closures round) |

Why the constructions are the natural ones: the per-box identity is the Hankel identity of reflection positivity itself
(`hankel_corr`), the object `NonTrivial` already refers to, not a redefinition; the one-loop line is the standard tuning of an
asymptotically free theory, and the clause it satisfies is about the tuning, not the measure (the content that remains, the
scheme clause, is named in III.9.5b). The owner's lead (non-triviality given by running in DMP as content, constructed per
box) is what III.9.5a carries; the scale uniformity is the part that does not fold into O1 automatically, because O1 is an
upper edge (decay) and non-triviality a lower edge (no collapse).

Knock-on: Part III's (O2) paragraph and III.9's table can say "not an input of the gap; per box by construction; the
scale-uniform lower edge is the remaining identification input".

**VII.3.6d** (split):

| VII.3.6d | The Euler ledger of one given integral curve W (by construction: the ledger is built from the curve, so its counts are the curve's point counts by `rfl`; natural because the step factor N_p/p is defined from these counts): its counts are Mathlib's point counts of W mod p by construction (Hasse for them stays the named input); at every prime of good reduction they are the computed counts of `Arsenal.BSD`, and the step factor is count/p; instance y^2 = x^3 - x at every odd prime | Lean (Hasse as input) | `ProofPhase/Closures/EulerCurve.lean`, `curveCount`, `ofCurve`, `ofCurve_N`, `ofCurve_N_good`, `ofCurve_fac_good`, `E32Euler_N` | none |
| VII.3.6e | That these counts give the linear coefficient of Mathlib's local factor (`WeierstrassCurve.localPolynomial`: minimal model over the completion, its reduction, residue field Z/p) at a good prime is the classical definition of a_p; not linked in Lean | classical (not linked in Lean) | Silverman, AEC, App. C.16 (recalled); Mathlib `WeierstrassCurve.LFunction`; `Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv`, `PadicInt.residueField` | the link, stated and proved |

Knock-on: the chapter's care point (VII.3.6, "[open as a formalisation item]") becomes "[Lean] for the ledger of one curve;
the link to Mathlib's local factor is a formalisation item [classical]".

**IX.7b**:

| IX.7b | Route 2, done classically in Lean: for one generation with the Standard Model representations the four anomaly conditions (SU(3)^2 U(1), SU(2)^2 U(1), gravitational, U(1)^3) have exactly the solutions q = q_Q (1, 4, -2, -3, -6), up to u <-> d, and the degenerate family q_Q = 0; with q_Q > 0 and coprime charges the charges are those of `smFields`, and the centre acting trivially is the Z_6 (composing with `sm_kernel`, `gen_trivial_iff`). The input is a classical theorem, not a DMP one | Lean | `ProofPhase/Closures/Anomaly.lean`, `anomalyFree_iff`, `anomaly_fixes_sm`, `fermion_kernel`, `anomaly_fixes_Z6`; Geng-Marshak 1989; Minahan-Ramond-Warner 1990 | none (the degenerate family is excluded by q_Q > 0, the Yukawa input, stated in the file) |

Knock-on: IX.4.1a can add "Lean: IX.7b"; IX.3.1i drops "the anomaly equations" from its list; the GU card's "External inputs"
row (Part IX, L54) can say "fixed classically by anomaly cancellation (Lean, IX.7b) or by SU(5)". The folded label IX.4.1b
still points to IX.7b. This closes a route, not the GU card's open step (IX.5e, IX.5f).

### 2.2 Lean closure in IM (`proof/`)

**I.10e** (the file is in an IM worktree, branch `closures-arsenal`, uncommitted; the row applies once IM merges it):

| I.10e | Tokens only attenuate (by construction: attenuation is intersection with a caveat, the discipline of Macaroons, Biscuit and SPKI that IM cites, so the subset bound is an unfolding): an attenuated token's kinds are a subset of its parent's; a chain of attenuations is the intersection of the root with its caveats, in any order; along any chain the sentences a door passes only shrink; the empty grant attenuates only to itself (the C# token code is not proved to implement the model) | Lean | `im` repository, `proof/Im/Attenuate.lean`, `attenuate_sub`, `attenuateAll_eq`, `attenuateAll_perm`, `attenuateAll_sub`, `Grants.pass_of_attenuateAll`, `Grants.refuse_of_attenuateAll`, `Grants.attenuate_noGrants` | name the three hypotheses in DMP 04 or 06 (the second half of IM's IF9, the owner's) |

Knock-on: the chapter line (Part I L297, "[open]") becomes [Lean]; `proof/Im/Closure.lean`'s header and IM's
`docs/findings.md` IF9 and `docs/language.md` L116 say "not written yet" and need the same update in IM.

### 2.3 Corrections and citations

**IV.1.5b**:

| IV.1.5b | The explicit formula for Dirichlet and other L-functions, for test functions of class C^2, and Weil's criterion are classical; they are not formalised in Lean here | classical (not in Lean) | Weil 1952 ("Sur les formules explicites de la theorie des nombres premiers"); Bombieri 2000 (recalled); `docs/unified/CONTOUR-SHIFT.md` 5 | formalise them |

**V.1.9** (matches the chapter's "[classical] on paper" and audit row V.1.9):

| V.1.9 | On paper the Dobrushin and spectral-gap results hold for infinite or continuous single-site spaces, with hard constraints, and for systematic scan; in Lean they are not yet unconditional (the gauge-theory instance rests on the couplings and the L^2 spectral theorem as hypotheses) | classical (Lean conditional) | Dobrushin 1968; Georgii, *Gibbs Measures and Phase Transitions*, ch. 8 (general single-site spaces); Salas-Sokal 1997 (hard constraints); Dyer-Goldberg-Jerrum 2008, Hayes 2006 (systematic scan) (recalled); `ITEMS.md` 3 | Lean |

**V.3.11**:

| V.3.11 | No superpolynomial lower bound is known for AC^0[p]-Frege, Frege or extended Frege; best formula lower bounds about n^3 (a statement about the literature; the bounds themselves are open problems outside the card, whose open step is V.4.10) | classical | Hastad 1998; Tal 2014; Krajicek, *Proof Complexity* (2019) (recalled) | none |

**VI.6.3j** (a sketch from classical surgery theory; I recommend an independent read before it goes in):

| VI.6.3j | "Poincare for SU(N)": for N >= 4 false already topologically (H^8(SU(N); Q) is nonzero below the top degree, so surgery realises manifolds homotopy equivalent to SU(N) with p_2 != 0; SU(N) is parallelisable and rational Pontryagin classes are homeomorphism invariants). For N = 3 true topologically (H^*(SU(3); Z) sits in degrees 0, 3, 5, 8, so the normal invariants reduce to the top class, which maps injectively to L_8 = Z, and the structure set is trivial). Smoothly for N = 3 not settled here. N = 2 is Poincare | paper (sketch from classical surgery theory) | Browder, *Surgery on Simply-Connected Manifolds* (1972); Wall, *Surgery on Compact Manifolds* (1970); Kirby-Siebenmann (1977); Novikov 1965 (recalled) | an independent check of the sketch; for N = 3 smooth, the inertia group of SU(3) (class d) |

The argument in full, for the check. Let M = SU(N), n = N^2 - 1 >= 8, simply connected, closed, parallelisable; H^*(M; Z) is the
exterior algebra on classes of degrees 3, 5, ..., 2N - 1, torsion free. Surgery exact sequence (TOP, n >= 5):
S(M) -> [M, G/TOP] -> L_n(1). Rationally [M, G/TOP] is the sum of H^{4i}(M; Q). For N >= 4, x_3 x_5 is nonzero in H^8, with
8 < n. A normal invariant with nonzero H^8 part and suitable top part has zero surgery obstruction (for n odd L_n = 0; for
n = 0 mod 4 the top part compensates the signature), so it is realised by a homotopy equivalence f: X -> M, and the rational
Pontryagin class p_2(X) differs from f^* p_2(M) = 0 (H^4(M; Q) = 0, so p_1 does not change, and the change of the L-class in
degree 8 is the H^8 part). A homeomorphism X -> M would carry p_2(M) = 0 to p_2(X) (Novikov), so X is not homeomorphic to M.
For N = 3: H^2(M; Z/2) = H^4(M; Z) = H^6(M; Z/2) = 0 and H^8 = Z, so [M, G/TOP] = Z from the top cell, and the surgery
obstruction is injective on it (the top-cell normal invariant is detected by L_8 = Z); S^TOP(SU(3)) is a point.

**VIII.1.3d** (split; the open half gets a new row):

| VIII.1.3d | Grothendieck's standard conjecture C (Kuenneth type) holds over finite fields, from the Weil conjectures | classical | Katz-Messing 1974 | none |
| VIII.1.3g | The standard conjectures B (Lefschetz type) and D (numerical equals homological) are open in general (known in special cases, e.g. B for abelian varieties, Lieberman 1968) | open | HODGE 1.4; Lieberman 1968 (recalled) | a proof (class d of the closures round) |

**VIII.1.4a**: fold into VIII.1.3c and VIII.1.3g (after the audit's fix it lists exactly "B in general; D; the Hodge type in
characteristic p"). Add to "Folded labels": `VIII.1.4a | VIII.1.3c, VIII.1.3g`. Chapter VIII.1.4 can keep its sentence with
the two references.

**IX.6h** (audit row IX.6h makes the same point):

| IX.6h | SU(2) as the stable Ricci-flow profile (Part VI.6) has no found link to the global form Z_6 | paper (observation; under IX.6's readings) | GU 3.3 | a link |

**IX.7d**:

| IX.7d | Route 4: a statement about running couplings needs the continuum theory with matter | (statement of scope) | GU 6, item 4 | beyond the paper's scope |

### 2.4 A bonus closure that is not an open row

**The Euler product bound over Q** (`EulerProductBound ℚ`, IM `arsenal/Arsenal/BSD/EulerRat.lean`, same IM worktree): if its
build passes (section 3.3), for curves over Q only `Hasse` stays named in VII.3.4d and VII.3.5d.

| VII.4d | Euler products with Hasse-type coefficient bounds converge absolutely for `re s > 3/2`, dominated by `zeta_K(s - 1/2)^2`: proved over Q (the factor at p_v has q_v = p_v and v -> p_v is a bijection onto the primes); for a number field of degree > 1 a named part | Lean over Q (IM); classical (recalled) beyond | `Arsenal.BSD.EulerRat`, `eulerProductBound_rat`, `abs_eulerProduct_le`, `lseriesSummable_eulerProduct_primes`, `card_residueField_rat`; `Arsenal.BSD.Hasse`, `EulerProductBound` | a Lean proof over number fields (q_v = p^f, several v over one p) |
| VII.3.4d | From the named part Hasse (and, beyond Q, the Euler product bound): absolute convergence for `re s > 3/2`, a finite order at s = 1, and parity with no order given separately | Lean (from the named parts) | `Arsenal.BSD.Hasse`; over Q `Arsenal.BSD.EulerRat`, `LSeriesSummable_of_hasse_rat`, `order_ne_top_rat`, `analytic_parity_of_hasse_rat` | a Lean proof of Hasse |

---

## 3. Lean files added, build and axiom results

### 3.1 This repository (`docs/mass-gap/formal/ProofPhase/Closures/`)

Five files (the fifth, `NonTrivialSplit.lean`, added after the coordinator's request on III.9.5):

| File | Closes | Main declarations |
|---|---|---|
| `Anomaly.lean` | IX.7b | `AnomalyFree`, `anomalyFree_iff`, `anomaly_fixes_sm`, `fermion_kernel`, `anomaly_fixes_Z6` |
| `OneBoxForm.lean` | III.5.9, III.5.7, III.9.5 | `O1Form`, `o1Form_of_wilson`, `o1Form_of_split`, `decay_of_o1Form`, `gap_of_o1Form`, `yang_mills_assembly_onebox_of_resolution` |
| `ChainJoint.lean` | III.5.8 | `joint_gives_both`, `tube_not_chain`, `chain_not_tube` |
| `EulerCurve.lean` | VII.3.6d | `curveCount`, `ofCurve`, `ofCurve_N`, `ofCurve_N_good`, `ofCurve_fac_good`, `E32Euler_N` |
| `NonTrivialSplit.lean` | III.9.5a, III.9.5b (relation to O1) | `wcorr_even_eq_rpForm`, `wcorr_even_nonneg`, `UniformLower`, `nonTrivial_of_uniformLower`, `lower_of_spectral_weight`, `gap_not_lower`, `gap_and_lower_compatible`, `oneLoopTuning`, `running_oneLoop` |

Axiom script: `docs/unified/closures-axioms.sh`; log: `docs/unified/closures-axioms.log`.

Result (2026-11-24, `bash docs/unified/closures-axioms.sh`, build folder `~/formal-close` with a private copy of the packages):
all five modules build (`Build completed successfully`); **81 declarations, with a non-standard axiom: 0**; no sorry / admit /
native_decide / axiom in `ProofPhase/Closures`. Log: `docs/unified/closures-axioms.log`.

### 3.2 IM `proof/` (worktree `C:\claude\im\.claude\worktrees\closures-arsenal`, branch `closures-arsenal`, nothing committed)

`proof/Im/Attenuate.lean` (new) and one import line in `proof/Im.lean`.

Result (2026-11-24, in a Linux clone of IM at `e1e95bd` with the two files applied): `proof/tools/check.sh` passes end to end:
pins of `vendor/dmp` and `vendor/gravity` OK, setup check OK, `lake build` OK, **59 theorems, none resting on more than propext,
Quot.sound, Classical.choice**, table of 32 shapes matches. The 16 new theorems: `attenuate_sub`, `attenuate_sub_caveat`,
`Perms.sub_trans`, `attenuate_mono`, `attenuateAll_eq`, `attenuateAll_perm`, `attenuateAll_sub`, `Grants.attenuate_sub`,
`Grants.sub_trans`, `Grants.attenuateAll_sub`, `Grants.pass_of_sub`, `Grants.pass_of_attenuated`, `Grants.pass_of_attenuateAll`,
`Grants.refuse_of_attenuateAll`, `Grants.attenuate_noGrants`, `decide_is_verdict` (each on a subset of the three).

### 3.3 IM `arsenal/` (same worktree)

`arsenal/Arsenal/BSD/EulerRat.lean` (new) and one import line in `arsenal/Arsenal.lean`.

Result (2026-11-24, in `~/arsenal-close`, a CR-stripped copy of the worktree's `arsenal/`): `tools/lint.sh` OK (8 modules,
Mathlib v4.34.0 only, no escape hatch; the R136a1 list still names "Euler product bound", because the general number-field
statement stays named), `tools/lint-selftest.sh` OK, `tools/check.sh` OK: **100 declarations, none resting on more than
propext, Quot.sound, Classical.choice**, among them `eulerProductBound_rat`, `card_residueField_rat`,
`LSeriesSummable_of_hasse_rat`, `order_ne_top_rat`, `analytic_parity_of_hasse_rat`. IM's `tools/scrub-scan.sh` is clean with
both new files staged (in a throwaway clone). One linter note (a `haveI` where `have` suffices), no warning of substance.

The other two named parts, weak Mordell-Weil and Hasse, were not attempted: Hasse needs isogeny degrees or intersection theory
on E x E (not in Mathlib); weak Mordell-Weil needs the Kummer map into a finite Selmer-type group and the finiteness of class
groups and unit groups modulo squares over the 2-division field, several thousand lines on today's Mathlib by the estimate of
VII.4h. Both stay named (R136a1).

### 3.4 A build incident, and a script bug it exposed

The brief's setup links `~/formal-close/.lake/packages` to `~/formal/.lake/packages`. `sync-build.sh` decides whether to run
`lake update arsenal` by reading the arsenal rev from `lake-manifest.json` with `grep -A6 '"name": "arsenal"'`; in the
manifest the `rev` line comes *before* the `name` line, so the read is always empty and every run calls `lake update arsenal`
(and the Mathlib cache step). My first closures build therefore ran `lake update arsenal` through the link into `~/formal`'s
packages. I stopped it within about a minute and checked: `~/formal/lake-manifest.json` is unchanged and no file under
`~/formal/.lake/packages` is newer than the start of that run. All later builds used a private copy of the packages
(`cp -a`, no link). Follow-up for the coordinator: fix the rev read in `sync-build.sh` (e.g. match the `"rev"` line inside the
arsenal block, or use `jq`), and change the brief's setup from a link to a copy.

---

## 4. For the owner (class c)

*Answered by the owner on 2026-11-24 (`PREP.md`, "Five answers"): 1, uniform charge quantisation with the ODP's guarantee (IX.5f,
reading); 2, DMP-complete means runs on DMP (X.64b; VI.7e's second half stays open); 3, reading (i), the lower edge is part of the
one assumption (X.64a); 4, the headline carries the excess act, F_e(L) - 2c(L) > log mu_4. VI.6.3j waits for a Perelman-style
round and an independent read.*

1. **IX.5f, the GU gate.** Whether candidate (a), candidate (b), or "well-defined inputs, guaranteed" meets the gate's "at least
   one checkable consequence". Unchanged by this round; IX.7b (now Lean) makes the hypercharge input a classical theorem, which
   is relevant to candidate (b) but does not decide it.
2. **VI.7e, DMP-completeness.** Whether DMP-completeness has a precise statement that Navier-Stokes violates and from which
   blowup follows. It first needs a formal definition of DMP-completeness; that definition is yours. Once it exists, the
   question is a route to the blowup side of the NS card (class a2).
3. **III.9.5b, the scale-uniform lower edge.** Non-triviality per box is now Lean (by construction), and a uniform lower bound
   gives `NonTrivial`. The uniform bound itself is separate from O1: O1 is the upper edge (a gap, decay), non-triviality the
   lower edge (the correlation does not collapse), and the model shows neither implies the other while both fit one window.
   Two honest readings: (i) the one assumption "the one box is a running system" (X.64) includes the lower edge, since a
   system that runs does not collapse; then III.9.5b folds into it and Part X 4.4 says so; (ii) it does not, and III.9.5b
   stays an open identification input beside O1. This is the wording of the one assumption, so it is yours.
4. **A wording choice that follows from III.5.8 (not a row).** III.5.6 states O1 as F_e(L) > log mu_4. The model shows that
   the statement which gives both the chain and the tube is F_e(L) - 2c(L) > log mu_4 (the cost after the excess act). The
   Lean form chosen for III.5.9, `FineOneBox`, is neither number; it is the per-outside one-box sum. Whether the paper's headline
   number for O1 stays 1.91, or is restated with the excess act, is yours. This round changes no chapter.

---

## 5. Genuinely open, not O1-type (class d), and what would close each

| Row | Why it cannot be closed now | What would close it |
|---|---|---|
| VI.4.4c | Independence of ZFC is a meta-question about an open problem; nothing about it is known, and the card does not use it. | A proof of regularity, of blowup, or of independence. |
| VI.5.3 | What a blowup solution continues as past T* depends on uniqueness of weak continuation, which fails in general for weak solutions (Buckmaster-Vicol type non-uniqueness, recalled). | A uniqueness theorem in a class that contains the continuation, e.g. a suitable-weak-solution class adapted to the profile. |
| IX.7c | Twist sectors of a lattice SU(3) x SU(2) x U(1) theory with Z_6-invariant vector-like matter is a large extension of the `SUNTwist` chain (U(1) factor, matter fields, mixed twists). | That extension, in Lean; chiral matter remains out of reach (lattice chiral fermions). |
| VI.6.3j, smooth N = 3 (split off) | The topological answer for SU(3) is yes; smoothly it depends on whether SU(3) # Sigma^8 (Sigma^8 the exotic 8-sphere) is diffeomorphic to SU(3), i.e. on the inertia group of SU(3), not found. | A computation of the inertia group of SU(3) (and of the smooth structure set). |
| VIII.1.3g (split off) | The standard conjectures B and D are open in general (Grothendieck's standard conjectures). | A proof; known cases are special families. |

---

## 6. What is left, in one paragraph

After this round the open rows of the ledger are the seven cards' open steps and their restatements (31 rows, a1), the routes
to and strengthenings of the same open problems (9 rows, a2), two owner decisions (IX.5f, VI.7e) and five genuinely open side
questions (three rows plus two split-off remainders), none of which the paper needs; III.9.5b (the scale-uniform lower edge of
O2) is folded into the one assumption or stays an identification input, by the owner's reading. In particular the Yang-Mills card no
longer carries open care points beside O1: the annealed-to-quenched step (III.5.7), the chain/tube relation (III.5.8) and the
choice of O1's Lean form (III.5.9) are closed, and the line of constant physics is no longer an input of the gap (III.9.5); non-triviality holds per box by construction
(III.9.5a).
