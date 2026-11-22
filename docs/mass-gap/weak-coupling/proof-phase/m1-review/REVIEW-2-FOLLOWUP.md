# M1 referee review 2, follow-up (adversarial), 2026-11-22

Scope: whether the findings of `REVIEW-2.md` (G1-G6, F7, N1-N3) are fixed by the revision. Read for this:
`../m1-tools/REVIEW2-RESPONSE.md`, `S1-CURRENT.md`, `WRITEOUTS.md`, the updated sections or update notes of
`DECODER-LOCAL.md`, `FILL.md`, `HANDOVER.md`, `R10-SCOPE.md`, `CLOSE-OUT.md`, `REGULAR.md`, `EXTERNAL.md`, `M1-PLAN.md`
section 0, and the row structure of `formal/ProofPhase/M1/Assembly.lean`. Nothing was built or re-run.

## Verdict

The revision is honest and substantive. The author agreed with every finding and repaired G3 and G6 with the right
objects. The decoder is now a maximum-weight packing with a Peierls bound over conflict chains, which I checked, and
holes are capped by the number of layers, not their extent. Labels are no longer carried as large-field regions, which
removes the divergence of G2. But the final verdict in `M1-PLAN.md` 0 ("a complete argument at paper level") still
overstates what is written:
* `S1-CURRENT.md` calls itself an outline;
* the label factorisation needs a relative bound that the Mayer-expansion route does not give;
* the small-field definition at the bare scale is now wrong as stated;
* G4 has been moved to a density claim ("by martingale convergence") that is a real continuum-limit statement, not a
  routine step, and that M1's own erasure of sub-block centre flux makes doubtful for fundamental-representation
  observables.

No finding is FATAL. G1, G2 and G4 remain GAPs in reduced or moved form; G5 is open by design (interface).

## Status of the REVIEW-2 findings

| finding | status | reason |
|---|---|---|
| G1 no S1 for the current design | **partly resolved** | see G1 below |
| G2 labels fit neither half of the form | **resolved in design, open in proof**; one new problem introduced | see G2 below |
| G3 decoder locality estimate false | **resolved in substance**; residual FIXABLE | see G3 below |
| G4 hand-over / RP upgrade on tori | **conceded, then relabelled**; new GAP | see G4 below |
| G5 SU(2) encoding not covariant | **still open** (moved to the interface by design) | see G5 below |
| G6 extended holes | **resolved** (paper sketch) | see G6 below |
| F7 Lean rows stale; signed/complex densities | **mostly resolved** | rows renamed; complex extension stated on paper; docstrings stale (NIT) |
| N1 R7 normalisation | **resolved in substance** | `poly(beta)` per flip; `M1-PLAN.md` R7 row not updated (NIT) |
| N2 twist sectors | **resolved** | `DECODER-LOCAL.md` 6.4 withdrawn |
| N3 smaller points | **resolved**, with stale text left in `M1-PLAN.md` | rate (0.31) added to `EXTERNAL.md` row 1 with the 33 % / 11 % margins; `r >= 2` pinned; gauge selection in `FILL.md` |

### G1. One-step induction: partly resolved

`S1-CURRENT.md` states `Form_k` for the law of `(V_k, tau'_k)` (items F-a to F-g) and gives a one-step table with the
deltas against Balaban. That is the right shape, and it supersedes the trapping-era S1 explicitly. But:
* by its own words it is a "paper outline with explicit deltas". The E-rows are asserted to change "none beyond SO(3)
  constants" rather than re-checked: for example E5-E9 "hold as Balaban's, with the deltas of section 2", and E6
  "fillings analytic in the data where used";
* `M1-PLAN.md` 0 then lists `S1-CURRENT.md` under "paper" and concludes "complete argument at paper level", which is a
  higher level than the note claims for itself;
* `Form_k` places the label factors `a_ell (1 + h_ell)` outside `T_k(Z_k)`, but labels are extracted from polymers of
  `T`-operations at release (`WRITEOUTS.md` 1); how the two representations match at the release step is not written;
* the small-field item (F-c) has the bare-scale problem described under G2 (N-1).

Severity now: GAP (reduced: the structure exists, the line-by-line check does not). Confidence: high.

### G2. Labels as decorations: resolved in design, open in proof, plus one new problem

What is fixed: labels are no longer regions, so they are not charged Balaban's per-step entropy and do not need
(1.76) or (1.80). The divergence I computed no longer applies. The count per coarse bond (`e^{-16/g_k^2} L^{(1-16b)k}
poly`) and the parity sum of `WRITEOUTS.md` 1 step 4 are correct.

What is not yet proved:
* **The multiplicative form needs a relative bound.** Step 2 of `WRITEOUTS.md` 1 writes the labelled activity, times
  the cluster terms meeting it, as `a_ell (1 + h_ell(V))` with `h_ell` "analytic, local and small". Balaban's polymer
  bounds ((1.92)-(1.97)) are absolute upper bounds on signed activities. They give no lower bound on
  `|F_ell(Y; V_ref)|` relative to its variation in `V`. Without that, `h = F/F(V_ref) - 1` need not be small, and
  `log(1 + h)` need not exist.
* **Likely repair.** Extract the label before the Mayer expansion, where the labelled `T`-integral is a positive
  integral. Then:
  * Balaban's analytic-extension bounds (1.73)-(1.75) give relative control of its `V`-dependence;
  * R8's lemma (no linear coupling) turns that into `|h| <= C eps_k^2 L^{-4(k-j)}`.
  
  This is plausible, but it is not what is written.
* **New problem (N-1): the bare-scale small-field definition.** `S1-CURRENT.md` (F-c), the amended R9 row
  (`CLOSE-OUT.md` update) and `M1-PLAN.md`'s R9 row now define small field as SO(3)-regular, with no condition on
  `tau`. Only `REVIEW2-RESPONSE.md` 2 says "at scales >= 1".
  * At scale 0 that is wrong. A thin closed vortex sheet with `U_p ~ -1` is SO(3)-flat. Under the SO(3)-only rule it
    would be "small field" at the bare scale, where the Tomboulis weight `exp(-(beta/2)|tr U_p|)` has the wrong sign
    (`ROUTE-B.md` 0.4). Its suppression (`2 beta` per plaquette) would never be booked as a large-field factor, and the
    label would never pass through a release step to receive its `a_ell`.
  * Fix: keep SU(2)-regularity (`tau = +1`) at scale 0, and use SO(3)-regularity at scales `>= 1` only. State it in
    (F-c), in the R9 row and in `M1-PLAN.md` 0.
  * Also, item 3 of the main line in `M1-PLAN.md` 0 still says "the Z2 background is `+1` in small-field regions",
    which contradicts the amended R9.
* **Minor:** `WRITEOUTS.md` 1 says labels are created "only during the first O(window) steps". They are decided at
  step 0 but extracted at their region's release, which can be up to `n0 + R_0` steps later (`R_0 >= (log g^{-2})^2`),
  not within the window. This is harmless, because `a_b` is bounded with the bare `beta`, but the text is wrong.

Severity now: GAP (reduced; the design is consistent once N-1 is fixed, and the missing piece is one relative-bound
argument). Confidence: medium-high.

### G3. Decoder locality: resolved in substance

Checked:
* the decoder is a maximum-weight packing of positive-gain closed connected sets (gain additivity over disjoint
  components);
* it decomposes over the components of the conflict graph, with the tie-breaks additive (`|sigma|`) or chosen per
  component;
* in a shortest conflict path each plaquette lies in at most two consecutive members (otherwise there is a shortcut).
  So the union `U` is connected, with `|tau ∩ U| > |U|/4` and `|U| >= r`;
* the Peierls sum `(2C_d)^u (c beta^{3/2} e^{-beta})^{u/4}` converges for large bare `beta`, uniformly in the volume;
* no percolation; the merging rule is withdrawn.

Residual (FIXABLE): the component `U(q)` is not a stopping set. The event "the conflict component of `q` is exactly
`U`" requires that no positive-gain set touching `U` extends outside it, which depends on `tau` outside `U`. So the
statement "the label pattern of a polymer is a deterministic function of the configuration inside it"
(`WRITEOUTS.md` 1 step 1) and the "enlargement of Balaban's regions by conflict components" (`REVIEW2-RESPONSE.md` 1)
need one more step. Either expand the constraints "`g(S) <= 0` for sets crossing the boundary" as a convergent
correction (each violating set is Peierls-suppressed), or use a local surrogate decoder plus a Peierls-small
discrepancy event. Standard, but not written. Confidence: high on the repair, medium that the residual is routine.

### G4. Hand-over: conceded, then relabelled; new GAP

Points 1-4 of REVIEW-2 G4 are accepted in full. `TorusDecayLoc` is no longer claimed, and the RP upgrade is moved to
the limit theory. `WRITEOUTS.md` 2 writes the UV transfer for character polynomials of **M1 block variables** at a fixed
physical scale `ell`, in `L^1`, with constants `C(n, R/ell)` uniform in spacing and volume. Its structure is sound,
with one NIT:
* the "event" `E_D` (a large-field region of `Z_K` joining `A` to distance `D/2`) is a summation index of Balaban's
  representation, not an event of the configuration (as `R2-REPAIR.md` 1 itself notes);
* the `L^1` bound should be done with the positive partition (characteristic functions before the Mayer expansion):
  `|E[F|V] - E_nc[F|V]| <= 2 rho_c/rho`, whose `L^1` norm is the mass of the crossing terms;
* this is easy, but the written "on `E_D` / on `E_D^c`" split of a conditional expectation is not literally
  meaningful.

**New GAP: the density claim** (`REVIEW2-RESPONSE.md` 5(c), `HANDOVER.md` update, `M1-PLAN.md` 0 "`MassGapLoc` via
the limit"). The route needs `∪_ell D_ell` to be dense in the limit OS space, "by martingale convergence as
`ell -> 0`". This is not routine:
* **Martingale convergence is per lattice.** On a fixed lattice it gives `E[F | F_ell] -> E[F | bare state]` as `ell`
  decreases to `a`, with the noise of all finer steps included so that the sigma-algebras increase. The limit OS space
  is a limit `a -> 0`. Density there needs `||F - E[F | F_ell]|| -> 0` as `ell -> 0` **uniformly in `a`**: a UV
  regularity statement about the continuum limit, of the same kind as the transfer bound it was meant to replace.
* **M1's state at scale `ell` deliberately forgets centre flux below `ell`.** Thick-born sheets are erased once they
  are thinner than a block (`BYPASS.md` 1), and thin ones are absorbed unless closed and of positive gain. For a
  fundamental Wilson loop `C` of physical size `R > ell`, the sign contributed by such vortices linking `C` is
  therefore not `F_ell`-measurable.
  * Whether their expected number linking `C` goes to 0 as `ell -> 0`, uniformly in `a`, depends on the minimal action
    `c0/g^2` of a closed Z2 sheet against `1/b ~ 10.8` (the same comparison as `CLOSING.md` 2, now for thick sheets).
  * `MILESTONE-1.md` found no minimum at finite thickness, and nothing in M1 bounds `c0`.
* **If density fails, the gap is shown only on part of the space.** If the closure of `∪ D_ell` is a proper subspace,
  the upgrade gives the gap only on that subspace, and fundamental-representation observables are not covered.
* **The assembly does not exist yet.** The per-observable decay of limit correlations at one rate (from P4), the
  interchange of limits, and an assembly that concludes `MassGapLoc` without `TorusDecayLoc` are all new and outside
  M1 (acknowledged).

Severity: GAP (the burden moved, not removed). Confidence: medium-high that the density step is non-trivial; medium on
whether it can fail.

### G5. SU(2) encoding: still open, by design

The response agrees and proposes none. The block state should be `(SO(3), closed Z2)` with gauge-invariant
observables, and P4 and the one-box route restated for it. That is a coherent decision, but it is a change to P4, the
core open problem, not just to an interface. A strong-coupling crossover must now be proved for a state in which
centre flux below `L_*` has been erased.

The proposed Wilson loop `W(C) = (prod_S tau'_p) · 1/2 tr(lift of Hol_V(C))` uses a canonical lift "where `Hol_V(C)` is
regular". For large loops the SO(3) holonomy is generically not near the identity, so the lift branch is ambiguous
there. It is also not `E[W_C^{fine} | state]` (see the density point in G4). Status: open (outside M1, but it bears on
whether M1's output is the right input for P4). Confidence: medium.

### G6. Extended holes: resolved (paper sketch)

Capping the number of layers per component (components merge when they touch) makes the rule deterministic. Thin
centre sheets become twist-free after `O(1)` layers, because short loops see `Ad(-1) = 1`.

The filling of a slab of thickness `w` with Dirichlet gap `(pi/w)^2` and exponentially decaying Green's function along
the slab is the right mechanism. I also checked that there is no topological obstruction: a closed centre sheet has
`d tau = 0`, so no monopoles, and the SO(3) bundle on its tubular neighbourhood is trivial for a trivial normal
bundle, so a regular filling exists.

Thin slabs (`w = O(1) < L`) never swallow a whole block face, so R4 holds as stated. The implicit-function argument
in sup norms is described, not written ("the same structure as [15] Sect. C-E"), which fits the "paper sketch" level,
not "paper". Confidence: medium-high.

## New findings in the revised text

* **N-1 (GAP, fixable):** small-field definition at the bare scale (G2 above).
* **N-2 (GAP):** the density claim for `∪ D_ell` (G4 above).
* **N-3 (FIXABLE):** the label factorisation needs a relative bound (G2 above).
* **N-4 (FIXABLE):** decoder components are not stopping sets (G3 above).
* **N-5 (NIT):** `E_D` is a summation index (G4 above).
* **N-6 (NIT): stale or inconsistent text.**
  * `M1-PLAN.md` 0 still has:
    * main-line item 3 ("Z2 background `+1` in small-field regions");
    * the R4 row ("needs R11 to allow it", although `RandBlocking.lean` exists);
    * the R7 row ("`O(1)^{|tau|}`, Jensen");
    * the R11 row ("SU(2) encoding of `(V, tau)`", which G5 withdrew);
    * a "Paper sketch" list naming R10 and the swallowed-bond compactness argument, while the final verdict lists R10
      as paper and the swallowed bonds are randomised;
    * "Lean: ... the record gas", which is off the line.
  * `Assembly.lean`'s module docstring (lines 15, 33, 39) still refers to `TRAP.md`, `P0.md` and "D-mod, TRAP, P2',
    P4", though the rows themselves were renamed.

## What I checked and found sound in the revision

* The conflict-graph Peierls argument (`REVIEW2-RESPONSE.md` 1), including the multiplicity-two property of shortest
  conflict paths.
* The parity formula for decorations per coarse bond (`WRITEOUTS.md` 1 step 4) and the label count.
* The split "cluster expansion on a subset = full expansion minus the clusters meeting the removed set"
  (`WRITEOUTS.md` 1 step 2).
* R10's scale choice (polynomials in block variables at a fixed physical scale). It makes the constants independent of
  the lattice spacing, which the fine-link version could not.
* The rate (0.31) row in `EXTERNAL.md` and the pinned exponent `r >= 2` (`REGULAR.md` update).

## Could not check

* Balaban's (1.73)-(1.75) as applied to labelled `T`-integrals (the repair proposed for N-3).
* The slab filling line by line.
* Whether the minimal action of a closed Z2 sheet exceeds `1/b` (bears on N-2). This is a physics question outside the
  notes.

## Second follow-up (part 1)

Read for this: `../m1-tools/REVIEW3-RESPONSE.md` (sections 1-5) and the update notes in `DECODER-LOCAL.md`, `FILL.md`,
`WRITEOUTS.md`, `S1-CURRENT.md`, `CLOSING.md`, `CLOSE-OUT.md` and `M1-PLAN.md` 0. I re-read [V] pp. 379-380
((1.73)-(1.75) and the first-order bound before them) and pp. 388-391 ((1.92)-(1.97), (1.103)-(1.104)) in the extracted
text layer of the local PDF. REVIEW-3 itself was not read, to keep this check independent.

### Verdict (part 1)

* **N-1: resolved.** At scale 0 small field now means SU(2)-regular, which is exactly the fix I asked for, and section
  1.1 of the response derives it exactly.
* **G3 residual: resolved by a change of the blocking.** The new decoder is local by definition, and its stopping-set
  property holds.
* **G2: much improved.** Extracting the label before the expansion, as a positive factor with relative stability in the
  complex directions, is the right mechanism, and the bound it rests on follows from positivity. But the carrying
  argument for labels that survive to `L_*` (section 4.4) contains one undercounted sum and leans on (1.103) for more
  than (1.103) gives. That is one reduced GAP.
* The withdrawal of the "complete at paper level" verdict in `M1-PLAN.md` 0 is right.

No FATAL finding.

### N-1 (small field at scale 0): resolved

* `S1-CURRENT.md` (F-c), the R9 rows and `M1-PLAN.md` 0 now say: SU(2)-regular at scale 0, SO(3)-regular from scale 1
  on.
* The exact observation of section 1.1 is correct, and I checked it:
  * given the SO(3) field, the Z2 layer is a Z2 gauge theory with couplings `(beta/2)|tr U_p|`;
  * flipping `tau` on a closed set `S` costs `exp(-beta sum_S |tr U_p|)`;
  * since `|tr U_p| = 2 cos(phi_p/2)`, this inverts the SO(3) quadratic term on `S` (`e^{-2 beta} e^{+beta phi^2/4}`).
  
  It is the precise form of ROUTE-B 0.4 and justifies the rule.
* Every flip (`tr U_p < 0`, operator distance `>= sqrt 2` from the identity) now lies in Balaban's scale-0
  large-field set in every term, and is charged its own action. The split `p0^2 + (1 - delta) beta` per flip, with
  `delta = p0^2/beta`, is consistent: no action is used twice, and the label exponent becomes `16 b (1 - delta)`, a
  negligible loss.

### G3 residual (decoder components not stopping sets): resolved by redesign

* **The new decoder.** It runs per connected component `C` of the union `D_0` of the `M R_0`-cubes that contain a bare
  flip, and packs only closed positive-gain sets contained in `C`.
* **Local in the sense Balaban needs.**
  * The output on `C` is a function of `tau` on `C`.
  * The event "`C` is a component of `D_0`" depends only on `tau` on `C` and on the adjacent cubes (which must be
    flip-free). It is a product of per-cube indicators, so it is a stopping set.
  * By N-1 every flip cube lies in Balaban's scale-0 large-field domain, so `C` lies inside one component of `Z_0`, and
    the decoder is a function of that component's integration variables.
* **What is kept.** The label count (each chosen set has positive gain, at least 4 flips for the smallest), the
  absorption of lone flips and measurability all carry over.
* **What changes, and where it goes.**
  * Covariance is now only under shifts of Balaban's grid, as for his own domains.
  * Real thin closed sheets that leave `D_0` (an unflipped stretch longer than `M R_0`) are absorbed rather than
    labelled. This is a loss of fidelity, not of correctness, and it belongs to N-2, which is correctly deferred.
  * `D_0` is sparse: per `M R_0`-cube the expected number of flips is `(M R_0)^4 e^{-beta_0} poly << 1`, so
    components of `D_0` have cube-animal tails.

### G2 (labels): mostly resolved; one reduced GAP

**What is now right.**
* **Labels extracted before the expansion.** At release, `T_k(X)` is split by label pattern before the Mayer
  expansion, into positive operations, and `Phi_ell(X; V) := T^ell_k(X) 1 > 0` (P1).
* **(P2) is sound.** From [V] p. 379: the integrand of `T_k(X, (U, J))` is the positive real integrand at `(U, 0)` times
  `e^{Delta}`, with `Delta` the small first-order term. Then for `F = 1_ell >= 0`,
  `|T(U, J) 1_ell - T(U, 0) 1_ell| <= (e^{sup|Delta|} - 1) T(U, 0) 1_ell`. This follows from positivity alone, and
  (1.75) is the ratio form of the same thing.
* **No smallness of a constant prefactor is needed.** The earlier `a_ell (1 + h_ell)` form is abandoned.
* **The count (P3)** is consistent with N-1's action split.

**What is not yet right.**

1. **The carrying sum is undercounted (section 4.4).**
   * The response bounds the total change of a label factor over all later steps by
     `exp(C sum_{k'} (delta_{k'} + c1) |X_{k'}|) <= exp(C |X| + C' sqrt(K) polylog)`, "since `|X_{k'}|` shrinks by
     `L^{-4}` per step".
   * But a domain cannot shrink below one cube. A label on a bond of the deep coarse skeleton survives up to `K` steps,
     so `|X_{k'}| >= 1` for all of them, and the `c1` term gives at least `C c1 (K - k)`, linear in `K`.
   * The `delta_{k'}` part does give `sqrt(K) polylog` (`delta ~ g polylog`, `sum_j (b j log L)^{-1/2} ~ sqrt(K)`), which
     is harmless against `L^{(1 - 16b')k}`.
   * The `c1` part is harmless only if the attached-cluster constant is itself summable over scales, for example of size
     `e^{-p0(g_{k'})}` as in R8's sum. Otherwise it is a per-step cost: the bound closes only under a rate condition
     `C c1 < (16 b' - 1) log L`. That is the P3 rate condition of `D-PIN.md` in a weak form, with a constant instead of
     a polylog.
   * Which case holds depends on what `c1` is for clusters attached to a fixed domain in a small-field neighbourhood.
     The response does not say.
   * Note that the response also drops R8's dimension-4 argument for labels ("not needed"). That argument is exactly
     what would make the attached clusters cancel against the vacuum ones and be summable.
2. **(1.103) covers less than it is cited for.**
   * In [V] (1.103)-(1.104), Balaban's fixed domains `Y_i` "are still large field domains", carrying characteristic
     functions. They stay part of `Z` and are governed by (1.80)-(1.83) at later steps.
   * The labelled domains of the response are not large-field domains after release: the SO(3) field there is regular.
     So (1.103) supports only the one-step convergence of the Mayer expansion with fixed domains (no tree decay needed
     for them). It does not support their treatment at later steps, which rests entirely on section 4.4's own argument
     (point 1).
   * The response should say this, and state what a labelled domain is in `Form_{k'}` for `k' >` release: neither a
     large-field domain nor an E/R-term.
3. **The relative bound along real directions.**
   * Section 4.4 writes `Phi_ell(V_k) = Phi_ell(U_bg)(1 + eta(B))` for the real fluctuation `V_k = U_bg e^{i g B}`. That
     compares two real configurations, so the statement in 4.3/4.4 that "real backgrounds are never compared" and "the
     real oscillation of `Phi_ell` is never needed" is not accurate.
   * The bound is available if Balaban's first-order expansion around a regular `U` is in both the real and the complex
     deviation (the text layer says "first order in `A'`, `J`", which supports this) over the next step's fluctuation
     domain. Then the same positivity argument covers real deviations of size `g|B|`.
   * Citation-level and plausible, but the citation should say that `A'` covers the real fluctuation, and the wording
     should be corrected.
4. **Per cube or per component.** The author's own open point (is `delta_k` per `M R_k`-cube or per component?) stands.
   * The displayed bound before (1.73) carries `M^d R_k^{d+2}`, which looks like a per-cube volume factor.
   * The remark "the resummed expression has the same bound" for `V(X~)` is ambiguous.
   * The case split (small components released, large ones carried until `delta |X| <= 1/4`) covers both readings, so
     this is not a gap, only a check.

Severity of the remaining G2 point: GAP (reduced). Confidence:
* high that the sum in 4.4 is undercounted as written;
* medium on whether `c1` is summable (I could not pin it in the text layer);
* medium-high on point 2.

### Smaller observations on part 1

* **H6 (per-flip normalisation): consistent with my N1.** The withdrawal of `f(P) <= |P|/6` and the rank-count exponent
  `beta^{3/2}` per removed plaquette are what I would expect. The ratio stays at citation level, as stated.
* **Label lifetime: corrected.** Labels are decided at scale 0 and extracted at the release of their component, up to
  `n0 + R_0` steps later (section 4.2). This matches my earlier note.
* **New NIT: "an upper bound, not a closed form".** The response says the parity sum of `WRITEOUTS.md` 1 step 4 is now
  only an upper bound (labelled domains have a hard core). That is fine for the count, but `Form_k`'s sum over
  `ell ~ tau'` must then be written as a hard-core polymer sum over labelled domains, not as a product over coarse
  bonds. It should go into the part-2 rewrite of `S1-CURRENT.md`.

## Third follow-up

Read for this: `../m1-tools/REVIEW3-RESPONSE.md` sections 7, 8, 9, 11 and 12; `S1-INDUCTION.md` in full; `M1-PLAN.md`
0 (new verdict and the five sketch points); and the definition of `MassGapLoc` (`formal/ProofPhase/Objects.lean` 470-481)
to check what the density argument has to deliver. REVIEW-3 and its follow-ups were not read. Nothing was built.

### Verdict (third follow-up)

* **G2: the carrying sum is resolved in substance.** The one-box contraction is the right mechanism: a gauge-invariant
  term at a point with no linear coupling is irrelevant and shrinks by about `L^{-4}` per step. The bound on the
  weight over a label's life no longer depends on `K`. One detail in the proof (the localisation tails) needs
  tightening or one more condition on the constants.
* **G1: resolved at the level it claims.** `S1-INDUCTION.md` is now an induction with an order of constants, not an
  outline.
* **The parity NIT: resolved,** but it introduces a small new inconsistency: a hard core that cannot persist across
  scales.
* **G4/N-2: relabelled, not resolved.** Section 8's framework is correct: density in the OS norm is enough, and it does
  dispose of the sign question I raised about the erased vortices. But its key input, decorrelation of **bounded
  measurable fine** observables given the block state, uniformly in the spacing, is the measurable ultraviolet transfer
  that the author's own `SKETCH-STEPS.md` 2 identified as a new piece of analysis (the frozen-region problem, blueprint
  P5.2). `M1-PLAN.md` 0 lists it as sketch point 4, alongside detail-level items; it is the remaining hard part of the
  ultraviolet half.
* **`M1-PLAN.md` 0's verdict is accurate as a list, but mis-weighted on point 4.** The proposed interface change
  ("`MassGapLoc` on the OS closure") would weaken the target theorem unless point 4 is proved.

No FATAL finding.

### G1 (the one-step induction): resolved at the claimed level

`S1-INDUCTION.md` gives:
* the order of constants (11 rows, no circularity I could find);
* `Form_k` with items F1-F7, including the window form (unreleased labels as indicators inside `T`);
* the step as S0-S11, each with input, output, references and level;
* the new E-row 7c (coarse plaquettes meeting holes, paid from the deep plaquette's own action `r0^2/(8 g_k^2)`,
  attributed to at most `C(C_1)` coarse plaquettes, with the budget condition 8).

That is what G1 asked for. Remaining NITs:
* **7c "recursively":** if the finer field in the deep plaquette's blocks is itself irregular, (71) does not apply
  directly. "Recursively" points to the earliest scale at which the structure was regular. That is the attribution of
  R2 and should cite it.
* **Stale sentence:** section 4 "Uniformity" still says "label factors grow sub-exponentially". After
  `REVIEW3-RESPONSE.md` 12.2 they change by at most `e^{4 C eps_*}` in total.
* **Hard core across scales (see the parity NIT below).**

### G2 (labels, the carrying sum): resolved in substance; one detail

* **What is fixed.** I checked the steps of 11.1, 11.2 and the lemma of 12.2:
  * With the constant split off at a flat base (`a_ell = Phi_ell(flat)`, `L_ell(flat) = 0`), gauge invariance and the
    absence of an `Ad`-invariant vector in `so(3)` remove the linear term.
  * Cauchy estimates give `|Q(F)| <= N_k (|F|/alpha_1)^2`.
  * The background curvature on the old box is about `L^{-2}` times the new one, so the quadratic part contracts by
    about `L^{-4}`.
  * Terms linear in `F_bg` vanish identically: any covariant adjoint vector built from the fluctuations is zero at
    `F_bg = 0`.
  * The per-step constant goes into `a_ell` and sums geometrically.
  
  So the linear-in-`K` term I found does not arise, and labels on the deepest skeleton are covered. Restoring R8 for
  labels was the right move.
* **Persistence rule (12.1).** Only remainders linked with the next skeleton are labels; a label is summed out when its
  parent stops persisting. This is consistent with the law, since the index stops being a law variable exactly then,
  and it only removes terms.
* **Detail to fix: the localisation tails in step 6 of the lemma.**
  * The proof says the tails of 11.3 "add `C e^{-kappa} N_k` to the weighted norm and are absorbed into `C`" of
    `theta = C L^{-4}`. A contribution `C e^{-kappa} N_k` without the factor `L^{-4}` is absorbed only if
    `kappa >= 4 log L + log C`, and that condition is not in the constants table of `S1-INDUCTION.md` 1.
  * Most likely the tail terms also have no linear coupling and contract like the main term, and distances shrink by `L`
    in the new units. But that has to be shown; as written the contraction factor is not established.
  * Either prove the tails contract with the `L^{-4}` factor, or add the condition on `kappa` (or settle for any fixed
    `theta < 1`, which is all the iteration needs) to row 6 or 8 of the table.
* **Readings still to check** (already listed by the author as sketch point 3): whether Balaban's first-order expansion
  at p. 379 covers real deviations (`A'`) over the next step's whole fluctuation domain, and per cube or per component.
  Both bear directly on (P2) with a flat base, which 11.1 now uses.
* **Large components above `eps_*`:** still sketch, as stated. Note that `eps_* <= L^{-4}/(2C)` is smaller than
  Balaban's own threshold, so more components fall into this case unless `delta_k |X|` is small. At the bare end
  `delta_k` is tiny; near `g_K = gamma` it needs `gamma <= gamma0(L)`, which condition 8 provides.

Severity now: FIXABLE (tails) plus the named readings. Confidence: medium-high.

### The parity hard-core NIT: resolved, with a new NIT

`Form_k` (F6) now writes labels as a hard-core polymer sum and says the per-bond parity formula is only an upper bound.
That is what I asked for. But the hard core ("pairwise disjoint, non-adjacent domains") cannot persist across scales:
* labelled domains shrink to single cubes after release;
* two labels released far apart at a fine scale can share a coarse cube later. Two bubbles on bare bonds of the same
  coarse bond is the typical case, and exactly the parity-cancelling one.

11.2 says released labels have "no hard core towards other polymers"; the same must hold between labels at later
scales. Their factors simply multiply. State the hard core at the release scale only. NIT.

### G4/N-2 (hand-over and density): relabelled, not resolved

**R10 (section 7).** Real `t` only, so the conditional step stays positive; the mixture over `A`-clusters; the scale-`K`
normalisation of the top variables paid from the large-field budget. This is the right structure. One FIXABLE point:
* the text Mayer-expands "the attached boundary terms into connected clusters" and then asserts non-negative
  activities;
* Mayer activities (`e^{B} - 1` products) are signed;
* define the `A`-cluster through the large-field domains and labelled domains only, and keep the boundary terms in the
  exponential (positive). Their `t`-dependence is then the local `Phi_t` term, and every `rho_G` is non-negative as
  claimed.

**Density (section 8).** What is right:
* the spectral upgrade needs density in the OS norm only, and `||.||_OS <= ||.||_{L^2}`;
* the decomposition `||F - f_ell||_OS^2 = E[Cov(theta F, F | F_ell)] + E[E[theta R | F_ell] E[R | F_ell]]` is correct,
  and `f_ell` drops out of the first term;
* the erased vortices linking `C` but not `theta C` drop out by conditional decorrelation, and the only survivors are
  crossing terms. So the comparison of `c0` with `1/b` is indeed not needed for OS density. This answers my N-2
  point about the sign of fundamental Wilson loops, **given** item 2.

What is not right:
* **Item 2 is the measurable ultraviolet transfer.**
  * `MassGapLoc` (`Objects.lean` 478) quantifies over all slab families of bounded measurable fine observables of
    physical extent `R`, with the number of fine links growing like `(R/a)^4`.
  * To transfer the limit-space gap to such families, section 8 needs, uniformly in `a`, the conditional covariance
    `Cov(theta F, F | F_ell)` for bounded **measurable** fine `F`, and `||E[F | F_ell] - f_ell||_{L^1}`.
  * Section 7's argument does not give this: it works by inserting `e^{tF}` for `F` analytic, with constants depending
    on the number of variables.
  * For measurable `F` the conditional law of the fine variables on `supp F` must decouple in total variation from the
    far block field. That means running Balaban's induction with those fine variables fixed: the "permanent frozen
    region of arbitrary content" of `SKETCH-STEPS.md` 2, which the author then assessed as "a new piece of analysis,
    not a write-out", and the scale-`< ell` part of blueprint P5.2.
  * Section 8 calls it "standard in form, not written line by line". I do not agree that it is standard. It also needs
    the large-field part, not only "the small-field part" as the status note says.
* **The interface change must not replace item 2.** `M1-PLAN.md` 0 puts "`MassGapLoc` on the OS closure" under
  "outside M1".
  * If `MassGapLoc` is restated for the OS closure of block observables, the theorem becomes weaker than the current
    one unless item 2 shows that the fine families lie in that closure, uniformly in `a`.
  * The interface change is legitimate only together with item 2, not instead of it.
* **Item 4 (polynomial approximation of `f_ell`) is probably unnecessary.** `BlockGapBddW` already treats bounded
  measurable block observables, so `f_ell` itself can serve as the dense-class element if P4 delivers decay for it.
  This simplifies, and does not affect the gap above.

Severity: GAP (the burden is now precisely located, in sketch point 4, but it is the hardest remaining piece of the
ultraviolet half, not a write-out). Confidence: medium-high.

### Is `M1-PLAN.md` 0's verdict now accurate?

Largely yes. It withdraws "complete at paper level", lists what is paper, citation and sketch, and names five sketch
points. Corrections I would make:
1. **Point 4 is not of the same kind as points 1, 2, 3 and 5.** Those are detail-level (a nonabelian fractions step, a
   lifetime re-reading, two text readings, a super-rare tail). Point 4 is the measurable UV transfer at scales below
   `ell`, the problem `SKETCH-STEPS.md` 2 said was not a write-out. The verdict should say so.
2. **"Outside M1: `MassGapLoc` on the OS closure"** should be qualified as above: it is only a valid restatement if
   point 4 holds.
3. **R10 "paper on citation-level inputs"** should carry the signed-Mayer fix (FIXABLE).
4. **The one-box contraction's tail step** (or a `kappa` condition) should be added, as part of the labels' citation
   level.
5. **Stale text in `S1-INDUCTION.md` 4** ("sub-exponentially").

### Summary table (my findings, current status)

| finding | status now |
|---|---|
| G1 one-step induction | resolved at the claimed level (NITs: 7c recursion via R2, stale sentence) |
| G2 labels: form and positivity | resolved (citation-level readings named) |
| G2 labels: carrying sum linear in `K` | resolved in substance by the one-box contraction; FIXABLE detail in the tails |
| G3 decoder | resolved (second follow-up) |
| N-1 bare-scale small field | resolved (second follow-up) |
| G4 hand-over / R10 | R10: paper sketch with a FIXABLE sign point; interface still outside M1 |
| N-2 density | relabelled into `M1-PLAN.md` sketch point 4; GAP (measurable UV transfer) |
| G5 encoding | moot by design (state `(SO(3), closed Z2)`); bears on P4 |
| G6 extended holes | resolved (H5 constants now in the table) |
| Parity NIT | resolved; new NIT on the hard core across scales |

## Fourth follow-up

Read for this: `../m1-tools/REVIEW3-RESPONSE.md` 13 and 14, and `UV-TV.md` in full. REVIEW-3 was not read. Nothing was
built.

### Verdict (fourth follow-up)

* **N-2 is now honestly stated.** Section 13.4 agrees that the key step is new analysis, withdraws the "OS closure"
  interface line, and keeps `MassGapLoc` unchanged. That resolves my objection to the verdict's weighting.
* **The coupling method does avoid the frozen region, as a method:**
  * the reverse-kernel factorisation is exact (the forward blocking chain is Markov in the scale, noise included, so the
    fine law given the block state is the composition of the kernels `K_j`);
  * no observable is inserted with fixed content.
* **But the frozen-region demand comes back through the repair's hypothesis.** `UV-TV.md`'s Theorem A asks that bad
  boxes be **dominated by an independent percolation**. That needs a bound on the probability that a box is bad given
  **arbitrary** configurations of its neighbours, including bad ones. It fails for the same worst-case boundaries that
  caused obstruction (b), and is the same kind of "uniform over arbitrary fine content" condition as the frozen region.
* **A formulation that avoids this** uses:
  * Peierls-type joint bounds on bad sets, under the law **given the coarse field only**;
  * bad sets defined through Balaban's large-field patterns (mixture indices), not as events of the configuration;
  * a coupling that matches the pattern mixtures first, and runs the box-by-box coupling on good boxes only.
  
  With that change the repair looks sound in principle.
* **The composition (ii) is routine only for the original (i),** which the obstruction shows to be false. For the
  good-boundary (i) it becomes a multi-scale disagreement percolation through bad regions inherited from coarser scales.
  That is part of the new analysis, not a union bound.

Severity: GAP (open, now precisely located). No FATAL finding.

### 1. Does the coupling method avoid the frozen region?

* **Yes, as far as it goes.** The forward chain `V_{j+1} = B(V_j, xi_j)` is Markov in `j`, with independent noise. So
  `law(V_j | V_{j+1}, ..., V_ell) = law(V_j | V_{j+1}) = K_j`, and the fine law given the block state at scale `ell` is
  exactly `K_0 ∘ ... ∘ K_{ell-1}`.
  * Each `K_j` is the fibre measure of M1's own law `rho_j`; noise and labels are included in the state.
  * The bound `|E[F | F] - E[F | F']| <= 2 ||F|| P(disagreement reaches supp F)` holds for every bounded measurable `F`.
  * Nothing is frozen; only true conditional measures are coupled.
* **Where it can come back.** Any argument that controls a kernel's law in a box **given arbitrary fine data around the
  box** asks for exactly what the frozen region asked for: uniformity over fine content that the action does not
  penalise. The Lean one-box hypothesis (sup over all `sigma`) asks this, which is why it fails (section 3 below), and so
  does Theorem A's independent-domination hypothesis (section 4).

### 2. Is the composition (ii) routine, uniformly in the spacing?

* **Given (i) in its stated form,** uniform over all conditioning fields outside the agreement region, yes. Choose
  shrinkages `r_j = w_j t/(L^j a)` with `sum_j w_j <= 1/2`, for example `w_j` geometric in `ell - j`. Then:
  * the per-scale failure `C |B_j| e^{-kappa r_j}` is dominated by the top scale, because `t/(L^j a)` grows like
    `L^{ell-j}` while `|B_j|` grows only like `L^{d(ell-j)}`;
  * the slow scale dependence of the good-box constants (box side `(log p(g_j))^{d+1}`, rate `m/log log g_j^{-1}`) is
    harmless against that growth;
  * the bound is uniform in `a`.
* **But (i) in that form is false** (obstruction (b)). Only the good-boundary (i) is plausible. Then:
  * the agreement region at scale `j` contains bad regions inherited from every coarser scale. A scale-`j'` bad box is
    a connected bad cluster of linear size `L^{j'-j}` at scale `j`, common to both copies;
  * a disagreement can pass through such a common region without contraction, since the fine law inside it, given
    identical coarse data, is still sensitive to its boundary;
  * so the composition must bound multi-scale bad crossings: paths made of bad regions of all scales `j' >= j`, under
    the law given `V_ell`.
  
  That is Balaban's multi-scale large-field geometry (his history-summed `d_j`-polymer bounds, [V] (1.80)-(1.85)),
  used as a **conditional** statement. It is likely doable with his bookkeeping, but it is not "a union bound over
  scales". **Not routine.**
* **Density of bad boxes in physical units is not the problem.** Bad boxes at fine scales are dense in physical units
  near `supp F` (`sum_j (R/(L^j a))^d e^{-p0(g_j)}` diverges as `a -> 0`, as for all of Balaban's large fields). What
  matters is subcriticality per box at each scale against crossing lengths `r_j` that grow like `L^{ell-j}`, and that
  holds.

### 3. Is the obstruction real?

* **(a) Single-site TV Dobrushin fails: real.** A weakly coupled, narrow Gaussian-like variable has conditional total
  variation influence of order one or more from a neighbour. This holds even for a free massive Gaussian field with
  compact or narrow spins: after one disagreement the values differ by about one width, which moves a neighbour's
  conditional mean by an `O(1)` fraction of its width.
* **The block version on small-field boundaries: plausible, with one point to write.** For continuous variables, the
  Hamming-Wasserstein distance needs couplings with **exact** agreement at far sites. A plain shift coupling makes every
  site differ. The claimed `k_J(z) <~ (log p/m)^d` needs a nested construction: couple the far marginals maximally, then
  extend inward conditionally, with each layer's conditional total variation controlled by the decaying mean shift.
  That works for a Gaussian with exponentially decaying covariance and small analytic perturbations, but it is the
  construction to write in `UV-TV.md` 2.
* **(b) Worst-case boundaries: real.** A large-field boundary can force a deep structure (vortex sheet, monopole line)
  through the box at a position the block constraint leaves free, and one boundary site can move it across the box. So
  the one-box hypothesis with `sup` over all `sigma` cannot be verified, and the present Lean layer does not apply.

### 4. Is the repair sound in principle?

**The idea, yes; the hypothesis as written, no.**

* **Independent domination fails here.** Theorem A assumes the bad set is "dominated by a subcritical independent
  percolation of boxes". By the standard criteria (Liggett-Schonmann-Stacey, or the sequential form used in van den
  Berg-Maes), that requires `P(J bad | the configuration outside J) <= eta` for the outside configurations met during
  the coupling. Near a bad box this fails:
  * a forced deep structure that crosses a bad box continues into its neighbours;
  * so `P(J bad | bad neighbour with a structure ending on the common face)` is of order one.
  
  Badness is spatially correlated in exactly the worst-case way of obstruction (b). The box-by-box coupling of 3.1
  conditions on revealed fine content of neighbouring boxes, so it meets this.
* **What works instead:**
  * **Peierls-type sparseness under the law given the coarse field.** For every set `S` of boxes,
    `P(all boxes of S bad | V_{j+1}) <= eta^{|S|}`, with `eta = e^{-c p0(g_j)}`. Balaban's polymer bounds give this
    shape, with the normalisation adaptation (section 5). It needs no conditioning on fine neighbours.
  * **Bad sets as mixture indices.** Balaban's large-field regions come from smooth partitions of unity. They are
    summation indices of a positive mixture, not events (the same point as for `E_D` in R10, settled in 13.3). Define
    "bad" through them.
  * **Mixture-first coupling.**
    1. Couple the two copies' pattern mixtures near `B` through the locality of the ratio `Xi_{-G}/Xi` (section 7's
       mechanism at scale `j`).
    2. Given identical patterns near `B`, couple the small-field parts by the good-boundary block argument.
    3. Large-field components that lie wholly inside the agreement region then have identical boundary data and
       identical laws.
    4. Disagreement can reach `B` only through a connected bad cluster joining the front to `B`, which is bounded by the
       Peierls sparseness.
  * Path counting of the van den Berg-Maes kind then needs only the joint bounds.
* **So Theorem A should be restated** with a sparseness hypothesis on a mixture (pattern) index, and a coupling built
  over that mixture, not with domination of a configuration event by independent percolation. As stated it would push
  the frozen-region uniformity into its domination hypothesis.

### 5. Does the conditional rarity of bad boxes hold uniformly, or does the frozen region come back?

* **Given the coarse field near `J` good:** the rarity of new scale-`j` large fields near `J` is section 7's crossing
  estimate one scale down. It conditions only on the top variable `V_{j+1}`, as in Balaban's own step, so no fine
  content is frozen.
  * **Uniform in `V_{j+1}` away from `J`:** plausible, because the ratio `Xi_{-G}/Xi` is local in the polymer
    expansion. Fixed large-field regions of `V_{j+1}` far away enter numerator and denominator alike.
  * **What it rests on:** the pointwise lower bound for the fibre normalisation `rho_{j+1}(V_{j+1})` relative to the
    small-field Gaussian fibre integral near `J`. That is the "top variables paid from the large-field budget"
    adaptation, now needed at **every** scale and **pointwise in the conditioning**, not only on average. Still
    unchecked, and the main technical risk outside the small-field coupling.
* **Given the coarse field bad near `J`:** bad by fiat. The rarity has to come from the kernel one scale up, given its
  own coarser field, and so on up to `V_ell`, whose large fields are controlled in `L^1` by its law (which is all that
  (A) and (B) need). This induction is consistent, but it is exactly the multi-scale conditional geometry of section 2,
  and it must be organised with the history-summed bounds, not box by box.
* **Unfinished finer history.** `rho_j` also contains regions born at finer scales that have not yet been released
  (unfinished `T`-operations in the history of `rho_j`). Near them the kernel `K_j` is not Gaussian-like in `V_j`, even
  where `V_j` is regular. They must count as bad boxes too. They are mixture indices of `rho_j`, so the sparseness
  formulation covers them; an event-based "bad = the field is not small near `J`" does not.
* **Where it would come back:**
  * if rarity is required given arbitrary fine neighbours (independent domination, or a sequential box coupling through
    bad boxes);
  * if the normalisation lower bound is needed given arbitrary **fine** data rather than coarse data.
  
  In both cases the uniformity over unpenalised fine content, which is the frozen region, reappears. With the mixture
  formulation it does not.

**Answer: the conditional rarity can hold uniformly, given the coarse field only, and then the frozen region does not
come back. Under Theorem A's present hypothesis it would come back.** Confidence: medium.

### Status (fourth follow-up)

| item | status |
|---|---|
| N-2 statement and the theorem unchanged | resolved (the "OS closure" line withdrawn; `MassGapLoc` unchanged) |
| coupling method avoids the frozen region | yes as a method; the reverse-kernel factorisation is exact |
| obstruction (a) and (b) | both real; the block version on good boundaries is plausible, with the nested exact-agreement coupling to write |
| Theorem A as stated | **hypothesis to change:** independent domination reintroduces uniformity over fine content; use Peierls sparseness on pattern indices given the coarse field, and a mixture-first coupling |
| composition (ii) | routine only for the original, false (i); for the good-boundary (i) a multi-scale conditional crossing estimate (Balaban's history geometry); part of the new analysis |
| conditional rarity of bad boxes | plausible given the coarse field, pointwise normalisation at every scale (unchecked adaptation); includes unfinished finer-history regions |
| N-2 overall | **GAP**: open, new analysis, now precisely located |

## Fifth follow-up

Read for this: `../m1-tools/UV-TV.md` sections 7-13. REVIEW-3 was not read. Nothing was built.

### Verdict (fifth follow-up)

The rebuild follows the right design, and my three points from the fourth follow-up are answered in substance:
1. "bad" is defined through the mixture index `ω`, with one acceptable exception;
2. no rarity or influence statement conditions on unpenalised fine content, so the frozen region stays out;
3. the multi-scale crossing estimate is named as the open core (section 12), not hidden.

Two things need correcting before section 12 starts:
* **A gap in the proof (step 3 of Theorem A_good).** As written, bad boxes get `d <= 1`, which makes every bad cluster
  anywhere a source of disagreement. That contradicts step 4's "activated only if a disagreement reaches its boundary"
  and would give an `O(eta)` floor instead of `e^{-lambda dist(B, D)}`.
* **The hypothesis H2 is stated in the wrong form for the tower.** Theorem A_good uses an annealed H2 with a fixed source
  `D`, but in the tower `D` is random and correlated with the bad sets. So the tower needs H2 conditional on all coarser
  data (quenched in the coarse field), which is the pointwise fibre normalisation. That is still frozen-free, but it is
  not the annealed statement the text names in sections 8 and 9.

Nothing in H0-H4 looks unavailable in principle. N-2 stays a GAP (open, section 12 not started). No FATAL finding.

### 1. Is "bad" now defined through mixture indices?

**Yes, with one acceptable exception.**
* `Bad_j(ω)` is the set of boxes meeting a large-field domain, an unreleased region (including those born at finer
  scales), a labelled domain, a Z2 excitation, or a long link of `ω`. These are all summation indices of the positive
  representation before any Mayer expansion.
* This also takes care of the "unfinished finer history" point of my fourth follow-up.
* **The exception:** `Bad^c(X_{j+1})`, "the block field `X_{j+1}` is not small field", is an event of the conditioning
  variable, not an index. That is acceptable, since it is coarse data, fixed given `X_{j+1}`, with two provisos:
  * its threshold must lie outside the support of the small-field characteristic functions at scale `j + 1`, so that its
    rarity comes only from the large-field pattern weights of `rho_{j+1}`;
  * there is no joint positive mixture of indices across scales: the R-operation destroys `ω_j`'s structure when it
    builds `rho_{j+1}`. So the tower carries coarse badness only as this event (plus the unreleased regions that
    `rho_j` still holds), not as a coarser index.
  
  Both should be stated in section 8. NIT.

### 2. Is the frozen region kept out?

**Yes.**
* **H3** asks for influence bounds only for boundary pairs in the support of pattern-good neighbourhoods. Those are
  small field, within `C eps` of a common background in a common gauge. Every hybrid boundary stays in that set, so
  nothing unpenalised is quantified over.
* **Bad clusters** carry no influence bound.
* **H1 and H2** are properties of the pattern weights given coarse data.
* **The Doeblin floor** is used only qualitatively, for unique ergodicity.
* **The comparison states:** (A) resamples the far coarse data from the law, and (B) uses fresh randomness on the
  mirror side. Neither allows an arbitrary `X'`. This removes the uniformity over coarse data as well.

**Caveat, the annealed/quenched point (GAP-level, part of section 12).** Sections 8 and 9 state H2 annealed (averaged
over the coarse pair), for a single scale with a **fixed** source `D`. In the tower:
* the source `D_j` is the disagreement inherited from scale `j + 1`, a random set correlated with the scale-`j` bad sets
  (both concentrate where the coarse field is bad);
* applying Theorem A_good scale by scale then needs H2 conditional on all coarser data, including `D_j`: quenched in the
  coarse field, annealed only in the scale-`j` indices;
* that is the pointwise bound of section 10.3, `P(A ⊂ Bad_j(ω) | X_{j+1}) <= eta^{|A|}` for boxes outside
  `Bad^c(X_{j+1})`. The coarse bad set's own rarity is carried by the coarser scale's chain.

This still conditions only on coarse data, so the frozen region stays out. But the annealed form named in sections 8
and 9 is not what the tower uses: annealing alone cannot handle a random correlated source. Reconcile the two
statements; the pointwise fibre normalisation is then genuinely needed, as section 12 already says.

### 3. Does the structure leave room for the multi-scale crossing estimate, or hide it?

**It leaves room, and names it.**
* Section 8 ("The tower") says that the failure event is a multi-scale chain, "not a union bound over scales", with bad
  regions of coarser scales inherited.
* Section 12 lists the estimate as not started.

Two remarks on its shape:
* **Theorem A_good, as stated, is a single-scale theorem with a deterministic source.** The tower needs either a
  version with random sources and joint (cross-scale) Peierls bounds, or Theorem A_good applied conditionally on the
  coarse data with the quenched H2 above, whose conditional conclusions are then chained from scale `ell` down. The
  second is the natural route. Section 12 should say which.
* **The cross-scale Peierls bound** has to come from Balaban's history-summed bounds ((1.80)-(1.85)). The weights of
  chains that mix bad clusters of several scales must factorise conditionally scale by scale, and a conditional chain
  rule gives exactly that, given the quenched H2. This is consistent with my fourth follow-up.

### 4. Is anything in H0-H4 unavailable in principle?

| hypothesis | assessment |
|---|---|
| H0 (range, agreement) | **Available.** The positive tail decomposition `e^{E(X)} = e^{m_X}(1 + h_X)` with `h_X >= 0` turns long-range terms into a positive sum over link sets. The link weights are positive functions of the configuration rather than constants, which is fine for a positive decomposition. Fibre constraints and gauge-fixing are internal to the `L`-blocks. |
| H1 (pattern coupling) | **Available in principle, not standard.** Balaban's patterns are not a plain hard-core polymer gas: they are admissible histories across scales (nested domains, the (i)/(ii) conditions, merging rules), and their weights include `T`-values and exponentiated boundary terms that couple domains. A disagreement-percolation or clan coupling needs these written as a positive gas with small local activities given the coarse data, with the boundary terms decomposed like the links of H0. Part of section 12. |
| H2 (Peierls per copy) | **Available in principle,** in the quenched form, given the pointwise fibre normalisation (the unchecked adaptation). The annealed form alone does not serve the tower. |
| H3 (good-box influence) | **Available.** The far-to-near nested coupling with exact agreement at far sites answers my fourth-follow-up point. The numbers (`k_J(z) <~ (log p/m)^d`, `ell_B ~ (log p/m)^{d+1}`, `lambda ~ 1/ell_B`) are consistent, and the rate is harmless for the composition. The Pinsker step with the analytic perturbation, uniform over pair-good boundaries, is still to write. |
| H4 (small bad gas) | **Available:** `eta = e^{-c p0}` is tiny against `e^{lambda C ell_B} = O(1)`. |

### 5. The proof of Theorem A_good: one inconsistency to fix

* **Step 3** gives, for `x` in a bad box, near `D` or at a link endpoint, only `d(x) <= 1`. Iterated in step 5, every
  chain may then end at **any** bad cluster with weight 1, whether or not the cluster is connected to `D`. Bad clusters
  occur at density `eta` per box, so the bound becomes `d(x) <~ sum (nearby clusters) gamma^n`, of order `eta`, not
  `e^{-lambda dist(B, D)}`.
* **What is needed is the property step 4 states but step 3 does not derive.**
  * If `ω = ω'` on a bad box `J` and its `r_int`-surroundings, `J` is far from `D`, and the two configurations agree on
    those surroundings, then by H0 the two specifications coincide and the coupled update is the identity. So no
    disagreement is created inside a bad cluster; it can only be carried in.
  * The stationary inequality for bad boxes is then `c(x) d(x) <= sum_{J ∋ x} sum_{z in the r_int-shell of J} d(z)`,
    with weights up to 1 (no contraction), not `d(x) <= 1`.
* **Iterating that inside a large cluster compounds weights above 1.** So the cluster has to be treated as one node:
  disagreement inside `𝒦` is bounded by the boundary disagreement times a sweep factor of order `|𝒦|`, through a
  cluster-level stationarity argument. That is step 4's claimed "outgoing influence `<= C ell_B^d |𝒦|`".
* This is the "first-passage bookkeeping" the text defers. It is not a formality: without it the conclusion is false
  as written.

FIXABLE, but it must be written before any Lean. Confidence: high that steps 3 and 4 are inconsistent as written;
medium-high that the cluster-node argument closes.

### 6. Smaller remarks

* **Unimodality after matching (section 11): agreed.** Given the full index, the remaining law on pattern-good boxes
  is a small perturbation of a strictly log-concave Gaussian with a unique background. This is the right reason why
  H3 holds and bad boxes need no influence bound.
* **(B) by fresh mirror randomness:** the standard conditional-independence-by-coupling trick, correctly set up.
* **The Doeblin floor `e^{-C beta_0 L^{dj} |J|}`:** qualitative only, used only for unique ergodicity of finite-volume
  chains. That is correct; irreducibility of the block heat bath on supports restricted by characteristic functions
  should get one line.

### Status (fifth follow-up)

| item | status |
|---|---|
| (1) "bad" as mixture indices | resolved; the coarse bad set is an event of the conditioning variable (acceptable, with two provisos to state) |
| (2) frozen region kept out | resolved; but H2 must be quenched in the coarse field for the tower, so annealed and pointwise statements are to be reconciled |
| (3) room for the multi-scale estimate | yes, named in sections 8 and 12; section 12 should choose "conditional Theorem A_good, chained" and the cross-scale Peierls form |
| Theorem A_good proof | sketch; **steps 3-4 inconsistent as written** (bad boxes as sources); fix by identical coupling on agreeing boundaries plus cluster-level bookkeeping |
| H0, H3, H4 | available (H3 Pinsker step to write) |
| H1, H2 for Balaban's patterns | available in principle, not standard; section 12 |
| N-2 overall | **GAP**: open, with the core in section 12 not started |
