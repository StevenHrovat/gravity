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

## Sixth follow-up

Read for this: `../m1-tools/UV-TV.md` sections 14-20. REVIEW-3 was not read. Nothing was built.

### Verdict (sixth follow-up)

* **Section 15 is right.** The box-by-box linear inequality cannot close. My fifth-follow-up remedy (treat the cluster
  as one node) is, done properly, exactly the static composite box.
* **Lemma C is sound in principle.** The partition-function-ratio argument uses only the collar's small-field law and
  its decaying cross term, and never bounds the multimodal inside of the cluster. It needs **long links** included in
  the cluster connectivity.
* **The H2 form and the coarse bad set** from my fifth follow-up are resolved in statement.
* **Three problems with the static form as written:**
  1. **The coverage fix does not work as stated.** Repeating a composite box raises the influence that outside sites
     exert on it by the same factor as its coverage. The condition that matters, site by site, is not helped, and the
     region next to `W` is left under-covered. A working variant is below.
  2. **The merge rule percolates.** With collar width `w` growing like `log |K|`, clusters merge at size-dependent
     distances. The lattice-animal count `(C η (log n)^d)^n` is not summable for astronomically large `n`, so the rule
     percolates in large volume at fixed spacing. `MassGapLoc` takes the volume limit first, so this matters. A
     hierarchical (Froehlich-Spencer type) sparse decomposition should replace it.
  3. **Step (ii) of Theorem A_good** treats every composite box as rare at scale `j`. Inherited coarse-bad clusters are
     not: they are rare only per box of their own scale.

None is FATAL. The multi-scale step (section 12) is well posed on the static form, once item 3 is put where it belongs.
N-2 stays a GAP.

### 1. Is section 15's argument right?

**Yes.**
* With weight 1 per collar site on bad boxes (all that an arbitrary coupling on a multimodal bad box allows), the
  inequality system `d <= min(1, M d + s)` has loop gain `>= |collar| > 1` inside a cluster. Its minimal solution
  saturates at 1 on every cluster that receives any positive input.
* Every cluster does receive input, because good-box influences are small but positive. So the bound bottoms out at
  the cluster density, independent of `dist(B, D)`.
* The point is the method, not the true `d`. The true marginals on a far cluster differ only by what reaches it, but a
  time-local, box-by-box coupling cannot see that.
* Treating the cluster as one node (fifth follow-up, item 5) means coupling its **marginal**, which is the static
  composite box of section 16. So the two remedies coincide.

### 2. Is Lemma C sound for the constrained, gauge-fixed, non-Gaussian measure?

**In principle yes, with one omission and one simplification.**
* **Structure.** The law of `W` given `σ` is `w(c) Z(c, σ)`, with `c` the data on `𝒦` and on the inner layer of the
  collar. The ratio `law(c | σ')/law(c | σ)` lies in `[e^{-2M}, e^{2M}]`, with `M` the sup over `c, c'` of the mixed
  variation of `log Z`. So `TV <= e^{2M} - 1`. This is correct, and uses nothing about the inside of `𝒦` beyond its own
  weight `w(c)`.
* **Gaussian and fibre constraint.** In the collar, `log Z` is a quadratic form in the boundary data through the
  constrained Green's function. Balaban's propagators with block constraints ([13] Theorems 3.12, 3.13, read) decay
  exponentially. The analytic perturbation and the smooth small-field truncation enter `log Z` through Balaban's
  small-field expansion as local terms with decay (truncation effects `e^{-c p^2}`). So the mixed variation decays
  across the collar, as stated. Citation level, plausible.
* **Gauge.** In the block-axial gauge relative to the coarse configuration, both inner data `c, c'` and both outer data
  `σ, σ'` are within `C eps` of the same background. So `|Δc|/g, |Δσ|/g <= 2p` holds. Correct, given equal coarse
  data near `W`.
* **Only boundary layers enter.** By H0, `σ` enters the collar's law only through the outer `r_int`-layer, and `c`
  through the inner layer. Both are small field: the inner layer is good by construction, and the outer layer is good
  because other composite boxes are at least `2w` away.
* **Omission: long links.** A link of `ω` from inside `𝒦` to a far box couples `c` directly to `σ`, bypassing the
  collar.
  * Given `ω`, a chosen link is a factor `h_X(V)` (not `1 + h_X`) whose relative variation is not small.
  * So link endpoints have to be bad, and **link-connected** to the cluster: clusters are components of
    `Bad(ω) ∪ Bad(ω')` with links as edges.
  * Section 16 defines clusters through `w`-connectivity of bad boxes only, and section 8 lists links separately from
    `Bad`.
  * The composite box of a link-joined pair is then non-local (two pieces joined by a link). That is harmless:
    `dist_ω` contracts it, and the averaging pays `e^{-κ s}` per link through H2.
  * Must be stated. FIXABLE.
* **Simplification.** The bound `C |∂_in| p^2 Σ_z e^{-m d(z, ∂_in)}` overcounts. For fixed `z`, the sum over
  `x ∈ ∂_in` of `e^{-m d(x, z)}` is `<= C_m e^{-m d(z, ∂_in)}`. So `TV <= C p^2 Σ_z e^{-m d(z, ∂_in)}`, without the
  `|∂_in|`. The factor `|W|` from "count all of `W` if `c` differs" remains, more precisely `|𝒦|` plus the collar's
  near-inner disagreement `|∂_in| (log p/m)^d`. So the collar must still satisfy `e^{-m w} <~ 1/(|𝒦| p^2)`, which is
  where the size dependence of `w` comes from.

### 3. Is the coverage fix right, and is the cluster-merging count under control?

**The coverage fix does not work as written.**
* In the averaged block heat bath (the contraction behind `cov_le_weighted_on`), the condition per site `z` is:
  `Σ_{J ∌ z} k_J(z) e^{λ ...} <= γ c(z)`. That is, the total influence that `z` exerts on blocks not containing it,
  against the coverage of `z`. For a translation-invariant family this reduces to the per-box sum of `OneBoxSum`.
* Repeating `W` `n` times multiplies the influence that each outside site `z` near `W` exerts on `W` by `n`, while
  `c(z)` does not change. So the multiplicity makes the condition **worse** at sites just outside `W`, and only helps
  at sites inside `W`.
* "Good boxes not meeting any `W`" also leaves the sites next to `W` covered by fewer good boxes than elsewhere.
* **A variant that does work:**
  * let good boxes overlap the collar, keeping only `r_int` away from `𝒦`. The collar is good, so H3 applies there,
    and collar sites get the full coverage `|Λ_0|`;
  * use `W` with multiplicity 1;
  * then a site `z` of `𝒦` exerts influence only on `W` (finite range; good boxes stay `r_int` away), so its exerted
    sum is 0;
  * a site `z` outside or in the collar exerts its usual good-box influence plus `k_W(z) <= C (log p/m)^d + small`,
    against `c(z) ~ |Λ_0| = ell_B^d`, which is much larger than `(log p/m)^d`.
  
  This is check 1 of section 16, and it should be settled in this form.

**The merging count is not under control as written.**
* Clusters merge when closer than `2w(|𝒦|)`, with `w ~ (2/m) log(|𝒦| p)`. The number of `w`-connected sets of `n` boxes
  through a point is about `(C w^d)^n = (C (log n)^d)^n`, so the Peierls sum has terms `(C η (log n)^d)^n`. They grow
  once `log n > (C η)^{-1/d}`.
* The threshold `n* = exp((C η)^{-1/d})` is astronomically large, but finite. In volumes `>> n*` boxes at fixed
  spacing, the size-dependent rule percolates: a cluster of size above `n*` finds more than one bad box within its own
  merge range per box.
* `MassGapLoc` takes the volume limit **first** (`Objects.lean` 476-481), so uniformity in the volume at fixed level is
  needed. As written, check 3 fails in that limit. This is the same mechanism as the merging rule of G3, much weaker,
  but structurally the same.
* **Repair: a hierarchical sparse decomposition** (Froehlich-Spencer; Bricmont-Kupiainen).
  * Level-`n` clusters have size `<= C^n` and separation `>= 2^n w_0`, and exist with probability 1 when `η` is small.
  * The collar width a level-`n` cluster needs, `~ log(size) ~ n`, is far below its separation `2^n w_0`. So collars
    never merge, and the count is per level, summable.
  * Standard, but it replaces "merge within `2w`" and must be written. GAP-level until then (FIXABLE in kind).

### 4. Are my fifth-follow-up points resolved?

* **H2 form: resolved in statement.** Section 17 states H2 quenched in all coarser data and pointwise only where the
  coarse field is small field. It says that "annealed" now means annealed in `ω_j` only, and that the source is
  measurable in the coarser data. This is exactly what the tower needs. It still rests on the pointwise
  fibre-normalisation lower bound, which is unchecked and is the key adaptation of section 12.
* **Coarse bad set: resolved,** with one check. Section 18 uses a sharp threshold `2 eps_{j+1}` outside the support of
  Balaban's small-field characteristic functions, which section 18 says is `(1 + δ) eps_{j+1}`, `δ < 1`.
  * Check the support against [III] (2.17)'s actual smoothing (the OCR of those formulas was poor in REVIEW-1). If
    Balaban's smooth cut-off reaches `2 eps`, take the threshold strictly above it.
  * "No joint mixture across scales" is stated, and coarse badness is carried as an event.
  * With the threshold outside the support, the chain closes: `P(box ∈ Bad^c(X_{j+1}) | X_{j+2}) <= P(box ∈
    Bad_{j+1}(ω_{j+1}) | X_{j+2}) <= η` wherever `X_{j+2}` is small field. That is the quenched H2 one scale up.

### 5. Is the multi-scale step (section 12) well posed on the static form?

**Yes, with step (ii) corrected.**
* **Sources.** The scale-`j` conclusion is an expected count of disagreeing sites given coarser data. Turned into
  `P(D_j within r of B) <= E[#disagreeing sites in N_r(B)]`, it feeds the next finer scale. The recursion runs from
  `ell` down, and its polynomial prefactors are harmless against `t/ell -> ∞`.
* **Coarse-bad regions are not sources.**
  * Where the two copies' coarse data agree, an inherited coarse-bad region with matched `ω_j` is a composite box whose
    two laws coincide (H0), with Lemma C for its influence. So it creates no disagreement, and only its probability
    matters.
  * This is the static form's advantage over the dynamic one: an inherited bad region far from the source costs only
    its rarity.
* **Step (ii) of Theorem A_good does not hold for inherited clusters.** It bounds the probability that composite boxes
  cover half of a path by `(C' η^{1/2})^{dist/2}`, counting scale-`j` boxes at rarity `η_j` each.
  * An inherited coarse-bad box of scale `j'` covers `L^{j'-j}` scale-`j` path length at probability `η_{j'}`. That is
    `η_{j'}^{L^{-(j'-j)}}` per scale-`j` box, close to 1.
  * So, at scale `j`, inherited clusters must not enter step (ii). They have to be paid at their own scale: the path
    sum is multi-scale, with each bad region priced per box of its own scale.
  * This is the multi-scale crossing estimate. The static form leaves room for it, but step (ii) as written covers only
    the scale-`j` patterns.
  * The joint Peierls bound it needs, across scales, comes from chaining the quenched H2 scale by scale. The top field's
    bad set is priced by its own law, since (A) and (B) are averaged over it.
* **Lemma C for inherited clusters.** These can be large (`|𝒦| ~ L^{d(j'-j)}`). The collar `w ~ (2/m) log(|𝒦| p)` grows
  only like `(j' - j) log L`, which is fine. Under the hierarchical decomposition of section 3 they are high-level
  clusters, with separation growing faster than their collars.

### Status (sixth follow-up)

| item | status |
|---|---|
| section 15 (dynamic fix saturates) | **correct**: a real obstruction to the box-by-box method; the cluster-as-node remedy is the static composite box |
| Lemma C | **sound in principle**; FIXABLE: long links must join clusters; simplification (no `|∂_in|` factor) |
| coverage via multiplicity (check 1) | **does not work as written** (it worsens the per-site condition outside `W`); variant: good boxes overlap the collar, `W` with multiplicity 1 |
| cluster-merging count (check 3) | **not under control**: the size-dependent merge rule percolates in volumes `>> exp((Cη)^{-1/d})` at fixed spacing; `MassGapLoc` is volume-first. Replace by a hierarchical sparse decomposition (GAP until written) |
| H2 quenched (my fifth point) | resolved in statement; rests on the pointwise fibre normalisation (unchecked) |
| coarse bad set (my fifth point) | resolved; check the support of Balaban's cut-off at [III] (2.17) |
| step (ii) of Theorem A_good | covers scale-`j` patterns only; inherited coarse-bad clusters must be priced at their own scale (section 12) |
| section 12 well posed | yes, on the static form, as a recursion of conditional expected counts with a multi-scale (chained) Peierls bound |
| N-2 overall | **GAP**: open; section 12 not started |

## Seventh follow-up

Read for this: `../m1-tools/UV-TV.md` section 21. REVIEW-3 was not read. Nothing was built.

### Verdict (seventh follow-up)

* **The construction is not a Froehlich-Spencer hierarchy, but a valid alternative for what UV-TV needs.**
  * The hierarchy decomposes **all** bad sets, with probability 1 in infinite volume.
  * Section 21 replaces it with a fixed merge range per scale, localisation to a region of the size of `dist(B, D)`,
    and truncation of oversized clusters into a failure event of polynomial probability `|Λ''|^{-C_2}`.
  * That is enough for the volume-first limit (every estimate is local) and for OS density, which needs only `o(1)`.
    The conclusion now has a polynomial tail besides the exponential one, and must say so. `C_2 > 1` is needed for the
    composition over scales, which is available by taking `C_1` large.
* **What the hierarchy provides and section 21 does not yet:** separation **between** levels, here between birth
  scales. Two things are missing:
  1. inherited regions grow by accreting scale-`j`-born clusters at every finer scale, and allowed (non-truncated)
     born clusters can be long enough to bridge two inherited regions' birth-collar gap. A cross-scale bridging event,
     with its own bound, has to be added;
  2. the size bound `|K| <= C L^d n_{j+1}` for inherited composite boxes holds only for regions born one scale up. A
     region born at `j'` can cover up to `L^{d(j'-j)} n_{j'}` scale-`j` boxes, so its scale-`j` collar must grow with
     its age `j' - j`. That fits inside its birth collar, but the recursion `n_j := max(n_j^born, n_{j+1})` undercounts.
* **The condition `p0 >> d log log g_0^{-2}`: the conclusion is right, the derivation is not.**
  * The derivation uses `p0(g_j) >= p0(g_0)`, which is reversed: `g_j >= g_0`, so `p0(g_j) <= p0(g_0)`.
  * With the crude bound `|Λ''_j| <= e^{C g_0^{-2}}`, the right-hand side grows without bound at coarse scales as
    `a -> 0`, while `p0(g_j)` stays bounded.
  * The correct, **scale-local** bound `log |Λ''_j| <= (d/b) g_j^{-2} + C(t)` gives `w_j ~ log g_j^{-2}`, and the
    condition `p0(g_j) >> d log log g_j^{-2}` holds for any `p >= 1` at `g_j <= γ0(L)`.
  * So the weaker condition stands, with `g_j` in place of `g_0`. REVIEW-3's `p >= 2` (or `c A0 > 2d`) is needed only
    for a merge range growing like `log |Λ''|`. It would hold anyway: Balaban's own `p0 >> M^d R^{d+1}` with
    `R >= (log g^{-2})^r`, `r >= 2`, forces an exponent far above 2.
* **Volume uniformity with `MassGapLoc`'s volume-first limit: holds,** given the two additions above and one wording
  fix. The localisation must be done by treating the outside as a **source** in the global coupling, not by
  **conditioning** on outside fine configurations. The latter would put arbitrary fine content near `∂Λ''` into the
  pattern weights.

No FATAL finding. N-2 stays a GAP (section 12 not started). The cross-scale items above are new FIXABLE points that
belong to section 12.

### 1. Is section 21 a hierarchical decomposition, and what does it miss?

**What it is.** Per scale `j`:
* a fixed proximity `2w_j + ell_B` for merging, independent of cluster sizes, which removes the cascade mechanism;
* clusters born at `j` larger than `n_j = C_1 log |Λ''_j| / log(1/η_j)` go into a failure event `F_j`, with
  `P(F_j | 𝒳_{j+1}) <= |Λ''_j|^{-C_1/2 + 1}`. I checked the count: lattice animals under fixed proximity, the quenched
  H2, and the min-trick;
* inherited regions keep the collars of their birth scale.

**This is not FS:**
* FS needs no localisation and no failure event: it decomposes everything with probability 1.
* Section 21 localises to `Λ''`, accepts a polynomially small failure, and gets uniformity in the total volume from
  locality.

For UV-TV that is enough:
* composition (ii) at scale `j` needs `|B_j| P(failure_j) -> 0`, summed over scales. With
  `|Λ''_j| ~ (t/(L^j a))^d` this is `sum_j L^{d(ell-j)(1 - C_2)} (t/ell)^{...}`, geometric for `C_2 > 1`;
* OS density needs only `o(1)` (`REVIEW3-RESPONSE.md` 13.4).

State the conclusion of Theorem A_good on the truncated event as `C |B| (e^{-λ R'} + R'^{-d C_2})`.

**What the hierarchy provides that is missing: separation between levels.** Here the levels are birth scales.
* **Accretion.** An inherited region born at `j'` is a composite box at every finer scale `j`. At each such scale,
  born clusters within `2w_j + ell_B` of it merge into it. So its extent grows by up to
  `n_i (2w_i + ell_B) ell_B L^{i-j}` scale-`j` units at each scale `i` between `j` and `j'`.
  * Born clusters need not be compact: a lattice animal of `n_i` boxes under proximity `2w_i + ell_B` can be a chain of
    diameter `n_i (2w_i + ell_B)` boxes.
  * `n_i ~ C_1 log |Λ''_i| / (c p0(g_i))`. With the scale-local bound, `log |Λ''_i| ~ (d/b) g_i^{-2}` while `p0(g_i)`
    is only polylogarithmic in `g_i^{-2}`, so `n_i` is large.
  * So the total accretion, dominated by `i = j' - 1`, is about `n_{j'-1} (2w + ell_B) L^{j'-1-j} ell_B` per side. The
    birth gap between two regions born at `j'` is `2 w_{j'} ell_B L^{j'-j}` scale-`j` units.
  * The gap survives only if `n_{j'-1} (2w + ell_B) < (L - 1) w_{j'}`. With `n` large, this fails.
* **Bridging.** So two inherited regions can be bridged at a finer scale by allowed (non-truncated) born clusters. The
  author's sentence "they can be bridged only by bad boxes born at the finer scales in between, which H2 prices" is
  right in substance, but the construction never turns it into an event:
  * a bridged pair is a merged composite box far larger than the collar budget `w_j` assumes, so Lemma C fails for it;
  * it has to go into a failure event `G_j`: some pair of inherited regions meeting `Λ''_j` is joined by a scale-`j`
    born chain of length at least the remaining gap;
  * the bound is `P(G_j | 𝒳_{j+1}) <= |Λ''_j|^2 (C w_j^d η_j^{1/2})^{(gap_j)/(2w_j + ell_B)}`. Since `gap_j` grows like
    `L^{j'-j}` while `|Λ''_j|` grows like `L^{d(ell - j)}`, this is summable.
  
  That is the FS separation condition, in this construction's terms. FIXABLE, but it has to be written: it is exactly
  the "cross-level percolation" the coordinator asks about.
* **The size of inherited regions.**
  * Beneath a coarse bad region H2 says nothing, so at a finer scale the whole footprint can be bad. A region born at
    `j'` then has up to `L^{d(j'-j)} n_{j'}` scale-`j` boxes, not `C L^d n_{j+1}`.
  * Lemma C needs `e^{-m w} <~ 1/(|K| p^2)`, so its scale-`j` collar must be `w_j + (d/m)(j' - j) log L`, growing
    linearly in its age.
  * That still fits inside its birth collar, which is about `L^{j'-j} w_{j'} ell_B` wide. But the definition
    `n_j := max(n_j^born, n_{j+1})` with `|K| <= C L^d n_j` has to be replaced by an age-dependent collar for inherited
    regions.
  * Their merge range with born boxes then depends on age, not on size, so no cascade arises. FIXABLE.

### 2. The condition `p0 >> d log log g_0^{-2}`

* **Section 21.3's chain** is: `|Λ''_j| <= e^{C g_0^{-2}}`, so `w_j <~ log g_0^{-2}`, so
  `c p0(g_j)/2 > d log(C log g_0^{-2})`, which holds "since `p0(g_j) >= p0(g_0)`".
* **The last step is reversed.** The bare coupling is the smallest (`g_j >= g_0`), so `p0(g_j) <= p0(g_0)`. At the
  coarse end (`j` near `ell`) `p0(g_j)` is bounded as `a -> 0`, while `log log g_0^{-2} -> infinity`. With the crude
  volume bound, the condition **fails** at coarse scales in the continuum limit.
* **The scale-local bound repairs it.**
  * `log |Λ''_j| = d log(t/(L^j a ell_B)) <= (d/b) g_j^{-2} + C(t)`, from the running `g_j^{-2} ≈ b log(1/(L^j a Λ))`.
    So `log n_j <~ log g_j^{-2}` and `w_j <~ (3/m') log g_j^{-2}`.
  * The condition `C (2w_j + ell_B)^d e^{-c p0(g_j)/2} < 1/2` becomes `c p0(g_j)/2 > d log log g_j^{-2} + C`.
  * That holds for `p0 = A0 (log g^{-2})^p`, any `p >= 1`, once `g_j <= γ0(L)`.
* **So the weaker condition is correct, with `g_j`.** Section 21.3 should replace `g_0` by `g_j` and drop
  "`p0(g_j) >= p0(g_0)`".
* REVIEW-3's stronger condition belongs to a merge range of order `log |Λ''|`, as the author says. It is satisfied
  anyway: S1-INDUCTION row 6 already requires `p0 >> M^d R^{d+1}` with `R_j >= (log g_j^{-2})^r`, `r >= 2`, which
  forces the exponent `p` far above 2.

### 3. Volume uniformity with the volume-first limit

* **Every estimate in section 21 is local:**
  * the failure bounds depend on `|Λ''_j|` and `R'_j`;
  * the collar widths depend on `g_j` and `log |Λ''_j|`;
  * the cross-scale event of section 1 depends on `|Λ''_j|` and the gaps.
  
  None depends on the total volume. So at fixed level `k` the bounds hold uniformly as the volume goes to infinity, and
  `MassGapLoc`'s order of limits (volume first, `Objects.lean` 476-481) is compatible. **Holds, given the two
  additions of section 1.**
* **Wording fix (FIXABLE, but it matters for the frozen region).** Section 21.2 applies Theorem A_good "to the two
  conditional laws on `Λ''_j`, given the configurations outside". Conditioning on outside **fine** configurations puts
  arbitrary, unpenalised content next to `∂Λ''` into the pattern weights. That is uniformity over fine content again.
  * It is not needed. Keep the global coupling of the two laws, and count every site outside `Λ''_j` as a source
    (`d <= 1`) in the static Dobrushin-Shlosman iteration.
  * The minimal solution with a source at distance `R'` gives `e^{-λ R'}` without conditioning on anything fine.
  * The truncation and bridging events are then events of the global law, bounded by the quenched H2 given coarse data
    only.

### Status (seventh follow-up)

| item | status |
|---|---|
| merging cascade (my sixth follow-up) | **resolved in substance**: fixed merge range per scale plus localisation plus truncation; no cascade |
| is it FS? | no; a localised, truncated alternative, sufficient for the volume-first limit and OS density (`o(1)`); the conclusion gains a polynomial tail `R'^{-d C_2}`, `C_2 > 1` needed |
| cross-level separation | **missing (FIXABLE):** accretion of born clusters onto inherited regions can bridge birth-collar gaps (allowed clusters of size `n_i` can be long chains); add a bridging failure event with its bound |
| inherited region sizes | **undercounted (FIXABLE):** up to `L^{d(j'-j)} n_{j'}` scale-`j` boxes; collar must grow with age `(d/m)(j'-j) log L`, still inside the birth collar |
| condition `p0 >> d log log g^{-2}` | **conclusion holds with `g_j`; derivation wrong** (`p0(g_j) <= p0(g_0)`, crude volume bound); use `log |Λ''_j| <= (d/b) g_j^{-2} + C(t)` |
| volume uniformity | holds, given the two additions; localise by sources, not by conditioning on outside fine configurations |
| N-2 overall | **GAP**: open; section 12 not started, and now also carries the cross-scale bridging event and age-dependent collars |

## Eighth follow-up

Read for this: `../m1-tools/UV-TV.md` sections 12 (parts 5 and 6, 12.1-12.5) and 23. REVIEW-3 was not read. Nothing
was built.

### Verdict (eighth follow-up)

* **My seventh-follow-up points are resolved.** I checked each one:
  * bridging is a truncation event;
  * inherited regions are capped through the annealed large set of the next scale's field, so persistence does not
    compound;
  * the condition now uses `g_j` with the scale-local region bound;
  * the outside of the region is a source in the global coupling.
* **The frozen region is kept out** of the annealed large-set bound (H2a), the quenched H2 and the global coupling: no
  statement conditions on unpenalised fine content.
* **H1 is not right as written.** It is stated as Dobrushin uniqueness for the pattern restricted to boxes, with a
  per-box influence `C η^{1/2} e^{-κ' d}` that must hold for **every** boundary pattern. A polymer that crosses a box
  face forces its continuation into the neighbouring box, so the influence of that neighbour is of order 1. This is
  obstruction (b) again, now in the discrete pattern gas. It does not condition on fine content, so the frozen region
  does not come back, but the stated bound fails.
  * The standard repair works and keeps the frozen region out: the convergent cluster expansion of the positive dilute
    gas (activities `η^{|γ|} e^{C|∂γ|}`, weak many-body terms), with the coupling built on polymer configurations
    (disagreement percolation on polymers, or the expansion's own locality).
  * It is a fourth write-out, missing from the verdict's list.
* **Two smaller corrections:**
  * the claim in 23.1 that the annealed bound "applies conditionally on `𝓗` too" is not justified, and is not needed:
    (A) and (B) are averaged statements, so failure events need only probabilities under the joint law;
  * 12.1's "admissibility is local" needs a check against Balaban's non-local admissibility conditions.
* **The verdict** "complete at paper-sketch level, apart from the named reading and three write-outs" is **nearly**
  accurate:
  * add H1's repair, which is standard and small, as a fourth write-out;
  * say plainly that the one unchecked reading (Balaban's normalisation terms `E_k(Z)` are the Gaussian fibre
    normalisations) now carries H2, H2a and R10 together: a single point of failure.
* **My long-standing N-2 GAP is reduced, not closed.** It is no longer "open, new analysis". The argument is complete at
  paper-sketch level, but it is not a proof until the normalisation reading is checked and the four write-outs are
  done. No FATAL finding.

### 1. My seventh-follow-up points

| point | status | check |
|---|---|---|
| cross-scale bridging | **resolved** | 23.2: two clusters of the large set of `X_{j+1}` are at least `2w_{j+1} + ell_B` scale-`(j+1)` units apart by construction, and every connection between them at scale `j` is a born chain spanning that gap. `G_j` (more than `n_j` bridges in a cluster) is priced by the quenched H2: `<= |Λ''_j| (C w^d η^{1/2})^{ell_br n_j}`. Correct. NIT: the cluster size bound `N_j` counts born components as if each were a bridge, but born clusters attached to one inherited piece need not bridge. Their number is bounded by the piece's boundary, so `N_j <~ n_j^2 L^d n'_{j+1}` up to constants, still polylogarithmic, and only `log N_j` enters the collar. |
| inherited-region size | **resolved** | 23.1: only the large set of `X_{j+1}` passes to scale `j`, and under the **law** of `X_{j+1}` its clusters are capped by `T_{j+1}` with `P <= |Λ''|^{-C_2}`. The annealed bound is the right object: under the unconditioned law, `X_i` being large on many boxes costs action per scale-`i` box (`η_i^{|A|}`), whatever the coarser fields do. So a coarse region that stays bad does not inflate the finer large set, unlike under the quenched chain. Every coarse state in the tower is law-distributed (resample in (A), trivially in (B)), so the bound applies. |
| condition with `g_j` | **resolved** | 23.3: `log |Λ''_j| <= (d/b) g_j^{-2} + C(t)`, `w_j <~ log g_j^{-2}`, condition `c p0(g_j)/2 > d log log g_j^{-2} + C log log p`. The inversion is withdrawn. |
| outside as source | **resolved** | 23.4: the global coupling, with the outside of `Λ''_j` and the truncation boxes counted as sources. Nothing fine is conditioned on. |
| polynomial tail | **resolved** | 23.5: stated, with `C_2 > 1`. The sum over scales in 12.4 is geometric from the top. |

### 2. Is the frozen region kept out everywhere?

* **H2a (annealed large-set Peierls): yes.** It is a statement about the unconditioned law of `X_i`, through Balaban's
  per-cube large-field factors and the averaged normalisation. No conditioning at all.
* **Quenched H2 (12.1): yes.** It conditions on the coarse field only, and holds pointwise where it is small field.
  * The lower bound for the denominator by one family of terms (the small-field alternative `ω_0` on `N_A`) is the
    right construction.
  * The ratio needs the normalisation reading (section 4).
  * NIT: "admissibility is local, so `ω_0` is admissible" needs a check. Balaban's admissible histories carry non-local
    conditions: components inside a `100 M R` cube are rectangular parallelepipeds ([III] (2.3)), regions have ages and
    the (i)/(ii) conditions, domains are nested across scales. Turning `N_A` small may split components and change
    their shapes or ages. A local completion very likely exists, but say which one.
* **The global coupling: yes** (23.4).
* **H1's gas: the frozen region stays out** (only patterns, which are discrete indices, are conditioned on), **but the
  stated influence bound is false in the worst case.**
  * The polymers `γ` are connected components of the discrete data, and can span several boxes.
  * In Dobrushin's formulation over the box variables `ω_b`, the influence of box `b'` on box `b` is a supremum over
    all boundary patterns. Take a pattern at `b'` where a polymer ends on the common face with `b`, in a shape that is
    only admissible if it continues into `b`. Then the conditional law of `ω_b` is forced, and the total-variation
    influence is of order 1, not `C η^{1/2}`.
  * This is the same worst-case-boundary failure as obstruction (b), now for the discrete gas.
* **The repair is standard:**
  * a positive polymer gas with activities `z(γ) <= η^{|γ|} e^{C|∂γ|}` and small many-body interactions
    (`|E(X)| <= C p^2 e^{-κ d}`, `d > r_int`) has a convergent cluster expansion (Kotecky-Preiss);
  * local pattern marginals then depend on far data (far coarse fields, `D`, the outside) with exponential decay;
  * a coupling of the two copies' pattern laws, with `P(ω_b != ω'_b)` bounded by connected polymer chains to the
    difference set, comes from disagreement percolation **on polymer configurations** (polymers as discrete objects,
    each priced by its activity), or directly from the expansion.
  
  None of this uses sup-over-boundary influences. FIXABLE, a fourth write-out.

### 3. The chaining (12.3, 12.4)

* **Structure: right.** Per scale, conditionally on the coarser data:
  1. couple the patterns;
  2. build the composite boxes;
  3. apply the coupling-form Dobrushin-Shlosman theorem with the sources (inherited disagreement, pattern
     disagreements, the outside, truncation boxes);
  4. turn expected counts into a front advance `a_j = C λ_j^{-1} log |Λ''_j|`, except on `|Λ''_j|^{-C_2}`.
  
  The front's remaining distance `R_j - Σ_{i >= j} L^{i-j} a_i >= R_j/2` holds once `t/ell >= C ell_B g_ell^{-2}`.
  The sum is dominated by the top scale, and `a_i` grows only like `g_i^{-2}`, linearly in `ell - i`, against
  `L^{ell-i}`. Correct.
* **Pricing of inherited composite boxes on the path:** by the annealed H2a one scale up, per scale-`(j+1)` box.
  Covering half a path of `R_j` scale-`j` units needs about `R_j/L` such boxes. That is exponentially small, and
  consistent with pricing at the own scale (my sixth follow-up, item 3).
* **Mixing quenched and annealed: consistent, if failure events are only averaged.**
  * The per-scale conclusions hold conditionally on coarser data on the good events. The failure events
    (`F, G, T`) enter as indicators whose probabilities are taken under the joint law, by a union bound over scales.
    That needs no independence, and the annealed bounds suffice because each copy is law-distributed.
  * **Drop the remark in 23.1** that the annealed bound "applies conditionally on `𝓗` too". Conditioning on the local
    block data `𝓗` near `F` changes the law near `B`. A pointwise-in-`𝓗` bound would need the quenched chain, where
    persistence **does** compound (H2 is silent under a coarse bad region). It is not needed, because (A) is an `L^1`
    statement averaged over `𝓗`. As written the remark is unjustified.
* **Result:** `P(the fine fields differ on B) <= C (R/ell)^d e^{-c t/(ell polylog)} + C (t/ell)^{-d(C_2 - 1)} -> 0`
  as `ell -> 0`, uniformly in the spacing and the volume. The bookkeeping is consistent at sketch level.

### 4. Is the final verdict accurate?

The verdict reads "complete at paper-sketch level, apart from one unchecked reading ([V] (1.70)-(1.71): `E_k` are the
Gaussian fibre normalisations) and three write-outs (Lemma C's cross term, the coupling-form theorem, the front-advance
estimate)". **Nearly accurate.** Corrections:
1. **Add H1's repair** (section 2) as a fourth write-out: replace Dobrushin uniqueness over box-restricted patterns by
   the cluster expansion of the positive dilute gas with a polymer-configuration coupling. Standard, small, but the
   present text claims a bound that is false in the worst case.
2. **Make the weight of the reading explicit.** The identification of Balaban's normalisation terms `E_k(Z)` with the
   Gaussian fibre normalisations of the small-field alternative is used pointwise (12.1, the quenched H2), averaged
   (H2a), and at scale `K` (R10). If it fails by a factor `(β^{3/2})^{#bonds}` per region, every rarity bound in the
   tower loses a `polylog` per box. That would be absorbed only if `p0 >> log β`, which holds (`p0` is polylog of
   high power). So even a failed reading is probably survivable. The verdict should say which way it degrades.
3. **Minor:** the admissibility check for `ω_0` (section 2), the `N_j` count (section 1), and the dropped `𝓗` remark
   (section 3).

### Status (eighth follow-up)

| item | status |
|---|---|
| seventh-follow-up points (bridging, size cap, condition, source wording, tail) | **resolved** (NIT: the `N_j` count) |
| frozen region in H2a, quenched H2, global coupling | **kept out** |
| frozen region in H1's gas | kept out (only discrete indices conditioned on); but the **stated Dobrushin influence bound fails in the worst case**; repair by the cluster expansion with a polymer coupling (FIXABLE, fourth write-out) |
| 12.1 comparison | right construction; rests on the normalisation reading; check locality of admissibility for `ω_0` (NIT) |
| 23.1 "conditionally on `𝓗` too" | unjustified and unnecessary; drop (NIT) |
| chaining and result (12.3, 12.4) | consistent at paper-sketch level, uniform in spacing and volume |
| final verdict | nearly accurate: add H1 as a fourth write-out; flag the normalisation reading as the single point that carries H2, H2a and R10, and say how it degrades |
| **N-2 (my long-standing GAP)** | **reduced:** no longer open new analysis; a complete paper-sketch argument, pending one reading and four write-outs. It stays a GAP until those are done |

## Ninth follow-up

Read for this: `../m1-tools/UV-TV.md` sections 24 and 25, and [V] pp. 387-389 ((1.92)-(1.97)) in the extracted text
layer. REVIEW-3 was not read. Nothing was built.

### Verdict (ninth follow-up)

* **All four of my eighth-follow-up points are resolved:**
  * H1 is now a cluster expansion of the positive dilute gas, with a polymer-configuration coupling and no supremum
    over boundaries;
  * the `𝓗` remark is dropped;
  * admissibility is handled by deleting whole history components;
  * the normalisation reading is named as the single point of failure, with its fallback analysed.
* **The per-cube restatement (rarity per `M R_j`-cube at rate `κ`) creates no new problem** for my earlier points
  (bridging, inherited regions, localisation, the cascade). If anything it simplifies them: the merge range now fits in
  one cube, so clusters are plain cube-adjacency components with entropy `3^d` per cube.
* **What changes is the type of smallness.** The per-cube rarity is now a **fixed** constant `C e^{-c κ}`, no longer
  `e^{-c p0(g_j)} -> 0`. So every subcriticality, the Kotecky-Preiss condition for H1 and the tail condition rest on
  "`κ` may be taken large for given `L`" ([III] p. 260). That is a dependency on Balaban's construction (in practice it
  costs a larger `M` or a smaller `γ0`), and the verdict should list it next to the normalisation reading.
* **The final verdict is accurate,** apart from that omission and one caveat on the admissibility check, which was done
  against a poor scan.
* **N-2 remains a GAP (reduced):** a complete paper-sketch argument, owing one reading (or its fallback) and four
  write-outs. No FATAL finding.

### 1. My eighth-follow-up points

| point | status | check |
|---|---|---|
| H1 stated via box-variable Dobrushin (false in the worst case) | **resolved** (write-out 4 owed) | 24.2: the polymers are connected components of the discrete data under cube adjacency, with activities `z(γ) <= e^{-p0} (C e^{-c κ})^{#cubes}` where the coarse field is small. The soft interactions are Mayer-expanded into links of size `C p^2 e^{-κ d}`. The effective interaction is taken correctly: as `log` of the integrated polymer measures minus the single-polymer parts, since cluster terms meeting several polymers depend on boundary fields inside the `T`-operations. This is a Kotecky-Preiss setting with a convergent expansion for `κ` large, and the coupling is disagreement percolation on polymer configurations. No supremum over boundary patterns enters, so the forced-continuation problem is gone. |
| "conditionally on `𝓗`" remark | **resolved** | Dropped (24.3). The `T_i` are taken over a deterministic ball containing `Λ''_i`, and every coarse state is law-distributed by induction. |
| admissibility of `ω_0` | **resolved in substance**; caveat | 24.1 step 1: delete every connected history component meeting `N_A`, at all scales. Shape conditions belong to a single component. Merging (adding layers, parallelepiped rule) is a function of components that are joined into one history component anyway. Distance conditions only relax when regions are removed. That is the right argument. **Caveat:** checked "as read; the scan of (2.3)-(2.9) is poor". Weak, but low risk. List it with the readings. |
| normalisation reading as a single point of failure | **resolved** | Section 25 states it, with the refined form (small-field fibre integral `>= e^{-δ_j |region|}` times the Gaussian normalisation, `δ_j (M R_j)^d -> 0`). The fallback is analysed below. |

### 2. Does the per-cube restatement create a new issue for my earlier points?

* **Merging and cascade (sixth, seventh):** no.
  * The merge range `2w_j + ell_B + 2 r_int + 2` is polylog in `log g_j^{-2}`, while `M R_j >= M (log g_j^{-2})^2` (with
    `r >= 2`). So the range fits inside one `Q_j`-cube.
  * Clusters are cube-adjacency components, with lattice-animal entropy `(3^d)^n`, which is fixed. There is no
    size-dependent reach, so no cascade.
  * Distinct components are at least one cube apart, which is `>= 2 w_j`, so collars are disjoint.
* **Bridging (seventh, eighth):** no.
  * Inherited pieces from different scale-`(j+1)` components are at least one `Q_{j+1}`-cube apart, about `L` cubes at
    scale `j`, depending on how `R_{j+1}` compares with `R_j` (Balaban's (1.81) note that `R_{m+1} = L R_m` at some
    steps).
  * A bridge needs `>= c L` born cubes, at cost `(C e^{-c κ/2})^{c L}`. The truncation `G_j` with
    `n_j = C_1 log |Λ''_j| / (c κ)` gives `|Λ''_j|^{-C_2}`.
  * The unpriced band (born cubes within one cube of an inherited piece, where the quenched H2 needs the coarse field
    small on a one-cube neighbourhood) is absorbed into the inherited composite box. That is my seventh-follow-up
    accretion point, now closed by construction: the band factor is `2^d` in `N_j`.
* **Inherited regions (seventh, eighth):** no. They are capped by `T_{j+1}` with the annealed H2a per cube. Persistence
  still does not compound, for the same reason as before: the annealed law of `X_{j+1}` prices its own large set per
  cube.
* **Localisation (seventh, eighth):** no. `Λ''_j` and the truncations are counted in cubes, and every bound is local.
  The outside is still a source in the global coupling.
* **The front and the final rate:** unchanged in form.
  * The rate per scale-`j` unit becomes `c κ/(M R_j)`.
  * The front advance needs `t/ell >= C M R_ell g_ell^{-2}/κ`, which is polylog times `g_ell^{-2}` and holds as
    `ell -> 0`.
  * The final bound `C (R/ell)^d e^{-c κ t/(ell M R_ell polylog)} + C (t/ell)^{-d(C_2 - 1)} -> 0` still holds.
* **One check on the per-cube Peierls.** [V] (1.92)-(1.97) bounds activities by `c1 e^{-(1+β) κ d(X')}`, with `d` the
  linear size (tree length) in `M R`-cube units. For a connected union of `n` cubes, `d >= n - 1` up to a constant, so
  `e^{-κ d}` does give a rate per cube. The per-polymer factor `c1` (taken `= e^{-p0}`, conservatively) is not needed
  for the counts. Correct as used.

### 3. The fallback and the verdict

* **The fallback is analysed correctly.**
  * If the normalisation reading fails, each `Q_j`-cube loses about `exp(C (M R_j)^d log β)` (the top variables'
    Gaussian normalisation), which a fixed rate `κ` cannot absorb.
  * It is absorbed by a per-cube margin `e^{-c p0}` that survives Balaban's entropy induction, given
    `c p0 >= C (M R_j)^d log β`.
  * That condition is implied by his `p0 >> M^d R^{d+1}`, since `R >= (log g^{-2})^2 >= log β`.
  * Whether such a per-cube margin survives (1.80)-(1.89) is a second reading:
    * (1.82)'s win condition `A_1^2 p0^2 >= O(1) M^d L^{d+1} R^{d+2}` leaves about `A_1^2 p0^2/2` per cube after the
      entropy charge, which makes it plausible;
    * but (1.89) states only a per-component `p0` and a rate `κ` per unit of linear size.
  * "At least one of the two readings must hold" is the honest statement.
* **The verdict** ("complete at paper-sketch level, one reading as a single point of failure with a fallback, four
  write-outs") is **accurate**, with two additions:
  1. **List the `κ`-large dependency.** The subcriticality `3^d C e^{-c κ/2} < 1/2`, H1's Kotecky-Preiss condition, and
     the tail condition `κ >= 4 log L + log C` (13.1) all require `κ` large for given `L`. The note cites [III] p. 260
     for this. It should be pinned as a reading of how `κ`, `M` and `γ0` trade off. It is likely harmless, but it is
     now load-bearing for every rarity bound, where before the smallness came from `p0(g) -> infinity`.
  2. **List the admissibility check** as done against a poor scan (low risk).

### Status (ninth follow-up)

| item | status |
|---|---|
| H1 (eighth follow-up) | resolved in design (cluster expansion plus polymer-configuration coupling); write-out 4 owed |
| `𝓗` remark | resolved (dropped) |
| admissibility of `ω_0` | resolved in substance (delete whole history components); checked against a poor scan (low risk) |
| normalisation reading | stated as a single point of failure; fallback (per-cube `p0` margin, second reading) correctly analysed |
| per-cube restatement vs bridging, inherited regions, localisation, cascade | **no new issue**; simplifies (cube-adjacency clusters, band factor `2^d`) |
| new dependency | rarity now fixed (`C e^{-c κ}`); "`κ` large for given `L`" ([III] p. 260) is load-bearing and should be listed with the readings |
| final verdict | accurate, plus the `κ` dependency and the scan caveat |
| **N-2** | **GAP (reduced):** complete paper-sketch argument; owes the normalisation reading (or its fallback) and four write-outs |

## Tenth follow-up

Read for this: `../m1-review/EK-DERIVATION.md` in full, `../m1-tools/UV-TV.md` 26 and 25 (revised). For the parts of
[V] pp. 379-390 that the re-proof touches, I compared against the extracted text layer, with the page-image readings of
`EK-DERIVATION.md` as the reference where the OCR is poor. REVIEW-3 was not read. Nothing was built.

### Verdict (tenth follow-up)

* **Route (c), Balaban's induction re-run with a kept slack `c_σ p0^2` per birth-scale `M R`-cube, is the right fix.**
  * It is a re-proof, internal to Balaban's own bounds, of the unconditioned large-field weights. The frozen region
    stays out: the slack is a property of the terms of `ρ_j`, and it is used only inside ratios conditioned on coarse
    data (quenched H2), or under the law (H2a, R10).
  * It removes reading (b), which `EK-DERIVATION.md` shows is not in Balaban, and the withdrawn `β^{3/2}` fallback.
  * The steps I can follow against the text are plausible:
    * halving the creation term, which needs (P0);
    * keeping the slack unchanged in (1.83) and summed in (1.85);
    * carrying `e^{-σ}` outside the entropy sums of (1.92)-(1.96), which spend only the per-component `p0` and `κ`;
    * the conversion to current-scale cubes, which now uses `p0(g_{j_b}) >= p0(g_k)` in the right direction.
* **None of my earlier points changes.** Bridging, inherited regions, localisation and the cascade are untouched; the
  slack only strengthens the per-cube rarity. The one-box label contraction's condition `κ >= 4 log L + log C` is
  compatible with "`κ` large at the cost of larger `M` and smaller `γ`" ([I] Theorem 3, now cited).
* **Two points the verdict does not yet reflect:**
  1. **(1.97') as stated covers only regions with births.** Regions from step 4 (new large fields of the preparatory
     operations) carry only the per-component `e^{-p0}`, no `p0^2` slack. Their cubes must be split off from `A` and
     priced through (P1). The text says (P1) is needed "in one place", but the statement (1.97') and its use in
     12.1/24.1 do not split `A`. NIT, but it should be written that way.
  2. **`EK-DERIVATION.md` Q4 also bears on Lemma C and H3,** not only on the denominator.
     * Balaban bounds the field-dependent small-field terms only as `O(1)` per site ([III] Theorem 2), or through
       analyticity on his domains.
     * H3's Pinsker step and Lemma C's cross term are written for "a Gaussian times **small** analytic terms", with
       factors `1 + O(δ)`.
     * The source supplies smallness only as a **constant** per `M`-cube, through the ratio of the fluctuation range
       to the analyticity radius, about `(A0/C0)^2 (log g^{-2})^{2(p0-q0)}`. It does not supply `δ_j -> 0`.
     * That is probably enough, since both arguments need only a weak perturbation and exponential decay, which
       Balaban's own cluster expansion of the fluctuation measure gives. But write-outs 1 (Lemma C) and 3 (front
       advance through H3) must be done with that smallness, not with `δ -> 0`. This belongs on the dependency list.
* **The verdict "UV-TV holds given (c), a re-proof" is nearly accurate.** It should read "has a complete paper-sketch
  argument given (c)", with the four write-outs, (c)'s check list including (P1) against Balaban's exponent chain, and
  the two points above.
* **N-2 stays a GAP (reduced)** until (c) is written and checked and the write-outs are done. No FATAL finding.

### 1. Does the re-proof keep the frozen region out?

**Yes.**
* (1.80') and (1.97') are statements about Balaban's own terms: creation factors, the induction, and the activities of
  the unconditioned representation. Nothing is conditioned on.
* M1 uses them only:
  * in the quenched H2 (12.1, 24.1), a ratio of pattern weights **given the coarse field**, small field near `A`;
  * in H2a and R10's normalisation, under the law.
* The denominator side now uses only [III] Theorem 2's `O(1)` per site on the small-field alternative, in a coarse
  region where the coarse field is small. That is again conditioned on coarse data only, and the loss
  `C 3^d (M R)^d` per cube is paid by the slack under (P2).
* No unpenalised fine content enters anywhere.
* **Double use?** The same carried region appears in `Bad_j` at several scales of the tower. That is not a double use
  of the slack: each scale's quenched bound is a separate conditional probability, computed from its own normalised
  law. The tower multiplies conditional probabilities by the chain rule, so each conditional factor may use the term's
  full slack.

### 2. The re-proof itself (what I could check)

| step | assessment |
|---|---|
| creation, (1.79) | unchanged source of both halves. Correct. |
| first step, (1.82): halving | Balaban's condition becomes (P0), with the constant doubled. Both sides are powers of `log g^{-2}`, and his condition already makes the `p0^2` side win, so (P0) holds for small `g`. Plausible. |
| (1.83), no new field | `σ` unchanged, costs to `κ`. Correct. |
| (1.83), preparatory new field | `κ_{j+1} := p0 - costs` as Balaban; old `σ` kept. Correct, **but** the new region has no `p0^2` slack (point 1 above). |
| merging (1.85)-(1.88) | the new regions' `p0^2` term is halved, and the tree argument uses the parts' `κ` and the `p0` surplus. So only the single-new-region case re-invokes (P0). Plausible; I cannot verify (1.86)-(1.88) line by line from the scan, and it is on (c)'s check list. |
| release (1.89) | `T'_k(X) 1 <= e^{-σ_k(X)} e^{-2(1+β0)^{-1} p0}`. Follows from the above. |
| activities (1.92)-(1.97) | `e^{-σ}` is carried outside. Balaban's entropy is paid by the per-component `p0`, the `κ` decay, and the "admissible sequences" factor `exp(O(1)(M R_j)^{-d} |Z_j|)` before (1.79), which is already a cost charged to `κ`. So `σ` is not needed there. Plausible. |
| conversion to current-scale cubes | `#cubes_k(X) <= d'_k(X) + 1` for connected unions, (1.81)'s scaling `d'_k <= 2^{-(k-j)} d'_j + 64^d`, and `p0(g_{j_b}) >= p0(g_k)` (correct direction). Gives `Σ σ >= (c_σ/C) p0^2(g_k) |A_births|`. Correct, for the cubes covered by regions with births (point 1). |
| (P2) from (P0) | `c'_σ p0^2 >= 2C 3^d (M R)^d` follows from `A_1^2 p0^2 >~ M^d L^{d+1} R^{d+2}`. Correct. |
| (P1) | `p0 >= C(κ + M^d) 100^d R^d`, the same form as Balaban's p. 389 condition. Compatibility with `2 p1 - (d+5) r0 > p0` is on the check list. Fine. |

### 3. Do my earlier points change?

* **Bridging, inherited regions, localisation, cascade:** no change. The slack strengthens the per-cube rarity under
  both the quenched H2 and H2a. The truncations, merge range (one cube) and pricing at the own scale are as in the
  ninth follow-up.
* **`κ` large (ninth follow-up):** now cited ([I] Theorem 3: `κ >= κ0` free, `M >= M(κ)`, `γ` smaller; `γ0` absolute).
  * M1's conditions on `κ` (subcriticality `C 200^d e^{-c κ/2} < 1/2`, H1's Kotecky-Preiss condition,
    `κ >= 4 log L + log C`) compare `κ` with constants that do not grow with `M`: lattice-animal entropy, the
    compatibility range in cubes, and `L`.
  * As `EK-DERIVATION.md` Q3 asks, I looked for M1 constants hiding `e^{O(κ)}` or `M^q`. The denominator loss
    `C 3^d (M R)^d` grows with `M`, but it is paid by `p0^2`, not by `κ`, so a larger `M(κ)` only tightens (P0)-(P2),
    which hold for small `g`. I found no other.
* **Labels (one-box contraction):** unaffected. Their release bound may now also use the slack, which only helps.

### 4. Is the verdict and dependency list accurate?

Section 25 (revised): "complete at paper-sketch level given (c)". It lists:
* (c) as a re-proof and single point of failure;
* (a) as citation-level, correct in substance;
* (b) as not in Balaban and not needed;
* `κ` as a citation;
* admissibility from a poor scan;
* four write-outs and (c)'s check list.

**Accurate, with three additions:**
1. **Split (1.97')** into regions with births (slack `c'_σ p0^2` per current cube) and preparatory-only regions (per
   component `e^{-p0}`, at most `100^d` cubes, priced by (P1)). Use the split in 12.1/24.1. NIT.
2. **Add Q4 to the dependencies of write-outs 1 and 3.** Lemma C's cross term and H3's Pinsker step must use only the
   smallness the source gives: a constant per `M`-cube from analyticity, `(A0/C0)^2 (log g^{-2})^{2(p0-q0)}` with
   `q0 >= p0`, plus Balaban's cluster expansion for decay. "Factors `1 + O(δ)` with `δ -> 0`" is not available. This
   is probably sufficient, but it is a dependency.
3. **Wording.** "UV-TV holds given (c)" should be "UV-TV has a complete paper-sketch argument given (c)". It still owes
   four write-outs, and (c) is itself a re-proof still to be checked (26.4).

### Status (tenth follow-up)

| item | status |
|---|---|
| frozen region under route (c) | **kept out** (re-proof is about unconditioned terms; used only in coarse-conditioned or annealed ratios) |
| re-proof (c), steps I could check | plausible; merging (1.86)-(1.88) not verifiable line by line from the scan (on the check list) |
| (1.97') | needs the split into birth-covered and preparatory-only cubes (NIT) |
| earlier points (bridging, inherited regions, localisation, cascade, labels) | unchanged; the slack only strengthens them |
| `κ` large | now a citation ([I] Theorem 3); no hidden `e^{O(κ)}` or `M^q` found in M1's `κ`-conditions |
| Q4 (small-field non-Gaussian part only `O(1)` per site in the source) | resolved for the denominator by the slack; **still a dependency for Lemma C and H3**, which must use constant-size analytic smallness, not `δ -> 0` |
| verdict | nearly accurate: add the split, the Q4 dependency, and say "paper-sketch argument" rather than "holds" |
| **N-2** | **GAP (reduced):** paper-sketch argument complete given (c); owes (c)'s write-up and checks and four write-outs |

## Eleventh follow-up

Read for this: `../m1-tools/UV-TV.md` 27 and 28, and again 22.2-22.5 (the column condition and the earlier form of the
theorem). REVIEW-3 was not read. Nothing was built.

### Verdict (eleventh follow-up)

* **The coupling-form Dobrushin-Shlosman theorem of 28.1-28.2 is correct.** I checked each step:
  * the averaged update preserves both marginals and the supports;
  * one step gives `Φ(Tπ) <= Φ(π) - (1/N)(1 - γ) Σ_x c(x) v(x) d(x) + s/N`, using the column condition with the full
    coverage `c(z)`;
  * hence `θ = 1 - (1 - γ) c_min/N`;
  * iterating from the product coupling gives the bound up to `ε` at a finite iterate.
  
  Removing the weak limit (22.5's portmanteau and compactness step) is an improvement: everything is finite and
  measurable.
* **It avoids every worst-case-boundary and frozen-region issue I raised:**
  * hypothesis (I) is required only for pairs **in the supports**, and the iteration never leaves them;
  * the supports are those of the pattern-conditioned measures, so near good boxes, and in collars, they contain only
    small-field configurations;
  * bad clusters are composite **good** blocks carrying Lemma C, never sources, so nothing saturates (section 15's
    obstruction does not arise);
  * the source term enters only once, through `s`.
* **The instantiation (28.3) is consistent with the localisation and with the global coupling.**
  * The theorem runs on the whole finite configuration.
  * Everything outside `Λ''_j` is source blocks from the same translate family, so the coverage there is
    `~ ell_B^d` and the column condition holds at sites near `∂Λ''_j`.
  * The weighted source sum `s` over the outside converges to `C e^{-λ R'} poly(R')`, independent of the volume.
  * The block family of 22.3 (multiplicity `n_W` for composite boxes, good boxes overlapping the collar,
    `ell_B >= C (log p/m)^{2d+1}/γ^2`) satisfies the column condition at every kind of site. It refines my sixth
    follow-up suggestion, which overlooked that the inner collar layer is covered only by `W`.
* **My tenth-follow-up points are resolved.**
* **Three NITs:**
  * the "truncation events" listed as source blocks are not blocks;
  * the numbering of the write-outs is inconsistent between 25, 27.9 and 28;
  * the covariance form for (B) should be written through a construction that stays in the supports.
* **N-2 stays a GAP, reduced further:** write-out 1 is done. It owes Lemma C's cross term, the front-advance estimate,
  H1's polymer coupling, and the write-up of (c). No FATAL finding.

### 1. The theorem (28.1-28.2)

| step | check |
|---|---|
| (S) specifications | Each kernel acts only on its block, depends only on the outside, is invariant (DLR), and preserves the support. That is what makes `Tπ` a coupling supported in `Ω_0 × Ω'_0`. Correct. |
| (C) block couplings | A measurable kernel coupling `q_b(σ, ·)` and `q'_b(σ', ·)` for pairs in the supports. Correct. Measurability: the explicit maximal coupling from densities with respect to a common reference is measurable, and the nested (far-to-near) version is measurable step by step. Fine. |
| (I) influence | Weighted, on good blocks only, for pairs in the supports. The clause "if `σ = σ'` off `B_b`, the pair agrees on `B_b`" requires `q_b = q'_b` there. For UV-TV that is H0's agreement: good blocks are at distance `> r_int` from the source, the pattern disagreements and the coarse-data disagreements, and carry no links. Correct as instantiated. |
| (K) column condition | Per site, with the full coverage including source blocks. This is the condition I asked for in the sixth follow-up. Correct. |
| one step and average | `Φ(Tπ) = (1/N)[Σ_x v d (N - c) + Σ_good (I-terms) + Σ_src v]`. (K) turns the middle term into `<= γ Σ v d c`. Hence the contraction `θ` and the fixed point `s/((1 - γ) c_min)`. Correct. |
| iteration | From `μ ⊗ μ'`, `Φ(π_0) <= Σ v < ∞` on a finite `Λ`. Some `n` of order `N log(Φ_0/ε)/((1 - γ) c_min)` suffices. No limit is needed. Correct. |
| consequence | `|μ(F) - μ'(F)| <= 2‖F‖ (min_A v)^{-1} Φ`. Correct. |

**Weights.** With `v = e^{-λ dist_ω(·, A)}` and composite boxes contracted to diameter 1, `v` varies by at most `e^λ`
on a composite block. So Lemma C's unweighted `k_W(z)` turns into (I) with `K_W = k_W e^{λ E_W}`, `E_W <= 2`. For good
boxes, `e^{λ(ell_B + C)} = O(1)` with `λ = 1/ell_B`. Consistent with 22.3.

### 2. Worst-case boundaries and the frozen region

* **Pattern-conditioned supports.** Given `ω`, the support of `μ_ω` near a good box consists of small-field
  configurations:
  * the small-field characteristic functions of the pattern;
  * no large-field domains, unreleased regions, labels, Z2 excitations or links there (these are all bad by
    definition).
  
  The same holds in the collar of a composite box. So (I) over pairs in the supports is exactly H3 and Lemma C as
  proved, with no hybrid and no off-support boundary.
* **Bad clusters as good composite blocks.** Their influence bound (Lemma C) needs only the collar's small-field law,
  never a bound on the multimodal inside. Nothing is quantified over unpenalised fine content.
* **Sources.** No influence bound is needed on source blocks; they cost only through `s`.
* **So the two failure modes of the earlier rounds do not occur here:**
  * the sup over all boundaries (obstruction (b), and H1's forced continuation);
  * saturation of the dynamic coupling (section 15).

### 3. Consistency with the localisation and the global coupling

* **Global coupling.** The theorem couples `μ_ω` and `μ'_{ω'}` on the whole finite configuration. Nothing outside
  `Λ''_j` is conditioned on. The outside is covered by source blocks.
* **Column condition near `∂Λ''_j`.** Sites just outside `Λ''_j` exert influence on good boxes inside. They are
  covered by the source blocks, which are translates of the same box family, so `c(z) ~ ell_B^d`, and (K) holds there
  as in the bulk.
* **Volume uniformity.** `s = Σ_{src blocks} Σ_{y} v(y) <= Σ_{y outside Λ''} c(y) e^{-λ dist_ω(y, A)} <= C ell_B^d Σ_{r >=
  R'} r^{d-1} e^{-λ r}`. That is uniform in the volume.
  * `dist_ω` outside `Λ''` does not matter, since every such site is a source.
  * Inside `Λ''`, the contraction of `dist_ω` by composite boxes is controlled by the half-path covering estimate
    (21.5, 24.1).
* **Truncation events (NIT).** 28.3 lists them among the "boxes meeting the source". They are events of the patterns
  and the coarse data, not sets of blocks. The right form is a case split before the theorem is applied: on
  `F_j ∪ G_j ∪ T_j ∪ T_{j+1}` bound the disagreement by 1, and on the complement apply the theorem. Both events are
  measurable in `(ω, ω', 𝒳)`, which are fixed first. This only changes wording.
* **(B), covariance form (NIT).** 28.2 says the same theorem applies "to the hybrid construction of 19".
  * The cleaner route stays in the supports. Apply the theorem to `μ_ω(· | η on A)` and `μ_ω(· | η' on A)`, with the
    blocks meeting `A` as sources and `η, η'` in the support (small field near `A` if `A` is pattern-good, otherwise
    `A` is in a source). This bounds the influence of `A`'s content on `θA`, and hence the conditional covariance.
  * It conditions on fine content near `A`, but only inside the support, and needs no estimate on it, since `A` is a
    source. So it is not a frozen region.
  * If the hybrid of 19 is kept instead, check that it never evaluates a specification off the supports.

### 4. My tenth-follow-up points

| point | status |
|---|---|
| split of (1.97') into birth-covered and preparatory-only cubes | **resolved:** 27.5. Every region descends from a creation event and inherits its slack. A preparatory region `Z = S(Z_0)` keeps `ψ(Z_0)`, and its current cubes are covered by (1.81)'s scaling of `Z_0`. This rests on preparatory domains staying inside `S(Z_0)` ([V] p. 384; [IV] Sect. 1 not re-read), with (P1) kept as insurance. Acceptable. |
| Q4: Lemma C and H3 may use only constant-size smallness | **resolved:** 27.9 puts it on the dependency list; those write-outs may use only [III] Theorem 2's `O(1)` per site, constant analyticity smallness per `M`-cube, [V] (1.2)'s explicit cubic terms, and the cluster expansion. |
| verdict wording ("paper-sketch argument given (c)") | **resolved** (27.10). |
| also checked | 27.3, `g_birth <= (1 + β0) g_k` ([III] (2.6)-(2.7)), so `p0(g_birth) >= (1 + β0)^{-1} p0(g_k)` (conservative, absorbed by (P2)): correct. 27.7, the top variables' Gaussian normalisation is the next step's constant, so (P2) needs an extra `log β` per site, which (P0) covers: correct. 27.4, unreleased regions take their slack from (1.79)/(1.80'): correct. |

**NIT:** the numbering of the write-outs is inconsistent.
* 25 (revised) lists: 1 Lemma C, 2 coupling-form theorem, 3 front advance, 4 H1.
* 28 calls the coupling-form theorem "write-out 1".
* 27.9 refers to "write-outs 2 and 4" for Lemma C and H3.

Renumber once.

### Status (eleventh follow-up)

| item | status |
|---|---|
| coupling-form Dobrushin-Shlosman theorem (28) | **correct**; finite iterate, no limit; Lean-ready as stated |
| worst-case boundaries, frozen region, saturation | **avoided**: (I) only on supports; bad clusters as good composite blocks via Lemma C; sources only through `s` |
| instantiation (28.3) with localisation and global coupling | **consistent**; volume-uniform source sum; NITs: truncation events as a case split, not blocks; (B) via conditioning inside the supports, or check the hybrid stays in support |
| column condition with multiplicity (22.3) | correct; refines my sixth-follow-up suggestion (the inner collar layer needs `n_W`) |
| tenth-follow-up points | resolved |
| write-out numbering | inconsistent (NIT) |
| **N-2** | **GAP (reduced):** write-out "coupling-form theorem" done; still owes Lemma C's cross term (constant smallness only), the front advance, H1's polymer coupling, and (c)'s write-up |

## Twelfth follow-up

Read for this: `../m1-tools/UV-TV.md` 29. REVIEW-3 was not read. Nothing was built.

### Verdict (twelfth follow-up)

* **Write-out 2 (Lemma C's cross term and the collar coupling) is correct at paper level.**
* **It respects the constant-size restriction throughout.** The only inputs are:
  * Balaban's `O(1)` per site and `C_0 e^{-κ d}` per localised term;
  * the decay rates `m` and `κ`;
  * the data size `p = ε_j/g_j` (polylog).
  
  Every smallness comes from decay across the collar width `w`, never from a `δ -> 0`.
* **The fixed-boundary-data reading does not bring back a frozen region:**
  * the data held fixed are small-field configurations in the support of the pattern-conditioned measure (the inner
    layer `I`, the outer layer `O`, and in 29.5 the far collar sites `F`);
  * they are fixed for one renormalisation step on a finite collar, never carried through scales;
  * the bounds are uniform over such data.
  
  The frozen region of `SKETCH-STEPS.md` 2 was arbitrary, unpenalised fine content (possibly large field) held fixed
  through all scales. Neither feature is present.
* **The bound is uniform in the volume.** Everything is local to the composite box `W`. The only non-local inputs (the
  cluster size bound `N (M R)^d` and the collar width) depend on `log |Λ''|`, not on the total volume.
* **Three NITs:**
  * the inner and outer Dirichlet layers should be unions of `L`-blocks, because of the fibre constraint;
  * the constant in the collar width contains Balaban's `E_0(M)`, which grows when `κ` is raised. It enters only
    logarithmically, but should be named;
  * the expansion of the characteristic functions relies on Balaban's analyticity domain containing their support
    (`q0 >= p0`, `EK-DERIVATION.md` Q4).
* **N-2 stays a GAP, reduced further.** Write-outs 1 and 2 are done. It owes the front advance, H1's polymer coupling,
  and the write-up of (c). No FATAL finding.

### 1. Is the constant-size restriction respected?

| place | input used | check |
|---|---|---|
| 29.2 (1), background | [15] Theorem 1, (190); [13] Theorems 3.12, 3.13: `|∂U_bg/∂data| <= C e^{-m d}` | decay only; constant `C`. Fine. |
| 29.2 (2), classical cross term | `⟨Δc, G_{I,O} Δσ⟩/g^2` with `|Δc|, |Δσ| <= 2C ε_j` | gives `p^2 e^{-m d}`; `p^2` is the data size, not a small parameter. Higher orders carry extra `ε` and the same decay. Fine. |
| 29.2 (3), fluctuation part | cluster expansion, localised terms `C_0 e^{-κ d(X)}` ([I] (1.18), [III] Theorem 2) | constant size; inherited E-terms as local factors of the same size. Fine. |
| 29.2 (4), characteristic functions | `χ = Π(1 - χ^c_□)`, `χ^c` at `e^{-c p^2}` per cube, entering through connected clusters | needs `exp(A_j)` controlled on the smooth cut-off's support, which lies inside Balaban's analyticity domain since `α_0 >= 2 ε` when `q0 >= p0` (`EK-DERIVATION.md` Q4). Balaban's own handling of the characteristic functions (their derivatives in [III] (3.37)) is the citation. NIT: state it. |
| 29.3, mixed variation | sum of the three cross terms over `x ∈ I`, `z ∈ Z` | `Σ_x e^{-m d(x, z)} <= C_m e^{-m' d(z, I)}`, with no interface factor. `C'(p^2 + C_0)` prefactor. Fine. |
| 29.4, total variation and Lemma C | `TV <= e^{2M} - 1 <= 4M` for `M <= 1/4`; `k_W(z) <= k_collar(z) + (|K| + C|I|(log p/m)^d) 4C(p^2 + C_0) e^{-m' d(z, I)}` | correct. Collar `w >= 2 r_int + (1/m') log(C N (M R)^d p^2/ε_W)`. The constant `C` here contains Balaban's `E_0`, which depends on `M`, and `M = M(κ)` grows when `κ` is raised ([I] Theorem 3). It enters `w` only through a logarithm, so it is harmless. NIT: name it (`EK-DERIVATION.md` Q3's caution). |
| 29.5, collar coupling (Pinsker redone) | `Cov_t(f, L_t) = Cov_t(f, E_t[L_t | φ_F])`, with `‖L_t‖ <= C p^2` | the conditional expectation's dependence on `φ_F` comes from the same cluster expansion with Dirichlet data; constant size times decay. The bound on `∂_t` of the E-terms uses Cauchy with `|Δσ|/α_0 <~ p/(log g^{-2})^{q0} = O(1)` for `q0 >= p0`. Fine. `TV_r <= C (p^2 + C_0) p^2 Σ_z r^{d-1} e^{-m' r} + C e^{-c p^2} e^{-κ r}`; `k_collar <= C (log p/m')^d`. Correct. |

**Verdict on the restriction: respected.** The previous "`1 + O(δ)`" of 19 is gone, and the price is only a polylog
prefactor in `p`, which shifts the crossover radius by `O(log p/m')`.

### 2. Does the fixed-boundary-data reading bring back a frozen region?

**No.**
* **What is held fixed:**
  * in 29.3-29.4, the inner data `c` enter `Z(c, σ)` only through the inner layer `I` (finite range, H0; good collar
    boxes carry no links, and links from `K` are cluster edges);
  * the outer data `σ` enter only through the outer layer `O`;
  * in 29.5, the far collar sites `F`.
  
  All of these are pattern-good collar sites, so the configurations there are small field and lie in the support of
  `μ_ω`. **The multimodal content of `K` is never held fixed inside an estimate:** it sits in `w(c)`, which cancels in
  the ratio.
* **For how long:** for one step, the integral over the scale-`j` collar variables with `A_j` (which already contains
  all finer scales as E-terms) on a finite domain. Nothing is carried through the induction with frozen content.
* **Uniformity over the data:** all bounds are sup over small-field data within `C ε_j` of a common background. Those
  are exactly the configurations Balaban's small-field estimates control.
* **Is the reading plausible?** Yes. Balaban's analysis always runs on small-field domains `Ω_k` whose complements are
  large-field regions with given fields. His localisation ([III] (2.13)-(2.15)) and [15]'s variational problem on a
  domain with boundary data are built for this. The boundary fields there are regular, as here. Citation level, as the
  note says.
* **Contrast with the frozen region (`SKETCH-STEPS.md` 2):** that was the content of `supp F`, arbitrary and possibly
  large field, with no action penalty, held fixed through `log_L(ell/a)` steps. None of these features is present.

### 3. Uniformity in the volume

* Every quantity in 29.2-29.5 is local to `W`: the collar, the layers `I`, `O`, the cluster `K`. The bounds depend on
  `|K| <= N (M R)^d`, `|I|`, `p`, `C_0`, `m`, `κ`.
* `N` depends on `log |Λ''_j|` (24.1), a local region of the size of `dist(B, D)`, never on the total volume.
* So Lemma C's `k_W` and the collar width are uniform in the volume. Combined with the theorem of 28 (eleventh
  follow-up), the per-scale conclusion is uniform in the volume, as `MassGapLoc`'s volume-first limit needs.

### 4. Smaller points

* **Layers and the fibre constraint (NIT).** The block constraint `block(V_j) = X_{j+1}` acts inside `L`-blocks. If `I`
  or `O` (width `r_int`) cut an `L`-block, a constraint straddles the Dirichlet boundary. [15]'s formulation on domains
  can handle that, but it is simpler to round `r_int` up to a multiple of `L`, so that `I`, `O` and the integrated
  region are unions of `L`-blocks.
* **Collar width versus `M R_j`.** `w ~ (1/m') log(...)`, with `m' = min(m, κ)/2`. The fluctuation mass `m` in scale-`j`
  units may be of order `L^{-2}` (Poincare). Then `w ~ L^2 log(...)`, still far below `M R_j >= M (log g_j^{-2})^2` at
  small `g`. So the merge-range-within-one-cube argument of 24.1 is unaffected. Worth one line.
* **Goldstein's simultaneous maximal coupling** for the nested far sets (29.5) exists and is measurable. Fine.

### Status (twelfth follow-up)

| item | status |
|---|---|
| write-out 2 (Lemma C cross term, collar coupling) | **correct at paper level** |
| constant-size restriction | **respected**: `O(1)` per site, `C_0 e^{-κ d}` per term, decay, data size `p^2`; no `δ -> 0` |
| fixed-boundary-data reading vs frozen region | **no frozen region**: data are small field, in the support, held for one step on a finite collar; `K`'s content stays in `w(c)` and cancels |
| volume uniformity | **holds** (local to `W`; `N` depends on `log |Λ''|` only) |
| NITs | Dirichlet layers as unions of `L`-blocks; name `E_0(M)` in the collar constant (logarithmic); state that the `χ`-expansion uses `q0 >= p0` |
| **N-2** | **GAP (reduced):** write-outs 1, 2 done; owes the front advance, H1's polymer coupling, and the write-up of (c) |

## Thirteenth follow-up

Read for this: `../m1-tools/UV-TV.md` 30, 31 and 32, with 26-27 (route (c), written) as background. REVIEW-3 was not
read. Nothing was built.

### Verdict (thirteenth follow-up)

* **N-2 is closed at paper level,** in the sense that every step now has a written argument. It rests on route (c) and
  the named citation-level readings, and has four FIXABLE items, none of which needs a new idea. I withdraw the GAP
  rating for N-2.
* **The front recursion (30) is right.**
  * The inherited disagreement enters as a source **set**. Only its distance to the target matters, not its size,
    because the source weights decay exponentially and the sum over a source of any size beyond distance `Δ` is
    `<~ e^{-λΔ}` times a polynomial.
  * So the disagreement advances by `a_j` per scale, and `Δ_j >= L^{ℓ-j} Δ_ℓ/2` follows from the geometric bracket.
* **The van den Berg-Maes coupling (31.5) is legitimate in the form used.**
  * It needs only two things: the deterministic fact that a cell vacant in both copies agrees, and per-copy
    **unconditional** Peierls bounds, combined by the min-trick. It needs no uniform conditional bound, so it is
    unaffected by forced continuation, and it holds for non-finite-range interactions once those are made objects.
  * But "Markov extended along occupied links" is an adaptation of their finite-range setting: the revealing procedure
    must follow links. Write it.
* **The global constant `Π_X e^{-M_X}` is harmless.** It is deterministic, independent of `ω` and of the copy, and
  cancels in every normalised law and ratio, provided `M_X` is a fixed bound, as stated.
* **One point to fix in 31 (FIXABLE):** the units of `d(X)`. The link weights and the vacuum-link density carry `p^2`
  (`C (p^2 + C_0) e^{-κ d}`). They are small as `g -> 0` only if `d` is counted in `M`-cubes (Balaban's unit for `κ`),
  or the separation of polymers in sites, so that `D_c` cell-separations give `e^{-κ D_c R_j}`. With `d` in
  `M R_j`-cubes and fixed `κ`, "density `C (p^2 + C_0) e^{-κ D_c}`, tiny" is false at fine scales, where `p -> ∞`.
* **Other FIXABLE items:**
  * the last kernel, from the scale-0 state `(Ad U, τ'_0)` to the bare SU(2) field, should be part of the tower;
  * my three twelfth-follow-up NITs are not yet folded in.
* No FATAL finding.

### 1. The front recursion (30)

* **The one-scale claim** `D_j ⊂ N_{a_j}(src_j)`, except on `E_j`, follows from Theorem 28.
  * With weights centred at `x`, `d(x) <= C_s Σ_{y ∈ src} e^{-λ dist_ω(x, y)}`.
  * The union over `x` with `dist_ω(x, src) > a` gives `|Λ''_j| e^{-λ a/2}`.
  * The passage from `dist_ω` to `dist` uses the half-path event, priced per cube by H2/H2a and the min-trick.
  * Truncations are a case split.
  
  Correct. `C_s` is polylog through the coverage. Fine.
* **Is the inherited disagreement only a source of size `a_j`?** It is a source set, the boxes under all of `D_{j+1}`,
  of arbitrary size. Its effect at `x` is the weighted sum over it. Since `dist(x, src¹) >= L Δ_{j+1} - C L ell_B` and
  the weights decay, only the distance enters, so the front moves by `a_j`, not by anything depending on `|D_{j+1}|`.
  * The other channels by which coarse disagreement acts (the background's non-local dependence) were moved into links
    (positive split, 10.1). Links are objects of the pattern gas, so they are covered by `src²` and its `a^{pat}_j`.
  * Correct.
* **Recursion and bracket.** `Δ_j >= min(L Δ_{j+1} - C ell_B L, ρ_j) - a_j`, with `ρ_j = L^{ℓ-j} Δ_ℓ`.
  * `a_{ℓ-k}` is polynomial in `k` and `log(t/ℓ)`, because `R_{ℓ-k} = (log g_{ℓ-k}^{-2})^r` with
    `g^{-2}` growing linearly in `k`.
  * So `Σ_k L^{-k} a_{ℓ-k} <= A_ℓ`, polylog in `1/ℓ`, and the condition `c t/ℓ >= 2(A_ℓ + C ell_B L)` holds for
    `ℓ <= ℓ_0(t)`.
  * Correct.
* **Result.** `P(differ on B) <= Σ_j P(E_j) <= C (t/ℓ)^{-d C_2}`. This is geometric in `k`, so any `C_2 > 0` works,
  uniformly in the spacing and the volume. Correct. The conditional-to-unconditional passage (each `P(E_j | coarser)`
  averaged) is fine, since every copy is law-distributed.
* **(B).** "Fresh randomness on the mirror side" is the in-support construction I asked for in the eleventh follow-up,
  provided it is done as follows. Take two towers `Y`, `Y°`, conditionally independent given `𝓕_ℓ`, and the tower `Z`
  that uses `Y`'s randomness on the `A` side and `Y°`'s on the `θA` side. Then `Z` is a genuine sample, and the front
  argument gives `Z = Y` near `A` and `Z = Y°` near `θA`. Say so explicitly in 30.1.
* **FIXABLE: the last kernel.**
  * The tower ends at the scale-0 **state** `(V_0, τ'_0) = (Ad U, σ*)`, plus noise. The fine observable `F` is a
    function of the bare SU(2) field.
  * Given `(Ad U, σ*)`, the bare signs `τ = c + σ*` are determined up to the decoder's ties inside flip-cube
    components (local), and `U` up to Z2 gauge (irrelevant for gauge-invariant `F`).
  * So the last kernel is local and nearly deterministic. It should be added as step `j = -1` of the tower, with its
    (trivial) front advance of one flip-cube component.

### 2. H1 at the polymer level (31)

* **The positive split and the constant.** `e^{I_X} = e^{-M_X}(1 + h_X)`, `0 <= h_X <= e^{2M_X} - 1`, needs
  `|I_X| <= M_X` for all `ω`, with `M_X` independent of `ω` and of the copy. Both hold, since `M_X` is the deterministic
  bound `C (p^2 + C_0) e^{-κ d(X)}` and `I_X` is real for real fields.
  * Then `Π_X e^{-M_X}` is a finite constant in a finite volume. It cancels in the normalised pattern law, in the
    Peierls ratios and in the coupling. **Harmless.**
  * Vacuum links (`I_X = 0`, `h_X = e^{M_X} - 1`) are a positive, ω-independent sprinkling. Fine, given their density
    is small (see the units point below).
* **Units of `d(X)` (FIXABLE, needed).**
  * 31.1 says `d(X) >= D_c` for `X` meeting two polymers, and 31.2 calls the vacuum-link density
    `C (p^2 + C_0) e^{-κ D_c}` "tiny". With `D_c = 100` and `κ` fixed, that is not small uniformly in `g`: `p = p(g_j)`
    grows like a power of `log g_j^{-2}` at fine scales.
  * **The resolution is in Balaban's units.** His `κ` multiplies linear size in `M`-cubes ([I] p. 257; [V] (1.97),
    `EK-DERIVATION.md` Q2). Polymers that are `D_c` cells (`M R_j`-cubes) apart are `D_c R_j` `M`-cubes apart. So
    `M_X <= C (p^2 + C_0) e^{-κ D_c R_j}`, which is small because `R_j >= (log g_j^{-2})^2 >> log p`.
  * The classical part of `I_X` decays per site (rate `m`) across `D_c M R_j` sites, so it is even smaller.
  * State `d(X)` in `M`-cubes (or sites) in 31.1-31.3 and in the link sums. Otherwise the Peierls (31.3) and
    Kotecky-Preiss (31.4) conditions, which include links, are not uniform as `g -> 0`.
* **Peierls per copy (31.3).** For a positive product-form gas, `P(objects present) <= Π weights` times a ratio of
  partition functions `<= 1`, times `sup Π (1 + h)` over the links touching them. Correct, given the units fix.
* **Kotecky-Preiss (31.4).** Standard for polymers with hard core `D_c` and Mayer bonds `e^{I_X} - 1` (decorated
  polymers). It gives the pattern-index covariance of (B). Correct.
* **Van den Berg-Maes (31.5): legitimate, with one adaptation.**
  * **What the bound uses:**
    * a coupling in which every disagreeing cell is occupied in at least one copy. This is deterministic: two vacant
      cells agree;
    * the disagreement set is connected to `S` through occupied cells or links;
    * per-copy **marginal** Peierls bounds (31.3), combined by the min-trick
      `P(A_1 occ in copy 1, A_2 occ in copy 2) <= min(P_1(A_1), P_2(A_2))`. This is valid for any coupling.
  * **What it does not use:** a uniform bound on conditional occupation probabilities given revealed neighbours. So
    the forced-continuation problem of the earlier box-variable Dobrushin version does not arise. The conditioning in
    the revealing procedure is on discrete pattern data, not on fine fields, so no frozen region arises either.
  * **The adaptation.** Van den Berg-Maes prove this for finite-range Markov fields. Here the interaction has
    unbounded range, through links. 31.2 makes links objects that occupy the cubes of their domain, and asserts that
    the field of cell states is Markov "extended along occupied links".
    * For the identical-coupling step ("an unrevealed region surrounded by agreeing revealed cells has the same
      conditional law"), the revealed set must include, for every link crossing into the region, everything that
      link's weight `h_X(ω)` depends on, namely the polymers it meets along its whole domain.
    * So the procedure must reveal along occupied links. A disagreement can then jump along a link, which the path
      bound already counts ("joined by a link").
    * This is an adaptation, not a quote of their theorem: one paragraph to write.
* **Coarse-bad cells (31.6).** Counted as always occupied in the coupling, with their rarity from the annealed H2a and
  `T_{j+1}`. Conditionally on the coarse data they cost nothing, and they are paid when averaging, inside 30.2's
  `E^{path}_j`. Consistent with the quenched/annealed bookkeeping of the eighth follow-up.

### 3. Is N-2 closed at paper level?

**Yes.** The chain is:
* OS density (13.4, 8);
* Lemma UV-TV via the reverse-kernel tower;
* per scale:
  * the coupling-form Dobrushin-Shlosman theorem (28);
  * H3 and Lemma C with constant-size inputs (29);
  * composite boxes with fixed collars and truncations (21-24);
  * H2/H2a via route (c) (26-27);
  * H1 via the polymer gas (31);
* chaining by the front argument (30).

Every link is now written at paper level. What remains:
* **Citation-level readings** (named in 32):
  * (a), what `E_k(Z)` is;
  * admissibility, from a poor scan;
  * Balaban's machinery on a domain with Dirichlet data;
  * "`κ` large for given `L`" ([I] Theorem 3).
* **Route (c):** a re-proof, checked three ways. It is the single point of failure of the rarity bounds.
* **FIXABLE items** (this follow-up and the twelfth):
  1. units of `d(X)` in 31, so that the link terms are small uniformly in `g`;
  2. van den Berg-Maes adapted to links (reveal along occupied links);
  3. the last kernel `(Ad U, σ*) -> U` as step `-1` of the tower, and (B)'s hybrid stated explicitly;
  4. the twelfth-follow-up NITs (Dirichlet layers as unions of `L`-blocks; `E_0(M)` in the collar constant; the
     `χ`-expansion uses `q0 >= p0`).

**On 32's wording:** "complete at paper level, resting on (c), the citation-level readings and the standard tools" is
accurate once the four FIXABLE items are folded in. I would add "pending items 1-4" until then.

### Status (thirteenth follow-up)

| item | status |
|---|---|
| front recursion (30) | **correct**; the inherited disagreement acts by distance, not size; result `C (t/ℓ)^{-d C_2}`, uniform |
| (B) via fresh mirror randomness | fine as the conditionally-independent-towers hybrid; state it explicitly |
| last kernel to the bare field | **FIXABLE**: add `(Ad U, σ*) -> U` (local, ties only) as step `-1` |
| positive split, `Π e^{-M_X}` | **harmless** (deterministic, `ω`- and copy-independent, cancels) |
| units of `d(X)` in 31 | **FIXABLE, needed**: count in `M`-cubes or sites, so `e^{-κ D_c R_j}` beats `p^2`; as written, the vacuum-link density is not small at fine scales |
| Kotecky-Preiss (31.4) | correct (standard) |
| van den Berg-Maes (31.5) | **legitimate in the form used** (deterministic vacant-agree plus marginal Peierls plus min-trick); adaptation to links to write (reveal along occupied links) |
| twelfth-follow-up NITs | not yet folded in |
| **N-2** | **closed at paper level** (GAP withdrawn), resting on route (c) and the named citation-level readings, pending FIXABLE items 1-4 |
