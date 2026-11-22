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
