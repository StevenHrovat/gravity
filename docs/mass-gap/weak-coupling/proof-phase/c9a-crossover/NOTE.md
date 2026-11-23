# c9a-crossover: the crossover P4, from the hand-over scale L_* to the strong-coupling scale L_1 (cycle 9, workstream a, 2026-11-23)

Task: state P4 precisely in the current setting (input = what M1 hands over at `L_*`, output = what the assembly needs at
`L_1`); look for a reduction of P4 to a fixed, finite system and name its weakest link; say whether a computer-assisted
certification is conceivable and over what; place it in the literature; check the two-layer picture (centre layer, adjoint
layer); recommend the next step.

Lean: `formal/ProofPhase/Crossover/Openness.lean` (new, 5 declarations), built in a throw-away copy (`build.sh`, "Build
completed successfully", no warnings), axioms checked (`axioms.sh` -> `axioms.log`: each depends only on `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`, no new axiom). The build folder was deleted afterwards.

Claim marks: **Lean** (built and axiom-checked), **paper** (argued here, complete at the level stated), **sketch** (argued, gaps
named), **citation** (a source used as stated; "read" = checked in this repo, with the note named; "recalled" = from memory, not
re-checked), **numerical** (computed here; one-loop estimates are labelled as such), **open**.

---

## 0. Results in plain words

1. **P4 can be stated as one lattice theorem at `L_*`** (section 1). Input: the law of M1's block state `(V, tau)` (SO(3) field,
   closed Z2 layer) on the `L_*` lattice, in Balaban's inductive form at coupling `g_K <= gamma`, with bounds that do not depend
   on the lattice spacing. Output: the one-box criterion (worst case over every outside, Dobrushin-Shlosman form) for that law,
   with a box of side `ell` in `L_*` units, where `ell` must be a few correlation lengths, i.e. of order `N_* = L_1/L_*`. Through
   existing Lean (`lawGapBddW_of_oneBoxLaw`, v4 assembly) this gives the gap, given the owed interface change and M1's ultraviolet
   transfer. The precise statement is `P4_*` in section 1.3.
2. **The difficulty does not shrink because the number of steps is finite.** The number of steps is fixed, but at one loop it is
   about `15.5/gamma^2 - 6` doublings: 10 doublings at `beta_* = 4/gamma^2 = 4`, 33 at `beta_* = 10`, 150 at `beta_* = 40`.
   An `L_1` cell then contains `N_*^4` sites of the `L_*` lattice: `3e11`, `3e39`, `6e179` (numerical, one loop). Balaban's and
   M1's smallness condition `gamma <= gamma_0(L)` is not explicit and is presumably far from `beta_* = 4`. Section 2.1.
3. **The gap is invisible at `L_*`** (paper). In `L_*` units the mass is about `1/N_* ~ exp(-1/(2 b_0 gamma^2))`. Every Taylor
   coefficient of this at `gamma = 0` vanishes, so no expansion at the hand-over scale contains it. The whole gap is produced
   inside the crossover. This is dimensional transmutation, and it matches the owner's reading that full acts exist only at the
   confinement scale. In the mathematics, M1's hand-over point and the confinement scale are separated by the factor `N_*`: that
   separation *is* P4.
4. **What P4 is, honestly** (paper, reading). `P4_*` is a mass-gap problem for a 4D SU(2) lattice gauge theory at one fixed weak
   coupling `gamma`, with an action in Balaban's neighbourhood of the Wilson action, in the worst-case-boundary form. M1 and
   Balaban have removed the continuum limit. What is left is the **weak-coupling lattice mass gap at a fixed coupling**. No
   method in the literature proves a gap for a 4D non-abelian lattice gauge theory with a continuous group at any coupling outside
   the strong-coupling window (c7d, confirmed here). A method that proved `P4_*` would almost certainly prove the gap of the Wilson
   action at `beta = 4/gamma^2`. So P4 is the classical open lattice problem, in a well-posed finite-scale form.
5. **The reduction to a finite system, and its weakest link** (section 2). Openness of the one-box criterion is now **Lean**
   (`isInfluenceBoundOn_of_near`, `oneBoxSum_of_near`, `influence_of_net`). It says that a class of laws satisfies the criterion if
   a finite net of the class does, with every member worst-case close to a net point. It also names the precision needed:
   closeness `delta` costs `2 delta |shell|/|box|`, so `delta` must stay below about `(1 - gamma) ell/16` differing sites per box
   law. That makes a "finite system" reduction logically trivial. **All content sits in one link, in every formulation tried:**
   - quasi-locality (continuity in the worst-case-boundary topology) of the map from the `L_*` law to the `L_1` box laws; or
   - equivalently, **a conditional mass across the crossover**: the field below a scale, conditioned on the block field at that
     scale *and on an arbitrary outside*, decorrelates at the block scale, uniformly over block fields, at every scale from
     `L_*` to `L_1`.

   This is the quenched `CondMass` of cycle 4, now as **the** crossover link. At the weak end Balaban's fluctuation bounds should
   give it; at the strong end the single-link Dobrushin condition gives it; in between it is **open**.
6. **The input class is not compact at the resolution the output needs** (sketch). The small-field part is precompact modulo
   tails (analytic, localised E-terms: Montel plus exponential decay). The large-field part is not. M1 makes Balaban's large-field
   weights into probabilities, `<= e^{-p_0(gamma)}` per `L_*`-block. But `p_0` grows only polylogarithmically in `1/gamma`, while an
   `L_1` cell holds `N_*^4 ~ exp(2/(b_0 gamma^2))` blocks. **At `L_1` resolution the hand-over law is a dense gas of large-field
   regions, not "small field plus rare defects."** Whatever carries the crossover must carry Balaban's large-field machinery with
   it, at couplings where that machinery has no small parameter. This is the owner's "large difference of scales" reading, read
   backwards: it holds towards the fine end and fails across the crossover.
7. **Computer-assisted certification** (section 3). The direct one-box check at `L_1` on the `L_*` lattice is not conceivable
   (`>= 1e11` sites per cell even at `beta_* = 4`). What is conceivable is an **RG-step certification** of the last few doublings
   (Wilson-equivalent `beta` from about 3.5 down to 2.3, roughly 4 to 6 doublings). It would work on a finite-dimensional family
   of effective actions (roughly 5 to 20 character couplings) plus a tail norm, with one rigorous enclosure per step and a
   certified landing window (c3c/c4d), and the Openness lemma would convert the enclosures into the criterion. It is conditional
   on two things: the conditional mass per step (item 5), and an explicit-constant bridge from `gamma_0` up to `beta ~ 3.5`. The
   bridge is perturbative in the physicist's sense but not covered by Balaban with explicit constants. A cautionary precedent: the
   Migdal-Kadanoff recursion carries the crossover in finitely many finite-dimensional steps, and it flows to strong coupling for
   U(1) too (Ito 1985, read in c6c). **A finite-dimensional flow that fails the photon test proves nothing.** The truncation must
   keep what MK loses, and the tail norm is where the photon would hide.
8. **The two-layer picture splits the output, not the crossover** (section 4). At `L_1` the split criterion
   `gamma_Z + gamma_A < 1` is Lean (c8a).
   - The **centre half** needs `H_sat(l)`: quenched block-plaquette flux free energy `Jbar_P(l) < 0.0556`. At `L_*` the same
     quantity is about `(pi^2/2) beta_* >= 20` nats. Bringing it down by two or more orders of magnitude across the crossover is
     the running of the vortex free energy: Tomboulis' programme, whose comparison step is the known gap (Ito-Seiler). c7b and c8a
     **consume** `H_sat` at `L_1`; they do not **produce** it from `L_*`.
   - The **adjoint half** `gamma_A` is the gap of the SO(3) layer with the centre configuration frozen. It carries the whole
     passage from near-massless gluons to a mass, and the photon test lives in it.
   - The halves are coupled across the crossover. The centre couplings `J_P(V)` are functions of the adjoint field, and their
     running is an adjoint-fluctuation effect (asymptotic freedom is centre-blind). Worse, a quenched adjoint layer has its own
     known hazard: the SO(3) and mixed fundamental-adjoint actions have a first-order bulk transition at intermediate coupling
     (Bhanot-Creutz 1981; Greensite-Lautrup 1981; recalled). A worst case over centre backgrounds could produce ties in `gamma_A`.
9. **Recommended next step** (section 5). Three workstreams and one decision.
   - (W1) Paper plus small Lean: state `P4_*` and prove the chain `P4_* => assembly`, with the interface as a named input.
     Provable now.
   - (W2) The weakest link first, numerically: a pre-registered measurement of the quenched constrained Dobrushin coefficient
     across `beta` 2.3 to 3.5, on sampled and adversarial block fields, with the photon (U(1)) and 2I controls. GPU, about
     10 to 20 h. If it fails at some scale for adversarial fields, the iterated route with that blocking is dead.
   - (W3) Computation: a certified landing window with a tail budget (the Openness lemma tells it what `delta` it may spend).
     CPU, days.
   - Decision for the owner: whether to invest in an explicit estimate of `gamma_0(L)`. It decides whether the perturbative
     middle of the crossover is 10 or 150 doublings, i.e. whether any computer route is realistic at all.

---

## 1. P4, stated precisely

### 1.1 Input: what M1 hands over at `L_*` (paper, M1; read: `m1-tools/HANDOVER.md`, `M1-PLAN.md` 0, `UV-TV.md` 37)

At the stopping scale `K` (first scale with `g_K` above a threshold `gamma' < gamma`, so `g_K in [gamma', gamma]`, a compact
interval; `L_* = L^K a` is two-sided comparable to a fixed physical length along the line of constant physics, through
[I] Theorem 2, external), M1 delivers, uniformly in the lattice spacing `a` and the volume:

* **(a) The law** of the block state `(V_K, tau_K)`: an SO(3) block field and a closed Z2 layer (2-cochains with closed sheets
  only, after the local decoder and mod-2 Stokes) on the coarse torus of side `M` in `L_*` units. The law has Balaban's inductive
  form ([III] (2.18), [V] (1.104)):
  - a sum over large-field histories of products of characteristic functions;
  - a small-field effective action `g_K^{-2} A(U_K(V)) + E_K + R_K + B_K`, with analytic, localised E-terms
    (`|E(X)| <= C e^{-kappa d(X)}`);
  - R-terms `<= e^{-p_0(g_K)} e^{-kappa d(X)}`;
  - label factors for long-lived remainders.

  The constants `(kappa, p_0, M, C)` do not depend on `a`. **Because the densities are laws** (law preservation, Lean,
  `Exact.lean`, `m1_laws`), Balaban's large-field factors are probability bounds: a large-field region costs `<= e^{-p_0}` per
  `L_*`-block, up to entropy.
* **(b) The `L^1` transfer** of block observables (R10, paper on citations) and OS-norm density of block observables (Lemma UV-TV,
  paper).
* **Not delivered:**
  - any decay at `L_*` (the law there is weakly coupled; one-box influences are of order one, `HANDOVER.md` 2);
  - any worst-case-boundary statement. M1's bounds are for the torus density. M1's shell adaptation (`UV-TV.md` 34.8: Dirichlet
    data on both sides, constants uniform in the shape) is the closest thing, for regular data only.

### 1.2 Output: what the assembly consumes (Lean, read in `formal/ProofPhase/`)

Three admissible forms, all Lean consumers:

| form | statement | consumer | what else it needs |
|---|---|---|---|
| (O-fine) | `WilsonOneBox T`: the bare Wilson measure, regrouped into cells of physical size `L_1`, one box `Lambda_0` of `<= n_max` cells; influences of one outside cell on gauge-invariant functions of the box with frozen boundary, **worst case over all fine outsides**; `sum_u kappa(u) e^{lambda E(u)} <= gamma_box |Lambda_0|`, `gamma_box < 1`; uniformly in level `k >= k_0` and volume | `yang_mills_assembly_wilsonOneBox` (`OneBox2/Concrete.lean`) | `OnLCP'`, `NonTrivial`; no blocking, no ultraviolet transfer |
| (O-split) | `FineOneBoxSplit T`: the same with hybrid laws and budgets `gamma_Z + gamma_A < 1` | `yang_mills_assembly_split` (`Saturation/Reduction.lean`) | as (O-fine) |
| (O-block) | `OneBoxLaw rho lambda` for the `L_*` laws `rho k j`: one box of `L_*`-sites, worst case over all `L_*` outsides | `lawGapBddW_of_oneBoxLaw` then `BlockGapBddW` then `yang_mills_assembly_v4_bdd` (or `_meas`, `_rand`) | `ObsTransferPhysTW` (M1's `L_*` half, R10, paper) and the interface change R11 (block state `(SO(3), closed Z2)` instead of an SU(2) `RPBlocking`; owed, outside M1) |

Two remarks on the output.
* **The box must be large.** The one-box sum compares a surface of about `8 ell^3` positions with a volume `ell^4`. Influence
  spreads with near-massless (power-law) propagation up to the correlation length `xi` and decays only beyond it. So the criterion
  can hold only with `ell >= C xi` in the units of the sites (paper, c7c 1.3; the power-law failure mechanism is Lean in c7c). For
  (O-block) the box side in `L_*` units is therefore of order `N_* = L_1/L_*` or more. That is allowed (`n_max` is any fixed
  number), but the box is astronomically large (section 2.1).
* **(O-fine) versus (O-block).** (O-fine) states nothing about any blocking, so a proof may use any auxiliary (noisy, randomised)
  blocking internally without the noise-limit trap of cycle 3. Its cost: the ultraviolet segment must then be redone in a box with
  an arbitrary fine outside. (O-block) uses M1's hand-over as is, but needs the interface change and M1's transfer. Section 5
  recommends (O-block) as the statement and (O-fine) as the later strengthening.

### 1.3 The statement `P4_*`

**`P4_*(L, gamma, c)` (open).** Let `C = C(gamma, c)` be the class of probability laws `rho` of block states `(V, tau)` on coarse
tori `(Z/M)^4` (every `M`), of M1's inductive form at final coupling `g in [gamma', gamma]` with constants `c`. There exist a box
side `ell`, a rate `lambda > 0` and `gamma_box < 1`, depending only on `(L, gamma, c)`, such that every `rho in C` satisfies the
gauge-restricted one-box criterion:
* box: the cube of side `ell`;
* influences: from one outside `L_*`-link on gauge-invariant functions of the box with frozen boundary, worst case over **all**
  outsides in the state space;
* the sum `sum_u kappa(u) e^{lambda E(u)} <= gamma_box ell^4`.

`P4_*` implies (O-block) uniformly in the lattice spacing, because every actual `L_*` law lies in `C` for `a <= a_0(gamma)`, and
uniformity in the volume is part of the statement. With the existing Lean chain and the two owed items (interface R11, M1's R10
transfer) it gives the assembly conclusion (paper: the chain is composition of Lean theorems plus the named items; W1 in section 5
formalises it).

### 1.4 The gap between input and output, exactly

| # | input (M1 at `L_*`) | output (`P4_*`) | status of the gap |
|---|---|---|---|
| G1 scale | law at `L_*`, coupling `gamma` | box of side `~ N_* = L_1/L_*` (in `L_*` units), coupling of order one at its scale | fixed but huge, section 2.1 (numerical, one loop) |
| G2 kind | a representation with mostly upper bounds, **annealed** (torus density) | **quenched**: worst case over every outside, including large fields on the box boundary | open; M1's shell adaptation covers regular data only |
| G3 content | analytic in the coupling, perturbative structure | a mass `~ exp(-1/(2 b_0 gamma^2))` in `L_*` units | **the whole gap**, section 2.2 (paper) |
| G4 class | `a`-independent bounds, large fields `<= e^{-p_0(gamma)}` per block | a statement at `L_1` resolution, where those large fields are dense | sketch, section 2.3 |
| G5 state | `(SO(3), closed Z2)` | SU(2) `BlockingFamily` (`RPBlocking`) in the assembly | owed formal refactor (R11), not mathematics |
| G6 group | Balaban's machinery is group-specific through asymptotic freedom | must fail for U(1) (photon), 2I, SU(2)xU(1) | every reduction must pass the unit tests (section 3.3) |

---

## 2. The search for a finite-system reduction

### 2.1 The size of the "fixed number of steps" (numerical, one loop)

One-loop running for SU(2) gives `b_0 = 22/(48 pi^2) = 0.0464` and Wilson `beta = 4/g^2`. Per factor-2 blocking towards the
infrared, `Delta beta = 8 b_0 ln 2 = 0.2575`. Anchor `L_1` at the c3b point: `L sqrt(sigma) = 2.8`, about 7.5 lattice spacings at
`beta = 2.3`. Then `N_* = L_1/L_* ~ 7.5 exp(2.69 (beta_* - 2.3))`:

| `beta_* = 4/gamma^2` | `gamma^2` | `N_*` | doublings | `L_*`-sites per `L_1` cell (`N_*^4`) |
|---|---|---|---|---|
| 3 | 1.33 | 49 | 5.6 | 6e6 |
| 4 | 1.00 | 730 | 9.5 | 3e11 |
| 6 | 0.67 | 1.6e5 | 17.3 | 6e20 |
| 10 | 0.40 | 7.5e9 | 32.8 | 3e39 |
| 40 | 0.10 | 8.8e44 | 149 | 6e179 |

One loop is only an order-of-magnitude guide (asymptotic scaling is violated by tens of percent below `beta ~ 2.5`). Balaban's
`gamma_0(L)` is not explicit. Nobody, including M1, has an estimate. Given how his constants are chosen (`kappa` large, then `M`,
then `gamma` small, [I] Theorem 3, cited in M1), `beta_* = 10` would already be optimistic. **"Fixed number of steps" means
dozens to hundreds of doublings, of which only the last handful are non-perturbative.**

### 2.2 Why the input cannot contain the answer (paper)

Along the line of constant physics the mass in `L_*` units is `m L_* = c_m / N_*(gamma) ~ c exp(-1/(2 b_0 gamma^2))`. This
function of `gamma` is `C^infty` at `gamma = 0` with all derivatives zero. So a statement about the `L_*` law whose constants are
analytic (or merely asymptotic-series) functions of `gamma` near 0 can never contain the gap. Concretely, no finite order of
Balaban's expansion at `L_*` distinguishes SU(2) from a hypothetical gapless theory with the same perturbative coefficients. The
gap has to be built in the crossover, over the `N(gamma)` steps, by a mechanism without a small parameter. This is the
mathematical form of the owner's readings:
* "The quantum of assertion fixes the thickness": the only scale is `Lambda`, the full act sits at `1/Lambda`, and M1 stops
  `N_*` short of it.
* "The strength comes from a large difference of scales": that difference holds towards the fine end and fails exactly across
  the crossover (`PREP.md`, coordinator's reading of the second item says the same).

### 2.3 Is the input class compact up to small local errors? (sketch)

* **Small-field part: yes, up to tails.**
  - The dominant term `g^{-2} A(U_K(V))` is a one-parameter family over the compact interval `g in [gamma', gamma]`.
  - The E-terms are analytic in the fields on a fixed complex neighbourhood, with bounds uniform in `a`. By Montel, for each
    localisation domain `X` the set of possible `E(X)` is relatively compact in the sup norm on real configurations. With the
    decay `e^{-kappa d(X)}`, the whole small-field effective action ranges over a compact set in the weighted norm with any
    `kappa' < kappa` (diagonal argument).
  - So **finite `epsilon`-nets exist**. Their size grows like `exp(n(R) log(1/epsilon))`, where `n(R)` is the number of
    independent local couplings up to diameter `R ~ kappa^{-1} log(1/epsilon)`: finite, astronomically large.
* **Large-field part: no, not at `L_1` resolution.** A large-field region costs `<= e^{-p_0(gamma)}` per `L_*`-block (a law-level
  bound, thanks to M1). Balaban's `p_0(g)` grows polylogarithmically in `1/g` (recalled form). An `L_1` cell holds `N_*^4`
  `L_*`-blocks, and `N_*^4 ~ exp(2/(b_0 gamma^2))` grows faster than any power of `1/gamma`. So the expected number of
  large-field regions per `L_1` cell, `N_*^4 e^{-p_0(gamma)}`, is enormous for small `gamma`. These are ordinary fluctuations above
  Balaban's threshold `g p(g)`, not instantons (the instanton count of size `L_*` per `L_1` cell is small, `~ (L_* Lambda)^{22/3 - 4}`,
  recalled one-loop density). In the worst-case (sup) norm the one-box criterion uses, they cannot be netted. Inside the box only
  their probabilities matter, which are annealed. On the box boundary the worst case puts them wherever it likes.
* **Consequence.** The class is "compact up to small local errors" per `L_*`-block, not per `L_1` cell. A finite-system reduction
  at `L_1` must therefore carry Balaban's large-field gas through the crossover, where its suppression `e^{-p_0}` is not small.
  This is P3.5's remark ("large fields and crossover are one obstruction there") made quantitative.

### 2.4 The reduction, in its cleanest form, and its weakest link

**Openness (Lean, `ProofPhase/Crossover/Openness.lean`).**
* `IsNearSpec B q q' delta`: for every boundary condition and every bounded test function of the box with per-site oscillation
  `<= L`, the two box laws differ by `<= delta L`. This is a worst-case Wasserstein distance in the "number of differing sites"
  metric.
* `isInfluenceBoundOn_of_near`: influence `k` for `q` gives `k + 2 delta` for `q'`, on any admissible (gauge-restricted) class.
* `influence_of_net`: a class within `delta` of a net whose influences are bounded by `kappa_bar` has influences
  `kappa_bar + 2 delta`.
* `oneBoxSum_of_near`: a perturbation that adds `<= 2 delta` on a shell `sh` keeps the one-box sum with
  `gamma + 2 delta S/|Lambda_0|`, where `S` is the weighted shell size.
* `near_budget_lt_one`: the margin survives iff `2 delta S < (1 - gamma)|Lambda_0|`.

For a cube of side `ell` with a one-cell shell (`S ~ 8 ell^3`, `lambda = 0`) this is `delta < (1 - gamma) ell / 16` differing sites
in total per box law.

**The compactness reduction (paper, given Openness).** Suppose:
* (i) the input class `C` is compact in some topology `tau`;
* (ii) the map `Phi` from an `L_*` law to its family of box specifications at the output scale is continuous from `tau` into the
  `IsNearSpec` (worst-case) topology.

Then `P4_*` on `C` follows from the criterion with margin on a finite net. Here (i) holds up to the large-field caveat of 2.3, and
(iii), openness of the criterion, is the Lean above. **But (ii) is the whole problem.** Continuity of `Phi` in the worst-case
topology says that changing the `L_*` input far from a box, or by a small amount in a tail, changes the conditional law of the box
given any outside only a little. That is quasi-locality of the crossover map with worst-case boundary, i.e. a decay statement at
every intermediate scale.

**The iterated form (paper, standard pattern).** Write the crossover as steps `s = 1, ..., N` of a noisy, measurable blocking
(`Interface/RandBlocking.lean` allows noise). Suppose each step satisfies:

> **`CU_s` (constrained uniqueness, quenched):** the field below scale `s`, conditioned on the block field at scale `s` and on an
> arbitrary outside, satisfies a Dobrushin(-Shlosman) condition with constant `c_s < 1`, uniformly over block fields and outsides.

Then:
* the step's output is quasi-local, with an explicit exponential tail;
* the output on a box is determined to precision `epsilon` by a finite collar of width `~ log(1/epsilon)/|log c_s|`;
* the step admits a finite-dimensional enclosure with a tail norm (pattern: renormalised measures are Gibbsian when the constrained
  system is in a uniqueness regime; van Enter-Fernandez-Sokal 1993, Haller-Kennedy 1996, recalled; the Haller-Kennedy result as
  described by citing papers is that a single RG step maps a region including the critical point to a well-behaved one, given a
  constrained-uniqueness condition).

Errors then add over `N` steps, and Openness turns the final enclosure into the criterion. `CU_s` for all `s` is `CondMass`
(c4a), in its quenched form, at every crossover scale. The Rebeschini-van Handel caveat (c4c: exact observations of composites
can destabilise the conditional system) is why the blocking must be noisy.

**The weakest link, named.** In all three formulations (direct box check, compactness, iteration) the irreducible input is the
same:

> **(WL) Quenched conditional mass across the crossover.** For every scale between `L_*` and `L_1`, the field below that scale,
> given the block field at that scale and an arbitrary outside, decorrelates at the block scale, uniformly over block fields
> (including large-field and twisted ones) and outsides, with constants independent of the lattice spacing.

* At the weak end it should follow from Balaban's fluctuation-propagator bounds plus M1's law form (sketch: the constrained
  fluctuation operator has a Poincare gap of order one on `ker Q`, `POINCARE.md`; the work is the arbitrary outside and the
  large-field gas of 2.3).
* At the strong end it follows from the single-link Dobrushin bound (Lean, `OneBox2/Anchor.lean` type estimates).
* In between it is **open**, and it is where the physics happens. It is gap-like (it fails for the photon if the blocking loses
  long-wavelength content: the noise-limit trap) but weaker than the gap (it is a statement at the block scale, given the block
  field). Whether it holds at `beta ~ 2.3` to 3 for a noisy good blocking is unknown. It is measurable (W2).

`(WL)` is not sufficient on its own. With it, each step is a computable local map, but tracking the flow over `N` steps still needs
a closure: the truncated family must stay a good description, with tails controlled by `(WL)`'s decay. At the perturbative end
power counting gives closure. At the non-perturbative end closure is a computation with error bars (section 3). That is the second
link, computational rather than conceptual.

### 2.5 Literature position (citations; levels as marked)

| work | what it does at the crossover | level |
|---|---|---|
| Balaban, CMP 109-122 (1987-89) and [12]-[16] | ultraviolet stability: effective actions controlled while `g_k <= gamma <= gamma_0(L)`; partition functions, not laws; finite volume in units of the last scale; **stops at `L_*`**; [I] Theorem 2 (running) unpublished | read (`c5d-supplier/BALABAN-READING.md`, `m1-tools/EXTERNAL.md`) |
| Magnen-Rivasseau-Seneor, CMP 155 (1993), "Construction of YM4 with an infrared cutoff" | continuum SU(2) Schwinger functions with a **fixed infrared cutoff**, no ultraviolet cutoff, axial gauge at large field; the infrared cutoff is kept, so it also stops before the crossover | citation (abstract-level, checked by search this session; year listed as 1993 or 1994) |
| Federbush, "A phase cell approach to Yang-Mills theory", CMP series 1986-87 | ultraviolet programme; no crossover | recalled |
| Brydges-Dimock-Hurd (e.g. CMP 198 (1998), non-Gaussian fixed point in `4 - epsilon`); Dimock, "The renormalization group according to Balaban" (2013-14, scalar) | RG maps on polymer activities with a finite-dimensional relevant part and an irrelevant remainder in a norm: the prototype of "compact up to small local errors"; all at small coupling | recalled |
| Balaban-Imbrie-Jaffe (abelian Higgs) | infrared controlled at weak coupling because the mass is classical (Higgs); the contrast case: pure Yang-Mills has no classical mass | citation (c7d row 23) |
| Goepfert-Mack, CMP 82 (1982) | the one lattice gauge theory where an RG argument runs to the infrared for all couplings (3D U(1), monopole gas, Debye screening); abelian and 3D | recalled |
| Migdal-Kadanoff; Tomboulis (2007); Ito-Seiler (2007); Ito (1985) | the only "finite-dimensional crossover" in the literature: the MK recursion reaches strong coupling in finitely many steps for **every** group, U(1) included; Tomboulis' attempt to make it a bound fails at one comparison inequality | read (`c6c-floor/NOTE.md` 1.1) |
| Dobrushin-Shlosman (1985, 1987); Martinelli-Olivieri (1994); Stroock-Zegarlinski (1992); Dobrushin-Kolafa-Shlosman (1985) | finite-box (one-box) criteria and their computer-assisted use, spin systems only, boxes of side 3 to 4 | citation (c7d, abstract/secondary) |
| Haller-Kennedy, J. Stat. Phys. 85 (1996) 607; van Enter-Fernandez-Sokal, J. Stat. Phys. 72 (1993) | RG maps well defined (Gibbsian) when the constrained system is in uniqueness; near criticality by an explicit finite condition; the pattern for `CU_s` | citation (Haller-Kennedy: existence and topic confirmed by search; whether its verification is computer-assisted **not confirmed**); van Enter-Fernandez-Sokal recalled |
| Koch-Wittwer (hierarchical models, 1980s) | computer-assisted RG fixed points, rigorous; hierarchical, so one-site maps | recalled |
| Luescher (small-volume expansion, NPB 219 (1983)); Luescher-Weisz-Wolff (step scaling, NPB 359 (1991)) | the physicist's finite-scale formulation of exactly this crossover: a finite-volume coupling `g^2(L)` and its step-scaling function, iterated from weak to strong in a finite number of finite-box steps; numerical, not rigorous; the closest conceptual match to "P4 as a finite-scale problem" | recalled |
| Osterwalder-Seiler (1978); Chatterjee (2021); Shen-Zhu-Zhu (2023); Cao-Nissim-Sheffield (2023) | strong-coupling side: gap or area law for small `beta`, extended windows; Chatterjee: decay under every boundary condition in every cube plus non-trivial centre gives the area law | Chatterjee read (c7d); others recalled |
| Forsstroem (2022), Adhikari-Cao (2025) | weak-coupling decay for **finite** gauge groups (group-specific, no continuous group) | citation (c7d, abstract) |

**Position.** Every rigorous programme for 4D Yang-Mills stops at the scale where the coupling is still small (Balaban,
Magnen-Rivasseau-Seneor, Federbush). Every strong-coupling result starts where `beta` is small. Nothing rigorous crosses. The
finite-scale formulation exists in physics (step scaling) and in a lossy finite-dimensional form (Migdal-Kadanoff), and both
illustrate the danger: the first is numerical, the second fails the photon test. No "finite-scale theorem" for the crossover is
known to me in any non-abelian gauge theory.

---

## 3. Computer-assisted certification: what is conceivable

### 3.1 Not conceivable: the direct check

A certified one-box check at `L_1` on the `L_*` lattice needs, per box, a worst-case Wasserstein bound between two laws on
`3 x 4 x (ell N_*)^4` real variables: at least `1e12` already for `beta_* = 4`. Conditional laws given adversarial outsides of
that size cannot be integrated with interval arithmetic. Not conceivable at any `beta_*` that Balaban covers.

### 3.2 Conceivable, conditional: an RG-step certification of the last few doublings

Shape (sketch):
1. **Parameter space.** Effective actions on the current lattice in a truncated family: characters of the plaquette and the
   `1 x 2` loops in the fundamental and adjoint representations, and a few 3D loops; about 5 to 20 couplings. Add one tail norm
   (a weighted norm of the remainder) and one large-field budget (the probability weight of regions outside the small-field
   threshold).
2. **One step.** Under `CU_s`, the new couplings are expectations in a constrained finite system (block plus collar, one block of
   `2^4` sites and about 64 links, plus collar), computed to `epsilon` with an a-priori collar error. The rigorous enclosure needs
   a convergent expansion of the constrained system, which `CU_s` provides (Dobrushin-type cluster or coupling bounds). Each step
   is a box enclosure of a finite-dimensional map plus a tail bound.
3. **Landing.** After the last step, the certified W1/one-box window: c3c (two-coupling plaquette family) and c4d (the fitted
   action at `L sqrt(sigma) = 2.80`, base column 0.732, knife edge 0.99988 in one extension). The Openness lemma converts the
   enclosure's width and tail into the budget loss `2 delta S/|Lambda_0|`. **c4d's truncation margin (one more centre-charged loop
   family above coupling 0.0013 breaks it) shows the landing window must be widened with a tail budget before it can catch an
   enclosure.**
4. **Range.** Wilson-equivalent `beta` from about 3.5 to 2.3, i.e. 4 to 6 doublings. Above `beta ~ 3.5` the steps should be
   perturbatively controlled, but with explicit constants, which Balaban's `gamma_0(L)` does not supply. That bridge, from
   `gamma_0` up to `beta ~ 3.5` (section 2.1: tens to over a hundred doublings), is a second, very large project.

### 3.3 What a certification must pass

* **Photon.** U(1) has the same kind of step map. A truncated family plus tail norm that cannot tell U(1) from SU(2) would certify
  a gap for the photon. MK does exactly this (Ito 1985). The certification must therefore carry, in the tail norm or the
  enclosure, the information that the U(1) flow keeps a massless mode: long-wavelength influence. In practice `CU_s` must be
  checked against the photon control and must fail there at long wavelengths, or the blocking has lost content (the noise-limit
  trap).
* **2I.** Weak coupling must fail (ties). **SU(2)xU(1):** `gamma_A >= 1`.
* **Mixture:** the landing check is worst-case over outsides, so a two-phase mixture fails it (c7c), correctly.

**Verdict on certification.** Conceivable only as an RG-step certification of the non-perturbative end, conditional on
`(WL) = CU_s` and on an explicit-constant bridge through the perturbative middle. Over a parameter space of roughly 5 to 20
couplings plus two scalar budgets per step, for about 4 to 6 steps. It is research-scale, and nothing like it exists for 4D gauge
theory.

---

## 4. The two-layer picture

**What is Lean.** At `L_1` the criterion splits exactly at a hybrid law, and the budgets add: `gamma_Z + gamma_A < 1` gives
`FineOneBox` and the assembly (`isInfluenceBoundOn_split`, `oneBoxSum_add`, `fineOneBox_of_split`, `yang_mills_assembly_split`).
Ties are exactly large `gamma_Z` (`tie_forces_budget`).

**What each half needs, and at which scale.**

| half | needed at `L_1` (block scale `l L_1`) | value at `L_*` | what the crossover must do | status |
|---|---|---|---|---|
| centre `gamma_Z` | `H_sat(l)`: quenched centre Dobrushin `c_Z(l) < 1`; plaquette form `Jbar_P(l) < 0.0556` (c8a 6.3); then `gamma_Z <= 8 Lambda_fb c/((1 - c) l)` (paper, c8a 5.2) | `Jbar_P(L_*)` about the flux cost of one block plaquette, classically `(pi^2/2) beta_* ~ 4.93 beta_*` (c8a 6.1), so `>= 20` nats for `beta_* >= 4`: sheets are dilute, the layer is effectively deconfined at that scale. M1's closed layer has only closed, costly sheets | lower the quenched vortex free energy per block plaquette by two or more orders of magnitude, uniformly over adjoint backgrounds: the running of the vortex free energy, Tomboulis' programme | **open**; c7b/c8a consume `H_sat`, do not produce it; the annealed results (Tomboulis-Yaffe, chessboard) do not give the quenched form (c8a 4) |
| adjoint `gamma_A` | single-site SO(3) Dobrushin `c_A < 1` at fixed centre configuration, uniformly over centre configurations and outsides; `gamma_A <= 8 c_A/((1 - c_A) l)` | weakly coupled SO(3) field, near-massless; `c_A` near 1 | produce the mass: the whole asymptotic-freedom-to-gap passage, with the photon test living here (SU(2)xU(1): `gamma_A >= 1`) | **open**; the certified annealed fitted numbers (0.0036, about 1e-3) are evidence, not bounds (c8a 5.3) |
| feedback `Lambda_fb` | the number of box cells whose adjoint law moves when one centre variable flips: `O(1)` if the adjoint layer is stateless | not defined at `L_*` in quenched form | stay bounded | open |

**Does the split split P4?** It splits the *output* cleanly. It does **not** split the crossover into an easy and a hard part
(paper):
1. The centre couplings at block scale are functions of the adjoint field (`J_P(V)`, the two-layer reading of
   `z2_background_saturation`). Their running from `~ 5 beta_*` to `< 0.06` is driven by adjoint fluctuations, because the
   beta-function is a property of the Lie algebra and is centre-blind. **The centre half's input is produced by the adjoint
   half.**
2. The adjoint half is the gap of an SO(3) lattice gauge theory with a frozen closed centre layer, at a fixed weak coupling.
   SO(3) has the same Lie algebra and the same `b_0`, so it is as hard as P4 itself.
3. **Hazard (citation, recalled; to be tested).** SO(3) lattice gauge theory and the mixed fundamental-adjoint action have a
   first-order bulk transition at intermediate coupling (Bhanot-Creutz, PRD 24 (1981) 3212, confirmed by search; Greensite-Lautrup
   1981; Halliday-Schwimmer 1981), driven by Z2 monopoles. The Wilson axis itself passes smoothly. A **quenched** adjoint budget
   (worst case over centre configurations) asks the adjoint layer to stay single-phase for every frozen centre background. A
   background that acts like a large adjoint coupling could push it towards that transition and produce ties in `gamma_A`. M1's
   closing rule helps here: monopole loops are large-field regions, and only closed sheets feed `tau`. Whether the closed-layer
   effective adjoint action stays on the smooth side across the crossover is a concrete, measurable question.

**What the two-layer picture does buy.**
* At `L_1` it turns the gap-strength input into two measurable budgets with sharp unit tests (c8a 7).
* The centre budget becomes a statement about essentially one scalar per scale, `Jbar_P(l)`, whose `L_*` value is known and whose
  target value is known. That is a clean observable of the crossover: a **pre-registrable curve** `Jbar_P(l)` from `L_*` to
  `L_1`.
* In the owner's reading ("what crosses the hand-over is quantized assertion"): the closed Z2 layer is the quantised part that
  crosses `L_*`. It arrives dilute (each sheet costs far more than a quantum) and must become saturated by `L_1`. The adjoint
  layer is the stateless carrier that makes that happen. The reading fits the mathematics: the centre half is a consequence of
  the adjoint half's running, not an independent mechanism.

---

## 5. Recommendation: the next cycle

**Provable now (paper plus small Lean).**
* **W1, the statement and the chain** (Lean about 200 to 400 lines, paper about 10 pages).
  - Define `P4Star` as a named hypothesis on a family of laws: the gauge-restricted one-box criterion on the `L_*` lattice
    (`OneBoxLaw` with `ActAdm`, as in `FineOneBox`).
  - Prove `P4Star => LawGapBddW` (reuse `lawGapBddW_of_oneBoxLaw` and the restricted Theorem A).
  - Prove `=> BlockGapBddW => assembly`, with interface R11 and M1's R10 as named inputs.
  - Use the Openness lemmas to state the "net plus closeness" form.

  This makes P4 one named Lean hypothesis at the place where M1 ends, and removes the `L_1`/`L_*` double bookkeeping.
* **c8a's reachable Lean items** (box version of `vortex_saturation`, Z2 layer Dobrushin with background couplings, the
  comparison `kappa_Z <= Lambda_fb c/(1 - c)`): they finish "`H_sat => gamma_Z` small". Useful, but not P4.

**Needs new mathematics.**
* **(WL), quenched conditional mass across the crossover.**
  - Weak end: Balaban's constrained fluctuation bounds with an arbitrary outside and the large-field gas (an adaptation of
    M1's shell work; estimate 30 to 60 pages).
  - Middle: open, no known method.

  This is the core of P4. It is weaker than the gap and stated at the block scale, but it has no small parameter.
* **The explicit-constant bridge** from Balaban's `gamma_0(L)` to `beta ~ 3.5`: a quantitative re-run of the perturbative RG with
  explicit constants. Very large (book-length) and, in principle, mechanical.

**Needs computation.**
* **W2, the weakest link first** (GPU about 10 to 20 h; pre-registration first).
  - Measure the quenched constrained single-link Dobrushin coefficient `c_s`: the fine links of one block given the noisy
    good-blocking block field and the outside, the worst change of their law under one outside or block-variable change.
    Sampled and adversarial block fields (flat, random, twisted, one large-field plaquette); `beta = 2.3, 2.6, 3.0, 3.5`; block
    sizes 2 and 3.
  - Controls: compact U(1) at `beta = 1.1` (must show long-wavelength content survive the blocking, i.e. no fake uniqueness);
    2I at large `beta` (ties).
  - Decision rule: if `c_s >= 1` for some adversarial block field at some `beta` in the window, the iterated route with that
    blocking fails as stated.
* **The `Jbar_P(l)` curve and the quenched `gamma_A`** (c8a 6.3 measurements, extended down to finer scales). They fix where `L_1`
  really is, i.e. at which `l` the budgets close, and so fix `N`.
* **W3, a widened landing window** (CPU, days). Certify the W1/one-box column for the truncated family **with an explicit tail
  budget**, sized by `near_budget_lt_one`, so that an enclosure of width `delta` can land. c4d's margin of 0.0013 is too thin.

**Decision for the owner.** Whether an explicit estimate of `gamma_0(L)` is worth commissioning (a desk study of Balaban's
constant chain, about one cycle). It decides whether the perturbative middle is about 10 or over 100 doublings, and with it
whether a computer-assisted crossover is realistic or only conceivable.

**Overall verdict.** P4 has a precise statement (`P4_*`) at M1's hand-over scale. Its reduction to a finite system is logically
clean (Openness, Lean) but carries all content in one input, the quenched conditional mass across the crossover (WL), which is
open and equivalent in kind to the weak-coupling lattice mass gap at a fixed coupling. The two-layer picture sharpens the
observables but does not split off an easy part. The next honest step is to state `P4_*` formally and to measure `(WL)` before
building anything on it.

---

## 6. Files and commands

* Lean: `formal/ProofPhase/Crossover/Openness.lean`.
* Build (one-time copy of the build cache into a throw-away folder, then the module):
  `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/build.sh`.
  Axioms: `axioms.sh` (writes to stdout; the log is `axioms.log`). The build folder `~/formal-c9x` was deleted after the check;
  `build.sh` recreates it.
* Numbers of section 2.1: one-loop formula in the text (`b_0 = 22/(48 pi^2)`, `N_* = 7.5 exp(2.69 (beta_* - 2.3))`).

## 7. Not checked

* Balaban's exact form of `p_0(g)` and the size of `gamma_0(L)` (recalled form; nobody has a number).
* The literature rows marked "recalled".
* Haller-Kennedy's method: existence and topic confirmed by search, the computer-assisted part not confirmed.
* Bhanot-Creutz: confirmed by search, located by secondary sources.
* The claim that Balaban's class at scale 0 contains the Wilson density (used only for the reading in 0.4, not in any implication).
* c7c's statement that gauge-blind and gauge-restricted influences agree for covariant specifications (used only to justify
  stating `P4_*` in the restricted form).
