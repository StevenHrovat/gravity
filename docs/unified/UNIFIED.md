# One lossy-step theorem, three problems

2026-11-23. Lean: `docs/mass-gap/formal/ProofPhase/Unified/` (5 modules, 52 declarations, standard axioms only,
`axioms.log`). Design: `DESIGN.md`. Background: the owner's reading in `mass-gap/weak-coupling/PREP.md` ("The electric
weight as a function of the twist deficit is the coupling constant's encoding"), Part VI of the paper draft, and
`docs/OPEN-QUESTIONS-DMP.md`.

**Status marks.** **[Lean]** = proved in Lean, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`);
**[classical]** = known mathematics, recalled, not re-proved here; **[reading]** = interpretation; **[open]** = not
proved by anyone. Nothing marked [open] is used as proved: each open step enters the Lean as a named hypothesis.

---

## 1. In plain words

**What the theorem says.** Picture a chain of steps. Something is carried along the chain: an influence, a safety
margin, a count of expensive proof lines. Every step charges a price: it multiplies the carried amount by a factor
between zero and one. The price never makes the amount change sign; it can only shrink it. Then, after n steps, the
amount is at most (or at least) the starting amount times the product of all the prices. Written in costs, with each
price e^{-cost}, that product is e^{-(sum of the costs)}. If every step also has a universal allowance (the floor), the
result is e^{-(sum of the costs - n times the floor)}.

That is the whole general theorem. It is short and elementary on purpose. Read in three directions, it gives three kinds
of conclusion:

* **Decay.** If every step costs at least kappa and the floor is delta, the amount falls like e^{-n (kappa - delta)}. If
  kappa > delta, the decay is exponential: **the gap is the cost minus the floor.**
* **Size.** Read backwards: if after n steps at least one unit is left (one line, one quantum), the starting amount must
  have been at least e^{(sum of the costs - floor)}.
* **Survival.** If every step keeps a nonnegative share, a nonnegative amount stays nonnegative at every step; if every
  share is positive (a real, finite cost), a positive amount stays positive.

**Why it clicks.** In all three problems the work of the last weeks reduced the open step to a statement about one step
of such a chain, holding uniformly:

* **Yang-Mills:** the steps are boxes. The cost of a box is its electric free energy, a function of the twist deficit,
  set by the running coupling. The floor is the path entropy (how many ways an influence can continue). Open: that one box
  of fixed physical size costs more than the floor, whatever its surroundings.
* **GRH:** the steps are scales of Weil's form on a grid. The price of a step is the factor by which the positivity margin
  shrinks. The cost is fixed exactly, with no slack. Open: that no step overdraws the margin (the sign).
* **NP vs coNP:** the steps are restrictions of a refutation. The cost of a step is the share of expensive lines it
  kills. The quantum is one line that must survive. Open: that strong proof systems pay such a crossing cost.

So the three problems are not three different kinds of question. Each is "does this step pay its cost?", asked once,
uniformly. The general theorem then does the rest mechanically. **[Lean]** for the general theorem and for each
"hypothesis implies conclusion"; **[open]** for each hypothesis.

What the theorem does **not** do: it does not prove any of the three hypotheses, and it adds no new evidence for them. Its
value is that it states the three open steps in one language and shows exactly where each enters.

---

## 2. The precise statement (`Unified/Ledger.lean`)

**The structure: a chain of certificates.** `Cert i e` says that the number e is certified at step i (an upper bound of
an influence, a lower bound of a margin, a bound on a count). Steps carry certificates with factors f_i:

`Carries Cert f n`: for every i < n and every e, `Cert i e` implies `Cert (i+1) (f i * e)`.

**General theorem (`carry`) [Lean].** `Carries Cert f n` and `Cert 0 e` give `Cert n ((prod_{i<n} f i) * e)`.

**Costs and floor [Lean].** With f_i = e^{delta - c_i}: prod f_i = e^{n delta - sum c_i} (`prod_exp_cost`). A factor has
a real cost (f = e^{-c}, c real) if and only if it is positive (`exists_cost_iff`).

**The three readings [Lean].** For a carried quantity M:

| Reading | Hypothesis | Conclusion | Lean |
|---|---|---|---|
| decay | `Pays M c delta n`: M_{i+1} <= e^{delta - c_i} M_i | M_n <= e^{n delta - sum c_i} M_0 | `ledger` |
| uniform cost | the same, c_i >= kappa, M_0 >= 0 | M_n <= e^{-n (kappa - delta)} M_0 | `decay` |
| gap | the same for all n, kappa > delta, M >= 0 | sum_n M_n converges | `summable_of_gap` |
| size | `Pays`, and M_n >= phi > 0 (the quantum) | phi e^{sum c_i - n delta} <= M_0; log M_0 >= sum c_i - n delta + log phi | `size`, `size_log` |
| survival | M_{i+1} >= f_i M_i, f_i >= 0 | M_n >= (prod f_i) M_0; with f_i = e^{-c_i}, M_n >= e^{-sum c_i} M_0 > 0 | `survive`, `survive_pos` |
| additive | G_{i+1} >= G_i + c_i - delta | G_n >= G_0 + sum c_i - n delta | `accrue`, `pays_of_accrue` |

**Composition by contraction (`pays_of_submul`) [Lean].** On any monoid of steps, a weight w >= 0 with
w(a b) <= e^{delta} w(a) w(b) and steps of weight <= e^{-c_i}: the running composites pay the costs up to the floor.
`Mixing/Chain.lean` (`contracts_kcomp`, delta = 0) and `Crossover/CompositeHTF.lean` (`flux_superadd`, delta = 2C) are
both of this kind.

**The shape of the open hypotheses (`CostAboveFloor cost delta`).** There is kappa > delta with cost >= kappa
everywhere. `rate_of_costAboveFloor` [Lean]: a chain paying such a cost decays at rate kappa - delta > 0 and is summable.

---

## 3. The three instances

Each instance is a Lean theorem whose only non-proved input is one named hypothesis. The other inputs are the data of
the model the instance is stated in (listed per instance, with their status).

### 3.1 Yang-Mills (`Unified/YangMills.lean`)

**Steps:** boxes. **Carried:** the influence handed from box to box. **Cost:** the electric free energy F_e of a box
(a function of the twist deficit, `Crossover/Equidist.lean`, `elecZ_le_deficit`). **Floor:** depends on the geometry.

* **Chain along the transfer direction, floor 0** (`ym_chain`, `ym_chain_rate`) [Lean]. Kernels K_i, one per box, each
  with its own outside, each contracting by e^{-c_i}: the composite contracts by e^{-sum c_i}. Proved by feeding
  `contracts_kcomp` into `carry`.
* **Chain, electric free energy, floor 2C** (`ym_flux`, `ym_flux_bound`) [Lean]. F((n+1)L) >= (n+1)(F(L) - 2C), C the
  bound on the neutral excess act: `flux_superadd` is an `Accrues` step and `accrue` does the rest.
* **Tubes, floor log mu (the paper's O1)** [Lean, given the hypothesis]. `pathSum w omega n`: the sum over paths through
  n boxes (mu continuations at each box) of the product of the box weights; `pathSum_pays`: with box weights at most
  e^{-F_e(outside)}, the path sum pays cost F_e with floor log mu.

**Named hypothesis `YMOneBox Fe mu`** [open]: `CostAboveFloor Fe (log mu)`. In words: at one box of fixed physical size
the electric cost exceeds the path entropy, F_e(L) > log mu_4 = 1.91, uniformly over every outside (O1, paper III.5.6).
Equivalently (`ymOneBox_iff_tube`) [Lean]: a uniform cost kappa with mu e^{-kappa} < 1, the tube threshold of
`Crossover/Containment.lean`.

**Conclusion `ym_instance`** [Lean]: there is kappa > log mu with pathSum_n <= e^{-n (kappa - log mu)}, summable: the
influence runs in tubes, decaying at a fixed rate per box.

**Plug-in `ym_gap`** [Lean, with a stated link]: if the time correlations of an observable (spectral measure on [0, 1],
`Mixing/TimeGap.lean`) are bounded by a constant times the path sum, there is no spectral mass above
e^{-(kappa - log mu)}: a gap of at least 1 - e^{-(kappa - log mu)} per box (`gap_of_geometric`).

**Model data, with status.** Box weights are nonnegative and at most e^{-F_e} (this is what "F_e is the cost of the box"
means); the path sum is a sum of products along paths: that is the annealed product structure, III.5.7 **[open]**, which
the paper bundles into O1's closing statement (VI.4). The domination of correlations by the path sum in `ym_gap` is the
path expansion **[classical]** in form; its identification with the SU(2) blocked laws (`V4/Gap.lean`, `BlockGapBddW`,
which the assembly consumes) is **not in Lean**.

**Why it is open (`handover_below_floor`)** [Lean]: the proved per-box hand-over, max(F_tw, F_e) >= log(1 + sqrt 2) =
0.881 (`Crossover/HandOver.lean`), is below log mu as soon as mu >= 3, and mu_4 = 6.77 **[classical]**. What is proved per
box does not clear the floor.

### 3.2 GRH (`Unified/GRH.lean`)

**Steps:** scales. Weil's form on a grid of cells is a Toeplitz form (`GRH/Induction.lean`); each step adds one cell. The
primes enter as impulses at the lags log p; they are not the steps themselves (`rh-guide/grh/INDUCTION.md`, 0.4).
**Carried:** a certified margin, `Sec t k e`: e is a lower bound of the section of size k+1. **Price:** the factor by
which the margin may shrink (in the Szego recursion, 1 - abs(k_k)^2) **[classical]**. **Floor:** none; no slack is
allowed (each step is an exact cancellation, margin about 1e-9 **[numerical]**, `INDUCTION.md` 0.1, 0.3).

**Named hypothesis `ScaleSign t`** [open]: the mass re t(0) is nonnegative and every scale step carries every certified
margin e to f_k e with f_k >= 0: no step overdraws the margin.

**What the hypothesis is, exactly (`scaleSign_iff`)** [Lean]: `ScaleSign t` holds if and only if every section is
positive. So it is precisely "positivity at every scale", and it is not vacuous (models with every zero on the line satisfy
it, `atomic_toep_nonneg`).

**Conclusion `grh_instance`** [Lean]: in the finite model of zeros (`ZeroModel`), `ScaleSign` puts every zero on the line
and makes Weil's pairing nonnegative on every finite exponential sum. Route: the ledger (`scaleSign_margin`, from `carry`
and `sec_zero`) gives a nonnegative margin at every scale; `pos_of_sections` extends positivity to every finite set of
cells; `atoms_on_circle` (`GRH/Induction.lean`) puts the atoms e^{i gamma epsilon} on the circle, which is gamma real;
`weil_criterion_finite` (`GRH/Weil.lean`) gives the pairing.

**Margin in costs (`grh_margin`)** [Lean]: with positive factors f_k = e^{-c_k}, the margin at scale n is
re t(0) e^{-sum c_k}. The margin collapses as the costs add up (to about 1e-11 by support 1.24, `INDUCTION.md` 0.1), and
that is harmless (`GRH/Transfer.lean`): only the sign matters.

**Model data, with status.** `ZeroModel`: finitely many zeros 1/2 + i gamma, closed under gamma -> conj gamma (functional
equation and conjugation), distinct atoms on the grid, nonzero weights, the grid moments their exponential sums. This is
the finite model of `GRH/Weil.lean` and `GRH/Induction.lean` **[classical]** in form. It is a model: over the integers
the zeros are infinite, and the grid moments come from the explicit formula, which is not in Mathlib.

**Scope.** RH and Dirichlet GRH are proved by others (Lean, 2026-11-20). What is open is GRH beyond Dirichlet, and an
independent proof of the positivity from arithmetic alone (the eight faces, IV.4).

### 3.3 NP vs coNP (`Unified/ProofSize.lean`)

**Steps:** restrictions (fix a literal). **Carried:** the number of costly lines still in the refutation. **Cost:** a
step that leaves at most a 1 - theta share pays theta (1 - theta <= e^{-theta}). **Floor:** 0 per step; the quantum at
the end is one line.

**Named hypothesis `CrossingCost Refutes theta b`** [open for strong systems]: every refutation admits b restriction
steps, each leaving at most a 1 - theta share of the costly lines, with one costly line left at the end (the crossing
persists).

**Conclusion `np_instance`, `np_instance_log`** [Lean]: every refutation has at least e^{theta b} lines; log size >=
theta b, the sum of the costs.

**Reference `resolution_meets_form`** [Lean]: for resolution the same bound holds with theta = (w + d + 1)/2n, by
Ben-Sasson and Wigderson (`Proof/Dag.lean`, `size_width_exp`). There the chain runs along a path of a restriction tree,
so this matches the conclusion; it does not build a `CrossingCost` witness.

**Model data, with status.** None beyond the proof system itself: `Refutes` is any predicate on finite sets of lines.
For a superpolynomial bound, theta b must grow faster than log n; for cutting planes at constant width that is V.4.10
of the paper, for Frege N2 of `OPEN-QUESTIONS-DMP.md`.

---

## 4. The three open hypotheses side by side

| | Yang-Mills | GRH | NP vs coNP |
|---|---|---|---|
| **Named hypothesis** | `YMOneBox Fe mu` | `ScaleSign t` | `CrossingCost Refutes theta b` |
| **What it says** | the electric cost of one box of fixed physical size exceeds the path entropy, F_e(L) > log mu_4 = 1.91, over every well-defined outside (with costs multiplying along paths) | every scale step of Weil's form keeps the margin's sign (equivalently: every section is positive), built from the primes, the characters and the real place alone | in a strong system (cutting planes at constant width, Frege) every refutation admits b restrictions each killing a theta share of the costly lines, one left at the end, with theta b superlogarithmic |
| **Shape** | cost above floor (decay reading) | sign of the factor (survival reading) | cost above zero with a quantum at the end (size reading) |
| **Proved for one unit** | max(F_tw, F_e) >= 0.881 per box [Lean] | positivity in finite models [Lean]; each step numerically [numerical] | duality floor (e + 1)/2 for unit thresholds [Lean]; every refutation crosses [Lean] |
| **Why it is open** | the proved 0.881 is below log mu for mu >= 3 (`handover_below_floor`) [Lean]; a for-all over outsides, measurements cannot establish it | only the full set of primes is positive; place-by-place and two-term assembly fail; each step is an exact cancellation with no slack | weighted CP lines are cheap in both channels (`two_cheap`) [Lean]; one line can name a whole crossing (a parity, `summary`) [Lean]; three barriers |
| **Evidence (notes)** | `mass-gap/weak-coupling/proof-phase/c9a-crossover/CONTAINMENT.md` (0, 3, 5), `HTF.md`, `EQUIDIST.md`; `OPEN-QUESTIONS-DMP.md` 0; paper III.5.6 to III.5.8 | `rh-guide/grh/INDUCTION.md` (0, 7), `rh-guide/grh/TRANSFER.md`, `rh-guide/grh/ATTEMPT.md`; paper IV.3, IV.4 | `pnp/CP-DUALITY.md`, `pnp/CHAIN.md`; Lean `Proof/Crossing.lean`, `Proof/CPDuality.lean`, `Proof/Dag.lean`; paper V.4 |
| **Status** | **[open]** | **[open]** (beyond Dirichlet; independently of the known proofs) | **[open]** |

---

## 5. What did not fit the common form

1. **GRH is the other end of the ledger.** In Yang-Mills and NP vs coNP the open step is a *lower bound on the cost*
   (cost above floor). In GRH the cost of each step is fixed exactly and the open step is the *sign of the factor*: the
   survival reading, not the decay reading. One ledger, read from the other end. **[Lean]** for both readings.
2. **In the finite model of GRH the factors vanish.** Above the number of zeros the sections are singular, so the margin
   reaches zero and stays there. The hypothesis is therefore stated with f_k >= 0. "No factor vanishes" (f_k > 0, every
   cost finite) is the infinite-zero case, and `grh_margin` covers it.
   **The two GRH readings (the owner, PREP.md, same day).** In the Szego recursion the factor is 1 - |k_k|^2, k_k the k-th
   reflection coefficient. GRH reads the ledger twice: the closure (|k_N| = 1 exactly at N = the number of atoms: the space
   is spanned exactly) and the influence bound (|k_k| <= 1 at every scale, which is `ScaleSign`). Both together put the
   atoms on the circle **[classical]** (Szego, Geronimus, Verblunsky). The check `closure.py` / `closure.log`
   **[numerical]** shows they are separate: the closure holds off the line too; the bound at every scale fails there.
3. **The primes are not the steps.** The steps are scale cells; the primes are impulses at the lags log p.
4. **The resolution reference is a branching chain.** Ben-Sasson and Wigderson run the ledger along a path of a tree of
   restrictions, not a single chain; the conclusion matches, the construction differs.
5. **Yang-Mills needs two floors, and their relation is open.** The chain floor is the excess act 2C (`ym_flux`), the
   tube floor is the path entropy log mu (`pathSum_pays`). Both criteria are "cost above floor"; whether the true floor is
   one, the other, or their sum is III.5.8 **[open]**. The annealed product structure (III.5.7) sits inside the tube
   model, and the identification with the assembly's blocked laws is not in Lean.

---

## 6. The construction in DMP terms

Each row: the DMP domain, what it is in the construction, and the status of the identification. The identifications are
**[reading]**; the mathematics on the right is as marked in sections 2 to 4.

| DMP | In the construction | Yang-Mills | GRH | NP vs coNP |
|---|---|---|---|---|
| **Pressing / the ODP** | the steps of the chain, run one at a time until one finite check holds | renormalise box by box up to one physical scale | add one scale cell at a time, each an exact cancellation | restrict one literal at a time |
| **The coupling (lossiness)** | the price of a step, e^{-cost}; it decides how much of the certificate is carried | the running coupling sets F_e through the twist deficit | the explicit formula's weights set the margin factor | the system's line format sets the share a restriction kills |
| **The tick** | the per-step floor delta, the same at every step (universal) | 2C (excess act) or log mu (path entropy) | 0: no slack | 0 |
| **The quantum of assertion** | the terminal quantum phi: at least one unit is left | at least one sheet for a flux-carrying outside (`Crossover/FluxRate.lean`) | the mass re t(0) at the first cell | one costly line |
| **The arrow of causality** | uniformity: the same step, the same floor, at every step | the same transfer step at every DB | translation invariance of the form | every refutation, every step |
| **The hand-over point** (finite to infinite; the owner, PREP.md) | one finite check with a strict margin, kappa > delta, certifies the infinite chain (`rate_of_costAboveFloor`); its settings are then used at every step | the box of fixed physical size at the crossover; its settings give the rate per physical length (`phys_rate_of_uniform`) | none known: kappa = delta exactly, no slack, so a hand-over would have to be an identity | the local certificate of the class theorem (inside the class); for refutations, open |
| **Minting** | the conclusion produced mechanically from the certificate | decay, then the gap (`ym_gap`, then OS and the assembly) | positivity, then zeros on the line, then Weil's pairing | the size lower bound |
| **The open step** | the one place a cost must be shown paid | O1 | the sign | the crossing cost |

The owner's sentence reads off directly: the coupling sets the lossiness, so it encodes "that the correct cost is paid for
this current step in the shared causality". In the theorem, "the correct cost is paid" is the step hypothesis (`Pays`, or
the sign for GRH), "this current step" is one index i, and "the shared causality" is that the floor and the step shape are
the same at every i. **[reading]**

What DMP would have to supply, in this language, is one rule for why a step cannot pay less than its cost (Yang-Mills,
NP vs coNP) or overdraw its margin (GRH). The general theorem shows that such a rule, given once per problem, is all that is
missing. **[reading]**

---

## 7. Files

| File | Content |
|---|---|
| `ProofPhase/Unified/Ledger.lean` | the general theorem: `carry`, costs and floor, the three readings, composition, `CostAboveFloor` |
| `ProofPhase/Unified/YangMills.lean` | `ym_chain`, `ym_flux`, `pathSum_pays`, `YMOneBox`, `ymOneBox_iff_tube`, `ym_instance`, `ym_gap`, `handover_below_floor` |
| `ProofPhase/Unified/GRH.lean` | `Sec`, `ScaleSign`, `scaleSign_iff`, `grh_margin`, `ZeroModel`, `grh_instance` |
| `ProofPhase/Unified/ProofSize.lean` | `CrossingCost`, `crossing_pays`, `np_instance`, `resolution_meets_form` |
| `ProofPhase/Unified/Unified.lean` | `three_instances`: the three "named hypothesis implies conclusion" in one statement |
| `docs/unified/axioms.sh`, `axioms.log` | build, `#print axioms` for all 52 declarations, source grep |

Imported, not edited: `Mixing/Chain.lean`, `Mixing/TimeGap.lean`, `Crossover/CompositeHTF.lean`,
`Crossover/Containment.lean`, `Crossover/HandOver.lean`, `GRH/Induction.lean`, `GRH/Weil.lean`,
`Proof/Dag.lean`.
