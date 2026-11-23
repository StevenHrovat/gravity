# The unified lossy-step theorem: design

Working design note, 2026-11-23. Written before the Lean (`ProofPhase/Unified/`) and before `UNIFIED.md`, which is the
write-up. It fixes the abstraction, the general theorem, and how each of the three problems is literally a special case
with one named hypothesis.

Starting point: the owner's reading (PREP.md, "The electric weight as a function of the twist deficit is the coupling
constant's encoding"): a chain of lossy steps, each paying a cost fixed by a coupling, composed by a contraction, with a
universal floor. Part VI of the paper draft states the common open step in words; this design states it as one theorem.

---

## 1. What the three chains have in common

| | Yang-Mills | GRH | NP vs coNP |
|---|---|---|---|
| step | one box along the transfer direction (or one box along an influence path) | one scale (one more cell of Weil's form on a grid; the primes enter as impulses at the lags log p) | one restriction (fix a literal) |
| carried quantity | the influence (total variation of two pushed laws), or the path sum | the certified margin of the scale's section | the number of costly lines still in the refutation |
| price of a step | the box's contraction factor eta = e^{-F}, F the electric free energy (twist deficit) | the margin factor f_k (Szego: 1 - abs(k_k)^2) | the share 1 - theta of costly lines that survive |
| how steps compose | contraction coefficients multiply (`Mixing/Chain.lean`) | the margin is the start times the product of factors | survivors of survivors |
| floor | per step: the excess act 2C (`CompositeHTF.lean`) or the path entropy log mu (`Containment.lean`) | none (no slack is allowed: an exact step) | at the end: one line (the quantum) |
| what is read off | decay e^{-n (F - floor)}: block clustering, then a gap | the margin stays nonnegative at every scale: positivity | size >= e^{theta b} |

The minimal common structure is not a measure, an operator or a DAG: it is a **chain of certificates**. At step i there is
a set of certified values (`Cert i e`: "e is certified at step i"); each step carries every certified value e to a certified
value f_i e, with a factor f_i >= 0. Measures (influence bounds), Toeplitz forms (margins) and line counts are three ways
of certifying a number. Positivity of the structure is exactly f_i >= 0: a step may shrink a certificate, never flip its
sign.

## 2. The general theorem

**Core (the certificate ledger, `carry`).** If every step i < n carries `Cert i e` to `Cert (i+1) (f i * e)`, then
`Cert 0 e` gives `Cert n ((prod_{i<n} f i) * e)`.

**Prices as costs.** Writing the factor as f_i = e^{delta - c_i} (c_i the cost of the step, delta the universal floor
per step), prod f_i = e^{n delta - sum c_i} (`prod_exp_cost`). A factor is of this form for some real c_i iff it is
positive (`exists_cost_iff`): "the step is paid at a real cost" is the sign.

**The three readings of the ledger** (all corollaries of `carry`):

1. *Decay (upper certificates, `Cert i e := M i <= e`).* If step i pays at least c_i up to the floor,
   M_{i+1} <= e^{delta - c_i} M_i (`Pays`), then M_n <= e^{n delta - sum c_i} M_0 (`ledger`). With costs >= kappa:
   M_n <= e^{-n (kappa - delta)} M_0 (`decay`), and when kappa > delta the sum over n converges (`summable_of_gap`).
   **The gap is cost minus floor.**
2. *Size (the same ledger read backwards, with a quantum at the end).* If moreover M_n >= phi > 0, then
   phi e^{sum c_i - n delta} <= M_0 (`size`), i.e. log M_0 >= sum c_i - n delta - log(1/phi) (`size_log`).
3. *Survival (lower certificates, `Cert i e := e <= M i`).* If M_{i+1} >= f_i M_i with f_i >= 0, then
   M_n >= (prod f_i) M_0 (`survive`); with f_i = e^{-c_i}: M_n >= e^{-sum c_i} M_0 > 0 (`survive_pos`).

**The additive form (`accrue`).** In log units G = -log M the ledger is G_n >= G_0 + sum c_i - n delta: the global
quantity is at least the sum of the costs minus the floor. `pays_of_accrue` turns the additive form into `Pays`.

**Composition by contraction (`pays_of_submul`).** For any monoid of steps with a weight w >= 0 that is submultiplicative
up to the floor, w(a b) <= e^{delta} w(a) w(b), and steps of weight <= e^{-c_i}, the running products satisfy `Pays`.
This is the abstract form of `Mixing/Chain.lean` (`contracts_kcomp`) and of `CompositeHTF.lean` (`flux_superadd`).

**The shape of every open hypothesis (`CostAboveFloor`).** `CostAboveFloor cost delta`: there is kappa > delta with
cost >= kappa everywhere (uniformly over every outside, every refutation, every step). Yang-Mills and NP vs coNP have
their open step in this shape; GRH has it in the survival shape (the sign), see section 4.

Nothing problem-specific enters the general theorem: no lattice, no primes, no clauses. Its proofs are a few lines each;
the content of each problem sits entirely in one hypothesis. That is the point of the construction, and it is said
plainly in `UNIFIED.md`: the general theorem does not solve anything; it shows that each problem is one statement of the
same kind.

## 3. The three instances

**Yang-Mills (`Unified/YangMills.lean`).**
* *Chain, transfer kernels:* `Cert n e := Contracts (kchain Ks n) e`; the step is `contracts_kcomp`. With every box
  contracting by e^{-kappa} (any outside: the kernels `Ks i` are arbitrary), the influence across n boxes is
  <= e^{-n kappa} (`ym_chain`). Floor 0.
* *Chain, electric free energy:* G_k = F_e((k+1) L) accrues F_e(L) per box with floor 2C (the excess act):
  F_e((k+1)L) >= (k+1)(F_e(L) - 2C) (`ym_flux`, re-derived from `flux_superadd` through `accrue`).
* *Tubes (the paper's O1):* the path sum over n boxes with mu continuations per box and box weights w <= e^{-F},
  W_n = sum over paths of the product of the weights, satisfies `Pays` with cost F and floor log mu (path entropy).
  **Named hypothesis `YMOneBox`:** `CostAboveFloor` for the per-box electric cost against the floor log mu, uniformly over
  every outside. Conclusion (`ym_instance`): W_n <= e^{-n (F - log mu)}, summable. Plug-in (`ym_gap`): if the transfer
  correlations are dominated by the path sum (the path expansion, a stated link), `gap_of_geometric`
  (`Mixing/TimeGap.lean`) gives no spectral mass above e^{-(F - log mu)}.
* Evidence lemma: the proved per-box hand-over log(1 + sqrt 2) = 0.881 is below the floor log mu for mu >= 3
  (`handover_below_floor`): the hypothesis is not met by what is proved.

**GRH (`Unified/GRH.lean`).** `Cert k e := Sec t k e`: e is a certified lower bound of the Toeplitz section of size k+1
of Weil's form on a grid. **Named hypothesis `ScaleSign t`:** the mass is nonnegative and every scale step carries the
margin with a nonnegative factor. Proved: `ScaleSign t` iff every section is positive (`scaleSign_iff`, so the hypothesis
is exactly "positivity at every scale", not vacuous); then every finite section is positive, and in the finite model of
zeros (`ZeroModel`: finitely many zeros closed under the functional equation, the grid moments their exponential sums)
every zero is on the line and Weil's pairing is nonnegative (`grh_instance`, through `atoms_on_circle` and
`weil_criterion_finite`). With positive factors the margin is the start times e^{-sum c_k} (`grh_margin`).

**NP vs coNP (`Unified/ProofSize.lean`).** `Cert i e := card (Q i) <= e`, Q i the costly lines after i restrictions.
**Named hypothesis `CrossingCost Refutes theta b`:** every refutation admits b restriction steps, each leaving at most a
1 - theta share of the costly lines, with a costly line left at the end. Conclusion (`np_instance`): every refutation has
at least e^{theta b} lines. Reference (`resolution_meets_form`): for resolution the same bound is proved
(Ben-Sasson-Wigderson, `Proof/Dag.lean`, `size_width_exp`) with theta = (w + d + 1)/2n.

## 4. What does not fit cleanly (decided, reported)

* **GRH is the survival reading, not the decay reading.** In Yang-Mills and NP vs coNP the open step is a lower bound on
  the cost (cost above floor). In GRH the cost of each step is known exactly and no slack is allowed; the open step is
  the sign of the factor (the step does not overdraw the margin). Both are the same ledger, read from the other end.
* **In the finite model of GRH the factors vanish** once the scale exceeds the number of atoms (the Toeplitz sections
  become singular), so the sign is stated with f_k >= 0, not f_k > 0. "No factor vanishes" is the infinite-zero case.
* **The primes are not the steps** in GRH: the steps are scale cells and the primes enter as impulses at the lags
  log p (`grh/INDUCTION.md` 0.4). The task's "steps = primes" is the coarser reading.
* **The resolution reference is a branching chain.** Ben-Sasson-Wigderson runs the ledger along a path of a restriction
  tree, not a single chain; `resolution_meets_form` matches the conclusion, it does not construct a `CrossingCost`
  witness.
* **The Yang-Mills plug into the assembly** stops at a spectral gap of a stated transfer correlation. The identification
  of the path sum with the SU(2) blocked laws (`BlockGapBddW`, `V4/Gap.lean`) is not in Lean; the annealed-to-quenched
  step (III.5.7) is part of the hypothesis as the paper states it (VI.4), and the relation of the chain floor 2C to the
  tube floor log mu is III.5.8, open.

## 5. Files

* Lean: `ProofPhase/Unified/Ledger.lean` (general), `YangMills.lean`, `GRH.lean`, `ProofSize.lean`, `Unified.lean`
  (imports all four, the side-by-side statement).
* Docs: this file, `UNIFIED.md` (write-up), `axioms.sh` and `axioms.log`.
* Existing modules are imported, never edited.
