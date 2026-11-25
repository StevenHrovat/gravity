# Unconditional for finite systems

Private working note, 2026-11-23. It closes the first two items of section 8 ("Missing") of `DICTIONARY.md` for
finite systems (finite site set, finite single-site space): the two hypotheses of the Lean results of sections 2 and 3
are now proved, not assumed. `DICTIONARY.md` itself is not edited; read this note next to its sections 2, 3 and 8.

Claim marks as in the dictionary: **[Lean]** is proved in this repository, standard axioms only (`axioms-items.sh`,
`axioms-items.log`: 115 declarations, `propext`, `Classical.choice`, `Quot.sound`, no `sorry`, no new axiom).

## In plain words

* **Item 1 closed.** The couplings that `Glauber.lean` assumed (the measurable kernels Q of the coupling form of
  Dobrushin's condition) are now **built** from the classical objects. The classical condition alone, "the influence
  sums of Dobrushin's coefficients are at most alpha < 1", gives fast mixing of the heat-bath sampler.
* **Item 2 closed.** The spectral measure of the heat-bath operator and its support in [0, 1] are now **proved** from
  Mathlib's finite-dimensional spectral theorem. The spectral gap statement has no spectral hypothesis.
* **Both together:** for a finite spin system with positive weights, the classical Dobrushin condition alone implies
  fast mixing and a spectral gap of at least (1 - alpha)/n per single-site step. Nothing else is assumed.

## 1. The coupling from Dobrushin coefficients

File `ProofPhase/Mixing/Classical.lean`. **[Lean]**

**Setting.** A finite site set, a finite single-site space S with the discrete measurable structure, a probability
measure mu on the configurations with positive weights (`mu {sigma} > 0` for every sigma). That is the Gibbs measure of
every system with soft constraints.

| Object | What it is |
|---|---|
| `heatBath mu hpos` | The heat-bath update at site x (resample the spin at x from its conditional law given the others), as a Markov kernel, with `P_local` (only the spin at x changes) and `P_inv` (mu is invariant: detailed balance, `rev`, `bind_hbKernel`). |
| `dob mu x z` | **Dobrushin's coefficient**: the largest total-variation distance between the conditional laws at x of two configurations that differ only at z. |
| `maxCoup a b` | The **maximal coupling** of two probability vectors: the overlap `min(a, b)` on the diagonal, the two residuals coupled independently off it. Explicit formula; its marginals are a and b and its off-diagonal mass is at most the total-variation distance (`maxCoup_sum_right`, `maxCoup_sum_left`, `maxCoup_offdiag_le`). |
| `condTV_le_sum` | **Triangle inequality along hybrid configurations**: the total-variation distance of the conditional laws at x of sigma and sigma' is at most the sum of `dob mu x z` over the sites z where they differ. |

**How the coupling is built.** The coupling kernel at x takes two configurations, couples their two conditional laws at
x by the maximal coupling, and writes the two sampled spins back into the two configurations. Its off-diagonal mass is the
total-variation distance of the two conditional laws, and the hybrid triangle inequality bounds that by the influence sum
over the sites where the configurations differ. That is exactly the coupling inequality that `Glauber.lean` assumes:
`heatBath mu hpos` is a `SiteDynamics mu` with influence matrix `dob mu`, all fields proved. One maximal coupling per
update is enough; gluing couplings along the hybrids (the textbook route) is replaced by the triangle inequality for the
total-variation distance, which is the same estimate one level down.

**Results** (only the classical condition as hypothesis; `hpos` is positivity of the weights):

| Theorem | Statement |
|---|---|
| `tv_sweep_dobrushin` | Systematic scan, rows: if the sum over z of `dob mu x z` is at most alpha <= 1 for all x, then after t sweeps from any start, the total-variation distance is at most n alpha^t. |
| `tv_rs_dobrushin` | Random scan, columns: if the sum over x of `dob mu x z` is at most alpha for all z, then after k single-site steps the distance is at most n (1 - (1 - alpha)/n)^k. |
| `mixing_sweep_dobrushin`, `mixing_rs_dobrushin` | The mixing times: O(log n) sweeps, O(n log n) single-site updates. |
| `integral_sweep_dobrushin`, `integral_rs_dobrushin` | The same for bounded test functions. |

These are the theorems of section 2 of the dictionary with the assumed `SiteDynamics` replaced by `heatBath`.

## 2. The finite spectral theorem for the heat bath

File `ProofPhase/Mixing/FiniteSpectral.lean`. **[Lean]**

**Steps.**
1. *One site is a projection.* Conjugated by the square roots of the weights, the heat-bath matrix at a site is a
   symmetric idempotent matrix (`Bx_symm`, `Bx_idem`; reversibility plus `K_mul_K`: resampling twice is resampling
   once). A symmetric idempotent matrix has quadratic form between 0 and the squared norm (`quad_proj`).
2. *The random-scan operator is an average of projections*, hence a symmetric positive contraction (`Bm_quad`):
   `0 <= <v, B v> <= <v, v>` for all v.
3. *The spectral measure.* For a real symmetric matrix B with that property and any vector h, Mathlib's
   `Matrix.IsHermitian.spectral_theorem` gives `<h, B^k h> = sum_j lambda_j^k c_j^2`. The measure
   `rho = sum_j c_j^2 * (point mass at lambda_j)` is a finite sum of point masses, carried by [0, 1] (the eigenvalues
   lie in [0, 1] by step 2 applied to the eigenvectors), with `integral lambda^k d rho = <h, B^k h>`
   (`exists_spectral_measure`).
4. *The link.* The law of the sampler after k steps acts on test functions as the k-th power of the random-scan matrix
   (`heatBath_integral_iterate`), and the time correlation of `Link.lean` is `<h, B^k h>` for `h = sqrt(mu) (F - mu F)`
   (`timeCorr_eq`).

| Theorem | Statement |
|---|---|
| `timeCorr_spectral` | For every function F on configurations there is a finite measure rho on [0, 1] (a finite sum of point masses) with `acorr rho k = timeCorr F k` for all k. This is `hrep` and the support hypotheses of `spectral_gap_of_column`, now proved. |
| `spectral_gap_dobrushin` | With only the classical column condition (sum over x of `dob mu x z` at most alpha < 1): for every F the spectral measure exists and has no mass above 1 - (1 - alpha)/n. The spectral gap in time is at least (1 - alpha)/n per single-site step. No coupling, no spectral hypothesis. |

## 3. What is still not unconditional

* **Infinite or continuous single-site spaces.** Everything above uses a finite S. For a compact spin space such as the
  gauge group of lattice gauge theory the couplings Q (maximal couplings of the conditional laws, measurable in the
  boundary condition) and the spectral theorem of a self-adjoint operator on L^2 are still hypotheses in
  `Glauber.lean` and `Link.lean`. The lattice gauge theory instance of the dictionary therefore still rests on them.
* **Hard constraints.** The weights must be positive (soft constraints). Proper colourings and independent sets need
  conditionals that are undefined on forbidden pinnings; the support sets of M1 are not built here.
* **Systematic scan under column sums** is not formalized (rows only); the dictionary's remark on weighted norms stands.
* **The spectral statement is per test function.** It says: for every F, the spectral measure of F has no mass above
  1 - (1 - alpha)/n. That is the classical statement for the operator (every F), stated as the dictionary does. It is not
  restated as a list of eigenvalues of the operator.
* **Everything else of the dictionary** (sections 4 to 7: the chain from spatial mixing to counting, hardness beyond
  uniqueness, the reading of the owner's entry and the barriers) is as marked there, classical or conditional or open.
  The two items closed here do not touch them.

## 4. Files and checks

* `docs/mass-gap/formal/ProofPhase/Mixing/Classical.lean` (imports `Glauber.lean`), `FiniteSpectral.lean` (imports
  `Classical.lean` and `Link.lean`). New files only; nothing existing was edited.
* `docs/pnp/axioms-items.sh` builds both modules, prints the axioms of all 115 declarations and greps the sources for
  `sorry`, `admit`, `native_decide` and `axiom`; the output is `docs/pnp/axioms-items.log`.
