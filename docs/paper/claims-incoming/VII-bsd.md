# Claims incoming: Part VII, Birch and Swinnerton-Dyer (`draft/07-part-VII-bsd.md`)

Draft 2, 2026-11-24. Rows in the format of `../CLAIMS.md` (ID, claim, status, source, upgrade), for the coordinator to merge. The status
column holds one primary mark; a row with two parts of different status is split or carries the weaker status first. Lean paths of this
repository are relative to `docs/mass-gap/formal/`. Modules of the Mathlib-only core live in DMP.IM (public repository `im`, directory
`arsenal/`, files `Arsenal/BSD.lean` and `Arsenal/BSD/{Algebraic,Analytic,Count,Hasse}.lean`) and are cited as `Arsenal.BSD...`; they were
read in the working copy that is being merged into `im`. Notes are relative to `docs/unified/` (`BSD.md` is cited as BSD); the owner's
readings are in `docs/mass-gap/weak-coupling/PREP.md` (cited as PREP, entries of 2026-11-24).

Verification by this writer: every Lean name in the rows was checked by script against the declarations (`theorem`, `def`, `structure`,
`abbrev`, `instance`) of the cited file, and the statement was read in the source. **No Lean file was rebuilt.** The axiom log
`bsd-axioms.log` was written before `ProofPhase/Unified/BSDAPI.lean` was adapted today to the native core (it lists earlier signatures),
so the standard-axioms claim is **not** re-made for the adapted instance; see VII.7.1. External and classical references are cited as the
notes cite them and were not re-read.

## Part VII. Birch and Swinnerton-Dyer

### VII.0 State

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VII.0a | Clay's statement (Wiles): for an elliptic curve over Q, the Taylor expansion of L(E, s) at s = 1 is c (s - 1)^r + higher terms with c not zero and r the rank of E(Q); so L(E, 1) = 0 exactly when E(Q) is infinite | classical | Wiles' official description; BSD 1.1 | none |
| VII.0b | The Clay text also states the refined formula for c: real period, regulator, order of Sha, Tamagawa numbers, torsion order | classical | Wiles' official description; BSD 1.1 | none |
| VII.0c | The statement needs the continuation of L(E, s) to s = 1, which is modularity (Wiles, Taylor-Wiles, Breuil-Conrad-Diamond-Taylor) | external | BSD 1.2 | independent rebuild of modularity |
| VII.0d | `BSDStatement W` for K = Q (a continuation exists and the rank equals the order of its zero at s = 1) is the rank part of the Clay statement, given the continuation | paper | `Arsenal.BSD` (`BSDStatement`, `bsdStatement_iff`); BSD 3.2 | a Lean statement of Wiles' text word by word |
| VII.0e | This part proves no case of the conjecture that was not already known; the notes record no claimed proof of the general statement | (statement of scope) | BSD header, 5 | none |
| VII.0f | The rank part is open for analytic rank 2 and more | open | BSD 1.3 | a proof |

### VII.1 The problem, what is proved by others, what is open

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VII.1.1a | E(K) is finitely generated over a number field (Mordell 1922, Weil 1929); the proof is weak Mordell-Weil plus descent with a height | classical | Mordell; Weil; BSD 1.2 | none |
| VII.1.1b | Hasse's bound abs(a_p) <= 2 sqrt p (Hasse 1933-36, Weil 1948): the Riemann hypothesis of the curve over F_p | classical | BSD 1.2 | none |
| VII.1.1c | For CM curves L(E, s) is a Hecke L-function, entire with a functional equation (Deuring) | classical | Deuring 1953-56; BSD 1.2 | none |
| VII.1.1d | Every E/Q is modular; so L(E, s) is entire and the completed function has a functional equation with sign w = +1 or -1 | external | Wiles; Taylor-Wiles; Breuil-Conrad-Diamond-Taylor; Hecke; BSD 1.2 | rebuild |
| VII.1.1e | CM curves: L(E, 1) not zero gives E(Q) finite (Coates-Wiles 1977) and Sha finite (Rubin 1987) | external | BSD 1.2 | none needed for this paper |
| VII.1.1f | Gross-Zagier 1986: L'(E, 1) is a nonzero multiple of the height of a Heegner point; a simple zero gives a point of infinite order | external | BSD 1.2 | none needed for this paper |
| VII.1.1g | Kolyvagin 1988-90 with modularity: analytic rank 0 or 1 gives rank = analytic rank and Sha finite | external | BSD 1.2 | none needed for this paper |
| VII.1.1h | Buhler-Gross-Zagier 1985: the curve 5077a has a zero of order exactly 3 and rank 3 | external (recalled) | BSD 1.2 | re-reading of the paper |
| VII.1.1i | Kato 2004, Skinner-Urban 2014 and later: the p-part of the refined formula for many curves of rank 0 or 1 and many p | external (recalled) | BSD 1.2 | re-reading |
| VII.1.1j | p-parity: Monsky 1996, Nekovar, Dokchitser-Dokchitser 2010; so finiteness of Sha would give (-1)^rank = w | external | BSD 1.2 | none needed for this paper |
| VII.1.1k | Bhargava-Shankar 2015 with Skinner-Urban and others: average rank below 1; a positive proportion of curves have rank 0, a positive proportion rank 1; the rank part holds for a positive proportion; context only, not used | external (recalled) | BSD 1.2 | none |
| VII.1.2a | No construction of two or more independent points from a higher zero (no higher Heegner points); no bound "rank <= order" beyond order 1 | open | BSD 1.3, 4 | a construction and a bound |
| VII.1.2b | Finiteness of Sha in general (known for analytic rank at most 1) | open | BSD 1.3 | a proof |
| VII.1.2c | The refined formula for all curves of analytic rank 0 and 1 at all primes at once, and any case of rank 2 or more beyond single curves | open | BSD 1.3 | a proof |
| VII.1.2d | The Riemann hypothesis for L(E, s) (zeros on re s = 1) is part of GRH beyond Dirichlet L-functions | open | BSD 1.3; Part IV | a proof |
| VII.1.2e | No curve of proved analytic rank 4 or more is known; a zero is certified only up to order 3; numerics cannot certify a zero | classical (recalled) | BSD 1.3 | re-reading |

### VII.2 The card

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VII.2a | The BSD card: input a curve, a function and a sign; one open step `BSDStatement W`; conclusion the existence line and the parity of the rank; external inputs modularity and weak Mordell-Weil | Lean | `ProofPhase/Unified/BSDAPI.lean`, `Input`, `problem` | none (the open step is VII.5.1) |
| VII.2b | The ledger card: open step the growth form `C (log p)^r` of the partial Euler products, conclusion BSD, external input Goldfeld | Lean | `ProofPhase/Unified/BSDAPI.lean`, `LedgerInput`, `ledgerCard` | none (the open step is VII.5.2) |
| VII.2c | Nothing in the card is an axiom: a named part (R136a1) or an `OpenStep` or `External` slot is an ordinary hypothesis | Lean | `Arsenal.R136a1` (`R136a1`, `R136a1.out`); `ProofPhase/API.lean` (`OpenStep`, `External`) | audit rerun (VII.7.1) |
| VII.2d | IM states BSD over any number field and uses the true rank in the extended naturals (no junk value) | Lean | `Arsenal.BSD.Algebraic`, `algRank`; `Arsenal.BSD`, `BSDStatement` | none |

### VII.3 What is proved

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VII.3.0 | The standard-axioms-only claim for the adapted API instance and for the native modules is not re-made in this draft: the instance's axiom log predates today's adaptation, and nothing was rebuilt | paper | `bsd-axioms.log` (earlier signatures); this writer's check | regenerate the log; run IM's audit |
| VII.3.1a | E(K) is finitely generated if E(K)/2E(K) is finite (Mordell-Weil from weak Mordell-Weil, through Mathlib's descent and naive height) | Lean | `Arsenal.BSD.Algebraic`, `mordellWeil_of_weak`, `WeakMordellWeil` | a Lean proof of weak Mordell-Weil |
| VII.3.1b | The torsion of E(K) is finite, unconditionally | Lean | `Arsenal.BSD.Algebraic`, `torsion_finite` (Mathlib `finite_torsion`) | none |
| VII.3.1c | The rank `algRank` is the Z-module rank in the extended naturals; it equals `finrank` and is finite once E(K) is finitely generated | Lean | `Arsenal.BSD.Algebraic`, `algRank`, `algRank_eq_finrank`, `algRank_ne_top` | none |
| VII.3.1d | Rank zero is: every point has finite order; and, unconditionally, E(K) finite; E(K) is infinite exactly when the rank is positive | Lean | `Arsenal.BSD.Algebraic`, `algRank_eq_zero_iff_torsion`, `algRank_eq_zero_iff`, `infinite_iff_algRank_pos` | none |
| VII.3.2a | A continuation is analytic on `re s > a` with `a < 1` and equals Mathlib's L-series on a right half-plane; an entire function equal to the series for `re s > 3/2` is one; a continuation is analytic at 1 | Lean | `Arsenal.BSD.Analytic`, `IsContinuation`, `IsContinuation.of_entire`, `IsContinuation.analyticAt_one` | none |
| VII.3.2b | Two continuations agree near s = 1, so the order of the zero there is well defined; a zero exists exactly when the order is positive | Lean | `Arsenal.BSD.Analytic`, `continuation_unique`, `order_welldefined`, `zero_iff_order_ne_zero` | none |
| VII.3.2c | The gamma factor (over Q `N^{s/2} (2 pi)^{-s} Gamma(s)`) is analytic and not zero at s = 1; the completed function has the same order as the L-function | Lean | `Arsenal.BSD.Analytic`, `gammaFactor`, `gammaFactor_degree_one`, `gammaFactor_analyticAt`, `gammaFactor_one_ne_zero`, `completed_order` | none |
| VII.3.2d | From the local functional equation `xi(2 - s) = w xi(s)` and a natural-number order n, `w = (-1)^n`; the strip form over Q implies the local one | Lean | `Arsenal.BSD.Analytic`, `order_parity`, `order_parity_of_factor`, `FunctionalEquation`, `analytic_parity`, `FunctionalEquation.of_strip` | none |
| VII.3.3a | `count` is the number of solutions plus the point at infinity over a finite ring; `frobTrace = q + 1 - count`; the decidable Hasse check is the real inequality | Lean | `Arsenal.BSD.Count`, `count`, `frobTrace`, `hasseCheck`, `hasseCheck_iff` | none |
| VII.3.3b | Over a finite field the count is Mathlib's `Nat.card` of the group of points; at every prime of good reduction the count of the curve read mod p is Mathlib's | Lean | `Arsenal.BSD.Count`, `count_correct`, `reduceMod`, `count_reduceMod` | none |
| VII.3.3c | For y^2 = x^3 - x mod 5 the trace is -2 and the Hasse check passes, both by the kernel | Lean | `Arsenal.BSD.Count` (the two `example`s) | none |
| VII.3.4a | If `a^2 <= 4q`, the coefficients of `1/(1 - aT + qT^2)` satisfy abs(c_k) <= (k + 1) q^{k/2}; at bad places abs(c_k) <= 1 | Lean | `Arsenal.BSD.Hasse`, `invQuad`, `invQuad_coeff`, `quad_bound`, `lin_bound`, `invQuad_bound`, `invQuad_bound_lin` | none |
| VII.3.4b | Under Hasse at one place, the coefficients of Mathlib's local power series are bounded by max 1 ((k + 1) q^{k/2}); the first coefficient of `W.LFunction` is 1 | Lean | `Arsenal.BSD.Hasse`, `LocalHasse`, `localPowerSeries_coeff_zero`, `localPowerSeries_coeff_bound`, `eulerProduct_apply_one`, `LFunction_one` | none |
| VII.3.4c | An L-series with first coefficient 1 that converges absolutely somewhere is not zero for all large real arguments; so every continuation has a finite order at s = 1 once the series converges somewhere | Lean | `Arsenal.BSD.Hasse`, `LSeries_not_eventually_zero`, `order_ne_top_of_LSeries`, `order_ne_top_of_summable` | none |
| VII.3.4d | From the named parts Hasse and the Euler product bound: absolute convergence for `re s > 3/2`, a finite order at s = 1, and parity with no order given separately | Lean | `Arsenal.BSD.Hasse`, `Hasse`, `EulerProductBound`, `LSeriesSummable_of_hasse`, `order_ne_top`, `analytic_parity_of_hasse` | Lean proofs of the two parts |
| VII.3.4e | Over a finite field the local form of Hasse is the decidable check | Lean | `Arsenal.BSD.Hasse`, `hasseCheck_iff_card` | none |
| VII.3.5a | `BSDStatement W`: a continuation exists and the rank equals the order of its zero; with a continuation in hand it is the equation rank = order | Lean | `Arsenal.BSD`, `BSDStatement`, `bsdStatement_iff` | none |
| VII.3.5b | Under BSD, E(K) is infinite exactly when `Lam 1 = 0` (no finite generation assumed) | Lean | `Arsenal.BSD`, `existence_line` | none |
| VII.3.5c | Under BSD and the functional equation, a rank equal to n gives `w = (-1)^n`; also with `finrank` under finite generation | Lean | `Arsenal.BSD`, `rank_parity`, `rank_parity_of_fg` | none |
| VII.3.5d | Under BSD, Hasse and the Euler product bound, the rank is finite and `w = (-1)^rank` with no rank given separately | Lean | `Arsenal.BSD`, `algRank_ne_top_of_hasse`, `rank_parity_of_hasse` | Lean proofs of the two parts |
| VII.3.5e | `RefinedBSD` states the refined formula with the rank, torsion order and discriminant derived and the period, regulator, Sha order and Tamagawa product as free numbers; it gives `BSDStatement` when its leading coefficient is not zero | Lean | `Arsenal.BSD`, `RefinedBSD`, `bsd_of_refined` | Lean definitions of the four free quantities |
| VII.3.6a | The Frobenius eigenvalue `alpha` has norm `sqrt q` exactly when `a^2 <= 4q`, and the point count is `norm(1 - alpha)^2` | Lean | `ProofPhase/Unified/BSDAPI.lean`, `frobAlpha`, `frobAlpha_normSq`, `norm_frobAlpha`, `count_normSq` | none |
| VII.3.6b | Hasse's bound is an encoder: reflection coefficient `a/(2 sqrt q)` (cos theta), Szego factor `1 - a^2/(4q)` (sin^2 theta) in the unit interval | Lean | `ProofPhase/Unified/BSDAPI.lean`, `frob`, `frob_refl`, `frob_szego` | none (Hasse is an input) |
| VII.3.6c | Each step factor `N_p/p` lies between `(1 - p^{-1/2})^2` and `(1 + p^{-1/2})^2`; the partial product keeps a margin and has a chain bound; no finite stage is zero | Lean | `ProofPhase/Unified/BSDAPI.lean`, `factor_bounds`, `EulerData`, `EulerData.fac_bounds`, `EulerData.lower`, `EulerData.upper`, `EulerData.no_finite_zero`, `EulerData.P_le` | none (Hasse is an input) |
| VII.3.6d | That the counts in `EulerData` are those of one given curve is documented, not checked in Lean; it needs the link from Mathlib's local factor at the completion to the count over Z/p at every prime | open | BSD 2, 3.2 | the link, stated and proved |
| VII.3.7a | From modularity and weak Mordell-Weil as inputs: E(Q) finitely generated, torsion finite, the order independent of the continuation, its parity the sign | Lean | `ProofPhase/Unified/BSDAPI.lean`, `unconditional` | none |
| VII.3.7b | Gross-Zagier-Kolyvagin in its slot fills the card's open step whenever the order is at most 1; the content is external | Lean (plumbing) | `ProofPhase/Unified/BSDAPI.lean`, `LowRank`, `open_of_lowRank` | none |
| VII.3.7c | Goldfeld in its slot: from the growth form, BSD; true only when the prime data are the curve's own | Lean (plumbing) | `ProofPhase/Unified/BSDAPI.lean`, `ledgerCard`, `LedgerInput` | VII.3.6d |
| VII.3.8a | The curve y^2 = x^3 - x over Q and Z has discriminant 64 and is elliptic; the three points of order two are on it | Lean | `ProofPhase/Unified/BSDAPI.lean`, `E32`, `E32_Δ`, `E32Z`, `E32Z_Δ`, `E32_points` | none |
| VII.3.8b | For this curve the computed count mod p is Mathlib's at every odd prime; the trace of Frobenius runs at the odd primes to 37; the Hasse check runs by `#guard` at the odd primes to 59 and at p = 5 is proved by the kernel (the notes say "below 100"; the source checks to 59) | Lean | `ProofPhase/Unified/BSDAPI.lean`, `count_E32`, `hasse_E32_five` | extend the guard, or drop the note's claim |
| VII.3.8c | The known values of this curve (continuation and functional equation by Deuring, `L(E, 1)` not zero, E(Q) the four points by Fermat's descent) are external inputs | external | `ProofPhase/Unified/BSDAPI.lean`, `Data32`; Deuring; Fermat; BSD 3.3 | rebuild |
| VII.3.8d | From those values: rank 0 equals order 0, BSD holds for this curve, the card's open step is filled and the root number is +1 | Lean | `ProofPhase/Unified/BSDAPI.lean`, `input32`, `bsd_E32`, `card_E32` | none |
| VII.3.8e | Hasse holds for 32a2 and 37a1 at all 2262 primes below 20000 (largest ratio 0.99989 and 0.99648) | numerical | `bsd_check.py`, `bsd_check.log` | none (never proves for all primes) |
| VII.3.8f | 32a2: `L(E, 1) = 0.655514388573`, `L(E, 1)/Omega = 0.1250000000`, equal to the refined right-hand side 2 * 1/16 with recalled `c_2 = 2`, `Sha = 1`, `T = 4` | numerical | `bsd_check.log` | none |
| VII.3.8g | 37a1: `L'(E, 1) = 0.305999773834`, `L'(E, 1)/Omega = 0.0511114083` against the recalled regulator 0.0511114082; (0, 0) has infinite order (5P not integral, Nagell-Lutz) | numerical | `bsd_check.log` | none |
| VII.3.8h | The Euler ledger over `(log x)^r` at x = 100, 1000, 5000, 20000 is 1.65, 2.24, 2.12, 2.25 (32a2, target 2.157) and 6.82, 6.79, 7.96, 7.19 (37a1, target 8.23); the targets use Goldfeld's recalled constant `sqrt 2` | numerical | `bsd_check.log`; BSD 3.3 | none |
| VII.3.8i | The recalled constants (the Tamagawa number of 32a2, the regulator of 37a1, `sqrt 2`) | classical (recalled) | BSD 3.3 | re-reading |

### VII.4 What is borrowed

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VII.4a | Modularity gives the continuation and functional equation of L(E, s) over Q (`Input.cont`, `Input.fe`) | external | Wiles; Taylor-Wiles; Breuil-Conrad-Diamond-Taylor; `ProofPhase/Unified/BSDAPI.lean`, `Input` | rebuild (very large) |
| VII.4b | Weak Mordell-Weil: E(K)/2E(K) is finite (a named part in IM, an `External` in the API) | classical | Mordell 1922; Weil 1929; `Arsenal.BSD.Algebraic`, `WeakMordellWeil` | a Lean proof on Mathlib |
| VII.4c | Hasse's bound at every good prime (a named part in IM, an `External` in `EulerData`); its textbook proof is the positive definite degree form on End(E) | classical | Hasse; Silverman V.1.1 (recalled); `Arsenal.BSD.Hasse`, `Hasse`; `ProofPhase/Unified/BSDAPI.lean`, `EulerData` | a Lean proof (isogeny degrees or intersection theory on E x E) |
| VII.4d | Euler products with Hasse-type coefficient bounds converge absolutely for `re s > 3/2`, dominated by `zeta_K(s - 1/2)^2` (a named part) | classical (recalled) | `Arsenal.BSD.Hasse`, `EulerProductBound` | a Lean proof |
| VII.4e | Gross-Zagier and Kolyvagin with modularity: analytic rank 0 or 1 gives BSD (`LowRank`) | external | `ProofPhase/Unified/BSDAPI.lean`, `LowRank` | none needed for this paper |
| VII.4f | Goldfeld 1982: the 1965 growth form of the Euler products implies BSD and the Riemann hypothesis for L(E, s) (`LedgerInput.goldfeld`) | external | Goldfeld; K. Conrad 2005 (recalled); `ProofPhase/Unified/BSDAPI.lean`, `LedgerInput` | re-reading of the exact hypothesis at bad primes |
| VII.4g | The three named parts of IM are classical theorems missing from Mathlib, not open problems | classical | `Arsenal.R136a1`; `Arsenal.BSD` header | none |
| VII.4h | Weak Mordell-Weil is within reach on Mathlib; Hasse needs isogeny degrees or intersection theory on E x E; modularity is a very large formalisation | paper (estimate) | PREP (2026-11-24, BSD is IM; Hasse entries); BSD 2 | the formalisations |

### VII.5 The one open step

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VII.5.1 | **Open step of the card:** `BSDStatement W`, the order of the zero of L(E, s) at s = 1 equals the rank of E(Q); proved for order 0 and 1 by others, open from order 2 | open | `ProofPhase/Unified/BSDAPI.lean`, `problem`; `Arsenal.BSD`, `BSDStatement`; BSD 4 | a construction of r points from a zero of order r and a bound rank <= order |
| VII.5.2 | **Stronger slot:** the ledger form, `product of N_p/p` grows like `C (log p)^rank`; by Goldfeld it also gives the Riemann hypothesis for L(E, s) | open | `ProofPhase/Unified/BSDAPI.lean`, `ledgerCard`, `EulerData.Balance`; BSD 4 | a proof |
| VII.5.3 | The refined formula for all curves, with all five invariants, is open in general; it gives the rank part | open | `Arsenal.BSD`, `RefinedBSD`, `bsd_of_refined`; BSD 1.3 | a proof |
| VII.5.4 | A point of infinite order forces `L(E, 1) = 0` for every E/Q (contrapositive of Kolyvagin with modularity) | external | Kolyvagin; BSD 4 | none needed for this paper |
| VII.5.5 | A simple zero produces a point (Heegner) and a nonzero value forbids points (Kolyvagin); so the proved arrow runs by construction and exclusion, not by counting; from order 2 nothing is known in either direction | external | Gross-Zagier; Kolyvagin; BSD 4 | none needed for this paper |
| VII.5.6 | No finite stage of the Euler product is zero; the order of the zero is decided by all primes together | Lean | `ProofPhase/Unified/BSDAPI.lean`, `EulerData.no_finite_zero`; BSD 4 | none |
| VII.5.7 | The functional equation fixes the parity of the order and not the order | Lean | `Arsenal.BSD.Analytic`, `analytic_parity` | none |
| VII.5.8 | Hasse is the curve's local Riemann hypothesis, proved; the Riemann hypothesis for L(E, s) is global and open; BSD does not need it, its ledger form would imply it | classical | Hasse; Goldfeld; BSD 4; GRH-TIE-IN | a proof of GRH beyond Dirichlet |

### VII.6 DMP readings and VII.7 closure

| ID | Claim | Status | Source | Upgrade |
|---|---|---|---|---|
| VII.6a | BSD is IM: both sides are derived from one Weierstrass equation and the card takes no content input; a statement about form, not about settling | reading | PREP (owner, 2026-11-24, "BSD is IM"); BSD 3 | none (a reading stays a reading) |
| VII.6b | "The zeros follow existence": the order of the zero counts the independent rational points; exact counterpart in three levels (existence line, rank equation, ledger form) | reading | PREP (2026-11-24 entries on primes on a curve); BSD 0, 4 | none |
| VII.6c | Hasse is rotation at a DB: Frobenius at p acts as a rotation with `cos theta_p = a_p/(2 sqrt p)` the encoder's reflection coefficient; the piece left open in Lean is one rotation per DB confined by one positivity | reading (Lean for the encoder: `frob`, `frob_refl`) | PREP (owner, 2026-11-24, "rotation at DB shaped"); `ProofPhase/Unified/BSDAPI.lean` | none |
| VII.6d | Hasse's bound for one curve reads as `weil_bound_abs` at genus 1 (Lean proves it for every genus g from the Hodge index property and the intersection numbers; the genus-1 specialisation and the link of N to Mathlib's count are not made in Lean) | reading | `ProofPhase/Unified/HodgeLinear.lean`, `weil_bound_abs`; `ProofPhase/Unified/HodgeAPI.lean`, `curveCard`, `curve_open` | state the genus-1 instance and tie N to `count` |
| VII.6e | What is left of BSD is the `.cmb` record: the refined formula's counts and measures balance to a dimensionless 1 (logarithm 0); the functional equation carries both sides through the rotation with sign `(-1)^rank`; dividing by `(s - 1)^r` removes the zero | reading | PREP (owner, 2026-11-24, "what is left of BSD is the .cmb file"); BSD 4 | none |
| VII.6f | In Lean the refined ratio's five quantities are free numbers; "the ratio is 1" is the refined conjecture itself, open in general | open | `Arsenal.BSD`, `RefinedBSD`; PREP (same entry, care point) | Lean definitions and a proof |
| VII.6g | BSD in the triad: an equation between an existence count (independent points) and a zero count (the vanishing rate of the Euler ledger) | reading | BSD 4; PREP (the triad entries) | none |
| VII.7.1 | Regenerate the axiom log of the adapted API instance and run IM's audit on the native modules before the standard-axioms claim is made | paper | this writer's check of `bsd-axioms.log` | the rerun |
| VII.7.2 | If an independent proof supplies the construction and the bound for orders 2 and more, the card's open step is discharged by that work; one row, one verdict line and one abstract item of this paper change | paper | BSD 4 ("What would close it") | the proof |
