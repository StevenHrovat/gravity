# GRH tie-in: the easy direction, the external proofs, and the function-field instance

Status: 2026-11-23. Follows `OPEN-STEPS-DMP.md` section 2 (b), (c+), (d). Under the construction principle: content from the
best existing results, cited and audited; DMP supplies the tying theorems.

Files:
- Lean: `ProofPhase/GRH/TieIn.lean` (easy direction, external hypotheses, the tie) and `ProofPhase/GRH/TieInFF.lean`
  (curves over a finite field). `grhtiein-axioms.sh` and `grhtiein-axioms.log`: 43 declarations, all on the standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`), no `sorry`, no `native_decide`.
- Third-layer check: `grh_tiein_check.py`, `grh_tiein_check.log`. CPU only, about two seconds, no saved data.

Status marks as in `OPEN-STEPS-DMP.md`: **Lean**, **classical**, **external**, **numerical**, **reading**, **open**.

---

## 0. In plain words

**The easy direction (Lean).** If every zero is on the line, Weil's pairing is nonnegative, and so every finite section of the
ledger's Toeplitz form is positive, which is `ScaleSign`. Part of this was already in the repository (the pairing level);
the missing piece, the step from the pairing to the ledger's sign, is now a theorem. In the finite model with multiplicities
it is an equivalence: **`ScaleSign` holds exactly when every zero is on the line.**

**The external proofs.** Others proved RH for zeta and GRH for all Dirichlet L-functions in Lean (released 2026-11-20). The
repository records the statement and its tie as two named hypotheses, written in the same words as their theorems and in
Mathlib's own vocabulary. From them, through the easy direction, the project's sign follows. So the Dirichlet column of the
ledger becomes **a theorem from others' work plus our tie**. Two things stay named inputs of the tie, and the audit list
says what they are:
1. the external hypothesis itself (to be discharged by importing their library, not vendoring it);
2. the explicit-formula identity that makes the ledger's prime-side moments equal Weil's zero pairing of a test function.
   In the finite model of the ledger this identity is a theorem and needs no hypothesis. In the infinite case it is the
   classical explicit formula, which Mathlib does not have.

**The function-field instance (Lean, vacuity check).** A curve of genus `g` over `F_q` gives a finite existence space with
`2g` atoms and a real tick (`F_q` to `F_{q^m}`, the lag `m log q`). Weil's theorem (Hasse-Weil bound, named external
hypothesis; Mathlib has none of it) puts the atoms on the circle. Then, as theorems:
- the ledger's sign holds;
- in this model the sign is *equivalent* to Weil's theorem (so the sign is exactly the Riemann hypothesis of the curve);
- the sections are definite up to the number of atoms, and the next one is singular: the closure.
The GRH column is therefore inhabited by a true case with a genuine tick, which the zeta grid model cannot show. The CPU check
counts the points directly over `F_p, F_{p^2}, F_{p^3}, F_{p^4}` for three genus-2 curves and confirms all of it.

**What this does not do.** It does not touch GRH beyond Dirichlet L-functions (Dedekind, Hecke, automorphic: open, also for
the external authors), and it does not give the sign from the primes alone. Everything above takes the sign *from* the
zeros (easy direction) or from Weil's theorem. The independent route, positivity from the prime side, is still the open
step. Section 5.

---

## 1. The easy direction in Lean (`TieIn.lean`)

**Already in the repository (checked before writing):**

| declaration | what it says | file |
|---|---|---|
| `weilSum_re_nonneg_of_real` | zeros on the line give `Re W(F) >= 0` for every test function `F`, any family of zeros | `GRH/Weil.lean` |
| `weil_criterion_finite` | both directions on finite exponential sums, finite model | `GRH/Weil.lean` |
| `atomic_toep_nonneg` | positive atoms on the circle give positive Toeplitz sections | `GRH/Induction.lean` |
| `grh_instance` | in the finite model, `ScaleSign` puts every zero on the line (hard direction) | `Unified/GRH.lean` |

So the easy direction **at the level of the pairing** existed. What did not exist was the step to `ScaleSign` of the
Toeplitz moments. **New, Lean:**

- `scaleSign_of_explicit_formula`: zeros on the line, plus the explicit formula `ExplicitFormula T t gamma sigma` (the
  Toeplitz form of `t` on the cells `s` with coefficients `c` equals Weil's pairing of the test function `T s c`), give
  `ScaleSign t`. Any family of zeros, infinite included. The test class `T` is left open on purpose: finite exponential sums
  (`gridTest`, the finite model) or smoothed cells (the infinite case, where point masses are not admissible).
- `scaleSign_of_online`: in the finite model `ZeroModel`, with real nonnegative weights (the multiplicities), zeros on the
  line give `ScaleSign` with **no** explicit-formula hypothesis: the moments are the atoms' power sums.
- `scaleSign_iff_online`: therefore, in the finite model with multiplicity weights,
  `ScaleSign Z.t <-> every zero on the line`. The hard direction is `grh_instance`.
- `moments_zpow`, `mass_nonneg_of_forms`: small helpers (Hermitian moments of atoms on the circle with real weights are the
  power sums for every integer exponent; nonnegative forms give nonnegative mass).

How it is used below: `scaleSign_of_online` is the tie in the finite model (section 2) and the function-field step
(section 3); `scaleSign_of_explicit_formula` is the tie in the general form.

## 2. The external proofs and the tie

### 2.1 What they prove [external]

Source: the entries S1 to S4 of `docs/rh-guide/SOURCES.md`. In this round the statements were read again from the two
primary places (the top-level file `src/Main.lean` of the community mirror, and the verification page of S2) through a read-only
web fetch. **Nothing was cloned, vendored, built or run.** The proof itself was not read here.

Released 2026-11-20, about 17 million lines, 175,187 modules; certified by the Lean and Mathlib communities (S1). Verification
page (S2, state of 2026-11-23): built with Lean 4.33.1 and the matching Mathlib release; only the three standard axioms on
the five headline theorems and on `robin_inequality`, `lagarias_inequality`; the statements were matched, as elaborated
terms, against a file that imports only Mathlib, by three independent comparison tools; several independent kernels accept
the export; two further end-to-end runs were still in progress when the page was read.

The five theorems of `Main.lean`, with the types printed on the verification page (copied, not paraphrased):

```lean
theorem riemannHypothesis : RiemannHypothesis
-- Mathlib's own: forall s, riemannZeta s = 0 -> (not exists n : Nat, s = -2 * (n + 1)) -> s <> 1 -> s.re = 1 / 2

theorem LFunction_ne_zero_of_half_lt_re :
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

theorem LFunction_eq_zero_re :
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

theorem LFunction_eq_zero_re_of_isPrimitive :
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```
(`riemannZeta_eq_zero_re` is the written-out form of the first.)

**Scope, exactly.** Zeta, and Dirichlet L-functions of every modulus and every character (primitive or not), zeros in the
open strip `0 < Re s < 1` on `Re s = 1/2`, and the nonvanishing for `Re s > 1/2`. **Not** covered: Dedekind zeta functions,
Hecke L-functions, automorphic L-functions (stated on S2; the author expects extensions, S3, which is not a theorem).

### 2.2 The two named hypotheses and the tie [Lean]

In `TieIn.lean`, as hypotheses (definitions of type `Prop`, not axioms, nothing imported from their library):

- `ExtRH := RiemannHypothesis` (Mathlib's own definition, so it is their `riemannHypothesis` type if both sides use the same
  Mathlib).
- `ExtDirichletGRH`: their `LFunction_eq_zero_re`, word for word.

The tie, with `StripZeros L gamma` = "the family `rho_i = 1/2 + i gamma_i` lists zeros of `L` in the open strip":

| theorem | says |
|---|---|
| `real_of_extDirichlet`, `real_of_extRH` | the external hypothesis puts every strip zero on the line: `gamma_i` real |
| `dirichlet_tie_in`, `zeta_tie_in` | general form: external hypothesis + `ExplicitFormula` gives `ScaleSign t` and `Re W(F) >= 0` for every test function |
| `dirichlet_tie_in_finite`, `zeta_tie_in_finite` | finite model of the ledger: a `ZeroModel` whose zeros are strip zeros, with multiplicity weights, gets `ScaleSign` and nonnegative Weil pairing on every finite exponential sum **from the external hypothesis alone** |

**Status of the Dirichlet column after this round.**
- Finite model of the ledger: **external hypothesis + Lean tie**, a complete derivation. `Ext*` is the only non-proved input.
- Infinite case: **external hypothesis + Lean tie + the explicit formula on the ledger's test class** (named, classical for
  Dirichlet L-functions, not in Mathlib). Nothing else.
- The independent positivity route (not through the zeros) stays open (section 5).

### 2.3 Audit list: what discharges the external hypothesis by importing their result

Each item is a thing to check or do; none is done here.

1. **Statement identity.** In an environment that has both libraries, check `example : ExtDirichletGRH := LFunction_eq_zero_re`
   and `example : ExtRH := riemannHypothesis` (the second is trivial by definition if the Mathlib is the same). The statements
   above were compared by eye with `ExtDirichletGRH` and agree; the machine check is the audit.
2. **Version skew.** Their build: Lean 4.33.1 with the matching Mathlib. This repository: Lean 4.34.0 with Mathlib v4.34.0.
   `riemannZeta`, `DirichletCharacter.LFunction`, `RiemannHypothesis` must unfold to the same objects in both. Either bump
   this repository's toolchain to theirs for the one bridge file, or check the three definitions in both versions.
3. **Their `Statements` module.** `Main.lean` uses the names `DirichletLNonvanishingRightOfHalf`, `DirichletLZerosOnLine`,
   `PrimitiveDirichletLZerosOnLine`, `RiemannZetaZerosOnLine`; the unfolded forms above come from the verification page, not
   from reading `Statements.lean`. Read it.
4. **Axiom footprint, again, by ourselves.** Run `#print axioms` on the five theorems in a build of their library: expect only
   `propext`, `Classical.choice`, `Quot.sound`. Also grep the library for `sorry`, `native_decide`, `Lean.ofReduceBool`,
   `unsafe`, `implemented_by`, `extern`, custom `elab`/`macro` that could alter what a statement means.
5. **Trust base.** The three standard axioms are a statement about the proof term. What remains: the Lean kernel, the
   independent kernels the community used, and that Mathlib's definitions mean what the informal statement says (S1, S2 give
   the matching with a Mathlib-only file). Read their two caveats (a stub in one comparison step; two runs still in progress
   on 2026-11-23) and re-read the page when they finish.
6. **Import mechanics.** Policy of this project: cited and audited, not vendored. A dependency pinned by commit in a separate
   lake workspace, building only a one-file bridge that states `ExtDirichletGRH` and `ExtRH` from their theorems, keeps the
   main build untouched. The cost is their full build (175,187 modules); a cache from the community, if available, avoids it.
   Decide where this check runs (memory heavy).
7. **Scope check, our side.** The tie uses only: zeros in the open strip, `rho = 1/2 + i gamma`. Trivial zeros (`Re <= 0`)
   and, for imprimitive characters, the extra zeros on `Re s = 0` are outside the strip. Zeta is covered by `ExtRH` (the
   trivial-zero and pole exclusions are derived from `0 < Re < 1` in `real_of_extRH`).
8. **Closure under the functional equation (`sigma`).** `ZeroModel` and the Weil pairing take `gamma (sigma i) = conj (gamma i)`.
   For one `L(chi, .)` this holds: a zero `rho` gives the zero `1 - conj rho` of the same function (functional equation plus
   `L(chi-bar, s-bar) = conj L(chi, s)`). Classical; to be stated and used as a hypothesis in a model that is built from a
   real `L(chi, .)`.
9. **Multiplicities.** Weights are real nonnegative (multiplicities). A model built from a real `L(chi, .)` must take them from
   the analytic order of vanishing; the finite model takes them as data.
10. **The explicit formula on the ledger's test class.** The one classical input of the infinite case: for the test class the
    grid form uses (smoothed cells, with decay), the prime side (`Lambda(n) chi(n)` terms, archimedean Gamma term, pole terms
    for the trivial character) equals Weil's zero pairing. Not in Mathlib. The external library has statements named
    `explicit_formula_dirichlet_zeros_right_half`, `explicit_formula_and_window_count` (S4, statements only): read them, but
    note they are used for a different purpose (a window count) and may not have the shape needed.
11. **Convergence.** In Lean `tsum` of a non-summable family is `0`, so the pairing `weilSum` is nonnegative even then, vacuously.
    For a real `L(chi, .)` the sum over zeros of `F(gamma) conj F(gamma)` converges for the right test class (zero count
    `N(T) = O(T log T)`, also not in Mathlib). The audit must show summability, otherwise "nonnegative pairing" says nothing.
12. **Which moments.** The `t` in `ScaleSign t` must be the ledger's Dirichlet prime-side moment sequence, the one in
    `ExplicitFormula`. In `Unified/GRH.lean`, `t` is abstract; the Dirichlet column has to name it.

---

## 3. The function-field instance (`TieInFF.lean`)

### 3.1 The model [classical facts as fields; named external hypothesis for Weil]

`CurveModel g q` carries the classical facts about a curve of genus `g` over `F_q` as fields (not proved here): `n` distinct
Frobenius eigenvalues `alpha_i` with multiplicities adding to `2g`, closed under conjugation (real `L`-polynomial) and under
`alpha -> q/alpha` (functional equation), and the point counts `N_m = #C(F_{q^m})` given by rationality,
`N_m = q^m + 1 - sum mult_i alpha_i^m`. The ledger's moments are `A_n = sum mult_i z_i^n` with `z_i = alpha_i / sqrt q`
(the tick normalisation), and `moment_pointcount` states `(sqrt q)^n A_n = q^n + 1 - N_n`: **the moments come from the point
counts alone**, the prime side at the lag `n log q`.

`WeilBound`: `|alpha_i| = sqrt q`. **Weil's theorem** (1948, the Hasse-Weil bound; **classical**, named external hypothesis).
Checked by search in the pinned Mathlib (v4.34.0): nothing on the Hasse-Weil bound, zeta functions of curves, or Weil's
criterion.

### 3.2 What is proved from it [Lean]

- `CurveModel.toZeroModel`: under `WeilBound`, the curve is a `ZeroModel` of `Unified/GRH.lean`, with zeros
  `rho_i = 1/2 + i gamma_i`, `gamma_i = arg z_i` real, and the multiplicities as weights.
- `curve_scaleSign`: `ScaleSign` of the curve's moment sequence, by `scaleSign_of_online` (section 1).
- **`curve_scaleSign_iff`: `ScaleSign t <-> WeilBound`.** The converse direction uses `atoms_on_circle` with the mirror
  closure built from the functional equation and conjugation (`CurveModel.mirror`). So in this model the ledger's sign is
  exactly the Riemann hypothesis of the curve, and it is supplied from outside by Weil.
- **`curve_sections`: the closure.** Under `WeilBound`, with `n` distinct atoms (`n = 2g` when the `L`-polynomial has simple
  roots, `curve_closure_2g`):
  - every section of size `m <= n` is definite (no nonzero null vector): the reflection coefficient has `|k| < 1` at each
    step before the closure;
  - the section of size `n + 1` has a nonzero null vector with last coefficient `1`: `|k_n| = 1`, the existence space is
    spanned exactly. The general pieces are `section_definite` and `section_degenerate` for any `k` distinct atoms on the
    circle with positive weights.

So the GRH column of the ledger is **inhabited by a true theorem case with a real tick**, with the single named external
input Weil's bound (and the classical structure of the zeta function of a curve).

Not done: a concrete curve built inside Lean (the fields would need point counts over all `F_{q^m}`); and `Weil`'s bound itself.

### 3.3 The CPU check [numerical]

`grh_tiein_check.py` lists the elements of `F_{p^m}` and counts `N_1, ..., N_4` directly (no rationality, no Weil), for the
three genus-2 curves of `open_steps_check.py` part B with `p = 7, 11, 13`:

| p | N_1..N_4 counted | N_3, N_4 predicted from N_1, N_2 | least eigenvalue, sections 1..5 | `abs(k_1..k_4)` |
|---|---|---|---|---|
| 7 | 11, 53, 380, 2409 | 380, 2409 (agree) | 4, 2.87, 2.17, 0.85, -3e-15 | 0.283, 0.204, 0.658, 1.000 |
| 11 | 11, 147, 1337, 14795 | 1337, 14795 (agree) | 4, 3.70, 1.65, 1.33, -3e-16 | 0.075, 0.577, 0.116, 1.000 |
| 13 | 10, 162, 2026, 28374 | 2026, 28374 (agree) | 4, 2.89, 2.71, 0.24, 2e-15 | 0.277, 0.083, 0.933, 1.000 |

- N_1 and N_2 agree with `open_steps_check.log`; the `abs(k)` agree with that log to the printed digits.
- Rationality: the directly counted `N_3, N_4` equal the values predicted from `N_1, N_2`. So the moments beyond `g` are spanned
  by the prime side, as the structure says.
- The sections of size 1 to 4 are definite and the one of size 5 `= 2g + 1` is singular, the closure of `curve_sections`,
  computed from the counts alone.
- Control: one count changed by one (`N_4 + 1`): the size-5 section gets a negative eigenvalue (about `-5e-3` to `-8e-3`):
  the counts and the sections are tied, a miscount is detected.

---

## 4. Status table of the GRH column after this round

| case | statement | status |
|---|---|---|
| zeros on the line imply the sign, pairing level | `weilSum_re_nonneg_of_real` | Lean (before) |
| zeros on the line imply the sign, ledger level, finite model | `scaleSign_of_online`, `scaleSign_iff_online` | **Lean (new)** |
| same, general families, given the explicit formula | `scaleSign_of_explicit_formula` | **Lean (new)**, explicit formula named |
| zeta and every Dirichlet L-function: zeros on the line | `ExtRH`, `ExtDirichletGRH` | **external** (others, Lean, 2026-11-20); audit list 2.3 |
| Dirichlet column, finite model of the ledger | `dirichlet_tie_in_finite` | **external hypothesis + Lean tie** |
| Dirichlet column, infinite case | `dirichlet_tie_in` | external hypothesis + Lean tie + explicit formula (named, classical) |
| curves over `F_q`: sign, equivalence with Weil, closure | `curve_scaleSign`, `curve_scaleSign_iff`, `curve_sections` | **Lean**, given Weil's bound (classical, named) and the classical structure fields |
| curves over `F_q`: counts, rationality, definite sections and closure | `grh_tiein_check.py` | numerical |
| GRH beyond Dirichlet (Dedekind, Hecke, automorphic) | | **open** |
| the sign from the primes, characters and real place alone | `ScaleSign` | **open** |

## 5. What this does not do

- It does **not** touch GRH beyond Dirichlet L-functions. The external proofs do not cover Dedekind, Hecke or automorphic
  L-functions, and nothing here does either.
- It does **not** prove the sign from the primes alone. Every case above takes the sign from the zeros being on the line
  (easy direction, with the external proofs) or from Weil's theorem (curves). The statement `ScaleSign` from the prime side,
  positivity of Weil's form without using the zeros, is still the open step, and still zero slack. A known route for zeta
  and Dirichlet that uses positivity is not what the external authors did (S3, S5: their route does not use positivity), so
  the project's own claim structure (the paper) is unaffected and unaided.
- It does **not** simplify the open step over the integers. Over a finite field Weil's theorem supplies the sign through a
  self-product and a Hodge-index positivity; over `Z` no tick and no self-product exist yet
  (`OPEN-STEPS-DMP.md` 2(c)).
- It does **not** verify the external proofs. They are hypotheses with an audit list; the project has not read the proof.
- The infinite Dirichlet case needs the explicit formula and a convergence statement (audit items 10 and 11) before
  "ScaleSign for `L(chi, .)`" is a theorem rather than a conditional one.
