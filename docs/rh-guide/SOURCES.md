# Sources for the RH guide

Read 2026-11-23. Every claim in `GUIDE.md` points to one of the entries below by its tag (S1, S2, ...). Nothing was
downloaded except the author's 4-page note (read as a PDF through a web fetch); the Lean library was read file by file
on the web (read-only), never cloned, built or run.

## Primary sources

**S1. Joint statement of the Lean and Mathlib communities** (2026-11-21).
URL: https://leanprover-community.github.io/blog/posts/riemann-hypothesis/
Taken: the release date (2026-11-20) and size (about 17 million lines); the certification that the Lean statement is
Mathlib's own `RiemannHypothesis`; that the library compiles; that the proved theorem was matched to a Mathlib-only
statement file by two independent comparison tools; that several independent kernels accepted the exported proof, two of
them (con-leche, con-ron) with a formal proof of their own soundness relative to set theory. The statement itself says
nothing about the mathematics of the proof; it closes by looking forward to the community explaining its new ideas.

**S2. Verification page by Andrew Sutherland (MIT)** (updated 2026-11-22).
URL: https://math.mit.edu/~drew/grh/
Taken: the exact five theorems of `Main.lean` and their statements; the scope note that "GRH" here means Dirichlet
L-functions only (all moduli, all characters; not Dedekind, Hecke or general automorphic L-functions); 175,187 modules;
only the three standard axioms; the independent kernels (nanoda, con-leche, con-ron, lean4lean, Lean's own kernel per
module); the byte-identical sandboxed rebuild; the arithmetic corollaries `robin_inequality` and `lagarias_inequality`
obtained by combining the proof with an independent formalization of Robin's and Lagarias's criteria; the caveat that a
passing check depends on the kernels and on Mathlib's definitions.

**S3. The author's note, Levent Alpoege, "remark.pdf"** (2026-11-20, 4 pages).
URL: https://alpo.ge/remark.pdf
Taken: that the method resolves GRH and is expected to extend to the Extended RH given more time; that the argument is a
descendant of Stepanov's method for RH over function fields, where multiplicity is hard to find over the integers and
is replaced by chaining theta lifts; that the chain length for a von Mangoldt sum of length X is sqrt(X); the 20-entry
discovery timeline (Stepanov determinant; a definite sign in a function-field identity; switching to the weighted von
Mangoldt sum; Guinand-Weil credited with the sign; iterated theta lifts between totally definite unitary groups winning
multiplicity m; Chowla-Selberg, Weyl and Siegel mass; seesaw and Rallis; Bost slope inequality; a relative trace
formula; a weakening of Vandiver; an Iwasawa tower; a cost computation that would stop at 2/3; GRH on 2026-11-16); the
author's remark that a readable write-up is still to come and that the argument should simplify; footnote 2, where the
generated "book" begins with the trichotomy of the reals at 1/2. The note does not give theorem names.

**S4. The Lean library, community mirror** `leanprover-community/riemann-hypothesis` (GitHub; branch `main`, and
branch `original` = the unmodified release).
URL: https://github.com/leanprover-community/riemann-hypothesis
Read directly (via the GitHub API, read-only):
- `README.md`: purpose of the mirror; the five theorems; the `original` branch.
- `src/Main.lean` (main and original): the five theorems and how they are assembled.
- `src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean`: `Claim.strip`, `Claim.zeta`,
  `Claim.prim_reflect`, `Claim.prim_zero` (the mirror step).
- `src/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean`: `Claim.HalfPlane`, `Claim.Strip`,
  `Claim.Zeta`, `Claim.factor_ne_zero`.
- `src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean`: `UpperTheory.EveryCharacter`.
- `src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`: `UpperTheory.FinalTheorems.everyCharacter`.
- `src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean`
  (5,950 lines): `OpenLiteratureStatements`, the `..._of_literature` theorems, `every_character_of_literature_of_vWin`.
- `src/Development/AutomorphicArithmetic/CharacterBoxes/RiemannHypothesisOfEveryCharacter.lean` (branch `original`):
  `UpperTheory.riemannHypothesis_of_everyCharacter`, which uses `completedRiemannZeta_one_sub`.
- `src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/`: `explicit_formula_dirichlet_zeros_right_half`,
  `explicit_formula_and_window_count`, `logFree_zeroDensity_dirichlet_one_modulus` (statements only).
- Top-level and second-level folder names of `src/`, and a list of about 77,000 file paths (the GitHub tree listing is
  truncated for the largest folder, so path searches are incomplete). Used only to check which classical names occur
  as file names (for example: no file name contains "Stepanov", "HilbertPolya", "Montgomery" or "DeBranges"; many
  contain "Weil", "Bessel", "Seesaw", "ThetaLift", "ExplicitFormula", "ZeroFree").

## Secondary sources (community readings of the code)

These are careful readings of the Lean source by others. Their names of declarations were checked by their authors
against the exported list of declarations the final theorems use; I re-read only the files listed under S4.

**S5. "An unofficial reader's map of the proof strategy"**, issue #5 in the mirror repository (opened 2026-11-21,
revised since).
URL: https://github.com/leanprover-community/riemann-hypothesis/issues/5
Taken: the call path from `RiemannHypothesis` down to `zeroFreeAll_of_topG`; the windowed Landau endgame
(`zeroFree_of_rpow_window`, `landau_window`, `poleData`, `level_of_tiedWin`); the weighted von Mangoldt sum `Gz`; the
families of Hermitian lattices indexed by binary words; the slope inequality `Frame_at` / `FrameF` (read as a
Bost-type arithmetic Siegel lemma); the prime side `ASK` (Legendre's formula, Chebyshev's device) and the archimedean
side `MAIN` via the Chowla-Selberg formula (`mean_log_period`, `meanPeriod`); the pointwise bound
`each_unit_bound_statement`; near-orthogonality `LinkS` and its three pillars (a representation-theoretic vanishing,
Bessel multiplicity one, the Siegel-Weil formula); the arithmetic input `VWin` and `Row0b`; that the
`OpenLiteratureStatements` package is filled with internal proofs and the final theorems do not depend on the local
Langlands correspondence; that auxiliary moduli are chosen by a zero-density argument (`ZD.zero_density_box`).
Tags in the issue: [code] (read from the source) and [reading] (interpretation). I keep that distinction.

**S6. Ishaan Dixit, "The Riemann Hypothesis via a chain of theta lifts: a human-readable account of the Lean proof"**
(November 2026, 27 pp.).
URL: https://ishaan2006.github.io/rh-lean-reproduction/
Taken: the one-paragraph idea; the six steps (windowed Landau; Fourier isolation with auxiliary primes q = 3 mod 8 and
d = 7 mod 16; the size bound; the divisibility layer; near-orthogonality; the Tate-Shafarevich window); the balance
"error relative to the main term is about x/m + m for a chain of m lifts, smallest at m about sqrt(x)"; the parameter
table (m about x^(1/2 - eps/16), chosen by `exists_even_between`); the signature walk of the lifts from (k-1, m) to the
definite (k+m-1, 0); that positive Dirichlet coefficients are what makes a one-sided bound enough
(`Level.cyc`); that the auxiliary L-functions are not proved to satisfy GRH but chosen outside a few bad moduli;
`height_chain_atR` (submultiplicativity along the chain); the reconstruction of the author's 2/3 barrier
(charging each lift for the chain below it gives x/m + m^2, optimum x^(2/3)); Ferrero-Washington, Poitou-Tate and
Bloch-Kato inputs, all proved in Lean. Dixit's labels: Exact, Verified, Reading, Ours.

**S7. Xena project blog, "...and the proof is checked in Lean"** (2026-11-12, posted as "xenaproject").
URL: https://xenaproject.wordpress.com/2026/11/12/and-the-proof-is-checked-in-lean/
Taken: only the framing that S1 relies on (the four questions to ask of an AI-generated Lean proof, the first being
whether the Lean statement matches the informal one). Nothing about RH.

## In the owner's repository

**S8. `docs/mass-gap/weak-coupling/PREP.md`** (this repository), entries "24/a^4 and -1/12", "zeta(-1) = -1/12, binary
existence and the real numbers", "The reals are binary in the glueball/WHK sense", and the earlier binary-existence and
WHK entries. Taken: the owner's readings mapped in the DMP section of the guide, and the coordinator's earlier readings
(functional equation as a mirror about Re s = 1/2; the completed xi(s) = xi(1 - s); the reals as Dedekind cuts).

## Classical background (no URL; standard references)

**S9.** Standard facts used for the "classical" marks: Riemann's functional equation and the completed zeta function;
the explicit formula (Riemann-von Mangoldt, Guinand-Weil); RH equivalent to psi(x) = x + O(x^(1/2 + eps)); Landau's
theorem on Dirichlet series with non-negative coefficients (Pringsheim-Landau: the first singularity of the Laplace
transform of a positive measure sits on the real axis); Weil's positivity criterion; the Hilbert-Polya idea;
Montgomery's pair correlation and the GUE comparison; Li's criterion; the Lindeloef hypothesis as a consequence of RH;
Robin's and Lagarias's criteria; Stepanov's elementary method for curves over finite fields (an auxiliary polynomial
vanishing to order m at all rational points, optimal m about sqrt(q)); zero-density estimates; the Osterwalder-Schrader
reconstruction (reflection positivity gives a Hilbert space and a positive Hamiltonian). Standard texts: Iwaniec-Kowalski
"Analytic Number Theory"; Davenport "Multiplicative Number Theory"; Bombieri's Clay problem description of RH.

## Not accessed

- The Lean Zulip discussion (needs a login to read in full); not attempted.
- Manvir Jaswal's map (Zenodo, https://doi.org/10.5281/zenodo.24410057), Bartosz Naskrecki's guide
  (github nasqret/riemann-rev), Lee Crossley's dashboard and the in-progress written proof by tamnd: linked from S5/S6,
  not read. S6 credits the x/m + m balance independently to Naskrecki's guide and a Zulip post.
- The PDF version of S6 (the HTML version was read; its last third, sections 9 to 11, only in part).
- The comment thread under S5 beyond the issue body (the "section 5, continued" comment on divisibility).
- Any proof files deeper than those listed under S4 (for example the proofs of `landau_window`, `LinkS`, Siegel-Weil).
  Statements about those come from S5/S6 and are marked as such in the guide.
