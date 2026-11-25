# Review of Draft 5 (Opus, medium effort)

Reviewer: an Opus subagent at medium effort, run from the coordinating session on 2026-11-25 (a separate session could not be started
while the first author was on Remote Control; he had asked for the draft to go to a reviewer). It worked only in fresh clones of
gravity `draft-5` at `d66ff2a` and IM `full-turn` at `e84f78c`, read the Lean (`Arsenal/FullTurn.lean`, `General/SUNFullTurn.lean`,
the `Essence.lean` additions, `wInt`, `sunZtw`), checked the mathematics by algebra and by script, and ran `tools/reproduce.sh paper D5`
and `tools/reproduce.sh paper` (both OK). It found Draft 4 untouched (`git diff origin/main...draft-5` on its paths empty) and the build
of Draft 4 without an argument unchanged apart from commit ids, dates and one preamble comment.

Verdict: no blocker; 3 major and 11 minor findings; the Lean is sound and states what the text says. The coordinator re-checked the two
mathematical majors (D5-2 by the realification SU(N) in SO(2N); D5-3 by computing log(N - 1) against log(1 + sqrt N)) and the
Mathlib name the reviewer could not locate (`Stirling.tendsto_stirlingSeq_sqrt_pi`, `Mathlib/Analysis/SpecialFunctions/Stirling.lean`).

| id | sev | location | problem | disposition |
|---|---|---|---|---|
| D5-1 | major | introduction, "What is new", full-turn bullet | One [Lean] covered the hypothesis-free form and the [paper] identification of the encoder as N = 2 | Fixed: the hypothesis (positive electric sectors, N >= 3) stated, the encoder identification marked [paper] |
| D5-2 | major | R.7b and its ledger row | The "exact part" switched relation (double cover at N = 2, stabiliser in G2 at N = 3); as a bare inclusion SU(N) lies in SO(N! + 1) for every N, so "N = 4 stops" was wrong | Fixed: two different facts stated as such, neither continuing, the bare inclusion said to say nothing; the selection of {2, 3} marked [reading] |
| D5-3 | major | III.5.4d and its ledger row | The missing steps were incomplete (one-box reduction only for SU(2); the excess act 2C) and the label entropy was not weighed: log(N - 1) per box exceeds log(1 + sqrt N) for N >= 5 (equal at N = 4) | Fixed: five steps listed, the labelling step stated to fail by naive counting unless the rotation fixes the labels; "narrowed" replaced by "reduced to these steps ... not closed" |
| D5-4 | minor | IV.1.5c | The Lean shifts Lambda'/Lambda of the completed zeta; the poles at 0 and 1 give H(0) + H(1) | Fixed |
| D5-5 | minor | III.3.1c | `sunZel_pos_two` needs beta != 0 and even time extent; `sunZtw_neg` even time extent | Fixed |
| D5-6 | minor | ledger III.3.1c | Status left out the classical positivity | Fixed: "Lean + classical" |
| D5-7 | minor | `SUNFullTurn.lean` module doc | "continuum picture" against the text's transfer-matrix picture | Fixed: the lattice transfer matrix, Z_el(e) = Tr(P_e T^T) >= 0 |
| D5-8 | minor | abstract | "the BSD rank" overstated (Lean gives the analytic rank) | Fixed: "the analytic rank"; the abstract stays at 1,920 characters |
| D5-9 | minor | II.2.7 | "any single component of N" garbled | Fixed: "any single coefficient of a sum of N powers" |
| D5-10 | minor | II.2.7 | The mirror image of the halves holds for functions real on the real axis only | Fixed: scoped to such functions, as exp |
| D5-11 | minor | R.7a | The phase balance holds after dz = i z d theta | Fixed |
| D5-12 | minor | R.6a, reference 214 | No birthday baseline for collisions, no memory caveat; FIPS sections not re-read | Fixed: the birthday bound 2^(n/2) and the memory stated; the FIPS sections marked "recalled" (the coordinator's download of the standard was declined, so it was not re-read) |
| D5-13 | minor | R.5c | "U(1) as O1" could read as touching the open assumption | Fixed: one clause, the open assumption O1 unchanged |
| D5-14 | minor | Lean headers, tools, IM docstring | Headers pointing at Draft 4 files; the axiom-script echo; `reproduce.sh` usage and `all`; `claims-check.py` without argument validation; the Stirling remark in a docstring stated as if proved | Fixed: headers point to `docs/paper/D5`, echo and usage updated, `all [DN]`, argument validated, the Stirling remark marked an aside (IM `f7661fc`) |

Also added after the review, at the first author's word (2026-11-25): his reading of the dimension N! + k as "literally defining how
much you can say by how much you have to say", in R.7b as [reading].
