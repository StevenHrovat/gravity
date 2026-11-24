# Attempt round 1: summary (2026-11-21)

Five independent proof attempts on the open hypothesis of the reduction (`UniformGDS`: a box of fixed physical size forgets its boundary by
the same margin at every grid fineness), run in parallel under `RULES.md`, started before any SU(2) result of Leg B. Notes in each
folder; Lean in `../../formal/Attempts/*`, all verified by the coordinating session (builds, no `sorry`, standard axioms only).

## Verdict

**No attempt proves the hypothesis or a layer inequality.** All five end in precise, structural negatives, and they agree on one
obstruction. That agreement is the main result of the round.

## The common obstruction

At weak coupling the gauge field is locally flat: every non-abelian effect costs about g² per link and becomes of order one only after
about 1/g² lattice steps, which shrinks to zero in physical units (route (d), checked numerically: the covariant-Laplacian gap is
1.00·g² from β = 4 to 64). At that level SU(2) behaves like three photons, and for the free (Gaussian) field the boundary influence of a
box is at least 1 at every box size (route (c), the sum rule, exact). So:
- the contraction can only switch on at the **physical** scale where the running coupling is of order one, through fluxes and twists that
  wrap the group across the box (routes (c), (a));
- a layer inequality gives a fixed physical scale only if its cost per layer equals the **exact** asymptotic-freedom coefficient
  (route (d), Lean: `scale_bounded`, `scale_unbounded`); methods that lose constants cannot work, which is why soft arguments have
  always failed here;
- reflection positivity alone moves bounds only inward, compares within one measure, and holds for U(1) (route (b), Lean:
  `rp_no_outward`);
- worst-case boundaries (what the hypothesis needs) cannot be reached from torus estimates by chessboard bounds without a boundary cost
  e^{β·(box surface)} (lead route);
- a centre twist sees only central jumps of a boundary link, while the influence is dominated by small continuous rotations (route (a),
  Lean: the split lemma).

## What the round adds

**Formal results (Lean, verified):** the recursion theorem `uniformGDS_of_recursion` (a contracting recursion above an entrance scale gives
`UniformGDS`; the entrance stays a physical-scale hypothesis), the persistence lemma, `rp_no_outward`, `one_distance_ratio`,
`conj_trivial_iff_mem_center` (adjoint-only observables ignore exactly the centre), the influence split into twist and coset parts, the
layer lemma, the deficit identity and the sharp-coefficient lemma, the blocking growth of the admissibility bound, the free-field sum
rule, soft-admissible Z₂ = Wilson Z₂ at shifted β, admissible U(1) without monopoles.

**A correctness fix, found independently by routes (a) and (c):** the Lean `UniformGDS` is stated with the oscillation (H) form of the
influence, while the proof note's open problem is the Lipschitz (W) form; the H form may be false at fixed physical size even when the W
form holds. A W-form restatement of the chain is in progress (`OneScale/CorollaryBW.lean`).

**The structure of the problem, as the round sees it (conjecture C1, route (b), and the owner's readings):**

| ingredient | mathematics | the owner's reading | what it gives |
|---|---|---|---|
| adjoint part | how links act on gluons (commutators) | self-charge: existence, prescribed path | the gap |
| centre part | the ±1 twist (MG3) | the root frame, the root swap at the existence boundary | confinement |

U(1) has neither (payload). Z₂ has only the centre: in the owner's words a **naked duality, which can only exist at G0**; it has a gap
for the same reason DMP has its own (it counts, two values: README §2) and does not confine (there is no self-charged content to
anchor); no standalone Z₂ gauge field is known in nature, it appears only as the centre inside SU(N). SU(N) has both.

## Cheap next experiments proposed by the attempts (CPU, minutes each; not yet run)

1. **Route (d):** define a coupling from the box influence at large β in small boxes; does it run by −0.2575 per doubling for SU(2) and
   by 0 for U(1)? If yes, route (d) merges with the lead route and what remains is the one-scale certificate.
2. **Route (c):** 2D compact U(1) (exactly solvable given the boundary): does the influence coefficient drop below 1 at box size of
   order the confinement length? That would calibrate L₀.
3. **Route (a):** central-jump coupled pairs (y → −y) for SU(2) at β = 2.3, ℓ = 4, 6, 8, against Leg B's continuous-rotation estimate.
4. **Lead route:** construct a reflection-positive coupling of two SU(2) copies that agrees on a block with positive probability
   (mathematics, no numerics); with it, torus decay would follow without the worst-case hypothesis.
