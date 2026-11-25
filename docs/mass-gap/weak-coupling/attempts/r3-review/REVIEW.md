# Adversarial review of round 3 (2026-11-21)

An independent reviewer (model Fable, approved by the owner for this review) was given the Lean code and the notes, asked to form its
own view from the Lean before reading the notes, and to try to break the round-3 claim. Read-only: it edited nothing. The coordinating
session checked findings 1 and 2 against the code before recording them (`gap_of_stepScaling` still takes `hctrl` and `LimitGDS`; no
round-3 file imports both `WpNoise` and `Robust`; `noise_subseq` and `reach_of_noFixedPoint` are used nowhere else).

**Build check by the reviewer:** all eight round-3 modules build, no `sorry`, no `native_decide`; `#print axioms` on 13 headline theorems
shows only propext, Classical.choice, Quot.sound. No counterexample to any Lean theorem was found. The problems are in what
`ROUND-3.md` said the theorems say.

## Findings, most severe first

1. **"No fixed point" is not a second exact form of the open piece** (breaks that sentence of `ROUND-3.md`). `reach_of_noFixedPoint` only
   says a real sequence drops below a target in boundedly many steps. The theorem that would use it, `gap_of_stepScaling`
   (`formal/Attempts/R2/StepScalingH1.lean`), still needs the control hypothesis (its own header: stronger than H1) and `LimitGDS`. No
   fixed point supplies only the tuning step; it neither implies D′ nor is implied by it, and it presupposes a continuum step-scaling
   function (existence and uniqueness). `grid_certificate` is not a finite certificate in practice: each grid value is a continuum-limit
   quantity.
2. **There is no machine-checked reduction to Yang–Mills; there are three unconnected Lean pieces.** No file imports both `WpNoise` and
   `Robust`. `continuum_decay` takes full-sequence convergence to a Gibbs measure as a hypothesis; `noise_subseq` gives a volume-dependent
   subsequence of log-integrals with no measure attached. The glue (limit density as a Gibbs measure, convergence, the subsequence argument
   across volumes) is on paper; the reviewer checked it and believes it correct in the order mesh, then volume, then observable. The gap
   theorems contain no SU(2), no 4D lattice, no Wilson measure and no line of constant physics: they are about abstract Gibbs measures on
   finite product spaces. Probe (compiled): the zero-potential theory satisfies the hypotheses with γ = 0, so a mistuned limit that is
   pure noise satisfies them too and gets a "gap".
3. **Crossover-D′ is strictly stronger than the mass gap, and its content lies only in volume-uniformity.** D′ is a worst-case
   single-site Dobrushin condition, of complete-analyticity type; a gap does not imply it (2D Ising just above T_c has a gap and fails
   single-site Dobrushin). In any fixed volume D′ holds for every theory, the photon included, once the noise is strong enough; it bites
   only through one γ, one λ and one noise kernel across all volumes. Consistency bound: uniform D′ over all tori is false for
   L₁ < 1/T_c (about 1.4/√σ for SU(2)), because a torus one block thick is deconfined. The Lean needs a potential decomposition with
   small pair oscillations, not just "one-site conditional laws".
4. **Further open pieces behind "exactly one":** existence, non-triviality and identification of the limit rest on the OpenAI
   construction (cited at reading level) and on a tuning in no round-3 hypothesis; decay is proved only for bounded functions of the
   noise-smeared L₁ block variables (general local observables are a stated gap in attempt 1's note); reflection positivity of the blocked
   limit is proved only for one-sided coarse variables on finite sets; Osterwalder–Schrader axioms, rotation invariance and the
   infinite-volume limit are not addressed; Lemma T and the per-volume gap theorem are on paper. `ROUND-3.md` was also stale: weighted
   Theorem A (`theoremA_w`) is formalised.
5. **Statement fidelity of the individual theorems: mostly fine.** `gap_of_localFactorsW`, `levelFlat_of_local`, `specDist_site`,
   `theoremA_w` state what the notes say. In `continuum_decay` only the limit's bound is volume-uniform. `dist` should be required to be a
   metric (harmless as is). `su2_twist_eater` is real SU(2); twist eaters also exist for the finite subgroups (the note says so). The
   `Dmp*` files are openly toy or logical lemmas.
6. **Leg C can produce a false "inside".** Deterministic block variable versus the noisy step the chain needs; a truncated fit can only
   lower the D′ sum (bias towards false positives); coarse 4⁴ and 3⁴ lattices cannot test volume-uniformity; at L√σ ≈ 4 the expected
   fundamental coupling is below statistical error; the photon gate is weak; no non-abelian negative control. Proposed fixes: rename the
   verdicts, add a signal check (coarse Wilson loops must reproduce σ), a quantitative photon gate, deconfined SU(2) and frozen binary
   icosahedral controls, D′ against coarse volume. (Handed to attempt 4 to amend the pre-registration before any GPU data.)
7. **Unit tests** pass, but only because every gap theorem is conditional on D′; the zero-potential probe shows the hypotheses do not
   pin down Yang–Mills.

## The reviewer's verdict (the claim level that survives expert review)

"We formalised Dobrushin's uniqueness theorem with exponential weights for finite Gibbs systems, its openness under local perturbation,
and a compactness lemma for noisy blockings. On paper, these give: if every subsequential limit of a noisily blocked lattice gauge theory
at scale L₁ satisfies a volume-uniform worst-case Dobrushin condition, then covariances of L₁ block observables of those limits decay
exponentially, uniformly in the volume." A correct, modest conditional statement; its hypothesis is at least as strong as the mass gap and
is not known to be true or implied by a gap. Existence and identification of the limit, physical observables, positivity and symmetry,
and the Lean assembly are also open, and "no fixed point" is not an equivalent form of the remaining hypothesis.
