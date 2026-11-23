# c9b-adjoint: handover (kept current; last update 2026-11-23, end of round 2)

## Where things stand

* **Round 1** (`NOTE.md`, Lean `Adjoint2/Transfer.lean`, N1): the adjoint half `gamma_A` in the potential split; the binding problem is the
  shared propagation `c0 + c1`, not the adjoint source. Its "sup form 2.4 at 2.80" is the **crude** two-point bound (corrected in round 2).
* **Round 2** (`ROUND2.md`, Lean `Adjoint2/CostCoupling.lean`, `Adjoint2/PatternAssembly.lean`, N2):
  * N2 is **void as a pre-registered result** (its own P7 rule; reference-value mistake); all its numbers are diagnostics;
  * sharp sup-form column of the fitted action at 2.80: 1.021 (uniform, still > 1), 0.960 (weighted, post-hoc); W1 0.73 (plaquettes) /
    0.964 (with the fitted rectangle, c4d);
  * W1 + one smoothing step: Lean (generic theorem down to the `IsInfluenceBoundOn` slot; colour-class composition is paper); for the
    plaquette fit `kappa_Ham <= 12.2`, box side `>= 99` cells; with the rectangle's W1 column about 800 cells (numerical, sketch
    constants; scales like `1/(1 - c_W)`); coarse level only, the two-level (fine) step is still the sketch of `NOTE.md` 1.3;
  * larger `L1`: sharp columns 0.89 / 0.62 / 0.55 at 2.92 / 4.13 / 5.60, but all three fits lack content (noise-limit suspects);
  * pattern-conditioned assembly: `FineOneBoxPat` (named, open) ⇒ `FineDecayInv` ⇒ full assembly, Lean; its content is `DisintBound`
    (pair bounds only for content pairs in a full-measure set); `pair_bound_of_couplingDS` gives such bounds from M1's theorem, but the
    wiring into `DisintBound` (uniform constants over content pairs, content set vs coupling supports) is open;
  * GPU measurement drafted (`PREREG-GPU.md`), **not run, not approved**.

## Next steps (in order)

1. **Owner decision:** the GPU measurement (`PREREG-GPU.md`): first a CPU pilot (needs its own short pre-registration and the code of
   section 7 there), then one 30-minute GPU timing job (owner's OK), then the projection and Stage A (owner's OK).
2. Lean, reachable: iterate `cost_bind_le` over 8 colour classes as a theorem (the `K_s` arithmetic); the coarse-to-fine two-level coupling
   as a statement (`kappa <= (1 + C_UV) kappa_IR + b_UV`) on `CouplingSpec` data.
3. Paper, open: composite-box coverage and Lemma C at the cell scale (`ROUND2.md` 2.3 (a)-(d)); the rectangle tail in the sup form
   (sharp analogue of c4d's ext_R +0.23).
4. c8a maintainers: the hybrid label swap (`NOTE.md` 1.1) and the withdrawn `0.03/l` estimate are still to be fixed in c8a's prose.

## Build and checks

* Lean: `build-ir.sh <Module>` (WSL distro ym-replay, user ym; creates `~/formal-ir` from `~/formal/.lake` if missing); axioms: `axioms-ir.sh`.
  `~/formal-ir` was **deleted** at the end of round 2; the first build of the next round recreates it (about 5 minutes).
* Numerics: `py n2_sharp.py`, `py n2_posthoc.py` (Windows Python, numpy).
* Before finishing a round: `LC_ALL=C.UTF-8 bash tools/scrub-scan.sh > /tmp/scrub.txt; rc=$?` must give `rc = 0`.

## Do not touch

`formal/ProofPhase/Crossover/`, `proof-phase/c9a-crossover/` (crossover session), `formal/ProofPhase/M1/` (M1 session). New Lean only under
`formal/ProofPhase/Adjoint2/`. Do not commit, branch, push or stash: the coordinator commits.
