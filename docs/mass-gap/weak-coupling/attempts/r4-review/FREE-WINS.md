# Missed approaches and uncollected wins (2026-11-22)

The owner asked the round-4 reviewer (Fable, same session, read-only) for a second pass: "look for what promising approaches were missed
along the way, or which free wins were not collected. We might make life more complicated for ourselves than we need to, or we may not
think of a simple idea, because we never looked at it again after establishing it." Estimates are the reviewer's, from reading and power
counting, not proofs. The coordinating session checked finding 2 against `formal/OneScale/CorollaryB.lean`.

## Ranked findings

1. **Flux energy from the 4D reflection-positivity machinery we already have** (free win to promising). `OneScale/TimeShift.lean`
   (`hankel_identity`, `torus_theoremC_hankel`), `TorusRP.lean` (`hankel_cs`, `torus_doubling`, `torus_theoremC`), `Doubling.lean`
   (`prefactor_free`) work on the real 4D Wilson measure for any bounded slab observable. With a spatially summed Polyakov loop
   (centre-odd), log-convexity gives the flux energy as a decay rate ≥ 0 approached from above by effective masses: no temporal gauge,
   no Gauss projection to formalise. Round 4 rebuilt a transfer operator instead; the scout had listed the Hankel doubling as dead only as a
   cross-volume tool. Limit: `PlaqWeight` is one function for all plaquettes; the twisted box needs a plaquette-dependent weight.
2. **The open hypothesis is stated stronger than the chain consumes** (free win). `corollaryB_lattice` consumes only `LevelDecay` (decay
   of limit time-correlations at one physical rate, any prefactor; Corollary C1 removes prefactors). So the gap-strength hypothesis is
   "torus slab covariances decay at one physical rate", true for Z₂ and not hit by the deconfinement objection; D′ is one sufficient
   condition. The round-1 lead note recommended this retargeting; round 3 went back to worst-case D′. Stale header in `CorollaryB.lean`
   (the Hankel identity is formal).
3. **Reflection positivity is needed in the time direction only**, so averaging inside time slices is allowed (promising; the abstract
   lemma is free). The proof of `decimated_wilson_rp` uses only that the blocking commutes with the reflection and reads the closed half;
   spatial smearing removes the perimeter divergence that makes decimation trivial (power counting).
4. **Impose the Dobrushin condition on centre-blind (adjoint, SO(3)) block variables only** (promising). Local gauge-invariant observables
   are centre-neutral; the objection "D′ false below 1/T_c" comes through Chatterjee's centre argument, which has nothing to act on for
   SO(3) variables. U(1) still fails; Z₂ becomes trivial. Needs a one-page check that the projected specification stays quasi-local.
5. **The finite-volume transfer matrix of `PROOF-NOTE.md` §6.7(b)** joined with round 4's slice kernel: a spectral gap of the SU(2)
   transfer operator as a Yang–Mills conclusion, avoiding infinite-volume reconstruction. Needs per-direction sizes and Jentzsch.
6. **One chessboard module would serve three pieces** (Tomboulis–Yaffe and Borgs–Seiler cited from memory only; it would give Route B a
   rigorous Wilson-loop endpoint and a typical-case S′).
7. **Paper pieces with known-correct proofs not in Lean:** Lemma T, the per-volume gap theorem, limit states (Lemma 6.3), `dist` as a
   metric.
8. **The large-box act number is already on disk:** `results/luscher_summary.json` (β = 2.3, L = 6, 8, 10: z ≈ 3.6, 7.8, 12.2 at
   L√σ ≈ 2.1, 2.8, 3.5); caution: the stored fit's Luescher coefficient is in tension with π/3.
9. **The gradient-flow inequality R(t) < 2** (the scout's candidate 2) never taken: "no fixed point" inside one measure; with finding 3 a
   slice-restricted flow keeps positivity.
10. **P2.5 cites the weakest strong-coupling window;** `OneScale/SingleLink.lean` gives one about 1,800 times wider.
11. **Long shots:** Durhuus–Froehlich's uniform condition (never read); bootstrap bounds on a twisted flux correlator; Tomboulis's
    recursion as numbers (thread D of `HANDOVER.md`); round-1 experiment 3 and round-2 step 4 (low value now).

**Rightly closed:** pushing the Dobrushin threshold outward; exact replica agreement; hard admissibility; the Migdal–Kadanoff tree.

**Recommendation:** findings 2, 1, 3 first, in that order (an assembly whose hypothesis is exactly gap-strength, a flux energy on the real
4D measure, a blocking that is both reflection-positive and non-trivial); finding 4 is the one idea that could make the open hypothesis
easier, after a one-page locality check.
