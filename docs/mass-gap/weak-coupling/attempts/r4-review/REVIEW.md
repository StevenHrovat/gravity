# Adversarial review of round 4 and the proof blueprint (2026-11-22)

Independent reviewer (model Fable, approved by the owner as part of the phase-readiness plan), read-only, Lean first and notes after.
The coordinating session checked findings 1 and 3 against the code before recording them (`sector_partition_conserved` and
`act_conserved_per_layer` take any measurable map and any two measures; `twist_centre_transform` is proved by `ring`). The coordinating
session had verified round 4 by build and axioms only and passed the headline statements on without checking their content; that slip is
recorded here.

All eight R4 modules build, no `sorry`, standard axioms; no counterexample to any Lean theorem. Three compiled probes back findings 1–3.

## Findings, most severe first

1. **"The act is conserved per layer" is total-mass invariance of an image measure** (breaks the headline). `act_conserved_per_layer`
   and `sector_partition_conserved` (`R4/LayerTransport.lean`) hold for any measurable map and any two unrelated measures: no group,
   lattice, centre or covariance. Probe: blocking onto a one-point space "conserves the act". Never instantiated with `decimate` or a
   Wilson measure; no twisted 4D Wilson measure exists in R4 Lean. The real content (the image of the twisted ensemble is the twist of
   one local coarse action) is open (`r4-layer/NOTE.md`). `actNumber` (a free-energy ratio) is not linked to `fluxEnergy`. Fix: rename
   (`partition_map_invariant`), call it definitional.
2. **The SU(2) "flux sector" theorems are not 't Hooft's flux sectors.** No Gauss law in Lean (`Q` arbitrary, instantiated as `True`).
   With `Q = True` a single-link state is in the "flux sector" (a static charge pair one spacing apart), so the "flux energy" is bounded
   by the one-link static potential, for every group and phase. Fix: define gauge-invariant states, prove the sector hypotheses for
   them, restate.
3. **"'t Hooft duality, exact" is the definition of a two-point Fourier transform** (proof `ring`; needs no property of the kernel).
   The temporal twist is conjugate to electric flux; calling it the magnetic free energy needs the lattice rotation on a symmetric box,
   not in Lean. The "self-dual point" is one number written two ways.
4. **The blocking with Lean reflection positivity cannot be the route's blocking.** `decimated_wilson_rp_SU2` is real but one step; and
   decimation at fixed physical L₁ makes coarse links thin Wilson lines whose continuum limit is product Haar (pure noise; round-3
   finding 2 made concrete). Averaging blockings avoid this; their positivity is paper or open. Missing piece: one blocking that is
   centre-covariant, reflection-positive at every level, and has a non-trivial limit.
5. `fluxEnergy_nonneg` and `flux_correlator_decay` carry no dynamical content (Perron–Frobenius ordering; decay empty while E_e = 0 is
   allowed; junk value 0 when the flux eigenvalue vanishes; holds for negative β too).
6. `layer_rp` does not iterate as stated (needs product form; the output is a mixture). `straddle_breaks_rp` is a correct toy.
7. **ROUND-4 overclaimed:** "exact, two-sided layer structure on the real lattice theory" (see 1–3); "−1 is a commutator" is necessary,
   not separating (Q8, 2T, 2O, 2I have it and fail W); the photon and finite-group results are paper proofs; the photon result is for the
   Villain/free form.
8. **Unit tests:** no theorem is violated by any test group, because the theorems are group-blind. The order-12 binary dihedral claim was
   verified independently. Deconfined Z₂ has a gap and no flux floor, so "floor" and "gap" differ and P4.6 is not on the critical path.
   W's clause ℓ ≥ 2 is exactly marginal in the dilute semiclassical regime; use the summed form.
9. **The act-number pre-registration** can give a false or powerless verdict: a too-low growth threshold against the photon band;
   tunnelling at small L (too few sweeps; a frozen cold chain gives E ≈ 0 and inflates the growth); controls that pass on failure;
   plateau bias at large L; low power (the qualitative outcome is known). Fixes handed to attempt 1 before any data.

## Corrections to the blueprint (applied in `../../PROOF-BLUEPRINT.md`)

The route is two routes: **Route A** (P2 + P3 + P4.1: D′ at L₁ gives decay of block observables; never uses flux sectors) and **Route B**
(flux sector, act number, W: ends at flux confinement; reaches the vacuum gap only through the open P5.1). Five statuses overstated
(P1.3–P1.6, P2.3, P3.4/P6.1, P4.3, P4.6, P4.7, P6.3, P6.5); missing pieces: all compact simple G, local fields as distributions with the
OS regularity bound, the gap for the whole field algebra and vacuum uniqueness, a good blocking (finding 4), Gauss law and
`Z_Wilson = tr(P_G Tⁿ)` and strict E_e > 0 in Lean, D′ uniform in the spacing with the order of limits, translation invariance,
short-distance agreement with perturbation theory, two assemblies.

## The reviewer's verdict

Round 4 formalised correct but elementary facts: for the SU(2) temporal-gauge Wilson kernel, a centre flip of one row of links is a
symmetry and the odd-parity sector's norm is at most the even sector's; decimation by 2 commutes with gauge transformations, that flip and
time reflection, so decimated observables inherit reflection positivity for one step; the rest are algebraic identities and labelled
toys. No statement separates SU(2) from U(1) or Z₂, none bears on the vacuum gap, and the one blocking with machine-checked positivity
degenerates to noise at fixed scale. The blueprint is a useful inventory but joined two separate routes, overstated statuses, and omitted
field construction, the infinite-volume limit and the all-groups scope. The phase should start from Route A's open hypothesis D′, or from
an honest "Route B targets confinement".
