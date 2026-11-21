# Attempt round 4: summary (2026-11-22)

Four attempts under `RULES.md` (round-4 additions: claim discipline after the round-3 review; the deconfinement test), built on the
round-4 scout `../round4-prep/DMP-SCOUT.md`, which ranked the owner's **act identity** first (existence × extent = one quantum; in
Yang–Mills the **act number** z(L) = E_e(L)·L of a twisted box, E_e the energy of one unit of centre flux). Lean in
`../../formal/Attempts/R4/`, all verified by the coordinating session (builds; no `sorry`; axioms within propext, Classical.choice,
Quot.sound; check scripts and selftests re-run where named in the commits).

| attempt | folder | commit | Lean | one line |
|---|---|---|---|---|
| 1, measure the act number | `r4-actnumber/` | 4161e56 | none | z(L) pre-registered with photon, Z₂, 2I and symmetry controls; GPU run queued after Leg C |
| 2, the act identity per layer | `r4-layer/` | 8095fbf | `LayerSector`, `LayerKernel`, `LayerTwisted`, `LayerTransport`, `LayerDecimation`; 122 declarations, SU(2) in the hypotheses | the flux sector of the Wilson transfer kernel; **the act is conserved per layer** (`act_conserved_per_layer`); T38 for decimation |
| 3, Conjecture W | `r4-conjw/` | 570c4fa | `ConjW`, 10 (toy) | W stated precisely; photon marginality and finite-group failure proved; where b₀ enters; three named blocking steps |
| 4, the owner's minting conservation | `r4-minting/` | 0a15c2f | `MintingDmp`, `MintingScale`, 34 (toy) | minted quantum and tick carried to every layer by perfect duality; Λ as the act's conservation in units; a selection principle against fixed points |

## Verdict

Round 4 did not aim at the gap and does not claim it. It built the **exact, two-sided layer structure** the earlier rounds lacked, on the
real lattice theory: the flux sector of the SU(2) Wilson transfer matrix, its exact conservation under a gauge-covariant,
centre-respecting, reflection-respecting blocking, 't Hooft's duality as an exact identity, and reflection positivity of every decimated
layer. It located, again exactly, the one-sided step every route meets: **comparing the blocked measure with the original on the same
box** (Conjecture W's widening ratio). And it sharpened the separating property: not "non-abelian" but **"−1 is a commutator of G"**.

## What each attempt established

**2. The act identity per layer (real SU(2), Lean).** The Wilson transfer kernel in temporal gauge, 't Hooft's centre transformation
(stated as a gauge transformation periodic up to the centre: Gauss-law states labelled by the root), E_e ≥ 0 and the decay of flux
correlators in Euclidean time; the twisted partition function as the centre transform of the flux partition functions; 't Hooft's duality
F_e = dual(F_m) exactly, with the unique self-dual point log(1+√2) ≈ 0.881. The act is conserved per layer: under decimation (each
coarse link the product of two fine links: gauge covariant, centre- and reflection-commuting) the flux-sector partition functions, hence
F_e, F_m and z in each layer's own units, pass through unchanged. T38 in full for decimation: the decimated SU(2) Wilson layer is
reflection positive (`decimated_wilson_rp_SU2`). Stated gaps: the identification of the kernel with the 4D Wilson path integral
(standard, not formalised), strict E_e > 0 in finite volume, centre elements with z² = 1 only.

**3. Conjecture W.** One doubling of the cube is four moves: z(2L)/z(L) = 2·ℓ·w_x·w_y (lengthening ℓ, widenings w). W: ℓ ≥ 2 and each
w ≥ (1+δ)/2 along the line of constant physics. Proved: the free lattice photon has E_n = g²n²L_z/(2L_xL_y) exactly, so z = 2πα is frozen
(the owner's α pointer, exactly); for Z₂ and the finite subgroups every flux change costs at least μ_G·β per cross-section, so z falls. A
pre-registered prediction failed usefully: the order-12 binary dihedral group has no twist eater (−1 is not a commutator). Without
running, z of a cube cannot change (Lean): all growth of z is the scale anomaly. Mechanism (heuristic, standard semiclassics):
half-instanton tunnelling at cost 4π²/g², growth exponent 11/3. Three blocking steps for a proof: (B1) the minimal action on T³×ℝ
(certifiable), (B2) the fluctuation prefactor along the line of constant physics (where b₀ enters; needs constructive renormalisation),
(B3) the order of limits. Banks–Zaks: W is not claimed (fundamental quarks screen the flux; adjoint quarks put zero modes on the
half-instanton).

**4. The minting conservation (the owner's idea; toy Lean).** A root that mints quantum, tick and window, perfect duality (T4: a minted
value changes only by an act both halves sign) and one exact step rule give the act identity, 3s1t and the floor at every layer, derived
rather than assumed; with a one-sided standing a single witness can drop the quantum to zero. Yang–Mills side: the act is conserved
exactly for every theory (no gap by itself); Λ is the act's conservation in units, under assumption (U) (each blocked layer is the
original action at another coupling): "conserved because it is running" (Callan–Symanzik); the tie to G0 is asymptotic freedom (φ⁴₄ and
QED hit a Landau pole). "Something must run" becomes a selection principle: a floor excludes a fixed point (Banks–Zaks excluded by
construction), a selection rule, not a derivation.

**1. The act-number measurement.** z(L) from flux correlators in a twisted SU(2) box (flux parallel to the twist), readings: z against
L√σ, the crossing z = 1 against 1/T_c, the growth margin per doubling, the large end, the collapse test (attempt 4), the inversion box
(attempt 3), the deconfinement anomaly; controls: U(1) photon gate (checks z = 2πα), Z₂ deconfined, frozen 2I, symmetry; optional
four-move addendum for W's ratios (queued). Partly a re-measurement in a new form of Gonzalez-Arroyo and Martinez (1996).

## The owner's readings this round (all in `../PREP.md`)

The act identity as the core; G0 holds all information and existence at once, lossy causality loses information, an existence boundary
is an inversion (made exact as 't Hooft's duality and its self-dual point); the act is what is conserved, and it is conserved because it
runs (Callan–Symanzik); the tie to G0 is reach, inward (asymptotic freedom) and outward (confinement), traded by the sign of b₀; DMP
demands that something runs (no infrared fixed point); the centre is reached through the chain of causality (a commutator is a causal
round trip); internally verifiable messages are Gauss's law, with the non-abelian law counting the field's own charge.

## Unit tests

One more joins the list: **Banks–Zaks** (an argument for the gap must not apply to asymptotically free theories in the conformal
window). Round 4's statements pass all tests (photon, Z₂, finite subgroups, deconfinement, triviality, Banks–Zaks), mostly because they
are exact identities or claim no floor.

## Next: the proof phase (round 5)

The owner: round 5 is a phase aiming at the full proof. Readiness: an adversarial review of round 4, the proof blueprint (every piece,
its status, the complete open list), one assembled Lean theorem with the open pieces as named hypotheses, consolidation of the Lean the
assembly needs, and a reading pack for the hard pieces.
