# Pre-registration: how far does the exact single-link Dobrushin condition reach? (2026-11-21, before computing)

## The quantity

Four-dimensional Wilson lattice gauge theory, standard normalisation: weight exp(β Σ_p ½ Re Tr U_p) for SU(2), exp(β Σ_p cos θ_p) for
U(1). Treat each link as a spin with Haar a priori measure (no gauge fixing), as `lgt` does. A link e sits in 2(d−1) = 6 plaquettes;
given everything else, its law has density ∝ exp(β ⟨x, A⟩) on the group (S³ for SU(2) as unit quaternions, S¹ for U(1)), where A is
the sum of the six staples, each a group element. Two distinct links share at most one plaquette, so a link has exactly 6(d−1) = 18
neighbours, and changing one neighbour f changes exactly one staple, to an arbitrary group element.

Dobrushin's influence of f on e is C(β) = sup TV(law of e before, law of e after), the supremum over the other five staples (their sum
W is any vector of length at most 5) and the old and new value of the changed staple (unit vectors v, v'). The Dobrushin parameter is
α(β) = 18 · C(β); α < 1 gives a unique Gibbs measure with exponentially decaying correlations, uniformly in the volume (the mechanism
of `lgt`'s headline theorem). **β\*** is where α(β\*) = 1.

`lgt` bounds C by 1 − e^(−4nβ_lgt) (n = 2, β_lgt = β/2 for SU(2); β_lgt = β for U(1)) and counts 8(d−1) = 24 neighbours: β\* = 1/96
≈ 0.0104 in both groups. Shen–Zhu–Zhu (arXiv:2204.12737, Bakry–Émery, not Dobrushin): β < 1/(16(d−1)) in their normalisation N·β·Re
Tr, which is β < 1/12 ≈ 0.0833 in the standard one for SU(2).

## Predictions written before computing

- Small-β linearisation: C(β) ≈ β · E|y₁| with y uniform on the unit disk (the projection of uniform S³ to a plane) = 4β/(3π) for
  SU(2), and β · E|cos θ| = 2β/π for U(1). So β\* ≈ π/24 ≈ 0.131 (SU(2)) and π/36 ≈ 0.087 (U(1)). The supremum over the other staples
  can only raise C, so the exact β\* is at most these values.
- Expected outcome: SU(2) β\* between 0.09 and 0.131.

## Criteria

- **Sanity:** at β = 10⁻³ the computed C agrees with the linearisation within 1 %; the disk-projection shortcut agrees with a direct
  Monte Carlo on S³ within its error; the U(1) result passes the photon test trivially (β\* < 1.0111, the U(1) phase transition).
- **Worth step 2 (rigorous bound, Lean):** SU(2) β\* > 1/12 ≈ 0.0833, i.e. the exact single-link Dobrushin condition beats the best
  proven threshold we know of (to be confirmed by a literature check before any claim).
- **Not worth step 2 at single-link level:** β\* ≤ 0.0833; go straight to blocks (Dobrushin–Shlosman).

Claim level: a floating-point computation of a supremum, not a theorem, until step 2 makes it rigorous.

## Shot 2 (added before running it, at the owner's request for quick shots across the whole range)

The block route needs boxes that forget their boundary. `wall.py` freezes all links on one time slice, cold (identity) or hot
(random), and measures the mean spatial plaquette at distance r from that wall; Δ(r) = cold − hot is the wall's influence.

- Runs: SU(2) at β = 0.5, 1.0, 1.5, 2.0, 2.3, 2.5 on 8³ × 16; U(1) at β = 0.6, 0.9 (confined) and 1.1, 1.5 (Coulomb phase) on 6³ × 16
  and 10³ × 16. 300 thermalisation sweeps, 600 measurements, cold and hot each.
- Decay length ℓ(β): from an exponential fit of Δ(r) over the distances where Δ is above 3 errors.
- **Merit for blocks:** SU(2) ℓ stays below about 2 lattice units for every β up to 2.5 (so boxes of about ten sites could forget their
  boundary). **Hopeless on a laptop:** ℓ above about 4 at β = 2.3.
- **Photon test:** in U(1)'s Coulomb phase the decay must be set by the box (ℓ grows with L, the photon's lowest energy being 2π/L),
  in the confined phase it must not depend on L. If U(1) at β = 1.5 looks like SU(2) at the same L independent of L, the probe cannot
  tell the phases apart and says nothing about merit.
- Caveat fixed in advance: one pair of boundary conditions is a lower bound on the worst case, not the supremum the criterion needs.
