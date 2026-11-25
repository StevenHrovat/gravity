# Pre-registration: r3-monotone, one exact count (2026-11-21, written before running)

Scope: one exact finite computation, no simulation. CPU only, `CUDA_VISIBLE_DEVICES=-1`, one process, expected run time seconds
(hard cap 15 minutes). Script `frozen_twist.py`, output `frozen_twist.json`.

## What is computed

For a finite group G with a central element c of order 2 and the 't Hooft twist c in the 12-plane of an l^4 periodic lattice
(one twisted 12-plaquette per (x3, x4)), the beta -> infinity limit of the twist ratio is (NOTE.md, section 5, proved on paper there):

  lim_{beta -> inf} Z_tw / Z = |Hom_tw| / |Hom|,   F_inf := log(|Hom| / |Hom_tw|),   the same for every l >= 1,

with |Hom| = number of pairwise commuting 4-tuples (g1, g2, g3, g4) in G and |Hom_tw| = number of 4-tuples with
g1 g2 g1^-1 g2^-1 = c and all other pairs commuting. Groups: the cyclic groups Z2 and Z4 (abelian controls, c = -1), and the
finite subgroups of SU(2) that contain -1: Q8 (order 8), binary tetrahedral 2T (24), binary octahedral 2O (48), binary icosahedral
2I (120), c = -1. Elements are generated as unit quaternions (closure of explicit generators), counted by brute force over pairs and
centralisers.

## Checks (the run is void and repaired if any fails)

1. Group orders come out 8, 24, 48, 120; each set is closed under multiplication and contains -1.
2. Abelian controls: |Hom_tw| = 0 for Z2 and Z4 (twist never flat; F_inf = infinity).
3. Commuting pairs: |Hom(Z^2, G)| = |G| * k(G) (k = number of conjugacy classes; Q8: 8 * 5 = 40, 2I: 120 * 9 = 1080).
4. Q8 by hand: [g1, g2] = -1 exactly for g1, g2 in {+-i, +-j, +-k} with g2 != +-g1: 6 * 4 = 24 pairs; their common centraliser
   is {+-1}, so |Hom_tw(Q8)| = 24 * 4 = 96.

## Prediction (stated before running)

- Every non-abelian group in the list has |Hom_tw| > 0, so F_inf is finite: the twist free energy at beta = infinity is an l-independent
  O(1) number (frozen coupling). Expected size: between 1 and 6 (it is a log of a ratio of counts of order |G|^2-ish).
- What this is used for (NOTE.md, section 5): the finite-subgroup unit test. These groups are non-abelian, their centre element is a
  commutator (twist eaters exist), and yet their large-beta twist free energy neither grows (unlike Z2) nor decreases with l. An argument
  that would prove "F decreases with l" from properties shared with these groups is wrong.
