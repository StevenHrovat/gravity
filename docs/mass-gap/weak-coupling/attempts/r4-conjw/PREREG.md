# Pre-registration: r4-conjw small exact checks (written 2026-11-21, before any run)

One script, `groups_check.py`, CPU only, one process, `CUDA_VISIBLE_DEVICES=-1`, expected run time under one minute. Output
`groups_check.json`. Nothing here measures Yang–Mills; these are exact finite computations that check constants and lemmas used in
`NOTE.md` (sections 2 and 3).

Groups: Z2 = {±1}, Z4, Z10 (cyclic subgroups of the U(1) ⊂ SU(2) through −1), Q8, 2T (order 24), 2O (48), 2I (120), the binary
dihedral group Dic3 (order 12). All realised as unit quaternions (generated numerically by closure, elements identified to 1e-9).
Cost of an element: c(g) = 1 − ½ tr g = 1 − Re q (Wilson plaquette cost in units of β, SU(2) normalisation).

## Checks and predictions (pass/fail fixed now)

C1 (group orders): 2, 4, 10, 8, 24, 48, 120, 12. Each contains −1.

C2 (no doubly twisted flat 4-tuple): the number of (x, y, z, t) ∈ G⁴ with [x,y] = −1, [z,t] = −1 and [x,z] = [x,t] = [y,z] = [y,t] = 1
is **0** for every group. (Paper reason: the centraliser in SU(2) of an anticommuting pair is {±1}.)

C3 (per-point frustration patterns): call the six relations xy, zt (twisted: commutator = −1) and xz, xt, yz, yt (commutator = 1).
For a set R of relaxed relations, "satisfiable" means some 4-tuple satisfies all relations outside R. Prediction for the inclusion-
minimal satisfiable relaxed sets:
- non-abelian groups (Q8, 2T, 2O, 2I, Dic3): exactly {xy}, {zt}, {xt, yz}, {xz, yt};
- abelian groups (Z2, Z4, Z10): exactly {xy, zt}.

C4 (vacuum holonomy is central): for every non-abelian group, every element commuting with some anticommuting pair (a, b) is ±1.

C5 (minimal cost of writing −1 as a product), μ_G = min Σ c(g_i) over finite sequences with g_1⋯g_k = −1 (Dijkstra from 1 to −1):
Z2: 2; Z4: 2; Z10: 5(1 − cos(π/5)) = 0.954915; Q8: 2; 2T: 1.5; 2O: 4(1 − cos(π/4)) = 1.171573; 2I: 0.954915;
Dic3 (contains Z6): 3(1 − cos(π/3)) = 1.5. Also report the optimal length k_G (predicted 1, 2, 5, 2, 3, 4, 5, 3; ties allowed: pass if
μ_G matches to 1e-9 and some optimal sequence has the predicted length).

C6 (exact U(1) zero mode, the photon's frozen act number on the lattice): for the free lattice photon with compact zero modes, the
Villain kernel of the z zero mode c ∈ R/(2π/N_z)Z over one time step is K(Δ) = Σ_w exp(−(M/2g²)(Δ + 2πw/N_z)²), M = N_x N_y N_z.
Prediction: its eigenvalue ratio on the Fourier modes e^{i N_z n c} satisfies −log(λ_n/λ_0) = g² n² N_z/(2 N_x N_y) to 1e-10 relative
(computed by direct numerical quadrature on a fine grid, not by the Poisson formula), for (N_x, N_y, N_z, g²) in
{(2,2,2,1), (3,2,5,0.7), (4,4,4,2.5), (8,4,4,1.3), (4,4,8,1.3)} and n = 1, 2. Consequence checked: lengthening ratio 2, widening 1/2.

C7 (arithmetic, recorded only): the self-dual point of 't Hooft's duality F = −log tanh(F/2) is F* = log(1 + √2) = 0.881374; the
semiclassical growth exponent table γ_z(g²) = (11/3)(1 − 5g²/(44π²)) and doubling factors 2^{γ_z} for g² ∈ {0.5, 1, 2, 3, 4}.

A failure of C2–C6 means the corresponding lemma in NOTE.md is wrong as stated and will be reported as such.

## Result (added after the run, predictions above unchanged)

Run: `groups_check.py`, under one second, `groups_check.json`. C1, C2, C5, C6, C7 pass for every group. C3 and C4 pass for Q8, 2T,
2O, 2I and for the abelian groups, and **fail for Dic3** (binary dihedral, order 12): its minimal relaxed set is {xy, zt}, the abelian
pattern, and it has no anticommuting pair at all. The prediction was wrong, not the code: in Dic3 = ⟨a, x | a⁶ = 1, x² = a³,
x a x⁻¹ = a⁻¹⟩ the commutators are the powers of a², so −1 = a³ is not a commutator and there is no twist eater. The lemma in NOTE.md
§3 is therefore stated for the property "−1 is a commutator in G" (round 3's c ∈ [G, G]), not "G non-abelian"; groups without it
(abelian groups, Dic3) fall under the abelian branch of the same lemma. On C5, Z4 and Q8 have optimal length 1 (−1 itself, cost 2) tied
with the predicted length 2 (i·i, cost 2); ties were allowed.
