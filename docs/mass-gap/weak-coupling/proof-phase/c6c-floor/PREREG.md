# c6c-floor: pre-registration of one tiny CPU check (written before running, 2026-11-22)

Purpose: test the owner's cycle-6 reading "the act is super-additive", z(L1 + L2) >= z(L1) + z(L2) with z(L) = L * E(L) the box gap
times the box length, on models whose answer is known exactly or by brute force. Not a Yang-Mills computation.

Script: `superadd_check.py` (numpy only, one process, expected < 2 minutes). Output: `superadd_check.json`, `superadd_check.log`.

Models:
1. 2D Ising, row-to-row transfer matrix of a strip of width L (L = 2 .. 12), brute force 2^L states, symmetric form
   V = V1^{1/2} V2 V1^{1/2}. Two transverse boundary conditions: periodic and free. Couplings K = 0.25 (high temperature, gapped,
   K_c = 0.4407) and K = 0.6 (low temperature, ordered). Sectors by global spin flip: odd gap E_odd(L) (the "flip / centre-odd"
   analogue) and even gap E_even(L) (the "vacuum sector" analogue). Infinite-volume odd gap (Onsager, high T): m = 2(K* - K),
   tanh K* = e^{-2K}.
2. Free photon on an L^3 periodic lattice box (closed formula of c5e): z0(L) = 2 L arsinh(sin(pi/L)).
3. Free massive scalar in a 1D box with Dirichlet ends (continuum): z(L) = sqrt(m^2 L^2 + pi^2).

Quantities, for each model and sector: z(L) = L E(L); the super-additivity defect D(L1, L2) = z(L1) + z(L2) - z(L1 + L2) over all
L1, L2 >= 2 with L1 + L2 <= 12 (lattice) or on a grid (continuum); the pairs where D > 0 (violations); the smallest defect constant
c with z(L1 + L2) >= z(L1) + z(L2) - c on the range; and whether the one-box criterion z(L0) > c holds for some L0.

Pre-registered expectations (verdicts fixed now):
- E1 Ising free b.c., K = 0.25, odd sector: E_odd(L) > m at every L (correlations grow with the width, GKS), so super-additivity
  FAILS at some pair. Expected: FAIL.
- E2 Ising periodic, K = 0.25, odd sector: sign of E_odd(L) - m not predicted; reported. Super-additivity holds on the range iff no
  pair has D > 1e-9.
- E3 Ising K = 0.6 (ordered), odd sector, both b.c.: E_odd(L) -> 0 (tunnelling); z bounded; super-additivity FAILS.
- E4 photon: z0 increases to 2 pi, bounded; super-additivity FAILS (e.g. z0(8) < 2 z0(4)).
- E5 Dirichlet massive scalar: FAILS at every pair (sqrt is strictly sub-additive here).
- E6 approximate super-additivity with a defect: for the gapped high-temperature cases the one-box criterion z(L0) > c holds for some
  L0 on the range; for the photon and the ordered cases it does not. Caveat fixed now: c measured on a finite range is only a lower
  estimate of the true defect constant, so "criterion holds on the range" is necessary, not sufficient. For the photon (closed
  formula) c is also computed with L1, L2 up to 4096, where it must approach 2 pi and the criterion must fail (z0 < 2 pi always).
Any outcome is reported; no re-running with changed parameters except to fix a coding error, which would be stated.
