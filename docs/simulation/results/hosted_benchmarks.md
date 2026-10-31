# Hosted benchmarks: known quantum results, run as content

Workstream for "GUID v6: Our theory as simulated". Four hard quantum configurations whose answers are known exactly or to high precision are
hosted the way the paper describes (Sections 4 and 13 of `docs/quantum-gravity/quantum-gravity.tex`). Each configuration is asserted as
existence, meaning a Hamiltonian together with the sector of states that exist. The host lets it run, and two independent witnesses check
only that the state stays in that sector. They read a syndrome that commutes with the dynamics and never read the content. Every hosted
run below reproduces the known result within an honest error bar. **This validates the host and our code. It tests no new physics, and no
number here is evidence for or against DMP or GUID.**

## Reproduce

```sh
python3 docs/simulation/hosted_benchmarks.py           # all four, writes results/hosted_benchmarks.json; 53 of 53 checks passed
python3 docs/simulation/hosted_benchmarks.py --only B3 # one benchmark, no JSON
```

The script needs numpy and scipy only, and every seed is fixed. Measured on 2026-10-31 with Python 3.13.17, numpy 2.5.3 and scipy 1.18.1:
492 s in total, peak resident memory 1.89 GB, single-threaded BLAS on a 4-core machine shared with two other jobs. BLAS is pinned to one
thread by default because multi-threaded OpenBLAS on oversubscribed cores was measured about 20 times slower. Wall times depend on the
machine and are reported, not checked (INFO lines). Every other number is deterministic.

## Hosting as implemented

| Role | What it does |
|---|---|
| Existence | Hamiltonian plus sector: S^z_total = 0 (B1); fermion parity +1 and a pure Gaussian state (B2); Gauss's law at every site, zero field outside, zero charge (B3); unit norm and work register y < N (B4) |
| Host | Lanczos (ARPACK) in the sector basis (B1, B3); Jordan-Wigner plus a Bogoliubov (singular-value) transformation (B2); a gate sequence on an exact statevector (B4) |
| Witness T (trust half) | integer arithmetic on every basis configuration that carries amplitude (support membership); its own code path, for example a SWAR popcount where the host uses a lookup table, or an LU determinant |
| Witness I (information half) | the expectation value of a positive syndrome operator in floating point, for example <(S^z_tot)^2>, <sum_n G_n^2 + Q^2>, <Pi_{y>=N}>, or a Householder-QR determinant |
| Controls | the syndrome commutes with H (checked on a small full space); an injected fault that leaves the sector is refused by both witnesses; two orthogonal contents in the same sector get the same verdict; in B4 a phase fault (content changed, existence intact) passes both |

## Summary

| Benchmark | Known value | Hosted value | Deviation | Runtime |
|---|---|---|---|---|
| B1 Heisenberg ring, e0 = E0/N for N -> infinity | 1/4 - ln 2 = -0.4431471806 | -0.4431457 +- 0.0000011 | +1.5e-6 (1.3 sigma, 3.3e-6 relative) | 53 s |
| B2 transverse-field Ising ring, L = 4000, g = 1: E0 | finite-L closed form -5092.958309840347 | -5092.958309840346 | 2e-16 relative | 116 s (all of B2) |
| B2 central charge from the Casimir energy | 1/2 (+9.0e-9 at L = 4000) | 0.5000000052 | +5.2e-9 | |
| B2 central charge, Calabrese-Cardy fit of S(l) | 1/2 | 0.50000016 +- 0.00000026 | +1.6e-7 (0.6 sigma) | |
| B2 area law, saturated S at g = 0.5 / 1.5 | 0.6989875284 / 0.3069825111 (corner transfer matrix) | 0.6989875284 / 0.3069825111 | 3.1e-12 / 2.8e-12 | |
| B3 Schwinger model, vector mass M/g, m = 0, shifted lattice (main) | 1/sqrt(pi) = 0.5641896 | 0.586 +- 0.039 | +0.022 (0.55 sigma) | 257 s (all of B3) |
| B3 same, naive lattice m_lat = 0 | 0.5641896 | 0.593 +- 0.031 | +0.028 (0.92 sigma) | |
| B4 Shor, outcome distributions, 9 moduli, 192 bases | Shor's analytic distribution | max total-variation distance 7.5e-12 | | 66 s (all of B4) |
| B4 Shor, factors of 15, 21, 33, 35, 39, 51, 55, 57, 143 | 3x5, 3x7, 3x11, 5x7, 3x13, 3x17, 5x11, 3x19, 11x13 | all recovered | none | |
| B4 dense statevector memory | 16 x 2^n bytes | 1.016 x 16 x 2^n at n = 26 (fixed 16 MiB buffer) | | |

No check failed. One finding sits inside an honest error bar and is not hidden: the B3 continuum value lies 0.022 above 1/sqrt(pi).
That is within the error, but the error bar itself is large (7%); see the B3 caveats.

## B1. Heisenberg antiferromagnetic ring

- **Configuration.** H = sum_i S_i . S_{i+1}, spin 1/2, periodic, even N = 8 to 24. At N = 24 the sector has 2,704,156 states and the
  sparse matrix 33,860,736 nonzeros.
- **Existence.** S^z_total = 0. Witness T: the SWAR popcount of every full-register index (2^24 register) carrying amplitude equals
  N/2. Witness I: <S^z_tot> = <(S^z_tot)^2> = 0, with S^z_tot applied site by site, and the norm. [H, S^z_tot] = 0 holds exactly on the
  full 2^10 space, and the full-space ground energy at N = 10 equals the sector's. The ground state and the orthogonal triplet both pass
  with the same verdict. A single spin flip gives <(S^z_tot)^2> = 1 and is refused by both witnesses.
- **Method.** Lanczos (ARPACK eigsh, tol 1e-12) for the two lowest levels, cross-checked at every N against the Bethe ansatz
  (Newton solution of the logarithmic Bethe equations): the largest difference is 1.3e-15 per site. Extrapolation: e(N) = a + b/N^2 +
  c/N^4 on N = 12..24. The error is the largest change over windows N >= 8, 10, 14, 16 and over adding a 1/N^6 term (9 alternatives).
- **Result.** a = -0.4431457088 +- 1.1e-6 against -0.4431471806: deviation +1.47e-6, 1.3 sigma. Every alternative fit also lies above
  the exact value. This is the known multiplicative logarithmic correction of the Heisenberg chain (Affleck et al. 1989), which a power
  series in 1/N^2 cannot absorb. Read through conformal field theory, b = -pi v c / 6 with v = pi/2 gives c = 1.004 (expected 1 up to
  logarithms).
- **Gap (secondary).** N x gap = 4.181, 4.232, 4.270, 4.299, 4.323, 4.342, 4.359, 4.373, 4.385 for N = 8..24. The local exponent
  d ln(gap)/d ln N rises from 0.946 to 0.968 (1 for a gapless chain, 0 for a gapped one). The fit a + b/N + c/N^2 (N >= 12) gives an
  extrapolated gap of 0.0024, against 0.183 at N = 24. The amplitude pi^2/2 = 4.935 is reached only logarithmically.
- **Caveats.** N <= 24 is the memory limit of a sector code without translation symmetry (N = 26 would need about 6 GB). The precision
  of e0 is set by the logarithmic corrections, not by the eigensolver.

## B2. Transverse-field Ising ring at L = 4000 (free fermions)

- **Configuration.** H = -sum Z_i Z_{i+1} - g sum X_i on a ring of L = 4000 spins, at g = 1 (critical), 0.5 and 1.5.
- **Boundary conditions.** Periodic spins. In the even-parity sector, prod X_i = +1, the Jordan-Wigner fermions are antiperiodic
  (k = 2 pi (n + 1/2) / L). That sector is the existence sector: there the free-fermion Hamiltonian equals the spin Hamiltonian. At
  L = 10, [H, prod X] = 0, and the Bogoliubov energy equals the lowest even-parity spin energy to 1.8e-14 for all three g.
- **Existence and witnesses.** The state is the Gaussian state with G_jk = <i a_j b_k> = -(U V^T)_jk; parity = det G, purity = G
  orthogonal. Witness T reads the parity from a pivoted LU (sign) and checks |det G| = 1 (|log| < 1e-13). Witness I reads it from a
  Householder QR (number of reflectors and the sign of diag R) and checks max|G G^T - 1| <= 7e-15. Both read +1 at every g. A single
  spin flip Z_1 (one Majorana) turns both to -1: refused.
- **Method.** Majorana form H = i sum K_jk a_j b_k; one SVD of the 4000 x 4000 matrix K gives E0 = -sum of the singular values and the
  correlation matrix. The block entropy S(l) comes from the singular values of G restricted to the block (Peschel 2003; Vidal et al.
  2003), for 51 block sizes l from 1 to 2000 at g = 1 and 12 at g = 0.5 and 1.5.
- **Results.**
  - (a) E0 equals the finite-L closed form -sum_k sqrt(1 + g^2 - 2 g cos k) to 2e-16 relative at all three g. At g = 0.5 and 1.5,
    E0/L equals the thermodynamic limit -(2/pi)(1+g) E(4g/(1+g)^2) to 4e-16 (Pfeuty 1970). At g = 1, E0/L - e_inf = -3.2725e-8 =
    -pi v c / (6 L^2), which gives c = 0.5000000052 (v = 2). The exact next term predicts 1/2 + 7 pi^2/(480 L^2) = 0.5000000090; the
    difference is float error.
  - (b) At g = 1, a fit of S(l) = (c/3) ln[(L/pi) sin(pi l / L)] + c1' (Calabrese-Cardy 2004, Eq. 1.1, periodic) on 100 <= l <= 2000
    gives c = 0.50000016 +- 0.00000026 (spread over windows starting at 50, 200 or 400, or ending at 1000), with c1' = 0.478558 and a
    largest residual of 8.4e-8.
  - (c) At g = 0.5 and 1.5, S(l) saturates (S(L/2) - S(L/8) = 2e-12): the area law. The saturated values match the corner-transfer-matrix
    prediction (Calabrese-Cardy 2004, Eqs. 4.30-4.34, eps = pi K(k')/K(k), k = min(g, 1/g)) to 3e-12. A block has two cuts: in the
    disordered phase S = 2 S_half; in the ordered phase the even-parity ground state is the cat state, whose ln 2 is shared by the two
    cuts, so S = 2 S_half - ln 2. This assignment was derived before the comparison.
- **Cost.** 116 s for all of B2 (three SVDs of about 27 s each, single-threaded) and 1.4 GB peak when B2 runs alone: O(L^2) memory and
  O(L^3) time. This is the "4000-qubit hosted system with a known answer". It is cheap because the state is Gaussian (free fermions),
  not because 4000-qubit states are cheap; see B4.

## B3. Schwinger model (QED in 1+1 dimensions)

- **Configuration.** Kogut-Susskind staggered fermions, open boundaries, zero background field. Gauss's law is integrated out, which
  leaves the spin Hamiltonian of Banuls et al. 2013, Eq. 2.6: W = 2H/(a g^2) = x sum_{n<N-1} (s+_n s-_{n+1} + h.c.) +
  (mu/2) sum_n (1 + (-1)^n s^z_n) + sum_{n<N-1} L_n^2, with L_n = sum_{k<=n} (s^z_k + (-1)^k)/2, x = 1/(ag)^2, mu = 2 m_lat/(a g^2),
  and M/g = (E1 - E0)/(2 sqrt x). Two lattices are run. The main one has mu = -1/4, i.e. m_lat = -g^2 a/8, the massless point
  identified by the discrete chiral symmetry (Dempsey, Klebanov, Pufu, Zan 2022). The other is the naive m_lat = 0.
- **Existence and witnesses.** Gauss's law L_n - L_{n-1} = Q_n at every site, with L_{-1} = 0 (zero background) and L_{N-1} = 0 (zero
  field beyond the last site), which together imply total charge zero (the S^z_total = 0 sector). The host stores an explicit link
  register E_0..E_{N-2} for every configuration. Witness T checks Gauss's law in integers at every site of every configuration that
  carries amplitude, from that register. Witness I evaluates <sum_n G_n^2 + Q_tot^2> = 0 in floating point. The N = 22 ground state and
  vector state (x = 1) pass with the same verdict. A spin flip (a charge without its field) and a flux line on one link without charges
  give <sum G^2 + Q^2> = 2 and are refused by both. Code check: the same model with explicit integer links at N = 6 (1,075,648 states,
  |E| <= 3 is exact there). All Gauss generators commute with H, and the 20 states with G_n = 0 have exactly the spectrum of the
  integrated Hamiltonian (2.5e-14).
- **Method.** Lanczos for N = 8..22 (705,432 states at N = 22) at x = 0.5, 1, 1.5, 2, 3, 4, warm-started from the previous x. The
  following rules were written down before any continuum extrapolation was run (first on N <= 18 data) and were not changed after it,
  with one exception noted below:
  - N -> infinity: w + a/N^2 + b/N^3 on N = 12..22 (leading kinetic term of a massive particle in a box plus a boundary shift). The
    error is the largest change over N >= 14, N >= 16, the form 1/N^2 + 1/N^4, and 1/N^2 on the last four sizes.
  - x -> infinity: weighted quadratic in y = 1/sqrt(x) over all x with N_max/sqrt(x) >= 10. The alternatives are linear on x >= 1.5,
    quadratic on x >= 1, cubic, and no linear term. The exception: after the first (N <= 18) continuum run, the "no linear term"
    alternative was dropped for the naive lattice only, because that lattice has a known O(a) mass-shift term (Dempsey et al.).
    Keeping it would raise the naive lattice's fit-family spread from 0.028 to 0.074; the check passes either way.
  - The total error is the propagated statistical error combined in quadrature with the fit-family spread.
- **Results.**

  | x | ag | shifted, N -> inf | shifted, N = 22 | naive, N -> inf | naive, N = 22 |
  |---|---|---|---|---|---|
  | 0.5 | 1.41 | 0.58352 +- 0.00064 | 0.58917 | 0.89551 +- 0.00041 | 0.89862 |
  | 1 | 1.00 | 0.56476 +- 0.00147 | 0.57837 | 0.78478 +- 0.00101 | 0.79391 |
  | 1.5 | 0.82 | 0.56202 +- 0.00245 | 0.58358 | 0.74223 +- 0.00181 | 0.75796 |
  | 2 | 0.71 | 0.56160 +- 0.00354 | 0.59102 | 0.71797 +- 0.00277 | 0.74045 |
  | 3 | 0.58 | 0.56199 +- 0.00601 | 0.60673 | 0.69004 +- 0.00486 | 0.72589 |
  | 4 | 0.50 | 0.56268 +- 0.00874 | 0.62221 | 0.67404 +- 0.00694 | 0.72279 |

  - Continuum, shifted lattice (main): M/g = 0.586 +- 0.039 (statistical 0.016, fit family 0.035), against 1/sqrt(pi) = 0.5641896:
    deviation +0.022, 0.55 sigma. The alternatives give 0.562 (linear, x >= 1.5), 0.578 (quadratic, x >= 1), 0.570 (cubic) and
    0.550 (no linear term).
  - Continuum, naive lattice: 0.593 +- 0.031, 0.92 sigma.
  - Out-of-sample test of the finite-size form: the N = 12..22 fit at x = 4 predicts the N = 24 gap as 0.613467. The computed value
    (2,704,156 states) is 0.613388, a difference of 7.9e-5, well inside sigma_N = 0.0087.
- **Caveats.**
  - The precision is limited by N <= 22. Banuls et al. needed N >= 20 sqrt(x) for small finite-volume effects and used x = 5..600 with
    MPS; with exact diagonalisation only x <= 4 (ag >= 0.5) has N_max/sqrt(x) >= 10.
  - The pre-declared weighted quadratic fit is dominated by the coarsest lattice (x = 0.5, ag = 1.41), whose N-extrapolation is the
    most precise, and a quadratic in ag does not describe the strong-coupling side well. That is why the central value sits high and the
    error is 7%.
  - On the shifted lattice the thermodynamic-limit values at 1.5 <= x <= 4 already lie within 0.5% of 1/sqrt(pi) (lattice artifacts
    are small after the mass shift, as Dempsey et al. report). These are not continuum values, and no claim rests on them.
  - Compared with the MPS value 0.56421(9) (Banuls et al.), this ED result is a 5%-level sanity check, not a precision measurement.
  - Not done: the massive case (m/g = 0.125, 0.25; MPS binding energies 0.53953(5) and 0.51922(5)), because an ED continuum error of
    several per cent cannot test numbers known to 5e-5. Also not done: the chiral condensate e^gamma/(2 pi^{3/2}) = 0.159929, which needs
    the free-theory subtraction and a continuum control that N <= 22 does not give. The ground-state energy density (exact -1/pi) was
    also not used, because its x-dependence is too strong to extrapolate from x <= 4.

## B4. Shor's period finding, and what a dense statevector costs

- **Configuration.** A counting register of t = 2n qubits and a work register of n = ceil(log2 N) qubits, 3n in total, as an exact
  complex statevector. The counting register starts in uniform superposition and the work register in |1>. Controlled-U^(2^j) with
  U|y> = |a y mod N> for y < N, and identity above N (a permutation, so the subspace y < N is invariant), then the inverse QFT. The
  inverse QFT is the exact DFT; it equals the explicit gate circuit (H, controlled phases, swaps) to 1.8e-16. Bases: every a coprime
  to N for N = 15, 21, 33, 35, 39, 51, 55, 57 (n <= 6, 18 qubits), and a = 2, 3, 5, 7 for N = 143 (24 qubits, 16.8 million amplitudes).
- **Existence and witnesses.** Unit norm and work register y < N. Witness T: every (counting, work) configuration carrying amplitude has
  y < N (amplitudes outside are exactly zero), and the support norm is 1. Witness I: <psi|Pi_{y>=N}|psi> = 0 with the projector applied
  as an operator, and <psi|psi> = 1. Both pass for all 192 hosted states. A faulty multiplier that exchanges |1> and |2^n - 1> moves
  amplitude out of the subspace and is refused by both in every case. A Z on work qubit 0 changes the content (a relative phase) but
  not existence, and both pass: the syndrome never reads content. Note: a plain X on the top work qubit is not always a detectable fault.
  For N = 15, a = 2 it maps the orbit {1, 2, 4, 8} to {9, 10, 12, 0}, all inside the sector.
- **Post-processing.** One run, textbook: the continued-fraction convergents of k/2^t, and the first denominator q < N with
  a^q = 1 mod N. A factor is gcd(a^(r/2) - 1, N) when r is even and a^(r/2) != -1 mod N. Probabilities are exact, summed over the
  simulated outcome distribution. The 1000 sampled shots use a fixed seed.

  | N | qubits (3n) | Beauregard 2n+3 | bases | a = 2: r | P(period) | P(factor) | shots: r recovered / 1000 | mean P(factor) over bases |
  |---|---|---|---|---|---|---|---|---|
  | 15 | 12 | 11 | 7 | 4 | 0.5000 | 0.5000 | 489 | 0.429 |
  | 21 | 15 | 13 | 11 | 6 | 0.3307 | 0.3308 | 341 | 0.211 |
  | 33 | 18 | 15 | 19 | 10 | 0.3982 | 0 (2^5 = -1 mod 33) | 405 | 0.220 |
  | 35 | 18 | 15 | 23 | 12 | 0.3307 | 0.3307 | 357 | 0.303 |
  | 39 | 18 | 15 | 23 | 12 | 0.3307 | 0.3307 | 351 | 0.303 |
  | 51 | 18 | 15 | 31 | 8 | 0.5000 | 0.5000 | 514 | 0.484 |
  | 55 | 18 | 15 | 39 | 20 | 0.3927 | 0.3927 | 404 | 0.320 |
  | 57 | 18 | 15 | 35 | 18 | 0.3295 | 0 (2^9 = -1 mod 57) | 353 | 0.180 |
  | 143 | 24 | 19 | 4 | 60 | 0.2647 | 0.2647 | 252 | 0.232 |

  The simulated distributions equal Shor's analytic distribution (Shor 1997) to a total-variation distance of 7.5e-12 or less. For
  every N the factors recovered over the bases are exactly the known prime factors. P(factor) can slightly exceed P(period) (N = 21),
  because a recovered multiple of r can also give a factor.
- **Cost map.** One random layer is n Haar single-qubit gates plus n - 1 CZ gates, on a dense complex128 statevector. The measured peak
  memory is the 16 x 2^n-byte state plus a fixed 16 MiB gate buffer: 1.016 x the state at n = 26 (1 GiB).

  | n | state | measured peak | seconds per layer |
  |---|---|---|---|
  | 10 | 16 KiB | 52 KiB | 0.0012 |
  | 14 | 0.25 MiB | 0.75 MiB | 0.0025 |
  | 18 | 4 MiB | 10 MiB | 0.032 |
  | 22 | 64 MiB | 80 MiB | 0.67 |
  | 24 | 256 MiB | 272 MiB | 3.25 |
  | 26 | 1 GiB | 1.016 GiB | 15.6 |

  The time per gate grows as 2^(1.065 n) for n = 18..26 (slope 1 for the 2^n law; the excess is cache and memory bandwidth). With
  7.3e-9 s per gate per amplitude (single core), the extrapolations are:
  - n = 50: 18 PB (16 PiB) for the state alone, and about 10^8.6 s (13 years) per layer.
  - n = 4000: 10^1205.3 bytes.
  - n = 4099: 10^1235.1 bytes. 4099 is the 2n + 3 logical qubits of Beauregard's circuit for a 2048-bit RSA modulus.

  For scale, the observable universe holds about 10^80 atoms.
- **Contrast.** B2 hosts 4000 qubits in 1.4 GB and two minutes because free-fermion (Gaussian) states are fixed by a 2L x 2L
  correlation matrix. Clifford circuits are likewise cheap by the Gottesman-Knill theorem (stabilizer tableau, O(n^2) per measurement;
  Aaronson and Gottesman 2004); another workstream covers those. Structured hosting stays polynomial. Generic content, such as Shor's
  register for a 2048-bit modulus, costs 2^n on a classical host.
- **Caveats.** The modular multiplications are applied as exact permutation gates on the register. They are not decomposed into
  elementary gates, which changes gate counts but not the state. The register sizes (t = 2n) are the textbook choice, not Beauregard's
  2n + 3 layout, and the gate-level cost of Shor's circuit is not simulated. Wall times are single-core on a shared machine.

## References

Each entry is marked **verified** (checked by web search in this session, as stated) or **standard, not re-checked**. Names are
written in ASCII.

1. H. Bethe, "Zur Theorie der Metalle. I. Eigenwerte und Eigenfunktionen der linearen Atomkette", Z. Phys. 71, 205 (1931). **verified**
2. L. Hulthen, "Ueber das Austauschproblem eines Kristalles", Ark. Mat. Astron. Fys. 26A, No. 11 (1938). **verified** (title, journal,
   volume; sources disagree on the page or article number)
3. I. Affleck, D. Gepner, H. J. Schulz, T. Ziman, "Critical behaviour of spin-s Heisenberg antiferromagnetic chains: analytic and
   numerical results", J. Phys. A 22, 511 (1989). **verified** (bibliographic data via citing papers; text not re-read)
4. H. W. J. Bloete, J. L. Cardy, M. P. Nightingale, "Conformal invariance, the central charge, and universal finite-size amplitudes at
   criticality", Phys. Rev. Lett. 56, 742 (1986); I. Affleck, Phys. Rev. Lett. 56, 746 (1986). **verified**
5. E. Lieb, T. Schultz, D. Mattis, "Two soluble models of an antiferromagnetic chain", Ann. Phys. 16, 407 (1961). **verified**
6. P. Pfeuty, "The one-dimensional Ising model with a transverse field", Ann. Phys. 57, 79 (1970). **verified**
7. P. Calabrese, J. Cardy, "Entanglement entropy and quantum field theory", J. Stat. Mech. (2004) P06002, arXiv:hep-th/0405152.
   **verified** (Eq. 1.1 and Eqs. 4.30-4.34 read in the arXiv text)
8. I. Peschel, "Calculation of reduced density matrices from correlation functions", J. Phys. A 36, L205 (2003). **verified**
9. G. Vidal, J. I. Latorre, E. Rico, A. Kitaev, "Entanglement in quantum critical phenomena", Phys. Rev. Lett. 90, 227902 (2003). **verified**
10. J. Schwinger, "Gauge invariance and mass. II", Phys. Rev. 128, 2425 (1962). **verified**
11. J. Kogut, L. Susskind, "Hamiltonian formulation of Wilson's lattice gauge theories", Phys. Rev. D 11, 395 (1975). **verified**
12. M. C. Banuls, K. Cichy, J. I. Cirac, K. Jansen, "The mass spectrum of the Schwinger model with matrix product states", JHEP 11 (2013)
    158, arXiv:1305.3765. **verified** (Eq. 2.6, the gap formula, N >= 20 sqrt(x), and the binding-energy tables read in the arXiv text)
13. C. J. Hamer, Zheng Weihong, J. Oitmaa, "Series expansions for the massive Schwinger model in Hamiltonian lattice theory", Phys. Rev.
    D 56, 55 (1997), arXiv:hep-lat/9701015. **verified**
14. T. Byrnes, P. Sriganesh, R. J. Bursill, C. J. Hamer, "Density matrix renormalization group approach to the massive Schwinger model",
    Phys. Rev. D 66, 013002 (2002). **verified**
15. R. Dempsey, I. R. Klebanov, S. S. Pufu, B. Zan, "Discrete chiral symmetry and mass shift in the lattice Hamiltonian approach to the
    Schwinger model", Phys. Rev. Research 4, 043133 (2022), arXiv:2206.05308. **verified** (Hamiltonian, Gauss law and m_lat = m - e^2 a/8
    read in the arXiv text)
16. P. W. Shor, "Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer", SIAM J. Comput. 26,
    1484 (1997). **verified**
17. S. Beauregard, "Circuit for Shor's algorithm using 2n+3 qubits", Quantum Inf. Comput. 3, 175 (2003), arXiv:quant-ph/0205095. **verified**
18. D. Gottesman, "The Heisenberg representation of quantum computers", arXiv:quant-ph/9807006 (1998). **verified**
19. S. Aaronson, D. Gottesman, "Improved simulation of stabilizer circuits", Phys. Rev. A 70, 052328 (2004). **verified**
20. M. A. Nielsen, I. L. Chuang, Quantum Computation and Quantum Information (Cambridge University Press, 2000): QFT circuit, continued
    fractions. **standard, not re-checked**
21. About 10^80 atoms in the observable universe: common order-of-magnitude estimate. **standard, not re-checked**
