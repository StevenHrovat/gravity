# c8a-saturation: pre-registration of two tiny CPU checks (written before running, 2026-11-22)

Purpose: unit tests of the vortex-saturation statement (`ProofPhase.Saturation.vortex_saturation`) on Z2, where the answer is
known. No GPU. Scripts: `z2_exact_2d.py` (N1), `z2_twist_4d.py` (N2); logs `*.log`.

Definitions as in Lean: periodic lattice `(Z/NZ)^d`, Wilson action `beta * sum_p sigma_p`, twist sheet = the plaquettes of the
plane `(mu, nu)` based at `x_mu = a`, `x_nu = c` (in `d = 2` one plaquette, in `d = 4` `N^2` plaquettes), `Z_tw` = the same
weight with those plaquettes entering with `-beta`, flip probability `P = Z_tw / (Z + Z_tw)`, and the Lean bound
`|1 - 2P| <= B = (N^d p q^(N-1) / (1 - q))^N`, `p = 1 - exp(-2|beta|)`, `q = 2(d-1) p`, valid when `q < 1`.

## N1: 2D Z2, exact by brute force (N = 2, 3)

Prediction (high-temperature expansion: the only closed 2-chains of the 2D torus are the empty set and the whole torus):
`1 - 2P = tanh(beta)^(N^2)` exactly, for every real `beta` (both signs).

Pass: agreement to relative 1e-10 at `beta in {-0.3, 0.05, 0.2, 0.5, 1.0}`, `N in {2, 3}`; and wherever `q < 1`, `B >= |1 - 2P|`.
Fail of the first item means the twist sheet or the flip probability is mis-specified; fail of the second would contradict the
Lean theorem (a bug in the statement or the script).

## N2: 4D Z2, Monte Carlo with thermodynamic integration (N = 4)

`log(Z_tw/Z) = -2 beta * sum_{p in sheet} integral_0^1 <sigma_p>_tau dtau`, where in the ensemble `tau` the sheet plaquettes carry
coupling `beta (1 - 2 tau)`; heat bath, checkerboard, 11 values of `tau` (Simpson), 2000 sweeps after 500 thermalisation sweeps per
point, error by 10 bins.

Predictions:
- `beta = 0.05` (inside the Lean window; strong coupling): `P >= 0.49`.
- `beta = 0.30` (confined, outside the Lean window): `P >= 0.35` (saturating, finite size `N = 4`).
- `beta = 0.60` (deconfined): `P <= 0.05` (the sheet costs about `2 beta` per plaquette over `N^2 = 16` plaquettes, entropy
  does not compensate: no saturation, the regime where ties exist).

The Lean bound itself is vacuous at `N = 4` (`B > 1` for every `beta` with `q < 1`, because of the `N^d` start count); it is not
tested by N2. N2 tests the mechanism (confined: saturates; deconfined: does not), not the constants.
