# Pre-registration: the conditional photon given the block field (c3a-uv, 2026-11-22)

Written before any run. CPU only, one process, `CUDA_VISIBLE_DEVICES=-1`, a few minutes per run. Script: `condphoton.py`.

## Question

`ObsTransferPhys` (c) asks that fine observables decouple **given the block variables**. The mechanism proposed in `NOTE.md`
(ultraviolet half): if the block variable keeps the content of the slow modes, the conditional fine field is massive at the
block scale (a Poincare inequality on the kernel of the averaging map), uniformly in the resolution; if the block variable
loses the signal (decimation: its variance is dominated by the linearly divergent self-energy), conditioning removes less and
less as the resolution grows, and the conditional field tends to the unconditional (massless) one. This is the free-field
(linearised, abelian) form of both statements; it is the photon unit test of (c).

## Model

Linearised abelian gauge field `A_mu(x)` on the fine torus `(Z/N)^4`, `N = M*l`, Gaussian with covariance `delta_{mu nu}/phat^2`
(Feynman gauge; the constant mode removed). Only gauge-invariant functionals are used, so the gauge choice does not matter.

Block field: the linearisation of `RouteA.goodBlocking` (`Blocking.lean`): one step averages the straight path and, with weight
`w`, the spatial staples (4 for a spatial link, 6 for a temporal link), normalised by `1 + w*(#staples)` (the linearisation of
`projSU2` of the sum); `n = log2 l` steps. `w = 0` is decimation (sum of `l` link angles along a line).

Conditioning: all coarse plaquette fluxes (gauge invariant) and the four coarse zero-momentum link sums (holonomy averages).

Observable `X`: the fine flux `F_12` averaged over a fine hypercube of physical side `L1/2` (side `l/2` fine sites), placed at the
cell corner ("corner") or centred in the cell ("centre", away from the coarse time slice). `Y`: the same translated by `D` cells
(physical distance `D*L1`) in the time direction or in a spatial direction.

Quantities: unconditional covariance `C(D)`, conditional covariance `Gamma(D) = C(D) - Cov(X, Psi) Cov(Psi,Psi)^+ Cov(Psi, Y)`
(Bloch decomposition over coarse momenta, checked against a dense brute-force computation on a tiny torus), the ratio
`R(D) = Gamma(D)/C(D)`, and the content `kappa = 1 - Gamma(0)/C(0)` (fraction of Var X explained by the block field).

Runs: primary `M = 8`, `l = 2, 4, 8`, `w = 0, 0.5, 1`; secondary (only if the primary takes under 5 minutes) `M = 6`, `l = 8, 16`.

## Predictions (all directions and placements unless said otherwise)

* **G1 (good blocking massive):** for `w = 0.5` and `w = 1`, `|R(4)| < |R(2)|` and `|R(4)| <= 0.3`.
* **G2 (uniform in the resolution):** for `w = 0.5` and `w = 1`, `| |R(3)|_{l=8} - |R(3)|_{l=4} | <= 0.1`.
* **G3 (content kept):** for `w = 0.5`, `kappa(l=8) >= 0.5 kappa(l=4)`.
* **D1 (decimation loses it):** for `w = 0`, `|R(3)|` increases from `l = 2` to `4` to `8`, and `|R(3)|_{l=8}` exceeds the
  `w = 0.5` value by at least 0.2; `kappa` decreases with `l`.

A failed G-prediction would mean that the slice-smeared block variable does not pin the slow modes of the free field (the
ultraviolet half of the note would then need a different blocking); a failed D1 would mean that decimation is not a counterexample
at these resolutions. Either outcome is reported as is.
