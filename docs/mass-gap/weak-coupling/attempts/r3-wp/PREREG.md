# Pre-registration, round 3 attempt 3 (r3-wp): one-block relative convergence on large fields (2026-11-21)

Written before any computation for this attempt. Rules: `../RULES.md` (round-3 additions). CPU only, one process,
`CUDA_VISIBLE_DEVICES=-1`, at most 15 minutes per run.

## What is tested (new)

W_p asks for convergence of effective densities in **relative** sup norm, on all configurations, large fields included.
The worry (brief, part 1): where densities are tiny (large fields), relative closeness may fail or converge only with
constants of order e^{c/g²}. This test looks at the one case where a block law of SU(2) with the Wilson action is
exactly computable: one 2D block of ℓ × ℓ plaquettes (n = ℓ² independent Wilson plaquettes in axial gauge; the block
plaquette is their product, a chain of n SU(2) elements). Its tuned limit is the SU(2) heat kernel K_t.

- Fine density: w_β(U) ∝ exp((β/2) tr U) on SU(2), character coefficients d_j(β) = I_{2j+1}(β)/I_1(β).
- Block density: ρ_n = w_β^{*n} = Σ_j (2j+1) d_j(β)^n χ_j.
- Limit: K_t = Σ_j (2j+1) e^{−t j(j+1)} χ_j.
- Tuning (line of constant physics, by a block observable): β_n solves d_{1/2}(β_n)^n = e^{−3t/4}, i.e. the block
  expectation of the fundamental character is the same as in the limit.
- δ_n(t) = sup over all θ ∈ [0, π] (class angle; θ = π is U = −1, the largest field) of |log ρ_n(θ) − log K_t(θ)|.
- Naive conversion bound N_n(t) = sup|ρ_n − K_t| / min K_t (what one gets from absolute closeness plus a lower bound).

Parameters: t ∈ {1, 0.5}; ℓ ∈ {1, 2, 4, 8} (n = 1, 4, 16, 64). At t = 0.5, K_t(π)/K_t(0) is about 2·10⁻⁷ (a large
field in the sense of the brief).

## Method

1. Float design run (`chain_float.py`): δ_n, the location of the sup, and N_n, on a fine θ grid. Design only.
2. Certificate (`chain_cert.py`): mpmath interval arithmetic (directed rounding). Bessel values by their power series
   with a rigorous tail bound; β_n enclosed by bisection on the monotone map β ↦ d_{1/2}(β) (an enclosure of the root;
   all later quantities are evaluated on the β-interval); character sums truncated at j ≤ J with a rigorous tail bound
   (for 2j+1 > β the ratio I_{ν+1}/I_{ν−1} < 1 − ... is bounded via I_{ν−1} > (2ν/β) I_ν, giving geometric decay);
   supremum over θ by cells: third-order Taylor expansion at each cell centre with the fourth-derivative remainder
   bounded globally from the character coefficients. The result is a certified upper bound of δ_n and a certified
   lower bound (value at one point), for every listed (n, t).

## Predictions (fixed now, from a saddle-point argument, before any number)

- **P1 (contraction):** δ_n decreases with ℓ; for ℓ = 2 → 4 and ℓ = 4 → 8 the ratio δ_{4n}/δ_n is at most 1/2 at both t
  (heuristic scaling between 1/n and 1/n²).
- **P2 (no large-field blow-up):** n·δ_n(t) stays below 20/t for n ∈ {16, 64}: the relative error has the natural size
  of an irrelevant correction, not a factor e^{π²/t}.
- **P3 (the naive conversion is exponentially lossy):** N_n(0.5)/δ_n(0.5) ≥ 10³ for n ∈ {16, 64}.

Pass/fail: P1 and P2 are judged on certified bounds (upper bound of δ_{4n} over lower bound of δ_n for P1; upper
bound for P2). P3 on float values. A failure is reported as a failure.

## What it would and would not show

It shows (if passed) that relative closeness on large fields holds with natural rates in the one exactly solvable SU(2)
block: the density at U = −1 is approached relatively because both sides are dominated by the same smooth path. It
does not touch 4D: no running (2D is superrenormalisable), no coupling between blocks (no Bianchi constraint in 2D).
Photon/Z₂/triviality checks are in the note.
