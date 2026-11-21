# Sharper single-link influence bounds for `lgt`'s Dobrushin route (2026-11-21)

A note written to slot into `mrdouglasny/lgt` (`LGT/MassGap/DobrushinVerification.lean`), which proves the strong-coupling lattice mass gap
for U(n) Wilson theory when 8(d−1)·(1 − e^(−4nβ)) < 1, i.e. roughly β < 1/(32 n (d−1)) in `lgt`'s normalisation
(weight exp(−β Σ_p (n − Re tr U_p))). Three improvements of the per-link influence coefficient, in decreasing order of rigour. Numbers:
`influence_bounds.py` (output `influence_bounds.json`).

## 1. The ratio bound (rigorous, elementary): a factor of about 4

`lgt` turns a bound on the density ratio of two conditional laws into a total-variation bound via
`influenceCoeff_le_of_cylinder_ratio_bound`, giving 1 − 1/R with R = e^(2D), D = 2nβ the action oscillation on a shared plaquette.
The optimal bound from the same hypothesis is smaller:

**Lemma.** Let μ ≪ ν be probability measures with density g = dμ/dν taking values in [m, M], M/m ≤ R. Then
TV(μ, ν) ≤ (√R − 1)/(√R + 1) = tanh(ln R / 4).

*Proof.* TV = ∫(g − 1)₊ dν. For fixed m and M, with ∫g dν = 1, this is largest when g takes only the values M (on ν-mass p) and m, so
p = (1 − m)/(M − m) and TV = (M − 1)(1 − m)/(M − m). With M = Rm this is ((Rm − 1)(1 − m)/m)/(R − 1), maximal at m = 1/√R, where it
equals (√R − 1)²/(R − 1) = (√R − 1)/(√R + 1). ∎

With R = e^(2D): TV ≤ tanh(D/2) = tanh(nβ), against `lgt`'s 1 − e^(−4nβ). For small β that is nβ against 4nβ. With `lgt`'s
neighbour count the condition becomes 8(d−1)·tanh(nβ) < 1, i.e. **β < artanh(1/(8(d−1)))/n ≈ 1/(8 n (d−1))**: about 3.8 to 3.9 times
`lgt`'s threshold in d = 2 to 4.

## 2. The neighbour count: a further factor 4/3, if confirmed

A link e lies in 2(d−1) plaquettes; each has 3 other links, and two distinct links share at most one plaquette, so e has exactly 6(d−1)
neighbours. `maxNeighbors d = 8(d−1)` counts the 4 boundary links of each plaquette, which includes e itself once per plaquette, and
Dobrushin's column sum runs over the other links only. If that reading is right, 8(d−1) is a valid but loose upper bound, and the
condition becomes 6(d−1)·tanh(nβ) < 1.

## 3. The exact influence (floating point): factors of 8 (U(1)) and 12 (SU(2))

In the standard normalisation (U(1): weight e^(β cos θ_p), β = β_lgt; SU(2): e^((β/2) Re tr U_p), β = 2β_lgt), a link's conditional law is
exp(β⟨x, A⟩) on S¹ or S³ (unit quaternions), A the sum of the 2(d−1) staples. The influence of a neighbour is the supremum, over the
other staples' sum W and the old and new value v, v′ of the changed staple, of TV(law at W + v, law at W + v′). Numerically (Nelder–Mead
from a grid, `single_link.py`) the supremum sits at W = 0, v′ = −v in every case checked (d = 2, 3, 4; β = 0.05 to 1), where it has a
closed form, the ratio of a modified Struve function to a modified Bessel function:

- U(1): C(β) = L₀(β)/I₀(β) = 2β/π + O(β³);
- SU(2): C(β) = L₁(β)/I₁(β) = 4β/(3π) + O(β³).

(The SU(2) integral reduces to the unit disk, since the projection of the uniform measure on S³ to a plane is uniform on the disk.) Checked
against a direct Monte Carlo on S³: 0.04245 ± 0.00004 against 0.04242 at β = 0.1. The open step for rigour is a proof that W = 0, v′ = −v
is the worst case; an elementary series comparison gives L₀(β) ≤ (2β/π)·I₀(β), so for U(1) the linear form 2β/π is an upper bound at
that configuration.

## Thresholds (standard β; `lgt`'s β for SU(2) is half)

| group, d | `lgt` | ratio bound, 8(d−1) | ratio bound, 6(d−1) | exact influence, 6(d−1) |
|---|---|---|---|---|
| U(1), 2 | 0.0334 | 0.126 (×3.8) | 0.168 (×5.0) | 0.264 (×7.9) |
| U(1), 3 | 0.0161 | 0.063 (×3.9) | 0.084 (×5.2) | 0.131 (×8.1) |
| U(1), 4 | 0.0106 | 0.042 (×3.9) | 0.056 (×5.2) | 0.087 (×8.2) |
| SU(2), 2 | 0.0334 | 0.126 (×3.8) | 0.168 (×5.0) | 0.396 (×11.9) |
| SU(2), 3 | 0.0161 | 0.063 (×3.9) | 0.084 (×5.2) | 0.197 (×12.2) |
| SU(2), 4 | 0.0106 | 0.042 (×3.9) | 0.056 (×5.2) | 0.131 (×12.3) |

(The `lgt` column solves 8(d−1)(1 − e^(−4nβ_lgt)) = 1 exactly; the linearised 1/(32n(d−1)) is slightly lower.)

## Context

Single-link Dobrushin in total variation is a classical tool; these improvements make `lgt`'s existing route sharper, they do not change
its nature. Other (unrefereed) work reports more with different metrics: a Wasserstein single-link argument for SU(2) up to
β < 2/9 (`creelie/4Y-M`, pull request #9, 2026) and computer-assisted block bounds up to β ≈ 0.42 (preprint "Explicit strong-coupling mass
gap and a robust landing interface for four-dimensional SU(2) lattice Yang–Mills theory"). All of these stay far below the physical
region (β ≈ 2.3 for SU(2)), where the open problem lives.
