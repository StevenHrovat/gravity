# Sharper single-link influence bounds for `lgt`'s Dobrushin route (2026-11-21, revised after an adversarial review)

`mrdouglasny/lgt` proves, in Lean, exponential decay of plaquette correlations for U(n) Wilson lattice gauge theory on (ℤ/Nℤ)^d at strong
coupling (`ym_mass_gap_exponential_decay`, `LGT/MassGap/StrongCoupling.lean`), by Dobrushin's uniqueness method. The condition is
`maxNeighbors d · influenceBound n β < 1` with `influenceBound n β = 1 − e^(−4nβ)` and `maxNeighbors d = 8(d−1)`, i.e. roughly
β < 1/(32 n (d−1)) in `lgt`'s normalisation (weight exp(−β Σ_p (n − Re tr U_p))). The per-link bound is proved inside the headline theorem
(via `gibbsCondMeasure_cylinder_ratio` and `influenceCoeff_le_of_cylinder_ratio_bound_nocount`). This note gives sharper per-link bounds,
in decreasing order of rigour. Numbers: `influence_bounds.py`.

**Where it matters.** For SU(N) a different method already reaches further: Shen, Zhu and Zhu (arXiv:2204.12737, Bakry–Émery) prove a gap
for |β_SZZ| < 1/(16(d−1)) in their normalisation N β_SZZ Re tr, which for SU(2) is standard β < 1/(4(d−1)) (0.083 in d = 4), above every
rigorous row below. The improvements here matter for U(1) and U(n), which that result does not cover, and for `lgt`'s own route.

## 1. A factor of 2 with `lgt`'s existing lemma

`influenceCoeff_le_of_cylinder_ratio_bound` takes the hypothesis: for configurations σ, τ that differ only at y and every cylinder set B,
P_τ(B) ≤ e^C P_σ(B), here with C = 4nβ; it concludes influence ≤ 1 − e^(−C). Applied in both orders, the hypothesis bounds the density
g = dP_τ/dP_σ to [e^(−C), e^C], a ratio R = e^(2C), and from that alone the optimal total-variation bound is smaller:

**Lemma.** If μ ≪ ν are probability measures and g = dμ/dν takes values in [m, M] with M/m ≤ R, then
TV(μ, ν) ≤ (√R − 1)/(√R + 1) = tanh(ln R / 4).

*Proof.* TV = ∫(g − 1)₊ dν. For fixed m and M, with ∫g dν = 1, this is largest when g takes only the values M (on ν-mass p) and m, so
p = (1 − m)/(M − m) and TV = (M − 1)(1 − m)/(M − m). With M = Rm this is (Rm − 1)(1 − m)/(m(R − 1)), maximal at m = 1/√R, where it
equals (√R − 1)²/(R − 1) = (√R − 1)/(√R + 1). ∎

With R = e^(2C): influence ≤ tanh(C/2) = tanh(2nβ), against 1 − e^(−4nβ) (for small β, 2nβ against 4nβ). The same hypothesis, so the
change is local to the lemma.

## 2. A factor of 4 with the oscillation of the density

For the Wilson conditional the density ratio is better than the two-sided bound above. Changing y changes one plaquette's cost, which
lies in [0, 2n] for every value of the link x, so log(dP_τ/dP_σ) varies over x by at most 2 · 2n · β: R = e^(4nβ), and the lemma gives
**influence ≤ tanh(nβ)**. That needs a version of the cylinder-ratio lemma stated with the oscillation of the log-density (sup − inf ≤ 4nβ)
instead of the one-sided ratio; the existing interface cannot deliver it. Condition: 8(d−1) · tanh(nβ) < 1, about four times `lgt`'s range.

## 3. The neighbour count 6(d−1)

`lgt`'s own comment (`DobrushinVerification.lean`, "Interaction graph geometry") notes that `maxNeighbors d = 8(d−1)` counts each link as
its own neighbour once per plaquette, and that the tight count is 6(d−1), not tracked by the formal proof. With it, 6(d−1) · tanh(nβ) < 1.

## 4. The exact influence (numerical): factors of 8 (U(1)) and 12 (SU(2))

In the standard normalisation (U(1): weight e^(β cos θ_p), β = β_lgt; SU(2): e^((β/2) Re tr U_p), β = 2β_lgt), a link's conditional law
is exp(β⟨x, A⟩) on S¹ or S³ (unit quaternions), A the sum of the 2(d−1) staples. The influence of a neighbour is the supremum, over the
other staples' sum W (a sum of 2(d−1) − 1 unit vectors) and the old and new value v, v′ of the changed staple, of TV(law at W + v, law at
W + v′). Numerically (Nelder–Mead from a grid, `single_link.py`, `influence_bounds.py`) the supremum sits at W = 0, v′ = −v in every case
checked (d = 3, 4; β = 0.05 to 1), where it has a closed form, a ratio of a modified Struve function to a modified Bessel function:

- U(1): C(β) = L₀(β)/I₀(β) = 2β/π + O(β³);
- SU(2): C(β) = L₁(β)/I₁(β) = 4β/(3π) + O(β³).

(The SU(2) integral reduces to the unit disk, the projection of the uniform measure on S³ to a plane; checked against a direct Monte Carlo
on S³, 0.04245 ± 0.00004 against 0.04242 at β = 0.1.) Open for rigour: a proof that W = 0, v′ = −v is the worst case. In d = 2 the other
staples are a single unit vector, so W = 0 is not attainable and the closed form is an upper bound there. A series comparison gives
L₀(β) ≤ (2β/π)·I₀(β).

## Thresholds (standard β; `lgt`'s β for SU(2) is half)

| group, d | `lgt` | §1: tanh(2nβ), 8(d−1) | §2: tanh(nβ), 8(d−1) | §2 + §3: tanh(nβ), 6(d−1) | §4 exact, 6(d−1) (numerical) | Shen–Zhu–Zhu |
|---|---|---|---|---|---|---|
| U(1), 2 | 0.0334 | 0.063 (×1.9) | 0.126 (×3.8) | 0.168 (×5.0) | ≤ 0.264 (×7.9) | — |
| U(1), 3 | 0.0161 | 0.031 (×1.9) | 0.063 (×3.9) | 0.084 (×5.2) | 0.131 (×8.1) | — |
| U(1), 4 | 0.0106 | 0.021 (×2.0) | 0.042 (×3.9) | 0.056 (×5.2) | 0.087 (×8.2) | — |
| SU(2), 2 | 0.0334 | 0.063 | 0.126 | 0.168 | ≤ 0.396 | 0.250 |
| SU(2), 3 | 0.0161 | 0.031 | 0.063 | 0.084 | 0.197 | 0.125 |
| SU(2), 4 | 0.0106 | 0.021 | 0.042 | 0.056 | 0.131 | 0.083 |

(The `lgt` column solves 8(d−1)(1 − e^(−4nβ_lgt)) = 1 exactly; the linearised 1/(32n(d−1)) is slightly lower. In d = 2 the exact column is
an upper bound, see §4.)

## Context

Single-link Dobrushin in total variation is classical; these steps sharpen `lgt`'s existing route without changing its nature. Other
(unrefereed) work reports more for SU(2) with different metrics: a Wasserstein single-link argument up to β < 2/9 (`creelie/4Y-M`, pull
request #9, 2026) and computer-assisted block bounds up to β ≈ 0.42 (preprint "Explicit strong-coupling mass gap and a robust landing
interface for four-dimensional SU(2) lattice Yang–Mills theory"). All of these stay far below the physical region (β ≈ 2.3 for SU(2)).
