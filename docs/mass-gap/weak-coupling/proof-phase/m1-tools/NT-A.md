# NT′(a): the root bound of cut avoidance, proved (m1-tools, 2026-11-22)

Brief: prove part (a) of Lemma NT′ (`NO-TRAP.md` 4): every star of `n = 2d` elements of SU(2) has a sign pattern whose
corrected relative angles are all at most some `θ_root < π`. Claim marks as in `NOTE.md`. Lean:
`formal/ProofPhase/M1/CutAvoid.lean` (new). Check of the measure formula: `nt_b.py`, part M (`run_nt_b.log`).

## 0. Result in plain words

**Proved: `θ_root = 2 arccos(s_n)`, with `s_n` the root of `(2/π)(s√(1-s²) + arcsin s) = 1/n`; for `n = 8` (`d = 4`)
`s_8 = 0.09833` and `θ_root = 168.71°`**, 11.3 degrees from the cut. The adversarial worst case found numerically was
147 degrees, so the bound is not sharp but it is rigorous and simple. The proof has a probabilistic half (a direction
`u` that is far from every element's "equator") and an elementary half (sign-corrected elements on one side of `u` lie
in a cap); the elementary half is machine-checked.

## 1. Statement

Identify SU(2) with the unit sphere `S³ ⊂ ℝ⁴` (unit quaternions). For `g, h ∈ SU(2)`: `Re tr(g h⁻¹) = ⟨g, h⟩`, so the
angle of the relative element `g h⁻¹` is the angle between `g` and `h` as vectors. Changing the sign of `g` (the central
element `-1`) is `g ↦ -g`.

**Lemma NT′(a).** For all `x_1, …, x_n ∈ S³` there are signs `σ_i ∈ {±1}` with
`∠(σ_i x_i, σ_j x_j) ≤ 2 arccos s_n < π` for all `i, j`.

## 2. Proof

**Step 1 (a good direction exists).** For `u` uniform on `S³`, the first coordinate `t = ⟨x, u⟩` (for a fixed unit `x`)
has density proportional to `(1 - t²)^{1/2}` on `[-1, 1]` (the marginal of the uniform measure on `S^{m-1}` has density
`∝ (1 - t²)^{(m-3)/2}`, here `m = 4`). Normalising (`∫_{-1}^{1} √(1-t²) dt = π/2`):
`P(|⟨x, u⟩| < s) = (2/π)(s√(1-s²) + arcsin s) =: μ(s)`.
(Checked by Monte Carlo with `2·10⁶` points: `s = 0.05, 0.0983, 0.2, 0.5` give `0.06370, 0.12488, 0.25306, 0.60923`
against `0.06364, 0.12496, 0.25294, 0.60900`.) The set `B_i = {u : |⟨x_i, u⟩| < s}` is open. If `n μ(s) < 1`, the union
of the `B_i` has measure `< 1`, so some `u ∈ S³` lies outside all of them: `|⟨x_i, u⟩| ≥ s` for every `i`. `μ` is
continuous and increasing, so this holds for every `s < s_n` with `n μ(s_n) = 1`, and by compactness (the set of good
`u` for `s` is closed, nested, non-empty for `s < s_n`) also for `s = s_n`.

**Step 2 (sign correction puts everything in a cap; Lean).** Let `σ_i = sign ⟨x_i, u⟩`. Then `⟨σ_i x_i, u⟩ ≥ s`
(`signCorrect_inner_ge`). For unit vectors `a, b` with `⟨a, u⟩, ⟨b, u⟩ ≥ s ≥ 0`: write `a = α u + a'`, `b = β u + b'`
with `a', b' ⊥ u`; then `⟨a, b⟩ = αβ + ⟨a', b'⟩ ≥ αβ - ‖a'‖‖b'‖ ≥ s² - (1 - s²) = 2s² - 1` (`inner_ge_of_cap`,
using `‖a'‖² = 1 - α² ≤ 1 - s²`). Since `cos(2 arccos s) = 2s² - 1` and `arccos` is decreasing,
`∠(σ_i x_i, σ_j x_j) ≤ 2 arccos s` (`angle_le_two_arccos`). ∎

**Lean (`CutAvoid.lean`, 4 theorems):** `inner_ge_of_cap`, `signCorrect_inner_ge`, `cap_of_away` (the family version),
`angle_le_two_arccos`; standard axioms only (`axioms.log`). Step 1 (the measure of a band of `S³`) is on paper.

## 3. Remarks

* For the twisted rule (`TWIST.md` 1) the label created at the root can be taken to be this `σ` (or the best of the 128
  patterns, which is at least as good); the corrected root star then has all relative angles `≤ 168.7°`.
* A sharper `θ_root` would follow from a better covering argument (the union bound ignores overlaps); not needed.
* NT′(a) is about the root only. Along the orbit the largest angle can grow (by up to 22 degrees in one step,
  `NO-TRAP.md` 4); that is part (b′), `NT-B.md`.
