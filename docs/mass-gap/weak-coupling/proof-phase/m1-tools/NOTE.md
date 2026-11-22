# M1 tools: reading gaps, Lemma D, exactness of the conditional step (m1-tools, 2026-11-22)

Brief: build the tools for M1 (a law-preserving version of Balaban's large-field operation R, see
`../c6f-m1scope/ONE-STEP.md`): close the reading gaps of the one-step test, state and prove Lemma D (core dilution)
with its elementary part in Lean, prove the exactness of the block-constrained step in Lean, and list every estimate
M1 needs (`M1-PLAN.md`). Claim discipline as in `../../attempts/RULES.md`: every statement below is marked
**Lean** (machine-checked), **paper** (proved here on paper), **citation** (Balaban, equation given), **sketch**
(argument given, gaps named) or **open**.

Paper labels as in `ONE-STEP.md`: [I] CMP 109, [III] CMP 119, [IV] CMP 122 p. 175, [V] CMP 122 p. 355. Numbered
references `[12]`, `[14]`, `[15]` are those of [I]'s reference list (section 1.4). Reading marks: **full** = page
images read by me. New in this session, full: [IV] pp. 177-191 (pp. 182-191 for the first time), [V] pp. 364-373,
[I] pp. 251-254 (the averaging), reference lists of [I], [III], [IV], [V]. Nothing outside this folder and
`formal/ProofPhase/M1/` was edited.

## 0. Result in plain words

1. **Reading gaps closed; the rows of ONE-STEP that relied on them are confirmed.** [IV] pp. 182-191 (the general
   preliminary integration) consist only of exact operations: δ-constrained integrations, exact partitions of unity,
   a Faddeev-Popov insertion, a change of variables that removes the δ-functions, and identities showing that new
   characteristic functions imply the old ones. [V] pp. 364-373 are transformations of the Wilson-action term and
   localization expansions: identities and bounds. Nothing there changes the law. Two details matter for M1:
   Balaban already suppresses the influence of the old core on the new background by `L^{-N}` ([V] (1.31), (1.47);
   this is where his `N` comes from), and large plaquettes in the core are controlled by positivity of the
   group-valued Wilson action, never by analyticity ([V] (1.48)).
2. **How the averaging acts far from the identity.** Balaban's block variable ([I] (0.4); variant (0.12)) is an
   explicit formula: the Lie-algebra mean of the principal logarithms of the loops "path through the block, closed
   by the straight fine path along the coarse bond", multiplied by the transport along that straight path. It is
   defined on all configurations once `log(-1)` is fixed; Balaban claims its properties only near the identity and
   allows "many other definitions" ([I] p. 254). His minimiser reference `[15]` is **Balaban, The variational problem
   and background fields in renormalization group method for lattice gauge theories, CMP 102 (1985) 277-309**; also
   needed are `[12]` (averaging operations, CMP 98) and `[14]` (regular configurations, CMP 99). None is in the
   repository. **Download script for the owner: `get-balaban-refs.ps1` in this folder.**
3. **Lemma D as stated in ONE-STEP is false, for every admissible averaging.** A thin centre vortex (`U = -1` on
   four fine bonds at a coarse site, in two of the four axis directions) is reproduced exactly by every block
   average that is gauge covariant, conjugation covariant and rotation symmetric about block centres, at every scale
   at which that site stays a coarse site. Its coarse plaquettes stay at `-1` (maximally large) forever (**Lean**,
   `ProofPhase.M1.vortex_persists`). Balaban's renormalisation criterion does not exclude such a core: in the last
   `N` steps it tests the field only in shells around the old region, never over the core itself ([IV] (1.2)-(1.9)).
4. **The moderate half of Lemma D holds, with a much better rate than ONE-STEP guessed.** At a block centre,
   Balaban's average acts on the star of bonds by fixed weights `q + e₁[b = c] - e₂[b = -c]` with
   `e₁ + e₂ = L^{1-d}` (exact, checked with exact fractions for `L = 13`, `d = 4`). The visible part of a core
   perturbation therefore shrinks by `L^{1-d} = 1/2197` per step, plus nonlinear and background corrections
   (**paper**; elementary part **Lean**, `ProofPhase.M1.balaban_star_dilution`, `spread_iterate_quadratic`).
5. **What replaces Lemma D for deep cores: a proposal, ruled out by `D-N.md`.** The blocked law does not change if the block grid
   is shifted by an independent uniformly random offset at each step (translation invariance; **paper**, exact).
   With random shifts a deep core sits at a block centre only with probability `L^{-d}` per step, and off-centre a
   core touches only a small fraction of the averaging paths. So a deep core becomes moderate within `n` steps except
   with shift-probability about `(C L^{1-d})^n` (**sketch**, section 2.5). Whether this replaces the missing fresh
   large-field factor within Balaban's constants was open; `D-N.md` answers **no**: the shifts buy at most `L^{-d}` per
   step, while Balaban charges every unrenormalised region `exp(O(1) log g^{-2} (M R)^d)` per step.
6. **Exactness of the conditional step: proved in Lean.** `ProofPhase.M1.map_resample_eq`: resampling a term on
   `Λ` from the reference kernel with the next field fixed, with ratio `N(W)/D(W)`, leaves the joint law of the next
   field and the outside field unchanged; so the next block field's law is unchanged (`map_comp_resample_eq`), term
   by term (`sum_map_resample_eq`). Hypotheses: measurability, the fibre-integral representation of `N`, `D`, and
   `0 < D < ∞` on the regular set. **Analyticity is not needed for exactness**, only for the estimates.
7. **Corrected verdict of the one-step test.** ONE-STEP said SURVIVES WITH A NEW LEMMA (Lemma D). Corrected:
   **SURVIVES for moderate cores (Lemma D-mod, proved on paper with Lean core); OPEN for deep cores at nested
   block centres** (the shift device is ruled out, `D-N.md`; the owner's root rule is scoped in `D-PIN.md`: survives
   with lemmas P0 and P2; `P0.md` constructs P0 as the twisted-sector average (core = carried Z2 label) and reduces P2
   to P2', subscale hole decoupling). Not BREAKS: no step
   was found that fails for every device. M1 grows by about 6-8 pages (`M1-PLAN.md`).

## 1. Reading

### 1.1 [IV] pp. 182-191, the general preliminary integration (full)

| equations | operation | exact? |
|---|---|---|
| (1.24) cont. | regularity conditions defining `χ^{(n)}_k` on all scales `h..k`, with margins `β`, `L_0` | definition |
| (1.25) | the `(n+1)`-st integration: `∫ dA_j … ∫ dV_j δ(V̄_j V_{j+1}^{-1}) ζ χ exp A^{(n)}` over `Z_{j+1} \ Z''_{j+1}` | δ kept: a conditional integral |
| p. 182 | `1 = χ^{(n+1)} + (1 - χ^{(n+1)})` per component of `Z`; components with the large-field function are removed from `Z` (stay as large-field regions) | exact partition |
| p. 182 | gauge fixing on `(Ω^{~-3}_{j+1})^c ∩ Z''^c_{j+1} ∩ T^{(j)}` by Faddeev-Popov | exact (integrand invariant) |
| (1.26)-(1.28) | approximate fluctuation field `V^{(j)}_Z`, restriction `χ'_j`, plaquette completion | exact partitions |
| (1.29)-(1.52) | proof that the new characteristic functions make the old ones (1.3)-(1.8) and `χ^{(n)}_k` equal to 1, using [14] (1.65), [12] (106)-(108), (159)-(163) | identity |
| (1.53)-(1.59) | fluctuation field `V'_j`, `B'_j`; linearisation, removal of the δ-functions by the operator `C`, scaling `B_j = g_j B'_j` as in [III] Sect. 3, "an equality" (p. 187); new partition `χ'^{(j)}` (1.55) and change of variables (1.59) | exact |
| (1.60)-(1.63) | the integral is localized in `Z`; its log gives new boundary terms `C^{(n+1)}_k`, `B^{(n+1)}_k` ((1.61)-(1.62)) with localization domains of a more general type (1.63) | identity |
| (1.64)-(1.69) | complex configuration spaces `Ũ^{(n)c}_k(X, α̃0, α̃1)` (analyticity domains), descending in `n` | definitions |

Consequences. (a) ONE-STEP row "preliminary integrations: same" is **confirmed**: every operation is an equality,
and the δ-functions linking `V_j` to `V_{j+1}` are kept until they are removed by an exact change of variables.
(b) The integrations act only on `Z_{j+1} \ Z''_{j+1}`: the deep part `Z''` (the core) is never expanded. (c) The
last `N` operations carry **no** large-field characteristic functions (condition (ii), [IV] p. 177 and (1.2)); the
small-field functions (1.3)-(1.9) sit on the shells `(Ω_j \ Ω_{j+1}) ∩ Z`. So the block fields `V_{h+1}, …, V_k`
over the core are never tested. This is why section 2.4 matters.

### 1.2 [V] pp. 364-373 (full)

| equations | content | role for M1 |
|---|---|---|
| (1.30)-(1.32) | the Wilson-action term after the cancellation; `0 ≤ A(ζ_1, U_0) < g_k² L^{-4N} N^{4β0} O(1) A0² B3² B5² M^{14} R_k⁴ p0²(g_k)` (1.31) | the old core's contribution is suppressed by `L^{-4N}` |
| (1.33)-(1.37) | new determining set `B_k`, new background `U_k = U_{B_k}(V)`, new Wilson term `-A(g_k^{-2}, U_k)` | identity |
| p. 366, (1.38)-(1.45) | analytic extension of the background over `Λ`: identity `V_Λ(M^k(U)) = V'_Λ(M̃^k(U')) V_Λ(M^k(U))`, critical-point equation (1.40) with bound `|B'_Λ| ≤ 4d(100M)^5 γ0^{-1} B3² |B̃'|` (1.41); existence from `[15]` Sect. G | this is the device D1 needs (a constrained version of the same fixed-point problem) |
| (1.46)-(1.48) | the term `A(ζ_1/(g''_k)², U''_{k,Z})`: its part linear in `H''_{h+2}` is `≤ O(1) A0 C1 B3³ B5 M^{10} p0 q1 R_k² L^{-N}` (1.47); then (1.48) | Balaban's own dilution: the old core enters the background through H-functions whose decay gives `L^{-N}`. Large core plaquettes: positivity of the G-valued action |
| pp. 368-369 | "it determines the number `N`" | `N` is fixed by this cancellation |
| (1.49) | `(1.1) = …`, an equality | identity |
| (1.50)-(1.58) | expansion of `U''_k` around `U_k` in four stages, using `[15]` Sects. D, E and [13] (3.148)-(3.153) | identity |
| (1.59)-(1.62) | localization of the E-, R-, B-terms as in [I] Sects. 3-6; resummation over final domains | identity + bounds |

Consequences. ONE-STEP row "localization: same (+D1)" is **confirmed**: the step is a sequence of expansions of
backgrounds and their analytic extension; a block constraint on `Λ` enters only through the background. Two
refinements: Balaban needs analyticity only of **backgrounds**, never of the core variables (they stay G-valued
inside a positive action); and the `L^{-N}` mechanism of (1.31), (1.47) is the background-level analogue of Lemma D.

### 1.3 The averaging far from the identity ([I] pp. 252-254, full)

* (0.3): contour family `G(y, x)`: shortest paths from the block centre `y` to `x`, one for each order of the
  directions with nonzero displacement.
* (0.4): `Ū(c) = exp[i ∑_{x∈B(c_-)} L^{-d} |G|^{-1}|G'|^{-1} ∑_{Γ,Γ'} (1/i) log U(Γ ∪ [x,x'] ∪ (-Γ') ∪ (-c))] U(c)`,
  where `U(c)` is the transport along the straight fine path of the coarse bond `c`. (0.12): same with one contour
  family and the straight path as reference.
* (0.5)-(0.9): axioms for averages `M({U_j})` of finite sets **near the identity** (inverse, two-sided covariance,
  permutation invariance, linearisation, `G`-valuedness); (0.10): Federbush's average (the critical point of
  `∑ log(U_j U^{-1})`). These are used for the contour variables (0.11), not for the bond average itself.
* p. 254: "both definitions are equally good …, we may use many other definitions"; renormalisation
  transformations are considered on regular configurations (small-field regions). In the large-field regions the
  operations `T` still contain `δ(V̄_j V_{j+1}^{-1})`, i.e. the average on arbitrary configurations.

**Answer to ONE-STEP's question.** Balaban does not discuss configurations far from the identity. His formula is
defined everywhere once `log(-1)` is fixed; with `log(-1) := 0` it is gauge covariant (loops based at `c_-` are
conjugated, `U(c)` multiplied on both sides), conjugation covariant and symmetric under the lattice rotations and
reflections about block centres ([I] p. 252 chose the contour family for that). It is **not robust**: section 2.4
shows that no extension with these symmetries can be.

### 1.4 The references Balaban's large-field papers rely on

From [I]'s reference list (pp. 299-301): `[12]` Balaban, Averaging operations for lattice gauge theories, CMP 98
(1985) 17-51; `[13]` Propagators for lattice gauge theories in a background field, CMP 99 (1985) 389-434; `[14]`
Spaces of regular gauge field configurations on a lattice and gauge fixing conditions, CMP 99 (1985) 75-102; `[15]`
The variational problem and background fields in renormalization group method for lattice gauge theories, CMP 102
(1985) 277-309; `[16]` Ultraviolet stability of three-dimensional lattice pure gauge field theories, CMP 102 (1985)
255-275. [IV] and [V] cite `[15]` Sects. D, E, G for the extension of backgrounds ([V] (1.43)-(1.54)) and "Theorem 1
[16]" for the constant `B3` ([IV] p. 191).

**Needed for M1:** `[15]` (the constrained minimiser, row V1 of `M1-PLAN.md`), `[12]` (properties of the average,
rows D-mod constants and D-prob), `[14]` (regular gauges). All three are open access on Project Euclid; none is in
the repository. **Owner action:** run `pwsh -File get-balaban-refs.ps1` in this folder (PDFs are git-ignored here).

## 2. Lemma D, corrected

### 2.1 What ONE-STEP asked

(D1) the constraint `V̄_k = W` solvable by shell variables, analytic in `W`, uniformly in the core variables; (D2)
if `W` is irregular over a block meeting the core, the same holds with the core replaced by a regular filling, so a
**fresh** large plaquette exists outside the core. Both were to follow from a deterministic statement: after `n`
steps the core is invisible up to `π cⁿ`, `c < 1`, for a suitable extension of the averaging.

### 2.2 The star weights at a block centre (paper, exact; `star_weights.py`)

Fix a coarse site `y` (a block centre) and perturb the `2d` fine bonds of its star, `U(b) → e^{i a_b} U(b)` for
`b = (y, y ± e_μ)`, around the trivial field (a regular background in a gauge near 1 adds `O(ε)`, section 2.3).
Linearised, (0.4) is the weighted mean of the fine bond variables along the paths (the reference `U(c)` cancels at
linear order because the weights sum to 1). For the coarse bond `c = (y, y + L e_ν)`:

* the second half of every path (segment end, `Γ'` in `B(y + L e_ν)`) never meets the star of `y`;
* for `x ≠ y`, a path `Γ ∈ G(y, x)` uses exactly one star bond, its first one, and the law of that first bond does
  not depend on `c`;
* `x = y`: `Γ` is empty and the segment starts with the star bond `+ν`;
* `x = y - t e_ν`, `1 ≤ t ≤ (L-1)/2`: `Γ` leaves along `-ν` and the segment comes back through `y` and leaves along
  `+ν`; at linear order the `-ν` bond cancels and the path counts as `+ν`.

Hence `F(c, b) = q + e₁ [b = c] - e₂ [b = -c]`, `e₁ = (L+1)/(2Lᵈ)`, `e₂ = (L-1)/(2Lᵈ)`, `q = (1 - L^{-d})/(2d)`
(row sums 1). `star_weights.py` enumerates the contour family with exact fractions: `L = 5, d = 2` and
`L = 13, d = 4` (`q = 3570/28561`) both match. The Dobrushin coefficient is
`max_{c,c'} ½ ∑_b |F(c,b) - F(c',b)| = e₁ + e₂ = L^{1-d}` (`1/2197` for `L = 13`, `d = 4`).

Meaning: a common shift of all `a_b` (a gauge transformation at `y`) passes unchanged; the **spread**
`max ‖a_b - a_{b'}‖`, which is what plaquettes at `y` see, shrinks by `L^{1-d}` per step.

### 2.3 Lemma D-mod (moderate cores)

**Statement.** Let `y` be a site of the scale-`m` lattice for `m = m0, …, m0 + n`, and compare two configurations
that agree outside the stars of `y` (at scale `m0`) and are `ε`-regular outside them. Let `s_m`, `ŝ_m` be the spreads
of their scale-`m` stars at `y` (bi-invariant distance of `g_b g_{b'}^{-1}`, in a gauge where the background is within
`O(ε)` of 1) and `Δ_m` the spread of the difference. If `s_m, ŝ_m ≤ r0` (a fixed small absolute number) then
`Δ_{m+1} ≤ θ Δ_m` with `θ = L^{1-d} + K r0 + K' ε`, and so `Δ_{m0+n} ≤ θⁿ Δ_{m0}`.

**Proof (paper).** On the ball where all logarithms are within `1/2` of 0, the map "star at scale `m` ↦ star at scale
`m+1`" is analytic in the relative coordinates `a_b - a_{b_*}` and in the background. At zero spread and trivial
background its derivative on relative coordinates is `F` of 2.2, whose operator norm in the spread seminorm is the
Dobrushin coefficient `L^{1-d}` (`norm_wsum_sub_wsum_le`, `starW_tv_le`, `balaban_e_sum`: **Lean**). The BCH terms
of `log(e^{ia} e^{iρ} e^{-ia'})` are bilinear, `O(|a - a'|(|a| + |a'| + |ρ|))`, so the derivative at spread `≤ r0`
and background `ε` differs from `F` by `O(r0 + ε)`; the mean-value inequality along the segment between the two
stars gives `Δ_{m+1} ≤ (L^{1-d} + K r0 + K' ε) Δ_m`. Iteration: `spread_iterate_le`, `geom_of_quadratic`,
`spread_iterate_quadratic` (**Lean**). Location: a core of diameter `D_h` at scale `h` lies, after
`n1 = ⌈log_L D_h⌉ + 1` steps, in at most `2^d` blocks; one off-centre step moves its influence onto the stars of the
corresponding coarse sites, with factor at most the fraction of paths through it (`< 1`; `star_weights.py … off`
gives `0.36` for `L = 5, d = 2`); from then on each is a centre case. **Not computed:** `K`, `K'` (they come from the
analyticity bounds of [12]; routine).

**For M1.** If, for a renormalisable component, the images of the core are moderate at some scale `≤ k - n_mod` with
`θ^{n_mod} r0 ≤ g_k²`, i.e. `n_mod ≥ log(r0 g_k^{-2}) / log(1/θ) = O(log g_k^{-2} / log L)`, then (D1) and (D2) hold
as ONE-STEP section 3 derives them (forced shift `≤ g_k² ≪ δ'_k`; core-replaced field within `g_k²` of the true one,
so an irregular `W` has a large plaquette outside the core up to a margin Balaban's factor-2 thresholds absorb).

### 2.4 Deep cores: vortex persistence (Lean + paper)

**Theorem (`ProofPhase.M1.vortex_persists`, Lean).** Let `z` be central in `G` and `B_n` (scale `n` to `n+1`) block
maps such that, for a site `y` that is a coarse site at all scales considered, with stars `S_n`:
(i) `B_n(flip_z U) = flip_z(B_n U)`, `flip_z` = multiply the bonds of the star of `y` by `z` (gauge transformation
by `z` at `y`); (ii) `B_n(v U v⁻¹) = v B_n(U) v⁻¹` (global conjugation); (iii) `B_n(U ∘ ρ) = B_n(U) ∘ ρ` for a lattice
rotation `ρ` about `y`; (iv) locality: a coarse bond off the star reads no fine bond of the star, and trivial input
gives trivial output. Let `U₀` be central-valued, trivial off the star, with `U₀ ∘ ρ = flip_z U₀`. Then at every
scale `n` the `n`-fold block field is central-valued, satisfies the same relation, and every coarse plaquette with
two sides `c, ρ c` in the star and two sides off it has holonomy `z⁻¹`.

**Instance.** `G = SU(2)`, `z = -1` (`su2NegOne`, central, `≠ 1`, its own inverse: Lean). `U₀ = -1` on the fine bonds
`(y, y ± e_3)`, `(y, y ± e_4)`, `1` elsewhere; `ρ: 1 → 3, 2 → 4, 3 → -1, 4 → -2` (a rotation). Then `ρ` maps `U₀` to
its gauge transform by `-1` at `y`. Every coarse plaquette at `y` in the planes `(1,3), (1,4), (2,3), (2,4)` equals
`-1` at every scale at which `y` is a coarse site.

**Balaban's average has (i)-(iv)** (paper): (i), (ii) are gauge covariance of (0.4) (with `log(-1) := 0`, the
principal log is conjugation covariant everywhere); (iii) is the Euclidean symmetry of the contour family ([I]
p. 252); (iv): `Ū(c)` reads only `B(c_-) ∪ B(c_+)`, and blocks partition the lattice. With a non-covariant choice
`log(-1) := iπσ` the same configuration gives `Ū(+1) = exp(i(Σ f)πσ)`, `Ū(+3) = exp(i(Σ f)πσ)(-1)` with equal sums
by symmetry, so the plaquette is again `-1` (hand computation).

**Consequences.**
* The deterministic Lemma D of ONE-STEP is false for every extension of the averaging that keeps gauge covariance
  and the lattice symmetry (both of which Balaban's small-field theory uses). The "one risk" of ONE-STEP section 3
  is real.
* Condition (ii) of [IV] p. 177 does not exclude it (1.1 (c)). A renormalisable component can contain such a core
  if its site is a coarse site from scale `h` to `k+1`. Then `W` is irregular over the core, `D_X(W) = 0` (branch
  (a)), the shell can be perfectly regular, and **no fresh factor exists**: (D2) fails. (D1) fails near it as well
  (the average is discontinuous at the logarithm's cut).
* Whether the vortex is an isolated (unstable) persistent configuration or the centre of an open persistent set is
  **open**. It does not matter for the verdict: either way no uniform `π cⁿ` bound exists.
* Unit tests (RULES.md): this is a statement about block maps, not about a gap; it holds verbatim for U(1) and Z2 and
  claims nothing about them.

### 2.5 Replacement for deep cores: shift-averaged blocking and Lemma D-prob (sketch, open)

**Shifts are free (paper, exact).** On the torus the bare Wilson law is invariant under all lattice translations.
Let the block grid at step `j+1` be shifted by `s_j ∈ {0, …, L-1}^d` (scale-`j` units): `V_{j+1} = B(T_{s_j} V_j)`.
By induction the law of `V_j` is invariant under scale-`j` translations (`B` commutes with coarse translations), so
`T_{s_j} V_j` has the law of `V_j`, and the law of `V_k` is the same for every shift sequence. Hence the proof may use
i.i.d. uniform shifts, independent of the fields, at no cost; Balaban's construction runs on every shifted grid with
the same constants (it is translation covariant).

**Escape (sketch).** Fix any configuration; let a core sit at a fine site `z` (scale `m`). Under a uniform shift,
`z` is a block centre with probability `L^{-d}`; it lies on one of the `d` coordinate axes through the centre (where
the reference path of (0.4) passes through it) with probability `≤ d L^{1-d}`; otherwise the reference loops are
regular, the core enters a fraction `f(z)` of the loops, and each such loop contributes a logarithm of size `≤ π`, so
the coarse star moves by `≤ f(z) π + O(ε)`. If `f(z) ≤ C |z - y'|^{1-d}` (paths through a point at distance `R`
from the centre form a cone; **to be proved**, numerically checkable with `star_weights.py`), then the core's image is
moderate (`≤ r0`) except with probability `p_stay ≤ d L^{1-d} + (2R0 + 1)^d L^{-d}`, `R0 = (Cπ/r0)^{1/(d-1)}`, i.e.
`p_stay = O(L^{1-d})`. After escape, Lemma D-mod applies. So, **for every core configuration**, the shift-probability
that the core is still deep after `n` steps is `≤ p_stayⁿ` (independence of the shifts).

**Lemma D-prob (target).** With i.i.d. uniform shifts, for every configuration and every core of diameter `≤ D_h` at
scale `h`, `P_shift(the core's image at scale h + n1 + n_esc + n_mod is not within g_k² of the core-replaced one)
≤ p_stay^{n_esc}`. Status: **open** (sketch above; the cone bound on `f(z)` and the multi-site bookkeeping are the
two missing pieces, about 4 pages).

**Update (`D-N.md`): the shift device does not work inside Balaban's bookkeeping.** `p_stay ≥ L^{-d}` (exact
centres), while every step a region stays unrenormalised costs `exp(O(1) log g^{-2} |Z_j|)`, `|Z_j| ≥ (M R)^d` ([V]
p. 380). The persistent terms' bounds grow with every step, for any `N`. Section 2.6 is kept as the record of the
original proposal; its constraint on `N` turns out to be satisfiable after removing an artefact ([IV] p. 198) and
retuning `p0, p1, β0`, but that does not rescue the device. Deep pinned cores: open, next idea I1 in `D-N.md` 4.

### 2.6 What D-prob would buy, and the constraint on N (superseded by `D-N.md`)

With D-prob, a term whose core is still deep after `n_esc` steps carries the shift factor `p_stay^{n_esc}` (a weight
of the shift mixture, not a factor of the field density). For it to replace a fresh large-field factor
`exp(-p0(g_k))` one needs `n_esc ≥ p0(g_k) / log(1/p_stay) ≈ A0 (log g_k^{-2})^{p0} / ((d-1) log L)`, i.e.
Balaban's `N ≤ O(1)(log g^{-2})^ν` with `ν ≥ p0`. His side condition `½ν ≤ p0 - p1 - 1` ([IV] p. 198) then needs
`p0 ≥ 2p1 + 2`; and the entropy of recent regions (`L^{4N}` against `exp(-p0)`, `BALABAN-READING.md` 2.5) is then at
equal powers of `log g^{-2}` and needs `A0 > 4 log L` times a constant. Whether all of Balaban's constraints
((1.80)-(1.85), (1.89), p. 389) tolerate `ν = p0` is **open** (1-2 pages of bookkeeping). Alternative without shifts:
let the deep core's own Wilson factor `exp(-c r0²/g_h²)` pay for persistence; it gains only `2β0 c r0² log L` per step
against Balaban's per-step cost `O(1) M^d R^{d+1}`, so it does not pay for long persistence. The shift device is the
better candidate.

## 3. Exactness of the conditional step (Lean, `formal/ProofPhase/M1/Exact.lean`)

Setting of ONE-STEP 2.1, measure-theoretic. A term is the measure `ν.withDensity I` on the current configuration
`x : α`. The next blocking factors through a measurable `φ : α → γ` (in M1, `φ x = (W, V_out)`). `ŵ` is the reference
kernel, `Reg ⊆ γ` the regular set, `N`, `D : γ → [0, ∞]` the fibre integrals, given as densities against a reference
measure `λ` on `γ`: `φ_*(ν.withDensity I) = λ.withDensity N`, `φ_*(ν.withDensity ŵ) = λ.withDensity D` (this is the
measure-theoretic meaning of `N(W) = ∫ dV δ(V̄ W⁻¹) I(V)`). The step is `resample φ I ŵ N D Reg x = ŵ x · N(φ x)/D(φ x)`
if `φ x ∈ Reg`, `I x` otherwise (branch (a) left unrenormalised).

| Lean name | exact statement |
|---|---|
| `map_resample_eq` | measurable `φ, I, ŵ, N, D`, measurable `Reg`, the two representations, `D y ≠ 0` and `D y ≠ ∞` for `y ∈ Reg` ⟹ `(ν.withDensity (resample φ I ŵ N D Reg)).map φ = (ν.withDensity I).map φ` |
| `map_comp_resample_eq` | the same for `.map (ψ ∘ φ)`, any measurable `ψ` (the next block field: `T R̂ = T`) |
| `map_resample_rnDeriv_eq` | finite measures, `φ_*(I ν) ≪ φ_*(ŵ ν)` ⟹ resampling with the Radon-Nikodym derivative `d φ_*(Iν)/d φ_*(ŵν)` preserves `φ_*(Iν)` (no fibre densities, no regular set) |
| `sum_map_resample_eq` | the same for a finite sum of terms, each with its own `I, ŵ, N, D, Reg` (the history sum, term by term) |
| `measurable_resample` | the resampled density is measurable |

Axioms: `propext, Classical.choice, Quot.sound` only (`axioms.log`). Several disjoint components: apply the theorem
once per component (each resampling preserves the law of `φ`, and the next one starts from the resampled term).

**Named hypotheses and what they mean in M1.** (H1) fibre representation: `N`, `D` are the δ-function integrals of
ONE-STEP 2.1 against Haar measure on the fibres (paper, routine: the block map is a submersion on regular
configurations, [12]). (H2) `0 < D(W) < ∞` for regular `W`: the constrained minimiser lies in the fibre and in the
support of `ŵ` (needs row V1 of `M1-PLAN.md`, the constrained Proposition 1). Analyticity of `D` is **not** a
hypothesis of exactness; it enters the estimates (E3, E6 of the plan). The intermediate `R̂ρ_k` is not the law of
`V_k` (it resamples `V_k|Λ` in the fibre of `W`); nothing downstream reads `V_k` except through `φ`.

## 4. Files

- `NOTE.md` (this file), `M1-PLAN.md` (the estimate list), `D-N.md` (row D-N: the delay and the shift device),
  `D-PIN.md` (row D-pin: one root per pinned core), with `star_dynamics.py`, `near_vortex.py`, `zlift_traps.py`;
  `P0.md` (the twisted-sector average), with `twist_dynamics.py`; `NO-TRAP.md` (the `L = 13` off-centre step, local
  contraction, slow balanced stars, cut avoidance), with `offcentre_L13.py`, `notrap_search.py`,
  `notrap_longsearch.py`, `cut_avoidance.py`, `cut_adversarial.py` and their `run_*.log`; `NT-A.md` (NT′(a), proved;
  `formal/ProofPhase/M1/CutAvoid.lean`), `NT-B.md` (NT′(b′) reduced to the Cap Lemma, with `nt_b.py`, `cap_fixed.py`), `S6-START.md` (§6: V1 from `[15]`). `TRAP.md` (trapping of deep cores, the owner's proposal:
  root once + maintenance; replaces cut avoidance on the critical path). `E3.md` (§6 row E3: the constrained denominator). `E5-E9.md` (§6 rows E5-E9; Lemma E7.J, fibre mass, open),
  `TRAP-CHECKS.md` (trapping checks T1-T4), `formal/ProofPhase/M1/Assembly.lean` (§8: `m1_assembly`,
  `m1_assembly_rows`). `E7J.md` (fibre mass, proved), `POINCARE.md` (block-axial Poincaré), `V1-EXCISION.md` (T3), `V1-INPUTS.md` (its two inputs), `S1-ROWS.md` (inductive form, every row stated),
  `formal/ProofPhase/M1/LocalMod.lean`, `ROUTINE-ROWS.md` (the routine rows), `formal/ProofPhase/M1/Routine.lean`, `S1-PROOF.md` (§8 bookkeeping),
  `EXTERNAL.md` (what M1 rests on outside itself),
  `formal/ProofPhase/M1/FibreMass.lean`.
- `TWIST.md` (the twisted blocking on the full lattice, link reflection positivity, multi-site tests; with
  `lattice_twist.py`, `run_lattice_d34.log` and `formal/ProofPhase/M1/Twist.lean`), `P2-PRIME.md` (subscale-hole
  decoupling, sketch). `M1-PLAN.md` is now the outline of the accompanying paper plus the estimate inventory.
- `star_weights.py`: exact linear star weights of Balaban's contour family (`python -I star_weights.py 13 4`, 13 s;
  add a third argument for the off-centre maximum, small `L, d` only).
- `get-balaban-refs.ps1`: downloads `[12]`, `[14]`, `[15]` here (done by the owner; PDFs git-ignored).
- `setup.sh`, `build.sh <Module>`, `axioms.sh`, `axioms.log`, `grepml.sh`: private WSL build (`~/formal-m1`).
- Lean: `formal/ProofPhase/M1/Exact.lean`, `Dilution.lean`, `Vortex.lean`; build each with
  `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/m1-tools/build.sh Exact`
  (likewise `Dilution`, `Vortex`). No `sorry`, no new axioms, no `native_decide`.
