# Cycle 5, workstream 3 (c5c-repair): making the W1 inputs satisfiable (2026-11-22)

Brief: blueprint v4 draft step 3 (`../c4-fable/BLUEPRINT-v4-DRAFT.md` §3.4, §7), review `../c4-fable/REVIEW.md` §1.1 to 1.3.
Lean: `formal/ProofPhase/Repair/` (five new modules, all built in `~/formal-c5c`, no `sorry`, no new axiom, no
`native_decide`; `axioms.sh` prints `[propext, Classical.choice, Quot.sound]` for all 34 theorems listed in `axioms.lean`).
No existing file was edited.

Marks: **S** = proved in Lean (substantive), **D** = proved, definitional or bookkeeping, **H** = named hypothesis (open),
**P** = on paper only.

---

## 0. Result in one paragraph

The three statement defects are removed without weakening anything that was proved. (1) **Finite range:** a weighted W1
Dobrushin theorem (`theoremA_Ww`, single-site form `decay_of_siteWw`) needs only exponentially weighted column sums
`sum_{i != z} k(i,z) e^{lam d(z,i)} <= gamma < 1`; the new level hypothesis `LevelDprimeWw` (no `D1`) gives
`BlockGapUnifW`, and v4's `BlockGapBddW` / `LawGapBddW`; the old `LevelDprimeW` implies it. (2) **Plaquette-only limit:** the
Gibbs layer of the library was already general-support (`CoarsePot` is one term per finite link set); only `Vinf` and
`LimitDprimeW` were plaquette-bound. `regroup` turns any family of terms (plaquettes, rectangles, any loops) into a
`CoarsePot` with the same Gibbs measure and the same conditional laws. The pair is replaced by `RefDprimeWw` (a reference
action of any support, weighted column `<= gamma`) and `CloseWw` (eventually `<= eps0`, no limit, no range); the old pair
implies the new pair. Verdict on the draft's alternative: delete the pair from the top statement (use `LevelDprimeWw` only),
keep the repaired pair as a lemma. (3) **Gibbs representation:** a `NoisyRPBlocking` structure (block variable = image of
fine field and independent noise), reflection positivity proved for every such blocking (`noisy_blocked_wilson_rp`), the
multiplicative noisy good blocking built and shown to be one (`mulNoiseBlocking`, `goodNoisy_rp`), and the Gibbs clause
proved for any noisy blocking whose kernel has a density in `[m, M]` (`noisy_blockedLaw_gibbs`). Not proved in Lean: that
the heat-kernel noise has such a kernel density (paper, §3.2; Haar invariance), and nothing about the Dobrushin columns of
the true theory, which remain the content.

---

## 1. Weighted W1 Theorem A (task 1) — `Repair/WeightedW.lean`

### 1.1 Statements

* `lipBound_avg_w`, `cov_le_weighted_Ww` (S): the contraction step and core covariance bound of Theorem A (W variant,
  `g` Lipschitz for a cost `0 <= c <= D_c`) under the weighted block condition `Attempts.R3.GDSw P.block k e gamma`
  (`sum_{j : x notin B_j} k_j(x) e_j(x) <= gamma c(x)`) for any weight `w` with `w(y) <= e_j(x) w(x)` for `x notin B_j ni y`.
  Line-by-line merge of `OneScale.BlockSpec.theoremA_W` (W bookkeeping) and `Attempts.R3.theoremA_w` (weights).
* **`theoremA_Ww`** (S): with `E_j(x) >= dist(x, y)` for `x notin B_j ni y`, `lam >= 0`, `0 <= gamma < 1` and
  `GDSw P.block k (fun j x => e^{lam E_j(x)}) gamma`:
  `|Cov(f, g)| <= b D_c / (c_min (1 - gamma)) (c_max sum_A v_a) L_g e^{-lam (R - D0)}`.
* `WeightedColumnW k dist lam gamma` (D): `forall z, sum_{i : z notin {i}} k i z * e^{lam dist z i} <= gamma`.
* **`decay_of_siteWw`** (S): single sites, `Potential supp V`, `SiteInfluenceW nu supp V c k`, `WeightedColumnW k dist lam
  gamma`, `gamma < 1`: `|Cov_{gibbs}(f, g)| <= D_c/(1 - gamma) (sum_A v_a) L_g e^{-lam R}`. No range, no `D1`.
* `weightedColumn_le_of_range` (S): nonnegative coefficients, column `<= gamma`, range `D1` give
  `WeightedColumnW k dist lam (gamma e^{lam D1})`. `WeightedColumnW.mono` (S): monotone in the rate.
* `siteInfluenceW_nonneg`, `exists_geodSU2_pos` (S): W1 coefficients are automatically `>= 0` when the cost takes a
  positive value; `geodSU2(-1, 1) = pi`. (Needed so the finite-range form is a special case.)
* **`LevelDprimeWw T B lam`** (H, replaces `V3.LevelDprimeW`):
  `exists gamma, 0 <= gamma, gamma < 1, exists k0, forall k >= k0, forall j, exists V : CoarsePot j,
  blockedLaw T B k j = gibbsMeasure haar V and Potential (fun A => A) V and exists kk,
  SiteInfluenceW haar (fun A => A) V geodSU2 kk and WeightedColumnW kk linkDist lam gamma`.
* **`blockGapUnifW_of_levelDprimeWw`** (S): `0 <= lam`, `LevelDprimeWw T B lam => BlockGapUnifW T B lam`, constant
  `pi/(1 - gamma)`.
* **`levelDprimeWw_of_levelDprimeW`** (S): `0 <= lam`, `LevelDprimeW T B lam => LevelDprimeWw T B lam`.
* `LevelDprimeWw.mono` (S), `bothOrdersLoc_of_levelDprimeWw` (S: with `ObsTransferPhysTW`, the gap for bounded physical
  extent in both orders of limits, through v3's cut).

### 1.2 Claim discipline

The weighted theorem is standard (weighted Dobrushin uniqueness, Dobrushin 1970, Gross 1979; recalled), proved here in
Lean: substantive as a formalisation, not new mathematics. `LevelDprimeWw` has the same strength as `LevelDprimeW` minus
the range clause: it is strategy (a)'s D′ condition for the true blocked law, of gap strength at the working `L1` in the
sense of review §2. The repair changes what the hypothesis can be met by, not how strong it is.

### 1.3 Coordination with c5d (rare defects)

c5d's `Defects/Quenched.lean` uses `OneScale.BlockSpec.cov_le_weighted_W` with a finite range in the effective metric
`effDist`. `Repair.cov_le_weighted_Ww` takes the same abstract weight `w` with the per-block factor `e_j(x)` instead of one
global `E`, so with `w = effWeight` and `e_j(x) = e^{lam E_j(x)}` (`E_j(x)` an effective-distance bound) it gives the
defect theorem without the finite range in `rho` as well. No duplication: c5d owns the random-defect statement; this file
owns the deterministic weighted one.

---

## 2. General-support potentials (task 2) — `Repair/GeneralSupport.lean`

### 2.1 What was already general, what was not

`Attempts.R3.Potential supp V` and `gibbsMeasure` take any finite family of terms with any supports, and
`CoarsePot j = Finset (links) -> config -> R` (one term per link set) is the general-support class itself. So the level
potentials `Vk` of `H1LocalLipW` were never the problem. The plaquette restriction sat in two places only: `Vinf :
LatticePlaquette -> ...` with support `plaqSupp` in `H1LocalLipW`, and range 1 plaquette supports in
`Certified.LimitDprimeW`. Plus `D1` and `eps -> 0` in `H1LocalLipW`.

`Potential.bdd` is a per-volume sup bound (`exists K, forall x sigma, |V x sigma| <= K`), not uniform in the volume, so the
"quasi-local class" with exponentially weighted sup sums is not needed for the Gibbs clause; what the Dobrushin theorem
consumes is the weighted influence column, which is a property of the conditional laws and does not depend on how the
potential is split into terms (`siteSpec_regroup`). So the general-support class is stated at the level of influences.
(A sup/Lipschitz-norm envelope `sum_{A ni i, z} ||V_A||_Lip e^{lam diam A}` implies a weighted column on paper, by c3c §5's
per-term bound `pi eta + (3 pi/2) G (e^{2 eps} - 1)`; not formalised: P.)

### 2.2 Statements

* `regroup supp V : Finset iota -> config -> R`, `regroup supp V A = sum_{x : supp x = A} V x` (D).
* `potential_regroup` (S), `siteLog_regroup`, `totalLog_regroup` (S), **`siteSpec_regroup`** (S),
  **`gibbsMeasure_regroup`** (S), `siteInfluenceW_regroup` (S, iff): same Gibbs measure, same single-site
  specifications, same W1 coefficients. Any fitted action with plaquettes, 1x2 rectangles, larger loops (any finite
  supports) is a `CoarsePot` without loss.
* `influenceDevW_nonneg` (S).
* **`RefDprimeWw Vref lam gamma`** (H, replaces `LimitDprimeW`): `forall j, exists kk, SiteInfluenceW haar (fun A => A)
  (Vref j) geodSU2 kk and WeightedColumnW kk linkDist lam gamma`. `Vref j : CoarsePot j`, any supports, no limit.
* **`CloseWw T B Vref lam eps0`** (H, replaces `H1LocalLipW`): `exists k0, forall k >= k0, forall j, exists V : CoarsePot j`,
  the blocked law is `gibbsMeasure haar V`, `Potential V`, and the W1 boundary derivatives of `V`'s single-link laws
  differ from those of `Vref j` by `delta` (`InfluenceDevW`) with `WeightedColumnW delta linkDist lam eps0`. "Eventually
  `<= eps0`", as the draft asks.
* **`levelDprimeWw_of_ref`** (S): `0 <= gamma`, `0 <= eps0`, `gamma + eps0 < 1`, `RefDprimeWw Vref lam gamma`,
  `CloseWw T B Vref lam eps0` give `LevelDprimeWw T B lam`.
* `refDprimeWw_of_limitDprimeW` (S): `LimitDprimeW Vinf => exists gamma < 1, forall lam >= 0, RefDprimeWw (regroup
  plaqSupp Vinf) lam (gamma e^lam)`. So `limitDprimeW_twoCoupling` and `limitDprimeW_measured` (certified, under their
  computational hypotheses) feed the new pair.
* **`ref_close_of_h1LocalLip`** (S): `H1LocalLipW T B Vk Vinf and LimitDprimeW Vinf => exists lam > 0, gamma, eps0 >= 0,
  gamma + eps0 < 1, RefDprimeWw (regroup plaqSupp Vinf) lam gamma and CloseWw T B (regroup plaqSupp Vinf) lam eps0`
  (explicit: `lam = lam0 / max(1, D1)`, `gamma'' = (1 + 3 gamma)/4`, `eps0 = (1 - gamma)/4 e^{lam0}`).
  `levelDprimeWw_of_h1LocalLip` (S): the old openness lemma re-derived through the new chain.
* `refDprimeWw_wilson` (S, under the computational input `CertifiedAdjointW`): model case, §5.

### 2.3 Repair or delete? Both, in different places

* **As an input of the top theorem: delete** (draft S5 is right there). `LevelDprimeWw` is implied by the pair
  (`levelDprimeWw_of_ref`), is weaker, and is exactly what is consumed. c5a's v4 already consumes only the law-level D′
  (`LevelDprimeWOn`) in strategy (a); the weighted replacement is `LevelDprimeWwOn` (§4).
* **As a lemma: keep the repaired pair.** It is the only bridge from a certificate about one fixed fitted action (the
  certified windows of c3c, c4d) to the level condition, and its closeness clause is where the rare-defect form (c5d)
  plugs in: `CloseWw` is a worst-case statement (every boundary condition), review §1.4; the annealed version should
  replace `CloseWw`, not `RefDprimeWw`.
* The limit itself is gone: `Vref` is any reference action, and `eps -> 0` is replaced by `eps0 < 1 - gamma` from some
  level on (c3d had shown the limit is not needed).

---

## 3. Noisy local blocking (task 3) — `Repair/Noisy.lean`, `Repair/MulNoise.lean`

### 3.1 The structure and what is proved

* **`NoisyRPBlocking G d N M Y0 Yp`** (D): a block map `B : (fine field) -> Y0 x Yp x Yp -> (coarse field)` with
  `meas` (jointly measurable), `theta` (`B (Theta U) (c, a', a) = Theta (B U (c, a, a'))`: the reflection swaps the
  positive noise `a` and the negative noise `a'`, fixes the plane noise `c`), `half` (a coarse observable of the closed
  positive half reads only the closed positive fine half, `c` and `a`). The noise law is `nu0 x nup x nup` (the same law on
  `a` and `a'`: that is the reflection invariance of the noise).
* `RPBlocking.toNoisy` (D): trivial noise (`Unit`). `blocked_wilson_rp_of_noisy` (S): the old RP theorem re-derived.
* **`noisy_rp_fixed`, `noisy_blocked_wilson_rp`** (S): for every bounded measurable `F` of the closed coarse positive
  half and every `beta`:
  `0 <= int dnu0(c) int d(nup x nup)(a, a') int F(B(U,c,a,a')) F(Theta B(U,c,a,a')) prod_p e^{beta xp(U)} dHaar(U)`.
  Proof: `F(B(U, c, a, a')) = G_c(a, U)` and `F(Theta B(U, c, a, a')) = G_c(a', Theta U)`; swap the noise and field
  integrals (bounded, Fubini) and integrate out `a, a'` (`integral_prod_mul`): the inner integral is
  `int H_c(U) H_c(Theta U) e^{-S_W} >= 0`, `H_c(U) = int G_c(a, U) dnup(a)`, a positive-half function (`wilson_rp`).
* **`mulNoise`, `mulNoise_theta`, `mulNoiseBlocking`** (S): the multiplicative noisy blocking of any `RPBlocking P`:
  with `b = P.B U`,
  - fixed (plane) link `l`: `phi_l = b_l c_l`;
  - positive link `l`: `phi_l = b_l a_l`;
  - mirror `l = m(p)` of a positive link `p`: `phi_l = b_l a'_p` (spatial), `phi_l = (a'_p)^{-1} b_l` (temporal).
  It satisfies the three fields (`mulNoise_theta`: `Theta(mulNoise b (c,a,a')) = mulNoise (Theta b) (c,a',a)`).
* **`goodNoisyFamily T w n hn tau`** (D) and **`goodNoisy_rp`** (S): the good blocking (`RouteA.goodBlocking`) followed by
  i.i.d. noise of single-link law `tau` on every coarse link; every layer reflection positive, for every probability
  measure `tau` on SU(2).
* **`gibbs_of_density`** (S): a probability law on `iota -> S` with density `rho` w.r.t. the product measure,
  `0 < m <= rho <= M`, measurable, is `gibbsMeasure nu V` for a bounded `Potential (fun A => A) V` (one global term
  `log rho`).
* **`map_prod_eq_withDensity`** (S): if for every fine field `x` the noise pushes forward under `Phi(x, .)` to the law
  with density `kappa(x, .)` (jointly measurable, in `[m, M]`), the blocked law `(mu x eta) o Phi^{-1}` has density
  `int kappa(x, .) dmu(x)`, again in `[m, M]`.
* `KernelDensity NB k j` (H, a property of a concrete family): such a `kappa` exists at level `k`, volume `j`.
* **`noisy_blockedLaw_gibbs`** (S): `KernelDensity NB k j => exists V : CoarsePot j, Potential V and noisyBlockedLaw NB k j
  = gibbsMeasure haar V`. This is review §1.3 removed: for a noisy blocking with a kernel density, the Gibbs clause of
  every D′ input holds at every level and in every volume.
* `NoisyBlockingFamily T Y0 Yp`, `noise`, `joint`, `noisyBlockedLaw`, `noisyFamily_rp` (S), `BlockingFamily.toNoisy`,
  **`blockedLaw_toNoisy`** (S): the deterministic family is the trivial-noise case with the same blocked laws.

What the Gibbs clause does **not** give: a single global term has the right conditional laws but no locality. Locality of
the blocked law is entirely in the weighted column of `LevelDprimeWw` / `CloseWw`. The noise removes a representation
problem, not the content.

### 3.2 The concrete heat-kernel noise (P)

Take `tau = h dHaar` with `h` the SU(2) heat kernel at a time `t > 0` (or any `h` that is measurable, a class function,
inversion symmetric, with `0 < m_h <= h <= M_h`; the heat kernel is all of these).

* **Kernel density (P, the missing Lean piece).** For fixed `U`, the coarse links of `mulNoise (P.B U) eta` are
  independent. For `phi_l = b_l x` with `x ~ h dHaar`, left invariance gives density `h(b_l^{-1} phi_l)`. For
  `phi_l = x^{-1} b_l`: `x^{-1} ~ h(g^{-1}) dg = h dg` (inversion invariance of Haar, symmetric `h`), right invariance
  gives density `h(phi_l b_l^{-1}) = h(b_l^{-1} (phi_l b_l^{-1}) b_l) = h(b_l^{-1} phi_l)` (class function). So
  `kappa(U, phi) = prod_l h(b_l(U)^{-1} phi_l)`, between `m_h^{|E|}` and `M_h^{|E|}` (`|E| = 4 (coarseSide j)^4`; the bounds
  may depend on the volume, `Potential` is per volume). Joint measurability: `P.B` measurable, `h` measurable. Lean: about
  a hundred lines (reindex `Measure.pi` along `linkSplit`, `map_mul_left_eq_self`, withDensity under a measurable
  equivalence); next step 1.
* **Locality.** `phi_l` depends on `b_l` (the smeared transports near the coarse link, local) and one noise variable.
* **Gauge covariance (in law, P).** If `b(U^G) = b(U)^g` (true for the good blocking off the null set where a path sum
  vanishes; `RouteA/Blocking.lean` docstring), the kernel `K(b, dphi) = prod h(b_l^{-1} phi_l) dphi_l` satisfies
  `K(b^g, .) = K(b, .)^g`: `h((g_x b g_y^{-1})^{-1} g_x phi g_y^{-1}) = h(g_y b^{-1} phi g_y^{-1}) = h(b^{-1} phi)`. So the
  noisy blocked law is gauge invariant. Pointwise covariance fails (the noise is not transformed); only the law matters.
* **Bounded score.** `d log h` is bounded for the heat kernel, which is what c4a §2.2 uses to get parts (a), (b) from
  conditional mixing and c4a §2.3 for the envelope.
* **Content trade-off.** Small `t` keeps the block variable informative (the content question, review §2.2, c5b) and
  makes `m_h` small; the representation only needs `m_h > 0`.

### 3.3 Proposed `BlockingFamily` change (for c5a-v4; Objects/Assembly not edited)

`BlockingFamily T = forall k j, RPBlocking SU2 4 (T.side k j) (coarseSide j)` is a deterministic map. Two options:

* **A (recommended, no change to Objects):** keep `BlockingFamily`; use `Repair.NoisyBlockingFamily` beside it. Every
  deterministic family embeds (`BlockingFamily.toNoisy`, same blocked laws). The infrared input for a noisy family is
  stated at law level, `LawGapBddW (noisyBlockedLaw NB) lam` (§4), which v4 already supports. What c5a would add for the
  cut: `NoisyObsTransferPhysTW T NB` = `ObsTransferPhysTW` with `T.ym k j` replaced by `NB.joint k j`, fine observables
  read through `Prod.fst`, and `condExp` w.r.t. `comap (fun q => (NB.blk k j).B q.1 q.2)`; then
  `torusDecayLoc_of_noisy : LawGapBddW (noisyBlockedLaw NB) lam and NoisyObsTransferPhysTW T NB => TorusDecayLoc T.toV`
  with the proof of `V4.torusDecayLoc_of_blockGapBddW` unchanged (it uses `cov_transfer` for a generic probability measure
  and measurable map; the fine two-point function under `joint` equals that under `T.ym` because the noise is independent:
  `integral_prod` with an integrand depending on the first factor only).
* **B (invasive):** redefine `BlockingFamily` as the noisy structure with a coercion from deterministic families. Not
  recommended: every downstream statement mentions `(B k j).B U` and `T.ym k j`.

---

## 4. The version-4 interface (coordinator's request) — `Repair/V4Bridge.lean`

* **`LevelDprimeWwOn rho lam`** (H): weighted D′ for any family of laws `rho k j` on tori of side `M j` (v4's
  `LevelDprimeWOn` without `D1`). `levelDprimeWw_iff_on` (D): `LevelDprimeWw T B lam <-> LevelDprimeWwOn (blockedLaw T B)
  lam` (`Iff.rfl`).
* **`lawGapW_of_levelDprimeWwOn`** (S) and **`lawGapBddW_of_levelDprimeWwOn`** (S): `0 <= lam`, weighted D′ gives
  `V4.LawGapW rho lam` (constant `pi/(1 - gamma)`) and `V4.LawGapBddW rho lam`.
* **`blockGapBddW_of_levelDprimeWw`** (S): `LevelDprimeWw T B lam => V4.BlockGapBddW T B lam` (the IR statement of record).
* `levelDprimeWwOn_of_levelDprimeWOn` (S): v4's finite-range form is a special case.
* **`blockGapBddW_of_levelDprimeWwOn`** (S): strategy (a) of v4 with the weighted hypothesis at `L1`:
  `LevelDprimeWwOn (fun k j => (blockedLaw T B1 k j).map (B2 k j)) lam2` and `StageTwoW (blockedLaw T B1) B2 s` give
  `exists lam > 0, BlockGapBddW T B1 lam` (through `V4.blockGapBddW_of_stageTwo`).
* `CloseWwOn`, **`levelDprimeWwOn_of_ref`** (S): the general-support pair at law level.
* **Noisy blockings at law level:** `noisy_lawGapBddW` (S): `LevelDprimeWwOn (noisyBlockedLaw NB) lam =>
  LawGapBddW (noisyBlockedLaw NB) lam`; **`noisy_gibbs_clause`** (S): with `KernelDensity` from `k0` on, the Gibbs clause
  is automatic and only the weighted column of every bounded representing potential has to be shown;
  `blockGapBddW_iff_noisy` (S): for the trivial-noise family, `BlockGapBddW T B lam <-> LawGapBddW (noisyBlockedLaw
  (toNoisy B)) lam`.

So the noisy family plugs into the law-level form today; plugging it into `BlockingFamily` needs the joint-law
`ObsTransfer` of §3.3, option A.

---

## 5. Satisfiability checks

| new hypothesis | model case | status |
|---|---|---|
| `WeightedColumnW` / `RefDprimeWw` | **Wilson action at strong coupling**: `refDprimeWw_wilson`: for `|beta_F| <= 0.0685` (`beta_A = 0`), some `lam > 0`, `gamma = 18 K e^lam < 1`, every volume | S under `CertifiedAdjointW` (the c3c computational input) |
| same | every certified fitted plaquette action (c3c window, c4d measured box) | S (`refDprimeWw_of_limitDprimeW`) under their certificates |
| same, genuinely infinite range | an action whose pair influences are `<= K e^{-mu d}`: weighted column at `lam < mu` is `<= K sum_r n(r) e^{-(mu - lam) r}`, `n(r) <= c r^3` links at distance `r`: finite, `< 1` for `K` small | P (the finite-range form excludes all such actions) |
| general support | a measured action with 1x2 rectangles (c4d extension, column 0.96 certified in the c4d note, not in Lean) is `regroup` of a rectangle-supported family: a `CoarsePot` with the same Gibbs measure and conditional laws, so its certified column is a `RefDprimeWw` column | S for the regrouping; the rectangle certificate itself is P/numerical (c4d) |
| `CloseWw` | no model case with the true blocked law: it is worst-case closeness (review §1.4); its form no longer excludes the true theory (no limit, no range, no plaquette clause) | H; annealed form is c5d's |
| `NoisyRPBlocking` fields | `mulNoiseBlocking` of the good blocking, any noise law | S |
| `KernelDensity` | heat-kernel noise | P (§3.2) |
| Gibbs clause | noisy with kernel density | S (`noisy_blockedLaw_gibbs`) |

Vacuity: the weighted condition contains the finite-range one (S), which the certified actions satisfy; it is not
trivially true (`gamma < 1`, and pure-noise / bounded-coupling families still fail v4's `OpenInputsV4` for other reasons,
c5a). The noisy RP theorem is not vacuous: it holds for the trivial noise (old theorem) and for every `tau`.

---

## 6. What the old statements are now special cases of

| old (still in the library, unchanged) | new | link |
|---|---|---|
| `Certified.decay_of_siteW` (finite range) | `decay_of_siteWw` | `weightedColumn_le_of_range` (same constant `D_c/(1 - gamma e^{lam D1})`) |
| `V3.LevelDprimeW` | `LevelDprimeWw` | `levelDprimeWw_of_levelDprimeW` |
| `V4.LevelDprimeWOn` | `LevelDprimeWwOn` | `levelDprimeWwOn_of_levelDprimeWOn` |
| `V3.H1LocalLipW and LimitDprimeW` | `CloseWw and RefDprimeWw` | `ref_close_of_h1LocalLip` |
| `Certified.LimitDprimeW` | `RefDprimeWw` (regrouped) | `refDprimeWw_of_limitDprimeW` |
| `V3.levelDprimeW_of_h1LocalLip` | `levelDprimeWw_of_h1LocalLip` | through the new pair |
| `blocked_wilson_rp` | `noisy_blocked_wilson_rp` | `blocked_wilson_rp_of_noisy` |
| `blockedLaw T B` | `noisyBlockedLaw (toNoisy B)` | `blockedLaw_toNoisy` |
| `V4.BlockGapBddW` | `LawGapBddW (noisyBlockedLaw ...)` | `blockGapBddW_iff_noisy` |

Proposed changes to existing files (not made, owners decide): in `V4/Top.lean` strategy (a), take `LevelDprimeWwOn`
instead of `LevelDprimeWOn` (via `blockGapBddW_of_levelDprimeWwOn`); retire `H1LocalLipW`, `LimitDprimeW`,
`levelDprimeW_of_h1LocalLip` from any top statement; `W1Route.lean`'s "Limitation (named)" paragraph can point here.

---

## 7. Not done, and next step

1. **`KernelDensity` for `goodNoisyFamily` with heat-kernel `tau`** (Lean, about 100 lines): reindex `Measure.pi` along
   `linkSplit`, Haar left/right invariance, withDensity under a measurable equivalence. Then the Gibbs clause holds for the
   noisy good blocking with no hypothesis left.
2. **c5a:** `NoisyObsTransferPhysTW` and `torusDecayLoc_of_noisy` (§3.3 option A), so a noisy family reaches
   `TorusDecayLoc` and the top theorem.
3. **c5d:** the annealed replacement of `CloseWw` (closeness off a sparse bad set); `cov_le_weighted_Ww` is the
   deterministic engine with weights (§1.3).
4. Optional (P to Lean): Lipschitz-norm envelope `=>` weighted column (c3c §5's per-term bound), so a quasi-local action
   given by its terms meets `RefDprimeWw` directly.
5. The content is untouched: whether the true blocked laws at `L1` (or the `L_*` theory in strategy (b)) have a weighted
   column below 1 is the open infrared question (review §2).

---

## Files

* `formal/ProofPhase/Repair/WeightedW.lean` — weighted W1 Theorem A, `LevelDprimeWw`, subsumption.
* `formal/ProofPhase/Repair/GeneralSupport.lean` — `regroup`, `RefDprimeWw`, `CloseWw`, repaired openness, Wilson model case.
* `formal/ProofPhase/Repair/Noisy.lean` — `NoisyRPBlocking`, noisy RP, densities and Gibbs representation, noisy family.
* `formal/ProofPhase/Repair/MulNoise.lean` — multiplicative noise, `mulNoiseBlocking`, `goodNoisyFamily`, `goodNoisy_rp`.
* `formal/ProofPhase/Repair/V4Bridge.lean` — law-level forms, `LawGapBddW` / `BlockGapBddW`, strategy (a) weighted.
* This folder: `setup.sh` (one-time copy of `.lake` to `~/formal-c5c`), `build.sh ProofPhase.Repair.<Module>`,
  `axioms.sh` with `axioms.lean` (34 `#print axioms`). Run with `wsl -d ym-replay -u ym -- bash /mnt/c/.../<script>.sh`
  from PowerShell (from Git Bash the `/mnt/c` path is rewritten and the call fails).

## References (recalled, not reread)

Dobrushin 1968, 1970 (uniqueness condition, weighted form); Gross 1979 (exponential weights); Simon, *The Statistical
Mechanics of Lattice Gases*, and Georgii, *Gibbs Measures and Phase Transitions* (single-site influence bounds); Osterwalder
and Seiler 1978 (reflection positivity of lattice gauge theory, the argument `wilson_rp` formalises).
