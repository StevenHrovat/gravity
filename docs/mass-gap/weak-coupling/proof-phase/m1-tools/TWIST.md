# The twisted blocking on the full lattice (m1-tools, 2026-11-22)

Brief: P0 write-up, part 1 of the owner's "whole plan": define the twisted blocking on the full lattice, check link
reflection positivity, and test for trapping with several cores and correlated shells (CPU). Builds on `P0.md` (the
one-site rule). Claim marks as in `NOTE.md`. Lean: `formal/ProofPhase/M1/Twist.lean` (new). Numerics:
`lattice_twist.py` (new; the exact contour family of [I] (0.4) on a periodic lattice).

## 0. Result in plain words

1. **The full-lattice rule is simple: a Z2 label field rides on Balaban's blocking.** The state at each scale is the
   block field `U` and a field of signs `λ = ±1` on the bonds. The label-corrected field `S = λU` (the "outside", smooth)
   is blocked by Balaban's own average; the labels are blocked by the product of the signs along the straight fine
   path of each coarse bond; the new block field is the new label times the blocked `S`. Labels are created only at block
   centres where the deep part of the field is exactly a sign pattern on that site's bonds (isolated), and dropped where
   they no longer match the field.
2. **Proved in Lean (`Twist.lean`, 6 theorems):** with trivial labels the rule is Balaban's average; labels that are a
   pure Z2 gauge change nothing (only the gauge-invariant twist matters); gauge covariance; commutation with lattice
   symmetries; locality; and the general fact that reflection positivity passes to a blocked law if the blocking commutes
   with the reflection and keeps the positive half on its side.
3. **Link reflection positivity (paper, using the Lean facts):** for a reflection in a plane along block faces, every
   ingredient commutes with the reflection and reads only bonds inside its own blocks, so each twisted-blocked layer of
   the Wilson measure is link-reflection positive, as Balaban's own blocking is.
4. **Multi-site tests (CPU):** exact checks pass in every run (gauge covariance to `1e-11`; with no deep cores the twisted
   rule is bit-for-bit Balaban's). With sparse cores (vortices at centres, vortices off centre, generic deep cores) on
   a correlated background in a random gauge:
   * `d = 2` (`L = 5`, 4 levels) and `d = 3` (`L = 3`, 4 levels): every centre vortex is labelled and carried, nothing
     unexplained remains after one or two levels, nothing is trapped; Balaban's own average also clears everything (it
     simply erases what the labels carry).
   * `d = 4` (`L = 3`, 27⁴ sites, 3 levels; white-noise shells `δ = 0` and `0.03`): at level 1 every centre core is
     labelled and nothing is unexplained; at
     level 2 the cores that were off the level-2 centres have smeared into about 90 deep plaquettes **under both rules**,
     and the lattice is too small to watch the next step. With `L = 3` an off-centre core is next to the centre and
     carries a large share of the paths; Balaban's `L > 11` is out of reach of a full-lattice test in `d = 4` on this
     machine. Not evidence of trapping, but not evidence against it either. With `δ = 0.1` the fine field is too rough
     for the test thresholds (no centre pattern is isolated), no label is created, and the two rules coincide.
5. **Three rule fixes.** Two came out of the tests: a vortex sitting next to a block centre was first mislabelled at
   the centre and the label then outlived the vortex; fix: create a label only if, after correction, no deep plaquette
   remains within distance 1 of the centre (isolation), and drop labels that contradict the field. One came out of the
   reflection-positivity check: the drop rule must read only plaquettes inside the block of the next scale (in the
   tests drop never triggered, so the results are unaffected).
6. **Status of P0:** definition, small-field identity, covariance, symmetry, locality, link reflection positivity:
   done (Lean + paper). No trapping: numerical in `d = 2, 3` (several levels) and in the one-site model at `L = 13`,
   `d = 4`; the `d = 4` full-lattice test is limited to `L = 3` and two observable steps. A proof of no trapping is open.

## 1. Definition

State at scale `m`: `(U_m, λ_m)`, `U_m` the block field (SU(2) on bonds), `λ_m` a label field (`±1` on bonds).
One step `m → m+1` (blocks of side `L`, odd, centred at the coarse sites):

1. **Drop.** At every site `x` where a plaquette with label product `λ_p = -1` has angle `< r_deep` in `U_m` (the
   label claims a vortex the field does not have), reset `λ` to 1 on the bonds at `x`. Only plaquettes lying inside the
   block of the next scale that contains `x` are used (needed for reflection positivity, section 3).
2. **Create (root).** At each block centre `y`: let `S = λ U`. If some plaquette at `y` of `S` is deep (angle
   `≥ r_deep`), let `σ` be the sign pattern on the `2d` bonds at `y` with `σ_b σ_{b'} = sign Re tr S_{p(b,b')}` for the
   plaquettes `p(b,b')` at `y` (built along the star; unique up to a global sign, which is a pure Z2 gauge change and
   irrelevant by `twistBlock_pureGauge`). If `σ` is not constant, every corrected plaquette at `y` has angle `< θ_c`,
   and no plaquette of `σ·S` with a corner within distance 1 of `y` is deep (isolation), multiply `λ` by `σ` on the
   bonds at `y`. (These plaquettes lie inside the block of `y` for `L ≥ 5`.)
3. **Block.** `U_{m+1}(c) = Dec(λ)(c) · M(λ U)(c)`, `λ_{m+1} = Dec(λ)`, where `M` is Balaban's average [I] (0.4) and
   `Dec(λ)(c)` is the product of `λ` along the straight fine path of the coarse bond `c`.

Equivalently: the corrected field `S_m = λ_m U_m` is blocked by Balaban's rule, `S_{m+1} = M(S_m)` (outside creation
and drop events); the labels are blocked by Z2 decimation along straight paths; `U_m = λ_m S_m`. Thresholds in the
tests: `r_deep = 0.5`, `θ_c = 0.6` (angles of SU(2) elements, `θ = arccos(Re tr)`).

## 2. Properties

| property | status | where |
|---|---|---|
| trivial labels: the rule is `M` | **Lean** `twistBlock_one` | |
| no label is created on small fields (creation needs a deep plaquette) | paper (by definition); checked: 0 labels in every small-field run | `lattice_twist.py` V2 |
| pure Z2-gauge labels change nothing; so only the gauge-invariant twist of `λ` matters | **Lean** `twistBlock_pureGauge` | |
| gauge covariance (labels central, `M` covariant) | **Lean** `twistBlock_gauge`; creation and drop use plaquette traces, which are gauge invariant | checked to `1e-11` (V1) |
| commutes with lattice rotations and reflections | **Lean** `twistBlock_sym` given that `M` and `Dec` commute (paper: [I] p. 252 for `M`; straight paths map to straight paths for `Dec`); creation and drop rules are defined by invariant data | |
| locality: a coarse bond reads only bonds of its two blocks; creation reads plaquettes within distance 2 of the centre, inside the block for `L ≥ 5` | **Lean** `twistBlock_local` + paper | |
| measurable | paper: piecewise defined by finitely many polynomial inequalities in the entries | |
| exactness of the conditional step with labels and frozen hole in the conditioning variable | **Lean** `map_resample_eq` (any measurable `φ`) | `P0.md` 4 |

## 3. Link reflection positivity (paper, with `rp_map`)

Let `Θ` be the reflection in a fine hyperplane lying on block faces (between fine sites) at every scale; with odd `L`
and nested blocks, a face plane of a coarse block is a face plane of the fine blocks it contains. The Wilson measure is
link-reflection positive (Osterwalder-Seiler). By `rp_map` it suffices that the full blocking `B : U_0 ↦ (U_m, λ_m)`
(i) commutes with `Θ` and (ii) maps observables of the positive coarse half to observables of the positive fine half.
(i): `M` commutes with `Θ` ([I] (0.5) handles reversed bonds, `BALABAN-READING.md` 4), `Dec` commutes (straight paths
are mapped to straight paths, and `±1 = (±1)⁻¹`), the creation and drop rules are defined by plaquette traces (`tr U⁻¹
= tr U` in SU(2)) and by the canonical sign pattern; `twistBlock_sym` assembles them. (ii): a coarse bond in the
positive half has both blocks in the positive half; `M` and `Dec` read only bonds of those blocks; creation at a centre
reads bonds within distance 2 of it, inside its block for `L ≥ 5`; drop reads only plaquettes inside the block of the
next scale (section 1, rule 1), and a block never straddles the reflection plane. By induction over the scales, every
observable of `(U_m, λ_m)` in the positive half depends only on fine bonds in the positive half. Hence **each
twisted-blocked layer is link-reflection positive**, for observables of the block field and of the labels.

## 4. Multi-site tests (`lattice_twist.py`)

Background: random gauge transformation of a field built from the lowest Fourier modes (bond phases `eps/N`, so the
background stays small at every level), optionally plus white noise `δ` per bond (scale-stable under blocking only in
`d = 4`). Cores: `n` vortex stars at random block centres (`vc`), `n` vortex stars at random sites (`vo`), `n` generic
deep cores (Haar values on 1-3 bonds at a random site; `g`). Counted per level: deep plaquettes of the block field
(angle `> 0.5`); for the twisted rule also deep plaquettes of the corrected field ("unexplained") and plaquettes with
label product `-1` (carried cores).

The code applies the drop rule to all plaquettes at a site (the unrestricted version of section 1, rule 1); drop
triggered in none of the final runs (`-0 sites` at every level), so the restriction does not change any result.

**Validity checks (every run):** V1 gauge covariance of (0.4): max plaquette-angle difference with and without a
random gauge `≤ 7e-11`; V2: with no cores, 0 labels created and twisted output `=` (0.4) output exactly (difference 0).

| run | (0.4): deep plaquettes per level | twisted: deep / unexplained / carried per level |
|---|---|---|
| `d=2, L=5`, 4 levels, `vc` only, 10 cores | 40, 40, 8, 0, 0 | 40/40/0 (+10 labels), 40/0/40, 4/0/4, 0/0/0, 0/0/0 |
| `d=2, L=5`, `vo` only | 40, 0, 0, 0, 0 | 40/40/0, 0/0/0, 0/0/0, 0/0/0, 0/0/0 |
| `d=2, L=5`, `g` only | 23, 2, 0, 0, 0 | 23/23/0, 2/2/0, 0/0/0, 0/0/0, 0/0/0 |
| `d=2, L=5`, all kinds, 10 each | 104, 45, 8, 0, 0 | 104/104/0 (+11), 45/1/44, 4/0/4, 0/0/0, 0/0/0 |
| `d=3, L=3`, 4 levels, all kinds, 15 each | 329, 125, 15, 0, 0 | 329/329/0 (+15), 125/5/120, 8/0/8, 0/0/0, 0/0/0 |
| `d=4, L=3`, 3 levels, all kinds, 8 each, `δ = 0` | 347, 131, 101, 0 | 347/347/0 (+8), 128/0/128, 87/87/0, 0/0/0 |
| `d=4, L=3`, 3 levels, all kinds, 8 each, `δ = 0.03` | 338, 186, 114, 0 | 338/338/0 (+8), 128/0/128, 105/105/0, 0/0/0 |
| `d=4, L=3`, 3 levels, all kinds, 8 each, `δ = 0.1` | 311237, 186, 120, 0 | identical to (0.4): no label created (10% of the fine plaquettes are beyond the 0.5 threshold, so no centre pattern is isolated) |

(Totals of plaquettes per level: `d=2, L=5`: 390625, 15625, 625, 25, 1; `d=3, L=3`: 1594323, 59049, 2187, 81, 3;
`d=4, L=3`: 3188646, 39366, 486, 6. The last level or two are a handful of sites.)

**Discarded first version (recorded):** a background smoothed over 5 sites with amplitude `eps` became rough under
blocking in `d = 2` for both rules (a random field in `d < 4` has no asymptotic freedom), so deep counts grew with the
level; this tested the background, not the cores. The first creation rule (no isolation, no drop) mislabelled a vortex
next to a centre: in the `vo` run the twisted rule then showed 4 and 3 unexplained plaquettes at levels 1-2 while (0.4)
showed 0. Both fixed as in section 1.

**Reading.** In `d = 2, 3` the twisted rule never traps and carries exactly the centre vortices; generic and
off-centre cores clear in one or two levels under both rules. In `d = 4` the only full-lattice size that fits is
`L = 3`; there an off-centre core adjacent to a coarse centre spreads into the coarse star under both rules, and one
more level would be needed to see whether it clears (the one-site model at `L = 13` says generic deep stars clear in
under 10 steps, `D-PIN.md` 2.3).

## 5. What remains for P0

1. **No trapping, proof.** Numerical only. A proof would show that every deep star at a block centre either is an
   isolated sign pattern (labelled) or becomes moderate under (0.4) in a bounded number of steps.
2. **`d = 4` at realistic `L`.** A full lattice with `L = 13` in `d = 4` needs `13^8` sites for two levels: impossible
   here. A reduced multi-block model (a few blocks at `L = 13` with exact paths, periodic in the other directions) is
   the feasible next test.
3. **Interplay with Balaban's large-field partitions.** Labels are created only where Balaban's partition has already
   declared a large field; the label creation is then the root event of `D-PIN.md` 3 (charged once).
