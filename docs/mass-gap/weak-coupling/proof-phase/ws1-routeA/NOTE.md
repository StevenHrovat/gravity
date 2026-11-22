# Proof phase, workstream 1: Route A's crossover (`SlabDecay`) (2026-11-22)

Brief: free win 4 (centre-blind Dobrushin condition: one-page locality check), free win 3 (a good blocking, blueprint
P1.8), and the sharpest sufficient condition for `SlabDecay` with Yang–Mills inside the hypotheses. Mid-task request of
the coordinator: aim at workstream 4's level-uniform `TorusDecay` where possible.

Claim levels as in `../../attempts/RULES.md`: **Lean** (machine-checked), **Lean (definitional)**, **paper** (complete
argument here), **paper modulo** (a named standard theorem), **heuristic**, **numerical** (pre-registered). Lean: three new
files under `../../../formal/ProofPhase/RouteA/` (`Blocking.lean`, `BlockedSlab.lean`, `CentreBlind.lean`), built in
`~/formal-ws1` against the current `Assembly.lean` (with the corrected `oneLoopSlope`) and workstream 4's
`Existence/Bridge.lean`; `axioms-ws1.sh` prints the axioms of 21 headline theorems: all `propext, Classical.choice,
Quot.sound` (two without `Classical.choice`); no `sorry`, no `native_decide`, no new axioms. Scripts here:
`setup-ws1.sh`, `build-ws1.sh`, `probe-ws1.sh`, `axioms-ws1.sh`; numerics: `PREREG.md`, `selfenergy.py`, `.log`, `.json`
(one CPU process, 13 s).

---

## 0. Results at a glance

1. **Free win 4 fails as stated.** Two rigorous reasons and one structural one (§1): (a) the fundamental plaquette, a
   local gauge-invariant slab observable, is *not* a function of the centre-blind (SO(3)) variables (Lean); "centre-neutral"
   holds for the *global* centre symmetry only; (b) the photon test refutes "centre-blind D′ ⇒ SlabDecay" as a
   group-uniform statement: for U(1) the centre-blind variables are constant, D′ holds with γ = 0 and the photon has no
   gap (Lean half + Guth/Froehlich–Spencer); (c) the SO(3)-marginal of the blocked SU(2) theory is a Z₂ gauge theory in
   the SO(3) background (Mack–Petkova form, exact); it is quasi-local exactly when this **centre fibre** is in its
   high-temperature phase (paper modulo Kotecký–Preiss), and in the ordered regime Mack–Petkova monopole loops acquire an
   area interaction (heuristic mechanism: not quasi-local). A uniform fibre condition is confinement-type, so Chatterjee's
   argument comes back through it.
   **Repaired form:** D′ on the *refined* product structure (each coarse link = adjoint part ⊕ Z₂ part) is a valid
   sufficient condition; it splits D′ into a **centre half** (the fibre at strong coupling; in the round-2 proxy it holds
   from L₁√σ ≈ 2.0–2.5, above 1/T_c ≈ 1.45/√σ) and an **adjoint half** (the real obstruction: β_A ≲ 0.083 needed in TV form,
   proxy 0.50 at L₁√σ = 3). No numerical gain over plain D′; the gain is the split, which clicks with Route B (§3.4).
2. **The good blocking exists (P1.8), in Lean** (§2): slice smearing (straight path + spatial staples inside each time
   slice / time strip, projected to SU(2)) with time decimation, iterated `n` times; it commutes with the time reflection
   and lifts the closed positive half, so every blocked layer is reflection positive (`goodBlocking_rp`); `w = 0` is the
   old decimation. Non-trivial limit: **power counting** (the linear self-energy divergence is removed; the unsmeared
   time direction costs nothing at one loop) and a **pre-registered one-loop check**: coarse-plaquette flux variance
   ℓ = 2…16: decimation 1.37 → 15.1 (∝ ℓ), smeared (w = 0.5) 0.34 → 0.28 (converges). All predictions held.
3. **Missing link L1 closed in Lean** (§3): `H1Local ∧ LimitDprime(λ > 0) ∧ ObsTransfer ⇒ SlabDecay`
   (`slabDecay_of_blockedRoute`), hence `⇒ MassGap ∧ LatticeGap ∧ LimitRP` on a line of constant physics
   (`massGap_of_blockedRoute`), also with the concrete good blocking (`massGap_of_goodBlocking`). **TorusDecay:** not
   reachable from `ObsTransfer` as stated (its coarse support grows with the fine support count, physical observables have
   ~ℓ_k⁴ fine links); reachable from a level-uniform transfer `ObsTransferU` (oscillation-sum form), Lean:
   `torusDecay_of_blockedRouteU`, `bothOrders_of_blockedRouteU` (gap in both orders of limits via workstream 4).

## 1. Free win 4: the centre-blind Dobrushin condition

### 1.1 The exact decomposition (paper, elementary)

Fix a measurable section `s : SO(3) → SU(2)` of `U ↦ Ad U`. Then `SU(2) ≅ SO(3) × Z₂` measurably, `U = σ·s(R)`, and Haar
maps to Haar ⊗ uniform. For any coarse potential `H(U)` (one per link set), the SO(3)-marginal density is

  `ρ(R) = 2^{−|E|} Σ_{σ ∈ Z₂^E} e^{H(σ·s(R))}`.

For a plaquette action of the round-2 proxy form `Σ_p φ(t_p)`, `t_p = ½ tr U_p ∈ [−1, 1]`,
`φ(t) = β_F t + (β_A/3)(4t² − 1)`: `t_p = σ_p η_p τ_p` with `σ_p = Π_{l∈∂p} σ_l`, `τ_p = |½ tr s(R)_p|` and the sign
`η_p(R) = sgn tr s(R)_p` (both functions of `R`; `τ_p` depends on the SO(3) plaquette only). The adjoint term depends on
`t_p² = τ_p²`, a function of `R`. Hence

  `ρ(R) = e^{Σ_p (β_A/3)(4τ_p² − 1)} · Z_fib(R)`,  `Z_fib(R) = Σ_σ Π_p e^{J_p σ_p η_p}`, `J_p = β_F τ_p ∈ [0, β_F]`:

the SO(3) marginal is the adjoint weight times the partition function of a **Z₂ lattice gauge theory (the centre fibre)
with plaquette couplings `J_p` in the background 2-form `η`**. Changing the lift of one link flips `η` on its plaquettes,
a Z₂ gauge transformation absorbed by `σ_l → −σ_l`: `Z_fib` does not depend on the section. `M_c = Π_{p∈∂c} η_p` (cube
`c`) is section-independent: the Mack–Petkova Z₂ monopole charge; monopole cubes form closed loops on the dual lattice.

### 1.2 Quasi-locality iff the fibre is at high temperature

**Proposition 1.2 (paper modulo the Kotecký–Preiss cluster expansion).** `e^{Js} = cosh J (1 + s tanh J)` gives
`Z_fib = 2^{|E|} Π_p cosh J_p · Σ_{S: ∂S = 0} Π_{p∈S} η_p tanh J_p`, the sum over closed plaquette surfaces (Z₂
2-cycles). For a contractible `S = ∂V`, `Π_{p∈S} η_p = Π_{c∈V} M_c`: local in `R`. So `log ρ(R)` is a local adjoint
term, plus `Σ_p log cosh J_p` (local), plus the logarithm of a polymer gas of connected closed surfaces with activities
`|w(S)| ≤ (tanh β_F)^{|S|}`, `|S| ≥ 6`. If `tanh β_F · e^{c_d}` is below the Kotecký–Preiss threshold (c_d a
lattice-animal constant), the log is a convergent sum of cluster potentials decaying like `(C tanh β_F)^{size}`: **the
projected specification is quasi-local, uniformly in R.** Non-contractible surfaces (they see the SO(3) configuration's
't Hooft flux through a 2-torus) contribute a global relative correction `≤ C|Λ|(C tanh β_F)^{(side)²}`, vanishing with
the volume.

**Failure in the ordered regime (heuristic; standard low-temperature mechanism).** If `J_p` is large (weak fundamental
coupling: fine lattice, small boxes), `Z_fib` is dominated by `σ` with `σ_p η_p = +1` except on frustrated plaquettes
whose dual set is a surface bounded by the monopole loops: `−log Z_fib ≈ 2β_F × (minimal area spanning the monopole
loops)`. That is an area interaction between monopole loops; the conditional law of `R` near a point depends on where
the minimal sheet of a far-away loop runs, i.e. on the whole loop: not quasi-local (the van Enter–Fernandez–Sokal
pathology in its SU(2) form; physically, "SU(2) = SO(3) with Z₂ monopoles suppressed", Mack–Petkova). Not proved here.

**Uniformity forces confinement type (paper modulo Chatterjee).** A condition uniform over backgrounds includes `R ≡ 1`
(`τ = 1`, `η = +1`), where the fibre *is* the Z₂ Wilson theory at coupling `β_F`. A Dobrushin-type fibre condition
therefore gives that Z₂ theory decay under arbitrary boundary conditions, hence (Chatterjee, CMP 385 (2021)) unbroken
centre symmetry: the fibre condition is a centre-disorder (confinement-type) condition.

### 1.3 Two refutations of "centre-blind D′ suffices"

* **Fundamental observables are not centre-blind (Lean: `xp_not_adjointOnly`).** On `(ℤ/Nℤ)^d`, `N ≥ 2`, `Re tr U_p` is not
  a function of the adjoint images of the links: flipping one link by `−1` keeps all adjoint images and changes it from
  `2` to `−2`. `Re tr U_p` is a slab observable. The premise of free win 4 ("local gauge-invariant observables are
  centre-neutral") is true for the *global* centre symmetry (contractible observables are invariant under the centre flip
  of a row) and false for "functions of SO(3) variables". Decay of SO(3) block variables does not reach `SlabDecay`
  without controlling the fibre.
* **Photon test (Lean half: `cov_adjointOnly_comm`; other half: Guth 1980, Froehlich–Spencer 1982).** For an abelian group
  every centre-blind observable is constant, so its covariances vanish under every measure: a Dobrushin condition on
  centre-blind variables holds with γ = 0 for the free photon. A theorem "centre-blind D′ at L₁ ⇒ decay of all local
  gauge-invariant observables" uniform in the group would give the photon a gap. (The `U(1)/Z₂` reading of "centre-blind"
  escapes this, but then (a) applies: charge-1 plaquettes are not functions of `U²`.) Z₂: its centre-blind variables are
  trivial too; the same statement would give the 4D Z₂ theory torus decay at its (first-order, recalled) transition point.

### 1.4 The repaired condition and what it buys

**D′_ref (paper; Dobrushin's theorem for a product of standard Borel spaces with two site types, standard, not in our
Lean).** Sites: `(l, A)` with value `R_l ∈ SO(3)` and `(l, Z)` with `σ_l ∈ Z₂`. In TV–tanh form (as `r3-robust` §9) for the
proxy action, per shared plaquette: `R_m → R_l`: `tanh(β_F + 2β_A/3)`; `σ_m → R_l`, `R_m → σ_l`, `σ_m → σ_l`:
`tanh β_F`; same link `R_l ↔ σ_l` (six plaquettes): `tanh 6β_F`. Column sums (18 neighbours):

* centre columns: `36 tanh β_F + tanh 6β_F ≈ 42 β_F < 1`, i.e. **β_F ≲ 0.024**;
* adjoint columns: `18 tanh(β_F + 2β_A/3) + 18 tanh β_F + tanh 6β_F < 1`, i.e. **β_A ≲ 0.083** once β_F is small.

D′_ref (weighted, uniform in volume) gives decay of *all* bounded local coarse observables, fundamental ones included, so
it can replace `LimitDprime` in the blocked route. In the round-2 two-coupling proxy (`r2-curvature/NOTE.md` §3.4:
β_F = 7.3·10⁻², 7.7·10⁻³, 4.9·10⁻⁴ at L₁√σ = 2, 2.5, 3) the **centre half holds from L₁√σ ≈ 2.0–2.5** — above
1/T_c ≈ 1.45/√σ, as the deconfinement test demands. The **adjoint half fails by a factor ≈ 6 at L₁√σ = 3** (β_A ≈ 0.50);
in TV form it enters near L₁√σ ≈ 5, in the W₁ form of `r2-curvature` (β_A < 0.29–0.39) at 3.3–3.9. Plain D′ (SU(2)
sites) has the column `18 tanh(β_F + 2β_A/3)`: D′_ref is slightly *worse* numerically. Its value is structural: **the
open core of D′ at L₁ is entirely the adjoint (glueball) channel; the centre channel is a separate, much weaker,
confinement-type smallness condition.**

**Chatterjee and deconfinement.** The adjoint half alone has nothing for Chatterjee's centre argument to act on, as free
win 4 said; but it cannot be used alone (§1.3). The centre half is exactly where the deconfinement objection lives. One
new remark for centre-blind claims (heuristic, recalled facts): the SU(2) deconfinement transition is second order (3D
Ising class) and the adjoint Polyakov loop couples to the Ising energy operator, so centre-blind correlations are critical
on a torus of time extent exactly 1/T_c: a uniform centre-blind decay condition must fail at L₁ = 1/T_c (one-block-thick
tori), though not below it.

**Verdict on free win 4.** Locality check: the projected specification is quasi-local iff (essentially) the centre fibre
is disordered; the hidden Z₂ part does mediate long-range dependence (monopole sheets) when it is ordered. As a route,
"D′ on centre-blind variables only" is insufficient (§1.3). What survives is the split D′_ref = centre half + adjoint
half.

## 2. Free win 3: the good blocking (P1.8)

**Construction** (`Blocking.lean`). One step `(ℤ/2Mℤ)^d → (ℤ/Mℤ)^d`: for the coarse link `(x, μ)`, with `f = 2x`, sum the
transports along the straight path `f → f + 2e_μ` and, with weight `w`, the staples `f → f ± e_ν → f ± e_ν + 2e_μ →
f + 2e_μ` for every spatial `ν ≠ μ` (4 staples for a spatial link, 6 for a temporal one), and project:
`projSU2(A) = A/√|det A|` (a sum of SU(2) matrices is a real multiple of one; else 1, a null set). Spatial coarse links use
only the fine time slice `2x₀`; temporal coarse links only the strip `[2x₀, 2x₀ + 2]`, whose staple family is mapped to
itself by the strip mirror plus path reversal. Iterated: `smearIter n : 2ⁿM → M`; for a tuning with `ℓ_k = 2^{n_k}`,
`goodBlocking` gives a `BlockingFamily` (one coarse link per physical L₁).

**Lean.** `walk_thetaConn` (transport of `Θ U` along a path = transport of `U` along the mirrored path), `walk_rev`
(reversal inverts), `projSU2_star` (projection commutes with `†`), **`smearBlock_thetaConn`** (`B(ΘU) = Θ(BU)`),
**`linkDep_smearBlock`** (closed coarse positive half lifts to the closed fine positive half), `smearRP`,
`RPBlocking.comp`/`cast`, `smearIter`, `goodBlocking`, **`goodBlocking_rp`** (every blocked layer reflection positive),
`smearBlock_zero` (`w = 0` is `decimate`). Why it suffices: reflection positivity is used only for the time reflection
(Theorem C, `limitRP`), so spatial smearing is free and temporal smearing must respect the strip mirror.

**Non-triviality at fixed L₁ (power counting; not a proof).** A thin coarse line of length L₁ = ℓa has one-loop
self-energy `g² ∫ d³k_⊥/k_⊥²` per unit length, linearly divergent: `⟨W⟩ ~ e^{−c g²ℓ}` with `g² ~ 1/log ℓ` → 0, the
pure-noise limit of decimation (round-4 finding 4). A spatial coarse link smeared at radius r in the two other spatial
directions but sharp in time: `∫ dk_t d²q e^{−r²q²}/(k_t² + q²) = π ∫ d²q e^{−r²q²}/q ~ π^{3/2}/r`, finite: the one
unsmeared transverse direction costs no divergence. Temporal links are smeared in all three transverse directions.
Iteration makes r grow with the coarse spacing at every level. **Numerical check (pre-registered, `PREREG.md`):**
linearised abelian flux variance σ² of the coarse plaquette, ℓ = 2, 4, 8, 16:

| blocking | time–space plaquette | space–space plaquette |
|---|---|---|
| decimation (w = 0) | 1.37, 3.26, 7.17, 15.11 (ratio 16/8: 2.11) | same |
| smeared w = 0.5 | 0.337, 0.300, 0.286, 0.276 (0.96) | 0.277, 0.250, 0.246, 0.239 |
| smeared w = 1 | 0.307, 0.252, 0.232, 0.220 (0.95) | 0.260, 0.204, 0.189, 0.178 |

All three predictions held (decimation ratio ≥ 1.7; smeared ratio ≤ 1.15 and σ²(16) ≤ ½σ²_dec(16); both orientations
alike). "Non-trivial" here means **not pure noise**; whether the limit is non-free is P6.2. Gauge covariance
(`P(gAh⁻¹) = gP(A)h⁻¹` for `A ≠ 0`) and centre covariance (each staple crosses a twist row an even number of extra times)
hold off the null set where the path sum vanishes: paper, not in Lean.

## 3. Towards `SlabDecay`

### 3.1 Missing link L1, closed (`BlockedSlab.lean`)

* `cov_transfer` (generic): `|Cov(F,G)| ≤ |Cov(f∘Φ, g∘Φ)| + 5ε` when `E[F|Φ]`, `E[G|Φ]` are `ε`-close in L¹ to `f∘Φ`,
  `g∘Φ` (`|f|, |g| ≤ 1`) and `|E[FG] − E[E[F|Φ]E[G|Φ]]| ≤ ε` (law of total covariance, with `condExp`).
* `gaugeInvariant_tShift`, `gaugeInvariant_thetaConn`; `slab_transfer_data` (supports of `F∘S_n`, `F∘Θ` of size ≤ V_k,
  separated by `n` lattice steps via `sep_shift_mirror`).
* `wcorr_le_blocked`: one level, one volume.
* **`slabDecay_of_blockedRoute`**: for any `BlockingFamily T` (reflection-respecting blockings of the SU(2) Wilson measure
  along `T`), `H1Local T B λ Vk Vinf ∧ LimitDprime λ Vinf ∧ ObsTransfer T B ∧ λ > 0 ⇒ SlabDecay T` with physical rate
  `min(λ/(4L₁), m)` (the polynomial factor `(1 + D/L₁)⁴` of `ObsTransfer` is absorbed by halving the exponent).
* `massGap_of_blockedRoute`: `OnLCP ∧` the same `⇒ MassGap ∧ LatticeGap ∧ LimitRP`; `massGap_of_goodBlocking`: the same
  with `B = goodBlocking T w n hn`.

### 3.2 `TorusDecay` (workstream 4's request)

The constant from `ObsTransfer` is `(1−γ)⁻¹·4|K|(V_k + 1)·24(4/λ)⁴e^{λ/4} + 5c`: it grows with the level through the
support bound `V_k`, because `ObsTransfer` bounds the coarse support of the approximant by `K(|A₀| + 1)(1 + D/L₁)⁴` and
physical observables at level k have of order ℓ_k⁴ fine links. So only `SlabDecay` is reachable from it.
`ObsTransferU` (new, open): for every support bound `Vb`, the approximant `f` has a Dobrushin oscillation bound with total
`≤ 2K(1 + D/L₁)⁴`, uniform in the level (averaged observables, `N⁻¹Σ` of local terms, satisfy oscillation bounds of total
O(1) as N grows; a support *count* cannot be level-uniform for them). Lean: **`torusDecay_of_blockedRouteU`**
(`H1Local ∧ LimitDprime ∧ ObsTransferU ⇒ TorusDecay T.toV`) and `bothOrders_of_blockedRouteU` (`⇒ MassGap ∧ MassGapMF`,
via `bothOrders_of_torusDecay`). Caveat: Dobrushin-type bounds are support-sensitive while the true (spectral) bound is
`‖F‖₂² e^{−Δτ}`; observables whose approximant needs many coarse links with large oscillation (e.g. parities of many
spread plaquettes, unless `E[F|Φ]` is already small) are the hard case for `ObsTransferU`.

### 3.3 The sharpest sufficient condition I can justify

  `SlabDecay T ⇐ [good blocking B] ∧ H1Local(B) ∧ D′_ref,λ(limit at L₁) ∧ ObsTransfer(B)`,

with D′_ref = centre half (fibre at strong coupling) ∧ adjoint half (§1.4). In Lean with `LimitDprime` (plain SU(2) D′)
in place of D′_ref; the refined form needs Dobrushin's theorem with two site types (standard, not formalised). Every
hypothesis is about the real blocked SU(2) Wilson laws. It is strictly stronger than the gap (worst case at L₁; false for
L₁ < 1/T_c).

### 3.4 Clicks

* **Route B is the centre half (lead; paper modulo Kotecký–Preiss).** In the decomposition of §1.1 a 't Hooft twist
  multiplies `tr U_p` on the twist plaquettes by `−1`, i.e. replaces `η` by `ητ` in the fibre:
  `Z_tw/Z = E_ρ[Z_fib(J, ητ)/Z_fib(J, η)]` exactly. Under the centre half, only non-contractible surfaces see `τ`
  (`δτ = 0`), so `1 − Z_tw/Z ≤ C|Λ|(C tanh β_F)^{area}`: the vortex free energy vanishes like `e^{−c·area}` and, by the
  (definitional) sector identity P1.4, the electric-flux free energy grows like the area. So **the centre half of D′_ref
  at L₁ implies Route B's flux confinement** for the blocked theory (Chatterjee's direction, made quantitative); the
  converse is READING click C1 (twist insensitivity ⇒ insensitivity to all boundary conditions), open. Route B's natural
  target is the centre half; Route A's own content is the adjoint half. The positivity note's conjecture C1 ("adjoint
  disorder + non-critical centre ⇒ ratio gap") has the same split.
* **Round 4's "−1 is a commutator" is the coupling of the two halves (lead).** On a 2-torus, a flat adjoint background
  (`Ad a`, `Ad b` commute) lifts with `aba⁻¹b⁻¹ ∈ Z(G)` (`conj_eq_conj_iff`, already in Lean); its fibre class is non-trivial
  iff that commutator is `−1` (a twist eater). Where `−1` is not a commutator (abelian groups, the order-12 binary dihedral
  group) flat adjoint backgrounds carry trivial fibre class.
* **The owner's readings.** "D′ is the local form of entropy wins" (`PREP.md`) splits into vortex entropy (the centre /
  root half) and the self-charge (adjoint) half. "Exclusion must stay possible; existence has to be shown": decimation
  (`w = 0`, noise) is a member of the good-blocking family; `w > 0` keeps content (power counting).

## 4. Headline theorems (exact statements in words)

| theorem | statement | mark | Yang–Mills in hypotheses |
|---|---|---|---|
| `walk_thetaConn`, `walk_rev` | transport of `ΘU` along a path = transport of `U` along the mirrored path; reversed path gives the inverse | definitional-elementary (any group) | no |
| `projSU2_star`, `projSU2_coe` | the projection `A ↦ A/√|det A|` commutes with `†` and fixes SU(2) | elementary | SU(2) |
| `smearBlock_thetaConn` | the smeared step commutes with the time reflection | substantive-elementary (geometry of this map) | SU(2) field |
| `linkDep_smearBlock` | a coarse observable of the closed coarse positive half (coarse side even) is a fine observable of the closed fine positive half | substantive-elementary | SU(2) field |
| `smearBlock_zero` | `w = 0` gives decimation | definitional | — |
| `goodBlocking_rp` | for a dyadic tuning, every layer of the good blocking of the SU(2) Wilson measure is reflection positive | definitional given the two properties (`blocked_wilson_rp`) | Wilson measure, tuning |
| `cov_transfer` | covariances pass through a conditional expectation with error 5ε | generic measure theory | no |
| `gaugeInvariant_tShift`, `_thetaConn` | translates / reflections of gauge-invariant observables are gauge invariant | elementary | any group |
| `slabDecay_of_blockedRoute` | `H1Local ∧ LimitDprime(λ>0) ∧ ObsTransfer ⇒ SlabDecay` for any reflection-respecting blocking family | substantive reduction (geometry + condExp); all physics in hypotheses | Wilson measure, its blocked laws |
| `massGap_of_blockedRoute`, `massGap_of_goodBlocking` | `OnLCP ∧` the above `⇒ MassGap ∧ LatticeGap ∧ LimitRP` | assembly (composition) | yes |
| `torusDecay_of_blockedRouteU`, `bothOrders_of_blockedRouteU` | with `ObsTransferU`: `⇒ TorusDecay`, `⇒ MassGap ∧ MassGapMF` | substantive reduction; new open hypothesis | yes |
| `xp_not_adjointOnly` | the SU(2) plaquette `Re tr U_p` is not a function of the adjoint images (N ≥ 2) | elementary counterexample | SU(2) |
| `cov_adjointOnly_comm` | abelian group: centre-blind observables have zero covariance under every measure | definitional (constancy) | no (that is the point) |

No statement here separates SU(2) from U(1) or Z₂ by itself: the group-specific content of the route sits in
`LimitDprime`/D′_ref (fails for the photon) and in the open hypotheses.

## 5. Unit tests

* **Photon.** `LimitDprime`/D′_ref fail for 4D U(1) at weak coupling at every scale (Coulomb phase); the blocked-route
  theorems give it nothing. "Centre-blind D′ alone" would pass the photon: that is why it is rejected (§1.3).
* **Z₂.** Conclusions are gap-type (`SlabDecay`, `TorusDecay`), true for weak-coupling Z₂; the hypotheses are
  confinement-type and fail for it (sufficient, not necessary); no area law is claimed.
* **Finite subgroups.** The theorems are group-structure-generic in their proofs; for frozen finite subgroups (gap, no
  confinement) the confinement-type hypotheses fail, the gap-type conclusion is consistent (Adhikari–Cao).
* **Deconfinement.** D′/D′_ref at L₁ < 1/T_c must fail (volume-uniform local potentials of `H1Local` on a one-block-thick
  torus would give Polyakov-loop decay); in the proxy the centre half switches on at L₁√σ ≈ 2.0–2.5 > 1.45. New point
  test for centre-blind claims at L₁ = 1/T_c (§1.4).
* **Triviality.** The good blocking's "non-trivial" is "not pure noise" (the free field passes, as it must for the
  photon); non-freeness is P6.2 and is not claimed.
* **Banks–Zaks.** Nothing here is unconditional; D′ at L₁ fails for conformal-window theories (no strong-coupling scale).

## 6. Blueprint pieces that change status

* **P1.8 (good blocking):** open → **Lean** (construction; reflection positivity at every level for dyadic tunings);
  non-trivial limit **power counting + numerical (one loop)**; gauge/centre covariance paper.
* **P1.6:** now for the good blocking too (`goodBlocking_rp`).
* **P7.4 / missing link L1:** paper → **Lean** (`slabDecay_of_blockedRoute`, `massGap_of_blockedRoute`). Suggestion for the
  coordinator: the blocked route can become a third disjunct of `OpenPieces.crossover`
  (`∃ B λ Vk Vinf, 0 < λ ∧ H1Local ∧ LimitDprime ∧ ObsTransfer`), discharged by `slabDecay_of_blockedRoute`.
* **P4.1:** free win 4 as stated: **refuted** (§1.3); sufficient conditions now D′ at L₁ (Lean, via the blocked route) and
  D′_ref (paper); the open core is the **adjoint half**, the centre half is a weaker confinement-type condition that
  Route B targets.
* **P5.2:** `ObsTransfer` still open; new level-uniform `ObsTransferU` for `TorusDecay` (both orders of limits).

## 7. Next step

Evaluate the adjoint half of D′_ref in W₁ form on a fitted blocked action **with the good blocking as the block variable**
(the round-3 review criticised deterministic decimation-type block variables for Leg C; this one is reflection positive and
not noise), at L₁√σ ∈ {3, 4}; in parallel, with workstream 2, try to prove the centre half at L₁ from twist insensitivity
(READING C1), which is where Route B's flux energy would enter Route A.

## References (ideas only)

Mack, Petkova, Ann. Phys. 123 (1979) 442; Z. Phys. C 12 (1982) 177 (SO(3) × Z₂ split, Z₂ monopoles; recalled). Kotecký,
Preiss, CMP 103 (1986) 491 (cluster expansion; recalled). Chatterjee, CMP 385 (2021) 1007. van Enter, Fernandez, Sokal,
J. Stat. Phys. 72 (1993) 879. Guth, PRD 21 (1980) 2291; Froehlich, Spencer, CMP 83 (1982) 411. Dobrushin (1968, 1970).
Adhikari, Cao, arXiv:2202.10375. Project: `r3-robust/NOTE.md`, `r2-curvature/NOTE.md`, `positivity/NOTE.md`,
`r4-review/FREE-WINS.md`, `proof-phase/READING.md` (C1, C2), `formal/ProofPhase/Existence/Bridge.lean` (workstream 4).
