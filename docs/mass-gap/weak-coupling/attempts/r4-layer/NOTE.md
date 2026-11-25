# Round 4, attempt r4-layer: the act identity per layer, exact (2026-11-21)

Brief: make the Yang–Mills side of the act identity rigorous where it is rigorous. (1) The electric-flux sector of a (twisted) box
as a transfer-matrix sector, with E_e ≥ 0 and e^{−E_e T} decay. (2) Exact transport of the flux sector and of the act number
z = E_e·L under a gauge-covariant, centre-respecting blocking, with a precise meaning of "the blocked action". (3) T38 in full:
reflection positivity of a blocked layer including the variables that touch the reflection plane, for a blocking designed for it,
or the exact obstruction. Then state what stays one-sided, for r4-conjw.

Claim levels: **proved (Lean)** (one Lean theorem states it, Yang–Mills objects named where they occur), **proved (paper)**
(complete argument here), **standard** (literature, not re-proved), **heuristic**, **open**. **Strength against the mass gap:** every
result of this note is **weaker** than the mass gap (finite-volume identities and non-strict inequalities); none is a step that the
gap would follow from without the one-sided comparison of section 4.

Lean: five new files in `../../../formal/Attempts/R4/`, namespace `Attempts.R4.Layer`, built only in WSL `~/formal-att-r4-2`
(`build.sh <module>`, `axioms.sh` in this folder). All five build ("Build completed successfully"), no warnings in these files; no
`sorry`, no `axiom`, no `native_decide`; `#print axioms` on 51 headline theorems: 48 use propext, Classical.choice, Quot.sound,
3 only propext, Quot.sound. No numerics were run.

---

## 0. Lean names first (for r4-minting and r4-conjw)

| what | Lean name (namespace `Attempts.R4.Layer`) | file |
|---|---|---|
| flux sector is invariant (T commutes with Ω̂) | `top_parity` | `LayerSector` |
| E_e ≥ 0, operator level, any kernel ≥ 0 | `flux_bound_of_vacuum_bound`, `lamFlux_le_lamVac`, `fluxEnergy_nonneg` | `LayerSector` |
| flux correlators decay like e^{−E_e n} (the TTL) | `flux_correlator_decay` (with `sector_decay`, `lamFlux_eq`, `cs_int`) | `LayerSector` |
| Z = Z₀ + Z₁, Z_tw = Z₀ − Z₁ (twist = centre transform of flux sectors) | `twist_centre_transform` | `LayerSector` |
| 0 ≤ Z₁ ≤ Z₀, F_e ≥ 0 (finite configuration spaces) | `Ztw_nonneg`, `Zflux_nonneg`, `Zflux_le_Zvac`, `Zvac_nonneg`, `freeFlux_nonneg` | `LayerSector` |
| 't Hooft duality F_e = dual(F_m), exact; self-dual point log(1+√2) | `freeFlux_eq_dual`, `dual_selfDual` | `LayerSector` |
| the Wilson transfer kernel (temporal gauge) and Ω̂ | `wilsonKernel`, `centreFlip`, `wilsonKernel_symm`, `wilsonKernel_le`, `measurable_wilsonKernel`, `plaquetteHolonomy_centreFlip`, `wilsonKernel_centreFlip` | `LayerKernel` |
| E_e ≥ 0 and TTL for the Wilson transfer operator, any compact G with central z, z² = 1 | `wilson_fluxEnergy_nonneg`, `wilson_flux_correlator_decay` | `LayerKernel` |
| the same for **SU(2)**, z = −1 | `su2_fluxEnergy_nonneg`, `su2_flux_correlator_decay` | `LayerKernel` |
| the same in a **magnetically twisted box** (m ∥ e, any sheet) | `twKernel`, `twKernel_centreFlip`, `twisted_fluxEnergy_nonneg`, `su2_twisted_fluxEnergy_nonneg`, `su2_twisted_flux_correlator_decay` | `LayerTwisted` |
| U(n), U(1) (the photon) | `un_fluxEnergy_nonneg` | `LayerTwisted` |
| **the act is conserved per layer** | `act_conserved_per_layer` (with `sector_partition_conserved`, `partition_map`) | `LayerTransport` |
| the coarse flux sector lies in the fine one | `lift_charged`, `lift_mem_sec`, `map_centre_invariant`, `correlator_conserved` | `LayerTransport` |
| the one-sided half (coarse observers see a rate ≥ E_e) | `blocked_flux_decay`; SU(2): `su2_decimated_flux_decay` | `LayerTransport`, `LayerDecimation` |
| T38 in full (coarse plane included), abstract | `layer_rp`, `coarseForm_eq` | `LayerTransport` |
| T38 obstruction (straddling coarse plane variable) | `straddle_breaks_rp`, `straddle_fine_rp` (toy) | `LayerTransport` |
| decimation blocking, gauge / centre / reflection covariant | `decimate`, `decimate_gauge`, `decimate_centreFlip`, `decimate_thetaConn`, `linkDep_decimate` | `LayerDecimation` |
| **T38 for the blocked SU(2) Wilson layer** | `decimated_wilson_rp`, `decimated_wilson_rp_SU2` | `LayerDecimation` |

## 0.1 The result in plain words

1. **The flux sector is a transfer-matrix sector, on the real lattice, for SU(2).** In temporal gauge the Wilson weight is a product
   of kernels K_β(U, V) between consecutive time slices. 't Hooft's centre transformation Ω̂ (multiply the links of one row by −1)
   commutes with it. Its eigenspaces are the electric-flux sectors. Proved in Lean, with the SU(2) Wilson kernel inside the
   hypotheses: the flux sector is invariant, the flux sector norm of T never exceeds the vacuum sector norm, so
   E_e = log(λ_vac/λ_flux) ≥ 0, and every flux correlator decays like e^{−E_e n} relative to the vacuum. The same holds in a
   magnetically twisted box (the scout's m ∥ e setting) and for U(1).
2. **The duality has an exact home.** On a finite lattice the twisted partition function is the centre (Fourier) transform of the
   two flux partition functions, Z_tw = Z₀ − Z₁, and the electric free energy is exactly round 3's order-reversing involution of the
   magnetic one, F_e = dual(F_m). Its only fixed point is F = log(1 + √2) ≈ 0.881 (section 1.5).
3. **The act is conserved per layer, and exactly this is conserved:** the pair of flux-sector partition functions Z₀, Z₁ of the box
   (equivalently Z and Z_tw), hence F_e, F_m and the act number z = L·F_e/T, measured in each layer's own units. In addition the coarse
   flux sector is a subspace of the fine one: every coarse state of charge e lifts to a fine state of the same charge. This holds for
   every blocking that is a measurable map commuting with Ω̂ (a Markov kernel, once the noise is included), so for every group.
4. **What is not conserved (the exact line).** (a) The rate a coarse observer measures with coarse observables is at least the
   fine E_e and equals it only if the coarse flux states overlap the fine flux ground state (one-sided, proved in Lean as an inequality).
   (b) "The blocked action" is the image of the fine ensemble; nothing compares it with the original action on the same box. Growth of
   z is exactly such a comparison (section 4). That is round 3's obstruction, now located as an inequality between two measures on
   one box, and it is the target of r4-conjw.
5. **T38 in full holds for blockings that reach the coarse plane only through the fine plane, and can fail otherwise.** Proved in
   Lean: (i) such a blocking gives a reflection-positive coarse layer for every coarse observable of the closed positive half,
   the coarse plane included (`layer_rp`); (ii) the decimation blocking of the real lattice (each coarse link the product of the two
   fine links along it) is gauge, centre and reflection covariant, and the blocked SU(2) Wilson layer is reflection positive
   (`decimated_wilson_rp_SU2`); (iii) an explicit reflection-positive fine layer and a reflection-covariant blocking whose coarse plane
   variable is read from both halves give a negative coarse reflection form (`straddle_breaks_rp`). Proved on paper: site reflection
   positivity in all four directions at once, by this route, forces the decimation (up to a central factor and noise); with link
   reflection positivity, block-averaging windows of transverse radius 1 are allowed, and with an **odd blocking factor (3)** this
   survives every RG step, while with factor 2 it survives one step only (section 3.3).

## 1. The flux sector as a transfer-matrix sector

### 1.1 Objects (all Yang–Mills objects named)

- Spatial slice: the periodic lattice (ℤ/Nℤ)^ds (ds = 3 for 4D), slice configuration U : links → G, product Haar measure
  (`productHaar G ds N`).
- **Wilson transfer kernel** (temporal gauge), `wilsonKernel n β U V`:
  K_β(U, V) = exp(β/2 Σ_p Re tr U_p + β/2 Σ_p Re tr V_p + β Σ_l Re tr(U_l V_l⁻¹)). The temporal plaquette of link l between the
  slices has holonomy V_l U_l⁻¹ in temporal gauge; its real trace equals that of U_l V_l⁻¹ for a unitary representation.
  Magnetic twist: `twKernel n β w S` replaces Re tr U_p by Re tr(w U_p) for p in a set S of spatial plaquettes, w central ('t Hooft's
  m_z for S the xy-plaquettes at (x, y) = (−1, −1), all z, and w = −1).
- **Centre transformation** Ω̂_{μ₀}, `centreFlip z μ₀`: multiply the μ₀-links of the row x_{μ₀} = −1 by z (central, z² = 1, Haar
  preserving). It is 't Hooft's twisted gauge transformation; its eigenvalue on a state is (−1)^{e_{μ₀}}.
- Transfer operator (Tψ)(U) = ∫ K(U, V) ψ(V) dV on bounded measurable states (`top`). Sectors: ψ ∘ Ω̂ = ψ (vacuum sector e = 0),
  ψ ∘ Ω̂ = −ψ (flux sector e = 1), optionally intersected with a class Q of states closed under |·| (the gauge-invariant states, Gauss
  law).
- Sector norms: λ_vac, λ_flux = the best constants in ‖Tψ‖ ≤ λ‖ψ‖ on each sector (`lamVac`, `lamFlux`; attained, `lamVac_mem`,
  `lamFlux_mem`). **Flux energy** E_e := log(λ_vac/λ_flux) (`fluxEnergy`), per time step. For T ≥ 0 these are the top eigenvalues of
  the two sectors, so E_e is the energy of the lowest e = 1 state above the vacuum; the act number is z = E_e·L.

**Sectors of Gauss-law states, labelled by the root ('t Hooft's definition; the owner's dictionary).** Physical states obey Gauss's
law: they are invariant under every periodic gauge transformation (a local check, the "only correct messages" of the owner's
reading). Ω̂ is a gauge transformation that is periodic only up to the centre element, g(x + N e_{μ₀}) = z·g(x); on Gauss-law states it
acts as a global operator, and its eigenvalue (−1)^{e} labels the electric flux. In Lean the Gauss-law states are the class Q
(closed under |·|, preserved by T: stated gap 2 below), and the sectors are `Sec c Q (±1)`. The exact difference between the abelian
and the non-abelian Gauss law, on the lattice: with E^L_{x,μ}, E^R_{x,μ} the generators of left and right translation of the link
variable U_{x,μ}, the Gauss operator at x is G_x = Σ_μ (E^L_{x,μ} − Ad(U_{x−e_μ,μ}) E^R_{x−e_μ,μ}). For an abelian group Ad = id
and E^R = E^L, so G_x is the plain lattice divergence of E: the field carries no charge of its own. For a non-abelian group the
incoming field is parallel-transported by Ad(U), the lattice form of the covariant divergence D·E = ∂·E + [A, E]: the gluon field
counts in its own charge balance (standard, Kogut–Susskind; not formalised). None of the theorems below use this difference: they
hold for every group with central z, z² = 1.

### 1.2 Proved (Lean)

| statement | Lean | level |
|---|---|---|
| K_β is non-negative, symmetric, bounded by exp(\|β\|(#plaq + #links) n), jointly measurable | `wilsonKernel_nonneg`, `wilsonKernel_symm`, `wilsonKernel_le`, `measurable_wilsonKernel`; twisted: `twKernel_symm`, `twKernel_le`, `measurable_twKernel` | proved (Lean), any G with continuous unitary rep |
| Ω̂ leaves every spatial plaquette holonomy invariant (the two μ₀-links of a plaquette lie in the same row and cancel, z central) and every temporal plaquette; so K(Ω̂U, Ω̂V) = K(U, V), with or without magnetic twist | `plaquetteHolonomy_centreFlip`, `wilsonKernel_centreFlip`, `twKernel_centreFlip` | proved (Lean) |
| the sectors are invariant: T maps charge ε to charge ε | `top_parity` | proved (Lean), any kernel |
| \|Tψ\| ≤ T\|ψ\| pointwise (K ≥ 0); \|ψ\| is a vacuum-sector state with ‖\|ψ\|‖ = ‖ψ‖; hence every vacuum bound is a flux bound, λ_flux ≤ λ_vac, **E_e ≥ 0** | `abs_top_le`, `flux_bound_of_vacuum_bound`, `lamFlux_le_lamVac`, `fluxEnergy_nonneg` | proved (Lean) |
| **TTL:** for flux-sector ψ, bounded φ: (∫ φ·Tⁿψ)² ≤ (λ_vac^n e^{−E_e n})² ‖φ‖²‖ψ‖² | `flux_correlator_decay` | proved (Lean) |
| SU(2) (z = −1), every β, N, ds, μ₀, Q: E_e ≥ 0 and the TTL bound | `su2_fluxEnergy_nonneg`, `su2_flux_correlator_decay` | proved (Lean), SU(2) inside |
| the same in the magnetically twisted SU(2) box, any sheet S | `su2_twisted_fluxEnergy_nonneg`, `su2_twisted_flux_correlator_decay` | proved (Lean), SU(2) inside |
| U(n), z = −1 (U(1) is n = 1) | `un_fluxEnergy_nonneg` | proved (Lean) |

### 1.3 Trace level (finite configuration spaces: the finite gauge groups)

For a symmetric matrix T with non-negative entries and a permutation σ (for a finite gauge group G, T is the temporal-gauge transfer
matrix on G^{links}, finite):
- `twist_centre_transform`: Z(n) = tr Tⁿ = Z₀ + Z₁ and Z_tw(n) = tr(Ω̂Tⁿ) = Z₀ − Z₁, Z_e = (Z ± Z_tw)/2.
- `Ztw_nonneg`: Z_tw ≥ 0 (entries of Tⁿ are non-negative). `two_mul_Zper_sub_Ztw`: 2(Z − Z_tw)(2m) = Σ_{i,j}((T^m)_{ij} −
  (T^m)_{σi,j})², a sum of squares, so `Zflux_nonneg` Z₁ ≥ 0 at even time extent (it needs only T symmetric and σ a bijection).
  Hence 0 ≤ Z₁ ≤ Z₀ (`Zflux_le_Zvac`, `Zvac_nonneg`), ρ = Z₁/Z₀ ∈ [0, 1], and the free-energy flux energy F_e = −log ρ ≥ 0
  (`freeFlux_nonneg`). This is r3-monotone's B1 in Lean (finite case).
- `pow_sigma`: Tⁿ commutes with σ (sector invariance in trace form).

### 1.4 Stated gaps of section 1 (not formalised)

1. **Identification with the 4D path integral.** Z_Wilson(L₀) = tr(P_G T^{L₀}) and Z_tw = tr(Ω̂ P_G T^{L₀}) in temporal gauge, P_G the
   projection on gauge-invariant states. Standard (Luescher 1977, Osterwalder–Seiler 1978); for compact G it needs T trace class,
   standard; not formalised. The Lean theorems are about K_β and its operator, which is the transfer operator by this standard step.
2. **Gauss law as Q.** Gauge-invariant states form a class closed under |·|; that T preserves it (gauge invariance of K_β and of Haar
   measure) is standard and is a hypothesis (`hQT`) of the decay theorems. E_e ≥ 0 does not need it.
3. **Strictness.** E_e > 0 in finite volume (Perron–Frobenius/Jentzsch: the vacuum is the unique top state and lies in the e = 0
   sector) is standard (r3-monotone B2), not formalised. **Attainment:** that some flux state decays exactly at e^{−E_e n} is the
   spectral theorem (compact self-adjoint T), standard, not formalised; the Lean bound is the upper half, which is what a TTL needs.
4. Only the centre Z₂ (z² = 1) is formalised; this covers SU(2), U(1) with e^{iπ}, Z₂ and the binary polyhedral groups (centre {±1}).
   SU(N) with Z_N sectors needs complex characters (same proofs, not formalised).

### 1.5 The duality and the "inversion" (answer to the owner's reading)

- **Exact identities on the finite lattice:** Z_tw = Z₀ − Z₁, Z = Z₀ + Z₁ (`twist_centre_transform`): the magnetic (twisted)
  partition function is the centre transform of the electric ones; and F_e = dual(F_m) with dual(x) = −log((1 − e^{−x})/(1 + e^{−x}))
  (`freeFlux_eq_dual`, using round 3's `Attempts.R3.Monotone.dual`, an order-reversing involution). Both are conserved per layer
  (section 2), since Z and Z_tw are.
- **The crossing point:** the involution has exactly one fixed point, F = log(1 + √2) ≈ 0.881 (`dual_selfDual`; r4-conjw's
  `self_dual_point`, `self_dual_unique` prove the same and uniqueness). There F_e = F_m: the electric flux and the vortex cost the
  same. In the confined phase at large L, F_m → 0 (the vortex is free) and F_e grows; in a small box the roles are reversed. Every box
  family that interpolates crosses the fixed point once (the involution is strictly decreasing). This is a formal home for "going from
  existing by definition to not existing by definition": on one side of the crossing the vortex sector, on the other the flux sector,
  carries the box's free energy.
- **Where "still existing during the transition" sits:** at the self-dual box, F_e = F_m = log(1 + √2). On a symmetric box (T = L) and
  for a long enough box F_e ≈ E_e·T = z, so the self-dual box is near z ≈ 0.88, next to the scout's existence boundary z = 1 and to
  the deconfinement length (**heuristic**: F_e = E_e T holds only up to degeneracy and finite-T corrections, and T = L is not long).

## 2. Exact transport: the act is conserved per layer

### 2.1 Setting and the meaning of "the blocked action"

A blocking is a measurable map B from fine to coarse configurations; a random blocking (noise kernel) is a deterministic map on the
fine configurations together with the noise variables, so the statements cover Markov kernels. It **respects the centre** if
B ∘ Ω̂_f = Ω̂_c ∘ B. **The blocked layer** of a fine ensemble μ (periodic, twisted, or one flux sector) is its image B_*μ; **the blocked
action** is S_eff := −log of the density of B_*μ with respect to the coarse product Haar measure (for the decimation the image of
product Haar is product Haar by Haar invariance, proved (paper), so the density exists). There is one image per fine ensemble, all
made by the same kernel from the same fine action.

### 2.2 Proved (Lean)

| statement | Lean | level |
|---|---|---|
| partition functions are conserved: (B_*μ)(Ω_c) = μ(Ω_f) | `partition_map` | proved (Lean) |
| flux sector partition functions conserved: Z_e(B_*μ, B_*μ_tw) = Z_e(μ, μ_tw) | `sector_partition_conserved` | proved (Lean) |
| **the act is conserved per layer**: z(L/b, T/b; B_*μ, B_*μ_tw) = z(L, T; μ, μ_tw) with z = L·F_e/T | `act_conserved_per_layer` | proved (Lean) |
| the blocked layer inherits the centre symmetry | `map_centre_invariant` | proved (Lean) |
| coarse correlators = fine correlators of the lifts | `correlator_conserved` | proved (Lean) |
| a coarse state of charge ε lifts to a fine state of charge ε: the coarse flux sector is a subspace of the fine one | `lift_charged`, `lift_mem_sec` | proved (Lean) |
| decimation (D U)(x, μ) = U(2x, μ)U(2x + e_μ, μ) is gauge covariant, commutes with Ω̂ of the last row (fine row 2M − 1, coarse row M − 1), and with the site reflection | `decimate_gauge`, `decimate_centreFlip`, `decimate_thetaConn` | proved (Lean), any G |
| one-sided half: lifted coarse flux states of the SU(2) slice decay at least like the fine e^{−E_e n} | `blocked_flux_decay`, `su2_decimated_flux_decay` | proved (Lean), SU(2) inside |

**What exactly is conserved (the identification of lengths stated):** the pair (Z₀, Z₁) of the box, i.e. the free energies of the
two flux sectors; therefore F_e, F_m, the duality pair, and z = L·F_e/T with L and T in each layer's own lattice units (fine L, T;
coarse L/b, T/b). In physical units the box, the energy and z are the same numbers. As T → ∞, F_e/T → E_e of the **fine** transfer
operator, so the coarse layer carries the fine E_e exactly at the level of free energies. In addition the flux sector as a subspace is
carried: coarse flux states are fine flux states (`lift_mem_sec`).

### 2.3 What is not conserved, exactly

1. **The rate seen by coarse observables** (proved (Lean) as an inequality, `blocked_flux_decay`). With blocking in space only, a
   coarse observer's flux correlators are fine correlators of lifted states, so they decay at a rate ≥ E_e. With blocking in time by b,
   the coarse layer's own transfer operator (Osterwalder–Seiler reconstruction from the coarse ensemble, infinite time) is T_f^b
   restricted to the closure H_c of the lifted coarse positive-time observables, which is T_f^b-invariant; the constant (vacuum) lies in
   H_c, so λ_vac is unchanged and λ_flux^c ≤ (λ_flux^f)^b, i.e. **E_e^c ≥ b·E_e^f** (proved (paper)). Equality holds iff the spectral
   measure of some coarse flux observable reaches the top of the fine flux sector (finite dimensions: non-zero overlap with the
   fine flux ground state). Generic, not a theorem; open. The free-energy E_e (2.2) does not need it.
2. **The blocked layer is not, in general, Markov in time**, so on a finite periodic box Z_e(coarse) is not tr(P_e T_c^T) for a coarse
   T_c; the conservation is of the image ensembles, not of a coarse transfer matrix's traces.
3. **"The same S_eff for every sector" holds as: one kernel, one fine action, one image per sector.** Whether the twisted and the
   periodic images are Gibbs states of **one local coarse specification** with the coarse twist as a boundary condition is not proved;
   it requires locality of S_eff (its terms winding the torus included), the price named in r3-monotone §6.2. Open.
4. **Nothing compares the blocked action with the original action on the same box.** That is section 4.

## 3. T38 in full: reflection positivity of a blocked layer

### 3.1 Proved (Lean)

- `layer_rp` (with `coarseForm_eq`): fine layer in the factorised RP form v(p)w(p,a)w(p,b) (plane p, positive half a, reflected
  negative half b; this is `Positivity.Abstract`'s form). If the coarse plane variable c is drawn from the fine plane alone (K₀(p, c),
  K₀ ≥ 0) and the coarse positive variable y from (p, a, c) by K₊, the negative one by the same K₊ from the mirror, then for **every**
  coarse F(c, y) of the closed coarse positive half the coarse reflection form is Σ_{p,c} v K₀ (Σ_{a,y} w K₊ F)² ≥ 0. This extends
  r3's `gated_rp` (open positive half only) to the full coarse algebra, coarse plane included.
- `decimated_wilson_rp`, `decimated_wilson_rp_SU2`: the decimation of the Wilson measure on (ℤ/2Mℤ)^d (M even) is reflection positive
  under the coarse site reflection, for every bounded measurable coarse observable of the closed coarse positive half (coarse fixed
  slices included). Proof: reflection covariance (`decimate_thetaConn`) and `linkDep_decimate` (coarse closed half ← fine closed half,
  coarse planes ← fine planes) reduce it to `Positivity.wilson_rp`. With SU(2) inside.
- `straddle_breaks_rp` (toy, finite, named as such): fine layer w(b, Y) = [b = Y] on each half (RP: `straddle_fine_rp`), coarse plane
  variable c = [b̃ = b] read from both halves (reflection covariant), coarse positive y = Y. For F(c, y) = [c = 0]·(±1) the coarse form
  is −2 < 0. **A coarse plane variable read from both halves can destroy reflection positivity**, so the gating condition is not a
  technicality.

### 3.2 The exact obstruction (proved (paper))

The gated argument needs: every coarse variable of the closed coarse positive half is a function (or kernel) of the closed fine positive
half, and every coarse **plane** variable of the fine plane alone (deterministic, or with noise independent given the plane; random
plane noise needs the factorised fine form, the inequality form suffices for deterministic plane variables). `straddle_breaks_rp` shows
that dropping the plane condition can fail. It is sufficient, not necessary: a specific fine measure with a straddling blocking may
still be RP; for SU(2) Wilson with Balaban-type averaging this is open.

### 3.3 Design: which blockings respect the reflection (proved (paper))

1. **Site reflection positivity in all d directions forces the decimation.** A coarse μ-link at coarse site x is a plane variable of
   the ν-reflection through x_ν for every ν ≠ μ, so it must be read from the fine planes y_ν = 2x_ν for all ν ≠ μ, i.e. from the fine
   line through 2x in direction μ; as a positive (negative) variable of the μ-reflections through x_μ (x_μ + 1) it must be read from
   2x_μ ≤ y_μ ≤ 2x_μ + 2. The only fine links there are U₁ = U(2x, μ), U₂ = U(2x + e_μ, μ). Gauge covariance with the middle site
   integrated forces f(U₁h, h⁻¹U₂) = f(U₁, U₂), so f = φ(U₁U₂), and φ(g a g′⁻¹) = g φ(a) g′⁻¹ forces φ(a) = a·c with c central. So the
   deterministic gauge-covariant blockings that keep gated site RP in every direction are exactly decimation times a central constant
   (with noise: U₁U₂ times independent conjugation-invariant link noise). It iterates (each level's site RP gives the next by the same
   argument with the deterministic plane form), so decimation keeps site RP at every level. Lean: one level (`decimated_wilson_rp`).
2. **Link reflection positivity allows real block averaging.** The coarse link planes (midway between coarse sites) are, for factor 2,
   fine **site** planes. The coarse algebra of a link reflection excludes the crossing links and has no plane variables; it needs only
   that coarse links of the open coarse positive half be read from the closed fine positive half. A coarse μ-link may then read the fine
   variables in a window of transverse radius 1 around the coarse sites (y_ν ∈ [2x_ν − 1, 2x_ν + 1]) and [2x_μ − 1, 2x_μ + 3] along μ:
   Balaban/APE-type averages over such windows qualify, provided the kernel is reflection covariant and acts independently on the two
   sides (block-local; no global gauge fixing or noise coupling across the plane).
3. **Factor 2 breaks at the second step; an odd factor does not.** With factor 2 the level-k link planes are level-(k − 1) site
   planes, so link RP at level 2 needs site RP at level 1, which by 1. requires level 1 to be a decimation. A chain of averaging
   blockings with factor 2 keeps RP for one step only. With **factor 3**, coarse site X at fine 3X, blocks {3X − 1, 3X, 3X + 1}^d tile
   the lattice, and the coarse link planes 3X + 3/2 are fine **link** planes. Level-k link planes are level-(k − 1) link planes, every
   coarse link of the open half reads only fine variables strictly inside that half (transverse window [3X_ν − 1, 3X_ν + 1] ⊂
   (3X_ν − 3/2, 3X_ν + 3/2), longitudinal [3X_μ − 1, 3X_μ + 4]), and `gated_rp` (inequality form) carries link RP from each level to
   the next, at every level, in every direction. **This is the reflection-respecting blocking for T38 at every layer:** block-local,
   gauge-covariant averaging with an odd blocking factor. Literature not checked (constructive RG often uses odd L; whether RP was
   tracked this way I do not know). Lean: not done (only the factor-2 decimation instance).
4. Link RP gives a self-adjoint transfer operator T; T ≥ 0 needs site RP, and T² ≥ 0 always. The flux energy is then read from |λ|
   (or from T², two steps). Proved (paper), standard.

The transfer-matrix reading of section 1 therefore exists at every blocked layer of a factor-3 averaging chain (link RP), and at every
layer of a decimation chain (site RP).

## 4. What stays one-sided, exactly (target for r4-conjw)

The exact identity (`act_conserved_per_layer`) turns "z on the box 2L" into "z on the box L of the blocked layer":

  z(2L; μ_{2L,β}) = z(L; D_*μ_{2L,β})   (factor 2; for factor 3, z(3L; ·) = z(L; ·)).

Growth of z at fixed β, z(2L) > z(L), is therefore the inequality

  **E_e(L; D_*μ_{2L,β}) > E_e(L; μ_{L,β})**: two different ensembles on the same coarse box,

and along a line of constant physics the same with μ_{L,β′} on the right. In Conjecture W's per-direction form (r4-conjw,
`Attempts.R4.ConjW.four_move_identity`, `conjW_doubling`): widening x by 2 is, by the same exact transport with a decimation in x only
(paper; the Lean lattice is isotropic, so the anisotropic decimation is not formalised, the proof is identical), the ratio
w_x = E_e(L; D^x_*μ)/E_e(L; μ) of the flux energies of the x-decimated image (an anisotropic coarse ensemble on the same box, same
time units) and of the original; W asks w_x ≥ (1 + δ)/2.

What any proof of that inequality must contain (none of it is in this note):
- it compares **two measures**; reflection positivity orders nothing between two measures (r3-monotone §2), and every inequality used
  here is group-blind;
- it must be **two-sided with a margin**: for U(1) the two sides are equal at light's factor 1/2 (z frozen), for Z₂ and the finite
  subgroups the relief exceeds 1/2 (z falls);
- it must use **"−1 is a commutator of G"** (twist eaters; the owner's causal round trip a b a⁻¹ b⁻¹ that closes on the centre),
  since the binary dihedral group of order 12 is non-abelian without it (r4-conjw), and the **continuum of fluctuations** (b₀ > 0),
  since 2I has twist eaters and still falls. **No statement of this note uses twist eaters**: everything here holds for every group
  with a central element of order 2, which is why it is exact and why it cannot by itself give growth.
- the order of limits (T → ∞ before the comparison) does not affect the identity, which holds at every T; it enters only in the
  comparison.

## 5. Unit tests

| test | what this note's statements give | verdict |
|---|---|---|
| photon (U(1), z = e^{iπ}) | flux sectors exist, E_e ≥ 0, TTL bound, transport identities, T38 (`un_fluxEnergy_nonneg`; the kernel, transport and RP theorems are group-general). z is frozen at 2πα (known); nothing here gives a gap or growth | pass |
| Z₂ (weak coupling, deconfined) | all identities hold; E_e ≥ 0 only (Z₂'s flux energy falls like e^{−cβL²}); nothing claims growth or an area law; the gap of Z₂ is not contradicted | pass |
| finite subgroups (Q8, 2T, 2O, 2I; centre {±1}) | trace-level section 1.3 applies exactly (finite T); transport and T38 hold; z falls at large β (scout §2.2), consistent with no growth claim | pass |
| deconfinement (L < 1/T_c ≈ 1.45/√σ) | the identities hold at every L, including deconfined boxes; no claim of decay, of z ≥ 1, or of a strong-coupling condition at any scale | pass |
| triviality (φ⁴₄) | no existence claim; no centre, no flux sector | not applicable, pass |

These are exact identities and non-strict inequalities, so they **must** hold for every group: they claim nothing that separates
SU(2) from the rest. The step that must break the symmetry is the comparison of section 4 (the blocked image against the original on
the same box), and it must fail visibly for U(1) (equality), Z₂ and the finite groups (reverse inequality), and must not assert z ≥ 1
below L_*.

## 6. Status of the open piece (round-4 claim discipline)

This note proves no reduction of the mass gap. For the act-identity route the open items are, plainly: (existence) a continuum
limit of the flux energies along a line of constant physics; (identification) that limit is SU(2) Yang–Mills (tuning: the scout's
z(L_*) = 1); (observables) the vacuum-sector gap, which a flux-sector energy does not bound (the scout's "sector transfer", open);
(positivity) RP of blocked layers is settled here for decimation and, on paper, for odd-factor block averaging, not for Balaban's
factor-2 averaging; (symmetry) hypercubic symmetry is exact on the lattice, rotation invariance of the limit is open; (the comparison)
section 4. Neither "exactly one open piece" nor any reduction is claimed.

## 7. Next step

Prove, or refute on a toy that keeps the four features, the **two-sided flux-energy comparison of section 4 in its smallest form**:
one x-decimation of the SU(2) Wilson ensemble against the original on the same box, in the flux sector, at weak coupling where both
sides are semiclassical (fractional instanton upper bound, Bogomolny lower bound; scout candidate 3), so that w_x > 1/2 is certified
at the weak end with a stated margin and fails for U(1) and 2I. In parallel, cheap: formalise the factor-3 link-RP chain (§3.3,
item 3) as an instance of `gated_rp`, which would give T38 at every layer of a genuine averaging RG in Lean.

## 8. Files

- `NOTE.md` (this note); `build.sh <module>` (one module, WSL `~/formal-att-r4-2`, full log in `~/formal-att-r4-2/build.log`);
  `axioms.sh` (builds all five, prints the axiom sets of 51 headline theorems, scans for `sorry`/`axiom`/`native_decide`). Run with
  `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/attempts/r4-layer/axioms.sh`.
- `../../../formal/Attempts/R4/LayerSector.lean` (Mathlib, `Positivity.Abstract`, `Attempts.R3.MonotoneCrossing`): sections 1.2 (abstract),
  1.3, 1.5.
- `../../../formal/Attempts/R4/LayerKernel.lean`: the Wilson kernel, Ω̂, the Wilson and SU(2) flux-sector theorems.
- `../../../formal/Attempts/R4/LayerTwisted.lean`: the magnetically twisted box, U(n).
- `../../../formal/Attempts/R4/LayerTransport.lean`: transport (section 2), `layer_rp`, the straddle counterexample.
- `../../../formal/Attempts/R4/LayerDecimation.lean`: the decimation blocking, its covariances, T38 for the blocked SU(2) layer, the
  SU(2) one-sided transport.
