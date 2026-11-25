# Workstream 2, Route B: flux energy on the 4D measure, the sector transfer, duality (2026-11-22)

Brief: free win 1 (the flux energy from the real 4D measure), the sector transfer P5.1 (main target), clicks (inversion = duality,
Chatterjee's centre argument). Lean: `../../../formal/ProofPhase/RouteB/{HankelRate,Chain,FluxEnergy,Duality,Sector}.lean`, built in
`~/formal-ws2` (Lean 4.34.0, Mathlib v4.34.0) with `build.sh <module>`; `axioms.sh` builds all five, greps for `sorry`/`native_decide`/
`axiom` (none), and prints the axioms of 21 headline theorems: all `propext, Classical.choice, Quot.sound`. No numerics were run (none
was needed to decide anything here). Nothing outside this folder and `formal/ProofPhase/RouteB/` was edited.

Claim levels: **Lean**, **Lean (definitional)**, **paper** (complete argument here), **standard** (literature, cited), **read** (checked
in the source this session, through a summarising fetch of the arXiv/ar5iv HTML), **numerical** (others' data), **open**.

---

## 0. Result in plain words

1. **The flux energy is now an object of the real 4D measure (free win 1, Lean).** New anisotropic lattice `ℤ/Tℤ × (ℤ/Lℤ)³`,
   built as a time chain over an arbitrary spatial graph, with reflection positivity, time-translation invariance and the Hankel
   identity proved on it, for every compact group and every spatial (magnetic) twist. For the spatially summed Wilson line `Φ`
   around the first spatial axis (centre-odd, mean zero by a Lean centre-symmetry theorem), every limit `h` of the normalised
   correlation `⟨Φ(a_t)Φ(a_0)⟩_T` as `T → ∞` is a reflection-positive Hankel sequence; its effective masses decrease to a rate
   `fluxRate h ≥ 0` (approached from above) and `|h(t)| ≤ h(0) e^{−fluxRate·t}` with no prefactor; the rate is sharp. No temporal
   gauge, no Gauss projection. Group-blind: it defines the number, it says nothing about its size (strict `E_e > 0`, growth).
2. **Kanazawa's theorem does not close P5.1, and no twist/flux inequality can (section 2).** Every rigorous twist-to-decay inequality
   (Tomboulis–Yaffe, Kanazawa's Theorems 1–5, Borgs–Seiler) concludes decay of observables **charged** under the twisted symmetry;
   its zero-average hypothesis (Kanazawa's (100), which he calls indispensable) is false for every centre-neutral observable, and the
   observables of `MassGap` are centre-neutral. More: the zero-momentum, parity-even neutral sector (the 0⁺⁺ glueball) is neutral
   under **every** symmetry of the lattice theory, so no twist of any symmetry sees it. And a rigorous counterexample: the lattice
   gauge theory with group SU(2) × U(1) (product Wilson measure) at strong SU(2) and weak U(1) coupling has growing SU(2) flux energy
   and no gap (the photon). So `FluxGrowth ⇒ MassGap` cannot follow from reflection positivity, centre structure and flux growth;
   it would need Yang–Mills dynamics beyond the flux sector.
3. **Routes A and B meet, on Route A's side.** In Lean (definitional): `SlabDecay ⇒ SectorTransfer` and ws4's `TorusDecay ⇒
   SectorTransfer`. Route B's natural endpoint is confinement: with the sector identity, an order-of-limits bound (B3) and linear flux
   growth `E_e(L) ≥ ρL` (stronger than Conjecture W), Tomboulis–Yaffe plus the Lean rotation give the area law of Wilson loops
   uniformly in the box (paper, conditional). Conjecture W with a small margin gives **nothing** in infinite volume through this route
   (exponent count, section 2.4).
4. **'t Hooft duality proper is in Lean (P1.4′).** The lattice rotation `(0 2)(1 3)` maps the temporal twist (plane 01) to the spatial
   twist (plane 23) on the symmetric box, so the twisted partition functions agree, and the electric-flux ratio is the same function
   of the magnetic twist. This is the owner's inversion: it exists only on the symmetric box (`T = L`).
5. **The click (section 3):** Chatterjee's centre transform, Kanazawa's wall operator for the centre, 't Hooft's `Ω̂`, and the Lean
   `flipA` that makes `Φ` odd are one operator, the centre symmetry acting on the links that cross one hyperplane, in different
   orientations; the lattice rotation turns one into another; its `Z₂` Fourier transform is the electric-flux split. Chatterjee goes
   neutral ⇒ charged (all-boundary decay ⇒ unbroken centre ⇒ confinement); Kanazawa goes charged ⇒ charged. Nobody goes charged ⇒
   neutral, and the counterexample says nobody can without dynamics. The loop C2 of `READING.md` does not close.

---

## 1. Free win 1: the flux energy from the 4D Wilson measure (Lean)

### 1.1 The anisotropic lattice (`Chain.lean`)

Links `CLink E S T = ℤ/Tℤ × (E ⊕ S)`: `(t, inl e)` the spatial link `e` of slice `t`, `(t, inr s)` the temporal link from `(t, s)` to
`(t+1, s)`; `E` (spatial links) and `S` (spatial sites) are any finite types. Weight (`ChainWeight`):
`W(U) = ∏_t V(a_t) K(a_t, b_t, a_{t+1})`, `V, K ≥ 0` bounded measurable, `K(c, b⁻¹, a) = K(a, b, c)`. Reflection `Θ`: `a_t ↦ a_{−t}`,
`b_t ↦ b_{−t−1}⁻¹` (fixed slices `t = 0, T/2`, `T` even).

* `cweight_factor` (**Lean**): `W(U) = A(U)·A(ΘU)·B(U)`, `A` the open positive half, `B` the fixed slices. The only lattice input.
* `chain_rp` (**Lean**): `∫ F·(F∘Θ)·W d(Haar) ≥ 0` for bounded measurable `F` of the closed positive half (via `Positivity.config_rp`).
* `cweight_cshift`, `measurePreserving_cshift` (**Lean**): time-translation invariance.
* `cform_slice` (**Lean**, Hankel identity): `⟨f(a_j), Θ f(a_k)⟩ = C(j+k)`, `C(t) = ∫ f(a_t) f(a_0) W`.
* `ccorr_cs`, `ccorr_nonneg`, `nCorr_cs`, `nCorr_nonneg`, `abs_nCorr_le` (**Lean**): Hankel Cauchy–Schwarz for `j, k ≤ T/2`, normalised.
* `exists_isTimeLimit`, `rpSeq_of_isTimeLimit` (**Lean**): time extents `T_M = 2(M+1)`; limit points of the normalised correlation
  exist (compactness of `[−C, C]^ℕ`), and every limit is a reflection-positive Hankel sequence (`RPSeq`).

### 1.2 The rate (`HankelRate.lean`, real analysis)

For `RPSeq h` (`h(j+k)² ≤ h(2j)h(2k)`, `h(2j) ≥ 0`, bounded): `eq_zero_of_le` (if some `h(2s) = 0`, `h` vanishes from `2s` on);
otherwise, with `m(s) = ½(log h(2s) − log h(2s+2))`: `effMass_antitone`, `effMass_nonneg` (boundedness), `tendsto_effMass` to
`rate h = inf_s m(s) ≥ 0`, `rate_le_effMass`, **`abs_le_rate`: `|h(t)| ≤ h(0) e^{−rate·t}`**, `lower_effMass`,
`rate_sharp` (for every `ε > 0` eventually `h(2(s₀+n)) ≥ h(2s₀) e^{−2(E+ε)n}`), `rpSeq_of_limit`, `exists_limit`.

### 1.3 The Wilson instance (`FluxEnergy.lean`)

* `wilsonChain L hc hU β P`: `V = sliceV` (the spatial plaquettes of a slice, signs `−1` on a twist set `P`), `K = stepK` (one temporal
  plaquette per spatial link, holonomy `b(x) c(e) b(x+î)⁻¹ a(e)⁻¹`). These are exactly the plaquettes of `ℤ/Tℤ × (ℤ/Lℤ)³`; the
  weight is the 4D Wilson weight with a magnetic twist (by definition; stated in the module docstring). `stepK_symm` (**Lean**) is the
  reflection symmetry (conjugation invariance and `Re tr g⁻¹ = Re tr g`).
* `polySum`: `Φ(a) = Σ_y Re tr P_y(a)`, `P_y` the Wilson line once around the first spatial axis.
* Centre symmetry (**Lean**): `flipA` multiplies the first-axis links of the plane `x₀ = c` by a central `z`; `sliceV_flip`,
  `stepK_flip` (weight invariant), `polySum_flip` (`Φ ↦ −Φ` when `rep z = −1`), `polySum_mean_zero`, `su2_polySum_mean_zero`:
  `∫ Φ(a_t) W = 0` on every anisotropic torus. So `⟨Φ(a_t)Φ(a_0)⟩` is the connected correlation of a centre-odd observable.
* **`fluxEnergy_props`, `su2_fluxEnergy_props` (Lean):** for every flux time limit `h`: `RPSeq h`, and either `h` vanishes from some even
  time on, or `h(2s) > 0` for all `s`, `0 ≤ fluxRate h`, effective masses antitone, converging to `fluxRate h`, each an upper bound,
  and `|h(t)| ≤ h(0) e^{−fluxRate(h) t}` for all `t`.

**What is substantive, what is not.** Substantive: reflection positivity and the Hankel structure of the anisotropic Wilson measure
with any spatial twist; closedness under `T → ∞`; centre oddness of `Φ` with its zero mean. Group-blind: all of it (U(1), Z₂, finite
subgroups included). Not claimed: `fluxRate > 0` (P1.7), any size or growth (P4.2), uniqueness of the time limit (true if the transfer
matrix has a simple top eigenvalue, Perron–Frobenius, not formalised), the identification with `ProofPhase.fluxE` (Gauss-law states,
`Z = tr(P_G Tⁿ)`). Physics reading (standard, not Lean): by the transfer matrix, `h(t) = Σ_k |⟨k|Φ|Ω⟩|² e^{−t(E_k−E_0)}` over states in
the sector `e₁ = 1`, so `fluxRate` is the energy of the lowest one-unit-flux state `Φ` reaches (zero transverse momentum).

**Proposed change to the assembly (not made; ASSEMBLY.md missing piece 6 and P7.5).** Replace `fluxE`/`actZ` in `Objects.lean` by the
4D definition: `actZ4 β L := L · fluxRate h` for flux time limits `h` of `wilsonChain L … β ∅` (all limits, or assume uniqueness as a
named field), and restate `OnLCP.scheme` and `ConjW` with it. Then no transfer operator, Gauss law or `tr(P_G Tⁿ)` is needed anywhere,
and the per-move form of W (anisotropic boxes) becomes statable: `Chain.lean` takes any spatial graph, so `L_x × L_y × L_z` boxes are a
one-line change of `E`, `S`.

---

## 2. The sector transfer P5.1

### 2.1 Kanazawa's theorems, exactly (read: arXiv:0808.3442, Annals Phys. 324 (2009) 1634; the whole HTML text in three passes)

* **Setting.** Periodic hypercubic lattice, side lengths `L_μ` (anisotropic allowed), all directions periodic. Site reflection
  positivity only (link RP not used); any one-plaquette action with nonnegative character coefficients (Wilson included).
* **Theorem 1 (Tomboulis–Yaffe 1985, SU(2)).** `C` a rectangle in the `μν`-plane, area `A_C`; the vortex `𝒱` = the `μν`-plaquettes at
  fixed `(x_μ, x_ν)`, wrapping the other `d−2` directions, entering as `−U_p`; `Z⁻` the twisted partition function:
  `⟨W(C)⟩ ≤ 2 {½(1 − Z⁻/Z)}^{A_C/(L_μ L_ν)}`, with the dyadic condition `L_μ = 2^p l_μ`, `L_ν = 2^q l_ν`.
* **Theorem 2 (SU(N)).** With the vortex operator `𝒪^{[k]}[𝒱]` and `⟨ℱ^{[0]}[𝒱]⟩ = (1/N)Σ_k⟨𝒪^{[k]}[𝒱]⟩` (the `Z_N` average of the
  twisted ratios), for N-ality `≠ 0`: `|⟨W_R(C)⟩| ≤ 2 {1 − ⟨ℱ^{[0]}[𝒱]⟩}^{A_C/(L_μL_ν)}`. Theorem 3 (matter of N-ality m), Theorem 4
  (U(1), continuous twist angle).
* **Theorem 5 (spin systems, the generalisation).** Nearest-neighbour action with a compact global symmetry `G`; correlator
  `Γ_μ(x; n) = Σ_α f_α(φ_x) conj f_α(φ_{x+nμ̂})`, (99) `Γ` is `G`-invariant, **(100) `∫_G dg f_α(gφ) = 0` for all `φ`** (zero group
  average; "truly indispensable"; if it fails, `f` is replaced by `f` minus its group average), `L_μ = 2^k n`, wall `𝒱` perpendicular
  to the separation direction `μ`, wall operator `𝒪(g)[𝒱]` (the interaction across the wall twisted by `g`):
  `|⟨Γ_μ(x;n)⟩|/⟨Γ_μ(x;0)⟩ ≤ 2 {⟨Γ(0)²⟩/⟨Γ(0)⟩²}^{n/L_μ} {1 − ∫_G dg ⟨𝒪(g)[𝒱]⟩}^{n/L_μ}`.
  Proof: insert `ℱ_T(1) = ∫ dg 𝒪(g)` and its complement, Schwarz in reflection planes, doubling `k − 1` times; (100) is used in the
  wall-moving step. `g` need not be central.
* **What the paper says about the gap.** It reads boundary-condition insensitivity (`⟨𝒪(g)⟩ → 1`, e.g. `1 − O(e^{−ρL_μ})`) as a sign of
  a mass gap; for spin systems `ρ` is a lower bound on the gap of the charged correlator, and its equality with the true off-axis
  mass gap is stated as a conjecture. No theorem is stated in the thermodynamic limit, no statement about local gauge-invariant
  (glueball) observables of lattice gauge theory, and insensitivity is proved for no model (strong coupling is discussed without a
  rigorous proof). The conclusion calls the result "obtained essentially on a finite lattice".

### 2.2 Why it cannot reach `MassGap` (paper, structural)

`MassGap` is about slab observables that are gauge invariant and functions of SU(2) links. For the centre symmetry they are
**neutral**: every centre transformation (`flipA` in any orientation) leaves them unchanged unless they wind around the torus, and a
local slab observable does not. (100) requires the observable to average to zero over the twisted group; a neutral observable equals
its own average, so (100) fails and Kanazawa's replacement `f − ⟨f⟩_G` is zero: the bound says nothing. The same holds for every
symmetry used as a twist: global gauge transformations act trivially on gauge-invariant observables; for SU(2) charge conjugation is
inner; translations, rotations and reflections act on neutral observables, but their twists control only the non-zero-momentum or
odd-parity parts. **The zero-momentum, parity- and charge-even sector (the 0⁺⁺ glueball channel, where the gap is decided) is invariant
under every symmetry of the theory**, so no twist of any symmetry is sensitive to it. A Kanazawa-type theorem can control charged
sectors only.

### 2.3 The counterexample (paper; cited rigorous inputs)

The lattice gauge theory with group SU(2) × U(1) and Wilson action `β₁ Re tr U + β₂ cos θ` is a product measure (Wilson SU(2) at `β₁`
times Wilson U(1) at `β₂`); it is reflection positive (a product of reflection-positive measures, with the same reflection). Its SU(2)-centre twisted partition functions, flux sectors and act number are those of the SU(2) factor alone
(Fubini). Take `β₁` small: flux confinement of the SU(2) factor (strong-coupling area law, Osterwalder–Seiler 1978, standard; growing
flux energy at strong coupling, standard cluster expansion). Take `β₂` large: the U(1) factor is in the Coulomb phase with a massless
photon (Guth 1980; Froehlich–Spencer 1982, standard): the plaquette–plaquette correlations of the U(1) links, gauge-invariant local
observables of the product theory, decay by a power law. So every hypothesis about SU(2)-centre twists, flux energies or act numbers
holds as for confining SU(2), and the neutral sector has no gap. **Any proof of `FluxGrowth ⇒ MassGap` must use dynamics that excludes
decoupled gapless neutral degrees of freedom**, e.g. that the group is simple and the action is SU(2) Wilson along the line of
constant physics. Simple-group, physics-level versions: SU(2) or SU(3) with adjoint fermions in or near the conformal window (centre
intact, confining-type, massless or near-massless neutral states; recalled); the SU(3) fundamental–adjoint endpoint, where the 0⁺⁺
mass extrapolates to zero while the theory stays confining (Heller, hep-lat/9509010, numerical, abstract-level via a search summary);
for SU(2) the endpoint evidence is weak (Lacagnina et al., arXiv:1212.0635, read: the scalar mass decreases only slightly; the endpoint's
order is disputed).

### 2.4 The two questions of the brief

* **(b) A statement about the twisted free energy** is Kanazawa's hypothesis itself, and its conclusion is charged-sector decay (Wilson
  loops, Polyakov lines). It does not give `MassGap`.
* **(a) Growth of the act number** implies (b) only through three steps: (i) the sector identity `Z_{e=0,1} = (Z ± Z₀₁)/2`
  (`Z₀₁ = tr(Ω̂₁ T^T)`, transfer matrix; standard, r3-monotone B1); (ii) **the rotation** `Z₀₁ = Z₂₃` on the symmetric box (Lean,
  `tHooft_rotation`); (iii) **the order of limits B3**: the finite-`T` electric ratio at `T = L`, `F_e(L) = −log(Z_{e=1}/Z_{e=0})`,
  against the `T → ∞` energy, `z(L) = L·E_e(L)`. RP gives only one direction here (it bounds `Z_{e=1}(T)` from **below** by the lowest
  state), while (b) needs `F_e(L) ≥ z(L) − c₀`, an upper bound on the excited-flux-state sum at `T = L`. B3 is open and is exactly
  P4.5; it is where round 4's blocking step returns.
* **Exponent count (paper).** TY gives `⟨W(C)⟩ ≤ 2(½(1 − Z⁻/Z))^{A/L²}` in a box of side `L`, and with (i)–(iii)
  `½(1 − Z⁻/Z) ≤ e^{−F_e(L)}`. If `F_e(L) ≥ c L^γ` then `⟨W⟩ ≤ 2 exp(−c A L^{γ−2})`. For a fixed loop and `L → ∞` (infinite volume)
  this tends to the trivial bound unless `γ ≥ 2`. Conjecture W with margin `δ` gives `γ = 2 log₂(1+δ)`, which is `< 2` unless the
  doubling factor `(1+δ)²` is at least 4 (W∞, linear flux energy). So **W with a small margin yields nothing in infinite volume through
  TY**; only linear confinement does.
* **Order of limits in Kanazawa.** His bounds hold in one finite periodic box, any aspect ratio. For the flux instance (separation in
  time, wall = temporal twist, box `T × L³`; this is the gauge analogue of his Theorem 5 with spatial Polyakov lines as the spins,
  the Borgs–Seiler type of statement; I checked that his doubling argument uses only site RP and the twist, not that every step
  transfers verbatim): `1 − ⟨ℱ_T⟩ = Z_{e=1}/Z(T) ≈ e^{−T E_e(L)}`, so as `T → ∞` the bound tends to
  `2 e^{−n E_e(L)}`: Kanazawa at `T → ∞` is `fluxEnergy_props` with an extra factor 2. In the symmetric box `T = L` it gives the
  finite-`T` rate `F_e(L)/L`: the B3 gap again.

### 2.5 The strongest true statements

* **Lean (definitional), the meeting point** (`Sector.lean`): `sectorTransfer_of_slabDecay : OnLCP T → SlabDecay T →
  SectorTransfer T`; `sectorTransfer_of_torusDecay : a_k → 0 → TorusDecay T.toV → SectorTransfer T` (ws4's `TorusDecay`);
  `crossover_of_slabDecay`. They ignore `FluxGrowth`: P5.1 is at most as hard as route A's crossover piece.
* **Paper, conditional, Route B's endpoint (confinement, not the gap).** Assume the sector identity (standard), B3 in the form
  `F_e(L) ≥ L·E_e(L) − c₀` on symmetric boxes, and linear flux growth `E_e(L) ≥ ρL` for `L ≥ L₀`. Then for every `R × R` spatial
  Wilson loop and every symmetric box of side `L ≥ max(R, L₀)` (dyadic conditions as in TY):
  `⟨W⟩ ≤ 2 e^{c₀} e^{−ρR²}`, uniformly in `L`, so every infinite-volume limit point has an area law. Proof: (ii) Lean rotation, TY
  (Kanazawa Theorem 1), `½(1 − Z⁻/Z) = r/(1+r) ≤ r = e^{−F_e}`, `A ≤ L²`.
* **No-go (paper):** no implication `Y ⇒ MassGap` with `Y` a statement about SU(2)-centre twisted free energies, flux energies or act
  numbers holds for all reflection-positive compact-group lattice gauge theories (section 2.3). For SU(2) Wilson specifically the
  implication is not refuted; no mechanism for it is known.

**Verdict on P5.1:** not closed; the Kanazawa route is closed off (structurally). P5.1 lands on Route A: whatever proves it will be a
neutral-sector decay statement of `SlabDecay`/`TorusDecay` type, and then Route B's flux hypotheses are not used.

### 2.6 For workstream 1 (Route A)

Routes A and B meet at Route A's hypothesis: `SlabDecay ⇒ SectorTransfer` and `TorusDecay ⇒ SectorTransfer` are now in Lean
(`ProofPhase/RouteB/Sector.lean`). Nothing on the flux side helps `SlabDecay`; the one thing Route B can hand to Route A is the
scale: `lcp.scheme` (the act number fixes `L₁`), now definable from the 4D measure (`fluxRate`). If a Route A argument wants a
centre-blind condition (free win 4), section 2.2 is the reason it is natural: the vacuum sector is blind to every centre twist.

### 2.7 For workstream 4 (their points 1–4)

(1) `Sector.lean` imports the current `Assembly.lean` (with the corrected `oneLoopSlope`) and builds. (2) Done:
`sectorTransfer_of_torusDecay`. (3) **β(unit) ↔ z(L₁).** With `fluxRate` the act number is a measurable function of the 4D measure at
every level. Their condition fixes a coupling at one length; ours fixes `z(L₁)`. At weak coupling (small `L₁`) the two are equivalent to
leading order through the semiclassical relation `z(L) ≈ C(L)·e^{−4π²/g²(L)}` with `d log z/d log L = γ_z ≈ 11/3` (r4-conjw §4), a
strictly monotone function of the running coupling; making that an equivalence needs exactly B1–B3 of r4-conjw (attained floor,
fluctuation prefactor along the LCP, order of limits). So: equivalent modulo B2, B3; not provable here. (4) In a finite spatial box the
time limit has no phase choice (simple top eigenvalue, Perron–Frobenius, standard); the possible non-uniqueness of the time limit in
`IsFluxLimit` is a formal artefact, not a phase issue.

---

## 3. Clicks

### 3.1 The inversion is the lattice rotation ('t Hooft duality proper, Lean)

`Duality.lean`: `permPlaq`, `xp_rotU` (a coordinate permutation permutes `Re tr` of plaquette holonomies, inverting the orientation
when the axis order flips), **`twistZ_perm`** (the twisted partition function is invariant when the permutation maps the twist set onto
the other), **`tHooft_rotation`** (`(0 2)(1 3)` maps the temporal twist `P₀₁` to the spatial twist `P₂₃`; every compact group, every
`β`, every `N`), `electric_eq_magnetic` (`ring`). With the sector identity this is `F_e(e₁) = dual(F_m(m₁))`,
`dual(F) = −log tanh(F/2)`, on the symmetric box (P1.4′). The owner's reading "an existence boundary is an inversion" becomes precise
here: the inversion `dual` is an exchange of two twists by a symmetry that exists **only when `T = L`**; at `T → ∞` (the flux energy)
there is no rotation and no duality, which is the B3 gap seen from the other side. The self-dual box (round 4: `F = log(1+√2)`, near
`1/T_c`) is the symmetric box at which the temporal and spatial twist cost the same; it sits where the box temperature `1/L` crosses
`T_c` (heuristic, r4-conjw §6).

### 3.2 Chatterjee, Kanazawa, 't Hooft and `flipA` are one operator

* Chatterjee (read: arXiv:2006.16229v5, sections 2–3): the centre transform multiplies the links crossing from the bottom layer of a slab
  to the next by `g₀`; Definition 2.1: unbroken centre symmetry if every Gibbs measure of the slab, for some width, is invariant under any
  boundary condition; Theorem 2.2: then every Gibbs measure has `|⟨W⟩| ≤ e^{−V(R)T}` with `V(R) → ∞` (rectangles `R ≤ T`, irreducible
  representation nontrivial on the centre); Theorem 2.4: decay `|⟨fg⟩ − ⟨f⟩⟨g⟩| ≤ K₁e^{−K₂ dist}` for all cubes, all boundary
  conditions, local `f, g` ⇒ unbroken centre symmetry and the area law. Mechanism: Schur (`π(g₀) = c ≠ 1`) forces charged expectations
  to vanish; conditioning on interfaces multiplies the bound over sub-slabs.
* In the chain picture: multiplying the temporal links `b_0` of one slice by a central `z` is a symmetry of `K` (both temporal links of
  each temporal plaquette move) — Chatterjee's transform with time as the slab direction; its charged objects are temporal Polyakov
  loops. `flipA` (Lean) is the same operator on the links crossing the plane `x₁ = c`; its charged objects are spatial Polyakov loops
  (`Φ`, the flux). Kanazawa's `∫ dg 𝒪(g)[𝒱]` for the centre group is the projector average of the twist across one wall, and
  `1 − ⟨ℱ_T⟩ = Z_{e=1}/Z`. 't Hooft's `Ω̂` with `Z_tw = tr(Ω̂ T^N)` is again the same. The lattice rotation maps the orientations onto
  each other; on the symmetric box this is `tHooft_rotation`.
* **What separates the three uses** is the direction of the arrow. Chatterjee: neutral-sector decay for all boundary conditions ⇒ the
  operator acts trivially ⇒ charged expectations vanish (confinement). Kanazawa/TY: insensitivity to the operator ⇒ charged decay.
  't Hooft: the operator's trace = flux partition function. All three end in the charged sector; only Chatterjee starts in the
  neutral one, and his input is Route A's kind of hypothesis (stronger: all boundary conditions, all cubes, D′-like). So C2's loop
  "gap ⇒ confinement (Chatterjee), twist insensitivity ⇒ gap (Kanazawa), growth of z ⇒ twist insensitivity (duality)" does not close:
  the middle arrow is "twist insensitivity ⇒ charged decay", not "⇒ gap". C1's question (does centre-twist insensitivity give
  insensitivity to all boundary conditions?) has the answer no in general: the product counterexample is centre-twist insensitive
  and has a gapless neutral sector.

---

## 4. Headline theorems (exact statements in the Lean files; marks)

| theorem | statement (short) | mark | Yang–Mills inside? |
|---|---|---|---|
| `RPSeq.abs_le_rate`, `rate_sharp`, `tendsto_effMass`, `effMass_nonneg` | RP Hankel sequences: effective masses decrease to `E ≥ 0`, `\|h(t)\| ≤ h(0)e^{−Et}`, `E` sharp | Lean, real analysis (any RP system) | no |
| `rpSeq_of_limit`, `exists_limit` | limits of finite-range Hankel families are RP Hankel; limit points exist | Lean, real analysis | no |
| `cweight_factor`, `chain_rp` | anisotropic time-chain weight factorises; reflection positivity | Lean, substantive (lattice RP), group-blind | lattice + any chain weight |
| `cform_slice`, `ccorr_cs`, `nCorr_cs` | Hankel identity and Cauchy–Schwarz on `ℤ/Tℤ × box` | Lean, substantive, group-blind | same |
| `exists_isTimeLimit`, `rpSeq_of_isTimeLimit` | `T → ∞` limits exist and are RP Hankel | Lean, substantive, group-blind | same |
| `stepK_symm`, `wilsonChain` | the 4D Wilson weight (any spatial twist) is a chain weight | Lean (the plaquette bookkeeping is by definition) | Wilson action, any compact group |
| `polySum_flip`, `polySum_mean_zero`, `su2_polySum_mean_zero` | `Φ` centre-odd, weight centre-invariant, `⟨Φ⟩ = 0` | Lean, substantive (a symmetry), group-blind given `z` central with `rep z = −1` | SU(2) instance |
| **`fluxEnergy_props`, `su2_fluxEnergy_props`** | flux energy of the 4D measure: well defined, `≥ 0`, effective masses from above, no-prefactor bound | Lean; substantive as RP structure, **no physics content about its value** | SU(2) Wilson on `ℤ/Tℤ × (ℤ/Lℤ)³` |
| `twistZ_perm`, **`tHooft_rotation`** | coordinate permutation maps twists; `Z₀₁ = Z₂₃` on the symmetric box | Lean, substantive but elementary (lattice symmetry), group-blind | Wilson, any group |
| `electric_eq_magnetic` | `(Z−Z₀₁)/(Z+Z₀₁) = (Z−Z₂₃)/(Z+Z₂₃)` | Lean (definitional given the rotation, `rw`) | same |
| `sectorTransfer_of_slabDecay`, `sectorTransfer_of_torusDecay`, `crossover_of_slabDecay` | Route A's hypotheses discharge `SectorTransfer` | Lean (definitional) | via the assembly's objects |
| Route B endpoint (section 2.5) | sector identity + B3 + `E_e ≥ ρL` ⇒ area law uniformly in the box | paper, conditional; uses TY (standard) and the Lean rotation | yes (SU(2) Wilson) |
| no-go (2.2, 2.3) | no twist/flux hypothesis gives neutral decay for all RP compact-group lattice gauge theories | paper; counterexample rigorous by citation (Osterwalder–Seiler, Guth, Froehlich–Spencer) | — |

---

## 5. Unit tests

| test | what happens | verdict |
|---|---|---|
| photon (U(1), weak) | Lean results hold for U(1) and claim no positivity or growth of `fluxRate`; Kanazawa's hypothesis fails (twist free energy finite); the photon is the counterexample in 2.3 | pass |
| Z₂ (weak) | gap without flux floor: shows gap ⇏ flux growth; nothing here claims either for Z₂ | pass |
| finite subgroups (Q8, 2T, 2O, 2I) | twist free energies frozen at large β (r3-monotone), Kanazawa's hypothesis fails; the Lean results are group-blind and claim nothing | pass; no theorem here separates them from SU(2) (said so) |
| deconfinement (`L < 1/T_c`) | `fluxRate` small there is allowed; Route B's area-law endpoint needs `E_e ≥ ρL` only for `L ≥ L₀` | pass |
| triviality (φ⁴₄) | no existence claim | pass |
| Banks–Zaks | fundamental matter breaks the centre: `flipA` is no symmetry and `polySum_mean_zero` does not apply; adjoint matter keeps it and is the physics-level version of the 2.3 counterexample | pass |
| "−1 is a commutator" | not used (necessary, not separating: Q8, 2T, 2O, 2I have it) | — |

---

## 6. Status changes for the blueprint (proposed; `PROOF-BLUEPRINT.md` not edited)

* **P1.3′** open → **Lean**: the flux energy as the decay rate of a centre-odd slab observable on the 4D measure (`fluxRate`,
  `fluxEnergy_props`), on anisotropic tori `ℤ/Tℤ × (ℤ/Lℤ)³` (`Chain.lean`), with spatial twists. Still open: `fluxRate > 0` (P1.7),
  uniqueness of the time limit, identification with the Gauss-law transfer operator (no longer needed if the assembly adopts `fluxRate`).
* **P1.4′** open → **Lean** for the Euclidean statement (`tHooft_rotation`); the sector reading of `Z₀₁` stays standard (transfer
  matrix), not Lean.
* **P4.5 (B3)** open, sharpened: the finite-`T = L` electric ratio vs the `T → ∞` energy; RP gives only the lower bound on the
  flux-sector sum; an upper bound on excited flux states at `T = L` is what Route B needs.
* **P5.1** open, "no known route" → **"no route through twist/flux inequalities (structural no-go, rigorous counterexample for
  non-simple groups); discharged by Route A's `SlabDecay`/`TorusDecay` (Lean, definitional)"**. Recommendation: treat Route B as the
  route to confinement (area law from linear flux growth, conditional on B3) and as the source of the scheme `lcp.scheme`; drop it as a
  route to the gap unless a dynamical mechanism specific to simple groups is found.
* **P4.2** unchanged (open); note that Conjecture W with doubling factor below 4 gives no infinite-volume confinement through TY.
* **P7.5**: "the flux energy from the 4D measure (needs anisotropic tori)" → available (`ProofPhase.RouteB.Chain`, `FluxEnergy`).

---

## 7. Next step

Route B's useful remainder is B3 in the form `F_e(L) ≥ L·E_e(L) − c₀` at `T = L`: an upper bound on the flux-sector partition function
by its lowest state. It is a statement about the spectrum of the twisted box, and the chain framework is where to try it: the
temporal twist is an insertion of `flipA` in one slice of `Chain.lean`, so `Z_{e=1}(T)/Z(T)` is a chain integral, and RP doubling gives
the lower bound for free; the upper bound needs a gap between the lowest and the next flux states uniform in `L` (or a bound on their
number), which is the same kind of input as the vacuum gap. If that is judged not worth it, Route B's work is done: adopt `fluxRate`
in the assembly (section 1.3) and put all effort on Route A's `SlabDecay`/`TorusDecay`.

---

## Build

```
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws2-routeB/build.sh ProofPhase.RouteB.FluxEnergy
wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws2-routeB/axioms.sh
```

`grep-mathlib.sh` is a helper used during development (lemma-name lookups in the Mathlib copy).

## Sources (this session)

Kanazawa, arXiv:0808.3442 (ar5iv HTML, read in three passes through a summarising fetch); Chatterjee, arXiv:2006.16229v5 (HTML, first
100k characters: definitions and Theorems 2.2, 2.4, the mechanism); Lacagnina et al., arXiv:1212.0635 (ar5iv, conclusion on the SU(2)
endpoint); Heller, hep-lat/9509010 (search summary only). Tomboulis–Yaffe (1985) and Borgs–Seiler (1983) were not read directly: TY as
stated in Kanazawa's Theorem 1; Borgs–Seiler only through Kanazawa's remark that their inequality links the Polyakov-loop correlator to
the twist.
