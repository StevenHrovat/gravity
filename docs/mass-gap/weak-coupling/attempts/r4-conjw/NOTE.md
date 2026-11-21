# Round 4, attempt 3 (r4-conjw): where asymptotic freedom enters, and the weak end (2026-11-21)

Brief: state Conjecture W (widening relief) precisely; prove its abelian counterpart (the photon's exact marginality) and its failure
for Z₂ and the finite subgroups of SU(2); find the mechanism and the margin for SU(2); certify the weak end as a two-sided sandwich, or
record exactly what blocks it; say what W would deliver. Two later requests from the coordinating session are built in: the owner's
"existence boundary as an inversion" (§6, the inversion box) and the **Banks–Zaks test** (§7.2).

Claim levels: **proved (Lean)**, **proved (paper)** (complete argument here), **proved with a stated gap**, **certified/exact
computation**, **known** (literature; "read" when checked in the source this session, "recalled" otherwise), **heuristic**,
**conjecture**, **reading** (the owner's terms, not mathematics). Every target says whether it is weaker than, equal to, or stronger
than the mass gap (RULES, round 4).

Files: this note; `PREREG.md` (written before the run; result section added after); `groups_check.py`, `groups_check.json` (one CPU
process, under a second); `build.sh` (Lean build in `~/formal-att-r4-3` only). Lean: `../../../formal/Attempts/R4/ConjW.lean`
(10 theorems, toys by name and header; build result in §10).

---

## 0. Result in plain words

1. **Conjecture W, stated (§1).** In a periodic box with a magnetic 't Hooft twist in the xy-plane, let E(Lx, Ly, Lz) be the energy of
   the lowest state with one unit of centre flux along z, after the time extent has gone to infinity. W says: lengthening the flux
   direction at least doubles E, and widening either transverse side multiplies E by at least (1 + δ)/2, more than light's ½. Then the
   act number z(L) = E(L, L, L)·L grows by (1 + δ)² per doubling. It is stated in the continuum (along the line of constant physics,
   with the existence of the continuum box energies as an explicit hypothesis) and on the lattice with an artefact allowance. It is
   **not** a fixed-lattice, β → ∞ statement: there the widening ratio is decided by the sign of the lattice action's a² correction
   (§5.3), for SU(2) as well.
2. **The photon is exactly marginal (§2, proved).** For the free lattice photon (compact zero modes, Villain form, with or without the
   twist), E_n = g² n² Lz/(2 Lx Ly) **exactly, at every lattice size and every coupling**, and the same in the continuum: lengthening
   doubles E, widening halves it, z = g²/2 = 2πα is frozen. Checked numerically to 1e−14 (C6).
3. **Z₂ and the finite subgroups fail W at weak coupling (§3, proved; one standard theorem recalled).** Any flux-changing history has
   to pay a cost in every one of the Lx·Ly cross-sections, at least μ_G·β each, with μ_G the cheapest way to write −1 as a product of
   group elements (Z₂: 2; Q8: 2; 2T: 1.5; 2O: 1.172; 2I: 0.955, computed exactly). Widening doubles that cost, so the widening ratio
   goes to zero like e^{−βμ_G Lx Ly}: far more relief than light. A pre-registered check found one wrong prediction of mine: the binary
   dihedral group Dic3 has no twist eater (−1 is not a commutator there), so the lemma is stated for "−1 is a commutator", not for
   "non-abelian".
4. **The mechanism (§4).** In a classically scale-invariant theory without running, z of a cube cannot change under doubling (Lean:
   `scale_invariant_frozen`). So **all growth of z is the scale anomaly**, and it enters exactly once: the flux sectors of a small
   twisted box are split by a half-instanton (charge ½, Bogomolny cost 8π²·½/g²), and the running coupling makes that fixed classical
   cost cheaper in a bigger box. Growth exponent of z: 16π²·b₀·|Q| = 11/3 for every SU(N), with the universal two-loop correction
   **γ_z = (11/3)(1 − 5g²/(44π²)) + O(g⁴)**, a doubling factor of about 12 at the weak end (table §4.4); at the large end the string
   gives a factor above 4. Widening relieves less than light's ½ because the flux in a small twisted box is not a spread-out field (it
   costs no classical energy at all: the twist eater) but a rate of localized events, which a wider box both hosts more of and makes
   cheaper.
5. **The weak-end sandwich (§5).** A correction first: a trial tunnelling path gives a **lower** bound on E (tunnelling is at least this
   likely), Bogomolny an **upper** bound (it is at most this likely). Proved: the classical floor (every flux-changing path costs at
   least 4π²/g², in the continuum) and an explicit lattice configuration attaining less than 4π²/g² on the symmetric doubly twisted
   torus. Proved with a stated gap: at a fixed lattice size, g² log(aE) → −(lattice tunnelling distance) as g → 0. Not proved, and
   precisely located: (B1) the continuum floor is attained on T³ × R (numerically known since 1994, rigorous status open), (B2) the
   fluctuation prefactor along the line of constant physics, which is where b₀ enters the rigorous problem and must be controlled to
   within a factor of about 12 (Lean: `power_sandwich_certifies`), and (B3) the time limit: a Euclidean computation in a finite box
   gives a twisted partition-function ratio, and turning it into E needs spectral information about the box (a window between the
   sphaleron time and 1/E, which closes where z reaches about 1). Interval arithmetic can close (B1); nothing known closes (B2), (B3).
6. **The inversion box (§6, heuristic).** On a symmetric 4D box the electric flux free energy and the dual twist free energy are
   exchanged by 't Hooft's duality; they are equal at exactly F = log(1 + √2) ≈ 0.881 (Lean: `self_dual_point`, unique). At that box z
   ≈ 0.88 up to excited-state corrections. The string end puts it at L√σ ≈ 1.39 (Luescher term) to 1.55 (Nambu–Goto), around the
   deconfinement length 1/T_c ≈ 1.41/√σ: in that box the time extent is L too, so the box is at temperature 1/L ≈ T_c.
7. **What W would deliver (§8).** Unbounded growth of z (flux energy falls slower than any Coulomb law), in a bounded number of doublings
   per target (Lean `act_reach`). Linear confinement of flux needs the stronger asymptotic form (w → 1). Both are flux-sector
   statements, **incomparable** with the vacuum gap; the sector transfer to glueballs stays separate and open.
8. **Unit tests (§7):** photon (equality, no margin), Z₂ and finite subgroups (exponential relief), deconfinement, triviality, and
   Banks–Zaks: b₀ > 0 is not enough; the conformal-window theories either have no centre flux to measure (fundamental quarks) or
   freeze z at their infrared fixed point, and their half-instantons carry fermion zero modes that switch the mechanism off.

---

## 1. Conjecture W, precisely

### 1.1 The lattice objects (Yang–Mills inside the hypotheses)

- **Theory.** SU(2) Wilson lattice gauge theory on Λ = Z_{Nx} × Z_{Ny} × Z_{Nz} × Z_{Nt}, spacing a, action
  S = β Σ_p (1 − ½ tr U_p), β = 4/g₀².
- **Magnetic twist m_z.** The xy-plaquettes at (x, y) = (Nx − 1, Ny − 1), for every (z, t), enter with −U_p (one fixed sheet).
- **Transfer matrix.** Time t is the transfer direction. The twist is spatial, so the time reflection keeps reflection positivity: the
  transfer matrix T on the gauge-invariant L² space of a time slice is self-adjoint, positive, with a strictly positive kernel
  (Osterwalder–Seiler; the twisted spatial plaquettes enter only as a positive multiplication operator). Known; r3-monotone B1.
- **Centre transformation.** Ω̂_z multiplies every z-link with z-coordinate z₀ by −1. It commutes with T (every spatial plaquette
  contains either no such link or two), Ω̂_z² = 1, and on gauge-invariant states it does not depend on z₀ (two choices differ by a
  gauge transformation). Its eigenvalues ±1 define the flux sectors e_z = 0, 1.
- **Flux energy.** λ₀ = top eigenvalue of T (simple, in e_z = 0, by Perron–Frobenius and Ω̂-invariance of the positive eigenvector);
  λ₁ = top eigenvalue in e_z = 1. **aE(Nx, Ny, Nz; β) := log(λ₀/λ₁) > 0** (strict, r3-monotone B2). Equivalently
  aE = −lim_{Nt→∞} (1/Nt) log(Z_{e=1}/Z_{e=0}): the time extent goes to infinity **first**.
- **Act number of the cube.** z := L·E(L, L, L) (dimensionless; ħ = c = 1). For anisotropic boxes the photon-normalised version
  ζ := E·Lx Ly/Lz is frozen for light (§2).
- **Continuum box energies (hypothesis H_cont, not proved).** Along a line of constant physics (β → ∞ with Ni·a(β) = Li fixed in units
  of a reference scale, e.g. √σ), the limit Ê(Lx, Ly, Lz) := lim a(β)⁻¹·aE(Li/a(β); β) exists, is finite and positive. This is part of
  the existence/identification problem that the round-3 review lists as open; it is stated, not assumed silently.

### 1.2 The statement

Write ℓ(L) = Ê(L, L, 2L)/Ê(L, L, L) (lengthen z), w_x(L) = Ê(2L, L, 2L)/Ê(L, L, 2L) (widen x), w_y(L) = Ê(2L, 2L, 2L)/Ê(2L, L, 2L)
(widen y). Exactly (Lean `four_move_identity`):

  z(2L)/z(L) = 2 · ℓ(L) · w_x(L) · w_y(L).

The factor 2 is the extent; doubling time changes no energy. Light: 2 · 2 · ½ · ½ = 1.

**Conjecture W(δ, I)** (SU(2), continuum form). For every L with L√σ ∈ I:
- (W1) ℓ(L) ≥ 2 (lengthening at least doubles the flux energy);
- (W2) w_x(L) ≥ ½(1 + δ) and (W3) w_y(L) ≥ ½(1 + δ) (widening relieves less than light's ½, with margin δ > 0).

Then z(2L) ≥ (1 + δ)² z(L) (Lean `conjW_doubling`). **W_Σ(δ, I)**, the summed form: z(2L) ≥ (1 + δ)² z(L) on I. W ⇒ W_Σ; the
mechanism of §4 speaks directly to W_Σ, and to the per-move split only heuristically.

Versions: **global** W(δ, (0, ∞)); **stretch** W(δ, [ℓ_U, ℓ_∞]) to be joined with the semiclassical weak end below ℓ_U (§5) and the
string above ℓ_∞. **Lattice form** W_lat: for each β ≥ β₀ there is n₀(β) with n₀(β)·a(β) → 0 such that (W1)–(W3) hold for aE at fixed β
with N → 2N, N ≥ n₀(β), the margin δ reduced by an artefact allowance η(a/L) → 0. The lower cut n₀(β) is necessary: at fixed N and
β → ∞ the ratios are decided by lattice artefacts (§5.3).

**Strength.** W on a finite stretch: weaker than the gap (finite boxes; a tuning statement, like round 3's NFP but in a scheme where
light and the finite groups fail visibly). Global W: incomparable with the gap (§8). Couplings: in the continuum form "the coupling" is
LΛ itself; the weak end is g²(1/L) → 0.

---

## 2. Theorem A: the photon is exactly marginal (proved, paper; numerical check C6)

**Model (the same objects as §1.1, with U(1)).** Link angles θ_l ∈ ℝ on Λ, identified under θ ~ θ + dΛ + 2πm for real Λ on sites and
integer 1-forms m with dm = 0 (closed: this includes the windings, so holonomies are compact). Action S = (1/2g²) Σ_p (dθ)_p² (Villain
form with the plaquette integers restricted to dm, i.e. monopole-free; the free photon with compact gauge group). Optional twist: the
xy-sheet plaquettes get dθ + π. Ω̂_z: θ_l → θ_l + π/Nz on all z-links (half a winding: eigenvalue (−1)^n on flux n).

**Statement.** For all Nx, Ny, Nz ≥ 1, all Nt, all g > 0, with or without the twist: the electric flux sectors n ∈ ℤ along z have
Z_n/Z_0 = exp(−Nt·aE_n) exactly with

  **aE_n = g² n² Nz / (2 Nx Ny),  i.e.  E_n = g² n² Lz/(2 Lx Ly).**

Hence ℓ = 2, w_x = w_y = ½ exactly, and z = L·E_1(L, L, L) = g²/2 = 2πα (α := g²/4π) at every L and every lattice spacing: no margin,
no lattice artefact. The continuum free Maxwell field on T³ gives the same formula (its flux zero mode is the same particle on a circle).

**Proof.**
1. *Hodge split on the spatial torus.* A 1-form θ splits orthogonally into exact (gauge), coexact (transverse) and harmonic parts; the
   harmonic 1-forms are the constants c_i on all i-links. A closed integer m has harmonic part w_i/N_i (w_i its winding) and no coexact
   part, so the identification acts on c_z as c_z ~ c_z + 2π/Nz and on the rest only by gauge shifts.
2. *Decoupling.* The magnetic term contains no harmonic part. In the time-like plaquettes the z-mode enters as Δc = c_z(t+1) − c_z(t)
   with the same coefficient in all M = Nx Ny Nz zt-plaquettes, and the remainders r_p sum to zero over those plaquettes (the
   non-constant part is orthogonal to constants; the gradient of the time links sums to zero around z-circles). So
   Σ_p(Δc + r_p)² = M Δc² + Σ_p r_p²: the zero mode is an independent particle on the circle ℝ/(2π/Nz)ℤ.
3. *Its transfer kernel* is the periodised Gaussian K(Δ) = Σ_w exp(−(M/2g²)(Δ + 2πw/Nz)²). Its eigenfunctions are e^{ikc}, k ∈ Nz ℤ
   (periodicity), and unfolding the sum gives eigenvalue √(2πg²/M)·exp(−g²k²/(2M)). With k = Nz n: aE_n = g² Nz² n²/(2M) =
   g² n² Nz/(2 Nx Ny). The flux through a z-cross-section is the charge conjugate to c_z divided by the cross-section, i.e. n.
4. *Twist.* The sheet term π·δ_sheet splits into an exact part (absorbed by a real shift of θ, which commutes with the identifications)
   and a harmonic part (π/(Nx Ny) on every xy-plaquette). The cross term with dθ vanishes (an exact 2-form sums to zero over each closed
   xy-torus). So the twist adds a constant to the action, the same in every flux sector, and E_n is unchanged.
5. *Lengthening/widening.* Read off from the formula (Lean `coulomb_moves`, `coulomb_frozen_box`).

**C6 (pre-registered):** direct quadrature of the kernel's eigenvalue ratios for five boxes and n = 1, 2 reproduces the formula to
machine precision; lengthening (4,4,8)/(4,4,4) = 2.000000000000001, widening (8,4,4)/(4,4,4) = 0.4999999999999988.

**Compact Wilson U(1)** (cos action, monopoles present) is not exactly solvable; in its Coulomb phase the expectation is z(L) → e_R²/2
at large L (Guth 1980; Froehlich and Spencer 1982 for the Villain model's massless photon; recalled; the flux-energy statement itself
is not proved to my knowledge). Theorem A is the exact abelian counterpart the brief asks for; the Wilson U(1) control of r4-actnumber
should see ℓ ≈ 2, w ≈ ½ up to the slow drift of e_R².

**Why the photon is marginal, in one line.** Light's flux spreads over the whole cross-section: energy density ∝ (flux/area)², volume
= area × length, so E ∝ Lz/(Lx Ly), and nothing runs (b₀ = 0). This is the scout's `single_act_frozen` made exact on the lattice.

---

## 3. Theorem B: Z₂ and the finite subgroups fail W at weak coupling (proved, paper; one standard theorem recalled)

### 3.1 The obstruction, per cross-section

Let G be a finite subgroup of SU(2) with −1 ∈ G (Z₂ = {±1}, the cyclic Z_{2k}, the binary dihedral groups, Q8, 2T, 2O, 2I), Wilson
cost c(g) = 1 − ½ tr g per plaquette (in units of β). Flux-changing histories live in the **doubly twisted** torus: the electric flux
e_z is the Fourier transform over the zt-twist ('t Hooft 1979; B1 of r3-monotone), so a history from the + vacuum to its Ω̂-image is a
configuration with twist −1 on a zt-sheet as well as the xy-sheet.

- **Slice identity (standard).** For a 2D slice (a lattice 2-torus) with base point, the product of its plaquette variables, each
  transported to the base point (so each replaced by a conjugate), in a suitable order, equals c·[h_a, h_b]: the twist factor times
  the commutator of the two cycle holonomies at the base point. Round 3 proved the abelian case in Lean (`prod_plaq2_comm`).
- **μ_G.** μ_G := min Σ_i c(g_i) over finite sequences with g₁⋯g_k = −1. Since c is conjugation invariant, every slice whose transported
  plaquette product is −1 costs at least μ_G·β.

**Lemma B1 (lower bound on the flux-changing cost).**
- (a) *If −1 is not a commutator in G* (abelian groups; also Dic3, see C3): a flat zt-slice would need [h_z, h_t] = −1, which is
  impossible, so every one of the Nx·Ny zt-slices contains non-trivial plaquettes. For abelian G their product is exactly c = −1, so
  each slice costs ≥ μ_G·β. (For non-abelian G without −1 as a commutator the transported product is −[h_z, h_t]⁻¹, a non-trivial
  element of the coset −[G, G]; each slice then costs at least the cheapest way μ′_G > 0 to write such an element. Only the abelian
  case is used quantitatively below.)
- (b) *If −1 is a commutator* (Q8, 2T, 2O, 2I): suppose some time slice t* carries no non-trivial spatial plaquette (true for every
  finite-action history on Z_{Nx}×Z_{Ny}×Z_{Nz}×ℤ, and on a finite torus whenever Nt exceeds the number of time slices that carry one).
  At any point (x, y, z, t*), the xy-, xz- and yz-slices through it are flat, so h_x, h_y anticommute and h_z commutes with both. In
  SU(2) the centraliser of an anticommuting pair is {±1} (they are, up to conjugation, two imaginary quaternion units; anything
  commuting with both commutes with all of the quaternions), so h_z = ±1 and [h_z, h_t] = 1. The zt-slice through the point then has
  transported product exactly −1 and costs ≥ μ_G·β. This holds for every (x, y).

So **every flux-changing history costs at least μ_G·β·Nx·Ny** beyond the e = 0 vacuum. This is the "a discrete group cannot interpolate
smoothly" of the scout, made a counting lemma: the per-point patterns (which of the six slice relations a point can keep) were computed
exhaustively (C3): for Q8, 2T, 2O, 2I the inclusion-minimal sets of relations that must fail are exactly {xy}, {zt}, {xt, yz}, {xz, yt};
at a vacuum time slice only {zt} is available. For the abelian groups and Dic3 only {xy, zt}.

**μ_G (exact, C5).** Z₂ 2; Z4 2; Z10 5(1 − cos π/5) = 0.954915; Q8 2; 2T 1.5; 2O 4(1 − cos π/4) = 1.171573; 2I 0.954915; Dic3 1.5.
The optimal products are powers of the element of smallest rotation angle (cost/angle is increasing in the angle, and the angles of a
product add at most). For U(1) itself μ = 0 (the twist can be spread: the photon's case), and for SU(2) μ = 0 as well: continuity is
exactly what removes the per-slice cost.

**Lemma B2 (matching construction).** Put z₀ = Nz − 1 and let the z-links at z₀ ramp in time through h_j = g₁⋯g_j (j = 0…k) along an
optimal sequence for μ_G, uniformly in (x, y), all t-links 1, the xy twist eaten by a and b on the boundary x- and y-links (non-abelian
G) or carried by one frustrated xy-plaquette per (z, t) as in the e = 0 vacuum (abelian G). Then the zt-plaquettes of the ramp cost
exactly μ_G per (x, y) and the zt twist sheet at (Nz − 1, Nt − 1) is cancelled by the final value −1. For abelian G nothing else changes:
**excess action = μ_G·Nx·Ny·β exactly** (Z₂: 2Nx Ny β). For non-abelian G the intermediate h_j do not commute with a or b, so in each of
the k_G − 1 intermediate time steps the xz-plaquettes at x = Nx − 1 (Ny of them) and the yz-plaquettes at y = Ny − 1 (Nx of them) are
frustrated, each costing at most 2: **excess ≤ [μ_G Nx Ny + 2(k_G − 1)(Nx + Ny)]·β** (k_G = 5 for 2I, 4 for 2O, 3 for 2T, 1 for Q8).

### 3.2 From actions to energies (proved with one recalled theorem)

At fixed (Nx, Ny, Nz) the transfer matrix of a finite gauge group is a finite symmetric positive matrix with entries e^{−β·(cost)}. The
ground-state transform turns it into a reversible Markov chain whose odd-sector relaxation rate is 1 − λ₁/λ₀ = 1 − e^{−aE}. For such
families with exponentially small rates the low-temperature large deviations of Freidlin–Wentzell type give
lim_{β→∞} (1/β) log(1 − λ₁/λ₀) = −S*(N), S*(N) the minimal excess action of a path from a vacuum to its Ω̂-image (upper bound on aE:
canonical paths in reverse, i.e. the test function 1_A − 1_{Ω̂A}; lower bound: canonical paths; Diaconis–Stroock 1991, Holley–Stroock,
Catoni 1992, recalled, not re-derived here). With Lemmas B1, B2: μ_G Nx Ny ≤ S*(N) ≤ μ_G Nx Ny + 2(k_G − 1)(Nx + Ny), with equality on the
left for abelian G.

**Theorem B.** For G as above, at fixed N and β → ∞:
- Z₂: aE = e^{−2βNxNy + o(β)}, so w_x = e^{−2βNxNy + o(β)} → 0.
- Abelian G: w_x = e^{−βμ_G Nx Ny + o(β)} → 0.
- Q8, 2T, 2O, 2I: w_x ≤ e^{−β[μ_G Nx Ny − 2(k_G − 1)(Nx + Ny)] + o(β)} → 0 once μ_G Nx Ny > 2(k_G − 1)(Nx + Ny) (for 2I and a square
  cross-section: N ≥ 17; for the full doubling z(2L)/z(L), using 4μ_G N² against μ_G N² + 16N: N ≥ 6). The constant 2(k_G − 1) comes
  from a crude construction; the true S* is likely closer to μ_G Nx Ny.
- In every case ℓ = e^{o(β)} (the cost does not depend on Nz) and **z(2L)/z(L) → 0**: the act number falls (Lean `relief_exponential`
  for the abstract step; `nonincreasing_never_reaches`, scout).

Uniformly in N at fixed β ≥ β₀(G) the same exponential relief follows from a Peierls/low-temperature cluster expansion of the finite
gauge group (for Z₂, equivalently Wegner duality to strong coupling); standard, recalled, not done here. This is the frozen
(deconfined) phase; below their transition finite groups confine like everything at strong coupling, and z grows there. The unit test
is a weak-coupling test.

**What separates SU(2) from them, exactly.** (i) −1 is a commutator in SU(2) (round 3's twist eater), so the flux costs no classical
energy per cross-section, unlike all abelian groups and Dic3; (ii) SU(2) is a continuum, μ_SU(2) = 0, so the per-slice cost of Lemma B1
disappears and the flux-changing event can be a single localized object of size-independent classical cost (a half-instanton) instead
of a sheet across the cross-section; finite groups with twist eaters still pay μ_G per slice.

---

## 4. The mechanism and the margin (SU(2))

### 4.1 Exact: growth of z is the scale anomaly

If the continuum limit exists with one scale Λ (H_cont and identification), dimensional analysis gives z(L) = Φ(LΛ) for a cube, and
Ê(λL) = λ⁻¹ Ê(L)·[Φ(λLΛ)/Φ(LΛ)]. With no running (a classically scale-invariant theory with vanishing β-function) Ê is homogeneous of
degree −1 and **z(2L) = z(L) exactly** (Lean `scale_invariant_frozen`): the product of the four move factors is light's product 1,
whatever the per-move split. So the whole margin of W_Σ is the anomaly: with B(z) := dz/d log L the β-function of the act-number
scheme, **W_Σ(δ, I) ⇔ ∫ over one doubling of B(z)/z ≥ 2 log(1 + δ) on I.** In words: W_Σ is "no fixed point, with a margin" in the
act-number scheme (round 3's NFP), but on the whole stretch and beyond, and in a scheme where light's B ≡ 0 is visibly the boundary case.

### 4.2 Where b₀ enters: the half-instanton

Conventions: β(g) = μ dg/dμ = −b₀g³ − b₁g⁵, b₀ = (11/3)·N/(16π²) per unit log scale, b₁ = (34/3)·N²/(16π²)² (pure SU(N)), so
8π²/g²(μ) = 16π²b₀ log(μ/Λ) + O(log log). For SU(2): b₀ = 22/(48π²), b₁ = 17/(96π⁴).

1. **The flux sectors of a small twisted box are classically degenerate.** The twisted vacua are the twist eaters with P_z = ±1
   (round 3, `su2_twist_eater`), isolated and non-degenerate modulo gauge (the twist removes all constant modes; van Baal 1984,
   recalled). Ω̂_z exchanges them. So e_z = 1 costs nothing classically, unlike the photon's Coulomb energy and the finite groups'
   sheet: this is the "self-charge" at the level of the centre.
2. **They are split by tunnelling through charge ½.** A history from P_z = +1 to −1 lies in the doubly twisted sector, whose topological
   charge is Q ∈ ½ + ℤ ('t Hooft 1981; van Baal 1982: Q = −n·ñ/N mod 1). Bogomolny: S ≥ 8π²|Q|/g² ≥ 4π²/g².
3. **The cost is classically independent of the box** (scale invariance), and the half-instanton's size is set by the box (it "cannot
   fall through the lattice", García Pérez et al. 1994, read). With one-loop running the cost is S_I = 4π²/g²(1/ρ) with ρ ∝ L.
4. **Dilute splitting** (heuristic, standard semiclassics): E = 2K e^{−S_I}, K ∝ S_I²·(moduli volume)·(det′)^{−1/2}, four translation
   zero modes (dimension 4NQ = 4). By dimensional analysis z = c(shape)·S_I²·e^{−S_I}·(1 + O(g²)).
5. **Growth exponent.** With S_I = 8π²|Q|/g²(1/L) and ρ ∝ L: dS_I/d log L = 8π²|Q|·d(1/g²)/d log L = −16π²|Q|(b₀ + b₁g² + …).
   For SU(2), Q = ½: dS_I/d log L = −(11/3)(1 + 17g²/(44π²)). With z ∝ S_I²e^{−S_I}, d log z/d log L = (1 − 2/S_I)(−dS_I/d log L), so

   **γ_z := d log z/d log L = (11/3)(1 − 2/S_I)(1 + 17g²/(44π²)) = (11/3)(1 − 5g²/(44π²)) + O(g⁴),**

   with g = g(1/L) in any scheme (the O(g²) coefficient is universal: it comes from b₁ and the four zero modes; scheme changes and the
   two-loop correction to the prefactor enter at O(g⁴)). For SU(N) with Q = 1/N the leading exponent is 16π²·(11N/(48π²))·(1/N) = 11/3,
   independent of N.
6. **Antiscreening in this number.** 11/3 = 4 − 1/3: the gluon's spin (paramagnetic) coupling antiscreens with weight 4 and the orbital
   (Landau diamagnetic) part screens with weight 1/3 (Nielsen 1981, Hughes 1980; recalled). The 4 is the self-charge of the guiding
   principle in its quantitative form; the photon has neither term.

### 4.3 Why widening relieves less than ½ (the per-move split; heuristic)

Write the splitting as a rate of localized events: E = (number of places per unit time) × (cost). Then:
- **Lengthening** (Lz ≥ Lx, Ly, dilute along z): the events are localized in z with size ∝ L_⊥, so doubling Lz doubles the number of
  places and changes nothing else: ℓ → 2, light's value. A flux tube of fixed width at large L: E = σLz − π/(3Lz), ℓ > 2.
- **Widening x** at Lx ≈ Ly: classically (no running) the event grows with the box; by dimensional analysis the rate per unit length
  of z is φ(Lx/Ly)/(Lx Ly), with φ symmetric (φ(r) = φ(1/r)) and φ ∝ r^{±2} at the extremes (extensivity in the long direction).
  If φ is minimal at r = 1 (natural, unproved), the classical widening factor is ½·φ(2)/φ(1) ≥ ½: **already at least light's**. The
  running then multiplies by e^{S_I(ρ) − S_I(ρ′)} = 2^{(11/3)κ_x}, κ_x = ∂ log ρ/∂ log Lx (κ_x + κ_y + κ_z = 1, so ≈ ½ when the event
  size is √(Lx Ly)): **w_x ≈ ½·[φ(2)/φ(1)]·2^{11/6} ≈ 1.8·[φ(2)/φ(1)] ≫ ½.**
- **Widening when Lx ≫ Ly:** the event size is set by Ly, so only the number of places changes: w_x → 2.
- **Large boxes:** the flux tube has a fixed width, so widening does nothing: w → 1, ℓ → 2, z(2L)/z(L) → 4 from above.

So in every regime that can be described, the widening factor is above ½ by a margin of at least a factor 2. The photon is ½ because its
flux is a spread field; the finite groups are far below ½ because their event is a sheet whose cost scales with the area. SU(2) is above
½ because its flux-changing event is localized, scale invariant and (through b₀) cheaper when it is bigger.

**Hostile-expert checks of this section.** (i) The per-move claims depend on the unknown classical shape function φ and on how the event
size depends on the box; only the product (§4.1, §4.2) is fixed by the anomaly. (ii) Dilute-gas formulas hold only while z ≪ 1 (§5.4).
(iii) The 2/S_I term is the four zero modes; a different number of moduli would change it (not the case here: 4NQ = 4).

### 4.4 The margin as a function of the coupling

Weak end (from C7; g² = g²(1/L)):

| g² | α_s | S_I = 4π²/g² | γ_z | doubling factor 2^{γ_z} | per widening move (if split evenly) |
|---|---|---|---|---|---|
| 0.5 | 0.040 | 79.0 | 3.646 | 12.5 | ≈ 3.5 × light's ½ |
| 1 | 0.080 | 39.5 | 3.624 | 12.3 | |
| 2 | 0.159 | 19.7 | 3.582 | 12.0 | |
| 3 | 0.239 | 13.2 | 3.540 | 11.6 | |
| 4 | 0.318 | 9.9 | 3.498 | 11.3 | |

The doubling factor of the full cube is (1 + δ)² in W_Σ's notation, so the weak-end margin is 1 + δ ≈ 3.4–3.5 (δ ≈ 2.4). Large end
(Luescher term, z = σL² − π/3, x = σL²): z(2L)/z(L) = (4x − π/3)/(x − π/3) > 4, i.e. 1 + δ > 2. The minimum of the margin over the
stretch is unknown; it is the number r4-actnumber can measure (§9). **The margin is a statement about the full β-function of the
act-number scheme**: b₀ fixes it only at the weak end, where it is large; on the stretch W asserts that B(z) stays away from zero, which
b₀ > 0 does not imply (Banks–Zaks, §7.2).

---

## 5. The weak end as a two-sided sandwich

### 5.1 Which bound is which (a correction to the brief and the scout)

E is a tunnelling rate. A **trial tunnelling path** shows that some history with action ≤ S_trial exists, so tunnelling is at least
about e^{−S_trial}: a **lower bound on E** (DMP: "real paths come through"). **Bogomolny** shows no history costs less than 4π²/g², so
tunnelling is at most about e^{−4π²/g²}: an **upper bound on E** ("fake low values are flushed out"). A variational *state* in the odd
sector gives an upper bound on E too, but only through the ground state's weight in the barrier region, which is again controlled by
the action floor (the Agmon estimate). The brief's assignment (trial → upper, Bogomolny → lower) is reversed for E; it is right for the
minimal action.

### 5.2 Classical level (proved)

- **Floor (continuum, proved paper).** On the twisted T³ (m_z), the Agmon distance between the two vacua, i.e. the infimum of the
  Euclidean action over histories on T³ × ℝ from P_z = +1 to P_z = −1 (the two are equal by the standard reparametrisation argument,
  √(2V)|γ̇| ≤ ½|γ̇|² + V), is **≥ 4π²/g²**: every such history has Q = ΔCS ∈ ½ + ℤ (Ω̂_z shifts the Chern–Simons functional by ½ mod 1
  for e ∥ m) and Bogomolny gives S ≥ 8π²|Q|/g².
- **Attainment on the symmetric torus (proved paper).** On T⁴ with twists n_xy = n_zt = 1 the abelian constant field ('t Hooft 1981,
  recalled) has F_xy = 2π/(Lx Ly), F_zt = 2π/(Lz Lt) along σ₃/2, Q = ½ and action (2π²/g²)(r + 1/r), r = Lx Ly/(Lz Lt): **exactly
  4π²/g² when Lz Lt = Lx Ly** (self-dual), e.g. the symmetric L⁴ box.
- **Its lattice version (proved paper, explicit).** On the lattice torus with both twist sheets, take U = exp(iθσ₃) with θ_y(x, y) = φx,
  θ_x = −φ Nx y on the x-links that wrap from x = Nx − 1 to 0, zero otherwise (φ = π/(Nx Ny)), and the same in (z, t) with
  φ′ = π/(Nz Nt). Every twisted xy-plaquette is exp(iφσ₃) (the wrap at (Nx − 1, Ny − 1) gives φ − π, and the sheet's −1 = exp(iπσ₃)
  restores φ), mixed plaquettes are 1. Wilson action
  S_cf = β·V·[(1 − cos(π/(Nx Ny))) + (1 − cos(π/(Nz Nt)))] < (π²β/2)(r + 1/r) (because 1 − cos u < u²/2), so on the symmetric N⁴
  lattice **the doubly twisted sector has a configuration with action < π²β = 4π²/g₀²**, for every N. (A rigorous lattice upper bound
  on the minimal twisted action; there is no sharp lattice Bogomolny floor, recalled.)
- **T³ × ℝ (open rigorously).** On T³ × ℝ the floor 4π²/g² is attained by a self-dual half-instanton found numerically by over-improved
  cooling (García Pérez, González-Arroyo, Snippe, van Baal, Nucl. Phys. B 413 (1994) 535, read: "minimal action is 4π²", the
  solutions "cannot fall through the lattice"; smooth non-trivial solutions exist by Sedlacek, not shown to be self-dual). A gluing
  trial (vacuum → abelian flux configuration → abelian tunnelling with action exactly 4π²/g² by the computation above → vacuum) gives
  ≤ (4π² + 2C₁)/g² with C₁ the vacuum-to-abelian distance: rigorous but not sharp.

### 5.3 Quantum, at a fixed lattice size (proved with a stated gap; and why it is the wrong limit)

For the Hamiltonian (Kogut–Susskind) lattice theory on a twisted N³ torus, g²a·H = (g⁴/2)(−Δ) + V(U) is a semiclassical Schroedinger
operator with h = g² on the compact manifold SU(2)^{3N³}, restricted to gauge-invariant functions; the two twisted vacua are isolated,
non-degenerate gauge orbits with free action of the gauge group modulo the centre (the stabiliser of an anticommuting pair is ±1), so
the quotient is smooth near the wells. **Statement:** lim_{g→0} g² log(aE) = −d_N, d_N the lattice Agmon distance (minimal lattice
tunnelling action). **Gap:** Simon's theorem (Ann. Math. 120 (1984) 89; Helffer–Sjoestrand 1984) is for ℝⁿ with point wells; the
extension to a compact manifold with orbit wells on the invariant subspace is standard in spirit (the Agmon estimates are local) but
not written out here.

**Why this does not test W.** At fixed N the half-instanton's lattice action is S_N = 4π²[1 − c(a/ρ)² + …] with c = 1/5 for the Wilson
action for ρ ≪ L (García Pérez et al. 1994, eq. 19, read) and ρ ∝ L = Na, so d_N increases with N towards 4π². Then
w_x = exp(−(d_{2Nx} − d_N)/g² + o(1/g²)) → 0 for the Wilson action and → ∞ for over-improved actions: **at fixed N and β → ∞ the
widening ratio is a lattice artefact** (heuristic for the sign of c at ρ ∼ L; the mechanism is certain). The one-loop running that
makes z grow is a factor (L/a)^{11/3} = e^{O(1)/g₀²} along the line of constant physics, invisible at fixed N. This is why W is stated
along the line of constant physics, and the finite-group failure (a fixed-β, all-N phenomenon of the frozen phase) is not this artefact.

### 5.4 The continuum weak end: the sandwich and its three blocking steps

Target (T1c of the scout, weaker than the gap): for L ≤ L_U,
  c₋·S_I²e^{−S_I}·(1 − ε) ≤ z(L) ≤ c₊·S_I²e^{−S_I}·(1 + ε), S_I = 4π²/g²(1/L),
with c₊/c₋ small enough to certify each doubling. **Certification criterion (Lean `power_sandwich_certifies`):** a sandwich
C₁L^p ≤ z ≤ C₂L^p certifies z(L) < z(2L) iff C₂/C₁ < 2^p; here 2^p ≈ 11–12.5. A classical trial cost (4π² + c)/g² instead of 4π²/g²
widens the sandwich by e^{c/g²}, so it certifies only where **c < γ_z·log 2·g²(L) ≈ 2.5·g²(L)** (c/4π² < 13% at g² = 2, < 6.5% at
g² = 1): a non-sharp trial path certifies nothing as L → 0. The sandwich must be sharp in the exponent.

**(B1) Classical attainment on T³ × ℝ.** Needed for the lower bound on E with the sharp exponent. Status: numerically established,
rigorous open. *Closable by certified computation:* evaluate, in interval arithmetic, the action of an explicit smooth trial field on
twisted T³ × ℝ (e.g. a cooled lattice half-instanton interpolated by trigonometric splines with rational coefficients, glued to the
vacua by explicit exponential tails), as round 2's attempt A and round 3's attempt 3 certified their numbers (mpmath, 50 digits). A
certified action ≤ 4π²(1 + ε) with ε = 10⁻³ (c ≈ 0.04) meets the criterion for all g² ≳ 0.016, i.e. the whole weak end.

**(B2) Fluctuations along the line of constant physics.** This is where b₀ enters the rigorous problem. At fixed N the floor gives
E ≤ C_N e^{−d_N/g₀²}, and along the trajectory e^{−4π²/g₀²} = e^{−4π²/g²(L)}·(a/L)^{11/3}. So the entropy factor C_N of configurations
near the half-instanton relative to the vacuum must grow **exactly like (L/a)^{11/3} = (L/a)^{16π²b₀|Q|}**, uniformly, with its constant
known to within the factor ≈ 12 above. Gaussian part: a determinant ratio around the half-instanton (computable in principle, not done
in the literature I know for T³ × ℝ, recalled); beyond Gaussian: control of a large-field region (the instanton is not a small
perturbation of the vacuum) with sharp constants: Balaban's finite-volume ultraviolet stability gives e^{−c/g²} large-field
suppression, not c = 4π². **Not closable by computation alone**; needs constructive renormalisation with sharp constants.

**(B3) The time limit, T → ∞ before L → 2L.** Exact identity (spectral decomposition of the twisted box's transfer matrix):
  W1/W0(τ) = Σ_even e^{−τE_j} − Σ_odd e^{−τE_j} over Σ_all e^{−τE_j},
where W1/W0 = Z(n_zt = 1)/Z(n_zt = 0) is the zt-twist ratio of a T⁴ of time length τ. A Euclidean semiclassical computation controls
W1/W0(τ) in a finite box. E then follows as E ≈ 2(W1/W0)/τ only in the window
  τ_sph ≪ τ ≪ 1/E,
where τ_sph ≈ S_I/V_sph (the time below which thermal activation over the sphaleron barrier, with its large excited-state splittings,
outweighs tunnelling) and the excited states of both sectors are Boltzmann-suppressed with their splittings (spectral information
about the box that a finite-τ computation does not give). The window exists exactly while z ≪ 1 and closes near z ≈ 1. A direct
Euclidean RG bound does not help: its errors in log Z are extensive (∝ τ/L), while the signal is ≈ τE ≈ e^{−S_I}τ/L, so the twisted and
untwisted errors would have to cancel to relative precision e^{−S_I}. What would get past it: an RG in which the twisted and untwisted
boxes are blocked by the same centre-equivariant map (the scout's exact transport, §2.4 there) so that their errors cancel away from
the event; or a Hamiltonian (spectral) treatment in the continuum. Neither exists.

**Verdict on the sandwich.** Classical part: floor proved, attainment proved on symmetric T⁴ (continuum and lattice), numerically known
and certifiable on T³ × ℝ. Quantum part: rigorous only at fixed lattice size (wrong limit for W). The continuum weak end of z, and
with it the first certified doublings, need (B2) and (B3), which are a constructive-field-theory problem in a small box, not a
computation.

---

## 6. The inversion box (the owner's existence boundary; heuristic, clearly marked)

On a box with time extent Lt (and the spatial twist m_z), define F_e := −log(Z_{e=1}/Z_{e=0}) (electric flux free energy) and
F_m := −log(W1/W0) (zt-twist free energy). Exactly F_e = dual(F_m), dual(F) = −log tanh(F/2), an order-reversing involution (round 3,
Lean). Its unique positive fixed point is **F* = log(1 + √2) = 0.8814** (Lean `self_dual_point`, `self_dual_unique`; C7).

- Small box: F_e → 0 (the flux is free, "exists by definition"), F_m → ∞ (the twist must tunnel). Large box: F_e ≈ σL² → ∞ (the flux
  "does not exist by definition"), F_m → 0 (the twist is free: vortices condense). The duality is the inversion; the **inversion box**
  is where F_e = F_m = F*.
- On the symmetric L⁴ box (Lt = L), F_e = z + log[(1 + R₀)/(1 + R₁)] with R the excited-state sums of the two sectors, so **z ≈ 0.88 at
  the inversion box**, up to excited-state corrections (heuristic: they are not small near the crossover).
- **Where.** Weak end: semiclassics holds only while z ≪ 1, so the inversion box lies above L_U. String end (x = σL²): Luescher term
  z = x − π/3 gives z = F* at L√σ = 1.39 and z = 1 at 1.43; Nambu–Goto z = x√(1 − 2π/(3x)) gives 1.55 and 1.58, but it is near its own
  tachyon at L√σ = √(2π/3) = 1.45. A floor: if E ≤ σL for every L (heuristic), z ≤ σL², so z = F* needs L√σ ≥ 0.94. **Heuristic
  bracket: L√σ ∈ [0.94, 1.6], best guess 1.4 ± 0.15**, next to 1/T_c ≈ 1.41/√σ (T_c/√σ ≈ 0.709 for SU(2), recalled).
- **Why it coincides with deconfinement (reading, with a physics core).** In the symmetric box the time extent is L as well: the box *is*
  at temperature 1/L. z = E·L ≈ 1 says the flux state's time to live equals the box (the scout's `boundary_iff_ttl`, 3s1t), and a box
  whose temporal extent equals the flux TTL is at the temperature where flux stops being suppressed: deconfinement. In the owner's
  words, the transition is where the flux goes from existing by definition to not existing by definition, and at the self-dual point
  it is both electric and magnetic to the same degree.
- **Joining the ends is not a proof.** The weak-end sandwich (if completed) would show z ≪ 1 below L_U; the string form is not proved
  at all. Monotonicity of z (W_Σ) would make the inversion box unique.

---

## 7. Unit tests

### 7.1 The standard ones

| test | what happens | verdict |
|---|---|---|
| photon (U(1), weak coupling) | ℓ = 2, w = ½, z = 2πα exactly (Theorem A); b₀ = 0 so γ_z = 0 | W fails (no margin): **pass** |
| Z₂, weak coupling | w = e^{−2βNxNy + o(β)}, z falls (Theorem B) | W fails: **pass**; no gap-type claim is made, so Z₂'s gap is not contradicted |
| finite subgroups (Q8, 2T, 2O, 2I; Dic3, cyclic), large β | per-slice cost μ_G, z falls (Theorem B) | W fails: **pass** |
| deconfinement (L < 1/T_c) | W claims growth, never a value; z ≪ 1 at small L is predicted, not excluded; the inversion box sits near 1/T_c | **pass** |
| triviality (φ⁴₄) | no centre flux, no act number; nothing here asserts existence (H_cont is a hypothesis) | **pass** |
| lattice artefacts | at fixed N, β → ∞ the SU(2) widening ratio is artefact-dominated (§5.3); W is stated on the line of constant physics | built into the statement |

**The four features, each used once:** twist eaters (Theorem B separates on "−1 is a commutator"; the flux costs no classical
energy); the continuum (μ_SU(2) = 0, a localized event of box-independent classical cost); Bogomolny with Q ∈ ½ + ℤ (the event's cost
is fixed and positive); b₀ > 0 and no infrared fixed point (the cost falls with the box). Any argument that drops one of them proves W
for a theory that fails it.

### 7.2 The Banks–Zaks test (from the coordinating session)

SU(N) with N_f massless fermions is asymptotically free (b₀ > 0) but, in the conformal window, flows to an infrared fixed point and has
no gap (Banks and Zaks 1982). For SU(2) with fundamental Dirac flavours: b₀ ∝ 22/3 − 2N_f/3 > 0 for N_f < 11, and
b₁ ∝ 136/3 − 49N_f/6 < 0 for N_f ≥ 6, giving a two-loop fixed point g*² = −b₀/b₁ (the lower edge of the window is uncertain).

- **Fundamental quarks:** they break the centre explicitly, Ω̂_z is no longer a symmetry, and the electric flux sector does not exist
  (the flux is screened by pair creation). W is **not claimed**; the act number is undefined. This is the cleanest statement of what
  pure SU(2) has that these theories lack: **no matter to screen the flux.**
- **Adjoint quarks** (centre preserved, flux sectors defined; SU(2) with two adjoint Dirac flavours is the standard near-conformal
  case, b₀ ∝ 22 − 8N_f > 0 for N_f ≤ 2): (i) the half-instanton carries 2·2N·|Q| = 4 zero modes per adjoint Dirac flavour (index 2NQ
  per Weyl fermion), so the single-event splitting of §4.2 vanishes and the mechanism's first step fails; (ii) at the infrared fixed
  point the theory is conformal, Ê(λL) = Ê(L)/λ exactly, z → z* frozen, and γ_z = B(z)/z → 0 (our general formula γ_z ∝ −β(g) has a
  zero there). W fails at large L, as it must.
- **What the margin formula claims and does not claim.** §4.2 claims γ_z ≈ 11/3 only at the weak end and only for the pure gauge
  theory. On the stretch, W asserts that the act-number β-function has no zero, which is a statement about the full β-function, not
  about b₀. Pure SU(2) differs from the conformal window in three checkable ways: exact centre symmetry with no screening matter; the
  two-loop coefficient has the **same** sign as b₀ (b₁ = 17/(96π⁴) > 0: two-loop antiscreening adds to the growth, the +17g²/(44π²) in
  γ_z), where the window needs b₁ < 0; no fermion zero modes on the half-instanton. None of these proves W: "pure SU(2) has no infrared
  fixed point" is itself unproved, and global W_Σ is its act-number form with a margin.
- **Reading (the owner: "tie to G0 is reach"; inward reach = asymptotic freedom, outward reach = confinement).** The weak end of z is
  inward reach: b₀ alone sets its growth. The stretch is outward reach: it needs the β-function to stay away from zero all the way out.
  Banks–Zaks theories have unlimited inward reach and an outward reach that stops at the fixed point. In this note's terms: b₀ fixes the
  margin where it is largest and says nothing where it is smallest.

---

## 8. What Conjecture W would deliver

- **Global W(δ, (0, ∞)) ⇒** z(2^j L₀) ≥ (1 + δ)^{2j} z(L₀): z → ∞, and z reaches any target z* in a number of doublings bounded by z₀,
  z*, δ alone (scout's `act_reach`, Lean), uniformly in the bare coupling. In energies: E(L) ≥ c·L^{2 log₂(1+δ) − 1}: the flux energy
  falls slower than any Coulomb law (the photon's 1/L), a **weak form of flux confinement** (screening excluded).
- **Linear confinement** (E ≥ σ′L, 't Hooft's criterion F_e ∝ L·Lt) needs the asymptotic doubling factor 4, i.e. w → 1 and ℓ → 2 on large
  boxes ("W∞"); W with a small δ does not give it.
- **Strength.** Both are statements about the centre-charged (flux) sector of the transfer matrix. The vacuum gap is about the neutral
  sector. **Incomparable:** a gap does not imply W (deconfined Z₂ has a gap and a falling z, Theorem B); W does not imply a gap in
  general (flux sectors and the neutral spectrum are different sectors of one transfer matrix and no inequality between them is known;
  centre-symmetric confining theories with massless Goldstone bosons are the standard expectation for adjoint QCD below its conformal
  window, recalled). For pure SU(2) the **sector transfer** (large flux-sector energy ⇒ gap for glueballs) remains a separate, open
  piece; nothing here touches it. W on a finite stretch alone is a tuning statement (weaker than the gap).

---

## 9. For r4-actnumber: what would test the margin

1. **Per-move ratios, same β, same code:** ℓ(L) = E(L,L,2L)/E(L,L,L), w_x = E(2L,L,2L)/E(L,L,2L), w_y = E(2L,2L,2L)/E(2L,L,2L) (lattice:
   L/a = 4, 6, 8 with 2L/a = 8, 12, 16). The margin of W is δ(L) = min(2w_x − 1, 2w_y − 1) with ℓ ≥ 2. Predictions (heuristic): small L,
   ℓ ≈ 2 and w well above ½ (≈ 1.8 × a shape factor ≥ 1); large L, ℓ → 2 from above and w → 1. W predicts δ > 0 at 2σ everywhere; the
   smallest δ and where it occurs is the number a proof must certify. Symmetry check: E(2L, L, 2L) = E(L, 2L, 2L).
2. **Doubling factor z(2L)/z(L):** about 2^{γ_z} with γ_z ≈ 3.5–3.6 for α_s(1/L) ≈ 0.15–0.3 at the small end (table §4.4; expect the
   effective exponent lower in practice through the 2/S_I prefactor and lattice artefacts), above 4 at the large end.
3. **Inversion box:** on symmetric L⁴ boxes measure F_e and F_m (same ensembles as the twist free energy); F_e = F_m = 0.881 predicted
   near L√σ ≈ 1.4 ± 0.15, with z ≈ 0.88 there up to excited-state corrections.
4. **Controls:** U(1) (Villain, monopole-free: ℓ = 2, w = ½ exactly; Wilson at β = 1.1: the same up to the drift of e_R²); 2I above its
   transition: E unmeasurably small already at L/a = 3 (log-asymptotics e^{−0.955βN²}); never compare at fixed L/a with increasing β
   (artefact-dominated, §5.3).

---

## 10. Lean (`../../../formal/Attempts/R4/ConjW.lean`, toys)

`four_move_identity`, `conjW_doubling`, `coulomb_moves`, `coulomb_frozen_box`, `scale_invariant_frozen`, `sandwich_certifies`,
`power_sandwich_certifies`, `relief_exponential`, `self_dual_point`, `self_dual_unique` (statements in the file header). They contain no
Yang–Mills; each states what an input must supply or what follows from one. `self_dual_point` and `self_dual_unique` reuse round 3's
`dual` and `dual_strictAntiOn` (`Attempts.R3.MonotoneCrossing`). Build: `build.sh` in this folder, in `~/formal-att-r4-3` only:
"Build completed successfully", no warnings in the file (two linter warnings of the first build were fixed: an unused hypothesis and a
redundant `ring`), `#print axioms` on all 10 theorems shows only propext, Classical.choice, Quot.sound; no `sorry`, no `axiom`, no
`native_decide`.

---

## 11. Verdicts

| statement | status |
|---|---|
| Conjecture W stated (continuum along LCP with H_cont; lattice form with artefact cut); W ⇒ W_Σ; four-move identity | statement; identity **proved (Lean)** |
| Free lattice photon: E_n = g²n²Lz/(2LxLy) exactly, every N, g, with or without twist; ℓ = 2, w = ½, z = 2πα frozen; continuum the same | **proved (paper)**; numerically exact (C6); arithmetic **Lean** |
| Classical scale invariance without running freezes z; all growth is the anomaly; W_Σ ⇔ act-number β-function bounded away from 0 | **proved (paper)** given H_cont and one scale; toy **Lean** |
| Finite G ∋ −1: every flux-changing history costs ≥ μ_G β Nx Ny (abelian/−1 not a commutator: per slice; −1 a commutator: via a vacuum time slice) | **proved (paper)**; patterns and μ_G **exact computation** (C3, C5) |
| Matching constructions: excess = μ_G Nx Ny β (abelian), ≤ μ_G Nx Ny + 2(k_G − 1)(Nx + Ny) (non-abelian) | **proved (paper)** |
| Theorem B: lim (1/β) log(aE) = −S*(N); widening ratio and z(2L)/z(L) → 0 at weak coupling | **proved with a stated gap** (finite-state low-temperature asymptotics recalled) |
| Uniform-in-N version at fixed large β (Peierls/cluster expansion) | standard, **recalled**, not done |
| Pre-registered prediction for Dic3 | **failed**; lemma restated for "−1 is a commutator" |
| Continuum floor: flux-changing histories on twisted T³×ℝ cost ≥ 4π²/g² | **proved (paper)** (Bogomolny, Q ∈ ½ + ℤ, recalled inputs) |
| Symmetric doubly twisted T⁴: action exactly 4π²/g² (constant field); lattice configuration with Wilson action < π²β for every N | **proved (paper)** |
| T³×ℝ: floor attained (self-dual half-instanton) | numerically known (read); rigorous **open** (B1), certifiable |
| Fixed lattice, g → 0: g² log(aE) → −d_N | **proved with a stated gap** (Simon / Helffer–Sjoestrand extension) |
| Fixed N, β → ∞ widening ratio decided by the sign of the lattice a² correction | **heuristic** (mechanism certain) |
| γ_z = (11/3)(1 − 5g²/(44π²)) + O(g⁴); 11/3 = 16π²b₀|Q| for every SU(N); doubling factor ≈ 11–12.5 | **heuristic** (standard dilute semiclassics) |
| Per-move split (ℓ → 2, w ≈ ½·φ(2)/φ(1)·2^{11/6}, w → 2 for Lx ≫ Ly, w → 1 at large L) | **heuristic** |
| Sandwich certification needs C₂/C₁ < 2^{γ_z}; a non-sharp trial path certifies only where c < 2.5 g² | **proved (Lean)** for the criterion; the numbers arithmetic |
| Blocking steps (B2) fluctuations along the LCP, (B3) the time window τ_sph ≪ τ ≪ 1/E | located precisely; **open** |
| Inversion box: F* = log(1+√2), unique | **proved (Lean)**; z ≈ 0.88 there, L√σ ≈ 1.4 ± 0.15: **heuristic** |
| Banks–Zaks: fundamental matter: object undefined; adjoint: zero modes kill the event, fixed point freezes z | **heuristic/known**; W not claimed there |
| Conjecture W itself, any δ > 0, any stretch | **conjecture** |

## 12. The single most promising next step

Close (B1) by certified computation and measure the minimum margin. Concretely: (a) cool a half-instanton on a twisted Ns³ × Nt lattice
with over-improved action, interpolate it to a smooth field on T³ × ℝ, and certify its continuum action ≤ 4π²(1 + 10⁻³) in interval
arithmetic (this makes the classical sandwich sharp for the whole weak end); (b) have r4-actnumber measure ℓ, w_x, w_y across
L√σ ≈ 0.5–3 (§9.1), which turns W's margin into a number and locates where it is smallest. The analytic bottleneck after that is (B2),
the sharp fluctuation prefactor along the line of constant physics in a small twisted box: a constructive-renormalisation problem in
one small volume, where b₀ enters the proof exactly as (L/a)^{16π²b₀|Q|}.
