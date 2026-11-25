# Cycle 6, workstream 1 (c6a-flip): the corner as a flip probability (2026-11-22)

Task: define the flip probability p(L) of the centre sector on the existing SU(2) objects, prove p ≤ ½ from reflection
positivity, state the floor and find what it implies (confinement, D-T, the gap), unit tests including 2I. Four coordinator
messages arrived during the work and are folded in: the owner's "why the floor holds" (super-additivity of the act, section 4),
c6b's data finding (a bare floor does not separate SU(2) from the photon or finite groups, section 3), the owner's "not lowering
through DMP" (section 5), c6c's correction (exact super-additivity of z₀ is false; the repaired form z₀(2L) ≥ 2z₀(L) − c is the
target, section 4) and the owner's reading of the loss c (section 4.3).

Claim levels: **Lean** (built, no `sorry`, no new axiom, no `native_decide`), **exact** (closed formula or brute force, script
here), **paper** (argued here), **known** (literature, recalled), **reading** (interpretation), **SPECULATIVE**.

---

## 0. In plain words

1. **p(L) is now an object of the real 4D SU(2) measure, and p ≤ ½ is a theorem.** On the lattice ℤ/Tℤ × (ℤ/Lℤ)³ (Route B's
   time chain; T = L is the symmetric L⁴ box) the 't Hooft twist in the plane (t, x¹) gives Z_tw; p = Z_tw/(Z_tw + Z). For every
   β ∈ ℝ, every L, every even T, every background spatial twist: Z_tw ≤ Z, so 0 ≤ p ≤ ½ (`su2_flipProb_le_half`). Even more:
   Z − Z_tw = ½·(a reflection-positivity norm), so the electric-flux partition function Z_{e=1} = (Z − Z_tw)/2 is a square
   (`cZ_sub_cZtw_eq`). The owner's "the assertion reflects, 50 % limit" is exactly this: one reflection, one Cauchy–Schwarz.
2. **It is not true as stated for every L.** It needs one even extent in a direction of the twist plane. With both extents odd
   and β < 0 it fails: 2D Z₂ and 2D SU(2) on odd tori give p > ½ (exact, `odd_extent.log`). For β ≥ 0 and odd extents it holds
   by positivity of the transfer matrix (paper). The Wilson line of constant physics has β > 0, so nothing is lost.
3. **p ≤ ½ is group-blind**: the same proof works for U(1), Z₂, Q8, 2T, 2O, 2I. It is a standing, not content.
4. **Exact dictionary** (Lean): 1 − 2p = (Z − Z_tw)/(Z + Z_tw) = Z_{e=1}/Z_{e=0} = e^{−F_e}; ½ − p = ½ tanh(F_tw/2);
   F_e = dual(F_tw). The binary channel's contraction per crossing |1 − 2p| is the electric-flux ratio. The owner's "1/e per
   tick" is F_e = 1, i.e. p = (1 − e^{−1})/2 ≈ 0.316; the self-dual point is p = 1 − 1/√2 ≈ 0.293.
5. **A floor p ≥ p_min > 0 is too weak** (c6b, and here): the photon (p constant, about 0.02–0.27), the finite groups at β = ∞
   (2I: p = 1/160 exactly, every L) satisfy it with no gap and no confinement. In 't Hooft's classification the floor is
   "not Higgs" (confined or Coulomb). The right charged-sector statement is **saturation** p → ½ (`FlipSat`, ⇔ F_tw → 0),
   with a rate for the area law. Floor and saturation are both equivalent to statements about F_tw, in Lean.
6. **Confinement ≠ gap, located exactly.** Saturation with rate ½ − p(L) ≤ ½e^{−σL²} plus Tomboulis–Yaffe gives the area law
   (paper, TY recalled). Neither floor nor saturation implies the gap or D-T: the twist ratio is a centre-odd quantity and the
   vacuum (0⁺⁺) sector is blind to it; counterexamples: the photon (floor), SU(2) × U(1) (saturation, gapless), the Heller
   endpoint (saturation, massless 0⁺⁺, numerical). Even in the binary-channel model the floor gives only a **power law** in the
   dyadic size (`not_exponential`), and the centre-even correlations are not carried by the binary channel at all: the gap is
   exactly what leaks through the boundary besides the binary datum.
7. **The gap statement is the vacuum act's growth with a bounded loss** (owner's super-additivity, repaired per c6c):
   z₀(2L) ≥ 2z₀(L) − c and one start box with z₀(L₀) > c give the gap m ≥ (z₀(L₀) − c)/L₀ for every dyadic box, on the
   SU(2) objects (`su2_gap_of_doubling_defect`, Lean). The loss may even grow, as long as Σ c(2ᵏL₀)/2ᵏ⁺¹ < z₀(L₀)
   (`doubling_variable_defect`). A bounded act (photon, Heller endpoint) cannot satisfy it (`bounded_violates_defect`): the
   photon passes the loss law with c = 2π but then has nothing left to start with (net zero). The owner's mechanism for a
   fixed c is stated as a named hypothesis `SectorLoss` (c = log 64, the number of centre-flux sectors of a three-box); only
   its ingredients (the sector count, Z_{e=1} ≥ 0) are provable from existing objects.
8. **Not lowering, in DMP terms (section 5).** Reflection positivity gives only the one-witness side: Z_tw ≤ Z; effective masses
   only fall (act estimates from one correlation are upper bounds on the gap); Z(2t) ≤ Z(t)². The two-witness side, a lower
   bound on the gap, needs the trace over all states (the box glued to its mirror): the **gluing deficit**
   δ(L) = Z(L⁴)²/Z(L³ × 2L) − 1 bounds the box gap from below, z₁(L) ≥ −log δ(L) (Lean, finite-spectrum level). Its smallness
   is DMP's reach bound and is the content; 2I fails it (degenerate flat sectors, δ → D − 1), the photon fails it
   (scale-invariant δ), SU(2) × U(1) fails it (it is centre-blind, unlike every flip statement).

---

## 1. p(L) and the reflection bound (Lean)

File: `formal/ProofPhase/Flip/Bound.lean` (namespace `ProofPhase.Flip`).

**Objects.** Chain lattice `CLink E S T` of `ProofPhase.RouteB.Chain`, chain weight `W = ∏_t V(a_t)K(a_t, b_t, a_{t+1})`.
* `sliceMap g a`: a linkwise map `g e : G → G` of one slice's spatial links. `flip0 g U`: apply it to slice 0 (a fixed slice of
  the reflection Θ through t = 0, T/2).
* `twWeight w g U = ∏_t V(a_t)·K(g·a_t if t = 0 else a_t, b_t, a_{t+1})`: one twisted time step; `cZtw w g = ∫ twWeight`.
* Wilson: `flipG L z c` multiplies the first-direction links of the plane x¹ = c by z; `stepK_flipA_left`: the twisted step is
  exactly the Wilson weight with the temporal plaquettes of the (t, x¹) plane at t = 0, x¹ = c (all x², x³) entering with −β,
  for central z with rep z = −1, z² = 1. That is the 't Hooft twist in the plane (0, 1).
* SU(2): `su2Z L β P T` (periodic, background spatial twist P), `su2Ztw L β P c T`, **`su2FlipProb = Z_tw/(Z_tw + Z)`**.

**Theorems.**

| theorem | statement | kind |
|---|---|---|
| `twWeight_factor` | `K > 0` ⇒ `twWeight U = A(σU)·A(ΘU)·B(U)` (σ = `flip0 g`) | lattice bookkeeping |
| `cZ_sub_cZtw_eq` | `T` even, `K > 0`, g measure preserving, involutive, `V∘sliceMap g = V`: `2(Z − Z_tw) = ∫ F·(F∘Θ)·B`, `F = A∘σ − A` | **substantive (RP)** |
| `cZtw_le_cZ` | same hypotheses ⇒ `Z_tw ≤ Z` (via `Positivity.config_rp`) | **substantive (RP)** |
| `wilson_Ztw_le_Z` | Wilson chain, any compact group with central involution z, any β, P, c, even T: `Z_tw ≤ Z` | substantive, group-blind |
| `su2_Ztw_le_Z`, `su2_flipProb_le_half` | SU(2): `Z_tw ≤ Z`, `0 ≤ p ≤ ½` | the p ≤ ½ theorem |

Proof idea: Z = ⟨A, A⟩ and Z_tw = ⟨A∘σ, A⟩ for the reflection form ⟨F, F'⟩ = ∫ F·(F'∘Θ)·B; σ acts on a fixed slice, commutes
with Θ and preserves B and Haar, so ⟨A∘σ, A∘σ⟩ = Z and ⟨A, A∘σ⟩ = ⟨A∘σ, A⟩; positivity of ⟨A∘σ − A, A∘σ − A⟩ gives
2Z − 2Z_tw ≥ 0. Note: only the reflection symmetry and the positivity of B are used; the twist need not commute with K.

**Exactly what is needed.** One even extent in a direction of the twist plane (Lean: the time direction of the chain, extent T).
* Odd extents in both twist directions, β < 0: **false** in general. Exact, `odd_extent.py`/`.log`: 2D Z₂ on 3×3 at β = −0.5:
  Z_tw/Z = 1.0019, p = 0.5005; on 3×1: p = 0.549; 2D SU(2) (β multiplying tr U), area 9, β = −1: p = 0.50027. With one even
  side (2×3, area 6) p ≤ ½ at both signs. Formula: 2D Z₂, Z_tw/Z = (c^A − s^A)/(c^A + s^A), c = 2cosh β, s = 2sinh β; for odd A
  and β < 0, s^A < 0.
* Odd extents, β ≥ 0: holds (paper): Wilson's transfer matrix is a positive operator (Luescher 1977, Osterwalder–Seiler 1978,
  known), so Z_tw = Σ_{e=0} λⁿ − Σ_{e=1} λⁿ ≤ Z for every n. Not formalised (the project's link-reflection RP is for even tori).
* Planes: on the symmetric box T = L the chain is the L⁴ torus; `ProofPhase.RouteB.twistZ_perm` makes all six planes give the
  same Z_tw on `(ℤ/Nℤ)⁴`. The bridge chain ↔ `twistZ` (a relabelling of links and plaquettes) is **not formalised**.
* Group-blind: true for every compact group with a central involution acting as −1 (U(1), Z₂, finite subgroups). p ≤ ½ cannot
  carry Yang–Mills content.

## 2. Identities (Lean, `Floor.lean` section 1)

`flipP Z Ztw = Ztw/(Ztw + Z)`, `twistF = −log(Ztw/Z)`, `elecF = −log((Z − Ztw)/(Z + Ztw))`.
* `flipP_eq`: p = 1/(1 + e^{F_tw}); `flipP_le_half_iff`: p ≤ ½ ⇔ Z_tw ≤ Z.
* `one_sub_two_flipP`, `one_sub_two_flipP_exp`: **1 − 2p = (Z − Z_tw)/(Z + Z_tw) = e^{−F_e}**. With the transfer-matrix sector
  identity Z_{e=0,1} = (Z ± Z_tw)/2 (standard, not formalised; r3-monotone B1) this is Z_{e=1}/Z_{e=0}.
* `half_sub_flipP_tanh`: **½ − p = ½ tanh(F_tw/2)** (c6c's `half_minus_p`). `elecF_eq_dual`: F_e = dual(F_tw).
* Readings: the binary channel's per-crossing contraction |1 − 2p| is the electric-flux ratio; "one nat per tick" (|1 − 2p| =
  1/e) is F_e = 1, p ≈ 0.316; the self-dual point F_e = F_tw = log(1 + √2) is p = 1 − 1/√2 ≈ 0.293. On the symmetric box with
  the one-state proxy F_e ≈ z_e (c6b) the flux act number fixes p.

## 3. The floor, saturation, and what they imply

### 3.1 Statements (Lean, `Floor.lean` section 2)

Along dyadic boxes (n ↦ p(2ⁿL₀), symmetric boxes, fixed β, or along a tuning at fixed physical size):
* `FlipFloor p :⇔ ∃ p_min > 0, ∀ n, p_min ≤ p n`. `flipFloor_iff`: ⇔ F_tw bounded above.
* `FlipSat p :⇔ p → ½`. `flipSat_iff`: ⇔ F_tw → 0 ('t Hooft's confinement criterion). `flipFloor_of_flipSat`: saturation
  implies the floor (all p n > 0, which holds in every finite box since the twisted weight is positive); the converse fails
  (constant p < ½).
* Rate form (paper): `½ − p(L) ≤ ½ e^{−σL²}`, equivalently F_tw(L) ≲ 2e^{−σL²}.

c6b's finding is decisive for the statement: **the bare floor is satisfied by the photon and by every finite subgroup at β = ∞**
(p exact and L-independent: Q8 0.115, 2T 0.016, 2O 0.020, 2I 0.0063; my own count for 2I: twisted-flat quadruples 30·4·4 = 480,
commuting quadruples 76320, p = 480/76800 = 1/160 = 0.00625, agrees). So `FlipFloor` is kept only as a named statement with its
negative verdict; the corner on the charged side is `FlipSat` (with rate), and on the vacuum side the act growth of section 4.

### 3.2 (a) Tomboulis–Yaffe: confinement from saturation, not from a floor (paper)

TY (as stated in Kanazawa's Theorem 1, read in ws2-routeB): ⟨W(C)⟩ ≤ 2{½(1 − Z_tw/Z)}^{A_C/(L_μL_ν)} (dyadic side conditions).
In flip form ½(1 − Z_tw/Z) = (1 − 2p)/(2(1 − p)) = (½ − p)/(1 − p) ≤ 2(½ − p).
* Floor: base ≤ (1 − 2p_min)/(2(1 − p_min)) < ½, a fixed number: W ≤ 2·b^{A/L²}, nothing for a fixed loop as L → ∞.
* Saturation with rate ½ − p(L) ≤ ½e^{−σL²}: base ≤ e^{−σL²}, so ⟨W(C)⟩ ≤ 2e^{−σA_C} uniformly in the box: **area law**
  (exponent count of ws2 2.4: the rate must be at least L²).
* Flux-side growth gives saturation (Lean, `flipSat_of_growth`): if 1 − 2p_n ≤ e^{−F_n} and F_n ≥ b + 2ⁿa, a > 0, then p → ½.
  With F_e ≈ z_e and c6b's z_e ≈ (L√σ)² − 0.88 this is the measured situation (proxy, not a measurement of Z_tw/Z).

### 3.3 (b) The key question: does a floor (or saturation) imply D-T or the gap? No, and here is exactly where the gap needs more

* **Structural (paper, ws2 2.2 reused):** p is a ratio of partition functions differing by a centre twist; its Fourier transform
  is the e = 1 sector. Centre-even (vacuum-sector) observables are invariant under every centre transformation; the 0⁺⁺ sector
  is invariant under every symmetry, so no twist sees it.
* **Counterexamples (paper, inputs known):** photon U(1) (−1 is central, so p is defined; floor holds with p ≈ constant, gapless);
  SU(2) × U(1) product Wilson measure (saturation from the SU(2) factor, photon from the U(1) factor: gapless); the
  fundamental–adjoint endpoint (saturation with a massless 0⁺⁺; numerical, mainly SU(3), Heller).
* **Binary-channel model (Lean, `Floor.lean` section 3; a model, not the measure):** the signal of a ±1 datum after n crossings is
  ∏(1 − 2p_k) = e^{−ΣF_e} (`chainSignal_eq`). A floor gives ≤ (1 − 2p_min)ⁿ (`chainSignal_le`); on dyadic boxes R = 2ⁿL₀ that
  is the power law R^{log₂(1 − 2p_min)} (`pow_eq_rpow_logb`) and never an exponential e^{−m2ⁿ} (`not_exponential`).
  Exponential decay in R needs Σ_{k<n} F_e(2ᵏL₀) ≳ m2ⁿL₀, i.e. F_e growing linearly (the flux act z_e ≥ mL). And the datum is
  centre-odd: under exact conditional independence of inside and outside given the binary datum plus centre symmetry,
  E[O_in | s] = E[O_in | −s] for centre-even O_in, so centre-even covariances across the boundary are zero, not (1 − 2p)ⁿ.
  **The flip governs the charged signal; the gap is the size of what crosses besides the binary datum** (the stripped information
  that is not radiated away). That is Lemma X / the stage-two step again, now with an exact location.
* **What the gap needs instead:** a vacuum-sector statement, section 4 (D-T with a loss), or its partition-function form,
  section 5 (gluing deficit). Independence: floor ⇏ D-T (photon); D-T ⇏ floor (Z₂ at weak coupling: gapped, z₀ linear,
  p → 0 because the twist costs a sheet of about L² plaquettes, F_tw ≈ 2βL²).

## 4. Act growth: the owner's super-additivity, repaired (Lean, `Floor.lean` section 4)

### 4.1 What is true and what is not

* Exact super-additivity z₀(L₁ + L₂) ≥ z₀(L₁) + z₀(L₂) is **false** for gapped models (c6c: Ising strips, Dirichlet scalar,
  SU(2) at small L, where the box gap diverges as L → 0). Not proved here. The abstract Fekete lemma for super-additive
  sequences is in Lean (`superadd_tendsto`, from Mathlib's `Subadditive`) for completeness only.
* The **repaired form** (target statement, owner: "exactly what we need"): z₀(2L) ≥ 2z₀(L) − c.

| theorem | statement | kind |
|---|---|---|
| `doubling_defect_floor` | z(n+1) ≥ 2z(n) − c ∀n ⇒ z(n) − c ≥ 2ⁿ(z(0) − c) | abstract |
| `su2_gap_of_doubling_defect` | SU(2) boxes 2ⁿL₀ (c5e's `z0`, `E0`): 0 ≤ c < z₀(L₀) and the law ⇒ ∀n, E₀(2ⁿL₀) ≥ m := (z₀(L₀) − c)/L₀ > 0 and every connected time limit of every centre-even slice observable decays at rate m | **the gap statement on the SU(2) objects** (substantive via c5e: E₀ is the box gap) |
| `doubling_variable_defect` | z(n+1) ≥ 2z(n) − c_n ⇒ z(n)/2ⁿ ≥ z(0) − Σ_{k<n} c_k/2^{k+1} | abstract, summable-loss variant |
| `bounded_violates_defect` | z bounded, c < z(0), law ⇒ False | unit test (photon, Heller endpoint, IR fixed point) |
| `SectorLoss`, `su2_gap_of_sectorLoss` | named hypothesis c = log 64; with z₀(L₀) > log 64 ⇒ E₀(2ⁿL₀) ≥ (z₀(L₀) − log 64)/L₀ | named, open |
| `flipSat_of_growth` | flux-side growth ⇒ p → ½ | abstract |

c5e's multiplicative form (`su2_box_gap_of_DS_DT`, loss η summable) is the other variant; the additive one is weaker in its
hypothesis when z₀ grows (a fixed c is a relative loss c/(2z₀) that is summable along a growing act).

### 4.2 Photon and 2I against the target

* **Photon:** z₀ = 2L arsinh(sin(π/L)) ↑ 2π (c5e, exact). It satisfies the law with c = 2π (2z − 2π ≤ z when z ≤ 2π and z
  increases), but then the start z₀(L₀) > c fails: the loss eats the whole act, net zero. With any c < sup z₀ the law fails
  (`bounded_violates_defect`). Correct.
* **2I at weak coupling, fixed β:** in lattice units the theory has a local gap, but the box gap E₀ of c5e (all centre-even slice
  observables, winding ones included) sees the near-degenerate flat-connection sectors with non-central holonomies (the A₅
  layer holds state); their splitting needs a vortex sheet across a cross-section, so E₀(L) ~ e^{−cβL²} and z₀(L) → 0 (paper,
  expected, not measured). The start z₀(L₀) > c fails. Correct, and it uses exactly what 2I lacks: a unique vacuum in each box
  (no non-central flat sectors), i.e. a stateless adjoint layer (c5e 5.2).
* **SU(2):** z₀ ≈ 10 at L√σ = 2.8 (blueprint v4, measured), above log 64 ≈ 4.16; the law itself is unmeasured (c5e's
  PREREG-JOINT measures it).

### 4.3 The owner's loss reading and a fixed c

Owner: the loss c is the inefficiency of asserting existence over the doubled possibility space; inside confinement the assertion
is most efficient. Candidate mechanism, as a named hypothesis (`SectorLoss`): per doubling, only a fixed finite set of binary
centre-flux sectors is newly chosen; a periodic three-box has e ∈ Z₂³ and m ∈ Z₂³, 64 sectors at every L, so c ≤ log 64.
What the existing sector objects prove: the count (combinatorial; every twist set is indexed by a plane), Z_{e=1} ≥ 0 and
Z_tw ≤ Z for every sector (section 1), sector symmetry of the weight (`cweight_flipCfg`). What they do not prove: the
inequality itself, which compares two boxes (the two-sided step). It must use something 2I lacks: for 2I the newly chosen
sectors per doubling are not only the binary centre sectors but the non-central flat holonomy classes (their number is also
L-independent, so "a bounded number of sectors" alone does not separate; "only centre sectors are degenerate" does).
`doubling_variable_defect` shows a fixed c is more than needed: a loss growing like o(L) with Σ c(2ᵏL₀)/2ᵏ⁺¹ < z₀(L₀) suffices.

## 5. Chessboard, "not lowering", and the DMP dictionary

### 5.1 What reflection positivity gives, and which side

| RP consequence | statement | side |
|---|---|---|
| reflection bound (Lean, section 1) | Z_tw ≤ Z, Z_{e=1} = ½‖F‖²_RP ≥ 0 | upper bound on twisted weights |
| Hankel log-convexity (Lean, `RPSeq.effMass_antitone`, Route B) | effective masses of any one correlation decrease in t | **upper** bounds on E₀ (the gap ≤ every effective mass) |
| sub-multiplicativity (paper; positive transfer matrix) | Z(t₁ + t₂) ≤ Z(t₁)Z(t₂) in any direction with a positive transfer matrix; −log Z super-additive | gives the vacuum energy density (Fekete), not the gap |
| excess (Lean, finite spectrum: `excess_submul`) | R(a + b) ≤ R(a)R(b), R(t) = Σ_{n≥1}(λ_n/λ₀)^t | −log R super-additive in time: the "not lowering" that is true, per box |
| chessboard (known) | big-box expectations ≤ big-box fully reflected expectations | same box only; turning them into small-box data needs Z_{2L} ≥ e^{−O(1)}·(L-data), the reverse of sub-multiplicativity |

So: **RP gives sub-additivity on the vacuum side (upper bounds on the act); the super-additive direction it gives is in the
time extent of one box (−log Z and −log R), not across box sizes.** That matches c6c.

### 5.2 One witness against two (Lean, `Floor.lean` section 5, finite-spectrum level)

* One witness = one observable's reflection-positive correlation: its act estimates −log(h(t)/h(0)) are sub-additive (paper:
  log-convexity of a positive spectral measure) and the effective masses only fall (Lean, Route B). It can only tighten an upper bound on the gap ("one witness never loosens", T24, read on the gap).
* Two witnesses = the two halves A and ΘA glued, i.e. the trace over all states. For x_i = λ_i/λ₀ ∈ [0, 1] and Z(t) = 1 + R(t)
  (vacuum energy divided out): `excess_le_deficit` proves Z(2t) ≤ Z(t)² (positivity, the one-witness side) and
  **R(t) ≤ δ(t) := Z(t)²/Z(2t) − 1**; `gap_of_deficit`: e^{−Δt} ≤ δ(t) for every excited state x_j = e^{−Δ}. The vacuum energy
  cancels in δ, so δ is a ratio of partition functions only. On the symmetric box (t = L): **z₁(L) = L·E₁(L) ≥ −log δ(L)**,
  δ(L) = Z(L⁴)²/Z(L³ × 2L) − 1, E₁ the lowest excitation in all sectors (≤ E₀ of c5e).
* Dictionary (reading, precise where stated): DMP's two witnesses = A and ΘA; "loosening needs both" = a lower bound on the gap
  needs the glued trace; Axiom 1's reach bound = δ(L) ≤ e^{−mL} (the information crossing the mirror plane is exponentially
  small); `mg_reach_existence_floor` = `gap_of_deficit`. As in DMP (`mg_no_reach_no_floor`), without the reach bound there is no
  floor, and the reach bound is the gap in partition-function form: the premise is the content, not a consequence of RP.
* Tests of the premise δ(L) → 0 fast: photon δ → constant (scale invariance), fails; 2I δ → D − 1 ≥ 1 (D near-degenerate flat
  sectors), fails; SU(2) × U(1) fails (δ is centre-blind, unlike every flip statement: this is the one dictionary entry that
  passes the product test); Heller endpoint fails; Z₂ weak: δ → 7 (eight degenerate holonomy sectors in the full Hilbert space),
  fails (a missed gapped theory, not a wrong claim); SU(2) confined: expected δ(L) ≈ 2R(L) → 0 with the lowest glueball and the
  flux pairs (paper).
* Not formalised: the spectral representation Z(t) = Σλ_i^t of the SU(2) chain (transfer operator, Gauss law; Perron–Frobenius).
  The Lean lemmas are the finite-spectrum statements it would feed.

### 5.3 Flip floor versus super-additivity (task 3 of the coordinator)

Neither implies the other. Floor without D-T: photon, finite groups. D-T without floor: Z₂ at weak coupling. Saturation without
D-T: SU(2) × U(1), Heller endpoint. The flux act's super-additivity (σL², c6b) implies saturation (`flipSat_of_growth`, given the
order-of-limits link F_e ≥ z_e − c₀ of ws2 B3, open); the vacuum act's repaired super-additivity implies the gap; the two act
numbers are independent (Conjecture S's break, blueprint v4 6.3 item 4).

## 6. Unit tests

| test | p ≤ ½ | floor | saturation | vacuum law + start (section 4) | deficit δ → 0 (section 5) | truth |
|---|---|---|---|---|---|---|
| photon U(1) | holds (−1 central; group-blind) | **holds** (p ≈ const) | fails | fails (bounded z₀; c = 2π eats all) | fails | gapless, Coulomb |
| Z₂ strong | holds | holds | holds | holds | holds | confined, gapped |
| Z₂ weak | holds | fails (F_tw ≈ 2βL²) | fails | holds (z₀ linear) | fails (8 sectors) | deconfined, gapped: floor not necessary for the gap |
| deconfinement (L³ × T, T < 1/T_c fixed, L → ∞) | holds | fails for the (t, x¹) twist (F_e → 0 ⇒ p → 0), the Lean object itself | fails | — (temporal box) | — | correct |
| 2I weak, fixed β | holds | **holds** (1/160 exactly at β = ∞) | fails | fails (z₀ → 0: non-central flat sectors) | fails (δ → D − 1) | topological, deconfined; no continuum |
| mixture / Heller endpoint | holds | holds | holds | fails (bounded z₀) | fails | confined, massless 0⁺⁺ |
| SU(2) × U(1) | holds | holds | holds | fails | fails | gapless |
| SU(2) | Lean | data: p ≥ 0.485 on L√σ ∈ [2.1, 4.2] (c6b, proxy) | data: rising to ½ | z₀ ≈ 10 > log 64 at 2.8; law unmeasured | unmeasured | the claim |

Every flip statement passes or fails the tests exactly as confinement does; only the vacuum-side statements (sections 4, 5) fail
on the product and the mixture, i.e. separate confinement from the gap.

## 7. Next step

1. Measure what the corner now is, on existing configurations or with c5e's `PREREG-JOINT.md`: z₀(2L) − 2z₀(L) along
   β = 2.3–2.5 (the loss c, including small L where it must be large) and, as a cheaper partition-function proxy, the gluing
   deficit δ(L) = Z(L⁴)²/Z(L³ × 2L) − 1 by a free-energy ratio (snake/ratio method, as for twist free energies). A direct
   Z_tw/Z run for SU(2) in the transition region L√σ < 2 is the one flip measurement still missing (c6b).
2. Lean, small: the chain ↔ `twistZ` bridge (so the six planes of the symmetric box are covered by one theorem); the
   transfer-operator spectral representation is the larger missing piece for section 5.
3. Paper: whether the sector-loss mechanism can be argued in the strong-coupling regime of the blocked theory (Z₂ endpoint with a
   stateless adjoint layer), where both halves of a doubled box are in a convergent expansion; that would give c at one scale,
   the start of a crossing argument, not the infinite law.

## 8. Not checked

TY, Kanazawa, Luescher's transfer-matrix positivity, Heller, Fekete-type facts and 't Hooft's classification are recalled (TY via
ws2's reading of Kanazawa). The 2I degeneracy and z₀ → 0 at weak coupling are paper-level. The odd-extent counterexample is 2D
only (4D with odd L and β < 0 not determined). No GPU, no simulation; the only computation is `odd_extent.py` (seconds).

## Files

`NOTE.md` (this), `odd_extent.py` + `odd_extent.log` + `run_odd.sh`, `build.sh`, `check.sh`, `axioms.sh` + `axioms.log`,
`lookup.sh` (Mathlib name lookup). Lean: `../../../formal/ProofPhase/Flip/Bound.lean`, `../../../formal/ProofPhase/Flip/Floor.lean`.
Build: `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c6a-flip/build.sh`
("Build completed successfully"); `axioms.sh`: all 77 declarations depend only on `propext`, `Classical.choice`, `Quot.sound`
(some on fewer); no `sorry`, `native_decide` or `axiom`.
