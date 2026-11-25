# Round 4 preparation: DMP-derived routes into the open piece (scout, 2026-11-21)

Groundwork for a focused round 4. The brief: find, map and rank the DMP-derived routes into the crossover; prove nothing about the
crossover itself. Two messages from the coordinating session changed the focus while the scout ran: (1) the owner's priority, "the act
identity, maybe combined with our universal quantum and the tick rate, seems like the most promising approach. Existence asserting
itself, which an act is, seems to be the core principle on which everything stands"; (2) the adversarial review of round 3
(`../attempts/r3-review/REVIEW.md`): "no fixed point" is only a tuning step, crossover-D′ is strictly stronger than the gap, add the
**deconfinement test** (a torus one block thick is deconfined below 1/T_c ≈ 1.4/√σ), prefer targets no stronger than the gap. Both are
built in below: the act-identity family is candidate 1 and is treated in depth, and every candidate says whether its target is weaker
than, equal to, or stronger than the mass gap.

Claim levels: **proved (Lean)**, **proved (paper)**, **known** (literature, from memory unless marked "read"; to be re-checked before
an attempt relies on it), **heuristic**, **conjecture**, **speculation**, **reading** (an interpretation in the owner's terms, not a
mathematical claim).

Lean: `../../formal/Attempts/R4prep/ActIdentity.lean`, 11 theorems, built in WSL `~/formal-r4prep` with `build.sh` in this folder:
"Build completed successfully", no warnings in the file, `#print axioms` shows only propext, Classical.choice, Quot.sound; no `sorry`,
no `axiom`, no `native_decide`. No numerics were run.

---

## 0. The result in plain words

1. **The act identity has an exact Yang–Mills reading, and it is a running coupling.** Put the theory in a periodic box of side L. The
   cheapest state that carries one unit of centre ("electric") flux around the box has an energy E(L): that is the act's existence,
   and L, the length the flux must span, is its extent. Their product **z(L) = E(L)·L** (in units of ħc) is a pure number, the box's
   **act number**. The DMP act identity says z is one quantum. For light this is exactly true with the quantum replaced by
   **2πα**: z = e²/2 = 2πα ≈ 0.046 at every box size (known, classical electrostatics of a quantised flux on a torus). That is the
   owner's α pointer made exact: the fine-structure constant is the act number of light, and it never changes with the box.
2. **For SU(2) the act number runs, and every feature the unit tests demand enters it.** In a small box with a 't Hooft twist, the
   flux state is reached only by tunnelling through a **half instanton** (a "fractional instanton"), whose cost is a counted quantum
   that does not refine away (Bogomolny's bound, the counted floor of DMP's `mg_mass_gap_survives_refinement`). With the running
   coupling this gives **z(L) ∝ (LΛ)^{11/3}**: the exponent is the gluon's antiscreening number 11/3, the same "4 − 1/3" that round 3
   found as the sign of asymptotic freedom (heuristic, standard semiclassics). At large L the flux is a string, E ≈ σL, so
   z ≈ σL² (known as expectation; the act identity per segment with a reach bound gives exactly this form, proved in Lean as a toy).
   **z = 1, "the act fits its own box", is where space reach and time to live certify the same existence (3s1t)**, and it falls near
   L√σ ≈ 1.5, next to the deconfinement length 1/T_c ≈ 1.4/√σ (heuristic). So the DMP existence boundary and the review's
   deconfinement test land in the same place.
3. **What it does and does not deliver.** The act number gives the round a **DMP-native coupling with the tuning built in** (L₁ :=
   where z reaches a chosen value; this pins Yang–Mills down inside the hypotheses, the review's finding 3), a crossover statement that
   is **weaker than the mass gap** ("z crosses 1 and keeps growing", a finite-box statement), and a confinement-type statement in the
   flux sector. It does **not** give the vacuum-sector gap: a large flux-sector energy does not by itself imply a gap for glueballs.
   That link is open, and no DMP law supplies it.
4. **The two-sided step, located again.** Per layer, the act number is transported **exactly** by a gauge-covariant blocking that
   respects the centre: z(2L; fine action) = z(L; blocked action) (an identity, two-sided). Where it stays one-sided: comparing the
   blocked action with the original on the same box (the direction of the flow). Splitting one doubling into four one-direction moves
   (3s1t lets each direction play "time") shows exactly where b₀ must act: for light, lengthening the flux doubles E and widening each
   transverse side halves it, so z is frozen by an exact cancellation; growth of z needs the **widening relief** to be weaker than
   light's. That is a precise, testable conjecture (Conjecture W, §2.6).
5. **Cheapest decisive test:** a pre-registered GPU measurement of z(L) in a twisted box across L√σ ≈ 0.5–3.5, with U(1), deconfined
   finite-group and symmetry controls. It needs only a fixed sign flip on one plaquette sheet (a subset of attempt 2's kernel, no
   20-node coupling integration), so it is roughly an order of magnitude cheaper than the twist free-energy grid.

---

## 1. Inventory: DMP laws that are two-sided, cross-layer, about the root or existence boundaries, or carry a coupling

Files are `evidence/Dmp/*.lean` (DMP's formal theory, read only). "Proved" means a theorem in that file; DMP's own hypotheses are noted
where the law is an input, not a theorem.

| # | DMP law (file:line) | exact statement | in `evidence/` | kind |
|---|---|---|---|---|
| L1 | act identity, hypothesis of `mg_reach_existence_floor` (Reach.lean:35) | `x · e = Q · k · k` (existence × extent = one quantum, grid resolution k) | **input** (the owner's rule), not a theorem | per-layer exact identity |
| L2 | `mg_reach_existence_floor` (Reach.lean:35) | `x·e = Q k²`, `e ≤ R k` ⇒ `Q k ≤ x R` | proved | floor from reach |
| L3 | `mg_reach_floor_every_layer` (Reach.lean:43) | the same floor at every layer n if Q and R are the same at every layer | proved (its hypothesis is the open piece) | cross-layer, assumes uniformity |
| L4 | `mg_no_reach_no_floor` (Reach.lean:58) | without a reach bound every floor is undercut | proved | the payload case |
| L5 | `mg_ttl_existence_floor` (Reach.lean:73) | `x·τ = Q k²`, `τ ≤ Tmax k` ⇒ `Q k ≤ x Tmax` (tick rate: a bounded TTL is a gap) | proved | time side |
| L6 | `mg_space_time_certificate` (Reach.lean:80) | one existence certified in space and in time with one quantum ⇒ `e = τ` (3s1t) | proved | **two-sided identity**, space ↔ time |
| L7 | `Recipe.extend_preserves_decisions` (Theory.lean:268), `extend_chain` (262) | a new line changes no existing chain or decision (frame rule) | proved | exact cross-layer identity |
| L8 | `loop_hol_rekey`, `wilsonPot_rekey` (Gauge.lean:88, 99), `nonabelian_class_invariant` (218), `balanced_not_trivial` (172) | re-keying (gauge) preserves loop values, potentials and the class; a balanced net can carry non-trivial holonomy | proved | conserved under re-keying |
| L9 | `mg_mass_gap_survives_refinement` (MassGap.lean:141) vs `mg_refinement_closes_potential_gap` (133) | a counted quantum keeps its floor under refinement; a potential's gap closes | proved | cross-resolution, counted |
| L10 | `st_upper`, `st_lower`, `st_self_stabilizing` (R2Stable.lean:78, 103, 136) | real paths come through (upper), fake low values are backed by real paths (lower) ⇒ exact value | proved | **two-sided sandwich** |
| L11 | `st_no_root_takeover` (R2Stable.lean:145), `root_minted` (Theory.lean:188), `pressed_root_collapses` (224) | only the root holds 0; the root is minted; a pressed root collapses the chain | proved | root / existence boundary |
| L12 | `k4_stack_never_raises` (Theory.lean:393), `stackPhi_zero_iff` (406) | the stack potential (sum over layers) never rises under the system's own acts | proved | cross-layer monotone sum |
| L13 | `mg_returns_to_balance`, `mg_marginal_never_returns` (MassGap.lean:218, 226) | age < verify ⇒ back to balance; age = verify ⇒ stuck | proved | margin vs marginal |
| L14 | T24: `one_witness_never_loosens`, `loosening_needs_both` (Standing.lean:15, 25); `lowering_needs_both` (Field.lean:76) | tightening needs one witness, loosening needs both | proved | **asymmetric two-sided** |
| L15 | `pass_has_two_independent_witnesses` (Theory.lean:196), `gate_pass_iff` (Gate.lean:29) | every pass has two independent witnesses on its chain (T38) | proved | Duality per layer |
| L16 | `sublayer_only_tightens` (Theory.lean:162), `wv_dilation_only_tightens` (R1Wave.lean:118) | sub-layers only tighten; the dilated clock only tightens | proved | one-sided (round 3: data processing) |
| L17 | `wv_layer_succ` (R1Wave.lean:71), `wv_no_dilation` (84) | layer k ticks once per 10 ticks of layer k−1; ratio 1 = no dilation | proved | cross-layer tick rate |
| L18 | VIBE coefficient α (Balance paper, `docs/balance`, read via `../../README.md` §3.1a): "keeping an act in existence costs h·(1/c)·α per h" | — | **not in `evidence/`** (prose) | coupling |

What `evidence/` does **not** contain: a conservation law across layers in the physical sense (a quantity equal at every layer by a
theorem); the uniform reach (L3's hypothesis); any statement about the coupling α (L18 is prose). DMP's "same at every layer" laws are
all of the form "if the inputs are the same at every layer, so are the outputs".

### 1.1 Yang–Mills counterparts (under the hosting of `../attempts/r3-dmp/NOTE.md` §1.2)

| # | Yang–Mills counterpart | exact invariant on the YM side? | delivers for crossover | unit tests | target vs gap |
|---|---|---|---|---|---|
| L1, L6, L5 | **act number z(L) = E_e(L)·L** in a twisted box; TTL = 1/E_e by the transfer matrix (RP); 3s1t = Euclidean symmetry (hypercubic exactly, relabelling directions of the torus) | z(2L; S) = z(L; S_eff) under centre-equivariant blocking (**proved (paper)**, §2.4) | a DMP-native coupling and tuning; growth = crossover, large-L form = flux-sector confinement | passes all five (§2.5) | crossing: **weaker**; flux confinement: **incomparable** |
| L9 | Bogomolny: action ≥ 8π²\|Q\|/g², Q counted (Q ∈ ℤ + ½ in the doubly twisted torus) | Q is topological, exactly conserved by smooth flows and blockings that preserve it | the weak end of z(L): tunnelling cost 4π²/g²(L) | U(1), Z₂, finite: no instantons (π₃ = 0 or no continuum) | **weaker** (a floor at one scale) |
| L10 | semiclassical sandwich: trial fractional instanton (upper) + Bogomolny (lower) | — | two-sided bounds for z at small L (the "U" end of a grid) | as L9 | **weaker** |
| L12, L13 | gradient flow: dS/dt = −‖D_νG_νμ‖² per configuration (Luescher 2010, known); free field marginal | exact per configuration | NFP as a **one-measure** local inequality R(t) < 2 (§3.1) | photon R ≡ 2 exactly; Z₂/finite: no flow | **weaker** (tuning only) |
| L15 + exact identities | RP of each layer (T38) + Schwinger–Dyson loop equations = the bootstrap | loop equations exact at every β | two-sided certified bounds at finite spacing | method, not claim; Lie-type loop equations need a continuum | **weaker** (finite lattice) |
| L7, L8 | twist and flux sectors transported exactly by gauge-covariant, centre-equivariant blocking ('t Hooft gluing, r3-monotone §6.2) | yes, exact | turns "two volumes" into "one volume, two actions" | identity, holds for all groups | infrastructure |
| L11 | centre symmetry unbroken = no global colour root; Chatterjee: decay under all boundary conditions + centre ⇒ area law | 't Hooft duality F_e = dual(F_m) (proved, Lean, round 3) | links form (a) to flux growth (one direction only) | Z₂: centre broken at weak coupling, correct | — |
| L14 | one-sided scale comparisons (data processing, chessboard) are "one witness"; the missing step needs "both" | — | a reading of round 3's obstruction, no new inequality | group-blind | — |
| L16 | data processing for blocking (`blocking_tightens`, round 3) | inequality, factor ≤ 1 | nothing new | photon saturates it | dead |
| L17 | the blocking factor 2 per layer (the layer clock); 10 or e in DMP | — | none (the factor is a convention) | — | — |
| L18 | α as the act number of light, z_U(1) = 2πα (§2.2) | exact for the free photon | the photon test as an identity | — | reading |

---

## 2. Candidate 1 (first and deepest): the act identity on a box

### 2.1 The dictionary

| DMP (Reach.lean) | Yang–Mills on a periodic box of side L (ħ = c = 1) | status |
|---|---|---|
| existence x of an act | E_e(L): energy of the lowest state with one unit of centre flux (e = 1), above the vacuum | definition |
| extent e | L: a flux winding the box must span it | definition |
| quantum Q | the act number **z(L) = E_e(L)·L**; for light z = 2πα (fixed), for SU(2) z runs | §2.2 |
| grid resolution k | 1/a (lattice spacing); z is dimensionless, so k drops out exactly as in `mg_reach_existence_floor` | — |
| time to live τ (tick rate) | 1/E_e: Euclidean correlators of flux-carrying operators decay like e^{−E_e t}; with RP the transfer matrix makes E_e a true energy (r3-monotone B1) | known (Osterwalder–Seiler RP) |
| 3s1t, e = τ | z = 1: the box side equals the flux state's TTL (`boundary_iff_ttl`, Lean) | proved (Lean, trivial algebra) |
| reach R | the length beyond which a flux cannot stay one act: a flux-tube length scale | conjecture (it is confinement) |
| floor Q/R; act chain | E_e(L) ≥ (Q/R²)·L: a string tension σ = Q/R² (`act_chain_floor`, `act_number_quadratic`, Lean) | proved as a toy |
| no reach, no floor | one act spans the box at every size: z = Q frozen (`single_act_frozen`) — the photon | proved as a toy |

The sector: the cleanest choice is a box with a magnetic 't Hooft twist m_z (twist in the xy-plane) and electric flux e_z parallel to
it. Then the classical vacua are the twist eaters of round 3 (`su2_twist_eater`): P_x, P_y anticommute and P_z commutes with both, so
P_z = ±1. These two vacua are exchanged by the centre transformation Ω̂_z and are not gauge equivalent (tr P_z = ±2). The e_z = 1
state is their odd combination, and the energy splitting is a tunnelling energy. The Polyakov loop tr P_z is gauge invariant, carries
e_z = 1, and its time correlator decays like e^{−E_e t}: that is the measurable form. ('t Hooft 1979, 1981; van Baal's thesis 1984;
García Pérez, González-Arroyo, Snippe, van Baal 1994 for fractional instantons in twisted boxes; known, memory.)

### 2.2 What the act number does across the scales

| regime | z(L) | status |
|---|---|---|
| U(1), Coulomb phase | **z = e²/2 = 2πα per unit flux², at every L** (the flux zero mode: E = (e/L²)²/2 · L³) | known (classical, exact for the free photon) |
| SU(2), small twisted box | **z ∝ (log(1/LΛ))² · (LΛ)^{11/3}**: the tunnelling path from P_z = +1 to −1 is a doubly twisted configuration with Q ∈ ℤ + ½, so action ≥ 4π²/g²(L) (Bogomolny); with one-loop running 4π²/g²(L) = (11/3)·log(1/LΛ); the prefactor (four translation zero modes) gives the log² | heuristic (standard semiclassics); the exponent 11/3 is the same for every SU(N) (Q = 1/N, b₀ = 11N/48π²) |
| SU(2), large box | z ≈ σL² − π/3 (string with Luescher term), Nambu–Goto: z = σL²·√(1 − 2π/(3σL²)) | known as expectation (lattice: de Forcrand and von Smekal 2002, electric flux free energies linear in L, memory) |
| SU(2), z = 1 | Nambu–Goto: σL² = 2.49, **L√σ ≈ 1.58**; the Nambu–Goto deconfinement (Hagedorn) length is √(2π/3) = 1.45/√σ; lattice 1/T_c ≈ 1.41/√σ (T_c/√σ ≈ 0.71, memory) | heuristic |
| Z₂, deconfined (weak coupling) | **z falls**: the two flux sectors are split only by flipping one (z,t)-plaquette in every (x,y)-column, cost ≥ c·β·L_xL_y, so E_e ∝ e^{−cβL²} and z ∝ L·e^{−cβL²} | proved (paper, sketch: a minimal-action count; the splitting bound is heuristic at finite β) |
| finite subgroups Q8, 2T, 2O, 2I, large β | **z falls**, by the same count: a discrete group cannot interpolate between the two twisted vacua smoothly, so tunnelling costs a whole cross-section | proved (paper, sketch: minimal action) / heuristic (splitting) |

**Reading (the owner's α pointer, now exact).** Light's act number is 2πα, the same at every scale: information that never asserts
itself as an act (no running, no boundary). The Balance paper's "keeping an act in existence costs h·(1/c)·α" has the same structure
(the 2π here is the geometry of a box; for the electron it is a circumference). Gluons' act number starts far below light's in a small
box (an act that has to tunnel through a counted quantum), grows like the 11/3 power, passes 1 at the existence boundary, and then
grows like the area (an act stretched beyond its reach pays per segment).

### 2.3 Lead 1 of the coordinating session, checked

"E_e(L)·L at small L is proportional to g²(L)": **true for U(1), not for SU(2).** For U(1) it is exact (z = g²/2). For SU(2) it depends on
the sector: with e ∥ m it is exponentially small, e^{−4π²/g²} (§2.2); with m = 0 the small-volume flux energies come from the toron
valley and scale like g^{2/3}/L (Luescher 1983; van Baal and Koller; memory). The **twisted Polyakov loop scheme** (de Divitiis,
Frezzotti, Guagnelli, Petronzio, Nucl. Phys. B 1994 for SU(2); used for SU(3) by Itou and collaborators; memory) defines g² from the
**amplitude** of a twisted Polyakov-loop correlator at separation L/2, which is ∝ g² at tree level, not from the energy. The Wilson-loop
scheme of Bilgici et al. (2009) is a different scheme again. All of these define running couplings; the energy-based act number is the
one that matches the DMP act identity term by term and has the cleanest unit tests.

### 2.4 Lead 2: is the act identity per layer two-sided across volumes?

**Exact per layer (proved, paper; extends r3-monotone §6.2).** Take a block-spin map built from parallel transports that tiles the box,
is gauge covariant, commutes with global conjugation, and is applied in all four directions. The centre transformations Ω̂ on the
fine lattice map to the same centre transformations on the coarse lattice (a centre element is unchanged by parallel transport and
conjugation), and the 't Hooft gluing by Ad(A), Ad(B) is carried along (r3-monotone §6.2). The blocking is a Markov kernel (total mass 1),
so every sector's partition function is preserved. Hence

  z(2L; S) = z(L; S_eff),  E_e(2L; S)·(2L) = E_e(L; S_eff)·L in the coarse units,

with the same S_eff for every sector. This is the DMP frame rule (L7) and re-keying invariance (L8) in Yang–Mills form, and it is
**two-sided** (an equality). In DMP words: the act identity is transported layer to layer without loss.

**Where it stays one-sided.** The identity compares the fine action on the box 2L with the blocked action on the box L. Growth of z
needs z(L; S_eff) > z(L; S): two different actions on the same box. RP gives no inequality between two actions, and every known
scale-comparing inequality is one-sided and group-blind (r3-monotone §1). That is round 3's obstruction, unchanged.

**The anisotropic split (proved (paper) for the cancellation; the rest conjecture).** Write one doubling as four one-direction moves:
lengthen the flux direction, widen each of the two transverse directions, and double time (time does not change an energy once T → ∞).
With 3s1t each move can be read with its own direction as "time", so each is a one-direction statement of the kind RP controls
(r3-monotone B1–B3). For the photon, E = c·L∥/L⊥²: lengthening multiplies E by 2, each widening by ½, and z = L·E is then exactly
frozen (`coulomb_frozen`, Lean). For a string, E = σL∥: lengthening ×2, widening ×1, z ×4 (`string_quadruples`). So growth of z is
exactly the statement that **widening relieves the flux energy by less than light's factor ½** (with lengthening at least
proportional). This is `mg_returns_to_balance` versus `mg_marginal_never_returns` (L13): the photon is the marginal case where the two
rates cancel exactly, by classical scale invariance; b₀ tips the balance. What keeps it one-sided: the flux energy is defined after
T → ∞, and the RP bounds of each one-direction move hold at finite T; the limits do not commute in those bounds, and there is no RP lower
bound on a sector energy in a wider box.

### 2.5 Lead 3: does 3s1t link crossover form (a) to form (b)?

- **(a) ⇒ growth of z: yes, one way.** D′ for every boundary condition is confinement-strength (round 3, via Chatterjee's theorem with
  the non-trivial centre): an area law. Area law ⇒ E_e(L) ≳ σ′L for large L, so z grows like L² ('t Hooft's classification; the
  rigorous link between Wilson-loop area law and flux energies in a twisted box goes through the Tomboulis–Yaffe and Borgs–Seiler type
  inequalities; known in parts, memory; not re-checked). By `act_reach` (Lean) a multiplicative margin per doubling reaches any target
  in a bounded number of doublings, uniformly in the start.
- **(b) or growth of z ⇒ (a): no.** z measures the gap of the transfer matrix in the **centre-charged** sector. D′ and the Clay gap are
  about the vacuum sector (glueballs). 3s1t (Euclidean symmetry) makes spatial decay and temporal gap one statement **within a sector**
  (`mg_space_time_certificate`), but no known lemma bounds the vacuum-sector gap by the flux-sector energy. That "sector transfer" is
  the honest missing link of this family. (Deconfined Z₂ shows the converse failure: gap, but falling z.)
- Tick rate: in DMP the TTL floor `mg_ttl_existence_floor` is the gap; in Yang–Mills it is the gap of the sector the act lives in. The
  project's RP doubling tools (`OneScale/Doubling.lean`, `TorusRP.lean`: `torus_doubling`, `torus_theoremC`) apply to the flux-sector
  correlator on the twisted torus as they stand (the magnetic twist is spatial, so the time reflection keeps RP), and give one-sided
  control: decay at a long time bounds decay at a short time.

### 2.6 Unit tests (lead 4), the review's deconfinement test, and the features used

| test | act number | verdict |
|---|---|---|
| photon (U(1), weak coupling) | z = 2πα at every L (frozen); `nonincreasing_never_reaches` (Lean) | fails to grow: **pass** |
| Z₂, weak coupling (deconfined) | z falls like L·e^{−cβL²} (topological degeneracy of flux sectors) — not "growing for a different reason", as the lead guessed: it shrinks | fails to grow: **pass**; a gap-only claim is not made, so Z₂'s gap is not contradicted |
| finite subgroups of SU(2), large β | z falls (no smooth tunnelling between the twisted vacua) | **pass** — this is where the continuum of fluctuations enters |
| triviality (φ⁴₄) | no centre flux, no act number; the family makes no existence claim | not applicable, **pass** |
| deconfinement (box thinner than 1/T_c) | z < 1 there (heuristic: z = 1 near L√σ ≈ 1.5); the target is "z crosses 1 somewhere and keeps growing", never "z ≥ 1 at a prescribed small L" | **pass** if the target is stated that way |
| features used | twist eaters (the two twisted vacua), continuum of fluctuations (tunnelling at L-independent classical cost through a fractional instanton; Bogomolny floor 4π²/g²), b₀ > 0 (the floor falls with L: exponent 11/3), self-charge (non-abelian twist eaters; Q = ½ needs non-commuting holonomies) | all four |

**Conjecture W (widening relief).** On the crossover stretch, doubling one transverse side of the twisted box lowers the flux energy
by less than light's factor ½, with a margin: E_e(2L_x, L_y, L_z) ≥ ½(1 + δ)·E_e(L_x, L_y, L_z), and lengthening the flux direction at
least doubles it. Together these give z(2L) ≥ (1 + δ)²·z(L). U(1):
equality at ½ (fails the margin). Z₂ and finite groups: the relief is far stronger than ½ (fails). SU(2): small-L semiclassics and
large-L strings both satisfy it (heuristic). Not proved; target strength weaker than the gap (it is a finite-box statement).

### 2.7 Lean (proved, `ActIdentity.lean`, namespace `Attempts.R4prep.Act`)

`act_piece_floor`, `act_chain_floor`, `act_number_quadratic` (the act identity per segment within reach gives a string tension Q/R² and
z ≥ Q·L²/R²); `single_act_frozen`, `coulomb_frozen` (no reach: z frozen, the photon); `string_quadruples`, `power_doubling`,
`power_doubling_gt_one` (doubling factors 4 and 2^p); `act_reach` (a multiplicative margin 1 + δ while below z* reaches z* within N
doublings, N depending only on z₀, z*, δ: uniform in the bare coupling); `nonincreasing_never_reaches` (Z₂, finite groups, U(1));
`boundary_iff_ttl` (z = 1 ⇔ L = TTL). These are toys: they contain no Yang–Mills; they state what the measurement and the conjectures
would have to supply.

### 2.8 Targets of this family, and their strength

| target | statement | vs the mass gap |
|---|---|---|
| T1a, the existence boundary | z(L) crosses 1 at some L_* (and L_* sets L₁; a line of constant physics) | **weaker** (one finite box); a tuning step, like "no fixed point" (review finding 1), but in a scheme where the photon and the finite groups fail visibly |
| T1b, act growth | z(2L) ≥ (1 + δ)·z(L) for all L ≥ L_* (equivalently, with `act_reach`, z grows at least geometrically) | **incomparable**: flux-sector confinement; implied by D′ (via Chatterjee), does not imply the vacuum gap |
| T1c, the weak end | two-sided semiclassical bounds on z for L ≤ L_U, with the 11/3 exponent | **weaker** |
| missing link | flux-sector gap ⇒ vacuum-sector gap | would turn T1b into the gap; no route known |

### 2.9 Cheapest decisive first test: a pre-registered measurement of z(L)

Sketch for a pre-registration (to be written in the attempt's folder before any run; GPU, by the coordinating session):
- **Observable.** SU(2) Wilson action on L³ × T with the magnetic twist m_z (the xy-plaquettes at (x, y) = (L−1, L−1) for all (z, t)
  get coupling −β: one fixed sheet, no interpolation). C(t) = Σ_{x,y} ⟨tr P_z(x, y, t) tr P_z(0, 0, 0)⟩ with spatially smeared links;
  fit A(e^{−Et} + e^{−E(T−t)}); z = L·E in units of a√σ from the TTL scan.
- **Grid.** β ∈ {2.3, 2.4, 2.5, 2.6} × L/a ∈ {6, 8, 10, 12, 16}, T/a ≥ max(4L/a, 5/(aE)) (small boxes need long T because E is small),
  covering L√σ ≈ 0.5–3.5.
- **Pre-registered readings.** (1) z increases with L√σ at 2σ across the whole range (T1b on the data); (2) the location L_*√σ of z = 1,
  compared with 1/T_c ≈ 1.41 and Nambu–Goto 1.58; (3) the smallest doubling factor z(2L)/z(L) on the stretch and where it occurs (the δ of
  `act_reach`); (4) at the small-L end, the local exponent d log z / d log L, compared with 11/3 (qualitative: logs and artefacts);
  (5) at the large-L end, σL² − π/3.
- **Controls (same code).** U(1) at β = 1.1 with twist e^{iπ}: z flat, ≈ e_R²/2 (the photon gate for this observable); the binary
  icosahedral group 2I at large β: z falling (the finite-subgroup gate); SU(2) at β = 2.6, L/a = 12 with the twist in the yz-plane and
  flux e_x: equal z within errors (symmetry check).
- **Cost.** One ensemble per point with a fixed sheet sign (the kernel change is a subset of attempt 2's per-plaquette coupling);
  roughly 1/20 of attempt 2's per-point cost before the longer T at small L. Estimate (heuristic): a few GPU hours against attempt 2's
  about 11 h. A CPU feasibility check at L/a = 6, β = 2.3 fits in minutes.

---

## 3. Candidates 2–5

### 3.1 Candidate 2: the stack potential (gradient flow) — NFP as a one-measure inequality

- **DMP law:** `k4_stack_never_raises` (Theory.lean:393), `mg_returns_to_balance` / `mg_marginal_never_returns` (MassGap.lean:218, 226).
- **YM counterpart (known):** Luescher's gradient flow (arXiv:1006.4518) is the gradient flow of the action, so per configuration
  dS/dt = −‖D_νG_νμ‖². With E(t) the flowed energy density and K(t) = ⟨|D_νG_νμ|²⟩/volume: d⟨E⟩/dt = −K, hence
  t·d/dt log(t²⟨E⟩) = 2 − R(t), **R(t) := t·K(t)/⟨E(t)⟩**. The flowed coupling g²_GF ∝ t²⟨E⟩.
- **What it delivers:** "no fixed point" in the gradient-flow scheme is exactly R(t) ≤ 2 − δ on the stretch. The comparison of scales is
  done by an exact identity inside **one** measure: no second volume, no second action. That removes the structure round 3 found
  blocking (RP never compares two volumes); what remains is an inequality between two local expectation values at one flow time, the
  type RP and the bootstrap can address in principle.
- **Unit tests:** photon: R ≡ 2 exactly (free field: ⟨E⟩ ∝ t⁻², so −d⟨E⟩/dt = 2⟨E⟩/t; known), the marginal case: **pass**. Z₂ and finite
  subgroups: there is no flow (no Lie algebra), so the statement cannot be made: **pass by construction**, the continuum is built in.
  φ⁴₄: the scalar analogue has R > 2 (infrared free): **pass**. Deconfinement test: an infinite-volume statement, not applicable.
- **Target vs gap:** **weaker** (a tuning step; with the review's finding 1 it feeds `gap_of_stepScaling` only together with a control
  hypothesis).
- **Speculation (not ranked separately):** with Bogomolny, a box's flowed energy bounds its topological charge, and reflection
  positivity makes the topological-charge correlator negative at non-zero distance (Seiler), so box charge variance ≥ χ_t·volume. That
  suggests g²_GF(t) ≳ √χ_t·t, i.e. χ_t > 0 would give the reach. But RP gives only χ_t ≤ (finite-box quantity): the one-sided problem
  reappears as "no complete screening of topological charge".
- **First test:** Lean: the free-field identity R = 2 in a finite Fourier model and the reduction "R ≤ 2 − δ on the stretch ⇒ reach";
  numbers: R(t) on existing TTL/Leg B configurations (flow code is standard; CPU minutes to an hour per ensemble).
- **Cost:** low for the test; an analytic proof of R < 2 at α_s ≈ 1 has no known route.

### 3.2 Candidate 3: the self-stabilizing sandwich — semiclassics at the weak end, and 't Hooft-flux compactification

- **DMP law:** `st_upper` / `st_lower` / `st_self_stabilizing` (R2Stable.lean:78, 103, 136); the counted floor (MassGap.lean:141).
- **YM counterpart:** an upper bound by a constructed path (a trial fractional instanton: "real paths come through") and a lower bound by
  Bogomolny ("fake low values are flushed out": nothing in the Q = ½ sector costs less than 4π²/g²). This brackets z(L) from both sides
  at small L. Its 2D cousin: on ℝ² × T² with 't Hooft flux, small T² is weakly coupled and confines through centre vortices made of
  fractional instantons (Tanizaki and Uensal, arXiv:2201.06166, PTEP 2022; Hayashi and Tanizaki 2024; known, memory); continuity to large
  T² (adiabatic continuity) is a conjecture supported by lattice data.
- **Delivers:** certified two-sided values of z at the weak end (T1c), i.e. the "U" end of any grid; a controlled confining regime to
  start a continuity argument from.
- **Unit tests:** as candidate 1 (no fractional instantons for U(1), Z₂, finite groups). Deconfinement test: the small-T² regime
  confines only because of the twist; without flux it deconfines, correctly.
- **Target vs gap:** the weak-end bounds are **weaker**; adiabatic continuity is **stronger** (it would give the gap at every size).
- **First test:** a literature read (one afternoon) of the fractional-instanton tunnelling amplitude in a twisted T³ box and of the
  Tanizaki–Uensal construction, to fix the prefactor of z at small L; then compare with the small-L end of the measurement in §2.9.
- **Cost:** medium (semiclassical analysis is standard but rigorous one-loop control is hard).

### 3.3 Candidate 4: two witnesses per layer — the bootstrap at the blocked layer

- **DMP law:** T38 / `pass_has_two_independent_witnesses` (Theory.lean:196), `gate_pass_iff` (Gate.lean:29).
- **YM counterpart:** the two witnesses are reflection positivity of the layer (T38; Gram matrices positive) and the exact
  Schwinger–Dyson (Makeenko–Migdal) loop equations. Together they give **two-sided** certified bounds (Kazakov and Zheng, arXiv:2203.11360;
  the project's bootstrap runs). On the twisted torus the loop equations hold with the twist, so certified finite-time correlators of the
  flux sector are possible in principle.
- **Delivers:** two-sided bounds at fixed bare coupling; with the RP Hankel tools, one-sided bounds on E_e. Not a continuum statement.
- **Unit tests:** a method, not a claim (it would certify different numbers for U(1)); the Lie-type loop equations need a continuous
  group (finite groups have only discrete identities). The deconfinement test applies to whatever is certified.
- **Target vs gap:** **weaker** (finite lattice).
- **First test:** check whether the running bootstrap can include one twisted Polyakov-loop correlator; cost high (SDP machinery,
  artefact control unproved).

### 3.4 Candidate 5: frame rule and re-keying — exact sector transport (infrastructure)

- **DMP law:** `extend_preserves_decisions` (Theory.lean:268), `loop_hol_rekey` (Gauge.lean:88), `nonabelian_class_invariant` (218).
- **YM counterpart:** §2.4's exact identity z(2L; S) = z(L; S_eff), and the same for the twist free energy (r3-monotone §6.2).
- **Delivers:** turns every "compare two volumes" into "compare two actions on one volume"; no inequality by itself.
- **Unit tests:** an identity; true for every group (it claims nothing).
- **Target vs gap:** none (an identity).
- **First test:** Lean, finite spaces: a Markov kernel that commutes with a centre action preserves every sector trace, so the sector
  ratio of the blocked layer equals the fine one (a few dozen lines with the `gated_rp` style of round 3).

---

## 4. Dead on arrival (checked, with the reason)

| idea | why it dies |
|---|---|
| "a sub-layer only tightens" (L16) as the cross-layer law | data processing, factor ≤ 1, holds for every group; the photon saturates it (round 3, `identity_kernel_saturates`) |
| "the same floor at every layer" (L3) | its hypothesis is the open piece |
| `contraction_decay`, `st_self_stabilizing` as gap mechanisms | the contraction is the hypothesis |
| balance at every layer | excludes any area law (round 3, `balance_excludes_area_law`) |
| T24 asymmetry (L14) read as RP/chessboard | a reading of the one-sidedness, group-blind as an inequality |
| free-energy additivity across volumes (two-sided with surface errors) | group-blind, and the surface errors O(β·L³) swamp the O(1) quantities (twist, flux) that matter |
| Cauchy interlacing of blocked transfer matrices (two-sided between different Hilbert spaces) | group-blind; it orders spectra, it does not see b₀ |
| Hankel/RP doubling in time (`torus_doubling`) as a cross-volume tool | one direction at a time, every group |
| the twisted Polyakov loop **amplitude** scheme as the act identity | a fine coupling, but its tree-level ∝ g² is the amplitude, not existence × extent; it does not carry the unit-test structure of §2.6 |
| "E_e·L ∝ g²" for SU(2) | false (§2.3); true only for U(1) |

---

## 5. Ranking

| rank | candidate | DMP law | YM counterpart | delivers | unit tests | target vs gap | first decisive test | cost |
|---|---|---|---|---|---|---|---|---|
| 1 | **act identity on a box** | L1, L5, L6 (+ L9, L13) | act number z = E_e·L in the twisted box; 3s1t = Euclidean symmetry; exact transport per layer | DMP-native coupling and tuning; T1a/T1b/T1c; places the one-sided step at the "widening relief" | photon, Z₂, finite, triviality, deconfinement: pass; uses all four features | T1a weaker; T1b incomparable | §2.9 measurement (pre-registered, GPU, a few hours); Lean done for the toy layer | low–medium |
| 2 | stack potential (gradient flow) | L12, L13 | dS/dt = −‖DG‖²; R(t) < 2 | NFP without any volume comparison | pass (photon marginal; finite groups excluded by construction) | weaker | R(t) on existing configurations; Lean free-field identity | low (test), unknown (proof) |
| 3 | self-stabilizing sandwich | L10, L9 | fractional-instanton upper bound + Bogomolny lower bound; ℝ²×T² flux compactification | two-sided weak-end values of z; a controlled confining start | pass | weak end weaker; continuity stronger | literature read + small-L comparison with §2.9 | medium |
| 4 | two witnesses per layer | L15 | RP + loop equations = bootstrap | two-sided finite-lattice bounds | method | weaker | a twisted correlator in the running bootstrap | high |
| 5 | exact sector transport | L7, L8 | centre-equivariant blocking | infrastructure for 1 | identity | — | Lean, finite spaces | low |

---

## 6. Recommended round-4 design (three attempts plus one optional)

**Attempt 1: the act number, measured (data, pre-registered).** Write the pre-registration of §2.9 in full (thresholds, fit windows,
error model, what counts as a plateau), run a CPU feasibility point, then hand the GPU job to the coordinating session. The question
it answers is the owner's in numbers: does SU(2)'s act number pass 1 near the deconfinement length and keep growing by a margin at every
doubling, while light's stays at 2πα and the finite groups' falls? Its outputs (L_*, the smallest doubling factor and where it occurs,
the small-L exponent against 11/3) fix every constant the analytic attempts need, and it is the first test of Conjecture W on data.
It is cheaper than attempt 2's twist free-energy grid and should replace it as the first GPU job of the round.

**Attempt 2: the act identity per layer, exact (Lean and paper).** Make the Yang–Mills side of the dictionary rigorous where it is
rigorous: (i) the flux sector of the twisted box as a transfer-matrix sector (RP in time with a spatial twist; Z ratio = (1 − ρ)/(1 + ρ),
r3-monotone B1) and the TTL reading E_e = −log of the sector's top eigenvalue ratio; (ii) exact transport z(2L; S) = z(L; S_eff) for a
centre-equivariant blocking (finite-space Lean first, then the gauge statement on paper); (iii) the finite-subgroup and Z₂ gates as
theorems: the minimal action of any tunnelling history between the two twisted vacua is at least c·β·L_xL_y (a counting argument), so
z falls at large β; (iv) T38 in full for a reflection-compatible blocking (round 3's top transfer), since the blocked layer's flux
sector needs its own transfer matrix. Target: identities and test theorems, no growth claim, all weaker than the gap.

**Attempt 3: where b₀ enters — the widening relief (analytic, with an adversarial reviewer).** State Conjecture W precisely on the
lattice; prove the photon's exact marginality in the free lattice theory and the finite-group failure; then try the weak end as a
two-sided sandwich (Bogomolny lower bound on the Q = ½ sector, a fractional-instanton trial configuration for the upper bound) to
certify z and its doubling factor for L ≤ L_U, the "U" end of a grid. Credit and check the semiclassical literature (van Baal; García
Pérez, González-Arroyo; Tanizaki and Uensal). The attempt must say explicitly which of the four features each inequality uses, and it
must record where the order of limits (T → ∞ before L → 2L) blocks a full proof.

**Optional attempt 4: a second scheme for the same margin (gradient flow).** Measure R(t) = t·K/⟨E⟩ on existing ensembles and prove the
free-field identity R = 2 in a Fourier model. It costs little, needs no new kernel, and checks that the margin found in the act-number
scheme is not a scheme artefact.

**What this round would not deliver, said plainly.** None of these targets is the mass gap. The act-number family gives a DMP-native
coupling, the tuning that pins Yang–Mills down, a crossover statement weaker than the gap, and a flux-sector confinement statement. The
step from a large flux-sector energy to a gap for glueballs (the vacuum sector) is open, no DMP law in `evidence/` supplies it, and it
should be named in the round's rules as the next piece rather than claimed along the way.

---

## 7. Files

- `DMP-SCOUT.md` (this note).
- `build.sh`: builds `Attempts.R4prep.ActIdentity` in WSL `~/formal-r4prep` only, prints axioms, scans for `sorry`/`axiom`/`native_decide`
  (`wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/round4-prep/build.sh`).
- `../../formal/Attempts/R4prep/ActIdentity.lean`: the 11 theorems of §2.7.
