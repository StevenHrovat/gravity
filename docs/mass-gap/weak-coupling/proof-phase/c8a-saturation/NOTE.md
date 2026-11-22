# c8a-saturation: the saturation theorem for centre-vortex sheets (cycle 8, workstream 1, 2026-11-22)

Task: an energy-versus-entropy estimate showing that centre-vortex sheets are saturated at one block scale (free energy per
placement below the entropy of placements, so no tie can be forced), uniformly over every outside; the tie-free part of the one-box
criterion from it; method first on 4D Z2; the continuity mechanism (SU(2) against 2I); where uniformity over outsides enters and what
the chessboard estimate does with it; what saturation gives and what remains of the gap; unit tests.

Lean: `formal/ProofPhase/Saturation/{Sheet,Vortex,EnergyEntropy,Tests,Reduction}.lean` (1352 lines), built in `~/formal-c9a`
(`build.sh`, "Build completed successfully"), 32 headline declarations checked by `axioms.sh` (`axioms.log`: each depends only on
`propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`, no new axiom). Numerics: `PREREG.md` (written first),
`z2_exact_2d.py`/`.log` (N1), `z2_twist_4d.py`/`.log` (N2); CPU only, about 4 minutes in total.

Claim levels: **Lean** (built and axiom-checked), **exact** (closed formula or brute force here), **MC** (Monte Carlo here),
**paper** (argued here), **recalled** (literature, not re-read), **named** (a hypothesis stated, not proved).

---

## 0. Results in plain words

1. **A saturation theorem is proved, for real lattice objects, in every finite torus** (Lean, `vortex_saturation`): for any compact
   group with a central involution `z` (Z2, SU(2), U(1), finite groups), any plaquette actions whose worst-case oscillation is `E`,
   and the 't Hooft twist sheet in any plane, `|Z - Z_tw| <= B (Z + Z_tw)` with `B = (N^d p q^(N-1)/(1-q))^N`, `p = 1 - e^(-E)`,
   `q = 2(d-1) p`. So the flip probability `P = Z_tw/(Z + Z_tw)` obeys `|1 - 2P| <= B ~ q^(N^2)`: **P -> 1/2 at the area rate**, the
   Tomboulis-Yaffe form `1/2 - P <= e^(-rho L^2)`. The window `q < 1` is exactly "**one placement costs less than the entropy
   threshold log(K/(K-1))**", `K = 2(d-1)` (`satQ_lt_one_iff`); in `d = 4`, `E < log(6/5) = 0.182`.
2. **It is an energy-entropy theorem with the two sides exchanged by duality** (section 1): "vortex sheets are saturated" is the same
   statement as "the dual (electric) surfaces are dilute", a Peierls bound whose activity per element is `tanh(E/2)` (exact for Z2,
   `tanh beta`) and whose entropy is the number of ways to continue a surface. The proof's activity `1 - e^(-E)` is a pointwise
   upper bound of it (`tanh_half_le_satP`).
3. **Uniformity over outsides is where the method choice matters** (section 4). The proof uses activities bounded **pointwise, for
   every configuration**; the bound therefore holds uniformly over every field that enters the weights (Lean,
   `z2_background_saturation`: Z2 with an arbitrary coupling field `|J_p| <= Jbar`, uniformly in the field). The chessboard estimate is
   also worst-case, but over **patterns** on a reflection-positive torus, not over **outsides**: it is an annealed statement and
   cannot give a conditional bound given an adversarial outside. For the one-box criterion only the pointwise form works.
4. **Toy, 4D Z2, both phases**: confined, saturation holds (Lean in the window `beta < 0.091`; MC at `beta = 0.30`, `P = 0.494`);
   deconfined, it fails (MC at `beta = 0.60`, `P = 3e-8`, `F_tw = 17.4`), and the Lean theorem is silent there (`not_window_weak`).
5. **Continuity, made exact** (section 6): an SU(2) vortex of width `d` costs `beta pi^2/(2 d^2)` per fine plaquette of sheet, i.e.
   **`beta pi^2/2` per placement at its own scale, independent of `d`** (classical scale invariance of 4D Yang-Mills). A 2I vortex
   costs at least `0.95 beta d^2` per placement (it cannot spread: the minimal non-trivial plaquette of 2I has `1 - cos 36 deg`). So
   continuity makes the per-placement cost **bounded** for SU(2) and **growing like the area** for 2I; it does not by itself make it
   small. What must bring it under the threshold is the running coupling `beta_eff(l)` at the block scale: that is the open input,
   stated as the named hypothesis **H_sat(l)** in a testable form (section 6.3).
6. **What saturation gives to the gap** (section 5, Lean `Reduction.lean`): the one-box influence splits exactly into a **centre part**
   (the tie part) and an **adjoint part** (the stateless part) at a hybrid law, and the budgets add: `gamma_Z + gamma_A < 1` gives
   `FineOneBox` and the full assembly (`yang_mills_assembly_split`). A tie that moves a fraction `theta` of the box forces
   `gamma_Z >= theta` (`tie_forces_budget`). Quenched saturation (H_sat) gives `gamma_Z = O(1/l)` (paper, Dobrushin comparison for the
   binary layer). The adjoint part is **not** supplied by saturation and does **not** follow from known theorems; the certified
   adjoint numbers (0.0036, about 1e-3) are strong evidence that its budget is small, but they are annealed single-site numbers of a
   fitted action, not worst-case box influences.
7. **Unit tests** (section 7): photon (no central involution; the trivial twist gives `P = 1/2` in every phase: the statement is empty,
   correctly), Z2 both phases (pass / silent-and-fails), 2I at weak coupling (silent; cost grows like the area), mixture (saturation
   passes, `gamma_A` fails), SU(2)xU(1) (the twist sees only the SU(2) factor, saturation passes, the photon sits in the adjoint
   layer and `gamma_A >= 1`): saturation never implies the gap where there is none.

---

## 1. Energy against entropy, and why "saturated" is a Peierls statement

**Vortex sheets.** In a gauge theory with centre Z2, a centre vortex is a closed surface of the dual lattice made of plaquettes whose
centre sign is flipped. Let `E` be the cost of one placement (one plaquette of sheet) and `K` the number of ways a sheet can be
continued per element (entropy `log K` per element).

* **Sheets dilute (ordered, deconfined)**: `K e^(-E) < 1`. Energy beats entropy for sheets; long sheets are exponentially rare; a
  sheet forced by the boundary sits at its cheapest positions; if two positions are degenerate, one boundary cell decides: a **tie**.
* **Sheets saturated (confined)**: the dual condition. For Z2 the high-temperature expansion writes the weight of a plaquette as
  `cosh(beta)(1 + tanh(beta) sigma_p)`, so the partition function is a gas of closed **electric** surfaces with activity
  `u = tanh(beta)` per plaquette, and `beta = E/2`: `u = tanh(E/2)`. "Sheets cost nothing, every possibility exists" (the owner's
  reading) is `E -> 0`, i.e. `u -> 0`: the electric surfaces are dilute, `K u < 1`. A twist through the whole torus is then invisible
  except through electric surfaces that wrap the torus around it, which have area `>= N^2`: `1 - 2P = O((K u)^(N^2))`. For 2D Z2 this
  is exact: `1 - 2P = tanh(beta)^(N^2)` (N1 below). 4D Z2 is self-dual (Kramers-Wannier, recalled): the two Peierls conditions are
  exchanged at `tanh(beta*) = e^(-2 beta)`, self-dual point `beta_c = 0.4407`.

So saturation is a Peierls bound on the dual side, and the proof technique for it is the Peierls/cluster technique applied to the
electric surfaces. The Lean proof uses the **positive** version: write each plaquette weight as `e^(F0)(1 + h)` with
`0 <= h <= p(1 + h)`, `p = 1 - e^(-E)`, `E` the oscillation of the plaquette action. This activity is cruder than `tanh(E/2)`
(`tanh_half_le_satP`) but positive, which removes every sign problem and every cluster-expansion ratio estimate: the bad terms are
simply counted.

## 2. The theorem (Lean)

Setting: compact group `G`, left-invariant Haar probability, central `z` with `z^2 = 1`, plaquette actions `f_p` (one per plaquette,
measurable) with `F0 <= f_p <= F0 + E`; periodic lattice `(Z/NZ)^d`, `N >= 2`; directions `mu != nu`; slice `a`, layer `c`. The **twist
sheet** (`IsSheet`) is the set of plaquettes of the plane `(mu, nu)` based at `x_mu = a`, `x_nu = c`: one per value of the other
`d - 2` coordinates, a dual surface wrapping the torus. `Zf = int prod_p e^(f_p(U_p))`, `Ztw = int prod_p e^(f_p(z^[p in sheet] U_p))`.

**Proof structure** (all Lean):

1. *The sheet moves for free* (`tcount_move`, `twHol_move`): multiplying the `mu`-links at `x_mu = a`, `x_nu = c + 1` by `z` changes the
   twist count of every plaquette by `+-(sheet(c+1) - sheet(c))`; with `z^2 = 1` this turns the twist at layer `c` into the twist at
   layer `c + 1`, pointwise. Hence every term of the expansion is independent of the layer (`termI_tw_layer`).
2. *A configuration lets the sheet go unless it pins it* (`SurvLayer`, `tcount_cancel`, `twHol_cancel`): inside layer `c`, let
   `Reach` be the set of sites reached from just above a sheet plaquette of `A` by moves across non-sheet plaquettes of `A`. If no
   reached site sits just below a sheet plaquette of `A`, multiplying the `nu`-links starting in `Reach` by `z` makes every plaquette of
   `A` see an even total twist. So the term of `A` in `Ztw` equals its term in `Z` (`termI_tw_eq`) unless `A` pins the sheet in
   **every** layer (`SurvAll`).
3. *A pinning walk goes around the torus* (`length_ge_of_cross`): it starts at `x_mu = a + 1`, ends at `x_mu = a`, and may not cross the
   sheet; a lifted-height argument gives at least `N - 1` steps.
4. *The count* (`sum_surv_sheet_le`): a configuration pinning every layer contains `N` disjoint pinning loops (one per layer, loop-
   erased, each with its closing sheet plaquette), `>= N` plaquettes each, `>= N^2` in total; with `2(d-1)` continuations per step
   and at most `N^d` starts per layer, `sum_{A pins} prod_A h <= (N^d p q^(N-1)/(1-q))^N prod (1 + h)`.
5. *The comparison* (`expand_bound`, `vortex_saturation`): both partition functions are expansions in `prod_A h`; the non-pinning
   terms are equal; the pinning terms are bounded by `B` times the respective partition functions; so `|Z - Ztw| <= B (Z + Ztw)`.

**Statements.**

* `vortex_saturation (f) (hf : ∀ p, Measurable (f p)) (hlo : ∀ p g, F0 ≤ f p g) (hhi : ∀ p g, f p g ≤ F0 + E) (hN : 1 < N) (c)
  (hq : satQ d E < 1) : 0 < Zf d N f ∧ 0 < Ztw d N f z μ ν a c ∧ |Zf − Ztw| ≤ satB d N E * (Zf + Ztw)`, with
  `satQ d E = 2((d:ℝ) − 1)(1 − e^{−E})`, `satB d N E = (N^d (1 − e^{−E}) satQ^{N−1}/(1 − satQ))^N` (hypotheses `hz : ∀ g, Commute z g`,
  `hzz : z * z = 1`, `hμν : μ ≠ ν`, `a`, Haar left-invariant).
* `flip_saturation`: same hypotheses, `|1 − 2·flipP (Zf) (Ztw)| ≤ satB d N E` (`flipP Z T = T/(T + Z)`, c6a's object).
* `satB_eq`: `satB = (N^d p/(q(1 − q)))^N · q^{N·N}`: the area rate times `e^{O(N log N)}`.
* `wilson_vortex_saturation`: Wilson action `β Re tr` of any compact group with `|Re tr| ≤ n`, `E = 2n|β|`, window `twistQ d n β < 1`
  (the repo's centre-twist area-law window). Instances: `z2_vortex_saturation` (`|β| < log(6/5)/2 = 0.091` in `d = 4`),
  `su2_vortex_saturation` (repo's `SU2`, `negOneSU2`; `|β| < log(6/5)/4 = 0.046`, i.e. `β_std < 0.091`), `u1_vortex_saturation`.
* `z2_background_saturation`: Z2 with any coupling field `J_p`, `|J_p| ≤ J̄`, bound `satB d N (2J̄)`, uniform in the field.
* `energy_entropy` (abstract Peierls lemma, pointwise activities, witnesses counted by size `≤ C K^n`, sizes `≥ r`, `K p < 1`):
  `∑_{A bad} ∏_A h ≤ C (Kp)^r/(1 − Kp) · ∏(1 + h)`. `peierls_of_chessboard`: the probability form, with the chessboard estimate as a
  named input (`P(γ) ≤ z^{|γ|}`): `P(some contour of size ≥ r) ≤ C (Kz)^r/(1 − Kz)`.
* `satQ_lt_one_iff (hd : 2 ≤ d) : satQ d E < 1 ↔ E < log(K/(K − 1))`; `tanh_half_le_satP : tanh(E/2) ≤ 1 − e^{−E}`.

**What it is, honestly.** At the bare level this is the strong-coupling vortex free energy (Muenster 1981, recalled; consumed by
Tomboulis-Yaffe), here proved from scratch, group-blind, with explicit constants and no cluster expansion. Its window is far inside
the confined phase of Z2 (0.091 against 0.4407). It becomes SU(2) content only when applied at a block scale to an effective action
(section 6), and it applies directly only to effective actions of single-plaquette form.

## 3. The toy: 4D Z2, both phases (Lean, exact, MC)

* **Confined, strong coupling**: `z2_vortex_saturation`. (The finite-`N` bound needs `N` around 20 before `B < 1`, because of the
  crude `N^d` start count; a start count `N^(d-2)` on the sheet's slice is available and would lower that, not done.)
* **2D check (N1, exact)**: on 2x2 and 3x3 tori, `1 - 2P = tanh(beta)^(N^2)` to 50 digits at five couplings of both signs (odd `N`,
  `beta < 0` gives `P > 1/2`, as c6a found); the Lean bound (with `d = 2`) holds wherever `q < 1`. PASS. (A first run in double precision
  failed the 1e-10 criterion only by cancellation at `|1 - 2P| = 2e-12`; kept as `z2_exact_2d_float.log`; the rerun counts
  configurations exactly.)
* **4D Monte Carlo (N2)**, 4^4, thermodynamic integration over the sheet coupling, pre-registered: `beta = 0.05`: `F_tw = 0.005(2)`,
  `P = 0.4989`; `beta = 0.30` (confined, outside the Lean window): `F_tw = 0.023(16)`, `P = 0.494`; `beta = 0.60` (deconfined):
  `F_tw = 17.4(1)`, `P = 2.8e-8`. All three predictions pass. The deconfined value matches the classical count: one frustrated plaquette
  per `(0,1)`-slice is forced (each slice holds an odd number of frustrated plaquettes), `2 beta N^2 = 19.2`, minus the entropy of the
  sheet's position, about 2. The last integration point (`tau = 1`, `beta = 0.6`) is bimodal (-0.72 +- 0.19): the sheet tunnels; the
  Simpson weight of that point is 1/30, so even a shift of that point by its full range (about 1.6) moves `F_tw` by about 1,
  irrelevant for the pass (`P <= 0.05` needs only `F_tw >= 3`).
* **Deconfined, Lean**: silent (`not_window_weak`). The deconfined failure is the dual Peierls bound (sheets dilute) and the tie
  mechanism of c7c, both paper/recalled; MC above.

## 4. Uniformity over outsides: where it enters and what the chessboard estimate does

The one-box criterion asks for the influence of one outside cell on the box **for every outside** (worst case). A tie is an outside
that forces a sheet with two degenerate positions.

* **Where it enters the proof.** In the Lean proof the configuration enters only through the activity bound `0 <= h <= p(1 + h)`, and
  that bound holds **for every value of every link** (it is a statement about the range of the plaquette action). Everything else is
  combinatorics (the count) and exact changes of variables (moving and cancelling the sheet). So the bound is uniform over every field
  that enters the weights: inhomogeneous couplings, background fields, and, in the two-layer reading, every adjoint background
  (`z2_background_saturation`: the centre layer of a fixed adjoint background `V` is a Z2 gauge theory with couplings `J_p(V)` of
  any sign; the bound holds uniformly in `V` once `sup |J_p(V)| <= Jbar` with `6(1 - e^(-2 Jbar)) < 1`). For a box with frozen outside
  links the same argument runs with the expansion over the box plaquettes and the twists inside the box (paper; not formalised: the
  Lean objects are tori).
* **What the chessboard estimate does.** On a reflection-positive torus, `P(all plaquettes of X frustrated) <= z^|X|` for every pattern
  `X`, with `z` the reflected single-plaquette quantity; with a contour count this is a Peierls bound (`peierls_of_chessboard`). It is
  worst-case over **where the pattern sits** and needs no positivity of the activities, which is why it is the standard tool for
  ordered phases. But it is a statement about the torus measure itself: it bounds probabilities averaged over everything else
  (annealed). It does not bound the conditional probability given an arbitrary outside, and an adversarial outside can make a pattern
  likely. It cannot deliver the worst case over outsides that the one-box criterion needs.
* **The price of the pointwise form.** A pointwise activity must bound the **whole** plaquette weight, not only its centre-odd part.
  For the Wilson action the two coincide (`x -> -x` under the centre flip, so the oscillation `2n|beta|` is the worst centre-flip
  cost). For an effective block action they do not: the oscillation also contains the adjoint content. In the two-layer form
  (`z2_background_saturation`) the adjoint background is frozen and only the centre couplings enter, but then the bound must hold for
  **every** background, including block-flat ones. This is the exact place where the centre layer and the adjoint layer are entangled:
  a quenched centre statement needs either a worst case over adjoint backgrounds (strong), or an adjoint layer that is integrated out
  and stateless (then the effective centre couplings are non-local and the bound needs their decay).

## 5. What saturation supplies to the one-box criterion, and what remains

### 5.1 The split (Lean, `Reduction.lean`)

Between the box laws `q(sigma)` and `q(sigma')` (one outside cell changed) put a **hybrid law** `r`: centre layer distributed as under
`sigma'`, adjoint layer conditionally as under `sigma`. Then

    influence <= kappa_A + kappa_Z,   kappa_A: q(sigma) <-> r (adjoint conditional moved),  kappa_Z: r <-> q(sigma') (centre law moved)

(`isInfluenceBoundOn_split`; only the triangle inequality), and the one-box sums add (`oneBoxSum_add`).

* `FineOneBoxSplit T` (named, open): `FineOneBox` with the two influence numbers, the hybrid laws and budgets `gamma_Z + gamma_A < 1`.
* `fineOneBox_of_split : FineOneBoxSplit T → FineOneBox T`; `yang_mills_assembly_split (hL : OnLCP' T) (hN : NonTrivial T)
  (h : FineOneBoxSplit T) : TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T`.
* `tie_forces_budget`: for the centre specification of a block with influences `k_Z z <= kappa_Z(rel z)`, two outsides differing on
  cells at distinct relative positions that move a centre test function (oscillation `<= 1` per cell) by `theta |Lambda_0|` force
  `theta <= gamma_Z` (via c7c's `influence_telescope` and `sum_le_of_oneBoxSum`). **Ties are exactly large `gamma_Z`.**

### 5.2 From quenched saturation to the tie-free part (paper)

Let the binary layer at block scale `l`, conditional on any adjoint background and any outside, have plaquette couplings `|J_P| <= Jbar`
(Walsh form of c7b/c6c). One centre variable sees 18 others (6 plaquettes x 3 links); changing one of them moves its conditional log-odds
by at most `4|J_P|`, hence its conditional law by at most `tanh(Jbar)` in total variation. **Dobrushin's condition for the binary layer**
is `c := 18 tanh(Jbar) < 1` (the same constant as the repo's SU(2) single-link condition `18 tanh(2 beta) < 1`, with `Jbar = 2 beta`).
Dobrushin's comparison theorem (recalled, standard) then bounds the total influence of one boundary centre variable on all box centre
variables by `c/(1 - c)`, uniformly over outsides and backgrounds. With `Lambda_fb` the number of box cells whose adjoint conditional
law moves when one centre variable flips (the centre-to-adjoint feedback; `O(1)` if the adjoint layer is stateless):

    kappa_Z(u) <= Lambda_fb c/(1 - c),   sum_u kappa_Z(u) <= 8 l^3 Lambda_fb c/(1 - c),   gamma_Z <= 8 Lambda_fb c/((1 - c) l).

So **quenched saturation gives the tie-free part at every box size `l >= 8 Lambda_fb c/((1 - c) gamma_Z)`**, and with it Chatterjee's
Definition 2.3 for the binary layer conditional on the background (decay under every boundary condition in every cube, uniform
constants), hence the area law through the Ginibre comparison of c7b (`centre_area_law`, given `PlaqMixture`). In vortex free-energy
form it gives `1/2 - P <= e^(-rho L^2)` (section 2, applied to the binary layer). Not formalised: the conditional centre specification
of SU(2) and its single-site Dobrushin bound (the abstract pieces exist: `OneScale` Theorem A, `influence_telescope`).

### 5.3 What remains: the stateless adjoint part

`gamma_A` is the influence of one outside cell on the adjoint content of the box with the centre law held fixed, plus the feedback
`Lambda_fb` above. Saturation says nothing about it, and the unit tests show it must not (section 7: SU(2)xU(1), mixture). Known
results: for a single-site Dobrushin coefficient `c_A` of the adjoint layer at fixed centre configuration, valid uniformly over centre
configurations and outsides, the same comparison gives `kappa_A <= c_A/(1 - c_A)` and `gamma_A <= 8 c_A/((1 - c_A) l)` (standard). The
certified numbers (c3b: adjoint half 0.0036 of the linearised W1 column at `L sqrt(sigma) = 2.80`; c4d: adjoint half about 1e-3, two
orders below its window) would give `gamma_A` of order `0.03/l`, i.e. negligible. They do not yet: they are coefficients of the **fitted
blocked action**, averaged (annealed) and single-site, not worst-case bounds of the **true** conditional adjoint law. The missing link is
precise: **the fitted action's adjoint column bounds the true blocked conditional law of the adjoint layer, uniformly over centre
configurations and outsides** (the fit-to-measure step, Lemma UV in older language). The joint measurement (c5e: the vacuum act more than
doubles on `L sqrt(sigma)` 1.03 to 4.2) is vacuum-side (centre-even) evidence in the same direction, also not a box-influence bound.

## 6. The continuity mechanism

### 6.1 Cost of one placement at its own scale (paper, classical)

Standard normalisation `S = beta sum_p (1 - (1/2) Re tr U_p)` (SU(2)), `beta (1 - cos theta_p)` (U(1)).

| group | thin sheet, per fine plaquette | thick sheet of width `d` (fine units) | per placement at scale `d` (one block plaquette = `d^2` fine sheet units) |
|---|---|---|---|
| SU(2) | `2 beta` | flux `pi` spread over the `d x d` transverse plaquettes: `beta pi^2/(2 d^2)` per fine sheet unit | `beta pi^2/2 = 4.93 beta`, **independent of `d`** |
| U(1) | `2 beta` | the same, `beta pi^2/(2 d^2)` | `4.93 beta`, independent of `d` |
| 2I | `2 beta` | cannot spread: holonomy `-1` around a meridian needs plaquettes whose SU(2) angles add to `>= pi`; the cheapest non-trivial 2I element has angle 36 deg, cost `1 - cos 36 deg = 0.191`, so `>= 5 x 0.191 = 0.95 beta` per fine sheet unit | `>= 0.95 beta d^2`, **grows like the area** |

The SU(2) row is the classical scale invariance of 4D Yang-Mills (`A -> lambda A(lambda x)` leaves the action unchanged): continuity
makes the cost of a placement at its own scale **bounded**, where 2I's grows like `d^2`. The PREP reading "an SU(2) vortex gets cheaper
as it widens, about `beta pi^2/d^2`" is right per fine plaquette and needs this sharpening: per own-scale placement the classical cost
is flat, not falling. U(1) has the same flat classical cost.

### 6.2 What makes it small

At block scale `l` the relevant cost is the free energy of a centre flux through one block plaquette, roughly `4.93 beta_eff(l)` plus
fluctuation (entropic) corrections, against the threshold `log(6/5) = 0.18` (oscillation form) or `2 artanh(1/18) = 0.111` (Dobrushin
form). For SU(2), `beta_eff(l)` decreases with the block size (the coupling grows in the infrared; at `L sqrt(sigma) = 2.8` the torus
twist free energy is already about 0.06, c6b). For U(1) in the Coulomb phase `beta_eff` stays above `beta_c = 1.01`, so the cost stays
above 5 nats: never saturated (correct). For 2I the cost grows like `d^2`: never saturated at weak coupling (correct). **So continuity
separates SU(2) from 2I (bounded versus growing), and the running coupling separates SU(2) from U(1) (falling versus frozen).** Both are
needed; continuity alone does not give saturation.

### 6.3 The named SU(2) hypothesis, testable form

**H_sat(l)** (named, open). At block scale `l` (block side `l` cells of size `L_1`), for the blocked SU(2) Wilson measure written as
`U_b = s_b V_b` (centre sign `s_b`, SO(3) section `V_b`): the quenched centre Dobrushin constant

    c_Z(l) := sup over block links b of  sum over block links b' != b of
              sup over (V, s, outside) of  TV( law(s_b | V, s, outside), law(s_b | V, s with s_b' flipped, outside) )

satisfies `c_Z(l) < 1`. Plaquette-only approximation: `18 tanh(Jbar_P(l)) < 1`, i.e. **`Jbar_P(l) < 0.0556`**, where `Jbar_P(l)` is half
the worst-case log-odds change of one block centre variable when one block plaquette's centre sign is flipped (the worst-case
constrained flux free energy of one block plaquette is `2 Jbar_P < 0.111`).

How to test (GPU, constrained simulations; a pre-registration of its own): fix the block variables `(V, s)` outside one block link `b`
on sampled backgrounds plus the extreme ones (block-flat `V = 1`, random, twisted), sample the fine fields inside the two blocks adjacent
to `b`, and estimate the conditional log-odds of `s_b` and its change under `s_b'` flips. Predictions: SU(2) at `beta = 2.3 to 2.5`,
`Jbar_P(l)` decreasing in the physical block size, crossing 0.0556 at some `l L_1 sqrt(sigma)` (the claim); controls: 2I at large beta,
`Jbar_P` growing like `d^2`; U(1) at `beta = 1.1`, flat above the threshold. The lightweight version that the tie test of c8b already
measures is the box form: `gamma_Z(l) = sup over outsides of sum_u kappa_Z(u)/l^4`.

Where H_sat enters the Lean results: (i) `vortex_saturation` / `z2_background_saturation` with `E = 2 Jbar_P` if the blocked centre
law is of plaquette form (vortex free energy at the area rate); (ii) the `kappa_Z` half of `FineOneBoxSplit` via section 5.2 (paper).

## 7. Unit tests

| model | torus saturation | quenched centre (H_sat) | centre budget `gamma_Z` (ties) | adjoint budget `gamma_A` | one-box / gap | truth |
|---|---|---|---|---|---|---|
| photon (free, non-compact) | no central involution but `1` (`real_no_central_involution`); trivial twist: `P = 1/2` exactly in every phase (`ztw_trivial`, `flipP_trivial`): empty, correctly | no binary layer | none | fails: harmonic measure sums to one (c7c) | fails | gapless |
| compact U(1), Coulomb | silent (`not_window_weak`), `P -> p* < 1/2` (c6c) | fails: `4.93 beta_eff >= 5` per placement | — | fails (photon) | fails | gapless |
| Z2 confined | Lean (window); MC `beta = 0.30`: `P = 0.494` | holds for small `Jbar` | small | none (no adjoint layer) | holds at strong coupling | confined, gapped |
| Z2 deconfined | silent; MC `beta = 0.60`: `P = 3e-8` | fails | ties: `gamma_Z >= theta`, `theta ~ 1` (`tie_forces_budget`) | none | fails (c7c) | gapped, not confined |
| 2I, weak coupling | silent; `P = 1/160` at `beta = inf` (c6a) | fails: `>= 0.95 beta d^2` per placement | ties | A5 orders: fails | fails | topological |
| mixture of two confined phases | passes (`mixture_saturation`, same `B`) | — | small | fails: the phases differ in centre-even data | fails | massless mode |
| SU(2) x U(1), twist `(-1, 1)` | passes: `P` is SU(2)'s (`flipP_product`) | SU(2) part holds | small | **fails: the U(1) photon sits in the adjoint (quotient) layer, `gamma_A >= 1` at every `l`** | fails | gapless |
| SU(2), strong coupling | Lean (`su2_vortex_saturation`, `beta_std < 0.091`) | holds | small | small | holds (c7c anchor) | confined, gapped |
| SU(2), `beta = 2.3 to 2.5` | open (H_sat) | open, testable | open (c8b tie test) | evidence: 0.0036 / 1e-3 (annealed, fitted) | open | the claim |

Every row is a correct verdict: saturation holds exactly where the centre layer is disordered, and it never implies the gap by itself;
the two failures that keep a saturated centre layer (mixture, SU(2)xU(1)) fail through `gamma_A`, as they must.

## 8. Next step

1. **Measure H_sat** (section 6.3) with the 2I and U(1) controls; in parallel c8b's tie test measures `gamma_Z` directly. One positive
   reading at one block scale is what the centre half needs.
2. **Lean, reachable**: (a) the box version of `vortex_saturation` (frozen outside links, twists inside the box), making the uniformity
   over outsides formal; (b) the single-site Dobrushin bound for a Z2 gauge layer with background couplings and its Theorem A
   consequence (decay under every boundary condition and background: Chatterjee's Definition 2.3 for the binary layer); (c) the
   Dobrushin comparison `kappa_Z <= Lambda_fb c/(1 - c)`, which turns H_sat into the `kappa_Z` half of `FineOneBoxSplit`; (d) the `N^(d-2)`
   start count.
3. **The adjoint half**: the step from the certified fitted-action adjoint coefficient to a worst-case bound on the true conditional
   adjoint law (section 5.3); this, not saturation, is the remaining gap-strength input once H_sat holds.

## 9. Files and commands

* Lean: `formal/ProofPhase/Saturation/Sheet.lean` (sheet, move, cancel, pinning walks, count), `Vortex.lean` (the theorem),
  `EnergyEntropy.lean` (abstract Peierls and chessboard lemmas, threshold, area rate), `Tests.lean` (Wilson, Z2, SU(2), U(1), background
  field, unit tests), `Reduction.lean` (split, budgets, tie lemma, assembly).
* Build: `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8a-saturation/build.sh
  ProofPhase.Saturation.Reduction` (one-time `setup.sh`); single file: `check.sh <Module>`; axioms: `axioms.sh` -> `axioms.log`.
* Numerics: `py z2_exact_2d.py > z2_exact_2d.log`, `py z2_twist_4d.py > z2_twist_4d.log` (Windows Python with numpy; WSL has no numpy).

## 10. Not checked

Muenster, Tomboulis-Yaffe, Kramers-Wannier self-duality of 4D Z2, Dobrushin's comparison theorem, Chatterjee's Definition 2.3/Theorem
2.4 are recalled (the last as read in c7d). The section 6 costs are classical (minimum-action) estimates, not free energies. The box
version of the theorem (frozen outside) and section 5.2 are paper. N2 is one lattice size with a crude 11-point integration; it tests
the mechanism, not the constants.
