# The one proven blowup as a blueprint: the ledger form, the boundary, the bridge to Yang-Mills

Status: 2026-11-23. Answers the owner's direction recorded as the last entry of `docs/mass-gap/weak-coupling/PREP.md`
("Blowup blueprint: fit a proven, accepted blowup to DMP as a subset, and restate it as a consequence that ends in a DB"),
extended by the scope decision after it (Poincare as validation, section 6; Hodge and BSD mentioned only, section 10)
and by the owner's SU(N) reading (commit 1ebb988; section 7).
Builds on `UNIFIED.md` (the ledger), `ENCODER.md` (sections 1, 2, 6) and `GRH-LENS.md` (sections 1, 6, 7).

Files:
- Lean: `ProofPhase/Unified/Blowup.lean` (13 declarations, standard axioms only, no unproved steps; `blowup-axioms.sh`,
  `blowup-axioms.log`). A discrete skeleton of the rescaled-frame ledger. Nothing about Euler is proved in it.
- Third-layer check: `blowup_check.py`, `blowup_check.log` (CPU, under a second): the trapping threshold, the finite clock,
  and the size of the for-all in O1.

Status marks as in `ENCODER.md`: **[Lean]** (proved here, standard axioms), **[classical]** (standard mathematics,
recalled, not re-proved), **[external]** (a recent result proved elsewhere, recorded, not checked here), **[numerical]**
(checked by `blowup_check.py`), **[reading]** (an identification with DMP vocabulary, not a theorem), **[open]** (not
proved by anyone), **[fails]** (the requirement does not hold in this form). "Recalled" means from memory of the
literature, not re-checked in this round.

---

## 0. In plain words

**The blueprint.** Chen and Hou proved that the 3D axisymmetric Euler equations (and the 2D Boussinesq equations) develop a
singularity in finite time from smooth initial data, in a domain with a solid wall [external]. The proof is
computer-assisted: analysis plus rigorous numerics with certified error bounds. It is not machine-learning-assisted, and it
is not the Clay Navier-Stokes problem: no viscosity, a wall, axial symmetry.

**How the proof works, as a ledger.** Chen and Hou zoom in on the forming singularity at exactly the speed it forms. In
that zooming frame the blowup stands still: it becomes a fixed shape (the profile). The proof shows the solution stays near
that shape forever, in zoomed time. Three numbers do this:
- the **cost**: how strongly the zoomed equation pulls a perturbation back toward the shape (the damping);
- the **floor**: how far the computed shape is from an exact one (the residual), and how strongly the perturbation feeds on
  itself (the nonlinear constant);
- the **certificate**: damping above twice the geometric mean of residual and nonlinear constant. Then a small ball around
  the shape traps the solution forever. Below that threshold, the comparison recursion escapes. So the floor is a true floor
  [Lean].

**Why one scale is enough.** Euler looks the same at every scale. In the zooming frame every step of zoomed time is the same
step, so checking one step checks all of them. In the project's language the set of "outsides" has one element. That is
the whole reason a single, finite, computer-checked certificate covers infinite time.

**The boundary at the end.** Zoomed time runs forever, but each zoomed step takes a fixed fraction less real time than the
one before. The real durations add up to a finite time T*, while the amplitude grows without bound [Lean]. Each zoomed
step adds one fixed quantum to the Beale-Kato-Majda count (vorticity integrated over time). That count is infinite exactly
when smooth continuation fails [classical]. So the blowup is a consequence: the certificate forces infinitely many quanta
into finite time, and T* is the boundary where the smooth description ends. What crosses T* intact is the profile, the
shape. Whether an "act" happens at T*, a choice of how to continue, is a reading. Its mathematical counterpart, whether weak
continuations past T* are unique, is open for this solution.

**What generalizes.** Structural:
- a scaling symmetry that makes the zoomed equation the same at every step;
- an approximate profile;
- a certified damping above the floor;
- a focusing sign (the zoom speeds up).

Specific: the wall (it holds the singular point in place and allows smooth data), axial symmetry, and the particular
weighted norms. For Navier-Stokes the viscosity becomes a floor that changes with the scale. It grows without bound unless
the profile shrinks slower than the square root of the remaining time. That leaves a narrow window, between the energy
scaling and the viscous scaling, where a profile would have to live. Tao's averaged Navier-Stokes shows that the energy
identity alone cannot price a single step: it keeps the energy ledger and still blows up [classical].

**The bridge to Yang-Mills: no, with a precise reason.** Chen and Hou never certify a for-all by sampling. Each of their
for-alls is either free (time, by scale invariance), low-dimensional (space points, two variables, covered by interval
arithmetic), or linear around one reference shape (perturbations, handled by an operator bound). O1 asks for the twist
ratio `Z_tw/Z >= c0 > 0.743` at the hand-over box for **every outside**. Its for-all fits none of the three:
- it is not free, because Yang-Mills is not scale invariant at the hand-over box: the coupling runs there;
- it is not low-dimensional: at least 387 dimensions even for a box of side 2 [numerical];
- it is not linear around a reference: in the confining regime the outsides are disordered, far from any reference.

The deterministic quantity that would have to be enclosed is named in section 4.3. Interval arithmetic could serve the
refuting side (a certified bad outside at one box), not the certifying side. The template does say what is missing: a
reduction of "every outside" to one worst outside plus a contracting remainder. That is the open worst-case argument of
`c9b-adjoint/REDESIGN.md` section 8.

**Validation against Poincare (section 6).** Perelman's Ricci flow with surgery is a solved proof with the same outline:
- singularities are forced in finite time;
- a scale-invariant monotone quantity (the W-entropy) makes one estimate hold at every scale;
- at each singular time the high-curvature part is cut out (surgery), and the flow continues;
- finite extinction, the last boundary, certifies that a simply connected manifold is the sphere.

The restatement fits the structure, and the act at the boundary is even defined there. It does not fit the mechanism. What
reaches Perelman's boundaries is decided by classifying all possible blowup shapes, not by a cost above a floor. Nothing
new is claimed.

**Poincare and SU(N) (section 7).**
- SU(2) is the 3-sphere, so Perelman's certified object is the SU(2) gauge group manifold [classical; Lean as sets].
- Every SU(N) with its symmetric (bi-invariant) metric shrinks uniformly under Ricci flow and vanishes at time `1/N`, with
  no surgery (in the normalisation `<X, Y> = -tr(XY)`, Einstein constant `N/2`) [classical, Lean for the ODE, numerical].
  That is Perelman's final event, delivered by symmetry. But it holds for every positive Einstein space, so it says
  nothing about the topology of SU(N).
- Only SU(2) is stable. Every SU(N) with `N >= 3` is an unstable shrinker (Cao-He) [external; Lean for the inequality].
- A real "Poincare for SU(N)" (homotopy SU(N) implies SU(N)) is a surgery-theory question. I found no theorem for it,
  it may be false in the smooth category, and Ricci flow does not reach it [open].

---

## 1. The blueprint, and what it is not

**The result** [external]. J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
equations with smooth data", I: Analysis (arXiv 2210.07191), II: Rigorous Numerics (arXiv 2305.05660). Both were revised
on arXiv in August 2026 (v4 and v3). A summary appeared in PNAS in 2025 ("Singularity formation in 3D Euler equations with
smooth initial data and boundary").
- **Statement.** For 2D Boussinesq and 3D axisymmetric Euler, with smooth, finite-energy initial data and a solid boundary,
  the solution blows up in finite time. The blowup is stable (an open set of data) and nearly self-similar (the solution
  stays close to an approximate self-similar profile). The scenario is the one Luo and Hou found numerically in 2014: the
  singularity forms on the wall.
- **Method, Part I.** Nonlinear stability of the approximate profile in a dynamically rescaled formulation. The estimates
  are weighted `L^infinity` and weighted `C^{1/2}` estimates. The abstract notes that weighted `L^2` or `H^k` estimates fail
  here, because advection normal to the wall produces a large growth factor.
- **Method, Part II.** Computer assistance:
  - approximate space-time solutions built with rigorous error control (these handle a finite-rank part of the
    linearised operator);
  - the regular part of the velocity estimated by numerical integration with computer assistance.

  Together they verify that the constants of Part I satisfy the inequalities of the stability lemma.
- **Status of the claim.** Nearly self-similar: the abstract claims stability of an approximate profile, not convergence
  to an exact one.

**What it is not.**
- Not machine-learning-assisted. The numerics are classical, made rigorous.
- Not Navier-Stokes. There is no viscosity.
- Not boundary-free. The wall is essential to the scenario.
- Not the Clay problem, which asks about 3D incompressible Navier-Stokes on `R^3` or the torus, without a wall.

**Neighbours** (recalled, not re-checked):
- Elgindi (2021) proved finite-time blowup for 3D axisymmetric Euler without swirl and without a boundary, but only for
  `C^{1,alpha}` data, not smooth data. That proof is analytic, with no computer.
- Chen and Hou (2021) proved `C^{1,alpha}` blowup with a boundary.
- Chen, Hou and Huang proved asymptotically self-similar blowup for the 1D Hou-Luo model of the wall scenario. That paper
  is a precursor, not an extension: it shows convergence to an exact profile, in a one-dimensional model.

**The AI-found unstable profiles** [external]. Y. Wang and 21 co-authors, including T. Buckmaster, J. Gomez-Serrano and
C.-Y. Lai, "Discovery of Unstable Singularities", arXiv 2509.14185 (v1, September 2025, still the only version on
2026-11-23).
- They found families of unstable self-similar profiles numerically, with physics-informed neural networks and a
  high-precision Gauss-Newton refinement. The equations are the Cordoba-Cordoba-Fontelos model, the incompressible porous
  media equation, and Boussinesq (equivalently 3D Euler with a wall).
- The abstract claims accuracy near double precision, "meeting the requirements" for future computer-assisted proofs. It
  does not claim a proof.
- In this round's searches (2026-11-23) I found no proof of these unstable profiles. I found one 2026 talk by Gomez-Serrano
  outlining the intended programme: a precise approximate profile, the linearised operator reduced to a finite matrix plus a
  controlled tail, a computer-assisted middle step, and a topological argument for the unstable directions.
- So the status recorded in PREP.md ("not proved as of January 2026") still stands as far as checked. The searches were not
  exhaustive.

---

## 2. Question 1: the ledger form of the proof

**2.1 The rescaled frame** [external, schematic]. Write the solution in variables that zoom at the rate of the
singularity:

    omega(x, t) = C_omega(tau)^{-1} W(x / C_l(tau), tau),    dt/dtau = C_omega(tau),
    C_omega(tau) = exp( integral_0^tau c_omega ),            C_l(tau) = exp( -integral_0^tau c_l ).

The scaling rates `c_omega(tau)` and `c_l(tau)` are fixed by normalisation conditions on `W`. The rescaled equation for `W`
(and for the density or swirl in the Boussinesq form) does not contain `tau` explicitly. Euler is invariant under
`x -> lambda x`, `t -> mu t`, `u -> (lambda/mu) u`, so after the rescaling the equation is **autonomous**. A blowup
becomes a steady state `(W_bar, c_l_bar, c_omega_bar)` with `c_omega_bar < 0`. The exact normalisations and the weighted
norms are in the papers. Only the shape matters here.

**2.2 The ledger** [external for the inequalities, Lean for the skeleton, reading for the names]. Write `E(tau)` for the
weighted norm of the perturbation `W - W_bar` (Chen-Hou combine weighted `L^infinity` and `C^{1/2}` pieces into one
functional). The stability analysis gives an inequality of the shape

    dE/dtau <= -lambda E + C E^2 + eps .

| ledger | in Chen-Hou | here |
|---|---|---|
| **steps** | unit intervals of rescaled time `tau` | `M i`, `i = 0, 1, ...` |
| **carried** | the weighted norm `E` of the perturbation from the profile | `M i >= 0` |
| **cost** | the damping `lambda` of the linearised rescaled operator in the weighted norm, after the finite-rank part is split off and handled by rigorous space-time numerics | `q = e^{-lambda}`, cost `1 - q` |
| **floor** | the residual `eps` of the approximate profile (how far it is from solving the steady equation), and the nonlinear constant `C` | `r`, `C`; floor `2 sqrt(C r)` |
| **one-scale certificate** | `lambda^2 > 4 C eps` (in the discrete form `(1 - q)^2 >= 4 C r`) and a focusing margin `c_omega_bar + K R < 0`, checked once by analysis plus rigorous numerics | `trap_of_gap`, `blowup_of_certificate` |

One step obeys `M (i+1) <= q M i + C (M i)^2 + r`. Then:
- **Trapping** (`trap`, `trap_radius`, `trap_of_gap`) [Lean]. If `(1 - q)^2 >= 4 C r` and `M 0 <= R = (1 - q)/(2C)`, then
  `M n <= R` for every `n`. In continuous time the same computation is `lambda E* >= C E*^2 + eps`, solvable exactly when
  `lambda^2 >= 4 C eps`.
- **The floor is a true floor** (`escape_of_below`, `escape_pos`) [Lean]. For the comparison recursion with equality and
  `(1 - q)^2 < 4 C r`, every step adds at least `r - (1 - q)^2/(4C) > 0`. The perturbation grows linearly and no ball traps
  it. `blowup_check.log` part 1 [numerical]: at `q = e^{-0.5}`, `C = 1`, the recursion stays bounded at 0.99 of the
  threshold residual and escapes at 1.01 of it, after 85 steps.

**2.3 As `CostAboveFloor`** (`gap_of_costAboveFloor`) [Lean].

    CostAboveFloor (fun _ : Unit => 1 - q) (2 sqrt(C r))   implies   (1 - q)^2 >= 4 C r .

The index set is `Unit`: one step type. In `UNIFIED.md` the open hypotheses are `CostAboveFloor` over a set of outsides
(Yang-Mills) or of refutations (NP vs coNP). Here the set has one element, because the rescaled equation is autonomous.

**2.4 Why one scale suffices for all time** [classical for the symmetry, reading for the ledger name]. Scale invariance
makes the rescaled equation autonomous. The linearised operator, the nonlinear constant and the residual are therefore the
same at every `tau`. A for-all over steps, the "arrow of causality" row of `UNIFIED.md` section 6, costs nothing. The only
for-alls left are:
- over spatial points: pointwise inequalities on functions of two variables, covered by interval arithmetic on cells plus
  explicit far-field asymptotics;
- over perturbations in the ball: handled by one linear operator bound plus the quadratic nonlinear bound.

Neither is handled by sampling. This is the project's "hand-over point" (`UNIFIED.md` section 6): one finite check with a
strict margin certifies the infinite chain. Here the margin is `1 - q - 2 sqrt(C r) > 0`.

**2.5 Which reading** [Lean for each, reading for the choice]. Two quantities are carried, with two readings:
- **The perturbation: decay reading with a floor** (affine, not purely multiplicative, because the residual is additive).
  It is trapped, not driven to zero. The reading's content is that the **profile survives**: its shape stays within `R`
  forever.
- **The clock: decay reading, floor 0.** The physical duration of step `i` is `d i`, with `d (i+1) = e^{a i} d i` and
  `a i <= c_omega_bar + K M i <= -gamma < 0` (`durations_pay`). By `summable_of_gap` the durations are summable
  (`arrival`): infinitely many rescaled steps fit in finite physical time `T* = sum d i <= 1/(1 - e^{-gamma})`.
  `blowup_check.log` part 2 [numerical] shows the sum at `gamma = 0.7` meeting this bound.
- **The amplitude: the size reading run forward.** `1/d n >= e^{gamma n}`, tending to infinity (`amplitude_unbounded`).

So the right short answer is: **cost above floor in the decay reading, applied to the perturbation, certifies survival of
the profile; the same ledger applied to the clock gives a finite time.**

The mass gap uses the same line of `Ledger.lean`, `summable_of_gap`:
- in Yang-Mills, the summable quantity is the correlation over infinitely many boxes, and the consequence is a finite
  correlation length;
- here it is the duration over infinitely many rescaled steps, and the consequence is a finite blowup time.

One theorem, two carried quantities [Lean for both uses; reading for the parallel].

**2.6 What does not fit the encoder.** The encoder of `ENCODER.md` has linear steps with factor `<= 1` set by a reflection
coefficient. The blowup ledger has an additive residual and a quadratic term, so its step is affine-quadratic, and its
threshold `lambda > 2 sqrt(C eps)` is not an encoder factor. `Blowup.lean` adds this form (`trap`). The step factors that
do occur (`q`, `e^{a i}`) are plain ledger factors with floor 0 [reading].

---

## 3. Question 2: the blowup as a consequence that ends at a boundary

**3.1 The restatement** (`blowup_of_certificate`, `boundary_quantum`) [Lean for the skeleton; external for the PDE
inputs].

> **Given** the one-scale certificate in the rescaled frame (damping above the floor, `(1 - q)^2 >= 4 C r`; a start in
> the ball; focusing with margin, `c_omega_bar + K R <= -gamma < 0`),
> **then** the perturbation stays in the ball forever, the physical durations add up to a finite `T*`, the amplitude is
> unbounded, and every rescaled step adds one fixed quantum to the Beale-Kato-Majda count.
> **So** the smooth solution's domain of existence is a finite interval `[0, T*)`, and `T*` is its boundary.

The blowup is not assumed or constructed directly. It follows from a certificate at one scale, and it ends at a boundary.

**3.2 The identifications.** Each identification is a [reading]; the right-hand column is its exact mathematical
counterpart.

| owner's term | exact counterpart | status of the counterpart |
|---|---|---|
| **the boundary (DB)** | `T* = sup` of the maximal interval of smooth existence; in rescaled variables `T* = t(tau = infinity) = integral_0^infinity C_omega(tau) dtau` | [Lean] skeleton (`arrival`); [external] for Euler |
| **what is carried to the boundary** | the profile: `W(tau)` stays within `R` of `W_bar` for all `tau`, so near the singular point `omega(x, t)` is `C_omega^{-1} W_bar(x / C_l)` up to an error of relative size `R`. Shape is carried; amplitude (`C_omega^{-1}`, up) and scale (`C_l`, down) are the two running clocks | [external] (Chen-Hou); [Lean] for the trap |
| **what certifies it** | the one-scale certificate: `lambda`, `C`, `eps` with `lambda^2 > 4 C eps`, and the focusing margin; checked by weighted estimates (Part I) and rigorous numerics (Part II) | [external] |
| **what crosses the boundary** | the profile, as the asymptotic shape: the solution tends to the shape in the rescaled frame, while its physical amplitude diverges | [external] |
| **the event at the boundary** | the Beale-Kato-Majda count: `integral_0^T sup abs(omega) dt` is finite for `T < T*` and infinite at `T*`. Changing variables (`dt = C_omega dtau`, `sup abs(omega) = sup abs(W)/C_omega`) gives `integral sup abs(W) dtau`: each unit of rescaled time adds at least `sup abs(W_bar) - (error)`, one quantum per step. Infinitely many steps fit before `T*` | [classical] BKM (in domains with a boundary: Ferrari 1993, recalled); [Lean] for the count (`boundary_quantum`: per step, amplitude times duration is one) |
| **"an act can happen for it to exist"** | past `T*` the equation no longer selects the solution. Weak solutions of Euler are non-unique in general (De Lellis and Szekelyhidi; Isett's proof of the Onsager conjecture) [classical]. Whether this blowup solution has weak continuations past `T*`, and how many, is not addressed by Chen-Hou | [open] |

**3.3 The finite and the infinite.** In the project's ledger the hand-over point carries a finite check to an infinite chain
(`UNIFIED.md` section 6). The blowup runs the same hand-over in reverse:
- an infinite chain of rescaled steps is packed into finite physical time;
- the finite check at one scale (the certificate) is what makes the packing geometric.

The boundary `T*` is where the infinite chain ends in finite time [reading].

**3.4 In the DMP table of `UNIFIED.md` section 6** (all [reading]):

| DMP | blowup |
|---|---|
| pressing / the ODP | the rescaled steps, one unit of `tau` at a time |
| the coupling (lossiness) | the damping `lambda` |
| the tick | the floor `2 sqrt(C eps)` |
| the quantum of assertion | one Beale-Kato-Majda quantum per step (`boundary_quantum`) |
| the arrow of causality | autonomy of the rescaled equation (scale invariance): the same step at every `tau` |
| the hand-over point | the one-scale certificate |
| minting | the end of smooth existence at `T*` |
| the DB | `T*` |
| the open step | none for this case: Chen-Hou close it, because the outside set has one element |

---

## 4. Question 3: what generalizes

**4.1 Structural and specific.**

| part | structural or specific | why |
|---|---|---|
| a rescaled frame in which the equation is autonomous | **structural** | needs a scaling symmetry; it makes the outside set one element (2.4) |
| an approximate profile with small residual | **structural** | the reference object that the for-all over perturbations is linearised around |
| certified damping above the floor, `lambda > 2 sqrt(C eps)` | **structural** | the certificate; `trap_of_gap`, sharp by `escape_of_below` |
| a focusing sign with margin, `c_omega_bar + K R < 0` | **structural** | turns the trapped profile into a finite clock (`arrival`) |
| a continuation criterion (BKM type) | **structural** | identifies the end of the clock with the end of smooth existence |
| stability of the profile (an open set of data) | **structural for the method, specific for the case** | unstable profiles (arXiv 2509.14185) need, in addition, a fixed-point or topological argument on the unstable directions; not done (1) |
| the solid boundary | **specific** | the singularity sits on the wall; the wall supplies the symmetry and the stagnation-point flow that hold it in place, and allows smooth data (without a wall, Elgindi's blowup needs `C^{1,alpha}` data) |
| axial symmetry | **specific** | reduces 3D Euler to a 2D system (the Boussinesq analogy) where rigorous numerics are feasible |
| weighted `L^infinity` and `C^{1/2}` norms | **specific** | `L^2`-based norms fail for this profile (normal advection) |
| the finite-rank splitting computed by rigorous space-time numerics | **specific technique**, general idea | "finite part enclosed, tail estimated" |

**4.2 Navier-Stokes without a boundary** [classical for the scaling computation; reading for the ledger names; open for
everything else].

Suppose a profile shrinks like `l(t) = (T* - t)^alpha`, with velocity of size `l/(T* - t)`.
- **Viscosity as a floor.** In the rescaled frame the viscous term carries the coefficient `nu (T* - t)^{1 - 2 alpha}`.
  This is a floor that changes with the scale.
  - **`alpha > 1/2`:** the floor grows without bound, exponentially in rescaled time. No uniform cost can pay it, and
    viscosity destroys the profile.
  - **`alpha = 1/2`** (Leray scaling): the floor is constant. Self-similar Leray profiles are excluded: Necas, Ruzicka
    and Sverak (1996) for `L^3`, Tsai (1998) for finite local energy [classical].
  - **`alpha < 1/2`:** the floor decays, summably in rescaled time. The ledger tolerates such a floor.
- **The energy constraint.** The local energy near the singular point scales like `(T* - t)^{5 alpha - 2}`, so finite
  energy needs `alpha >= 2/5`. The `L^3` norm scales like `(T* - t)^{2 alpha - 1}`, and it must blow up
  (Escauriaza-Seregin-Sverak 2003) [classical]. That is consistent with `alpha < 1/2`.
- **So the Navier-Stokes analogue of Chen-Hou needs** a stable profile of the inviscid (Euler-type) rescaled equation with
  `2/5 <= alpha < 1/2`, on `R^3` or the torus without a wall, certified with damping above a floor that now includes a
  summable viscous term. The window `[2/5, 1/2)` is the supercritical gap between the energy scaling and the viscous
  scaling, in ledger form. No such profile is known; smooth-data blowup for 3D Euler without a boundary is itself open, as
  far as recalled [open].
- **For regularity**, the open step would be the reverse: a per-scale cost (the dissipated share per dyadic step) above
  the transfer floor, uniformly. That is the "cost above floor, uniformly" shape of the project's three open steps
  [reading].

**4.3 Why Tao's averaged Navier-Stokes shows the energy ledger is not enough** [classical: T. Tao, J. Amer. Math. Soc.
29 (2016)].
- Tao replaces the Navier-Stokes nonlinearity by an average of rotated and dilated copies. The average keeps:
  - the energy identity (the nonlinearity does no work);
  - the standard harmonic-analysis bounds.
- He then builds a cascade in which energy moves from one dyadic scale to the next in a controlled, delayed way. Each
  stage loses only a small share to dissipation, and each takes a geometrically shorter time. The solution blows up in
  finite time.
- In ledger terms:
  - The energy identity is **one global sum**: total dissipation at most the initial energy. It constrains the sum of the
    costs, not any single step.
  - Tao's cascade satisfies the global sum and runs the blowup ledger of section 2 step by step: the carried energy
    survives at each stage (survival reading), and the stage durations are summable (decay reading on the clock).
- So no argument that uses only the energy identity and those bounds can produce a per-step cost above the floor. A proof
  of regularity must price individual steps with the true Euler-Navier-Stokes structure, which the averaging destroys.
  This is the same kind of barrier as relativization for NP vs coNP: a model that keeps the used ingredients and violates
  the conclusion [reading for the parallel].

---

## 5. Question 4: the bridge back to Yang-Mills

**5.1 How Chen-Hou discharge their for-alls.** Every for-all in the proof is handled deterministically, and each is one of
three kinds:

| for-all over | how it is discharged | kind |
|---|---|---|
| time steps `tau` | free: the rescaled equation is autonomous | scale invariance |
| spatial points (two variables, half-plane or cylinder section) | interval arithmetic on finitely many cells plus explicit far-field asymptotics | low-dimensional exhaustion |
| perturbations in the trapping ball (infinite-dimensional) | one linear operator estimate (damping in a weighted norm, with a finite-rank part computed by rigorous space-time numerics) plus the quadratic nonlinear bound | linear around one reference |

The only infinite-dimensional for-all is over a small ball around **one** reference object. There it is linear up to a
quadratic remainder, so it reduces to one operator bound.

**5.2 O1's for-alls.** O1 (`ENCODER.md` section 6, `ymOneBox_iff_refl`, Lean) asks for `Z_tw/Z >= c0 > (mu - 1)/(mu + 1)`
(0.743 for `mu_4 = 6.77`) at the hand-over box, for every outside, at every lattice spacing, with the box fixed in
physical size. Per box, by the Markov property, the quenched outside enters only through the boundary links. That gives
three for-alls:
- (a) over boundary configurations `omega`;
- (b) the evaluation of `Z(omega)` and `Z_tw(omega)`, which are integrals over the interior links;
- (c) over lattice spacings: `beta -> infinity` with the box side `L(beta)` lattice units at fixed physical size.

**5.3 The quantity that would have to be deterministic and enclosed.** For the SU(2) Wilson action at coupling `beta` on a
box of side `L` lattice units:

    c_*(L, beta) = inf over boundary configurations omega of  Z_tw(omega) / Z(omega).

- **It is deterministic.** It is a ratio of finite-dimensional integrals, with the infimum taken over a compact set,
  `SU(2)^{boundary links}`. So it is a quantity interval arithmetic may legitimately enclose. That is different from a
  Monte Carlo estimate, which per `REDESIGN.md` section 8 can refute a for-all but never certify one.
- **O1 in these terms** is `c_*(L(beta), beta) >= c0 > (mu - 1)/(mu + 1)` for all `beta >= beta_0` [reading of
  `YMOneBox` for the Wilson box; the identification of the box's outsides with boundary links is the Markov property,
  classical].
- **An enclosure would need three things:**
  - (i) rigorous enclosures of `Z` and `Z_tw` for given `omega`;
  - (ii) a rigorous infimum over `omega`, by branch and bound with Lipschitz bounds;
  - (iii) uniformity in `beta`.

**5.4 Why the Chen-Hou template does not certify O1.**
1. **No scale invariance at the hand-over box** [classical]. Chen-Hou get "one scale for all time" from an exact symmetry.
   - Lattice Yang-Mills has none at the hand-over box: the coupling runs. The hand-over box is exactly where the theory
     leaves the asymptotically free, nearly scale-invariant regime and the mass scale appears.
   - In renormalisation-group terms, the fixed points are the Gaussian one in the ultraviolet (Balaban's analytic control)
     and the strong-coupling one at `beta = 0` (Haar measure, `c = 1`, the twist free).
   - The hand-over is a crossover between them, not a fixed point. A Chen-Hou-type argument certifies a neighbourhood of a
     fixed point. O1 is a statement about the trajectory that connects the two.
   - So for-all (c) is not free [fails].
2. **No linear structure for the for-all over outsides.** Chen-Hou's infinite-dimensional for-all is a small ball around
   one profile. O1 needs the confining side (`c -> 1`, the twist nearly free, `GRH-LENS.md` 6.3). There the outsides are
   disordered and lie far from any reference configuration, so linearisation around a reference does not cover them.
   For-all (a) would need exhaustion [fails].
3. **Exhaustion is out of reach in dimension.** `blowup_check.log` part 3 [numerical] counts the dimensions after gauge
   fixing, for a box of side `n` lattice units:

   | `n` | outside dimension | interior integral dimension |
   |---|---|---|
   | 2 | 387 | 21 |
   | 3 | 1299 | 240 |
   | 4 | 3075 | 1053 |

   Branch and bound at an optimistic 10 cells per direction needs `10^387` cells already at `n = 2`. Chen-Hou's exhaustion
   is over two spatial variables [fails].
4. **The analytic tail exists only where the answer is known.** At strong coupling the character expansion is exactly
   "finite part enclosed, tail estimated", and it gives twist-ratio bounds with explicit tails [classical, Osterwalder-
   Seiler]. But it converges only for small `beta`, where the gap is already proved. It does not reach the hand-over box.

**Verdict: no.**
- The Chen-Hou template certifies a for-all when the for-all reduces to one reference object plus a linear or contracting
  remainder, at one scale fixed by a symmetry.
- O1 has neither the symmetry (the coupling runs) nor the reference object (the outsides are disordered).
- The deterministic quantity `c_*(L, beta)` is well defined, and could be enclosed in principle. But only by exhaustion
  over at least 387 dimensions for the smallest box, and then only at one `beta`.
- Nothing in this round moves O1 [open].

**5.5 What the template does offer.**
- **The missing piece, named.** What would play the role of Chen-Hou's linearisation is a **worst-case reduction**: a
  theorem that some explicit outside (or a small explicit family) is worst for `Z_tw/Z`. Then the for-all becomes one
  number, `Z_tw/Z` at the worst outside, and that is enclosable.
  - For abelian (`Z_2`) lattice gauge theory, correlation inequalities (Griffiths-Kelly-Sherman) do this kind of
    reduction [classical].
  - For SU(2) none is known. This is the same open item as `REDESIGN.md` section 8 ("the worst-case argument is open").
  - The template sharpens the request: a worst-case theorem plus an enclosure at the worst outside would certify O1 at
    that `beta` [reading]. Uniformity in `beta` would still be separate [open].
- **Certified refutation.** Interval arithmetic can make the refuting side a theorem. For one explicit outside at a small
  box and fixed `beta`, an enclosure of `Z_tw/Z` below 0.743 is a rigorous counterexample to O1 at that box. That is
  stronger than a Monte Carlo refutation, which carries statistical error. For `n = 2` the integral is 21-dimensional,
  plausibly in reach with a truncated character expansion and a rigorous tail [reading; not attempted].
- **The closest existing attempt** [external, contested]. Tomboulis (arXiv 0707.2179, 2007) claimed confinement for all
  couplings in 4D SU(2) by bounding exactly this kind of twist ratio (the vortex free energy) through decimation steps.
  - Ito and Seiler (arXiv 0711.4930, 0803.3019) identified gaps in it.
  - Tomboulis replied (arXiv 0712.2620).
  - The argument is not accepted as a proof.

  It is the nearest thing in the literature to an RG-transported twist-ratio bound, and is reading material for O1, not a
  result.

---

## 6. Validation: Poincare (Perelman's Ricci flow with surgery)

Purpose: check the restatement of section 3 against a solved, accepted proof in which finite-time singularities occur, are
classified, and are cut at a boundary, after which the flow continues. **This section claims nothing new.** Everything in
it is [classical] (recalled from Perelman's three papers, arXiv math/0211159, math/0303109, math/0307245, and the
expositions of Kleiner-Lott, Morgan-Tian and Cao-Zhu; not re-checked this round), except the identifications, which are
[reading].

**6.1 The setting.** Ricci flow `dg/dt = -2 Ric(g)` on a closed 3-manifold (Hamilton 1982). It develops singularities in
finite time, and in one case the time is forced by an ODE certificate:
- on any closed 3-manifold, `dR/dt = Delta R + 2 abs(Ric)^2 >= Delta R + (2/3) R^2`;
- so by the maximum principle `R_min(t) >= 1/(1/R_min(0) - 2t/3)`;
- with positive scalar curvature this forces a singularity by `T <= 3/(2 R_min(0))`.

This is the same kind of conclusion as section 2.5's clock: a one-line comparison forces the end of smooth existence in
finite time.

**6.2 The ledger form.**

| ledger | Perelman | fit |
|---|---|---|
| **steps** | the smooth flow on the intervals between surgery times | yes: the chain of steps, each ending at a boundary |
| **monotone quantity** | the W-entropy `mu(g, tau)`, nondecreasing; its derivative is `2 tau integral abs(Ric + Hess f - g/(2 tau))^2 u dV >= 0`, a sum of squares that vanishes exactly on shrinking solitons. Perelman's reduced volume is nonincreasing in the same way | **partly**: `accrue` with nonnegative increments and floor 0, but **no uniform positive cost**. The increment measures the departure from self-similarity, and its role is not decay |
| **what the monotone quantity buys** | kappa-noncollapsing: a lower bound on volume ratios at every scale below `sqrt T`. The entropy is scale invariant, so one estimate holds at all scales | **yes**: this is section 2.4's "one scale suffices", from a scale-invariant quantity instead of a scale-invariant equation |
| **number of steps on `[0, T]`** | each surgery removes at least a definite volume `v(h, delta) > 0`, and the volume stays bounded on `[0, T]` (it grows at most at a controlled rate, from the lower bound on `R`). So surgery times do not accumulate: finitely many on every finite interval | **yes**: the size reading of `UNIFIED.md` (a quantum per step, a bounded budget), with volume as the budget |
| **the blowup analysis** | rescale at points of large curvature. The limits are kappa-solutions: ancient, kappa-noncollapsed, with bounded nonnegative curvature. In 3D they are classified: round shrinking spheres and their quotients, round cylinders `S^2 x R` and their `Z_2` quotients, and caps. The canonical neighbourhood theorem says every point of large enough curvature has a neighbourhood close, after rescaling, to an epsilon-neck, an epsilon-cap, or a closed positively curved component | **partly**: what reaches the boundary is classified, as in section 3.2 ("what is carried"). But the classification is a finite catalogue of models, not the stability of one profile with a certified damping |
| **the boundary (DB)** | a singular time `T_i`: the flow converges smoothly where the curvature stays bounded, and the high-curvature region is covered by canonical neighbourhoods | **yes** |
| **the act at the boundary** | surgery: cut along epsilon-necks deep in the horns at a small scale `h`, glue in standard caps, discard the components covered by canonical neighbourhoods, and restart the flow | **yes, and stronger than section 3.2**: here the act is defined, see 6.3 |
| **the end** | finite extinction for simply connected manifolds: after finitely many surgeries every component has disappeared (6.4) | **yes**: the last boundary, where the certificate is read |

**6.3 Why surgery is a well-defined act.**
- **What is cut is known.** By the canonical neighbourhood theorem the cut runs through a nearly round `S^2` in a neck. So
  each surgery is topologically a connected-sum decomposition, plus discarding pieces of known type: spherical space
  forms, `S^2 x S^1`, `RP^3 # RP^3`.
- **The flow can continue.** The surgery parameters (the neck quality `delta` and the scale `h`) are chosen so that
  kappa-noncollapsing and the canonical neighbourhood property hold again after surgery. That is the hard part of
  Perelman's second paper.
- **The act involves choices, but the outcome is determined.** The cut locations and the parameters are choices. The
  topological outcome does not depend on them.
- **Later, the act became canonical** [classical, recalled]. Kleiner and Lott constructed singular Ricci flows through
  the singularities without choices. Bamler and Kleiner (arXiv 1709.04122) proved these are unique and stable. So for
  Ricci flow in 3D, "past the boundary, the equation selects the continuation" is a theorem.
- **The contrast with Euler** is exact: in section 3.2 the same question is open for the Chen-Hou solution.

**6.4 Finite extinction as the certificate.**
- **The theorem.** For a closed, simply connected 3-manifold, the Ricci flow with surgery becomes extinct in finite time:
  Perelman (math/0307245), and independently Colding and Minicozzi (2005).
  - Both use a min-max quantity: Perelman the area of minimal disks and 2-spheres; Colding-Minicozzi the width, the
    min-max area of sweepouts.
  - It decreases at a uniform rate: an inequality of the form `dW/dt <= -4 pi + (3/(4t + C)) W`, so `W` would become
    negative in finite time.
  - In ledger terms this is cost above floor in the additive form (`accrue` read downward): a uniform cost `4 pi` per unit
    time, above a floor that shrinks relative to it [reading].
- **Why extinction certifies the sphere.**
  - Run the surgeries backwards. `M` is a connected sum of the discarded pieces: spherical space forms and copies of
    `S^2 x S^1`.
  - If `M` is simply connected, every piece is simply connected.
  - So `M` is a connected sum of `S^3`s, which is `S^3`.
  - The certificate is read at the final boundary.
- **One line on primes** [reading]: by Kneser-Milnor, every closed orientable 3-manifold is uniquely a connected sum of
  prime 3-manifolds, with `S^3` as the unit. The surgeries realise this decomposition, an echo of the owner's "primes as the
  base" reading.

**6.5 Verdict: the restatement matches partly, at the level of structure, not mechanism.**

Where it fits:
- **Blowup as a consequence.** The singular time is forced: by the `R^2` comparison (6.1), and globally by extinction
  (6.4).
- **One estimate at all scales.** It comes from a scale-invariant quantity: the W-entropy, giving kappa-noncollapsing.
  This matches Chen-Hou's autonomous rescaled frame (2.4).
- **A boundary where an act happens.** Surgery is a defined act. The theory continues past it, and since Bamler-Kleiner
  it does so canonically. This is the clearest instance of the owner's "ending in a DB, where an act can happen".
- **A ledger with a quantum per step.** Volume per surgery gives finitely many acts on finite time intervals: the size
  reading.
- **A final boundary that carries the certificate.** Extinction gives the sphere.

Where it does not fit:
- **One profile against a catalogue.** Chen-Hou carry one profile to `T*`, certified by a damping above a floor (sections
  2.2, 2.3). Perelman classifies all possible blowup limits (kappa-solutions, canonical neighbourhoods) by compactness and
  rigidity, with no certified damping and no `CostAboveFloor` at the boundary.
- **No positive cost in the monotone quantity.** The W-entropy has cost at least 0 and floor 0. It buys a sign
  (noncollapsing), not a rate. The uniform positive cost appears only in the extinction argument (the `4 pi` per unit
  time).
- **Many boundaries against one.** Ricci flow with surgery passes a sequence of boundaries and continues. Chen-Hou's `T*`
  is terminal, and what lies beyond it is open.
- **Who acts.** In Perelman the act is performed by the construction: a choice of the prover, later made canonical. In
  section 3.2 the act would be the equation's failure to select.

So the restatement passes the check as a description: every element of section 3 has an exact counterpart in Perelman's
proof, and the proof goes further at the boundary. It does not pass as a mechanism: the step that decides what reaches the
boundary is a classification, not a cost above a floor.

---

## 7. Poincare and SU(N)

Answers the owner's reading recorded in `PREP.md` (entry of commit 1ebb988): extend Perelman's Poincare to every SU(N)
through DMP. **Nothing new about Poincare or geometrization is claimed.** The goal is a clear line between what extends
trivially, by symmetry, and what does not.

Files:
- Lean: `ProofPhase/Unified/BlowupSUN.lean` (17 declarations, standard axioms only, no unproved steps;
  `blowupsun-axioms.sh`, `blowupsun-axioms.log`).
- Third-layer check: `blowup_sun_check.py`, `blowup_sun_check.log` (CPU, seconds; N = 2, 3, 5, 11).

**7.1 SU(2) is the 3-sphere** [classical; Lean as sets].
- **The map.** `(alpha, beta)` with `abs(alpha)^2 + abs(beta)^2 = 1` goes to the matrix `[[alpha, beta], [-conj beta,
  conj alpha]]`, the unit quaternion `alpha + beta j`.
- **What is in Lean.**
  - `su2Mat_mem`: every such matrix lies in `Matrix.specialUnitaryGroup (Fin 2) C`.
  - `su2_form`: every element of SU(2) has this form. The proof: `star U = adjugate U`, since both invert `U` when
    `det U = 1`.
  - `sphereEquivSU2`: the resulting bijection between the unit sphere of `C^2 = R^4` and SU(2).
- **What is not in Lean.** That this bijection is a homeomorphism, indeed a diffeomorphism, is classical.
- **What Perelman certified.** His theorem says every closed, simply connected 3-manifold is diffeomorphic to this
  manifold, the group manifold of the SU(2) gauge group [classical].
- **Normalisation.** With `<X, Y> = -tr(XY)`, SU(2) is the round 3-sphere of radius `sqrt 2`: every sectional curvature
  is `1/2` [numerical].

**7.2 Ricci flow on every SU(N)** [classical for the curvature, Lean for the ODE, numerical for the constants].
- **Curvature of a bi-invariant metric.** `Ric = -(1/4) B`, with `B` the Killing form. On `su(N)`,
  `B(X, Y) = 2N tr(XY)`. So with `<X, Y> = -tr(XY)`:

      Ric = (N/2) g,    scalar curvature R = N (N^2 - 1)/2.

  - **The coordinator's estimate is correct.** Einstein constant `N/2`, extinction time `1/N`.
  - It agrees with the PREP form "`Ric = (1/4) g` for the metric `-B`", since `-B = 2N (-tr)`.
  - For the metric `c (-tr)` the constant is `N/(2c)` and the extinction time is `c/N`.
- **The flow.** Ricci curvature is scale invariant, so `g(t) = phi(t) g(0)` solves `dg/dt = -2 Ric` iff
  `phi' = -2 lambda`. The flow is

      g(t) = (1 - N t) g(0),    extinct at T = 1/N.

  - `shrink_hasDerivAt`, `shrink_unique`: this is the solution, and the only one [Lean].
  - `shrink_pos`, `shrink_extinct`, `sun_extinction`: `phi > 0` before `T` and `phi(T) = 0` [Lean].
  - Uniqueness of Ricci flow on closed manifolds keeps the flow homothetic [classical].
- **The curvature blows up only at the final point.** The Einstein constant of `g(t)` is `lambda(t) = lambda/(1 - 2
  lambda t)`.
  - `einstein_hasDerivAt`: it satisfies `lambda' = 2 lambda^2` [Lean]. With `R = n lambda(t)` this is `R' = (2/n) R^2`,
    the equality case of `dR/dt >= Delta R + (2/n) R^2` (section 6.1).
  - `einstein_unbounded`: `lambda(t) -> infinity` as `t -> T` from below [Lean].
  - There is no other singularity and no surgery: the whole manifold shrinks to a point.
- **The constants checked** (`blowup_sun_check.log`) [numerical]:

  | `N` | dim | Ricci from structure constants | scalar curvature | extinction time | min sectional curvature |
  |---|---|---|---|---|---|
  | 2 | 3 | `(N/2) delta`, error 4e-16 | 3 | 0.5 | 1/2 (all) |
  | 3 | 8 | `(N/2) delta`, error 4e-16 | 12 | 0.3333 | 0 (commuting Cartan pair) |
  | 5 | 24 | `(N/2) delta`, error 9e-16 | 60 | 0.2 | 0 |
  | 11 | 120 | `(N/2) delta`, error 5e-15 | 660 | 0.0909 | 0 |

  The Killing form `-2N delta` is reproduced to 1e-14. The ODE, integrated numerically, reaches 0 at `1/N`.

**What this certifies, and what it does not.** The bi-invariant SU(N) reaches extinction in finite time, with no surgery.
That is the same final certificate as Perelman's, delivered by symmetry. But it certifies nothing about topology:
- Perelman's extinction says something because it holds for **every** metric on a simply connected 3-manifold.
- Here the metric was chosen symmetric. Every Einstein metric with positive constant shrinks homothetically to extinction
  (`CP^n`, `S^2 x S^2`, any positive Einstein manifold), so extinction does not single out SU(N).

**7.3 Stability: SU(2) is the stable one** [external, Lean for the arithmetic, numerical].
- **SU(2).** On a closed 3-manifold, every metric of positive Ricci curvature flows, after normalisation, to constant
  curvature (Hamilton 1982) [classical]. So S^3 = SU(2) attracts.
- **The criterion.** Cao and He (arXiv 1304.2697, Crelle 2015) classify the linear stability of Perelman's nu-entropy
  on symmetric spaces of compact type [external]. With `Ric = lambda g` and `mu_1` the first nonzero eigenvalue of the
  Laplacian on functions, a non-spherical Einstein manifold is unstable in the conformal directions when

      n/(n-1) lambda < mu_1 < 2 lambda.

  Their table (Theorem 1.4) lists SU(3) as "linearly unstable". Their general theorem lists SU(n+1), n >= 2. The latter
  was read through a summary of the paper, not verbatim.
- **Our check of the window.** On SU(N), `mu_1` is the Casimir of the fundamental representation, `N - 1/N` (the smallest
  nonzero Casimir) [classical; numerical to 2e-15]. With `lambda = N/2` and `n = N^2 - 1`:
  - `sun_window` [Lean]: for every `N >= 3`, `mu_1` lies strictly inside the window. For example, for N = 3 it reads
    `1.714 < 2.667 < 3`.
  - `su2_window_edge` [Lean]: for `N = 2`, `mu_1 = 3/2` sits exactly on the lower edge. This is Obata's equality case,
    the round sphere, which the criterion excludes.
- **What it means.** For `N >= 3` the bi-invariant SU(N) is not a local maximum of the nu-entropy. Kroencke showed that
  such an Einstein metric is dynamically unstable: there are nearby metrics whose Ricci flow does not return to it
  [external, recalled]. So the homothetic extinction of 7.2 is a property of one metric, not of a neighbourhood.
- **Flat planes.** For `N >= 3` SU(N) has rank at least 2, hence flat planes: commuting Cartan elements give sectional
  curvature 0 [numerical]. Its curvature operator is nonnegative but not positive, so Hamilton's, Boehm-Wilking's and the
  differentiable sphere theorems do not apply [classical].

In the language of section 4.1: the bi-invariant SU(N) is an **exact profile** of the rescaled (normalised) Ricci flow, a
compact shrinking soliton. SU(2) is a **stable** profile; every SU(N) with `N >= 3` is an **unstable** profile, like those
of arXiv 2509.14185 [reading, on the external and Lean facts above].

**7.4 What a genuine "Poincare for SU(N)" would be, and its status.**

The statement: *every closed manifold homotopy equivalent to SU(N) is homeomorphic (or diffeomorphic) to SU(N).*

- **`N = 2`: true.** This is Poincare itself. In dimension 3 the topological and smooth categories agree (Moise), so
  Perelman gives diffeomorphism [classical].
- **`N >= 3`: no theorem found** (dimension `N^2 - 1 >= 8`).
  - **Surgery theory decides it.** For a simply connected closed manifold of dimension at least 5, the manifolds homotopy
    equivalent to it are classified by the surgery exact sequence of Browder, Novikov, Sullivan and Wall: the normal
    invariants `[M, G/TOP]` (or `G/O` in the smooth case) and the simply connected L-groups [classical]. I found no paper
    that computes this structure set for SU(N), or states a recognition theorem for it. The searches of 2026-11-23
    turned up nothing specific; that is a negative search result, not a proof of absence.
  - **Smooth case.** For a homotopy sphere `Sigma`, `SU(N) # Sigma` is homeomorphic to `SU(N)`. Exotic 8-spheres exist
    (`Theta_8 = Z/2`) [classical]. Whether `SU(3) # Sigma^8` is diffeomorphic to SU(3) depends on the inertia group of
    SU(3), which I did not find computed. So a smooth recognition statement may fail [open as far as found].
  - **Topological case.** It needs the normal invariants of SU(N) and the surgery obstructions. Not computed here [open as
    far as found].
  - **The homotopy side.** "Being a Lie group" is not a homotopy-invariant notion. There are finite H-spaces that are not
    homotopy equivalent to any Lie group: the Hilton-Roitberg "criminal" (1969), a principal S^3-bundle over S^7 [classical,
    recalled]. And there is a whole theory of homotopy Lie groups: p-compact groups (Dwyer-Wilkerson) and their
    classification (Andersen, Grodal, Moller, Viruel) [classical, recalled].
- **Ricci flow is not the tool.** Singularities are not classified in dimension 4 and above. The symmetric SU(N),
  `N >= 3`, is unstable (7.3). No known preserved curvature condition singles out homotopy SU(N)s [classical].

So a genuine "Poincare for SU(N)" would be a statement in surgery theory. It may be false in the smooth category. It is not
attempted and not claimed here [open].

**7.5 The DMP tie-in** [reading]. Each identification, with its exact counterpart:

| owner's term | exact counterpart | status |
|---|---|---|
| **SU(2) is the base** | (a) SU(2) = S^3 is exactly the manifold Perelman certified (`sphereEquivSU2`). (b) Every SU(N) is built from SU(2) by the fibration tower `SU(N-1) -> SU(N) -> S^{2N-1}` (SU(N) acts on the unit sphere of `C^N` with stabiliser SU(N-1)), starting at `SU(2) = S^3`. Rationally `SU(N) ~ S^3 x S^5 x ... x S^{2N-1}`. (c) SU(N) contains one SU(2) per root | (a) [Lean] as sets, [classical]; (b), (c) [classical] |
| **every SU(N) runs to extinction under the same flow** | the bi-invariant metric shrinks homothetically, `g(t) = (1 - N t) g(0)`, extinct at `T = 1/N`, curvature `lambda' = 2 lambda^2` | [Lean] for the ODE, [classical] for `Ric = (N/2) g`, [numerical] for N = 2, 3, 5, 11 |
| **the same certificate as Perelman's** | the same final event (extinction, no surgery), but from a chosen metric. It holds for every positive Einstein manifold, so it carries no topological information about SU(N) | [classical] |
| **the base is distinguished** | SU(2) is the only stable profile: Hamilton's theorem; `mu_1` on the edge of the instability window. Every SU(N), `N >= 3`, sits strictly inside it (unstable) | [Lean] for the window, [external] Cao-He for the criterion and verdict, [classical] Hamilton |
| **pressed base causality** | in section 2's ledger: the bi-invariant SU(N) is an exact profile (residual `eps = 0`, perturbation `M = 0`), and its clock is the curvature ODE `lambda' = 2 lambda^2`. Only for the base does the certificate hold on an open set of metrics, as Perelman's does | [reading] |
| **another route to establish DMP v0.9.9's existence** | none, mathematically. The extension by symmetry is true but holds for every positive Einstein manifold. The genuine extension (7.4) is open, and Ricci flow does not reach it | [reading]; [open] |

**7.6 What extends trivially and what does not.**

| part of Perelman's proof | for SU(2) | for SU(N), `N >= 3` |
|---|---|---|
| the object | S^3 = SU(2) [classical; Lean as sets] | SU(N) is not a sphere: rationally a product of odd spheres, rank `N - 1` [classical] |
| finite-time extinction | from every metric, after surgeries (Perelman; Colding-Minicozzi) [classical] | from the bi-invariant metric only, homothetically, at `T = 1/N`, with no surgery [Lean, classical]. **Extends trivially, by symmetry** |
| stability of the symmetric shrinker | stable: it attracts every positive-Ricci metric (Hamilton) [classical] | unstable: inside Cao-He's window [Lean for the window, external for the verdict]. **Does not extend** |
| classification of blowup limits | kappa-solutions and canonical neighbourhoods, dimension 3 [classical] | none known in dimension 8 and above. **Does not extend** |
| surgery | necks `S^2 x R`, well defined [classical] | no analogue. **Does not extend** |
| recognition ("homotopy equivalent implies the same manifold") | true (Poincare) [classical] | a surgery-theory question; no theorem found; possibly false smoothly. **Open** |

---

## 8. Status table

| item | statement | status |
|---|---|---|
| Chen-Hou | stable nearly self-similar finite-time blowup, 2D Boussinesq and 3D axisymmetric Euler, smooth data, with a boundary; computer-assisted (rigorous numerics), not ML | [external] |
| not Clay | no viscosity, a solid wall, axial symmetry | [classical] |
| arXiv 2509.14185 | unstable self-similar profiles found numerically (neural networks plus Gauss-Newton); no proof claimed; none found in this round's search (2026-11-23) | [external] |
| trapping | `(1 - q)^2 >= 4 C r` and a start within `(1 - q)/(2C)` keep the perturbation in the ball forever (`trap`, `trap_radius`, `trap_of_gap`) | [Lean] |
| floor is sharp | below the threshold the comparison recursion escapes linearly (`escape_of_below`, `escape_pos`); bounded at 0.99, escapes at 1.01 of the threshold | [Lean], [numerical] |
| as `CostAboveFloor` | cost `1 - q` over floor `2 sqrt(C r)`, one step type, `Omega = Unit` (`gap_of_costAboveFloor`) | [Lean] |
| finite clock | focusing `a i <= -gamma < 0`: durations summable, `T* <= 1/(1 - e^{-gamma})` (`durations_pay`, `arrival`) | [Lean] |
| unbounded amplitude | `1/d n >= e^{gamma n} -> infinity` (`amplitude_unbounded`) | [Lean] |
| assembly | one-scale certificate implies trapped profile, finite `T*`, unbounded amplitude (`blowup_of_certificate`) | [Lean] skeleton; the step inequality is a hypothesis, [external] for Euler |
| BKM quantum | per rescaled step, amplitude times duration is one (`boundary_quantum`); BKM: the count is infinite exactly at `T*` | [Lean] skeleton, [classical] BKM |
| one scale suffices | scale invariance makes the rescaled equation autonomous, so every step is the same step | [classical] |
| `T*` as the DB | `T*` is the boundary of smooth existence; the profile is what crosses it | [reading]; counterparts as in 3.2 |
| the act at `T*` | the equation no longer selects a continuation; non-uniqueness of weak continuation for this solution | [reading]; [open] |
| same theorem as the gap | `summable_of_gap` gives both the finite correlation length (Yang-Mills) and the finite `T*` (blowup) | [Lean] for both uses, [reading] for the parallel |
| structural parts | autonomous rescaled frame, approximate profile, certified damping above floor, focusing margin, continuation criterion | [reading] |
| specific parts | the wall, axial symmetry, the weighted norms, stability (unstable profiles need more) | [reading] |
| Navier-Stokes | viscous floor `nu (T* - t)^{1 - 2 alpha}`; a profile would need `2/5 <= alpha < 1/2`, no wall | [classical] scaling; [open] |
| Tao 2016 | averaged NS keeps the energy identity and blows up: the energy ledger is a global sum and does not price a step | [classical]; [reading] for the ledger name |
| O1 quantity | `c_*(L, beta) = inf_omega Z_tw(omega)/Z(omega)`, deterministic; O1 is `c_*(L(beta), beta) >= c0 > 0.743` for all `beta >= beta_0` | [reading] of `YMOneBox` |
| Chen-Hou template for O1 | does not apply: no scale invariance at the hand-over box, no reference outside, outside dimension at least 387 | [fails] |
| what is missing | a worst-case theorem for outsides (one outside or a small family is worst) | [open] |
| refuting side | a certified enclosure at one explicit outside can refute O1 at a given box | [reading], not attempted |
| O1 | unchanged | [open] |
| Poincare: forced singular time | positive scalar curvature forces a singularity by `3/(2 R_min(0))` (the `R^2` comparison) | [classical] |
| Poincare: monotone entropy | W-entropy nondecreasing (cost at least 0, floor 0) gives kappa-noncollapsing at every scale | [classical]; [reading] for the ledger fit (partial) |
| Poincare: finitely many acts | a volume quantum per surgery and a bounded volume: the size reading | [classical]; [reading] |
| Poincare: the act | surgery along necks given by the canonical neighbourhood theorem; the flow continues; canonical since Bamler-Kleiner | [classical] |
| Poincare: the certificate | finite extinction for simply connected `M` (Perelman; Colding-Minicozzi) gives `S^3` | [classical] |
| Poincare: verdict | the DB restatement matches the structure (forced time, scale-invariant estimate, defined act, quantum per act, final certificate), not the mechanism (classification instead of cost above floor at the boundary) | [reading]; nothing new claimed |
| SU(2) = S^3 | the unit sphere of `C^2` is in bijection with SU(2) (`sphereEquivSU2`); homeomorphism classical | [Lean] as sets, [classical] |
| SU(N) Einstein | `Ric = (N/2) g` for `<X, Y> = -tr(XY)`; scalar `N(N^2-1)/2` | [classical], [numerical] N = 2, 3, 5, 11 |
| SU(N) extinction | `g(t) = (1 - N t) g(0)`, `T = 1/N`, `lambda' = 2 lambda^2`, curvature unbounded only at `T` | [Lean] |
| SU(N) stability | SU(2) stable (Hamilton); SU(N), `N >= 3`, strictly inside the conformal instability window, unstable (Cao-He) | [classical], [Lean] window, [external] verdict |
| Poincare for SU(N), `N >= 3` | homotopy SU(N) implies SU(N): no theorem found; surgery theory; possibly false smoothly | [open] |
| DMP tie-in | SU(2) is the base and the only stable profile; extinction by symmetry holds for every positive Einstein manifold, so it is no independent route | [reading] |

---

## 9. Files

| file | content |
|---|---|
| `ProofPhase/Unified/Blowup.lean` | `trap`, `trap_radius`, `trap_of_gap`, `gap_of_costAboveFloor`, `escape_of_below`, `escape_pos`, `durations`, `durations_pos`, `durations_pay`, `arrival`, `amplitude_unbounded`, `blowup_of_certificate`, `boundary_quantum` |
| `docs/unified/blowup-axioms.sh`, `blowup-axioms.log` | build, `#print axioms` for all 13 declarations, source grep |
| `docs/unified/blowup_check.py`, `blowup_check.log` | part 1 trapping threshold; part 2 finite clock; part 3 dimensions of O1's for-all |
| `ProofPhase/Unified/BlowupSUN.lean` | `su2Mat`, `su2Mat_det`, `su2Mat_mem`, `su2_form`, `Sphere3`, `sphereEquivSU2`, `shrink`, `shrink_hasDerivAt`, `shrink_unique`, `shrink_pos`, `shrink_extinct`, `einsteinAt`, `einstein_hasDerivAt`, `einstein_unbounded`, `sun_extinction`, `sun_window`, `su2_window_edge` |
| `docs/unified/blowupsun-axioms.sh`, `blowupsun-axioms.log` | build, `#print axioms` for all 17 declarations, source grep |
| `docs/unified/blowup_sun_check.py`, `blowup_sun_check.log` | Killing form, Ricci, scalar curvature, extinction time, sectional curvatures and `mu_1` for SU(N), N = 2, 3, 5, 11 |

Imported, not edited: `ProofPhase/Unified/Ledger.lean` (`Pays`, `decay`, `summable_of_gap`, `CostAboveFloor`).

Sources consulted this round (2026-11-23): the arXiv abstract pages of 2210.07191, 2305.05660 and 2509.14185; the PNAS
summary of Chen-Hou; the arXiv listings of Tomboulis 0707.2179, Ito-Seiler 0711.4930 and 0803.3019, and Tomboulis
0712.2620. Everything marked "recalled" was not re-checked, including all of section 6.

---

## 10. Links found, not pursued

By the owner's decision (`PREP.md`, last entry), these links are noted as existing and deliberately not worked on.

**Hodge.** The Hodge conjecture says that on a smooth projective complex variety every rational class of type `(p, p)` is a
rational combination of classes of algebraic cycles: what can be described in cohomology exists as geometry [classical,
conjecture]. The link to the GRH work is positivity. Weil proved RH for curves over finite fields through the Hodge index
theorem on the surface `C x C`. Grothendieck's standard conjectures (Lefschetz type and Hodge index type, the latter a
Hodge-Riemann positivity) would give RH for all varieties over finite fields by the same route; Deligne proved RH there by
another one [classical]. The missing arithmetic analogue of that Hodge index, a positivity on "`Spec Z x Spec Z`", is the
positivity the GRH work lacks [reading]. Not pursued.

**Birch-Swinnerton-Dyer.** For an elliptic curve `E` over `Q`, BSD says the order of the zero of `L(E, s)` at `s = 1` equals
the rank of `E(Q)`: the zeros count the rational points that exist [classical, conjecture; proved for analytic rank 0 and 1
by Gross-Zagier and Kolyvagin]. The curve's own RH over each `F_p` is Hasse's bound `abs(a_p) <= 2 sqrt p`, proved
[classical]. Not pursued.
