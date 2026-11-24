# Navier-Stokes: the state of the art, the ledger form of a blowup, and where a construction could start

Status: 2026-11-24. Answers the owner's scope decision recorded as the last entry of `docs/mass-gap/weak-coupling/PREP.md`
("Navier-Stokes is taken on as well; that a blowup cannot be ruled out is in itself enough for an existence to be
constructed where it does blow up"), and the entry before it ("this does not meet DMP-completeness, which blows it up as
a consequence"). Extended the same day by two directions passed on by the coordinator: build Navier-Stokes as an
instance of the project's DMP API (section 5), and tie in the Alpoge-Buckmaster claim as an external input with an audit
list, the way GRH was tied in (section 6; `PREP.md`, entry "the Buckmaster-Alpoege unforced Navier-Stokes work is the same
API as the owner's IM"). Builds on `BLOWUP.md` (sections 2 to 4: the rescaled-frame ledger of Chen-Hou and what
Navier-Stokes would need), `TRANSPORT.md` (section 1: transport of an uncertainty), `API.md` and `GRH-TIE-IN.md` (2.3).

Files:
- Lean: `ProofPhase/Unified/NavierStokes.lean` (27 declarations): a discrete skeleton of the two possible ledger forms.
- Lean: `ProofPhase/Unified/NavierStokesAPI.lean` (29 declarations, namespace `ProofPhase.API.NavierStokes`): the
  instance of the DMP API, with the four problem cards and the external tie.
- `navierstokes-axioms.sh`, `navierstokes-axioms.log`: both modules build with no warnings; 52 declarations depend on the
  three standard axioms only, 4 on none; no `sorry`. Nothing about the Navier-Stokes equations themselves is proved in
  either file.

Status marks as in `BLOWUP.md`: **[Lean]** (proved here, standard axioms), **[classical]** (standard mathematics, recalled,
not re-proved), **[external]** (a published or posted result, recorded, not checked here), **[claimed]** (a 2026 claim,
posted but not refereed and not checked here; the strongest status any Navier-Stokes blowup has today), **[reading]** (an
identification with DMP vocabulary, not a theorem), **[open]** (not proved by anyone), **[fails]** (the requirement does not
hold in this form). "Recalled" means from memory of the literature, not re-checked in this round.

---

## 0. In plain words

**The news first: the landscape changed in 2026.** When this round started, the brief expected Navier-Stokes blowup to be
wide open. It is not quite any more. Two claimed proofs were posted this autumn [claimed]:
- **OpenAI, 8 September 2026: blowup with a smooth force.** A smooth force, compactly supported in space and time, pushes
  a fluid that starts at rest into a singularity at time 1, with bounded energy. The paper says this settles statement
  (C) of the official Clay problem (and (D), on the torus). A Lean formalisation exists. An independent build record
  says it uses only the standard axioms and that its main statements match a public formalisation of the Clay
  statements. A preprint (Bastounis, Circelli, Hansen) shows that the Lean proof departs from the written proof in
  places. Not refereed.
- **Alpoge and Buckmaster, 20 November 2026 (four days ago): blowup with no force.** Smooth, compactly supported data on
  `R^3`, and smooth data on the torus, whose solutions blow up in finite time. That is the version without the "force
  loophole". Not refereed; the decisive numerical certificate is announced, not released (only its hash is published).
  Tao calls the paper technically human-readable with a clear strategy, and says a professional write-up is still needed.

Neither claim is checked here, and nothing in this note depends on either being correct. But the unforced claim is
**exactly the construction this round was asked to sketch**, so the round's answer is mostly a map of it.

**The ledger form.** A blowup is a forming singularity viewed through a zoom that runs at its own speed. Two routes exist,
and the Lean shows which constraints pin them down:
- **The window.** If the singular region shrinks like `(T* - t)^alpha`, viscosity in the zoomed frame has the weight
  `(T* - t)^{1 - 2 alpha}`. It grows without bound above `alpha = 1/2`, so no certificate can cover all steps there
  [Lean]. The local energy stays finite only for `alpha >= 2/5` [Lean]. So a profile must live in `2/5 <= alpha <= 1/2`
  [Lean for the arithmetic, classical for the scalings].
- **Route I, the Leray end `alpha = 1/2` (Type I).** Viscosity is a constant part of the zoomed equation. A shape that
  stands still in the zoom (exact self-similarity) is ruled out (Necas-Ruzicka-Sverak, Tsai) [classical]. A shape that
  repeats periodically in zoomed time (discrete self-similarity) is not ruled out. One period is one ledger step. The
  plain heat flow already pays a fixed cost per period. The profile adds a compact disturbance, which leaves finitely many
  directions that are not damped, and those are removed by choosing the starting data. Then the perturbation dies out,
  infinitely many periods fit into finite time, and the size grows like `(T* - t)^{-1/4}` [Lean for the skeleton]. This
  is the route of the unforced claim.
- **Route II, inside the window, `2/5 <= alpha < 1/2` (Type II).** A profile of the inviscid (Euler) zoomed equation, with
  viscosity as a residual that shrinks step by step. The Chen-Hou certificate of `BLOWUP.md`, with the residual raised by
  the viscosity, then forces blowup [Lean for the skeleton]. Viscosity is summable here, so even with no damping its total
  effect is bounded [Lean]. At `alpha = 1/2` it is not [Lean]. That is why route I must put viscosity inside the profile.
  No route-II profile is known [open].

**Why the energy ledger cannot decide it.** The energy identity is one global sum: total dissipation at most the start
energy. A summable budget never pays a uniform positive cost per step [Lean]. Tao's averaged equations keep this identity
and blow up [classical]. So any proof, either way, must use the finer structure of the true equations.

**Where a DMP-native construction could start.** Route I is the only route with a candidate, and that candidate is the
unforced claim. Building an independent profile and certificate from scratch is beyond reach now: the profile is a
genuinely three-dimensional, time-periodic shape found by large-scale Newton continuation, and the certificate is a
rigorous computation of an estimate for the linearised operator in 3D at 128-bit interval precision. A good first step for
the next round is small and concrete: map the claim's certificate conditions (its Appendix B) row by row onto
`LerayDSSCertificate`, and, once the certificate is released, check its hash and re-verify its explicit numerical
inequalities with an independent interval implementation (section 3).

**What the API answers when Navier-Stokes is filled in (section 5).** Filling in the template gives four answers. Each
comes from an API theorem, and each content step sits in a named slot:
- **Which window:** a computation sorts any rational exponent into one of the four windows, and a theorem proves the
  computed answer right [Lean, runs].
- **Regular?** The regularity card's open step is "every dyadic scale dissipates a uniform cost above the transfer floor".
  The API shows that the energy ledger cannot fill this slot. A summable budget pays no uniform cost, and per scale the
  transfer bound that energy allows outgrows the viscous cost by a factor `2^{k/2}` [Lean]. So the API does not settle
  regularity. Its slot names exactly what is missing: a per-scale cost from the true nonlinearity [open; false if the 2026
  claims hold].
- **Blowup?** In the Leray window the perturbation from a time-periodic profile is a running system in the API's
  contraction class. The API's `settle` theorem then says the perturbation dies out, with a computed number of periods,
  and dying out in the zoomed frame **is** blowup in real time [Lean]. The one open step is the period contraction, which
  is exactly what the Alpoge-Buckmaster certificate claims to supply.
- **The external tie (section 6):** their theorems sit in `External` slots, and their unreleased certificate is the card's
  one open step. Fefferman's (A) and (B) then fail by the card [Lean for the plumbing; claimed for the content].

So the mechanical answer is: the API does not settle Navier-Stokes as regular, and it settles blowup in the Leray window
once one named slot is filled. That slot is a claimed but unreleased certificate today.

**The logic point (section 4).** "Cannot be ruled out" gives a model where blowup holds only in the sense "the axioms of
mathematics cannot refute it". By Goedel's completeness theorem that model exists, but it may be nonstandard: its real
numbers and functions need not be the real ones. The Clay problem asks about the real equations over the real numbers.
What answers it is a proof, which holds in every model, the standard one included. The 2026 claims are of this kind: an
explicit datum and a proof. If they hold, they are an existence constructed where it blows up, in the owner's words, by a
finite certificate.

**The owner's reading, with its status.** "Navier-Stokes is not DMP-complete, which blows it up": in ledger terms, the
energy ledger cannot pay a uniform cost per scale (supercriticality, Tao). The reading predicted blowup, the side the 2026
claims now assert [reading]. The reading itself proves nothing. Supercriticality shows only that the energy method cannot
rule blowup out. The claims, if correct, prove it by a different mechanism: a certified profile, not a failed ledger.

---

## 1. The state of the art

### 1.1 The Clay problem (Fefferman's official statement) [classical]

Incompressible Navier-Stokes in three dimensions, viscosity `nu > 0`, force `f`. Four statements; a proof of any one wins
the prize.
- **(A) Existence and smoothness on `R^3`.** For every smooth, divergence-free initial datum with all derivatives decaying
  faster than any power, and **zero force**, there is a smooth solution for all time with bounded energy.
- **(B) Existence and smoothness on the torus `R^3/Z^3`**, zero force, smooth periodic data.
- **(C) Breakdown on `R^3`.** There exist a smooth, rapidly decaying divergence-free datum **and a smooth force** `f`
  (decaying in `x` and `t` like the datum) for which no smooth solution with bounded energy exists for all time.
- **(D) Breakdown on the torus**, likewise, with a force.

Two points that matter below:
- (C) and (D) **allow a force**. A forced blowup with a force of the admitted class proves (C) as stated. The force is the
  "loophole" the press discussed after the OpenAI claim.
- A blowup **without force** disproves (A) (respectively (B)), and so proves (C) (respectively (D)) with `f = 0`.

### 1.2 The no-go results and the known constraints [classical, recalled]

| result | statement | what it rules out for a blowup |
|---|---|---|
| Leray (1934) | if a smooth solution is singular at `T*`, then `sup abs(u) >= c (nu/(T* - t))^{1/2}` and `norm(grad u)_{L^2} >= c (T* - t)^{-1/4}` | blowup slower than these rates |
| Necas, Ruzicka, Sverak (Acta Math. 176, 1996) | a backward self-similar solution `u = (T* - t)^{-1/2} U(x / sqrt(T* - t))` with `U` in `L^3` is zero | exact self-similarity at the Leray scaling, in `L^3` |
| Tsai (Arch. Ration. Mech. Anal. 143, 1998) | the same for `U` in `L^p`, `3 < p < infinity`, and under local energy bounds | exact self-similarity in the natural classes |
| Caffarelli, Kohn, Nirenberg (Comm. Pure Appl. Math. 35, 1982) | for suitable weak solutions the singular set has zero one-dimensional parabolic Hausdorff measure | singularities on curves; isolated points remain possible |
| Escauriaza, Seregin, Sverak (Russian Math. Surveys 58, 2003) | a solution bounded in `L^infinity_t L^3_x` is smooth (and, Seregin 2012, the `L^3` norm must tend to infinity at a singular time) | blowup with a bounded scale-invariant `L^3` norm |
| axisymmetric Type I exclusion (Chen-Strain-Tsai-Yau; Koch-Nadirashvili-Seregin-Sverak, around 2008-2009) | axisymmetric solutions have no singularity with `abs(u) <= C (T* - t)^{-1/2}` | a Type I axisymmetric blowup |
| Chae-Wolf; Pineau-Vicol (cited by Alpoge-Buckmaster) | smooth backward discretely self-similar solutions obey the Type I bound; nonzero ones need a period bounded below | discretely self-similar solutions with too small a period |

**What is left open by these** [classical]: discretely self-similar solutions (the shape repeats after a fixed zoom, maybe
rotated; Bradshaw-Tsai Open Problem 5.1 asked exactly whether a nonzero backward one exists), asymptotically self-similar
solutions, and Type II rates.

### 1.3 Tao's averaged Navier-Stokes [classical]

T. Tao, "Finite time blowup for an averaged three-dimensional Navier-Stokes equation", J. Amer. Math. Soc. 29 (2016)
601-674 (arXiv 1402.0290).
- **What changes.** The bilinear term `B(u, u)` is replaced by an average of copies conjugated by rotations and by
  order-zero Fourier multipliers.
- **What is kept.** The cancellation `<B~(u, u), u> = 0` (hence the energy identity) and the standard harmonic-analysis
  estimates of the nonlinearity.
- **What happens.** A smooth solution blows up in finite time. The mechanism is a delayed cascade of energy from one dyadic
  scale to the next, an ODE system related to the Katz-Pavlovic dyadic model.
- **What it shows.** A proof of global regularity must use finer structure of the true nonlinearity than the energy
  identity and those estimates. The paper also proposes a programme for carrying the blowup over to the true equations,
  which it does not carry out.
- In ledger terms: section 2.5, `ns_energy_identity_not_costAboveFloor` [Lean].

### 1.4 Numerical blowup candidates [external]

- **Hou, "Potentially singular behavior of the 3D Navier-Stokes equations"** (arXiv 2107.06509, revised May 2022;
  Foundations of Computational Mathematics). Axisymmetric, smooth finite-energy data, constant viscosity (a relatively
  large `nu = 5e-3`). Reported:
  - maximum vorticity growing by about `10^7`;
  - nearly self-similar scaling, with the core size `R(t), Z(t) ~ (T - t)^{1/2}` and `max abs(omega) ~ (T - t)^{-1}`;
  - the Beale-Kato-Majda integral apparently growing without bound.

  Numerical evidence, not a proof [external]. These are Leray-scaling (Type I size) rates. Strict Type I blowup is
  excluded for axisymmetric solutions (1.2), so if this scenario is singular, its rate must deviate from the observed one,
  for example by logarithmic factors [reading; the tension is noted, not resolved here].
- **Hou and Huang** (arXiv 2102.06663): with a **degenerate** viscosity (vanishing like `r^2 + z^2` at the origin) a
  two-scale travelling solution forms. With constant viscosity, the same data do not blow up [external].
- In this round's searches I found no newer Hou paper specifically on Navier-Stokes blowup after 2022. That is a negative
  search, not exhaustive.
- **Machine-learning-found profiles** (Wang et al., arXiv 2509.14185, `BLOWUP.md` 1): Boussinesq, IPM and the
  Cordoba-Cordoba-Fontelos model, not Navier-Stokes [external].

### 1.5 Computer-assisted and AI-assisted programmes aimed at Navier-Stokes

**(a) Alpoge and Buckmaster, "Finite-time blow-up for the Navier-Stokes equations"** (79 pages, version of 20 November
2026; public GitHub repository with the paper and a Lean library) [claimed]. Read from the paper itself (sections 1.1 to
1.3) this round:
- **Statement.** Smooth, compactly supported, divergence-free data on `R^3`, and smooth divergence-free data on `T^3`,
  whose unforced solutions blow up in finite time. Viscosity normalised to 1, hence every viscosity by scaling. The paper
  says this disproves (A) and (B), and so proves (C) and (D).
- **Profile.** A pair `(W, q)` solving the Navier-Stokes equations in self-similar variables `y = x / sqrt(T - t)`,
  `s = log(T / (T - t))`, with the viscous term `-Delta W` **inside** the profile equation. It is periodic in `s` up to an
  isometry: backward discretely self-similar, the case Bradshaw-Tsai left open. Not steady, so Necas-Ruzicka-Sverak and
  Tsai do not apply. Bounds `abs(W) <= C (1 + abs(y))^{-1}`: Type I, bounded in weak `L^3`, not in `L^3`, consistent with
  Escauriaza-Seregin-Sverak.
- **Theorem 1.1 (conditional).** One such profile implies blowup from smooth compactly supported data, with
  `c (1 - t)^{-1/4} <= norm(grad u(t))_{L^2} <= C (1 - t)^{-1/4}`, Leray's lower rate. The solution converges to the
  profile in self-similar variables. The blowup is **stable in finite codimension**: the period map minus the free heat
  flow is compact, the free flow contracts `Ḣ^1` by `e^{-S/4}` per period (`Ḣ^1` is subcritical by `1/4`), so only
  finitely many eigenvalues lie outside a disc of radius below 1, and each is removed by adding an element of a fixed
  finite-dimensional space to the datum. Nothing is assumed about those eigenvalues. A Lyapunov-Perron argument and a
  contraction finish it. The torus case: the solution is cut off and periodised at a large period, and the error is
  removed by the contraction.
- **Theorem 7.1 (certificate to profile).** An approximate periodic profile with explicit inequalities (a "certificate")
  gives an exact profile nearby, via a Fredholm argument and the Schauder-Tychonoff fixed point theorem.
- **The candidate.** Found by Newton's method on an adaptive discretisation, after continuation. Not axisymmetric.
  Invariant under rotation by `2 pi / 19` about one axis and by `pi` about another. Period `S ~ 0.36`, and half a period
  rotates it by `pi/19`. Gradient norm of order `10^4`. The exact profile is said to lie within 0.017 in `Ḣ^1` of the
  approximate one.
- **What is not yet available.** The certificate is not released; the paper gives its hash
  `3f7a335b84b6c7631742cacc5343dfcd11cf72f5221ff79b2b9268790b4b22c5`. The interval-arithmetic verification (Arb through
  FLINT, 128 bits) is not part of the formalisation and not in the repository. Per its README the Lean library (about 2,270
  files and 600,000 lines, Lean v4.33.1, comparator files permitting only the three standard axioms) was patched on 20
  November and the patched package was not rebuilt.
- **Expert status.** Tao (blog, 20 November 2026): technically human-readable, broadly clear strategy (numerical
  approximate discretely self-similar solution plus rigorous perturbation), a professional write-up still needed. No
  referee report. **Status: [claimed].**
- A companion claim, unforced 3D Euler blowup on the torus (Alpoge, Buckmaster, Coiculescu), is reported alongside
  [claimed]; not read this round.

**(b) OpenAI, "Finite time blowup for Navier-Stokes"** (announced 8 September 2026; paper and the Lean repository
`openai/NavierStokesAndEuler`) [claimed]. Read from the paper's abstract and Theorem 1.1 this round:
- **Statement.** For every `nu > 0` there are a force `f` in `C_c^infinity(R^3 x (0, infinity))`, a compact set `K`, and a
  smooth solution on `[0, 1)` with **zero initial velocity**, supported in `K`, with bounded energy and
  `limsup norm(u(t))_{L^infinity} = infinity` as `t -> 1`. The paper says this establishes (C), and (D) by its Corollary
  10.6.
- **Method.** An axisymmetric leading flow in anisotropic similarity variables, slightly faster than Type I (an extra factor
  `(1 - t)^{-epsilon/2}`, `0 < epsilon < 1/200`), corrected to all orders. The remaining divergence-form residual is
  cancelled by oscillatory pulses, and what is left is the force. Expository Parts I and II by Lei and Ren (arXiv 2609.35406,
  2611.06869) rewrite the construction, call it a major advance, and claim no original contribution [external].
- **Lean.** An independent build record (Zenodo, 10 October 2026, Lean v4.34.0-rc2) reports: the main theorems depend only
  on `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `native_decide` or new axiom in 816 files; the 16 definitions
  and both statements match Google DeepMind's Formal Conjectures formalisation of (C) and (D) [external, not re-built here].
- **Criticism.** Bastounis, Circelli and Hansen (arXiv 2610.08144) show lemma-level places where the Lean proof is not a
  faithful translation of the written one (e.g. Lemma 8.6, where the Lean needs one more derivative). They expressly make
  no claim about the correctness of the written proof [external].
- **Status: [claimed].** If the Lean statement is a faithful rendering of Fefferman's (C) and the build is sound, (C) with
  a force would be machine-checked whatever the state of the prose. That fidelity rests on the Formal Conjectures
  formalisation and is not checked here. OpenAI states it does not intend to claim the prize.

**(c) Smaller programmes** [external]:
- Petrillo and Glimm (arXiv 2609.23868) set a target for a computer search for unforced blowup, the "positive defect
  problem". Its implications are proved in Lean 4 over Mathlib, with no Navier-Stokes object in the library. A first
  search at `256^3` found the needed energy-flux floor holding for a third of a turnover time, then failing at the
  Kolmogorov scale.
- Cheskidov, Dai and Palasek (arXiv 2609.26790) prove cascade blowup and non-uniqueness in dyadic shell models, not in
  Navier-Stokes.

**(d) Chen-Hou** (`BLOWUP.md` 1) remains Euler with a boundary, no viscosity [external].

---

## 2. The ledger form of a Navier-Stokes blowup (`NavierStokes.lean`)

### 2.1 The frame

Zoom at the singularity's own rate: `T* - t = e^{-s}`, length scale `l = (T* - t)^alpha`, velocity `l / (T* - t)`.

| ledger | Navier-Stokes |
|---|---|
| **steps** | route I: periods of length `S` in self-similar time `s` (the zoom factor per period is `e^{-S/2}` in length); route II: unit steps of the dynamically rescaled time, as in `BLOWUP.md` 2.2 |
| **carried** | the size `M n` of the perturbation from the profile, in the rescaled norm (route I: `Ḣ^1`, after finitely many directions are removed; route II: a weighted norm as in Chen-Hou) |
| **cost** | the damping per step: route I, the free flow's `S/4` per period plus the compact correction from the profile, net factor `rho < 1`; route II, the damping `1 - q` of the linearised inviscid operator |
| **floor** | viscosity: the coefficient `nu e^{-(1 - 2 alpha) s}` of the viscous term in the zoomed frame (`nsViscous`); plus, for an approximate profile, its residual and the nonlinear constant |
| **clock** | route I: explicit, `T* - t = e^{-s}`, so period `n` lasts `e^{-nS}(1 - e^{-S})` (`nsPeriodLength`); route II: the focusing ledger of `BLOWUP.md` 2.5 |
| **amplitude** | `e^{s/4}` times the rescaled size in `Ḣ^1` (route I), i.e. `(T* - t)^{-1/4}`; route II, `1/d n` as in `Blowup.lean` |

### 2.2 The window [Lean for the arithmetic; classical for the scalings]

| `alpha` | viscous floor `nu (T* - t)^{1 - 2 alpha}` | local energy `(T* - t)^{5 alpha - 2}` | velocity vs Type I | verdict |
|---|---|---|---|---|
| `> 1/2` | grows without bound (`nsViscous_tendsto_atTop`); no one-scale certificate covers all steps (`ns_no_uniform_certificate`) | bounded | slower than Type I, below Leray's lower bound | excluded |
| `= 1/2` | constant (`nsViscous_half`): part of the zoomed equation | bounded, tends to 0 | Type I (`ns_typeI_iff`) | **route I**: exact self-similarity excluded (NRS, Tsai), discrete self-similarity open |
| `[2/5, 1/2)` | shrinks (`nsViscous_le`), summable over steps (`nsViscous_summable`) | bounded (`ns_energy_window`) | Type II | **route II**: an inviscid profile with viscosity as a residual |
| `< 2/5` | shrinks | unbounded | Type II | excluded (infinite local energy) |

`ns_window` [Lean]: bounded viscous floor and bounded local energy hold together exactly for `2/5 <= alpha <= 1/2`.
`nsViscous_bounded_iff` [Lean]: the floor is bounded exactly when `alpha <= 1/2`.

**Correction to `BLOWUP.md` 4.2.** That section says a Navier-Stokes analogue of Chen-Hou "needs a stable profile of the
inviscid rescaled equation with `2/5 <= alpha < 1/2`" and that no such profile is known. That is route II only. At
`alpha = 1/2` exact self-similar profiles are excluded, but time-periodic (discretely self-similar) viscous profiles are
not, and the 2026 unforced claim is of exactly that kind (route I). The coordinator may want to amend the sentence; this
round touched only its new files.

### 2.3 Route I: the sufficient condition at the Leray scaling (`LerayDSSCertificate`)

**The named hypothesis** [Lean, as a structure]:
- a profile `W : R -> X`, periodic in `s` with period `S > 0` (`periodic`), and **not steady** (`nonsteady`);
- a lower bound `A > 0` on its rescaled `Ḣ^1` size;
- a contraction `0 <= rho < 1` and a quadratic constant `C >= 0`: over one period the perturbation obeys
  `M (n+1) <= rho M n + C (M n)^2`. This is the period map restricted to the complement of finitely many directions,
  which the datum removes.

**What the ledger then proves** (`ns_blowup_of_dss`) [Lean]:
- the perturbation decays geometrically: `M n <= (rho + C delta)^n delta` for a start `M 0 <= delta` with
  `rho + C delta < 1` (`ns_dss_converge`); the solution converges to the profile;
- infinitely many periods fit into the finite time 1 (`ns_period_hasSum`: the period lengths sum to exactly 1);
- the `Ḣ^1` amplitude `e^{nS/4} (A - M n)` tends to infinity (`ns_dss_amplitude`): the rate `(T* - t)^{-1/4}`, Leray's
  lower bound;
- the profile is not steady (`not_steady`).

**In the ledger's language**:
- `ns_free_flow_pays` [Lean]: the free flow (heat flow plus rescaling) is a decay ledger with cost `S/4` per period, floor
  0. This is the `Ḣ^1` subcriticality, the source of every damping in route I.
- `ns_dss_costAboveFloor` [Lean]: a period factor `0 < rho < 1` is `CostAboveFloor` with cost `-log rho` over floor 0, for
  one step type (`Omega = Unit`). As in `BLOWUP.md` 2.4, the zoomed equation is autonomous, so one period is every period.

**How route I respects the no-go results:**
- **Necas-Ruzicka-Sverak, Tsai**: they exclude steady profiles (exact self-similarity). The certificate demands a
  non-steady periodic one. For Alpoge-Buckmaster the non-steadiness is even forced: their profile's slices lie in `L^6`,
  where Tsai excludes steady ones (their 1.2) [claimed].
- **Escauriaza-Seregin-Sverak**: the profile decays like `1/abs(y)`, so the field is bounded in weak `L^3` but not in
  `L^3`. On a fixed ball the `L^3` norm then grows at most like `(log(1/(T* - t)))^{1/3}`. That is consistent with ESS and
  Seregin's theorem that the `L^3` norm must diverge [classical scaling computation; reading].
- **Caffarelli-Kohn-Nirenberg**: one singular point per profile, allowed.
- **Axisymmetric Type I exclusion**: route I is Type I, so its profile cannot be axisymmetric. The claimed candidate is
  not axisymmetric (19-fold symmetry) [claimed].
- **Chae-Wolf, Pineau-Vicol**: the period must not be too small. Here `S ~ 0.36` [claimed]; the bound's constant is not
  checked here.

### 2.4 Route II: the sufficient condition inside the window (`EulerProfileCertificate`)

**The named hypothesis** [Lean, as a structure]: the one-scale certificate of `Blowup.lean` (damping `q`, nonlinear
constant `C`, profile residual `epsilon`, focusing margin `cbar + K R <= -gamma < 0`), with the length exponent in
`2/5 <= alpha < 1/2` and the trapping condition raised by the viscosity:
`(1 - q)^2 >= 4 C (epsilon + nu)`.

**What the ledger then proves** (`ns_blowup_of_euler_profile`) [Lean]: if the step bound holds with the viscous term of
each step added to the residual, the perturbation stays trapped, the durations sum to a finite `T*`, and the amplitude is
unbounded. The certificate at step 0 covers every step because below the Leray scaling the viscous floor only shrinks
(`nsViscous_le`). `ns_euler_gap_of_costAboveFloor` states the same condition as `CostAboveFloor` of `1 - q` over
`2 sqrt(C (epsilon + nu))`.

**Viscosity as a transported uncertainty** (`TRANSPORT.md` 1) [Lean]:
- `ns_viscous_transport_bounded`: below the Leray scaling the viscous term is a summable fresh uncertainty, so even at
  cost = floor (no damping at all) its accumulated total stays bounded (`critical_bounded_iff`).
- `ns_viscous_transport_unbounded_at_leray`: at `alpha = 1/2` it is a constant fresh uncertainty and accumulates without
  bound (`critical_unbounded`). So at the Leray scaling viscosity cannot be a perturbation of an inviscid profile. It has
  to sit inside the profile equation, which is route I.

**How route II respects the no-go results:** the profile is not Leray-scaled, so NRS and Tsai do not apply. The `L^3`
norm scales like `(T* - t)^{2 alpha - 1}`, which tends to infinity for `alpha < 1/2`, consistent with ESS [classical].
It is Type II, so the axisymmetric Type I exclusion does not apply either. **No candidate exists** [open]: smooth-data
Euler blowup without a boundary was itself open until 2026, and the 2026 Euler claims (OpenAI unforced on `R^3`, as cited
by Lei-Ren; Alpoge-Buckmaster-Coiculescu on the torus) were not read this round. Whether any of their profiles has
`alpha` in the window and survives viscosity is unknown here.

### 2.5 Why the energy ledger cannot decide [Lean; classical for Tao]

`ns_energy_budget_not_costAboveFloor`: if the per-step costs are summable, `CostAboveFloor cost 0` fails.
`ns_energy_identity_not_costAboveFloor`: nonnegative dissipated shares whose partial sums stay below the start energy
`E_0` (the energy identity) never pay a uniform positive cost per step. The energy identity constrains the sum, not any
single step. Tao's averaged model (1.3) keeps exactly this and blows up. So:
- a **regularity** proof needs a per-step cost from the true nonlinearity (the reverse ledger, `BLOWUP.md` 4.2, last
  bullet) [open, and if the 2026 claims hold, false];
- a **blowup** proof needs a per-step certificate around a profile (routes I and II). The 2026 claims supply one for
  route I [claimed].

### 2.6 What is and is not in the Lean

- **In:** the window arithmetic, both named hypotheses, and the consequences of each by the ledger (`Blowup.lean`) and
  transport (`Transport.lean`) theorems. Standard axioms only, no unproved steps.
- **Not in:** the PDE. That a profile exists, that the period map has the stated contraction on a finite-codimensional
  complement, that the step bounds hold in a real norm: these are the external inputs, exactly what Alpoge-Buckmaster's
  Theorems 1.1 and 7.1 and their certificate claim to supply.

---

## 3. Where a DMP-native construction could start

**The candidate scenario.** Route I, a backward discretely self-similar viscous profile at the Leray scaling. It is the
only route with a candidate, and the claimed candidate already exists.

**What would have to be certified (Chen-Hou style), following Alpoge-Buckmaster's architecture:**
1. An approximate periodic profile: a 3D, time-periodic, non-axisymmetric field (gradient norm about `10^4`, a 19-fold
   symmetry), with a small residual.
2. An a priori estimate for the linearised periodic problem (with finitely many constraints), certified by bounds on
   finitely many functions and numbers (their Appendix B).
3. A fixed point (Schauder-Tychonoff) for the period and the profile.
4. The stability step (their Theorem 1.1). This needs no certificate: compactness plus finite codimension.

**The size.** Step 1 is a large-scale numerical continuation and Newton solve in 3D plus time. Step 2 is a rigorous
interval computation at 128-bit precision over that discretisation. For Chen-Hou (2D, a simpler setting) these took years
of expert work. The claimed Navier-Stokes certificate is not even released yet. **An independent DMP-native construction
is beyond reach now**, because:
- the profile is genuinely three-dimensional and time-periodic: no symmetry reduces it to two variables, unlike Chen-Hou's
  axisymmetric reduction;
- the certificate is an operator estimate, not a pointwise inequality, and needs a full rigorous linear-algebra pipeline;
- this round's budget is small CPU checks, and the computation is far outside that.

A DMP-native construction from scratch would mostly duplicate the claimed one. What the project can do well is check and
restate.

**A concrete first step for the next round (small, CPU, no GPU):**
1. **Map the certificate onto the ledger.** Read Alpoge-Buckmaster's Section 7 and Appendix B, and write each condition as
   a row of `LerayDSSCertificate` (period, contraction radius, quadratic constant, residual, the finite-dimensional space).
   Note where their norm differs from the skeleton's. Deliverable: a table and, where clean, a refined Lean structure.
2. **When the certificate is released:** check its SHA-256 against the published hash, and re-verify the explicit
   numerical inequalities (the part outside their formalisation) with an independent interval implementation, starting
   with the cheapest conditions. That is a check of the step that today rests on one computation by the authors.
3. **Optional, heavier, another machine:** rebuild their Lean library after the 20 November patch, with
   `#print axioms` on the comparator statements, as was done for the Yang-Mills submission. About 600,000 lines; CPU-hours,
   not a laptop check.

The full audit list for importing their result is section 6.4; steps 1 to 3 here are its items 5, 1 and 3 in the order
that fits a small CPU round.

Route II stays [open]; the first step there would be to read the 2026 unforced Euler claims and compute their exponents.

---

## 4. The logic point

**(1) The theorem behind "cannot be ruled out, so an existence can be constructed"** [classical]. Goedel's completeness
theorem: a consistent first-order theory has a model. So if ZFC plus the sentence "some smooth datum blows up" is
consistent (ZFC cannot refute it), there is a model of ZFC in which that sentence holds.

**(2) Three senses of "cannot be ruled out"** (as in the coordinator's note in `PREP.md`):
- (a) one method cannot rule it out: the energy method, by supercriticality and Tao's model
  (`ns_energy_identity_not_costAboveFloor`). This is a limit of a method; it gives no model and no blowup.
- (b) the axioms cannot refute it: independence of regularity from ZFC. Not known for Navier-Stokes. Only this sense feeds
  the completeness theorem.
- (c) it is not ruled out for the real equations over the real numbers: the Clay question itself.

**(3) What a completeness model gives.** A model of ZFC in which "blowup" holds can be **nonstandard**:
- its natural numbers may contain infinite elements;
- its real numbers and its smooth functions are whatever that model calls by those names.

The datum that "blows up" there need not be a real smooth field, and the blowup need not happen for the actual equations.
Absoluteness theorems (such as Shoenfield's for statements of low complexity) transfer truth only between well-founded
models that share the same ordinals, and a completeness model need not be well-founded [classical, recalled]. So sense (b)
yields an existence in some model, not in the standard one.

**(4) Why the Clay problem needs the standard solution.** Fefferman's statements are about `R^3`, the real torus, and
actual smooth functions. A proof from the axioms holds in every model, the standard one included, and that is what the
problem asks for. A model where blowup holds settles nothing about the real equations. Only a proof does.

**(5) How the 2026 claims fit.** Both are proofs, not completeness models: an explicit datum (OpenAI also an explicit
force) and an argument that its standard solution blows up. If correct, they are exactly "an existence constructed where it
does blow up", and that existence is the standard one. In Alpoge-Buckmaster the construction runs through a finite object,
the certificate: a finite check (Theorem 7.1) produces an exact profile, and the ledger (Theorem 1.1) carries it through
infinitely many periods into a finite time [reading]. This is the hand-over of `UNIFIED.md` section 6 again: a finite check
with a margin certifies an infinite chain.

**(6) The owner's reading, with its status.** "Not DMP-complete, hence blows up" is sense (a) read as a prediction
[reading]. It named the side that the 2026 claims assert. Sense (a) alone cannot prove that side, since a method's failure
to exclude blowup is not blowup. The claims prove it by route I's certificate, not by the failure of the energy ledger.
Whether the project's DMP-completeness has a precise statement that Navier-Stokes violates, and from which blowup would
follow, is [open]. Nothing in this round formulates or proves it.

---

## 5. Navier-Stokes through the DMP API (`NavierStokesAPI.lean`)

The owner's direction: fill in the API's template (`API.md` section 3) and let the API's theorems answer. The file
imports `ProofPhase.API` and the ledger skeleton. It adds no new mathematics about Navier-Stokes, and it puts every
content step into an `OpenStep` or `External` slot (a grep for `OpenStep` and `External` in the file lists them).

### 5.1 The template, filled in

| API concept | Navier-Stokes | in Lean |
|---|---|---|
| well-defined input | route I: the perturbation states, the period map, the size (rescaled `Ḣ^1`), `rho`, `C`, a ball radius `delta` with `rho + C delta < 1`; route II: an `EulerProfileCertificate` and a trajectory; regularity: a chain over dyadic scales; the tie: the statement interface | `DSSInput`, `RouteIInput`, `DyadicInput`, `ABInterface` |
| running system (`RunSys 0`) | route I: states in the ball, step = one period, factor `rho + C size` in `[0, 1]`, mass = the perturbation size; the ledger law is the open step | `system`, `contracting` |
| chain (`Chain delta`) | regularity: the quantity carried to dyadic scale `2^{-k}`, cost = share dissipated per scale, floor = share the transfer adds back | `regularity` |
| uncertainty (`Uncertainty 0`) | route II: the perturbation, factor `q + C M`, fresh uncertainty = profile residual plus the viscous term | `eulerUncertainty`, `routeII_bounded` |
| encoder | not used: the factors come from the period map's estimate, not from a reflection coefficient | |
| open-step slot | route I: `PeriodContraction` (one period contracts the perturbation); regularity: a uniform dissipation cost per dyadic scale above the transfer floor; the tie: the certificate | `PeriodContraction`, `regularity`, `abProblem` |
| external-input slot | Alpoge-Buckmaster's Theorems 7.1 and 1.1 and their Lean library | `ABInterface.thm71`, `thm11`, `formal` |
| computable layer | the window decision; the settle count `balanceBound` | `windowQ`, `windowQ_correct`, `settles_by` |
| problem cards | route I, regularity, the external tie | `routeI`, `regularity`, `abProblem` |

### 5.2 What the API answers, mechanically

**(a) Which window** [Lean, runs]. `windowQ` sorts a rational exponent into `aboveViscous`, `leray`, `typeII` or
`belowEnergy`.
- `#eval windowQ (1/2)` prints `leray` when the file is checked, and three `#guard`s check one exponent per other window.
- `windowQ_correct` proves the computed answer right. The decision says "inside" exactly when the real viscous floor and
  the local energy are bounded (`Admissible`, via `ns_window`). It says "Leray" exactly when the Type I bound holds as well
  (`TypeI`, via `ns_typeI_iff`).

This follows the API's rule for a new instance (`API.md` section 6): the decision runs, and a theorem proves it right for
the real statement.

**(b) Regular?** The `regularity` card [Lean]: from its open step (`CostAboveFloor` of the dyadic costs over the
transfer floor), the API's `Chain.decay` and `Chain.summable` give a positive decay rate and a summable cascade. Reading
that conclusion as "regular" is a [reading]: geometric decay over dyadic scales is the ledger form of smoothness. The API
then shows that the energy ledger cannot fill the slot:
- `energy_cannot_fill` [Lean]: shares whose partial sums stay below the start energy never pay a uniform positive cost.
- `dyadic_supercritical` [Lean for the arithmetic; the scalings are the classical heuristic]: at scale `2^{-k}` the
  viscous cost grows like `nu 4^k`, and the transfer bound from energy alone (Bernstein) like `K 2^{5k/2}`. Whatever `nu`
  and `K > 0`, the bound overtakes the cost at some scale, gaining a factor `2^{k/2}` per scale. In two dimensions the same
  count gives `K 4^k`, the critical case, which is why 2D Navier-Stokes is regular [classical].

So the API leaves regularity **open**, and its slot names the missing content exactly: a per-scale cost from the true
nonlinearity. Tao's averaged model shows that this cost cannot come from the energy identity and the standard estimates.
If the 2026 claims hold, the slot cannot be filled at all for some data.

**(c) Blowup?** The `routeI` card [Lean]. In the Leray window the perturbation from a time-periodic profile is a running
system (`system`) in the contraction class (`contracting`, `theta = rho + C delta < 1`).
- The API's `settle_everywhere` answers that the perturbation comes within every `epsilon` of the profile.
- `settles_by` (the API's `settle0`) gives the count: from period `balanceBound M epsilon q` on, for any rational `q` with
  `rho + C delta <= q < 1`.
- **Settling in the zoomed frame is blowup in real time.** The card's conclusion adds, from the ledger skeleton, that the
  periods fill the finite time 1, that the `Ḣ^1` amplitude tends to infinity, and that the profile is not steady.

The one open step, `PeriodContraction`, is the content a certificate supplies.

Route II: `routeII_bounded` [Lean] uses the API's bounded transport, with viscosity as the fresh uncertainty:
`M n <= M 0 + 2 (epsilon + nu)/(1 - q)`.

**(d) The answer, in one line.** The API does not settle Navier-Stokes as regular: the energy ledger cannot fill that
slot. It settles blowup in the Leray window once one named slot is filled, the period contraction. That is exactly what the
Alpoge-Buckmaster certificate claims to supply (section 6) [Lean for the plumbing; claimed for the content].

A note on words: in the API, "settle" means the carried quantity dies out. For the regularity card that quantity is the
cascade, so settling means regular. For route I it is the perturbation from the blowup profile, so settling means blowup.
The two cards carry different quantities, so the same theorem answers opposite physical questions.

---

## 6. The Alpoge-Buckmaster tie-in: what they state, what is certified, and the audit list

### 6.1 Primary sources (read-only; nothing cloned into the repository, nothing vendored)

- **The paper:** L. Alpoge and T. Buckmaster, "Finite-time blow-up for the Navier-Stokes equations", 79 pages, version of
  20 November 2026, in their public GitHub repository (`tristanbuckmaster/navier-stokes`, folder `paper/`). No arXiv
  number found. Read this round: the abstract, sections 1.1 to 1.6, 2.2, 2.3, the start of 7.3, the start of 7.4
  (Theorem 7.1, Corollary 7.2), and the starts of B.1 and B.4.
- **The Lean library:** the same repository, folder `lean/`. About 2,270 files and 600,000 lines, Lean v4.33.1 with Mathlib.
  It has statement files with `sorry` in place of proofs, plus `Solution.lean`, paired by `comparator*.json` files that
  permit only `propext`, `Quot.sound`, `Classical.choice`. Read: the README only. Not built.
- **The certificate: not released** as of 2026-11-24. The paper gives its SHA-256 hash,
  `3f7a335b84b6c7631742cacc5343dfcd11cf72f5221ff79b2b9268790b4b22c5`, and says it "will be released soon".
- **The companion unforced Euler claim** (Alpoge, Buckmaster, Coiculescu; a 55-page PDF on the second author's page): not
  read.
- **Tao's blog post** of 20 November 2026: read.

### 6.2 What they state, what is proved where, what is certified

| item | statement | where | status |
|---|---|---|---|
| Theorem 1.1 (paper) | a profile (period `S`, isometry `R`, their (1.2) and (1.3)) gives smooth, compactly supported data on `R^3` and smooth data on `T^3` whose unforced solutions blow up at the Leray rate `(T - t)^{-1/4}` in `Ḣ^1`, stable in finite codimension | paper, sections 2 to 6 | [claimed] |
| Theorem 7.1 (paper) | a certificate (section 7.3) gives a profile near the approximate one, with isometry `I`; smoothness by Proposition 7.11, Type I by Chae-Wolf | paper, section 7 | [claimed] |
| Corollary 7.2 | a certificate gives the conclusions of Theorem 1.1 on `R^3` and `T^3` | paper | [claimed] |
| formal Theorem 1.1 | **no rate**. For every positive viscosity: a smooth, compactly supported, divergence-free datum on `R^3` from which no smooth solution of bounded energy exists for all time, and a smooth periodic datum from which no smooth solution with periodic velocity exists for all time. Stated "in the form in which an earlier version of this paper stated them" | their Lean (section 1.5) | [claimed]; not built here |
| formal Theorem 7.1 | a certificate gives a **weak** solution of the profile equation | their Lean | [claimed] |
| formal chain | the conclusion of formal Theorem 1.1 is derived from conditions on finitely many functions and numbers (Appendix B), not from estimates for every perturbation | their Lean | [claimed] |
| two derivation steps | "two steps of the derivation are proved in the formalization and not in this paper" | Lean only | [claimed]; to be identified |
| the certificate check | that the released data satisfy the Appendix B conditions: a rigorous interval computation (Arb through FLINT, 128 bits) | outside the formalisation, not in the repository | **unreleased** |
| paper vs Lean | "the proof given here no longer follows the Lean proof" (section 1.6): the prose was rewritten after a draft generated from the Lean proof | section 1.6 | noted |
| patch | the Lean statements of the cell layer were patched on 20 November, and the patched package was not rebuilt (README) | README | noted |

**How their profile avoids the no-go results** (from the paper's sections 1.1 and 1.2) [claimed]:
- **Necas-Ruzicka-Sverak and Tsai** exclude profiles independent of `s` (exactly self-similar). Their profile depends on
  `s`, periodically up to an isometry: it is discretely self-similar. Non-steadiness is even forced in their class: the
  profile's slices lie in `L^6`, where Tsai excludes steady ones.
- **Bradshaw-Tsai Open Problem 5.1** asks whether a nonzero backward discretely self-similar solution with the Type I
  bound exists. The certificate answers it, for one example.
- **Chae-Wolf and Pineau-Vicol** bound the period from below; the computed period is about `0.36`.
- **Escauriaza-Seregin-Sverak**: the field is bounded in weak `L^3` but not in `L^3`.
- **The axisymmetric Type I exclusion**: the profile is not axisymmetric. It has a discrete 19-fold symmetry about one axis
  and a half-turn about another, and these symmetries restrict the perturbations the estimates must cover.

### 6.3 The tie, in the API's shape [Lean for the plumbing]

- **`ABInterface`** names four statements: a certificate exists, a profile exists, Fefferman's (A), Fefferman's (B). It
  holds their three theorems as `External` fields:
  - `thm71`: a certificate gives a profile;
  - `thm11`: a profile gives not (A) and not (B);
  - `formal`: their Lean, in which the certificate conditions give not (A) and not (B).
- **`abProblem`** is the card. Its one open step is the certificate ("satisfies Appendix B; unreleased", with the hash).
  Its conclusion is `¬ ClayA ∧ ¬ ClayB`, proved by the `formal` field.
- **`ab_paper_route`** gives the same conclusion by the paper's route.

Nothing is an axiom. The four statements are named, not defined, because this library has no Navier-Stokes object (audit
item 1).

**The tie to our ledger.** `routeI` is the skeleton of the proof of their Theorem 1.1:
- their period map minus the free flow is compact, and the free flow pays `S/4` per period (`ns_free_flow_pays`);
- finitely many directions are removed by the datum, which leaves a contraction on the rest (`PeriodContraction`);
- from there the API's settle and the ledger skeleton give convergence to the profile, a finite blowup time and an
  unbounded amplitude.

Their certificate is what would discharge `PeriodContraction` in a real norm: their `Ḣ^1`, with the weight of their
(7.14) [reading for the identification].

### 6.4 Audit list: what discharges the external hypotheses by importing their result

Each item is a thing to check or do; none is done here. Everything stays [claimed] until the certificate is public and
checked.

1. **Statement identity.** Replace the four named statements of `ABInterface` by real definitions. For (A) and (B), use
   Google DeepMind's Formal Conjectures formalisation (the one OpenAI's forced proof was matched against) or their own
   statement files. Then check, in one environment, that their formal Theorem 1.1 has exactly the type `¬ (A) ∧ ¬ (B)` for
   the definitions used. The formal version has no rate and speaks of "bounded energy" on `R^3` and "periodic velocity" on
   `T^3`; compare it word by word with Fefferman's (A) (smooth, bounded energy, for all time) and (B).
2. **Version skew.** Theirs: Lean v4.33.1 with the Mathlib pinned in `lean/lakefile.toml`. Ours: Lean 4.34.0 with Mathlib
   v4.34.0. Either build the bridge file against theirs, or check the definitions it uses (smoothness on `R^3 x [0, T)`,
   derivatives, periodicity, divergence) in both versions.
3. **Rebuild after the patch.** The README says the 20 November patch was not rebuilt.
   - Build the library at the pinned commit and run the comparator.
   - Run `#print axioms` on the comparator statements ourselves; expect only `propext`, `Classical.choice`, `Quot.sound`.
   - Grep the library for `sorry`, `admit`, `native_decide`, `Lean.ofReduceBool`, `unsafe`, `implemented_by`, `extern`,
     and custom `elab`/`macro`/`notation` that could change what a statement means.
4. **The comparator files.** Read each `comparator*.json` and its statement file. Check that the statement file is the one
   the paper's abstract describes, that `Solution.lean` proves exactly that statement, and that the axiom whitelist is as
   stated.
5. **The certificate.** This is the step that today rests on one computation by the authors. When it is released:
   - check its SHA-256 against the hash above;
   - check that its data have the form of Appendix B.1: finite sums of harmonics with piecewise-polynomial coefficients and
     a radial phase, the constant weight `w = 50/39`, and the symmetry group with `m = 2`;
   - re-verify the Appendix B conditions with an **independent** interval implementation: the multiplier inequality
     (B.2), the cells, their complement and the tree (B.3), and the norm bounds of B.4 (Lemma B.9 and after). Start with
     the cheapest scalar inequalities.
6. **The Lean-only steps.** Identify the "two steps of the derivation proved in the formalization and not in this paper"
   (section 1.1) and read their Lean statements. They are part of the trust base, with no prose proof.
7. **Prose vs Lean.** The prose proof no longer follows the Lean proof (section 1.6). The audit's trust rests on the formal
   chain (Appendix B conditions give formal Theorem 1.1) plus the certificate check, not on the prose. The prose is where a
   referee's reading enters (Tao: a professional write-up is still needed). For OpenAI's forced proof, arXiv 2610.08144
   found lemma-level departures between the two; the same comparison is worth doing here.
8. **Weak versus smooth profile.** Formal Theorem 7.1 gives a weak profile; the paper's Proposition 7.11 proves smoothness,
   and Chae-Wolf gives the Type I bound. Check that the formal chain needs neither (it goes from the conditions to
   Theorem 1.1 directly), or that it proves what it needs.
9. **No-go consistency, our side.** Check the certificate's period against the Chae-Wolf / Pineau-Vicol lower bound with
   their constant, the non-steadiness, and the weak-`L^3` tail. These are consistency checks, not proofs.
10. **Trust base.** The three standard axioms are a statement about the proof term. What remains: the Lean kernel (an
    independent kernel replay, as for the Yang-Mills submission), Mathlib's definitions, and that the formal statement
    means Fefferman's statement (item 1).
11. **Import mechanics.** Project policy: cited and audited, not vendored. Use a separate lake workspace pinned by commit,
    building only a one-file bridge that fills `ABInterface` from their theorems; this keeps the main build untouched. The
    cost is their full build (600,000 lines; CPU-hours, memory-heavy), so run it on a machine chosen for that.
12. **Scope.** The tie gives not (A) and not (B), hence (C) and (D) with zero force. It says nothing about which data blow
    up beyond the finite-codimensional family near their profile, and nothing about continuation past the blowup time.

---

## 7. Status table

| item | statement | status |
|---|---|---|
| Clay (A)-(D) | (A), (B) regularity without force; (C), (D) breakdown, **with a force allowed** | [classical] |
| Leray rates | singular implies `norm(grad u)_{L^2} >= c (T* - t)^{-1/4}` | [classical] |
| NRS, Tsai | no exactly self-similar Leray blowup in `L^3`, `L^p` (p > 3), local energy | [classical] |
| ESS | bounded `L^3` excludes blowup; `L^3` must diverge (Seregin) | [classical] |
| CKN | singular set of zero 1D parabolic measure | [classical] |
| Tao 2016 | averaged NS keeps the energy identity and blows up | [classical] |
| Hou 2022 | axisymmetric NS, nearly self-similar, `10^7` vorticity growth at Leray-type rates; constant-viscosity regularises the degenerate-viscosity scenario | [external], numerical |
| OpenAI forced blowup | smooth compactly supported force, zero data, bounded energy, `L^infinity` blowup at `t = 1`; Clay (C), (D) as stated | [claimed]; Lean build record [external]; lemma-level mistranslations shown (2610.08144) [external] |
| Alpoge-Buckmaster unforced blowup | smooth compactly supported data on `R^3`, smooth data on `T^3`, no force; discretely self-similar Type I profile from a certificate; rate `(T - t)^{-1/4}` in `Ḣ^1`; finite-codimension stable | [claimed]; certificate unreleased (hash only) |
| the window | bounded viscous floor and bounded local energy exactly for `2/5 <= alpha <= 1/2` (`ns_window`) | [Lean] arithmetic; [classical] scalings |
| above the window | no one-scale certificate covers all steps (`ns_no_uniform_certificate`) | [Lean] |
| route I hypothesis | `LerayDSSCertificate`: non-steady periodic profile, size `A > 0`, period contraction `rho < 1` | [Lean] as a structure |
| route I consequence | geometric convergence, periods sum to `T* = 1`, `Ḣ^1` amplitude unbounded (`ns_blowup_of_dss`) | [Lean] skeleton; PDE inputs [claimed] |
| free flow ledger | cost `S/4` per period, floor 0 (`ns_free_flow_pays`); `rho` as `CostAboveFloor` (`ns_dss_costAboveFloor`) | [Lean]; the `e^{-s/4}` bound [classical] |
| route II hypothesis | `EulerProfileCertificate`: Chen-Hou certificate with `(1 - q)^2 >= 4 C (epsilon + nu)`, `2/5 <= alpha < 1/2` | [Lean] as a structure |
| route II consequence | trapped perturbation, finite `T*`, unbounded amplitude (`ns_blowup_of_euler_profile`) | [Lean] skeleton; no candidate [open] |
| viscosity as uncertainty | summable below Leray, bounded even at cost = floor; constant and unbounded at Leray | [Lean] |
| energy ledger | a summable budget pays no uniform cost (`ns_energy_identity_not_costAboveFloor`) | [Lean]; Tao [classical] |
| `BLOWUP.md` 4.2 | "needs an inviscid profile with `2/5 <= alpha < 1/2`" is route II only; route I is open in the no-go results and is the claimed route | correction, [reading] |
| DMP-native construction | beyond reach now (3D time-periodic profile, operator certificate at 128 bits); next step: map Appendix B to `LerayDSSCertificate`, re-verify the certificate when released | [reading] |
| completeness model | exists if blowup is unrefutable; may be nonstandard; does not answer Clay | [classical] |
| "not DMP-complete, hence blowup" | a reading of supercriticality; names the side the 2026 claims assert; proves nothing itself | [reading]; [open] as a theorem |
| API: window decision | `windowQ` runs; `windowQ_correct` proves it right against `ns_window` and `ns_typeI_iff` | [Lean] |
| API: regularity card | a uniform dissipation cost per dyadic scale above the transfer floor gives a summable cascade (`regularity`) | [Lean]; open step [open] |
| API: energy cannot fill it | `energy_cannot_fill`; `dyadic_supercritical` (the transfer bound outgrows the viscous cost by `2^{k/2}` per scale) | [Lean]; scalings [classical] |
| API: route I card | the period contraction gives settling onto the profile (API `settle`, count `balanceBound`), finite time, unbounded amplitude (`routeI`, `settles_by`) | [Lean]; open step = the certificate's content |
| API: route II | viscosity as the fresh uncertainty, `M n <= M 0 + 2 (epsilon + nu)/(1 - q)` (`routeII_bounded`) | [Lean] |
| external tie | `ABInterface` (three `External` fields), `abProblem` (open step: the unreleased certificate), `ab_paper_route` | [Lean] plumbing; content [claimed] |
| audit list | 12 items (section 6.4), none done | to do |
| Clay problem | not advanced by this round | unchanged here |

---

## 8. Files

| file | content |
|---|---|
| `ProofPhase/Unified/NavierStokes.lean` | `nsViscous`, `nsViscous_nonneg`, `nsViscous_half`, `nsViscous_le`, `nsViscous_tendsto_atTop`, `nsViscous_bounded_iff`, `nsViscous_summable`, `ns_energy_window`, `ns_typeI_iff`, `ns_window`, `ns_no_uniform_certificate`, `EulerProfileCertificate`, `ns_blowup_of_euler_profile`, `ns_euler_gap_of_costAboveFloor`, `ns_viscous_transport_bounded`, `ns_viscous_transport_unbounded_at_leray`, `LerayDSSCertificate`, `LerayDSSCertificate.not_steady`, `ns_free_flow_pays`, `ns_dss_costAboveFloor`, `ns_dss_converge`, `nsPeriodLength`, `ns_period_hasSum`, `ns_dss_amplitude`, `ns_blowup_of_dss`, `ns_energy_budget_not_costAboveFloor`, `ns_energy_identity_not_costAboveFloor` |
| `ProofPhase/Unified/NavierStokesAPI.lean` (namespace `ProofPhase.API.NavierStokes`) | `Window`, `windowQ`, `Admissible`, `TypeI`, `windowQ_admissible_iff`, `windowQ_leray_iff`, `windowQ_half`, `windowQ_correct`, `DSSInput`, `PeriodContraction`, `Ball`, `fac_le`, `per_le`, `system`, `contracting`, `toY`, `system_iter`, `settles_by`, `RouteIInput`, `routeI`, `eulerUncertainty`, `routeII_bounded`, `DyadicInput`, `regularity`, `energy_cannot_fill`, `dyadic_supercritical`, `ABInterface`, `abProblem`, `ab_paper_route` |
| `docs/unified/navierstokes-axioms.sh`, `navierstokes-axioms.log` | build of both modules, `#print axioms` for all 56 declarations (52 on the three standard axioms, 4 on none), source grep |

Imported, not edited: `ProofPhase/Unified/Blowup.lean` (`blowup_of_certificate`, `gap_of_costAboveFloor`, `durations`),
`ProofPhase/Unified/Transport.lean` (`critAcc`, `critical_bounded_iff`, `critical_unbounded`),
`ProofPhase/Unified/Ledger.lean` (`Pays`, `CostAboveFloor`), `ProofPhase/API.lean` (`RunSys`, `Chain`, `Uncertainty`,
`Problem`, `OpenStep`, `External`, `settle_everywhere`, `settle0`, `balanceBound`).

Sources consulted this round (2026-11-24):
- Read in full text for the cited parts: Alpoge-Buckmaster, abstract, sections 1.1 to 1.6, 2.2, 2.3, and the starts of
  7.3, 7.4, B.1 and B.4 (the PDF in their repository); OpenAI, abstract, Theorem 1.1 and section 1.1 (the PDF linked from the announcement); Lei-Ren Part I,
  abstract and sections 1.1 and 2.2.
- Read as abstract or landing pages: arXiv 2611.06869, 2610.08144 (with its HTML sections 1 to 3), 2609.23868, 2609.26790,
  2610.06544, 2411.13896, 2604.16842, 2107.06509, 2102.06663, 1402.0290; the Zenodo build record of OpenAI's Lean proof;
  OpenAI's announcement page; the Alpoge-Buckmaster repository README; Tao's blog post of 20 November 2026.
- Press reports (not relied on for facts the papers state): news coverage of the 20 November claim.
- Recalled, not re-checked: the publication data of NRS, Tsai, CKN, ESS, Seregin, the axisymmetric Type I results, and
  Shoenfield absoluteness.
