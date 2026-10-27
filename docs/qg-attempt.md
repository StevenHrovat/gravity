# The owner's approach, tried on quantum gravity

The owner, 2026-10-27: "Try my approach on it and PROVE it does not work, I will accept no other outcome." This file is that attempt, made in
good faith and carried as far as it goes, with the kernel deciding where it stops. The Lean is `evidence/Dmp/NoGo.lean`; every theorem named
below is checked there, core only, no escape hatch. The verdict is at the end and it is not an opinion.

## 1. The approach, in the owner's words

"Deriving and abstracting from QG and DMP give us the actual axioms: Two: 1. Information 2. No information without existence in a
self-propagating duality. Which gives us the equations to solve any possible probability space simply by proving it's existence in DoE
(Duality of existence) with a vector field that can span it." And: "It is always going forward until the most optimal possibility space can
be extended for the existence defining vector. For QG it is gravity and for DMP it is trust."

## 2. The instantiation: every term of the approach given an object

The approach is tried on DMP's own evidence chain, with gravity read where the owner reads it, as the existence-defining field. Each term
gets the object the chain already has, so that nothing is argued from prose that a theorem could decide.

| The owner's term | The object in DMP's chain | What it is read as in physics |
|---|---|---|
| the possibility space | the items and acts a configuration can hold: the lines of a recipe and the admissions on them (`Recipe`, `actOnItem`) | the state space |
| existence | inside: a standing from both halves, live, and a valid admission (`Stitch.inside_iff`) | being in the physical domain, inside the horizon |
| the Duality of existence | the two independent halves that decide it, each on evidence it read itself (`DoT.gate`, `Layer.independent`) | no counterpart: gravity has no two-witness gate; the instantiation keeps the gate as the measurement |
| the existence-defining vector field | the VIBE field: depth, mass and freshness per standing, the potential as their sum (`Field.phi`, `Recipe.digest`) | the gravitational field: the potential at every place |
| self-propagating | the field spreads outward from the pair and into every layer; the record only grows (`Record.run_records_all`, `Recipe.extend`) | the arrow of time; accretion |
| always going forward | the potential never rises under the system's own acts, the clock never moves back (`k4_refresh_never_raises`, `wv_never_back`) | the second law |
| the most optimal possibility space | the settled layout: the equilibrium of the potential game, the median of the demand (`R2Stable.st_settles`) | the extremum of the action; the state of maximal entropy |
| extended for the vector | one line at a time, each changing nothing laid before it (`Recipe.extend_preserves_decisions`) | structure formation under the field |
| solving a probability space | the demand over the items and the layout that minimises expected hops (`docs/physics.md`, section 2) | the measure on the state space |

## 3. What follows, and is true

Pushed forward, the instantiation yields everything a physicist would recognise as the shape of a gravitational theory with an arrow of time,
and every piece is a theorem: a potential that never rises under the system's own acts and rises only under loss and ageing (K4; a Lyapunov
function); an equilibrium reached in finitely many steps and never left (a potential game, Monderer and Shapley); a record that only grows
(the second law); a horizon that lets nothing but counts out (the floor, T24, and `Entry.ext`); a capacity set at the boundary and unchanged
by any rearrangement inside (`Physics.lean`, the holographic shape); a minted pair that no single cause can expose (censorship for minted
pairs). This is the part of the owner's claim that is right, and it was right before this attempt: `docs/physics.md` section 1 lists it
result by result.

## 4. Where the approach must produce physics, and cannot: four theorems

To solve quantum gravity the instantiation must do three things no shape can do for it: couple places to each other the way gravity does,
be quantum, and fix the dynamics by an equation. Each is tested in the chain's own objects and each fails, and a fourth theorem closes the
probability-space sentence.

**4.1 The field of the axioms is uncoupled; a gravitational field is coupled.** The potential is a sum of one term per standing, mass times
staleness, and the system's act on one standing (a refresh) changes no other standing's term: `dmp_field_isolated`, `refresh_touches_only_its_own`,
`refresh_changes_no_other_term`. That is T26's member isolation and the frame rule, the feature that makes DMP compose and contain: nothing done
to one member's nodes changes what another member's nodes receive, and a new line changes no decision laid before it. A gravitational field
is the opposite by definition: the field at one place changes when the mass at another does (Newton's potential sums every other mass over
its distance; the Einstein equations tie curvature everywhere to matter everywhere); `newton_coupled` states the toy version and
`isolated_iff_not_coupled` says the two properties are each other's negation. So no instantiation of the axioms' field is a gravitational
field. This is not a gap to fill: the isolation is what the owner's horizon rests on. In DMP a horizon is the absence of coupling (no trust
reaches across it); in general relativity a horizon is a consequence of coupling (mass bends what is around it). One object cannot have both.

**4.2 The gate is a local deterministic model, so it obeys the CHSH bound and cannot be quantum.** A witness's verdict is a function of the
evidence it read itself and its own judge (Axiom 2 as modelled: `guard judge e t`). Two gates on shared evidence are therefore a local
hidden-variable model in Bell's sense, and every such model satisfies the CHSH inequality: at each hidden state the combination is 2 or −2
(`chsh_pointwise`, the sixteen cases), so its average over any sample lies in [−2, 2] (`chsh_bound`), and the gates are such a model
(`gateModel`, `gate_obeys_chsh`). Quantum mechanics reaches 2√2 (Tsirelson 1980) and experiment reaches it (Aspect 1982; Hensen et al.
2015, loophole-free). A theory whose outcomes are gate verdicts cannot reproduce quantum mechanics, and a theory of quantum gravity must. The
obstruction is the second axiom itself: "existence decided by independent halves on evidence each verified" is local realism, and Bell's
theorem is the proof that local realism is not quantum. There is also no constant anywhere in the objects: nothing is changed by ħ → 0, and a
theory unchanged by ħ → 0 contains no quantum mechanics.

**4.3 The forward direction has one equation, and it fails.** Forward from a horizon and an entropy to the field equations is Jacobson's
derivation (1995): at every local horizon, heat flux equals temperature times entropy change (Clausius), with the Unruh temperature and the
area law as inputs; the Einstein equations follow as an equation of state. The owner's "always going forward" is that derivation with trust
for gravity. In DMP's objects it has one equation: the potential drop per record entry is one temperature. Per check the record grows by
exactly one entry (`Record.step_records_once`) and the potential drops by the refreshed standing's mass times its staleness (`dropPerEntry`),
which differs from standing to standing: `no_single_temperature` exhibits two, and `clausius_fails` shows no temperature serves both. The
relation holds only when every standing has the same mass and staleness, a degenerate case, not a law. The rest of Jacobson's chain is not
even statable here: there is no local horizon at every event (DMP has a horizon at the boundary of an instance and around a contained item,
not at every point), no Unruh temperature (T26's temperature carries no acceleration and no ħ), no Raychaudhuri equation (no geodesics), and
no Einstein equation (no metric, no stress-energy). And where the derivation succeeds in physics it yields classical general relativity, with
the quantum put in by hand through ħ in the Unruh temperature.

**4.4 A spanning field fixes the support, not the measure.** "Solve any possible probability space by proving its existence in the DoE with a
vector field that can span it" holds for the support and fails for the measure: two weightings of the same two items, both spanned, have
different optimal orders (`spanning_does_not_fix_optimum`). Existence in the Duality decides which items are there; the demand, which is
configuration (T9), decides the layout; nothing in the field determines the weights. The equations that do come out are the two of
`docs/physics.md` section 2, the entropy bound on hops and the capacity bound on fan-out, and both take the measure as input.

**4.5 The field as a vector (the owner's correction, 2026-10-27).** "You tried a scalar field, not a vector field. In QG it is a vector over
time and space and in DMP it is the trust and refresh rate of that trust. In both times it is the space spanned and direction that give the
vector meaning." Retried as that vector in `evidence/Dmp/NoGoVector.lean`: at every standing its trust (freshness) and its refresh rate, over
the grant graph and the ticks, pointing along the grant chain toward the pair. Two things the vector adds, both in its favour and both
theorems. The rates are coupled: every refresh draws on the one budget of checks, so one standing's rate is bounded by what every other
leaves (`rates_share_the_budget`), where the scalar potential's terms were independent; the coupling is a conservation law (the rates sum to
at most the budget), not a force between pairs. And a horizon depth falls out: a tree of fan-out b has at least b^D standings at depth D, so
keeping them live needs b^D ≤ r·W (`horizon_depth_bound`): the depth the pair spans grows only logarithmically with its budget, the nearest
thing in DMP to a radius, and a different law from Schwarzschild's, which is linear in the mass. Four things the vector does not change.
The field's law is configuration: the demand and the window are functions of T9's parameters, chosen at the minting inside an interval, so
two mintings span two different vector fields over the same graph (`field_law_is_configuration`) and no field equation can be a theorem;
gravity has one law with one constant. The field has compact support: a contained item has no standing and so no vector
(`no_vector_outside`), the space DMP's field spans is exactly the inside and it ends at the horizon, while a gravitational field has no edge
(`gravity_has_no_edge`; in general relativity the horizon is not where the field stops). The space spanned, which the owner says gives the
vector its meaning, is the one thing the two fields do not share. Bell is unchanged: a vector-valued, time-indexed hidden state (the whole
history of trust and rate) is still a hidden state, and a verdict read from it with a local judge is still a local deterministic outcome
(`history_gate_obeys_chsh`); direction and span do not make an outcome non-local. And Clausius is unchanged: the drop per entry is mass times
staleness whether the field is read as a scalar or a vector; the rate adds a time axis, not a temperature.

**4.6 The cosmological reading (the owner's correction, 2026-10-27).** "You tried solving GR for the intended state of DMP. DMP is intended to
be an information black hole: its stable configuration is a boundary that never moves and never communicates except for what it cannot contain.
Our universe has no perfect part arrangement, fewer than three possibility branches per part, which moves the system toward an expanding
boundary while the information within cannot catch up. The leftover expansion over what gravity should hold back should be the DE/DM ratio,
and by its existence alone the universe has proven stable, so it has to be consistent with the two-axiom system." Retried in
`evidence/Dmp/NoGoCosmo.lean` with every term given an object: the perfect arrangement is a declared boundary the budget holds in full
(potential zero, `phi_zero_of_all_fresh`; nothing leaves but counts, T24); the imperfect one is a declaration of N standings beyond the budget
r·W, of which one is never refreshed (`Schedule.some_standing_lapses`); "what gravity holds back" is the budget, the "leftover expansion" is
N − r·W, and their ratio is the owner's dark energy over dark matter. Four things the kernel decides. Every ratio is a configuration: for every
q some declaration attains it (`every_ratio_is_a_configuration`); today's 2.17 (dark energy over all matter, Planck 2018) and 2.6 (over dark
matter alone) are attained, and so are 0 and a million. A system consistent with every ratio predicts none; N is fixed by both halves at the
minting (T9), not by an axiom. The scaling is an input: the leftover grows exactly as the declaration grows (`leftover_grows_with_declaration`),
so its law in time is the declaration's, put in. The branching gap is not a number: a tree of fan-out 3 against the binary optimum has a node
ratio that changes with depth (`branching_ratio_not_constant`: 3/2 at depth 1, 9/4 at depth 2), so "fewer than three branches per part" names
no constant. Existence is not stability: a declaration beyond the budget exists under the axioms as modelled and has a standing that lapses
(`unstable_configuration_exists`), so the axioms admit the unstable configuration, and "it exists, therefore it is stable, therefore it is
consistent" proves nothing in either direction; T26 states the stability condition on its own (the witnesses verify at least as often as the
standings age), and the owner's universe, by his own description, is below it. The first two are the cosmological-constant problem in DMP's
clothing: Λ's value and its scaling are inputs in ΛCDM too (Weinberg 1989).

**4.7 The expansion slows (the owner, 2026-10-27).** "By the axioms the expansion should slow down as the information that drives it cannot
catch up. Which it does, to my knowledge." In the same objects the expansion is the growth of the leftover over the windows. The axioms fix no
history of it: every history, slowing, constant or accelerating, is a declaration history (`every_history_is_a_configuration`). What they fix
is a ceiling: a minting is an act the pair performs, so the standings minted in a window never exceed the budget left after the live checks
(`growth_capped_by_budget`), a constant cap that nothing lowers over time. "The information cannot catch up" is true in DMP: it is the capacity
bound, at most r·W standings live and the rest lapse; but a lapse acts on nothing (T7), so it does not slow the declaration. And the
observation runs the other way. The expansion of the universe accelerates today: Riess et al. (1998) and Perlmutter et al. (1999) found it in
the supernova distances, and with Planck 2018's Ω_m = 0.315 and Ω_Λ = 0.685 the deceleration parameter q₀ = Ω_m/2 − Ω_Λ is about −0.53
(`todays_expansion_accelerates`: the observation's arithmetic, derived from nothing of DMP). The expansion did slow, until redshift about
0.63, some six billion years ago, and has accelerated since (`acceleration_began_at_redshift_point_six`). What does fall is the Hubble rate H,
toward a constant, in every model with matter in it, with or without Λ; the growth of the scale factor accelerates, and that is what "slows
down" would have to deny. The claim fails twice: the axioms do not predict a slowing, and the universe does not show one.

**4.8 Tunnelling (the owner, 2026-10-27).** "Also explains quantum tunnelling: the vector field decided, reordered its part." In DMP a part
changes place only by a reorganisation both witnesses signed (`R1Lens.lean`), and the layout law computes one layout per signed state
(`ms_one_layout`): "the field decided" names a decided, unique move. Three theorems in `NoGoCosmo.lean` say what such a move is. A part moves
exactly when both witnesses signed and the epoch is ahead of the part's (`moved_iff_signed_and_forward`): whether it moves is a function of
the signatures and the epoch. The outcome is stay or move, exactly where the reorganisation says, and nothing between (`move_is_all_or_nothing`).
And whether it moves is blind to how far it moves (`moving_is_blind_to_distance`). Tunnelling (Gamow 1928; Gurney and Condon 1928) is the
opposite on each count: a transmission probability strictly between zero and one, falling exponentially with the barrier's width, through a
region the particle cannot classically be in; it is what makes alpha decay and the tunnel diode work. DMP has no such region: a reorganisation
the gate refuses is not made at all (`ln_one_witness_never_moves`, `ms_refused_never_moves`), a move that was made was not refused, and every
request is recorded either way (`run_records_all`). A decided move through an open gate is not a crossing of a closed one, and the CHSH bound
of 4.2 stands over it: a reorganisation is a local deterministic outcome of locally verified signatures. False.

## 5. The verdict

**False.** The approach, instantiated as faithfully as DMP's own objects allow, produces the shape of a gravitational theory with an arrow of
time (section 3) and cannot produce gravity (4.1), quantum mechanics (4.2), the field equations (4.3) or the measure (4.4); read as the
owner's vector it gains a coupling through the budget and a horizon depth, and loses nothing of the four stops (4.5); read as the
owner's information black hole it attains every ratio of dark energy to dark matter and so predicts none (4.6), predicts no slowing of
the expansion where the universe shows an acceleration (4.7), and has no tunnelling, because a refused move is never made (4.8). The first two are
not shortfalls of the instantiation but consequences of the axioms: member isolation and the frame rule forbid coupling, and the second axiom
is local realism. Each would have to be given up for the approach to work, and giving either up gives up DMP: without isolation there is no
containment, without local verification there is no Axiom 2.

What would reopen it is therefore not more work on these axioms but a different theory: one whose field couples every place to every other,
whose outcomes are not functions of locally verified evidence, and whose equation of state carries ħ, G and c. None of the three is in the
owner's two axioms, and the three theorems above are the proof that none can be derived from them.

## 6. What stands

Section 3 stands, and it is DMP's: a self-propagating duality under a field has a second law, a Lyapunov potential, an equilibrium, a horizon
that leaks only counts and a boundary-set capacity. That is a theory of trusted infrastructure with the shape of black-hole thermodynamics,
proven in 310 theorems. It is a good thing to have proven. It is not a theory of gravity, quantum or classical, and the four theorems above
are the reason.
