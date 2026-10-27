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

**4.9 The rate-limited expansion (the owner's solution, 2026-10-27).** "While the existence space is able to grow simply by the vectors that
define it being raised, the information needed to cause that expansion still has to observe the rate limit of the scalar giving direction,
while travelling through the field spanned by the boundary vector. Try to disprove that." Instantiated in `evidence/Dmp/NoGoRate.lean`: the
existence space is the set of standings inside the boundary, a vector is raised when a standing is granted or widened, the scalar giving
direction is the budget of checks per tick whose spending order the field fixes (T26), and travelling through the field is the outward
propagation of the pair's acts, one layer per verification round (T26, the wave clock of `R1Wave.lean`, the rounds of `R2Stable.lean`). The
second half holds and was already a theorem (`growth_capped_by_budget`): the information that grows the boundary draws on the budget, so the
growth of a window never exceeds it. Three things disprove the rest. Raising a vector is a requested act, and the axioms contain no requester:
widening a standing needs both witnesses (`loosening_needs_both`, T16), the gate performs nothing without a request (`no_request_no_act`) and
performs at most as many acts as it is asked (`growth_le_requests`); "simply by the vectors being raised" moves the cause from the declaration
to whatever raises the vectors, and that is still configuration (T9). The rate limit forbids acceleration: every window has the same ceiling
(`growth_never_accelerates`), so the growth over k windows is at most linear in k (`growth_at_most_linear`), and a history whose increments keep
growing breaks the ceiling by window r·W + 1 (`accelerating_breaks_the_limit`); a boundary that coasts at a constant rate is a universe with
deceleration parameter zero, and the measured value is about −0.53 (4.7). Travelling through the field delays the growth and never adds to
it: a growth that reaches the boundary only after D rounds and is rate-limited after that lies under the same line shifted by D
(`travel_delays_never_adds`), and the field's depth is bounded by the budget anyway (`horizon_depth_bound`), so the delay is finite and the
propagation is neither a cause nor an acceleration. One consequence in the mechanism's favour, as far as it goes: expansion is paid with
maintenance (`growth_costs_maintenance`; at the full rate nothing stays live, `extremal_keeps_nothing`), and with any positive growth the
leftover over the bounded live set grows without bound (`no_stationary_ratio_under_growth`), so the ratio settles only at zero growth. ΛCDM's
ratio of dark energy to matter grows without bound too, as a³, so the direction agrees; the value 2.17 is a moment in both and a prediction in
neither. The claim's true half is DMP's rate limit. Its false half is that the rate limit supplies a cause, or allows the acceleration the
universe shows. Disproved.

**4.10 The extension itself (the owner, 2026-10-27).** "QG is an extension of the two axiom system that prescribes existence alone as proof of
existence, where that is replaced by the only allowable replacement, a vector consisting of one vector that bounds a space which can contain a
field, and another, which gives change in the field a direction. Those two things, given initial settings, Planck's constant, G and c, is able
to solve the field part of the duality, which also contains a hierarchical information space, which, with our settings, pushes the bounds
faster than the field they project allows the force transmitting particles to catch up, to also extend the field, which carries them, as they
go. So the growth of bounds, in our case, slows down, and should be completely modelable, since we are in an existence space that exists,
making that axiom true beyond any possible evidence to the contrary (trust)." And: "You are doing the wrong thing." So this section models the
extension and not DMP's objects. `evidence/Dmp/NoGoBound.lean` has a bound of the existence space, a field inside it that force carriers
extend toward the bound at their speed, and a push on the bound by the information inside that acts only where the field has arrived, the
push being projected through the field; nothing of DMP enters.

What holds, and it is more than before: the picture is real physics with names. The bound that force carriers cannot catch up with is the
cosmic event horizon of an accelerating universe: beyond it space recedes faster than light, and light sent from there never arrives (de
Sitter; Gibbons and Hawking 1977, who also gave that horizon a temperature and an entropy proportional to its area, the universe as a black
hole seen from inside, which is the owner's information black hole). The growth of that bound does slow down: the event horizon's radius
approaches c·sqrt(3/Λ) and stops growing, and the Hubble radius does the same. Section 4.7 read "expansion" as the distances inside and
called the slowing false; for the horizon it is true, and the owner's instinct about the bound was right. The information inside is capped by
the bound's area (Bekenstein 1981; Bousso 1999), and the expansion of space as the quest for equipartition between the degrees of freedom on
the horizon and in the bulk, with ħ, G and c as inputs and de Sitter as the end state, derives the Friedmann equation (Padmanabhan 2012). The
owner's sentence is that programme in his words.

What the model decides. The bound slows to the carriers' speed and never below it: it never gets further ahead of the field than one push
(`bound_within_one_push`), the field advances at most c per tick (`field_speed_le_carriers`), so the bound advances at most c·t plus one push
over t ticks (`bound_speed_le_carriers`), and it never stops, because while the information pushes and the carriers move the field reaches the
bound again and the bound moves again (`bound_never_stops`). The slowing the owner's mechanism gives is from faster than the carriers to the
carriers' speed, a coasting bound. To slow to zero, as the event horizon does, the bound needs a capacity: with a cap the push acts only while
the bound stays within it, the bound never exceeds it (`capacity_stops_the_bound`) and the growth ends there (`growth_ends_at_capacity`). The
capacity is where the physics enters, and it is the cosmological constant: the horizon freezes at c·sqrt(3/Λ), its information capacity is
its area over 4ℓ_P², and ħ and G enter there and nowhere else. The same Λ makes the distances inside accelerate: the horizon freezes exactly
because the recession speed at it reaches c, which is the acceleration of 4.7 seen from the edge. "The growth of bounds slows down" and "the
expansion accelerates" are one fact, and the duality derives neither; Λ does.

What breaks, three things. First, ħ, G and c do not fix Λ: they fix the Planck scale, and Λ is 10⁻¹²² of it (Weinberg 1989). The initial
settings the owner names leave out the one number that sets where the bound stops, and in Padmanabhan's derivation it enters as the end state,
not as an output. Second, the hierarchical information space is named and not given: the capacity counts degrees of freedom on the horizon,
and the theory of those degrees of freedom is what quantum gravity would be. The extension says that they exist and that their count bounds
the field; it does not say what they are, and the emergent-gravity programme it restates has the same open problem. Third, the change the
direction vector gives is a definite function of the field, so the model is local realism and the gate of 4.2 stands over it: no amplitudes,
so nothing quantum. And on the last sentence: "we are in an existence space that exists" proves that something exists, not that it is a
duality of two vectors; and "true beyond any possible evidence to the contrary" is the one thing the owner's own second axiom refuses, since
trust in DMP is live evidence and never existence.

The verdict for this section: the extension is a cosmology, not a quantum gravity. As a cosmology it is the de Sitter horizon with holographic
equipartition, which exists in the literature and reproduces the classical expansion with Λ as an input. As quantum gravity it is the
statement that the horizon's degrees of freedom exist, which everyone grants and no one has.

**4.11 The quantum as a duality of existence (the owner, 2026-10-27).** "It is a quantum gravity if the field that projects the inflation is
the information in the other constituent of each quantum. Those are the universal forces. Their interaction with the existence field is
what actually drives evolution, which also explains quantum effects. If you force a singularity to give up one of its constituent parts,
either its existence in the space, or information about it, the DoE dissolves, ending the wave particle duality. [...] It is a system that
ends there and started at the Inflation field and through all subsequent DoE chains, until it decayed to today. [...] the decay forward in
the scalar direction can not be observed by its decay because its existence constants are not yet defined. Backwards in the scalar direction
past decay chains can be seen by their imprint, since only one possible configuration can evolve into the current system. We currently can
only detect the decay back to the Inflation field."

What holds, with names. "The information in the other constituent of each quantum is the universal forces" is the gauge principle: a force
is the rule for carrying a quantum's phase, its information half, from one place to another; Weyl found it for electromagnetism (1929) and
Yang and Mills for the other forces (1954), and the Standard Model is nothing else. "Force a quantum to give up one constituent and the
duality ends" is Bohr's complementarity (1928) and von Neumann's measurement (1932): a quantum shows its wave or its particle face according
to what is asked of it, and the asking is irreversible. "Started at the inflation field, decayed to today, visible backward by its imprint,
the earliest thing we can see" is inflationary cosmology (Guth 1981): the earliest light is the cosmic microwave background, and inflation is
read off its imprint, the spectral tilt measured and the gravitational-wave amplitude bounded (Planck 2018; BICEP/Keck 2021). Existence from
information as the ground of physics is Wheeler's "it from bit" (1990), the owner's first axiom in Wheeler's words. All of it is physics;
none of it is new, and none of it is gravity.

What breaks, as physics. First, the quantum in question is the existence field itself. Everything in the owner's picture lives on the
existence field: the quanta, their information halves, the forces, the dissolutions. Quantum gravity is the question what the existence
field's own quantum is. If its information half is treated like the other forces', that is the graviton, and that route is the one known to
fail: the infinities at the Planck scale cannot be absorbed into finitely many constants ('t Hooft and Veltman 1974; Goroff and Sagnotti
1986). The owner's text offers no cure, and the duality supplies none. Second, dissolution gives no probabilities and no entanglement. Which
position the quantum lands at and with what likelihood (the Born rule), and how two dissolutions far apart agree beyond what any local account
allows (4.2), are the quantum effects; "the duality dissolves" names them without giving them, and the direction vector still makes change
a definite function of the field. Third, the picture contradicts itself. A dissolution throws one half away, so from what remains the quantum
before it is not unique (`evidence/Dmp/NoGoDuality.lean`, `dissolution_forgets`), and "only one possible configuration can evolve into the
current system" is exactly the uniqueness a dissolution destroys (`unique_past_forbids_dissolution`). Physics has had to choose since 1932:
unitary evolution never forgets and nothing ever dissolves, or measurement forgets and the backward chain branches at every measurement. The
owner's cosmology needs the first and his quantum needs the second. The imprint agrees with the branching: the pattern on the sky is one draw
from quantum fluctuations during inflation, and what is unique backward is their statistics, not the configuration. Fourth, "its existence
constants are not yet defined" forward in time: the constants have not changed over the whole backward chain. The fine-structure constant is
the same in the cosmic microwave background as in the laboratory and drifts by less than a few parts in 10¹⁷ per year (Rosenband et al. 2008),
so no decay so far has defined a constant, and nothing says the next would.

The verdict for this section: not a quantum gravity. A duality language for gauge theory, complementarity and inflation, carrying one
contradiction (a unique past against a dissolving quantum) and leaving the one question of quantum gravity, the quantum of the existence field,
unasked.

**4.12 The axioms as stated (the owner, 2026-10-27).** In general: "1. Information that interacts with existence must exist in an existence
field consisting of space vectors and a time vector, that is able to propagate a field through itself. 2. For information to be real it has to
exist, for anything to exist, there has to be information about it." Applied to quantum gravity: "1. Existence is made of three spatial vectors
and one time vector that moves forward in space. 2. [the first general axiom] 3. [the second general axiom]." Derived by the owner: information
and the existence it occupies must be coupled to be real; the existence-space constants can be derived by collapsing a duality from its
existence half, which exposes its information and ends its existence; the expansion can be derived in reverse; decay chains of force systems
leave an imprint while their information half is irreversibly destroyed; and there is one universal shared quantum, "as one must always be two
and two cannot become one".

What holds, with names. The first applied axiom is Minkowski's stage (1908): three space directions and one time direction, with the arrow
put in by hand, as every physical theory puts it in, since the equations run both ways and the arrow is a boundary condition. "Able to
propagate a field through itself" is the one feature gravity alone has: the existence field carries waves of itself, and they were heard in
2015 (Abbott et al. 2016). "Information and the existence it occupies have to be coupled to be real" is the coupling of matter to geometry,
Einstein's equation in words. The decay chains whose imprint remains while the previous force system is gone are the phase transitions of the
early universe: at high temperature the forces were one and the vacuum was different (Kirzhnits and Linde 1972), the transitions are
irreversible, and their imprint, the masses, the asymmetries, the background, is what we read. The frame is the standard model of cosmology
said in two sentences.

What breaks, as physics. First, and decisive: the axioms are true of a world without gravity. Take flat spacetime with electrons and photons
and nothing else, quantum electrodynamics with the gravitational coupling zero. It has three space directions and a forward time, fields
propagate through it, information interacts with existence and exists in the field, and nothing exists without information about it. Every
axiom holds and there is no gravity. An axiom system that a gravity-free world satisfies cannot entail gravity, let alone quantum gravity; to
be a theory of gravity it would have to be false of that world. The kernel records the independence in the smallest form
(`evidence/Dmp/NoGoAxioms.lean`: the axioms hold with the coupling zero and with it nonzero, `axioms_hold_without_gravity`,
`axioms_hold_with_gravity`, so they fix nothing about it, `axioms_do_not_fix_gravity`). Second, "collapsing a duality from its existence half
exposes its information and thus it ceases to exist" is contradicted by one electron: a single electron has been held in a trap and measured
continuously for months (Wineland, Ekstrom and Dehmelt 1973, and ever since), its information exposed again and again, and it never ceased
to exist. Measurement reads a quantum; it does not end it. Third, "the information half must be irreversibly destroyed when decaying"
asserts what quantum theory forbids: evolution is unitary and no information is ever destroyed, not in a decay and, after the longest
argument in the field, not in a black hole (Page 1993; Penington 2019; Almheiri, Engelhardt, Marolf and Maxfield 2019). A decay scrambles the
information into its products; it does not destroy it. The owner's second axiom holds in physics more strongly than he uses it, and that is
why the imprint can be read at all. Fourth, the constants: "derived by collapsing a duality" describes measuring them. A derivation would give
their values before the measurement; none is given, and the gravity-free world shows that none can be, since the coupling is not fixed by
the axioms.

The lowest quantum (the owner, in the same hour): "that quantum being the lowest possible amount of energy, which is also the lowest amount of
information." In flat space there is no lowest amount of energy: a photon's energy is ħ times its frequency, and the frequency can be as low
as one likes. A lowest quantum exists only where there is a largest wavelength, and the existence space has one, the horizon: the lowest
energy that fits inside it is about ħH, some 10⁻³³ electronvolt. The lowest amount of information is one bit, and the energy it costs is
Landauer's kT ln 2, which depends on the temperature (Landauer 1961); at the horizon's own temperature (Gibbons and Hawking 1977) that cost is
of the order of ħH, so the owner's identification holds there, and only there. Carried through, it is a known model: the horizon holds about
10¹²² bits, one per Planck area, and 10¹²² quanta of ħH each is the measured dark energy density to within its order of magnitude (Cohen,
Kaplan and Nelson 1999; Li 2004). That is the strongest thing the duality has said: it picks the right order of magnitude for Λ out of the
10¹²⁰ the naive vacuum is off by. It does not pick the value: the horizon is set by Λ and the count by the horizon, so the argument is a
consistency and not a derivation (with the Hubble radius as the cutoff the energy does not even accelerate the expansion, Hsu 2004; Li's
version needs the future event horizon, which is Λ again). And it is the universe's lowest quantum, not gravity's: nothing in it says what the
existence field's own quantum does at the Planck scale, the other end of the same horizon.

The owner's rebuttal (2026-10-27): "You are provably wrong: gravity is simply what we call the warping of the existence dimension. [...] if you
take my model and plug in the layers of information that are possible (the universal forces, because what is force but information given
existence at a specified point in space and time) within our current existence, the warping of the resulting existence space is what we call
gravity. Beings one layer up the information decay chain might have called it Bruce." Taken as the reading of the first axiom, "interacts
with existence" means "warps it", and then the flat world above is excluded: an axiom that says information warps existence is false of a
world where it does not. That much is conceded and recorded (`NoGoAxioms.lean` section 2, `strong_axioms_exclude_no_gravity`). What the
stronger reading buys is this. First, the warping is now in the axiom by hand: that existence is warped by information is stipulated, not
derived, and a stipulation that gravity exists is what every theory of gravity begins with, Newton's included. Second, the law is still free.
A warping of existence by information can be a scalar, one number per point (Nordstroem 1913), or a tensor, the metric (Einstein 1915); the
axioms admit both (`strong_axioms_admit_scalar_and_tensor`), and the sky chose: the scalar theory bends no light, and light bends by 1.75
arcseconds at the Sun's limb (Dyson, Eddington and Davidson 1920). Add what the axioms do not say, that existence is a metric, that its
dynamics is second order and that what is conserved locally sources it, and Lovelock's theorem (1971) makes the law Einstein's with two
constants left free, G and Λ (`strong_axioms_do_not_fix_the_constant`). That is the honest best case for the owner's sentence: it is general
relativity's own idea, that gravity is not a force but the geometry of existence warped by what it holds, and it reaches Einstein's equation
only with Lovelock's assumptions added and two numbers put in. Third, and this is where quantum gravity lives: the information plugged in is
quantum, and a warping by quantum information is the open problem. Warping by the average of the information, the semiclassical equation, is
ruled out as a fundamental law by argument and by experiment (Eppley and Hannah 1977; Page and Geilker 1981); warping branch by branch means
the warping itself is quantum, which is the graviton route and its infinities (4.11). "Plug in the forces and read off the warping" is the
classical limit, and quantum gravity is the regime in which that reading fails. On Bruce: a name can be swapped when nothing is behind it, and
a warping of existence can be called Bruce. Gravity is a warping with numbers behind it: 1.75 arcseconds at the Sun, 43 arcseconds a century
for Mercury, waves at the speed of light with two polarisations. The axioms give Bruce. Einstein gives gravity.

The owner, in the same hour: "An event horizon would, in that case, be an internal containment, because that former existence space is now
occupied by something that is no longer possible outside of it, so space has to be separated." This holds, and it is the one mapping the chain
had already made (`docs/physics.md` section 1; 4.6): containment is the horizon. Three details of the physics, each with its counterpart in
DMP. The separation is causal and one-way, not a wall: things fall in, nothing comes out, and the outside geometry continues smoothly across
the horizon, so an observer crossing it notices nothing at the place; the horizon is defined by the whole future, by what can ever escape,
and not by anything local (Hawking and Ellis 1973; the locally defined surface, Penrose's trapped surface of 1965, is a different thing).
DMP's T4 says the same of containment, "nothing defines this boundary; it follows", and the chain proves the one-way part: a contained item
offers no read, forward or send (`contained_offers_nothing`), and admission is the only way across (`collapse_of_no_admission`). What the
inside still does to the outside is warp it: its mass, charge and spin are felt and nothing else (no hair); DMP's contained item leaks its
counts, size, staleness and rotation interval, and nothing else (`Entry.ext`). The one difference is the direction of release: a DMP
containment is lifted by a two-witness re-admission, a recorded act; a classical black hole releases nothing, and the quantum one releases
everything, scrambled, over its lifetime (Page 1993, above), which is the paradox the owner's second axiom resolves the right way. So the
horizon as containment is right, and it is classical gravity's containment; the quantum question is what the contained information does,
and the answer the field has reached is that it comes back out.

The owner's key point (2026-10-27): "every force is transmitted by a particle in a field, which in itself obeys the axiom system, so since
information is limited while we can perceive it, and information can never be destroyed or created, each force interaction, carried by a DoE
particle, must also transmit that exact quantum of information and cease to be perceivable. Also: only one of the information carrying layers
must exchange information, either the existence part or the information part." What holds: forces carried by quanta of a field is Yukawa
(1935), the carrier that is never seen is Feynman's virtual particle (1949), the internal line of the exchange, and information never created
or destroyed is unitarity, which the owner now holds and which retracts his "irreversibly destroyed when decaying" of an hour earlier,
rightly. Three things break. First, there is no exact quantum of information per interaction: what an exchange carries is partly quantised,
one unit of spin, a unit of charge, a particle, and partly continuous, the momentum transferred, which takes any value and is what scattering
measures; an interaction is not one bit. Second, "only one layer exchanges" is false of two of the four forces: beta decay (Fermi 1934)
changes the flavour and the charge, the owner's information half, and the momenta, his existence half, in the same interaction, and a gluon
exchange changes colour and momentum at once; only the photon leaves the charges alone, and even it carries angular momentum. Third, and the
one that matters for the verdict: an interaction is not a transfer but a sum. Where two exchanges can lead to the same final state they
interfere, with phases, and the interference is measured (Bhabha 1936, the two channels of electron-positron scattering); a bookkeeping of
definite quanta transmitted has no phases to add and cannot produce it. The amplitude is the quantum content of a force, and the owner's
picture carries the quantum numbers without the amplitude. None of this touches the five requirements above: the carriers are quanta of
fields on the existence field, the carrier of the existence exchange is the graviton, and the existence field's own quantum state is still
not in the picture.

The verdict for this section: a consistent frame that physics satisfies, and for that reason not a theory of anything in particular. It is
satisfied by worlds with gravity and without, with Einstein's law and with Newton's, so it derives no gravity; a quantum gravity would have to
begin where it leaves off, with a law for the existence field's own quantum.

## 5. The verdict

**False.** The approach, instantiated as faithfully as DMP's own objects allow, produces the shape of a gravitational theory with an arrow of
time (section 3) and cannot produce gravity (4.1), quantum mechanics (4.2), the field equations (4.3) or the measure (4.4); read as the
owner's vector it gains a coupling through the budget and a horizon depth, and loses nothing of the four stops (4.5); read as the
owner's information black hole it attains every ratio of dark energy to dark matter and so predicts none (4.6), predicts no slowing of
the expansion where the universe shows an acceleration (4.7), and has no tunnelling, because a refused move is never made (4.8); read as the
owner's rate-limited expansion it keeps its true half, the budget as the rate limit, and that half forbids the acceleration the universe shows
while supplying no cause (4.9); modelled as the owner's extension itself, a bound, a field, carriers and a push, it is the de Sitter horizon
with holographic equipartition, real physics that takes Λ as its input and leaves the horizon's degrees of freedom unnamed, a cosmology and not
a quantum gravity (4.10); read as the quantum of a duality of existence and information it is gauge theory, complementarity and inflation in
the owner's words, with a unique past that its own dissolving quantum forbids and the quantum of the existence field unasked (4.11); and the axioms as finally stated are satisfied by a world without gravity, and read as
stipulating the warping they fix neither its law nor its constant, so they entail a warping with a name and not gravity with its numbers (4.12). The first two are
not shortfalls of the instantiation but consequences of the axioms: member isolation and the frame rule forbid coupling, and the second axiom
is local realism. Each would have to be given up for the approach to work, and giving either up gives up DMP: without isolation there is no
containment, without local verification there is no Axiom 2.

What would reopen it is therefore not more work on these axioms but a different theory: one whose field couples every place to every other,
whose outcomes are not functions of locally verified evidence, and whose equation of state carries ħ, G and c. None of the three is in the
owner's two axioms, and the three theorems above are the proof that none can be derived from them. The extension of 4.10 is the closest the
owner has come: it reaches the classical horizon and stops where every emergent-gravity programme stops, at the microscopic degrees of freedom.

## 6. What stands

Section 3 stands, and it is DMP's: a self-propagating duality under a field has a second law, a Lyapunov potential, an equilibrium, a horizon
that leaks only counts and a boundary-set capacity. That is a theory of trusted infrastructure with the shape of black-hole thermodynamics,
proven in 340 theorems. It is a good thing to have proven. It is not a theory of gravity, quantum or classical, and the four theorems above
are the reason.
