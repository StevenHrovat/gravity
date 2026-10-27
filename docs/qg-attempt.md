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
(the second law); a horizon that lets nothing but counts out (the floor, T31, and `Entry.ext`); a capacity set at the boundary and unchanged
by any rearrangement inside (`Physics.lean`, the holographic shape); a minted pair that no single cause can expose (censorship for minted
pairs). This is the part of the owner's claim that is right, and it was right before this attempt: `docs/physics.md` section 1 lists it
result by result.

## 4. Where the approach must produce physics, and cannot: four theorems

To solve quantum gravity the instantiation must do three things no shape can do for it: couple places to each other the way gravity does,
be quantum, and fix the dynamics by an equation. Each is tested in the chain's own objects and each fails, and a fourth theorem closes the
probability-space sentence.

**4.1 The field of the axioms is uncoupled; a gravitational field is coupled.** The potential is a sum of one term per standing, mass times
staleness, and the system's act on one standing (a refresh) changes no other standing's term: `dmp_field_isolated`, `refresh_touches_only_its_own`,
`refresh_changes_no_other_term`. That is T32's member isolation and the frame rule, the feature that makes DMP compose and contain: nothing done
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
not at every point), no Unruh temperature (T32's temperature carries no acceleration and no ħ), no Raychaudhuri equation (no geodesics), and
no Einstein equation (no metric, no stress-energy). And where the derivation succeeds in physics it yields classical general relativity, with
the quantum put in by hand through ħ in the Unruh temperature.

**4.4 A spanning field fixes the support, not the measure.** "Solve any possible probability space by proving its existence in the DoE with a
vector field that can span it" holds for the support and fails for the measure: two weightings of the same two items, both spanned, have
different optimal orders (`spanning_does_not_fix_optimum`). Existence in the Duality decides which items are there; the demand, which is
configuration (T4), decides the layout; nothing in the field determines the weights. The equations that do come out are the two of
`docs/physics.md` section 2, the entropy bound on hops and the capacity bound on fan-out, and both take the measure as input.

## 5. The verdict

**False.** The approach, instantiated as faithfully as DMP's own objects allow, produces the shape of a gravitational theory with an arrow of
time (section 3) and cannot produce gravity (4.1), quantum mechanics (4.2), the field equations (4.3) or the measure (4.4). The first two are
not shortfalls of the instantiation but consequences of the axioms: member isolation and the frame rule forbid coupling, and the second axiom
is local realism. Each would have to be given up for the approach to work, and giving either up gives up DMP: without isolation there is no
containment, without local verification there is no Axiom 2.

What would reopen it is therefore not more work on these axioms but a different theory: one whose field couples every place to every other,
whose outcomes are not functions of locally verified evidence, and whose equation of state carries ħ, G and c. None of the three is in the
owner's two axioms, and the three theorems above are the proof that none can be derived from them.

## 6. What stands

Section 3 stands, and it is DMP's: a self-propagating duality under a field has a second law, a Lyapunov potential, an equilibrium, a horizon
that leaks only counts and a boundary-set capacity. That is a theory of trusted infrastructure with the shape of black-hole thermodynamics,
proven in 288 theorems. It is a good thing to have proven. It is not a theory of gravity, quantum or classical, and the four theorems above
are the reason.
