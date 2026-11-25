# Round 3, attempt 5 (r3-dmp): "Yang–Mills is a subset of DMP" as a route to existence (2026-11-21)

The owner's idea: "If we can show that YM is a subset of DMP, we can offer an alternative route to the existence proof of OAI."
Earlier: DMP "doesn't allow any not DMP complete system to exist", "there may be some configurations in Yang–Mills that simply are
not DMP complete", DMP "settles the question of existence for any system that can be described in it" (`../../PREP.md`, route 6).
Owner's addition during the round: "Once YM is shown as a subset, we get quite a few nice properties of DMP-complete systems 'for
free', so we should make use of that where possible" (section 6).

Claim levels as in `../RULES.md`: **proved** (Lean where marked), **proved with a stated gap**, **heuristic**, **conjecture**,
**numerical** (arithmetic on existing data), **literature (memory)** (not re-read this round). Lean: `../../../formal/Attempts/R3/`
(`DmpBridge.lean`, `DmpFlow.lean`, `DmpBalance.lean`, `DmpDuality.lean`), 34 theorems, built in WSL `~/formal-att-r3-5`, no `sorry`,
standard axioms only (section 9).

---

## 0. Results at a glance

**Verdict.** "YM ⊂ DMP" can be made precise (a *hosting*, section 1), and under it DMP's own existence theorem is the verdict on a
*finite* configuration: it translates into "every regularised lattice theory exists", which is true and trivial. Existence of the
continuum theory is a statement about a *limit*, and DMP has no limit theorem. The bridge "DMP-complete ⇒ continuum limit with the
Osterwalder–Schrader axioms" therefore breaks as stated; it holds in a reduced form (a uniform certificate at every layer ⇒ a limit
along a subsequence with the closed properties), and in that form its whole content is the uniform per-layer estimates, which is what
the OpenAI construction (OAI) proves. Non-triviality cannot come from DMP structure at all: the free theory passes every DMP check, and
DMP's Axiom 3 says so in its own words. It must come from a uniform margin, which only asymptotic freedom supplies (the triviality
test, passed). The admissible route is not shorter than OAI's: admissibility removes large fields only at the cutoff layer, and the
balance rule imposed at every layer would forbid confinement (proved). What DMP gives "for free" under the hosting is bookkeeping and
three standard facts (data processing, inherited reflection positivity, contraction ⇒ decay); none discharges W_p, the crossover or
torus robustness.

| # | statement | level |
|---|---|---|
| D1 | Definition of "YM ⊂ DMP" (hosting): root = bare lattice measure, lines = blocked levels laid over finer ones by Markov kernels, ledger = per-level estimates with uniform constants (§1) | definition |
| D2 | DMP's existence theorem (`verdict_proven_iff`, `proven_extend`) translates into per-level existence only; DMP objects are finite, so no DMP theorem speaks about the continuum (§1.3) | proved (by inspection of the definitions) |
| B1 | Per-level completeness gives no limit: any predicate met by two different objects is met at every level by a sequence with no limit (`perLevel_no_limit`) (§2.1) | **proved, Lean** |
| B2 | Reduced bridge: a uniform certificate (one compact set for all levels) plus closed structural properties (RP, lattice symmetries) gives a subsequential limit keeping them (`exists_of_uniform_certificate`) (§2.2) | **proved, Lean** (abstract); the YM instance is OAI's theorem |
| B3 | Non-triviality is not closed: positive at every level, zero in the limit is possible (`margin_lost_in_limit`); a uniform margin survives (`nontrivial_of_uniform_margin`, `exists_nontrivial_of_uniform_certificate`) (§2.3) | **proved, Lean** |
| B4 | The free configuration passes every DMP check (`Ledger.empty_complete`, `Ledger.complete_allYes_iff`, restating `Cmb.empty_recipe_proven`, `Refute.rf_dmpComplete_is_the_ledger`): DMP-completeness cannot certify non-triviality (§2.4) | **proved, Lean** |
| A1 | Bare admissibility = Wilson weight × a mask in [0, 1] that is 1 on the small-field set; masking keeps upper bounds (`admissible_eq_wilson_of_small`, `admissible_le_wilson`, `masked_le`) (§3.1) | **proved, Lean** |
| A2 | Admissible continuum limit exists by OAI's own proof, unchanged except for the mask, if OAI uses bare large-field data only through upper bounds and β-continuity (§3.2) | proved with a stated gap (OAI's source not re-checked for this) |
| A3 | Admissibility removes only the cutoff-layer large fields; coarse large fields reappear (round 1, `admissible_coarse`, sharp) (§3.3) | proved (round 1, Lean) |
| A4 | Balance at every layer with one bound ε < 1 excludes any area law (`balance_excludes_area_law`), so it is false for Yang–Mills, which confines at strong coupling (§3.4) | **proved, Lean** |
| A5 | Leg B: the per-plaquette inadmissible fraction falls (5.3 → 2.1·10⁻³), the density per physical volume rises (0.35 → 1.90 σ²): the rule is not "physically free" as rarity, only (if at all) as universality (§3.5) | numerical (arithmetic, `legb_density.py`) |
| A6 | Not shorter than OAI; universality is not even needed for an existence claim (OAI has none); W_p's large-field half is untouched (§3.6) | proved (A1–A4) / heuristic (W_p) |
| T1 | Triviality test, toy: infrared-free flow (b < 0) gives physical coupling ≤ 1/(n·c) from every perturbative bare coupling (`irFree_trivial`); asymptotically free flow (b > 0) reaches any prescribed coupling from a bare coupling that tends to 0 (`af_shoot`, `af_bare_bound`, `af_bare_coupling_vanishes`) (§4.1) | **proved, Lean** (one-loop toy) |
| T2 | Photon: no running (`photon_flat`), never reaches order one (`photon_never_reaches`); exists as a free field, gapless, nothing claimed beyond (§4.2) | **proved, Lean** (toy) / literature |
| T3 | Only b > 0 generates a scale where the coupling is of order one (`af_reaches_one`; `irFree_never_reaches`) (§4.1, §5) | **proved, Lean** (toy) |
| I1 | "A sub-layer only tightens" = the data-processing inequality for blocking (`blocking_tightens`), sharp at factor 1 (`identity_kernel_saturates`): monotone, never contracting by itself (§6) | **proved, Lean** |
| I2 | T38 "every layer has its own Duality", gated form: a blocked layer inherits reflection positivity for coarse variables drawn from one half (`gated_rp`); straddling variables need their own proof (§6) | **proved, Lean** (finite spaces) |

---

## 1. What "YM ⊂ DMP" must mean

### 1.1 What DMP's formal objects are

In `evidence/Dmp/` a configuration is a **recipe** (`Recipe.lean`): `n` numbered lines, each a layer of some kind with its Duality
and the earlier line it is laid over; line 0 is the root (a galaxy with a minted Duality). **DMP-complete** (`Complete.lean`) is: the
recipe is well formed (parents earlier, singularities of at least three nodes, every non-minted Duality gated by its parent) and the
lemma ledger `agree i` is true for every line `i < n`. `verdict_proven_iff` proves that Gravity's checker says "proven" exactly then.
Everything is finite: `n` is a natural number, the ledger is a Boolean per line, and the content of a line's certificate is outside
the definition (it is whatever the two chains prove). `Refute.rf_dmpComplete_is_the_ledger` makes the last point explicit: under the
all-yes ledger, DMP-complete is well-formedness and nothing more.

### 1.2 The definition

A **DMP hosting** of a family of lattice gauge theories (the OAI family: cutoffs N, volumes p, block levels m = N (bare) … 0 (unit
scale)) assigns to each (N, p) a recipe R_{N,p}:

- **Root (line 0, the galaxy).** The bare lattice measure μ_{N,p,N} (Wilson or admissible weight times Haar measure). Its Duality is
  the pair of half-spaces of a lattice reflection; "minted" means reflection positive. Proved for both weights (`Positivity`,
  `admissible_rp`). This is G0: the regularised theory is defined directly, not derived.
- **Lines j = 1 … N.** Line j is level m = N − j, the effective measure μ_{N,p,m}, laid over line j − 1 by the blocking kernel K_m
  (a Markov kernel, total mass 1; OAI's `StepData`, `IsKernel.total`). Coarser layers are laid over finer ones; the chain of every
  line runs down to the bare root. Well-formedness holds by construction.
- **Re-keying** = gauge transformations; every line's content is gauge invariant (`Gauge.lean`: `loop_hol_rekey`,
  `wilsonPot_rekey`).
- **Ledger.** agree(j) = true iff μ_{N,p,N−j} has the level-m certificate C_m(κ): a polymer representation with small-field
  activities bounded in the regular norm, large-field activities bounded from above, and the coupling in its window, with constants
  κ (OAI's `History.Conv`, `Calendar.Fits`).
- **"YM ⊂ DMP"** (the uniform hosting) holds when there are constants κ such that **every** R_{N,p} is DMP-complete under the
  ledger C(κ): the same constants at every layer, every cutoff and every volume. This is Axiom 1's "This holds at every layer", read
  with uniform constants.

Structure preserved: configurations (link variables ↔ translations between key frames, `Gauge.lean`), the Gibbs family (the line
contents), blocking (the parent relation), reflection positivity (the Duality of each line). DMP's well-formedness and its recipe
theorems then apply to R_{N,p} verbatim.

### 1.3 Which DMP theorem is the "existence" theorem, and what it translates to

DMP's existence theorem is the verdict: `Recipe.verdict_proven_iff` (proven ⇔ DMP-complete), grown one line at a time by
`Recipe.proven_extend` (mint prep is incremental), with T40 (a minting originates only from G0 and a DMP-complete state). Under the
hosting it says: **each finite hierarchy R_{N,p} is certified**, i.e. each regularised lattice theory exists with its per-level
estimates. Existence of each regularised theory is trivial (a bounded density on a compact group); the estimates are OAI's work.

The continuum theory is not a recipe. As N → ∞ the root recedes to infinite depth below every fixed level; the object we want is the
limit of the level-m contents as N → ∞ at fixed m (then p → ∞). No DMP theorem speaks about limits of recipes. So the existence
theorem "on the other side" has to be added: it is a compactness theorem (section 2.2), and the DMP reading that comes closest is
`Reach.mg_reach_floor_every_layer` (the same bound at every layer gives the same floor at every layer), with the hypothesis
"the same constants at every layer" doing all the work.

---

## 2. The bridge: DMP-complete ⇒ a continuum limit with the Osterwalder–Schrader axioms

### 2.1 As stated, it breaks (B1, proved, Lean `perLevel_no_limit`)

If DMP-completeness is checked level by level (each R_{N,p} certified, constants allowed to depend on N), it cannot imply that a
limit exists. Lean: in any Hausdorff space, for any predicate P satisfied by two different objects x ≠ y, the sequence x, y, x, y, …
satisfies P at every level and converges to nothing. Every regularised Yang–Mills theory is DMP-complete in this weak sense (each is
a finite, certified object), so "every level is DMP-complete" proves nothing about the continuum.

### 2.2 What does hold: the reduced bridge (B2, proved, Lean `exists_of_uniform_certificate`)

If the certificate is uniform, i.e. all levels lie in one compact set K (the same constants for every N and p), and in a closed set F
of structural properties, then a subsequence converges and its limit lies in K ∩ F. Applied to Yang–Mills:

- **Existence along a subsequence:** compactness (Prokhorov's theorem for measures, compact sets in the polymer norms for effective
  densities). This is how OAI gets its volume limit (along a subsequence) [`../../H1-OPENAI.md` §1].
- **Reflection positivity (OS2):** a closed condition (a non-strict inequality of integrals of bounded continuous functions), so it
  passes to the limit. Proved for the bare Wilson and admissible measures (`Positivity`).
- **Lattice symmetries:** closed (equalities), so they pass.

What the reduced bridge does **not** deliver, so what a full bridge would have to contain:

1. **Euclidean invariance (OS1).** The lattice has only hypercubic symmetry; full rotation invariance in the limit is not a closed
   consequence of the lattice symmetries. It needs the content of the renormalisation group (rotation-breaking terms are irrelevant
   operators whose coefficients vanish), i.e. the small-field estimates themselves.
2. **Non-triviality.** Section 2.3.
3. **Clustering and a unique vacuum (OS4).** Not delivered by compactness; the committee lists uniqueness of the volume limit as
   open. This is where H2 (the gap) enters, and it is not an existence statement.

So the bridge theorem in its strongest true form is: *uniform hosting (every R_{N,p} DMP-complete under one ledger C(κ)) ⇒ a
continuum limit along a subsequence with OS2 and the lattice symmetries; OS1 and non-triviality need the ledger's content.* Its
hypothesis is OAI's set of uniform estimates; its conclusion is OAI's existence theorem minus Euclidean invariance and `nonfree`. The
ledger **is** OAI's proof. DMP supplies the bookkeeping: `proven_extend` is the induction over levels (`History.Selected`: `starts`,
`steps`, `represents`), the frame rule (`extend_preserves_decisions`) is the consistency of a coarser level with the finer ones
(blocking a coarser level does not change the finer levels), and `one_unproven_line_unproves` says that one level without its estimate
leaves the whole chain unproven.

### 2.3 Non-triviality needs a uniform margin (B3, proved, Lean)

"The limit is not free" is an open condition (the complement of the closed set of Gaussian measures), and open conditions are lost in
limits: `margin_lost_in_limit` gives a quantity positive at every level that tends to zero. This is exactly four-dimensional φ⁴
(Aizenman and Duminil-Copin, Ann. Math. 2021: every scaling limit of the critical lattice φ⁴₄ and Ising models is Gaussian, with the
connected four-point function bounded by C/(log L)^c; literature, memory for the exact exponent; earlier Aizenman 1982 and Froehlich
1982 in d > 4). The way out is a lower bound uniform in the level: if a continuous functional f (a renormalised coupling, a connected
four-point function) satisfies f ≥ c > 0 at every level, then f ≥ c in the limit (`nontrivial_of_uniform_margin`), and with the
compactness of 2.2 the limit exists and is not free (`exists_nontrivial_of_uniform_certificate`). For Yang–Mills the uniform margin is
the running coupling reaching a prescribed value at the physical scale, which is asymptotic freedom (section 4.1). OAI's `nonfree` is
of this kind (it excludes finite sums of free massive Wick profiles).

### 2.4 DMP cannot see the difference between free and interacting (B4, proved, Lean)

`Ledger.empty_complete` (restating `Cmb.empty_recipe_proven`): the empty configuration is DMP-complete under any ledger;
`Refute.rf_nothing_ever_performed`: a configuration in which nothing ever happens satisfies every theorem of the chain. The free field
is the Yang–Mills-side analogue (nothing interacts). DMP's Axiom 3 states the limit precisely: "From trust nothing can be derived about
information but its existence: a standing, a refusal or a count says that information is there, never what it says." Under the
hosting: a DMP certificate can give at most existence; **what the theory says** (interacting or free, gapped or not) is content and
must come from the ledger's content. This is the triviality test seen from inside DMP, and DMP passes it by its own axiom.

---

## 3. The concrete physics form: admissibility

### 3.1 Bare admissibility is a mask (A1, proved, Lean)

The admissible plaquette weight is exp(β·Re tr U_p)·1[shortfall ≤ ε] (`Positivity.admissibleWeight`). Lean:
`admissible_eq_wilson_of_small` (equal to the Wilson weight when the shortfall is at most ε), `admissible_le_wilson` (between 0 and
the Wilson weight everywhere), `masked_le` (|χ·K| ≤ |K| for χ ∈ [0, 1]). In any renormalisation-group construction whose bare
small-field threshold is below ε (true at weak coupling, where the threshold tends to 0 with g), the admissible bare density equals
Wilson's on small fields and differs on large fields by a factor in [0, 1].

### 3.2 The admissible continuum limit exists by OAI's proof (A2, proved with a stated gap)

OAI controls large-field activities only from above (sup bounds; `../../H1-OPENAI.md` §2: "Kᵢ (large-field activities): only upper
sup bounds"), the partition-function lower bound comes from small fields, the mask is a product of local gauge-invariant factors and
does not depend on β (so the shooting of β_{N,p} by continuity, `Selected.reaches`, is unaffected), and on the healthy set it is
identically 1 (so the regularity of the small-field activities is unaffected). Hence: **if** OAI's induction uses the bare large-field
data only through bounds of the form |∫ χ F| ≤ ∫ |F| and β-continuity, the admissible family has a continuum limit along the same
sequences, with OAI's headline properties, and it is reflection positive (closed, from `admissible_rp`). *Stated gap:* I have not
re-read OAI's first RG step to confirm that the bare density enters only this way; this is a source-reading check, not new
mathematics. This makes the owner's rule a theorem at the cutoff layer: the theory in which inadmissible configurations "simply do not
exist" exists in the continuum (along subsequences), by OAI's proof.

### 3.3 "No large fields by construction" holds only at the cutoff layer (A3, round 1)

Round 1 (`../admissible/NOTE.md` §3; Lean `admissible_coarse`, `u1_constant_field`): one 2 × 2 blocking multiplies the admissibility
bound by at most 4, and this is sharp. After about log₄(2/ε) blockings the bound is vacuous; OAI's level 0 lies about N blockings above
the cutoff, so its level-0 fields are unconstrained. Coarse large fields (smooth, coherent, such as thick centre vortices) are made of
admissible fine fields and reappear at every level. The large-field half of W_p, which lives at OAI's level 0 and asks for lower
bounds on large-field activities there, is untouched (W_p is r3-wp's subject).

### 3.4 Balance at every layer is not Yang–Mills (A4, proved, Lean `balance_excludes_area_law`)

One could try to impose DMP's balance rule at every layer, on the coarse plaquettes of every level, with one bound ε. Lean: if every
loop of every size has shortfall at most ε < 1 (normalised trace ≥ 1 − ε almost surely), no area law ⟨W(C)⟩ ≤ C·e^{−σ·Area} with
σ > 0 can hold. Strong-coupling Yang–Mills has an area law (proved: `AreaLaw.Twist*`), and physical Yang–Mills is expected to confine
at all couplings, so the rule at every layer with one bound describes a different, non-confining theory. Two readings remain:
(a) the rule at the cutoff layer only (Luescher admissibility, sections 3.1–3.3); (b) the rule relative to each layer's own coupling:
shortfall of the coarse plaquettes below g_k·p(g_k). Reading (b) is **Balaban's small-field condition** (Balaban 1983–89; Dimock's
exposition arXiv:1108.1335). It fails on a positive fraction of blocks at every level, roughly e^{−p(g_k)²} per block, and those blocks
are the large-field regions.

**This is the precise form of the owner's "configurations that are not DMP complete":** at layer k, the large-field blocks are where
the balance rule of that layer fails. They do not "simply not exist" (they have positive weight, and removing them at coarse layers
removes confinement, A4); they are **exponentially rare**, and OAI proves them rare enough for existence (upper bounds). W_p asks
that they be rare enough uniformly under every boundary condition (lower bounds). The owner's statement holds as a rarity statement
(proved by OAI where existence needs it) and fails as a strict selection rule beyond the cutoff layer (A4).

### 3.5 Leg B: the rule is not free as rarity (A5, numerical)

Leg B's bulk fraction of plaquettes with shortfall above ε = 1.5 (shortfall 2 − Re tr U, SU(2)), with our own a√σ from the TTL scan
(`../../../results/ttl_summary.json`), `legb_density.py`:

| β | fraction f | a√σ | density f/(a√σ)⁴ per orientation, units σ² |
|---|---|---|---|
| 2.3 | 5.3·10⁻³ | 0.3503(61) | 0.352(24) |
| 2.4 | 3.3·10⁻³ | 0.2579(29) | 0.745(33) |
| 2.5 | 2.1·10⁻³ | 0.1822(22) | 1.904(93) |

(Errors from a√σ only; f's own errors are below 3·10⁻⁴ at β = 2.3.) The fraction falls like e^{−4.6β}; (a√σ)⁻⁴ grows like e^{+13.1β};
the number of inadmissible plaquettes per physical volume grows like e^{+8.4β}, a factor 5.4 from β = 2.3 to 2.5. This is round 1's
prediction A2 (heuristic there), now seen in data: the per-plaquette average forgets what the physical density shows (the DMP shape
is `MassGap.mg_temperature_no_uniform_gap`: an intensive readout has no uniform gap). So "the rule is physically free" cannot mean
"the removed configurations become rare in a fixed physical box"; it can only mean universality in the renormalisation-group sense.
Caveat: β 2.3–2.5 is not in asymptotic scaling, and one ε only.

### 3.6 Is the admissible route shorter than OAI's? (A6)

No. For existence it is OAI's proof with one harmless factor inserted (3.2); the step it removes, bare-layer large fields, is the
easiest instance of the large-field problem, and the coarse instances remain (3.3). A cutoff-dependent ε(g) removes a few more levels
at the price of a harder universality question, and still leaves all levels above log₄(2/ε). The genuinely new theorem a shorter route
would need is a multi-layer balance bound; with one bound at every layer it is false for Yang–Mills (3.4), and relative to each
layer's coupling it is the large-field problem itself.

**Universality** (admissible and Wilson theories share the continuum limit) is not needed for an existence claim of the OAI kind:
OAI itself has no universality (no statement about other spacing sequences or other actions). It is needed only to say the
admissible limit is *the same* theory as Wilson's. Status: standard expectation, supported by identical perturbation theory at fixed
volume (round 1 A1) and numerics (Luescher; Hernandez–Jansen–Luescher 1999; Bietenholz et al. 2006; literature, memory), not proved;
A5 shows it cannot be proved by a rarity argument. Reflection positivity of the admissible measure is proved (`admissible_rp`), as the
brief says.

---

## 4. The tests

### 4.1 Triviality (T1, T3, proved in a one-coupling toy, Lean `DmpFlow.lean`)

The route must not give a non-trivial continuum φ⁴₄. Hosted the same way, φ⁴₄ has a root (bare lattice φ⁴ exists, is reflection
positive), lines (block-spin effective measures) and, with the field normalised by its two-point function, uniform per-level bounds:
it **is** uniformly DMP-complete, and its limit **exists**, as a Gaussian (Aizenman–Duminil-Copin). The route gives existence (true)
and must not give non-triviality; it does not, because non-triviality needs a uniform margin (2.3), and φ⁴₄'s renormalised coupling has
none.

What Yang–Mills has and φ⁴ lacks is the **sign of the one-loop coefficient**. Toy: one step of `flow b x = x + b·x²` towards long
distances, n steps between cutoff and physical scale (n ~ log(1/a)).

- **b < 0 (infrared free, φ⁴₄):** from every bare coupling x ∈ (0, 1/c) (b = −c), after n ≥ 1 steps the coupling is at most 1/(n·c)
  (`irFree_trivial`), and it never reaches order one (`irFree_never_reaches`). Removing the cutoff makes the theory free, whatever the
  bare coupling: triviality.
- **b > 0 (asymptotically free, Yang–Mills):** every prescribed physical coupling c > 0 is reached after n steps from a bare
  coupling x_n ∈ (0, c] (`af_shoot`, the toy of OAI's `Selected.reaches`), with x_n ≤ 1/(1/c + n·b/(1+bc)) (`af_bare_bound`), so
  x_n → 0 (`af_bare_coupling_vanishes`): the chain's root at infinite depth is the free theory, and the chain out of it is
  non-trivial (it lands on c ≠ 0). Every positive coupling reaches order one after finitely many steps (`af_reaches_one`):
  dimensional transmutation, the scale L₁.

The physics behind the sign: b₀ = 11N/(48π²) for SU(N) (Gross–Wilczek, Politzer 1973). In the spin decomposition (Nielsen 1981,
Hughes 1980; memory) a charged field of spin s contributes ∝ (−1)^{2s}((2s)² − 1/3): the gluon, a **spin-1 carrier that carries the
charge it transmits**, gives 4 − 1/3 = 11/3 > 0 (antiscreening). φ⁴ has no carrier and no charge; its contact self-interaction
screens. So the owner's "self-charge" is the right ingredient, but it enters quantitatively, through the sign: self-interaction alone
is not enough (φ⁴ self-interacts and is trivial), and self-charge alone is not enough either (QCD with 17 or more quark flavours has the
same gluon self-charge and loses asymptotic freedom, n_f > 16.5 for SU(3); its continuum limit is expected to be trivial like QED's;
literature, memory). Any version of the route that used "gluons carry charge" without the sign of b₀ would wrongly certify those
theories: that is the precise boundary of the reading.

Claim level: the toy statements are proved; the real ones are OAI (Yang–Mills side, existence and `nonfree`), Balaban (control of the
running), Aizenman–Duminil-Copin (φ⁴₄, non-perturbative, all bare couplings, not only the perturbative range of the toy).

### 4.2 Photon (T2)

Free 4D U(1) must come out as existing (a free field) and gapless. Hosted: root = Wilson U(1) at weak coupling (exists, reflection
positive); with no charged matter the coupling does not run (b = 0, `photon_flat`), and the photon's self-interactions on the lattice
are irrelevant operators (rescaling A → A/e leaves the free Maxwell action plus terms of order a²): the per-level certificate is
uniform (Gaussian) and the limit exists **as the free field** (literature, memory: Guth 1980 and Froehlich–Spencer 1982 for the Coulomb
phase; Driver 1987 for the convergence of lattice U(1)₄ to the free continuum field). The route claims nothing more: no margin
(the self-coupling functional tends to zero), no scale (`photon_never_reaches`: the coupling never reaches order one), no gap. Every
transferred property in section 6 was checked against U(1): those that would give a gap need a contraction hypothesis that U(1) fails
(`no_contraction_no_decay`, `identity_kernel_saturates`). Admissible U(1) is massless at every β (round 1, E1/E2): the admissible route
adds no gap either. **Passed.**

### 4.3 Z₂

Z₂ is a finite group: there is no Lie algebra, no small-field expansion and no running coupling, so the toy flow does not apply and
there is no chain out of a free root. 4D Z₂ lattice gauge theory has a first-order transition (Creutz–Jacobs–Rebbi 1979; memory), so no
continuum limit with a finite physical scale: its weak-coupling gap is at the lattice scale, and in physical units it diverges. The
route's existence claim for Z₂ is at most a trivial limit (consistent). Gap-only statements must hold for Z₂: the counted gap of
`MassGap.mg_gap_uniform` / `mg_mass_gap_survives_refinement` transfers to Z₂ as the discrete action quantum (a flipped link costs a
fixed multiple of β), correctly, and implies no area law, correctly (weak-coupling Z₂ has a perimeter law). Confinement-type
statements must fail for Z₂: `balance_excludes_area_law` is a no-go, not a confinement claim; soft-admissible Z₂ is Wilson Z₂ at a
larger β (round 1 E3), deeper in the deconfined phase. **Passed.**

---

## 5. The owner's readings, mapped

| reading | mathematical statement | level |
|---|---|---|
| "DMP doesn't allow any not DMP complete system to exist" | existence := uniformly certified hierarchy; as a definition it is a restatement, the content is the ledger | definition (§1.2) |
| "some configurations in YM are not DMP complete" | at layer k, the large-field blocks (Balaban's small-field condition fails there) | precise (§3.4) |
| "they simply do not exist" | true as exponential rarity (OAI, upper bounds, enough for existence); false as a selection rule beyond the cutoff layer (it removes confinement) | proved (A4) / literature (OAI) |
| DMP "settles existence for any system described in it" | settles it for each finite configuration (trivial for lattice theories); for the continuum only with uniform constants, which must be proved (OAI) | proved (B1, B2) |
| existence = self-charge with a prescribed path | b₀ > 0: the chain out of the free root lands on a prescribed coupling (`af_shoot`) and generates the scale L₁ (`af_reaches_one`) | toy proved; real: OAI, Balaban |
| IM vs payload | asymptotically free (a non-trivial chain, a scale) vs b = 0 (free field, no running, no scale; `photon_flat`) | toy proved |
| the root swap at the existence boundary | the continuum limit sends the bare root to infinite depth, where it becomes the free fixed point (`af_bare_coupling_vanishes`): the ultraviolet root swap. The infrared one (confinement) is not addressed here | toy proved / reading |
| Z₂ as naked duality at G0 | Z₂ exists only at the root (cutoff scale): no chain out of it, gap at the lattice scale, no continuum limit | reading, consistent with 4.3 |
| H1 = how something can exist, H2 = what existence is | the bridge delivers only H1-type statements (existence along the chain); Axiom 3: a certificate gives existence, never content; the gap (H2) is content | proved (B4) / reading |
| the α pointer | only b > 0 brings the coupling to order one at a finite scale; the photon never | toy proved (T3) |

---

## 6. What comes "for free" (the owner's addition)

A property of DMP-complete configurations transfers only once the hosting is established and preserves the structure the property's
proof uses. Below, for every theorem family in `evidence/Dmp/` and the stable chapters of `vendor/dmp/` (read only): its Yang–Mills
translation under the hosting of §1.2; the class **(a)** needed in the chain (W_p, crossover, torus robustness, the existence bridge,
H1/H2), **(b)** already known or proved, **(c)** not meaningful for Yang–Mills; the **price** (what part of the hosting it needs); and
the tests.

### 6.1 Table

| DMP property | Yang–Mills translation | class | price | tests |
|---|---|---|---|---|
| `verdict_proven_iff`, `verdict_trichotomy` (Complete) | each finite hierarchy is certified / has an uncertified level / is not a block hierarchy | (b) bookkeeping | the ledger (= OAI's estimates) | neutral |
| `proven_extend` (mint prep incremental) | induction over RG levels: estimates at levels N…m+1 plus a one-step lemma give level m; finer levels unchanged | (b) structure of OAI's `History.Selected`; the one-step lemma for large fields with lower bounds is W_p (a) | the one-step lemma | neutral |
| `one_unproven_line_unproves` | one level without its estimate (the crossover, α_s ~ 1) leaves the chain uncertified; no level certifies its neighbours | diagnostic, consistent with ROUND-2's map | none | neutral |
| `proven_sublayer_only_tightens`; Axiom 3 "a sub-layer only tightens" | **data processing**: blocking never increases the distinguishability of two fine laws (two boundary conditions, two cutoffs): `blocking_tightens` | (b), proved here | blocking by a Markov kernel (OAI's kernel is one) | photon: factor exactly 1 possible (`identity_kernel_saturates`), so it gives no gap. **Not** r3-monotone's statement: what is monotone is information, while the coupling *grows* towards the coarse end (asymptotic freedom) |
| `proven_no_pressed_root`, `root_minted`, `pass_has_two_independent_witnesses` | the bare measure is reflection positive (its Duality is minted); every positivity statement traces back to it | (b) proved (`Positivity`, `admissible_rp`) | reflection-symmetric bare action | neutral |
| T38 "every information layer has its own Duality", `lineOk` (a non-minted Duality is gated by its parent) | **gated form**: a blocked layer inherits RP for coarse variables drawn from one half by a kernel that factorises across the plane (`gated_rp`); full RP of a blocked layer (straddling variables) needs its own proof | gated form (b), proved here; full form **(a)**: needed for the transfer-matrix reading and torus robustness at the blocked scale (`../../H1-OPENAI.md` §5: not addressed by OAI's kernel) | reflection-compatible blocking kernel | photon: RP holds for U(1) too, no gap claimed |
| `mg_reach_existence_floor`, `mg_reach_floor_every_layer` (Reach) | mass ≥ 1/(reach): a correlation length bounded in physical units at every spacing gives a mass bounded below | arithmetic (b); its hypothesis is UniformGDS / the gap **(a), not discharged** | the reach bound itself, i.e. the open problem | photon: the hypothesis fails (`mg_no_reach_no_floor`), correct |
| `mg_space_time_certificate`, `mg_ttl_existence_floor` | spatial decay rate = temporal decay rate (exact along axes by hypercubic symmetry; in the continuum needs O(4)); bounded correlation time + RP ⇒ transfer-matrix gap | (b) standard (PREP route 3) | RP at the level used | neutral |
| `mg_gap_uniform`, `mg_refinement_closes_potential_gap`, `mg_mass_gap_survives_refinement` (MassGap) | the classical action of a continuous group has no gap in the continuum (classical YM is scale invariant); counted (integer) quantities, such as centre-flux sectors, do not refine | (b); the counted reading points at the twist free energy (twist route), not a theorem | none | Z₂: the classical quantum is a real lattice-scale gap, correctly without confinement |
| `mg_temperature_no_uniform_gap` | intensive averages forget local excitations: the falling inadmissible fraction vs the growing physical density (A5) | (b) | none | neutral |
| `mg_returns_to_balance`, `mg_marginal_never_returns` | a Markov dynamics (heat bath, Langevin) with a spectral gap returns to equilibrium exponentially; marginal = critical slowing down | (b) at strong coupling (Shen–Zhu–Zhu; round 2 C), open at weak coupling | a dynamics gap; note a dynamics gap is not in general the Hamiltonian mass gap | photon: marginal, correct |
| `mg_cluster_floor` (T3a, three nodes) | no Yang–Mills meaning (the smallest non-abelian group S₃ in `Gauge.lean` is a coincidence of small numbers, as that file says) | (c) | — | — |
| `loop_hol_rekey`, `wilsonPot_rekey`, `pure_gauge_balanced` (Gauge) | gauge invariance of Wilson loops and action; pure gauge has zero action | (b) textbook | the dictionary | — |
| `balanced_not_trivial` | flat connections with non-trivial holonomy on the torus (flux sectors, torelons) | (b); for torus robustness **(a) as an obstacle**: the robustness lemma must handle these sectors | — | U(1) and Z₂ have them too |
| `nonabelian_loop_value_moves`, `abelian_loop_value_fixed` | non-commutativity; the photon-test discriminant | (b) | — | it is the test |
| `contraction_decay`, `no_contraction_no_decay` | per-layer contraction q < 1 ⇒ exponential clustering uniform in volume (the skeleton of `gap_of_effective_W`, Corollary B, the lead route's recursion) | (b) as an implication; the hypothesis is the crossover / H2 **(a), not discharged** | the contraction itself | photon fails the hypothesis, correct |
| Layer.lean: independence, `confined_influence_never_passes_alone`, `not_minted_collapses` | reading: RP's Cauchy–Schwarz and chessboard estimates (an event confined to one half is bounded by its reflected spread) | (b) proved (`Positivity`: Gram, Cauchy–Schwarz) as reading; failure-class independence has no YM meaning (c) | RP | neutral |
| R2Stable `st_self_stabilizing`, `st_no_root_takeover` | forgetting the initial or boundary state at finite speed (Dobrushin uniqueness) | (b) at strong coupling; at weak coupling it is UniformGDS **(a), not discharged**: DMP has a fixed root and a deterministic rule, Yang–Mills has neither | a contraction | photon: no uniqueness speed, correct |
| R2Stable `st_settles`, `st_equilibrium_not_optimal` | a descent of the action settles (gradient flow, Luescher 2010); local minima that are not global (flat sectors, instantons) | (b) | — | — |
| `Cmb.empty_recipe_proven`, `Refute.rf_nothing_ever_performed`, `rf_dmpComplete_is_the_ledger`; Axiom 3 "from trust nothing … but its existence" | the free theory passes every DMP check; a certificate gives existence, never content | **(a) for the existence bridge, as its limit**: it is the triviality test inside DMP (B4) | none | triviality test passed by DMP's own axiom |
| Axiom 1 "This holds at every layer" | uniform constants across layers, cutoffs and volumes | **(a)**: it is exactly what must be proved (OAI for existence; UniformGDS / H2 for the gap) | the uniform estimates | photon: uniform existence yes, uniform reach no, correct |
| Floor, Gate, Standing, Field (T24), Record, R1Bridge/Laws/Lens/Mass/Model/Tier/Wave, Cmb encoding, Layouts | protocol semantics of IM/CMOS (verifiers, records, routing, clocks) | (c) | — | — |

### 6.2 What this means

No DMP property discharges or shortens W_p, the crossover or torus robustness. The ones that look closest are implications whose
hypothesis is the open piece itself: `mg_reach_floor_every_layer` and `contraction_decay` need the uniform reach or contraction
(UniformGDS / H2), `st_self_stabilizing` needs a contraction, `proven_extend` needs the one-step lemma (W_p). "A sub-layer only
tightens" transfers, and is proved here, but as **monotonicity of information under blocking (factor ≤ 1)**, not as contraction
(factor < 1) and not as monotonicity of the coupling; the photon saturates it. The one property that transfers in a form the chain
actually needs is T38 at every layer, reflection positivity of the blocked layers: its gated form is free (`gated_rp`), its full form
(coarse variables that straddle the reflection plane) is a finite, concrete lemma that torus robustness and the transfer-matrix
reading at L₁ need and that OAI's kernel does not provide.

Every transferred claim was checked: none gives free U(1) a gap (the gap-type ones need a contraction U(1) fails), none gives φ⁴₄ a
non-trivial limit (the only existence-type transfer is B2, which gives non-triviality only with a uniform margin), and none claims
confinement for Z₂.

---

## 7. Where the idea breaks, in one paragraph

DMP's existence is a verdict on finite configurations; Yang–Mills' existence is a limit. The hosting makes every regularised
Yang–Mills theory a DMP configuration, and makes "YM ⊂ DMP with the same constants at every layer" exactly equivalent to OAI's uniform
estimates (plus compactness, which is standard). So DMP offers a precise *language* for OAI's proof (induction over layers, the frame
rule, one unproven layer unproves the chain, the root at infinite depth is the free theory), not an alternative proof: the ledger has
to be filled, and filling it is the proof. Non-triviality and the gap are content, which DMP's Axiom 3 says a trust certificate cannot
supply. The owner's selection rule is legitimate at the cutoff layer (it yields an existing, reflection-positive theory by OAI's proof)
and wrong as a rule at every layer (it would remove confinement); in between it is the large-field problem, named precisely.

## 8. Most promising next step (one)

**Prove T38 at every layer: reflection positivity of a blocked Yang–Mills layer, including the coarse links that straddle the
reflection plane, for a reflection-compatible gauge blocking.** Concretely: choose blocks whose boundaries lie on the reflection plane;
build each straddling coarse link as the product of a positive-half transport and a negative-half transport meeting at a plane site
(with the random frame at that site shared), so that the kernel factorises as K₊ ⊗ ΘK₊ given the plane variables; then show the coarse
measure is RP by the argument of `gated_rp` with the plane variables as the conditioning layer (in Lean with the `Positivity` tools).
It is finite, new for gauge blockings as far as I know (check the literature first), cheap to test (also on Leg B data: the coarse
Gram matrix must be positive), and it is the one "free" DMP property the open chain needs: torus robustness (ROUND-2 piece 3) and the
spectral reading of H2 at L₁ both use RP of the blocked theory. Cheap side check alongside: confirm in OAI's first RG step that the
bare density enters only through upper bounds on large fields (A2's stated gap), which turns "the admissible theory exists" into a
complete reduction to OAI.

---

## 9. Files and Lean status

- `NOTE.md` (this note).
- `legb_density.py`: arithmetic on Leg B's admissibility fractions and our a√σ (no simulation; `py legb_density.py`).
- `build.sh`: builds the four modules in WSL `~/formal-att-r3-5` (`wsl -d ym-replay -u ym -- bash /mnt/c/.../r3-dmp/build.sh`).
- `axioms.sh`: prints `#print axioms` for every theorem, checks the sources for `sorry`/`axiom`/`native_decide`, lists warnings.
- Lean, `../../../formal/Attempts/R3/` (namespace `Attempts.R3.DmpHost`; the DMP side restated, since `evidence/` is a separate Lean
  project):
  - `DmpBridge.lean` (Mathlib only): `Ledger`, `Ledger.complete`, `Ledger.complete_allYes_iff`, `Ledger.empty_complete`,
    `alternate`, `alternate_even`, `alternate_odd`, `perLevel_no_limit`, `exists_of_uniform_certificate`, `margin_lost_in_limit`, `nontrivial_of_uniform_margin`,
    `exists_nontrivial_of_uniform_certificate`.
  - `DmpFlow.lean` (Mathlib only): `flow`, `flow_continuous`, `photon_flat`, `photon_never_reaches`, `irStep_pos`, `irStep_inv`, `irFree_iterate`,
    `irFree_trivial`, `irFree_never_reaches`, `afStep_ge`, `af_iterate_ge`, `af_iterate_zero`, `af_shoot`, `afStep_inv`,
    `af_inverse_gain`, `af_bare_bound`, `af_bare_coupling_vanishes`, `af_growth`, `af_reaches_one`.
  - `DmpBalance.lean` (imports `Positivity.Admissible`): `admissible_eq_wilson_of_small`, `admissible_le_wilson`, `masked_le`,
    `blocking_tightens`, `identity_kernel_saturates`, `balance_excludes_area_law`.
  - `DmpDuality.lean` (Mathlib only): `gated_rp`.
- Build status: all four modules build ("Build completed successfully"), Lean 4.34.0, Mathlib v4.34.0; no warnings in these files;
  34 theorems, `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` (two use only `propext`, `Quot.sound`); no `sorry`,
  no `axiom`, no `native_decide`.
