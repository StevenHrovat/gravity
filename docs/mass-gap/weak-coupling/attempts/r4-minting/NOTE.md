# Round 4, attempt 4 (r4-minting): the minting as a conservation law across layers (2026-11-21)

The owner's idea: "For the conservation we might be able to take advantage of the properties of minting in DMP. It only takes a perfect
duality and WHKs that define quantum and tick, everything else follows." Precisions that arrived during the attempt (all now at the end
of `../../PREP.md`): G0 holds all information and all existence at once, and every later step is lossy; "what is conserved ... seems to be
the act"; "it is conserved by the simple fact that it IS running ... which satisfies its tie to G0"; "isn't tie to G0 simply reach?";
the new **Banks–Zaks test**; and "DMP demands that something inside of it DOES exist, so something must be able to run and thus not
stall" (§2.7).

Claim levels as in `../RULES.md`: **proved (Lean)**, **proved (paper)**, **known** (literature, from memory unless marked), **heuristic**,
**conjecture**, **reading** (an interpretation in the owner's terms, not a mathematical claim). Every Lean theorem here is a **toy**: it
contains no SU(2), no lattice, no Wilson measure. Lean: `../../../formal/Attempts/R4/MintingDmp.lean` and `MintingScale.lean`, namespace
`Attempts.R4.Minting`, 34 theorems, built in WSL `~/formal-att-r4-4` with `build.sh` (this folder): "Build completed successfully",
`#print axioms` on all 34 shows only propext, Classical.choice, Quot.sound; no `sorry`, no `axiom`, no `native_decide`. The DMP side is
restated in the formal project because `evidence/` is a separate Lean project. No numerics were run.

---

## 0. The result in plain words

1. **The DMP law, made precise (proved, Lean, toy).** DMP has two kinds of recorded value. A **minted value** (T4: fixed by both halves at
   the minting, changed only by both) can be changed by no single half in either direction; a **standing** (T24) can be tightened by one
   half alone. Along a chain of layers laid over a minted root, a minted value is the same at every layer as long as nothing is reminted
   (`minted_value_every_layer`); a standing only tightens, and one witness can drop it to zero at the first layer (`standing_can_drop_to_zero`).
   With the quantum and the tick minted, the layer clocks derived from the root (the wave clock), and one exact step rule that carries the
   act to each coarser grid, the act identity holds at **every** layer with the minted quantum, and 3s1t too
   (`act_identity_every_layer`, `space_time_every_layer`); the floor of `Reach.lean` then holds at every layer with the reach only
   tightening (`floor_every_layer_of_minting`). This removes the per-layer hypotheses the round-4 scout found in every DMP "same at every
   layer" law: they become one root plus one step rule. **"Perfect duality" is precisely the T4 rule: a value both halves must sign to
   change, in either direction.** A one-sided (T24) rule gives monotonicity, never conservation.
2. **What is conserved is the act, and the conservation is exact for every theory.** Under an exact, gauge-covariant, centre-respecting
   blocking the flux-carrying state and its act number pass through each layer unchanged, z(2L; fine) = z(L; blocked) (proved (paper),
   scout §2.4; r4-layer is formalising it). That is the Yang–Mills form of `act_identity_every_layer`: the act is the same, only its
   description changes. It holds for U(1), Z₂ and the finite groups too, so it can carry no gap (it passes every unit test by claiming
   nothing).
3. **Λ is the act's conservation seen in units, and it needs one more thing.** To compare acts across **scales** (box L with box 2L), not
   across resolutions, every layer's description must come from one one-parameter family (the blocked action is the Wilson action at
   another coupling, up to irrelevant terms). With that, the running coupling obeys one autonomous flow u(2L) = σ(u(L)), and the flow has
   exactly one constant of motion: the scale **Λ** (Callan, Symanzik). The running *is* the conservation (`lambda_conserved`): this is the
   owner's "conserved by the simple fact that it IS running", and it is exact as an identity along any such trajectory. Every physical
   quantity is then a pure number times a power of Λ (dimensional transmutation, Coleman and Weinberg; `mass_over_lambda_invariant`).
4. **Tie to G0 = inward reach, and it is asymptotic freedom (proved, Lean, one-loop toy; known for the real theories).** Following the
   running back to the root at infinite depth, Yang–Mills' coupling goes to zero (`af_tied`); φ⁴₄ and QED hit a Landau pole before the
   root (`irFree_not_tied`); the photon does not run at all (`photon_not_tied`, `photon_no_clock`). So the triviality test is passed for
   exactly the reason the owner gives.
5. **What it does not deliver.** Λ-conservation fixes the *form* m = c·Λ, never c > 0 (`massless_with_scale`). The Banks–Zaks theories are
   asymptotically free, tied to G0, conserve their Λ, and are gapless. The extra condition pure Yang–Mills needs is that the flow has
   **no infrared fixed point**; on a compact stretch of couplings this is equivalent to crossing the existence boundary in a bounded
   number of doublings (`crossing_of_no_fixed_point`, `no_crossing_of_fixed_point`, `crossing_of_clock`). That is the tuning step, weaker
   than the gap, and even "no fixed point anywhere" gives only flux-sector growth; the step to the vacuum-sector gap (the sector transfer)
   stays open.
6. **The two-sided cross-volume comparison (the round-3/4 obstruction).** Λ-conservation turns "two volumes" into "one function of one
   variable": z(2L) = σ(z(L)), an exact identity **conditional on** a continuum step-scaling function existing (existence plus
   universality). It supplies the *form* of a two-sided comparison, not its *content*: the inequality σ(u) ≥ (1 + δ)·u on the crossover
   stretch is exactly what is not conserved and not supplied. Precisely what stays non-conserved: the comparison of the blocked action with
   the original on the same box.
7. **The selection principle (§2.7).** An act with a floor forces its act number to grow without bound (`floor_forces_unbounded`), so an
   act whose number follows a flow with an infrared fixed point has no floor (`fixed_point_no_floor`): "hostable with a non-trivial act ⇒
   no infrared fixed point" (`floor_excludes_fixed_point`). This excludes the conformal window, but it **selects, it does not derive**:
   showing that pure SU(2) has such an act is showing that its running does not stall. DMP's existence demand is in the constitution's
   prose (Axiom 1's balance, G0's five parts, T39), ranked below safety (T3d), and `evidence/` states no liveness at all.
8. **DMP mints its outward reach; Yang–Mills must grow it.** In DMP the floor follows from the minting because the minting record also
   fixes the window (Axiom 2, T4: "no validity is longer than the time the minting accepts"): the outward reach R is a minted value. Yang–
   Mills can mint only one number (Λ). Its outward reach is not minted; it is a property of the flow (content, in Axiom 3's sense). That is
   where "everything else follows" stops being true for Yang–Mills, and where the open problem sits.

---

## 1. The DMP side, formal (`MintingDmp.lean`)

### 1.1 What the minting fixes, read from the constitution

- **G0** (`vendor/dmp/01-constitution.md`): the minting is "the one act ... from which every later standing descends"; at least five parts
  become the White Key Holders; it draws the boundary of the instance; mint prep runs only on a provably DMP-complete configuration (T40).
- **T4**: "How resilient trust must be (the failure classes, the windows, the floors above the derived ones, the thresholds above a
  majority, the staleness time, the rotation interval, the parameters of the field of T32) is fixed by both halves at the minting and
  changed only by a majority of trust, never below a floor." T5: a majority means a majority in **each** half. T24b (lockstep): a change of
  one half's standing toward the other is one record both sign.
- **T20 and the wave clock** (`evidence/Dmp/R1Wave.lean`): "now" comes from two independent time authorities (in the minting record's
  failure classes); the trust system steps forward in a wave propagated by the root Duality, layer k stepping once per b^k root steps
  (`wvLayerBy`, `wv_layer_succ`), and one witness never moves time (`wv_one_witness_never_moves`). No layer has a clock of its own.
- **Axiom 2**: "no validity is longer than the time the minting accepts between a loss and its effect at the point of use": the maximum
  time to live (the outward reach in time, Tmax of `Reach.mg_ttl_existence_floor`) is minted.
- **T24** (`evidence/Dmp/Standing.lean`): standings are tightened on one witness, loosened only with both.

So the minting record contains a quantum (the owner's rule), a tick (the time source), and a window. The question "which DMP property is
the perfect duality" has a precise answer: **the T4 rule**, a value that neither half can move alone in either direction. T38 (every layer
has two independent witnesses) and the frame rule (`Recipe.extend_preserves_decisions`) are the structure that carries such values down
the chain; re-keying invariance (`Gauge.loop_hol_rekey`) says the value does not depend on the frame. T24 alone is one-sided.

### 1.2 Theorems (proved, Lean; restated model, toy)

| theorem | statement | DMP section |
|---|---|---|
| `configStep_fixed`, `config_conserved` | an act not signed by both halves leaves a minted value unchanged; along any such sequence it is conserved | T4, T5, T24b |
| `minted_value_every_layer` | with no both-signed act on the chain (no reminting), every layer holds the minted value; one chain property, not one hypothesis per layer | G0, T4, T38 |
| `standingStep_le`, `standing_never_rises`, `standing_layers_only_tighten` | a T24 value only tightens, step by step and layer by layer | T24, Axiom 3 "a sub-layer only tightens" |
| `standing_can_drop_to_zero` | one witness alone drops a T24 value to 0 at layer 1 and it stays 0: no conservation, no floor | T24 |
| `res_succ`, `res_pos` | layer resolution k_n = k₀/bⁿ, derived from the root (the wave clock) | T20, `wvLayerBy` |
| `act_identity_every_layer` | root act x₀e₀ = Q k₀², one exact step rule (x and e divided by b per layer) ⇒ xₙeₙ = Q kₙ² at every layer | the owner's rule, `Reach.lean` |
| `space_time_every_layer` | space and time certificates carried from the root ⇒ eₙ = τₙ at every layer with xₙ ≠ 0 (3s1t) | `mg_space_time_certificate` |
| `floor_every_layer_of_minting` | minted Q, exact step, reach that only tightens (Rₙ ≤ R) ⇒ Q kₙ ≤ xₙ R at every layer | `mg_reach_floor_every_layer` without per-layer hypotheses |
| `frozen_no_floor` | the same quantum for acts of every extent (E(L)·L = Q for all L) ⇒ existence below every floor | `mg_no_reach_no_floor` |

**The precise DMP conservation statement.** *Let a chain of layers be laid over a minted root that fixes a quantum Q > 0, a tick (root
resolution k₀ and clock ratio b) and a window R. If no act on the chain is signed by both halves (no reminting), and each layer step
carries the act to the next coarser grid by one fixed rule, then at every layer n the act identity holds with the minted quantum,
xₙeₙ = Q·kₙ² (and with the time to live, xₙτₙ = Q·kₙ², eₙ = τₙ), and every act within the layer's reach has existence at least
Q·kₙ/R. If Q is held as a standing (T24) instead, there are chains on which it is 0 from layer 1 on.*

**What makes this more than the scout's L3.** `Reach.mg_reach_floor_every_layer` takes "the same Q and R at every layer" as hypotheses.
Here the hypotheses are the root's values plus two properties of the step: two-sided for the quantum (T4), one-sided for the reach ("a
sub-layer only tightens" is enough for the floor, because the floor needs an upper bound on the extent). **What it is not:** a deep
theorem. Its proofs are inductions of a few lines. Its value is in placing the content: everything hinges on the step rule being exact.

### 1.3 The owner's "lossy causality", in these terms

At G0 the root holds everything; each step after it is lossy. In the model, what is lost is the description (the grid on which the act is
written: k shrinks by b per layer, and every finer detail of the root is gone at the coarse layer); what is not lost is the act's
product xₙeₙ/kₙ², the quantum. **What passes a lossy step exactly is a minted number, never information.** In Yang–Mills the same split
holds (round 3, attempt 5: blocking can only lose distinguishability, `blocking_tightens`, and the photon saturates it): information falls
from layer to layer, the act and the scale do not.

---

## 2. The Yang–Mills counterpart

### 2.1 Two different "across the layers"

The DMP layer chain can be read in two ways on the Yang–Mills side, and they must be kept apart.

| reading | layer n | the act at layer n | is the act number conserved? |
|---|---|---|---|
| **across resolutions** (the r3-dmp hosting: root = bare measure, lines = blocked levels) | the same physical box, block size 2ⁿa | one physical flux state, written on a coarser grid | **yes, exactly, for every gauge group**: z(2L; S) = z(L; S_eff) (proved (paper), scout §2.4: centre transformations commute with a gauge-covariant, conjugation-equivariant blocking, the blocking is a Markov kernel, so every flux sector's partition function is preserved; formalisation: r4-layer) |
| **across scales** (box L → 2L at fixed physics) | a box of side 2ⁿL₀ | the flux spanning that box | **only for the photon**: z = e²/2 = 2πα at every L (known, classical). For SU(2) z runs (scout §2.2) |

The first reading is the faithful one for "the act is conserved" (the owner's precision): the flux sector is topological, a local
blocking can neither create nor destroy it, and its cost in quanta is carried unchanged. It is `act_identity_every_layer` in Yang–Mills
form. It holds for U(1), Z₂ and every finite group, so it is **infrastructure**, not a gap mechanism.

The second reading is what the mass gap and confinement need, and there the DMP law read literally (the same quantum at every extent) is
light's law: `frozen_no_floor`. So the conservation law cannot be "z is the same at every scale" for Yang–Mills. It is "Λ is the same at
every scale".

### 2.2 From the conserved act to the conserved scale: what has to be added

Combine the exact transport z(2L; S) = z(L; S_eff) with one further statement:

> **(U) one-parameter description.** The blocked action S_eff on the box L describes the same continuum theory as the Wilson action S at
> some coupling u′ on that box (the irrelevant terms that blocking generates do not matter in the continuum limit).

Then the act number of the box 2L is a function of the act number of the box L alone: **z(2L) = σ(z(L))** for one continuous function σ
(the step-scaling function in the act-number scheme). The flow is autonomous ("perfect duality": the same map at every layer, depending
only on the layer's own state). An autonomous one-variable flow has exactly one constant of motion. Writing it as a clock Φ that one
doubling advances by one (Abel's equation Φ(σ(u)) = Φ(u) + 1), the scale

  **Λ := 2^{Φ(z(L))} / L**

is the same for every L (`lambda_conserved`). In continuum notation, with β(ḡ) = −L dḡ/dL the scheme's beta function, this is the
standard exact formula (Luescher, Weisz, Wolff 1991 and the ALPHA papers; known, memory):

  Λ·L = (b₀ḡ²)^{−b₁/(2b₀²)} · e^{−1/(2b₀ḡ²)} · exp(−∫₀^ḡ [1/β(x) + 1/(b₀x³) − b₁/(b₀²x)] dx),

and (L∂/∂L − β(ḡ)∂/∂ḡ)Λ = 0 identically: the Callan–Symanzik equation (Callan 1970; Symanzik 1970). **The running is the conservation:**
the coupling changes with L exactly so that Λ does not. That is the owner's "conserved by the simple fact that it IS running".

**Is Λ-conservation the act's conservation seen in units?** Yes, with (U) as the price. The act number z is already a pure number (the
act's cost in quanta ħ). Within one theory and its descriptions, exact blocking conserves it (§2.1, first row): no units are needed and
no Λ appears. Λ appears when acts of *different size* are compared, which needs every layer's description to be a point of one
one-parameter family: then the cost of the act at size L is F(LΛ) with one universal F, and Λ is the act's cost measured against the
minted quantum (ħ) and tick (the root's spacing): Λ = a⁻¹·f(g₀²) with a the root's tick and g₀² its quantum. **The minting fixes the pair
(g₀², a); the conserved standing is one combination of the two, Λ; neither the bare coupling nor the tick is separately conserved.** Every
reminting at a finer tick with the bare coupling retuned to keep Λ (a line of constant physics) redeploys the same theory (reading: T40's
"a reminting ... and a redeployment of a sealed state are the same act").

### 2.3 What is exact, what is perturbative, what is a theorem for the lattice theory

| statement | level |
|---|---|
| z(2L; S) = z(L; S_eff) for a centre-equivariant gauge-covariant blocking, every group | **proved (paper)** (scout §2.4); Lean: r4-layer (its note had not appeared when this note was written, so no Lean names are cited) |
| exact blocking preserves every physical quantity in physical units | **exact**, trivial (the blocked measure is a push-forward) |
| given an autonomous continuous flow u ↦ σ(u), Λ defined by the clock is exactly layer-invariant; every quantity determined by the layer coupling is a fixed number times Λ^dimension | **exact identity**; toy **proved (Lean)**: `clock_iterate`, `lambda_conserved`, `mass_over_lambda_invariant` |
| the flow exists in the continuum and is autonomous: a step-scaling function σ (existence of the continuum limit at fixed L/L_ref, its uniqueness, and (U)) | **not proved** for 4D SU(2). Known: numerically established in the Schroedinger-functional scheme (Luescher, Sommer, Weisz, Wolff, Nucl. Phys. B389 (1993) for SU(2); memory); the OpenAI construction gives limits along subsequences (H1), which is less than a function σ; (U) is universality, known in perturbation theory (Symanzik's effective theory, 1983), open beyond it |
| b₀ = 11N/(48π²), b₁ universal; σ(u) = u + 2b₀ ln2·u² + O(u³) | **known, perturbative** (Gross, Wilczek; Politzer 1973; Caswell, Jones 1974 for b₁) |
| on the lattice at finite a, Λ is conserved only up to cutoff effects O(a/L) (O(a²/L²) improved) | **known** (Symanzik); controlled perturbatively only |
| the tie to G0: the bare coupling tends to 0 as the root goes to infinite depth at fixed Λ | **known, perturbative** (asymptotic freedom); for the lattice theory the ultraviolet part is Balaban's programme (small-field control at weak coupling, finite volume; memory) and the OpenAI construction (existence, `nonfree`); toy **proved (Lean)**: `af_root_infinite_depth`, `af_tied` |
| φ⁴₄: no tie (the trajectory hits a Landau pole before the root) ⇒ trivial continuum | **theorem** for the lattice φ⁴₄ and Ising models at all couplings: Aizenman and Duminil-Copin, Ann. Math. 2021 (every scaling limit Gaussian); toy **proved (Lean)**: `irFree_root_depth_bounded`, `irFree_not_tied` |
| QED: Landau pole | **perturbative** (Landau; Landau and Pomeranchuk 1955); non-perturbative triviality of QED is supported by lattice studies, **not proved** |
| m = c·Λ with c > 0 (the gap) | **open**; not supplied (`massless_with_scale`) |

Non-perturbative content that Λ-conservation adds by itself: **none beyond the exact identity**. Its whole non-perturbative weight is in
its hypothesis (a continuum, autonomous, one-parameter flow), which is H1-type (existence plus universality), weaker than the gap and not
known. Once granted, it makes the rest of the problem one function of one variable, which is a real simplification of the *form*.

### 2.4 "Tie to G0 is reach": the two reaches and the one sign

Reading (the owner's question, made exact in the toy): **inward reach** = how far the running can be traced back towards the root;
**outward reach** = Axiom 1's R, how far an act extends. In the one-loop toy (`oneLoop c : w ↦ w − c`, w = 1/u the inverse coupling, c =
2b₀ ln 2) the clock is Φ(w) = −w/c (`oneLoop_clock`), i.e. Λ·L = 2^{−w/c} = e^{−1/(2b₀g²)}, the transmutation formula. One sign trades
the two reaches:

| theory | sign | inward reach (tie to G0) | outward reach | Lean (toy) |
|---|---|---|---|---|
| Yang–Mills | c > 0 | unlimited: the root's coupling → 0 | limited **if** the gap holds | `af_root_infinite_depth`, `af_tied` |
| φ⁴₄, QED | c < 0 | limited: N·d < w_N layers (Landau pole) | unlimited (no infrared scale) | `irFree_root_depth_bounded`, `irFree_not_tied` |
| free photon | c = 0 | no running, no tie to make | unlimited | `photon_oneLoop`, `photon_not_tied`, `photon_no_clock` |
| Banks–Zaks | c > 0, infrared fixed point | unlimited | unlimited (conformal) | `no_crossing_of_fixed_point`, `massless_with_scale` |

The last row is why "unlimited inward reach forces limited outward reach" is false in general, and why Λ-conservation cannot be the gap.

### 2.5 Where the extra condition sits

**Precisely (proved, Lean, toy):** for a continuous flow on a compact stretch [a, b] of couplings,
- no fixed point (σ(u) > u on [a, b]) ⇒ one N such that every start in [a, b] reaches b within N doublings (`crossing_of_no_fixed_point`;
  the margin δ = min(σ(u) − u) > 0 comes from compactness);
- a fixed point u_f of a monotone flow ⇒ every start below u_f stays below it forever (`no_crossing_of_fixed_point`);
- a clock (finite Λ) on the whole stretch excludes fixed points there; with the asymptotic-freedom direction u ≤ σ(u) it gives the
  crossing (`crossing_of_clock`).

So, given (U) and a continuum σ: **crossing the existence boundary ⇔ no fixed point on the stretch ⇔ Λ stays finite through the
stretch.** This is the review's finding 1 made exact: "no fixed point" is a statement about σ and presupposes σ exists; it gives the
tuning step (target T1a of the scout, **weaker** than the gap). Growth without bound (no fixed point on [u_U, ∞)) gives z → ∞, flux-sector
growth (scout T1b, **incomparable** with the gap); turning that into a vacuum-sector gap needs the sector transfer (open).

**In DMP terms (reading).** DMP gets its floor because the minting record contains the window (§1.1): the outward reach is minted. In
Yang–Mills nothing but Λ can be minted; the outward reach has to be produced by the act itself. "No infrared fixed point" is the
condition that the act's cost keeps growing as it is spanned outwards, i.e. that nothing in the theory can carry the act's flux for free.
In a Banks–Zaks theory the massless matter does exactly that (it screens: the flux is partly carried by payload that needs no
witnesses), the cost stalls at a fixed value, and no outward reach forms. Pure Yang–Mills has no such payload: the flux is carried only
by the gluons, which carry the charge they transmit. That is the owner's earlier "self-charge" reading, now with its precise role: it is
not asymptotic freedom (which Banks–Zaks has too) but the absence of a screening channel at large distance. Whether that absence is enough
is the open problem; no DMP law in `evidence/` supplies it.

### 2.6 Where the inversion happens

If the flow crosses, Λ-conservation fixes the place of the existence boundary as **a pure number over Λ**: L_* = F⁻¹(z_*)/Λ, the same in
every description and at every resolution. It does not compute the number. In the one-loop toy the clock reaches 0 (Λ·L = 1) exactly
where w = 1/g² reaches 0, which is the scheme-dependent point where the one-loop description itself fails; the physical number L_*√σ
(heuristic ≈ 1.5 for z = 1, next to 1/T_c ≈ 1.41/√σ, scout §2.2) is a measurement (r4-actnumber). The inversion itself (electric flux
ceasing to exist freely while the twist does, 't Hooft duality) is r4-layer's and r4-conjw's subject; Λ-conservation says only that
wherever it happens, it happens at the same L·Λ at every layer.

### 2.7 The selection principle: "something inside DMP does exist" excludes an infrared fixed point

**(1) Where DMP demands an existing act (quoted from the files, read only).**
- `vendor/dmp/01-constitution.md:142-144` (Axiom 1, the balance): "A system that does nothing keeps the bounds and fails the balance: the
  balance is the one commitment that asks for something to happen, and it ranks below the bounds (T3d)."
- `vendor/dmp/01-constitution.md:226-228` (G0): "at least five parts become the White Key Holders, and that minting draws the boundary of
  the instance": a minted instance is never empty.
- `vendor/dmp/01-constitution.md:339-341` (T39): "only a Duality that is both trusted for its acts and holds the information admitted to it
  is a part of a minted CMOS. A part trusted with no information has nothing it may act on".
- Against it, honestly: `vendor/dmp/01-constitution.md:409-410` (T3d, "Safety before liveness"): when a half falls silent "the system is
  safe and not live, and the balance waits": the existence demand ranks **below** the bounds. And the formal chain states no liveness:
  `evidence/Dmp/Cmb.lean:340-342` (`empty_recipe_proven`: the empty recipe is "proven") and `evidence/Dmp/Refute.lean:6-10`
  (`rf_nothing_ever_performed`: "The chain states no liveness; it cannot distinguish a working CMOS from a switched-off one"). So the demand
  is a constitutional commitment in prose (the balance plus G0), not a theorem of `evidence/`.

**(2) The selection principle, precisely (proved, Lean, toy).** Call an act chain (existence Eₙ at layer n, box side 2ⁿL₀, act number
zₙ = Eₙ·2ⁿL₀) **hostable with a non-trivial act** when it has a floor: Eₙ ≥ m > 0 from some layer on (`HasFloor`, the DMP floor
x ≥ Q/R read along the chain). Then:
- `floor_forces_unbounded`: a floor forces zₙ to exceed every bound;
- `fixed_point_no_floor`: if zₙ = σⁿ(z₀) for a monotone flow σ with a fixed point u_f ≥ z₀ (an infrared fixed point: long-distance scale
  invariance, existence × extent stuck at one value), there is no floor: the act behaves like payload (the photon is the case σ = id,
  compare `frozen_no_floor`);
- `floor_excludes_fixed_point`: **hostable with a non-trivial act ⇒ the flow has no fixed point at or above the start.**

So the conformal window (Banks–Zaks) is not hostable with a non-trivial act in this sense, and the Banks–Zaks test is passed by
construction.

**(3) A selection principle, not a derivation.** The theorem has "the act has a floor" as its hypothesis. For pure SU(2), proving that
hypothesis is the same as proving that the running does not stall (no fixed point on [u_U, ∞) in the act-number scheme), i.e. flux-sector
confinement. DMP's demand "something must exist" can *select* which theories DMP can host; it cannot *prove* that Yang–Mills is one of
them. Any argument that took hostability as given for Yang–Mills would assume what is to be shown.

**(4) Is "exclude an infrared fixed point for pure SU(2)" a cleaner target than D′?** Cleaner, yes; easier, no. Three versions:
- *In the act-number scheme* ("σ(u) > u on [u_U, ∞)", so z → ∞): flux-sector confinement (scout target T1b), **incomparable** with the
  gap (deconfined Z₂ is gapped with falling z; and it does not give the vacuum gap without the sector transfer). It is scheme-bound: a
  gapped deconfined theory has an act-number "fixed point" at 0.
- *Scheme-free* ("no gapless, scale-invariant long-distance limit"): **implied by the gap** (exponential decay is not power-law decay), so
  it is no stronger than the gap, unlike D′ (strictly stronger, review finding 3). It is **equivalent** to the gap only under the infrared
  dichotomy "the long-distance limit of a unitary 4D theory is either gapped or scale invariant", a widely held expectation, not a theorem
  (known: in 2D scale invariance implies conformal invariance, Polchinski 1988; in 4D the a-theorem, Komargodski and Schwimmer 2011, and
  scale implies conformal in perturbation theory; memory). So it is the gap restated, with the dichotomy in between.
- *The trace anomaly* θ^μ_μ = (β(g)/2g)·F² (exact operator identity; Crewther; Chanowitz and Ellis 1972; Collins, Duncan, Joglekar 1977;
  memory) does **not** by itself separate the cases when phrased as "θ does not vanish at long distances": its correlations decay at long
  distances both in a gapped theory (exponentially) and at an infrared fixed point (where β → 0). What separates them is whether massless
  states remain (a_IR = 0 for an empty infrared). A trace-anomaly target would have to be a statement about the low-lying spectral weight
  of θ, which is again the gap.

Verdict: the selection principle explains cleanly *why* DMP's demand excludes the conformal window, and gives the Banks–Zaks test a
formal shape; as a proof target, "no infrared fixed point" is the gap (scheme-free, modulo the dichotomy) or flux confinement (act-number
scheme), not a new, weaker handle. Its advantage over D′: it is not stronger than the gap, and it can be stated without a scheme.

---

## 3. Does it supply the two-sided cross-volume comparison?

**Partly, in form; not in content.**

- **What it supplies (conditional on existence and (U)).** An exact identity between volumes: z(2L) = σ(z(L)). Rounds 3 and 4 had an
  exact identity only between *two actions on one box* (z(2L; S) = z(L; S_eff)). (U) identifies S_eff with S at another coupling and
  turns that into a function of one variable. Every cross-volume question becomes a question about σ on the compact crossover stretch.
- **Where it stays one-sided.** (i) The inequality σ(u) ≥ (1 + δ)u on the crossover stretch is not supplied: it is exactly what fails
  for Banks–Zaks, so it cannot follow from Λ-conservation plus asymptotic freedom. (ii) (U) itself is the comparison "blocked action
  versus original on the same box", the obstruction round 3 named: Λ-conservation **assumes** it. (iii) On the lattice at finite a the
  identity holds only up to cutoff effects, controlled only perturbatively.
- **Exactly what is not conserved.** The description: the effective action at each layer, and with it the comparison of S_eff with S on
  one box. The act (its flux sector and its cost in quanta) is conserved exactly; the scale Λ is conserved exactly along any one-parameter
  trajectory; whether the blocked description stays on that trajectory, and what σ does at α_s of order one, is not.

---

## 4. Unit tests

| test | the DMP law (§1) | act conservation (§2.1) | Λ-conservation and the tie (§2.2–2.4) | verdict |
|---|---|---|---|---|
| **photon** (4D U(1), weak coupling) | literal law across scales = frozen z = 2πα, and no floor (`frozen_no_floor`): no reach, `mg_no_reach_no_floor` | holds exactly; claims nothing | no running, no clock, no Λ (`photon_no_clock`, `photon_not_tied`); dimensional analysis with no scale gives m = 0 | **pass**: nothing gives U(1) an infrared floor |
| **Z₂**, weak coupling | — | holds; claims nothing | no continuum flow (first-order transition; Creutz, Jacobs, Rebbi 1979, memory); the act number falls with L (scout §2.2), the shape of `no_crossing_of_fixed_point`'s blocked or falling orbits | **pass** (no confinement claim; no gap claim to contradict) |
| **finite subgroups** of SU(2), large β | — | holds; claims nothing | no Lie algebra, no flow through weak coupling (freezing transitions; memory); z falls | **pass** |
| **triviality** (φ⁴₄) | — | — | Landau pole in the ultraviolet: no tie to G0 (`irFree_not_tied`); holding the infrared coupling fixed with the root at infinite depth is impossible; proved for the real theory by Aizenman and Duminil-Copin (2021) | **pass**: no interacting φ⁴₄ limit is produced |
| **deconfinement** (box thinner than 1/T_c) | — | holds at every L | claims no inequality at any L; L_*Λ and 1/T_c·Λ are pure numbers, not compared by the law | **pass** (no uniform-decay claim below 1/T_c) |
| **Banks–Zaks** (asymptotically free, infrared fixed point; Banks and Zaks 1982; e.g. SU(3) with about 9–16 massless flavours, SU(2) with two adjoint Dirac flavours as a lattice candidate, memory) | — | holds | Λ conserved, tied to G0, yet gapless: the law gives only m = c·Λ (`massless_with_scale`) and crossing only without a fixed point (`no_crossing_of_fixed_point`); the selection principle declares it not hostable with a non-trivial act (`fixed_point_no_floor`) | **pass**: no floor is claimed; any floor needs "no infrared fixed point", which Banks–Zaks fails |

Features used: none of the four features (twist eaters, continuum of fluctuations, b₀ > 0, self-charge) is needed for the exact
statements (they hold for every theory); b₀ > 0 enters through the tie to G0; the self-charge enters only in the reading of §2.5.

---

## 5. Claim discipline

| target | statement | vs the mass gap | level |
|---|---|---|---|
| DMP conservation law | §1.2, boxed statement | not a Yang–Mills statement (DMP model) | proved (Lean), toy |
| act conservation per layer | z(2L; S) = z(L; S_eff) | an identity, no strength | proved (paper); Lean in r4-layer |
| Λ-conservation | (U) + continuum ⇒ autonomous flow with one invariant Λ; every quantity = number × Λ^d | **weaker** (H1-type: existence plus universality) | exact given the hypotheses; hypotheses open |
| tie to G0 | asymptotic freedom; the root at infinite depth is free | **weaker** | known (perturbative; Balaban, OpenAI construction for the lattice UV); toy proved |
| crossing | no fixed point on the stretch ⇔ crossing in N doublings | **weaker** (tuning step) | proved (Lean) for the toy flow; for SU(2) a conjecture supported by numerics |
| selection principle | act with a floor ⇒ no fixed point at or above the start | a selection rule, not a Yang–Mills statement | proved (Lean), toy |
| no infrared fixed point (scheme-free) | no gapless scale-invariant long-distance limit | implied by the gap; equivalent modulo the infrared dichotomy (conjecture) | open |
| no fixed point on [u_U, ∞) (act-number scheme) | z → ∞ | **incomparable** (flux confinement) | open |
| what a gap would still need | (U) and existence of σ; no fixed point on [u_U, ∞); the flux-to-vacuum sector transfer; plus the review's list: existence and identification of the limit, physical observables, Osterwalder–Schrader positivity and Euclidean symmetry | — | open |

No claim here is "the open piece"; the list in the last row is not claimed to be complete.

---

## 6. Next step (one)

**Test the Λ-conservation hypothesis directly on the act-number data, before any further proof work.** Λ-conservation is a falsifiable
statement about measurements r4-actnumber is already set up to make: at several β, z(2L) plotted against z(L) (same physical L/a ratio
pairs) must fall on **one curve** σ after the continuum extrapolation (the autonomy of the flow, i.e. (U) on data), and that curve must
stay above the diagonal across the crossover (no fixed point; its minimum ratio is the δ of `act_reach` and of
`crossing_of_no_fixed_point`). Pre-register it as a reading of r4-actnumber's runs (no new GPU job): (1) collapse of σ across β within
errors; (2) min σ(u)/u on the stretch and where it sits; (3) the U(1) control giving σ = id (the photon's frozen flow); (4) the finite
group control giving σ(u) < u. If the collapse fails, the one-parameter description (U) fails for this scheme and the minting picture's
"everything else follows" does not hold in it; if it holds and σ stays above the diagonal, the tuning step is supported and the open work
narrows to the sector transfer. In Lean, the follow-up is to assemble r4-layer's exact transport with `crossing_of_clock` into one theorem
whose hypotheses name (U) explicitly.

---

## 7. Files

- `NOTE.md` (this note).
- `build.sh`: builds `Attempts.R4.MintingDmp` and `Attempts.R4.MintingScale` in WSL `~/formal-att-r4-4` only, prints `#print axioms` for
  every theorem, scans for `sorry`/`axiom`/`native_decide`
  (`wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/attempts/r4-minting/build.sh`).
- `../../../formal/Attempts/R4/MintingDmp.lean` (Mathlib only): `Act`, `Act.both`, `configStep`, `standingStep`, `runConfig`,
  `runStanding`, `layerValue`, `res`; theorems `configStep_fixed`, `config_conserved`, `standingStep_le`, `standing_never_rises`,
  `minted_value_every_layer`, `standing_layers_only_tighten`, `standing_can_drop_to_zero`, `res_succ`, `res_pos`,
  `act_identity_every_layer`, `space_time_every_layer`, `floor_every_layer_of_minting`, `frozen_no_floor`.
- `../../../formal/Attempts/R4/MintingScale.lean` (Mathlib only): `IsClock`, `oneLoop`, `TiedToGround`; theorems `clock_iterate`,
  `lambda_conserved`, `no_clock_of_fixed_point`, `photon_no_clock`, `mass_over_lambda_invariant`, `massless_with_scale`,
  `oneLoop_iterate`, `oneLoop_clock`, `af_root_infinite_depth`, `irFree_root_depth_bounded`, `photon_oneLoop`, `af_tied`,
  `oneLoop_root_forced`, `irFree_not_tied`, `photon_not_tied`, `crossing_of_no_fixed_point`, `no_crossing_of_fixed_point`,
  `crossing_of_clock`, `HasFloor`, `floor_forces_unbounded`, `fixed_point_no_floor`, `floor_excludes_fixed_point`.
- Build status: both modules build, Lean 4.34.0, Mathlib v4.34.0, no warnings in these files after the fix of a deprecated tactic name;
  34 theorems, all with axioms ⊆ {propext, Classical.choice, Quot.sound}.
