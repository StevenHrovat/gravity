# Cycle 5, workstream 5 (c5e-dmp): the DMP-native line, built (2026-11-22)

Task: blueprint v4 draft, section 6 (`../c4-fable/BLUEPRINT-v4-DRAFT.md`), plan step 6. Define the vacuum act number in Lean next to
`fluxRate`, state D-ID, D-S, D-T exactly, prove the doubling theorem; answer whether per-volume UV suffices; locate the cross-volume
step and look for a mechanism; pre-register the joint GPU measurement (not run); draft the photon-control change (proposal only).
Three owner readings that arrived during the work are folded in (section 5).

Claim levels: **Lean** (built, no `sorry`, no new axiom, no `native_decide`), **paper** (argued here), **known** (literature,
recalled unless marked read), **numerical** (existing data, read only), **reading** (an interpretation), **SPECULATIVE**.

---

## 0. In plain words

1. **The objects exist in Lean, on the real 4D SU(2) Wilson measure.** In a periodic box L³ with the time extent sent to infinity,
   the connected correlation of every centre-even slice observable is a reflection-positive Hankel sequence (new: `IsConnLimit`,
   `rpSeq_of_isConnLimit`). The vacuum energy gap `E0 β L` is the best rate that bounds all of them; it is attained and it is
   exactly the box gap in the sense of decay rates (`decayLB_E0`, `E0_le_rate`). `z0 = L · E0` is the vacuum act number; `ze` the
   flux act number built the same way from `fluxRate`'s objects.
2. **The doubling theorem is proved** (`su2_box_gap_of_DS_DT`): if the act numbers start above thresholds in one box (D-S) and the
   vacuum act number at least doubles up to a summable loss from box to doubled box while the flux threshold persists (D-T), then
   every dyadic periodic box has the same gap `m = (ζ₀/L₀)·e^{−2Ση} > 0` for every centre-even observable. Also proved: a late start
   is enough when every box has a positive gap; a start from small boxes plus uniform growth on a compact stretch reaches the
   threshold (the reach step); and the unit tests: a frozen act number (photon, z₀ = 2π) needs loss η ≥ ½ at every step, and no
   bounded act number (lattice photon, infrared fixed point) can satisfy D-S ∧ D-T.
3. **D-T is the infrared statement, exactly** (`doubling_of_antitone_gap`): when the box gaps decrease towards a positive limit, D-T
   holds with equality and summable loss. The factor 2 in "z₀ doubles" is the doubled extent, nothing more. DMP renames here.
4. **Per-volume UV is enough, and for a reason that cuts both ways.** If D-S and D-T are stated per box, eventually in the lattice
   level (spacing first at fixed physical box, the OpenAI order), no volume-uniform ultraviolet estimate is needed: the line needs from
   the ultraviolet only identification and existence per volume (compactness gives the limit points, decay bounds survive limits).
   But that is because D-S and D-T are continuum statements about boxes of size about 2–3/√σ, and such a box contains the whole
   crossover. Published per-volume UV control (Balaban type, the OpenAI construction) ends at a weak-coupling scale far below L₀ and
   says nothing about z₀(L₀). The existing per-volume theorem (`perVolumeGap`) is a different route and is not used; its unconditional
   part (`exists_blockLimit`) is the compactness that the line gets free anyway.
5. **The cross-volume step, located:** D-T at one n, i.e. `E₀(2L) ≥ (1 − η) E₀(L)` for the continuum boxes. Through reflection
   positivity it becomes a bound on a ratio of partition functions of the 2L torus by data of the L torus, which needs an upper bound
   on one and a lower bound on the other at matched parameters: the step Ito and Seiler found unproved in Tomboulis (their (3.5)).
6. **What DMP supplies for it.** Precise names: minted versus standing (D-T needs a value both boxes sign; every known inter-volume
   inequality is a standing); "sector transfer" becomes literal in the crossover (the lowest centre-even state of a small periodic box
   is a pair of flux tubes, z₀ ≈ 2z_e, so in that range D-T for z₀ follows from flux growth, which is Conjecture W, also cross-volume);
   minting gives the one-flow form z₀(2L) = σ(z₀(L)). No mechanism. A no-go for the cheap kind: every DMP object formalised so far is
   group-blind, and any group-blind inequality also holds for the binary icosahedral group, whose act numbers freeze at weak coupling.
7. **The owner's readings point to the one known kind of mechanism, and to where it stops.** Binary existence plus a stateless
   adjoint layer plus a curvature clock is the Dobrushin/Ollivier endpoint: positive worst-case curvature at one block scale gives
   volume uniformity with no doubling law at all (the contraction is local and per step). This passes the photon (flat), the
   deconfinement (centre layer orders, curvature → 0) and the finite-subgroup tests (the 2I adjoint layer A₅ is not stateless at weak
   coupling). It moves the core to: reaching the binary regime under blocking without losing content, with worst-case validity
   (blueprint v4 strategies (a)/(b)). A second, new candidate: in a binary ferromagnetic layer, Simon–Lieb-type inequalities turn a
   one-box criterion into decay in all volumes (one-sided in the right direction); whether the centre layer of SU(2), with the
   adjoint layer integrated, keeps the needed positivity is open (SPECULATIVE).
8. **Existing data allow a rough look** at the "forced binary" scale: the fitted coarse fundamental coupling of the good blocking
   falls monotonically with L at all three β (approximate collapse), and crosses a crude Z₂-critical estimate near L√σ ≈ 1.0–1.3,
   the same order as 1/T_c ≈ 1.41; the adjoint couplings are ≤ 0.01 from L√σ ≈ 1.4 on. Not a test (content check failed at 8 of 9
   points; crude projection).
9. **Pre-registration written** (`PREREG-JOINT.md`, not run): z₀ and z_e on the same periodic configurations (existing
   `run_su2_gpu.py`, unchanged; z₀ from the A1⁺⁺ glueball operators plus a flux-pair operator formed in the analysis), β = 2.3, 2.4,
   2.5, L√σ from 1.03 to 4.20, 9 doubling pairs, about 2.5 GPU hours (±50 %) plus an optional 1.4 h point. Verdicts fixed. The photon
   control becomes the exact free-photon formula (z₀ = 2L·arsinh(sin(π/L)) → 2π; z_e = g²/2): **proposal, owner's decision.**

---

## 1. Objects and hypotheses (exact statements)

All in `formal/ProofPhase/DMP/` (namespace `ProofPhase.DMP`), lattice units, fixed coupling β.

**Lattice.** `ℤ/Tℤ × (ℤ/Lℤ)³`, `T → ∞` along `T_M = 2(M+1)` (Route B's time chain). `su2W L β P`: the SU(2) Wilson chain weight
with magnetic twist `P` (`P = ∅`: periodic box).

**Connected correlation.** For bounded measurable `f` of one time slice: `nMean w T f = ⟨f(a₀)⟩_T` (normalised),
`connSeq w f M t = ⟨(f − ⟨f⟩)(a_t)(f − ⟨f⟩)(a₀)⟩_{T_M}`; `IsConnLimit w f h` ⇔ `h` is a pointwise limit of `connSeq w f · t`
along a subsequence `M → ∞`. Proved: limits exist; every limit is an `RPSeq` (Hankel Cauchy–Schwarz, `h(2j) ≥ 0`, bounded).

**Vacuum sector.** `VacObs L`: `f` bounded, measurable, `CentreEven negOneSU2 f`, where `centreFlip z i c` multiplies the
direction-`i` links of the plane `xᵢ = c` by `z`, for all `i ∈ Fin 3`, `c`. (It keeps flux pairs: two units of Z₂ flux are none.)

**Gap numbers.** `DecayLB H E :⇔ ∀ h ∈ H, ∀ t, |h t| ≤ h 0 · e^{−E t}`; `gapOf H = sSup {E | DecayLB H E}`.
* `E0 β L = gapOf (vacLimits β L)`, `vacLimits β L = {h | ∃ O : VacObs L, IsConnLimit (su2W L β ∅) O.f h}`;
  **`z0 β L = L · E0 β L`** (vacuum act number).
* `Ee β L P = gapOf (fluxLimits β L P)` (`fluxLimits` = the `IsFluxLimit` objects of `fluxRate`); **`ze β L P = L · Ee β L P`**.
* Meaning (Lean): `decayLB_E0` (if `E0 > 0`, it is attained), `decayLB_of_le_E0`, `E0_le_rate` (`E0 ≤ rate h` for every
  non-vanishing vacuum limit), `Ee_le_fluxRate`. So `E0` is the box gap: no vacuum-sector correlation decays slower, and it is the
  best uniform rate. (`ze` is `actRate` of `Objects.lean` made uniform over the time limits.)

**Hypotheses** (boxes `side L₀ n = 2ⁿ L₀`; twist family `P : (L : ℕ) → Finset (LatticePlaquette 3 L)`; thresholds `ζ₀, ζe`;
loss `η`):
* **D-ID.** Abstract: `BoxGaps` = predicates `Q n E` ("box n has gap ≥ E"), downward closed, attained at their supremum when it is
  positive. On the lattice this is a **theorem** (`latticeBoxGaps β L₀`). In the continuum (spacing first, fixed physical box) it is the
  open existence-and-identification input; nothing else of the continuum is formalised.
* **D-S** `DS β P L₀ ζ₀ ζe :⇔ ζ₀ ≤ z0 β L₀ ∧ ζe ≤ ze β L₀ (P L₀)`.
* **D-T** `DT β P L₀ ζ₀ ζe η :⇔ ∀ n, ζ₀ ≤ z0(2ⁿL₀) → ζe ≤ ze(2ⁿL₀) → 2(1 − η n)·z0(2ⁿL₀) ≤ z0(2ⁿ⁺¹L₀) ∧ ζe ≤ ze(2ⁿ⁺¹L₀)`.
* **loss** `AdmissibleLoss η :⇔ (∀ n, 0 ≤ η n) ∧ (∀ n, η n ≤ ½) ∧ Summable η`. The ½ keeps the vacuum threshold; finitely many
  larger losses are absorbed by a later start (`floor_of_eventual_start`).

Sharper than the draft in two places: the thresholds are part of the premise of D-T (D-T is only asked where both act numbers are
above threshold), and the flux clause is visibly a domain restriction: the conclusion uses z₀ only. Consequence (honest): the line is
blind to gapped theories without flux growth (Z₂ at weak coupling: gapped, z_e → 0). That is a missed claim, never a wrong one.

## 2. Lean

Files: `formal/ProofPhase/DMP/Doubling.lean` (abstract, real analysis), `formal/ProofPhase/DMP/VacuumAct.lean` (objects).
Build: `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c5e-dmp/build.sh` in
`~/formal-c5e`: "Build completed successfully" for both modules. `axioms.sh`: all 55 declarations depend only on `propext`,
`Classical.choice`, `Quot.sound` (`centreFlip`: none; `side`: `propext`); no `sorry`, `native_decide` or `axiom` (`axioms.log`).

| theorem | statement | kind |
|---|---|---|
| `floor_of_doubling` | D-S ∧ D-T ∧ loss ⇒ `z n/(2ⁿL₀) ≥ (ζ/L₀)·e^{−2Ση}` ∀ n | abstract, the doubling theorem |
| `BoxGaps.floor` | D-ID ∧ D-S ∧ D-T ∧ loss ⇒ ∃ m > 0, ∀ n, `Q n m` | abstract |
| `su2_box_gap_of_DS_DT` | `DS ∧ DT ∧ AdmissibleLoss ⇒ ∃ m > 0, ∀ n, ∀ O : VacObs (2ⁿL₀), ∀ h, IsConnLimit … O.f h → ∀ t, |h t| ≤ h 0·e^{−mt}` | **the finite-volume gap statement on the SU(2) objects** |
| `floor_of_eventual_start` | all boxes have `z n > 0`, D-S ∧ D-T from box N on ⇒ uniform floor ∀ n | abstract |
| `crossing_of_growth` | `a ≤ z 0`, growth `δ > 0` on `[a, ζ)` ⇒ ∃ N, `ζ ≤ z N` | abstract (reach) |
| `frozen_violates_doubling` | constant `z = c > 0` with D-T ⇒ `η n ≥ ½` ∀ n, not summable | unit test (photon) |
| `bounded_violates_doubling` | `z` bounded ⇒ ¬(D-S ∧ D-T ∧ loss) | unit test (lattice photon, IR fixed point) |
| `doubling_of_antitone_gap` | `E` antitone, `E ≥ m > 0` ⇒ D-T with equality, `η = 1 − E(n+1)/E n ≥ 0` summable | D-T is the gap |
| `decay_of_limit` | box bounds pass to pointwise limits of correlations | volume limit, abstract |
| `rpSeq_of_isConnLimit`, `exists_isConnLimit` | connected limits exist and are RP Hankel | substantive (lattice) |
| `decayLB_gapOf`, `gapOf_le_rate`, `E0_le_rate`, `Ee_le_fluxRate` | the gap number is attained and bounds every rate | substantive (lattice) |

Substantive: the connected-correlation layer (RP of centred slice observables in the limit `T → ∞`) and the identification of `E0`
with the box gap. Definitional: the names "act number", "doubling law"; D-T's relation to the gap. Not formalised: the continuum
D-ID; the bridge from the time-first boxes `L³ × ℝ` to the symmetric tori of `MassGapMFLoc` (section 3, item U3); Perron–Frobenius
(`E0 > 0` for each finite box, used on paper in `floor_of_eventual_start`).

## 3. "IR ⇐ D-T ∧ D-S ∧ per-volume UV": does per-volume UV suffice?

**Statement (paper).** Let `T` be a tuning on a line of constant physics whose physical volumes are dyadic, `ℓ_j = 2^j L₀` (the
`Tuning` structure allows this choice). Suppose, for each j, **eventually in the level k** (k ≥ k₀(j), k₀ may depend on j):
(D-S) `z0(level k, box L₀) ≥ ζ₀`, `ze ≥ ζe`; (D-T) the doubling inequality between boxes j and j+1 with loss η_j (physical units:
z₀ = ℓ · E₀ with E₀ in units of 1/length). Then for every j, eventually in k, every vacuum-sector connected correlation of the box j
obeys `|h(τ)| ≤ h(0) e^{−mτ}`, m = (ζ₀/L₀)e^{−2Ση} (Lean: `su2_box_gap_of_DS_DT` applied level by level with K(j) = max_{i≤j} k₀(i)).
Spacing first at fixed j: every limit point obeys the same bound (closed condition, `decay_of_limit`). Then the volume: same.

So **no volume-uniform UV statement is needed**: the order "spacing first, then volume" only ever asks for the levels beyond k₀(j)
in volume j. This confirms the draft's click 1 (c3d: "the whole gap is volume-uniformity").

**What the per-volume UV half must still supply**, item by item:
* (U1) **existence of limit points** per volume: free (compactness, as `exists_blockLimit` and `exists_isConnLimit`).
* (U2) **identification**: the tuning is Yang–Mills (`OnLCP'`, `NonTrivial`); external (OpenAI construction) plus our bridge, as in
  v4 section 3.1. Unchanged.
* (U3) **geometry and observables**: `MassGapMFLoc` is stated for slab observables on symmetric tori (time extent = L), the line for
  slice observables of `L³ × ℝ`. Two ways: (i) state the target in the time-first order (an equally standard order: Hamiltonian in
  each box, then volume), where the line's conclusion is the gap directly; (ii) a thermal bridge **D-Th**: `sup_j Tr R_{ℓ_j} < ∞`,
  where `Tr R_s = Σ_{n≥1} e^{−(E_n − E_vac)s}` is the excess partition function of the box at temperature 1/s. The gap alone does
  not give D-Th (it bounds each term, not the number of low states); physically D-Th is `ℓ⁴ e^{−mℓ}`-small. Choose (i) for the line;
  record (ii) as an open bookkeeping-with-content lemma.
* (U4) **dyadic to all volumes**: not needed if the tuning's volumes are dyadic (every `vol` of `MassGapMFLoc` is then dyadic).

**What it does not mean.** It does not make the problem perturbative. D-S is a statement about the continuum box of side
L₀ ≈ 2–3/√σ, and that box contains all scales from the cutoff to L₀, the whole crossover. Per-volume UV "control" in the published
sense stops far below:
* **The OpenAI construction** (`../../H1-OPENAI.md`, read): per-volume convergence of smeared local moments, spacing first, symmetric
  tori, at their unit scale where g² ≈ 10⁻⁶; nothing at the scale of a box with z₀ of order one; no `T → ∞` boxes; no spectral data.
  It supplies (U1)–(U2) in the symmetric-torus order. It does not supply any value of z₀.
* **Balaban** (unread here) and Magnen–Rivasseau–Seneor: ultraviolet stability in a finite box, same verdict (recalled).
* **Our `perVolumeGap`**: needs `LimitDprimeAll` (H2-all, the crossover itself). It is an alternative route to the gap, not an input
  to this line. Its unconditional part `exists_blockLimit` is (U1).
* **D-UV (small boxes)**: Luescher's small-volume expansion (z₀ ∝ g(L)^{2/3}, recalled; rigour not checked) would give D-S only at
  a small box, where D-T is false (z₀ grows like g^{2/3}, far from doubling). To start there one needs the reach step: uniform growth
  of z₀ on a compact stretch up to the threshold (`crossing_of_growth`), a statement on finitely many boxes, non-perturbative.

**Answer.** Per-volume UV suffices for the *logic* (no volume-uniform locality, no `EnvelopeW`, no exact-cover problem). The existing
per-volume theorems and the published bounds supply existence and identification per volume, nothing more; the non-perturbative
content of one box (D-S, or D-UV plus a crossing on a compact stretch) and the cross-volume content (D-T) stay. The line is
**"ID per volume ⇒ (D-S ∧ D-T ⇔ the gap along dyadic boxes, time-first order)"**; the second arrow is `doubling_of_antitone_gap` in
one direction and `su2_box_gap_of_DS_DT` in the other.

## 4. The cross-volume step and what DMP does with it

### 4.1 Located

The only step that compares two volumes is D-T at one n: `E₀(2L) ≥ (1 − η(L)) E₀(L)` (continuum boxes, or lattice boxes at the same
fine level). D-S is a one-box statement; the crossing is a finite set of one-box statements; the rest is proved.

Why it is two-sided. A lower bound on E₀(2L) is an upper bound on vacuum correlations in the 2L box. Reflection positivity and
chessboard estimates do bound 2L correlations from above, but by expectations of fully reflected observables **in the same 2L torus**,
i.e. by ratios `Z_{2L}[f]/Z_{2L}` of partition functions of the big box. Turning those into L-box data needs an upper bound on the
numerator and a lower bound on the denominator by the L box, to accuracy O(1) in the exponent (not o(volume), which subadditivity
gives). Decimation (Migdal–Kadanoff/Hoelder), chessboard and RP each give one direction, for every compact group with positive
character expansion. Tomboulis's matching α(t*) = α⁺(t*) is this step for the twist free energy; Ito and Seiler reduce it to their
unproved (3.5) and note it fails for U(1) (r3-monotone, section 1, read there). For the vacuum act number the step has the same
structure with the twist replaced by the vacuum-correlation insertion.

Necessary features of any proof of D-T (paper, from the unit tests): it must fail for the free photon (Lean: frozen and bounded act
numbers violate D-T), so it must use non-abelian structure; it must fail for the binary icosahedral group at weak coupling, whose act
numbers freeze (r3-monotone, r4-conjw: tunnelling cost about 0.955βN²), so it must use the continuum of the group (where b₀ > 0
lives); and it must fail for Banks–Zaks (IR fixed point: bounded act number), so it must use the absence of light matter.

### 4.2 DMP's objects, one by one

| DMP object | on D-T | supplies or renames |
|---|---|---|
| minted vs standing (r4-minting) | D-T is a minted rule: a value the 2L box and its L sub-boxes must both sign. RP, chessboard, decimation, Griffiths-type monotonicity are standings: one box can tighten them alone. The only minted inter-box datum is the centre flux through a common face (Gauss's law: both sides see the same flux) | **names the step exactly; supplies nothing**: the minted flux is conserved, but the energy per flux is a standing |
| act identity, minting, Λ (r4-minting) | in the continuum z₀(L) = Z(LΛ) for one function Z (dimensional transmutation), so z₀(2L) = σ₀(z₀(L)) with σ₀ = Z(2Z⁻¹(·)) when Z is injective: D-T becomes `σ₀(u) ≥ 2u(1 − η(u))` for u ≥ ζ₀, one function of one variable | **form, not content** (as r4-minting found for z_e) |
| inward reach = asymptotic freedom (G0) | z₀ > 0 and small in small boxes; D-T false there (sublinear growth). Gives a start below threshold, then the crossing needs uniform growth on a compact stretch (`crossing_of_growth`: no fixed point of σ₀ on the stretch) | **supplies D-UV at physics level**; the crossing is the tuning step (finite, non-perturbative) |
| outward reach = confinement | z_e ~ σL²; the act-number reading of the gap is z₀ ~ mL | renames |
| sector transfer, "how existence is built" | **clicks, in a range**: on a periodic box the centre-even sector contains flux pairs (two Z₂ units = none). For L√σ ≲ 2 the lowest A1⁺⁺ state of SU(2) is known to be a torelon pair in small boxes (recalled, glueball spectroscopy), z₀ ≈ 2z_e^{per} − binding. There the vacuum act is literally built from two flux acts, and D-T for z₀ follows from the growth of z_e (factor about 4 per doubling: σL²). Beyond the switch (2E_e^{per} ≈ m, L√σ ≈ 2) the glueball branch takes over and the flux side no longer controls z₀; the Heller endpoint (fundamental-adjoint action, massless 0⁺⁺ with confinement intact) shows the glueball branch can fail while the flux branch grows | **supplies a mechanism below the switch, reduced to Conjecture W (flux-side doubling, also cross-volume); not above**. Measurable: section 7, reading J3 |
| dimension swap (`tHooft_rotation`) | E₀(L) is the time decay of `L³ × ℝ`; rotating gives `ℝ × L³`, the same geometry. On the symmetric box T = L the swap relates E₀ to the thermal sum at temperature 1/L (item U3) and puts the self-dual point at z ≈ 0.88 | **a check and a bridge (D-Th), not a step** |
| "−1 is a commutator" | separates SU(2) from U(1), not from 2I | necessary, not sufficient |

### 4.3 Mechanisms that do supply a cross-volume step, and why none is DMP-native in the typical-case form

Known mechanisms that turn one-box information into all volumes (recalled; none read in full text this session):
1. **Worst-case contraction at one scale** (Dobrushin; Dobrushin–Shlosman's constructive criterion; Ollivier's coarse Ricci
   curvature). Positive curvature of a block dynamics, uniformly over boundary conditions, is a local per-step property, so it holds in
   every volume at once: no doubling law is needed. Price: worst-case validity (all boundary conditions), and a lossless description at
   the scale where it is checked. This is v4 strategy (b) (and (a) with the lossy block plus Lemma X).
2. **Recursive spectral-gap bounds for Glauber dynamics** (Martinelli; Bertini–Cancrini–Cesi): gap(2L) ≥ gap(L)(1 − ε(L)) with ε from
   spatial mixing at scale L: exactly D-T's form, for a dynamical gap, driven by a decorrelation input at the same scale. Not available
   for transfer-matrix gaps of gauge theories.
3. **Finite-size criteria for frustration-free Hamiltonians** (Knabe; Gosset–Mozgunov; martingale method of Nachtergaele): a gap
   threshold in one patch implies the gap in all volumes. The Kogut–Susskind Hamiltonian is not frustration-free: not applicable.
4. **Simon–Lieb inequality and sharpness** (Simon; Lieb; Aizenman–Barsky–Fernandez; Duminil-Copin–Tassion): in ferromagnetic binary
   (Ising-type, also plane-rotator) systems a finite-box criterion φ(Λ) < 1 implies exponential decay in all volumes. The inequality is
   one-sided, in the right direction, because positivity (Griffiths) makes the big-volume correlation controlled by small-box data.

Why none is DMP-native in the form of section 6 of the draft: the line is typical-case (no boundary conditions) and its objects
(act identity, minting, standings) are group-blind. A typical-case, group-blind inter-volume inequality would hold for 2I and fail its
test (4.1). The mechanisms that work are either worst-case (1) or use a sign structure of a binary layer (4). Both are exactly where
the owner's new readings point (section 5).

## 5. The owner's three readings (cycle 5), folded in

Recorded in `../../PREP.md`, last section, with the coordinator's interpretation. Summary of the readings: (a) a universal rate,
"1/e per tick", in the information half; binary existence inside the volume; a stateless information layer reorganising on top;
indistinguishable deploys; (b) correction: "The 1/e is the universal information tick, the existence tick is still gravitational"
(two clocks: the information clock universal, the existence clock set by curvature); (c) "confinement is a state where the existence
boundary has contracted so far that existence is forced into a binary state, at which point a boundary is spanned and the
perturbance isolated."

### 5.1 The two-layer form (reading)

SU(2) = Z₂ (centre, binary) and SO(3) = SU(2)/Z₂ (adjoint). Tomboulis's representation writes the SU(2) measure as SO(3) links coupled
to Z₂ plaquette variables (thin vortices) (recalled). Dictionary:
* **existence layer** = the Z₂ vortex layer; its act number = the flux act number z_e (and the twist free energy, its dual);
* **information layer** = the SO(3) layer; "stateless" = its conditional law given the vortices mixes at a rate that does not depend on
  the volume or on the vortex configuration (a conditional Dobrushin condition, which is volume-uniform automatically);
* **"indistinguishable between deploys"** = uniqueness of the equilibrium state (no phase coexistence);
* **"forced binary"** = after enough blocking the adjoint couplings are negligible and only the centre datum carries influence: the
  blocked theory is an effective Z₂ gauge theory plus noise in the adjoint layer.

Measured fact that matches (c4d, c3b; numbers as recorded there): at L√σ = 2.80 the adjoint half of the single-link W₁ column is
0.0036, the centre half 0.673, **in the plaquette-only truncation**. With more loop families the column rises to 0.96 and 0.9999
(review W5: "LIKELY the all-loops single-link column at 2.80 is not below 1"). So the adjoint layer is stateless at L√σ = 2.80 in every
truncation; the centre layer's margin is truncation dependent and may be zero.

### 5.2 A DMP-native doubling law in two layers, and the curvature form

**Candidate (paper, SPECULATIVE in its truth, exact in its form).** At a block scale ℓ (cells of side ℓ, lossless description):
* (L-A) **information clock**: for every vortex configuration, the conditional SO(3) law satisfies a W₁ Dobrushin condition with
  constant γ_A(ℓ) ≤ γ̄_A < 1 (universal: one rate per block step, volume-free);
* (L-C) **existence clock** (curvature form): the centre layer's block dynamics, with the adjoint layer relaxed, has worst-case coarse
  Ollivier curvature κ_C(ℓ) ≥ κ₀ > 0, i.e. W₁ contraction 1 − κ_C per block step, uniformly over the outside configuration;
* then the halves criterion γ_A + (1 − κ_C) < 1 is a Dobrushin condition for the whole cell system, and Dobrushin gives exponential
  decay, uniformly in the volume, with **no doubling law**: the curvature is local and per step.

The coordinator's question, "does coarse curvature of the centre layer improve or at least persist under doubling?":
* In worst-case form, persistence is not an extra hypothesis: positivity at one scale already gives all volumes, and
  Dobrushin–Shlosman's theory (complete analyticity) gives the condition at all larger cell sizes (recalled). So **in the curvature
  form, D-T is replaced by worst-case validity at one scale.** That is the honest trade: no cross-volume step, but a statement about
  every boundary condition, which is what nobody can check at L√σ = 2.8 (c4d's certificates are single-link, fitted actions, truncation
  dependent).
* In typical-case (annealed) form, persistence under doubling is the content again (v4 strategy (c), rare defects).
* In the fitted, lossy description the centre coupling falls by about a factor 2 per doubling at L√σ ≥ 2 (table below), so the
  centre half would fall and the curvature would improve. **This is not evidence:** the content check fails at those points, and a
  block variable that turns into noise has curvature 1 (pure noise has a gap: the noise-limit trap, v4 section 5).

**Unit tests of the two-layer form.**

| test | (L-A) | (L-C) | verdict |
|---|---|---|---|
| photon U(1) | no separate adjoint layer (U(1)/U(1) trivial) | no binary layer: the centre is the whole continuous group, flat (κ → 0 at all scales: Coulomb phase) | fails, correctly ("light is flat" by construction) |
| deconfinement (one direction short) | holds | the centre layer orders (Polyakov loop), two equilibria, worst-case curvature → 0 | fails, correctly; also fails uniqueness ("distinguishable deploys": the two centre vacua) |
| finite subgroup 2I at weak coupling | **fails**: the quotient A₅ is finite and orders at large β (holds state) | binary layer present | fails, correctly. This is the first DMP-native statement that passes the finite-subgroup test: "stateless" separates SU(2) from 2I, which "−1 is a commutator" and "binary centre" do not |
| Z₂ at weak coupling | trivial | ordered (deconfined, gapped) | no claim (sufficient condition; misses a gapped theory, never wrong) |
| mixture / Heller endpoint | fails at the endpoint (the bulk transition of the mixed action is an SO(3)/Z₂ monopole transition, recalled) | — | fails, correctly |
| Banks–Zaks with adjoint fermions (centre kept) | fails: massless adjoint modes are a layer with state | — | fails, correctly. With fundamental fermions there is no centre: no binary layer |

### 5.3 "Forced binary" as a no-fixed-point statement; a rough look at existing data

Form (paper): let u(L) be the effective Z₂ coupling of the blocked centre layer at block size L. "Forced binary under doubling" is a
one-variable flow u(2L) = σ_C(u(L)) with σ_C(u) < u on a compact stretch [u_end, u_start] (no fixed point), which by r3-monotone's
reach theorem (and `crossing_of_growth` here, with z replaced by 1/u) reaches the strong-coupling side u_end < u_c(Z₂) in a bounded
number of doublings. Deep there the effective Z₂ theory with a stateless adjoint layer is in a convergent strong-coupling expansion,
which gives volume-uniform decay at one scale (mechanism 1 of 4.3). So in this form the **infinite** doubling law is replaced by a
**finite** crossing plus an endpoint expansion; the content moves to (i) the flow being one-variable (a lossless blocking whose
effective action stays in a one-parameter family up to irrelevant terms) and (ii) the endpoint expansion applying to the true blocked
measure (all loops, worst case). Both are the "reaching the binary regime under blocking without losing content" of the coordinator's
reading.

**Existing data** (`../c3b-refit/runs-gpu/refit_summary.json`, read only, not a measurement; fitted coarse couplings of the good
blocking, Wilson normalisation as fitted there; ts = time-space planes, ss = space-space):

| β | b | L√σ | content | bF_ss | bF_ts | bA_ss | bA_ts |
|---|---|---|---|---|---|---|---|
| 2.5 | 4 | 0.73 | no | 1.79 | 1.30 | −0.011 | −0.083 |
| 2.4 | 4 | 1.03 | no | 1.33 | 0.84 | 0.001 | −0.034 |
| 2.3 | 4 | 1.40 | no | 0.83 | 0.40 | 0.008 | −0.008 |
| 2.5 | 8 | 1.46 | no | 0.70 | 0.34 | 0.005 | −0.007 |
| 2.4 | 8 | 2.06 | no | 0.34 | 0.11 | 0.003 | −0.002 |
| 2.3 | 8 | 2.80 | **yes** | 0.17 | 0.054 | 0.0015 | −0.0006 |
| 2.5 | 16 | 2.92 | no | 0.15 | 0.048 | 0.0010 | −0.0005 |
| 2.4 | 16 | 4.13 | no | 0.10 | 0.034 | 0.0007 | −0.0002 |
| 2.3 | 16 | 5.60 | no | 0.09 | 0.031 | 0.0008 | −0.0001 |

Rough reading (numerical, crude): (1) the coarse fundamental coupling falls monotonically with L at every β, and the three β fall
roughly on one curve in L√σ (1.40 vs 1.46: 0.83 vs 0.70; 2.80 vs 2.92: 0.17 vs 0.15): a one-variable flow is not contradicted;
σ_C(u)/u per doubling at fixed β is 0.21–0.54. (2) The adjoint couplings are below 0.01 in modulus from L√σ ≈ 1.4 on (stateless,
in this fit). (3) A crude centre projection, β_Z2 ≈ bF·⟨|½ tr U_p|⟩ with the Haar value 4/(3π) ≈ 0.42, against the 4D Z₂ critical
coupling 0.4407 puts the crossing at bF ≈ 1.04, i.e. L√σ ≈ 1.0–1.3 (ss or geometric mean of ss and ts). That is the same order as
1/T_c ≈ 1.41 and the act number's self-dual point (1.39–1.55). **Not a test**: content failed at 8 of 9 points (the couplings may
describe a lossy variable, not the theory); the projection ignores the adjoint-dependent weights and the anisotropy; one-loop-free
mean-field reading of a first-order Z₂ transition. A proper look needs the centre-projected coupling measured directly (e.g. the
Z₂ Schwinger–Dyson fit of sign(tr U_p) of the blocked field), which is a pre-registration of its own (not prepared here).

### 5.4 Relation to Tomboulis's vortex free-energy route, and where it stalled

Tomboulis–Yaffe (1985, read in Kanazawa per r3-monotone) is a **one-volume** inequality: vortex free energy exponentially small in
the cross-section ⇒ area law. Tomboulis (2007) tried to get that input for all β by Migdal–Kadanoff decimations made into
inequalities, carrying Z₋/Z to coarser lattices with interpolation parameters; the matching α(t*) = α⁺(t*) is a two-sided comparison
across scales and is the unproved (3.5) of Ito and Seiler, who also note that the MK recursion cannot tell abelian from non-abelian
(r3-monotone, read there). In the present terms:
* Tomboulis worked **in the existence layer only** (the vortex free energy) with **group-blind standings** (decimation bounds): the
  combination that section 4.3 shows cannot work (it would also hold for 2I and, in MK form, for U(1)).
* The owner's two-layer reading adds what his argument lacked: a **stateless information layer** as a separate hypothesis (L-A),
  which is group-specific (fails for 2I, for adjoint matter) and is measured to hold at L√σ = 2.80 (0.0036).
* Even with (L-A), Tomboulis's target (area law) is incomparable with the gap; and the cross-scale comparison of the effective Z₂
  couplings remains two-sided unless one of the two escapes of 4.3 is used: worst-case curvature at one scale (Dobrushin endpoint),
  or a **sign structure**: if the effective Z₂ couplings after integrating the SO(3) layer are ferromagnetic (positive), Griffiths and
  Simon–Lieb-type inequalities give one-sided bounds in the right direction. For fixed SO(3) links the Z₂ couplings in Tomboulis's
  representation are positive (positivity of the character expansion of the Wilson action; recalled, to check); after averaging over
  an SO(3) law that depends on the vortices, positivity can fail. Whether "stateless" (weak dependence of the SO(3) law on the vortices,
  0.0036) restores enough positivity for a Simon–Lieb argument is, as far as I can see, the cleanest new question this line has
  produced. SPECULATIVE; one reading session (Simon–Lieb for lattice gauge observables; plaquette random-cluster representations of
  Z₂ gauge theory; sharpness results for Z₂ lattice gauge theory) would decide whether the tools exist at all.

## 6. Unit tests of the line (D-S ∧ D-T)

| test | z₀ | z_e | D-S ∧ D-T | status |
|---|---|---|---|---|
| photon (free, lattice) | `2L·arsinh(sin(π/L))`, increasing to 2π (one photon; 4π at zero momentum) | g²/2 frozen | fails: bounded z₀ (`bounded_violates_doubling`); photon doubling ratio 1.136 (L = 4→8), 1.064, 1.037, → 1, i.e. η → ½ (`photon_exact.json`) | **Lean + exact formula** |
| Z₂ weak coupling | linear (gapped) | → 0 | no claim (flux clause fails) | paper; missed claim, not wrong |
| Z₂ strong coupling | linear | grows | holds | paper |
| deconfinement | — | — | the line places D-S above the crossing; boxes below 1/T_c are the swapped deconfined regime, where z_e is small and z₀ sublinear | paper |
| mixture / Heller endpoint | bounded at the endpoint (massless 0⁺⁺) while z_e grows | grows | fails (bounded z₀): the line uses z₀, not z_e, correctly | paper + Lean lemma |
| Banks–Zaks | frozen at the fixed point | frozen or absent | fails (bounded) | paper + Lean lemma |
| finite subgroup 2I, weak coupling | gapped? (frozen theory, large action gap) | frozen | D-S ∧ D-T may hold at fixed β (a frozen lattice theory is gapped in lattice units); the line is at fixed β not a continuum claim; in the continuum order (k → ∞ along a tuning) 2I has no line of constant physics | paper; a reminder that the lattice-unit theorem alone is not the continuum gap |
| pure noise | huge gap | — | holds trivially | caught by `NonTrivial`, not by the line (as v4) |

## 7. Pre-registration and the photon control

`PREREG-JOINT.md` (this folder): the joint measurement of z₀(L) and z_e(L) on periodic boxes, β = 2.3, 2.4, 2.5, L√σ = 1.03–4.20,
using `lattice/run_su2_gpu.py` unchanged (it already records the A1⁺⁺ glueball operators and the torelons on the same configurations);
z₀ also from the flux-pair operator (squared summed torelon), formed in the analysis. Readings J1–J6 (doubling verdict per pair,
threshold, branch switch = the sector transfer made literal, loss η, scaling, the D-S candidate). Stage 0: a pre-registered pilot
reading of the existing β = 2.3 runs on disk. Runtime about 2.5 GPU hours (±50 %), optional β = 2.5, L = 24 point 1.4 h. Not run.
Section "Photon control: proposal" there: replace the simulated U(1) photon gate of `r4-actnumber` by the exact free-photon theorem
(z_e = g²/2 at every L, r4-conjw) and use the exact z₀ formula for this measurement; optionally a sector-resolved U(1) control.
**This changes a pre-registration and needs the owner's decision.**

## 8. Next step

1. Owner: decide the photon control (A: exact formula; B: sector-resolved simulation; or keep). Then run `PREREG-JOINT.md` Stage 0
   (CPU, minutes) and the GPU plan (about 2.5 h).
2. One reading session on the two candidate mechanisms of 4.3/5.4: Dobrushin–Shlosman's constructive criterion and complete
   analyticity (does persistence under doubling come free, as recalled?), and Simon–Lieb / random-cluster tools for Z₂ lattice gauge
   theory with positive couplings (do they exist for gauge observables?). If the second exists, state "(L-A) ∧ positivity of the
   effective Z₂ couplings ∧ a one-box Simon–Lieb criterion ⇒ gap" as a Lean target.
3. Lean (small, optional): the time-first gap statement as a named target next to `MassGapMFLoc` (item U3 (i)), and D-Th as a named
   bridge, so that the line's top theorem can be written against the tuning.

## 9. Not checked

No Lean statement about the continuum; Perron–Frobenius positivity of finite-box gaps is used on paper only. The small-box torelon-pair
contamination of A1⁺⁺, Luescher's small-volume expansion, Dobrushin–Shlosman, Martinelli's recursion, Knabe, Simon–Lieb and the
sharpness results are recalled, not re-read. Tomboulis and Ito–Seiler are taken from r3-monotone's reading. The refit table is read
from the summary file; I did not re-run or re-check the fits. No GPU, no simulation; the only computations are `photon_exact.py`
(closed formulas) and `runtime_estimate.py` (arithmetic).

## Files

`NOTE.md` (this), `PREREG-JOINT.md`, `photon_exact.py` + `photon_exact.json`, `runtime_estimate.py` + `runtime_estimate.log`,
`build.sh`, `axioms.sh` + `axioms.log`, `lookup.sh` (Mathlib name lookup). Lean: `../../../formal/ProofPhase/DMP/Doubling.lean`,
`../../../formal/ProofPhase/DMP/VacuumAct.lean`.
