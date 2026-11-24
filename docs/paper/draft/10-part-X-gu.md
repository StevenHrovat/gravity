# Part X. GU: the Grand Unified reading

*Draft 2, 2026-11-24. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/ProofPhase/`; notes relative to
`docs/unified/`. Claim labels (X.n; IX.n in draft 3) are listed in `../CLAIMS.md` (merged from `../claims-incoming/IX-gu.md`).*

## X.0 What "Grand Unified" means here, and where it stands

**GU is not a Clay problem.** There is no official statement to quote. In this work "Grand Unified" is the second half of the
owner's **release criterion** (`OUTLINE.md`): the paper may leave the draft stage when both readings of GUID hold. **General** is the
unified theorem with its open hypotheses closed. **Grand Unified** is *the framework containing SU(3) x SU(2) x U(1) in one structure
with at least one checkable consequence*. The owner's wording is a goal ("what I want to claim when finished, not what I can prove
now"), so this part states exactly how far each half of the Grand Unified reading holds today.

**State (2026-11-24).**

* **"In one structure": met, in a modest and classical sense.** The group SU(3) x SU(2) x U(1) divided by a cyclic group of order 6
  sits inside SU(5), and the kernel of that embedding is proved in Lean **[Lean]**, with the group-level facts about it **[classical]**
  (X.3).
* **"At least one checkable consequence": the owner's decision, uniform charge quantisation.** The notes find two candidates and
  prove what can be proved about each (X.5). The owner takes candidate (b), with its guarantee from the ODP: every charge is an
  integer multiple of one unit, the same unit for all matter, and the unit is the ODP's dimensionless 1 (X.5) **[reading]** for the
  guarantee, **[Lean]** for the integer charges on a compact circle, **[external]** for the measurements. Neither candidate is a
  consequence that the standard expectation of any compact U(1) or any SU(5) does not already contain; a consequence beyond it stays
  **[open]** (X.5e).

**What this part does not do.** It does not derive the Standard Model's hypercharges, does not predict a new particle or number, and
contains no new physics. The hypercharges are an **input**.

## X.1 The problem as meant in this work

**X.1.1 Grand unification in physics** **[classical]**. The Standard Model gauge group SU(3) x SU(2) x U(1) is embedded in one simple
group (SU(5): Georgi and Glashow 1974; SO(10): Georgi 1975, Fritzsch and Minkowski 1975), with one coupling at the unification scale,
from which the three couplings run apart toward low energies. Checkable consequences in such theories are coupling relations, charge
quantisation, proton decay and magnetic monopoles. Care points the paper keeps: the single coupling holds at one scale only; minimal
non-supersymmetric SU(5) is excluded by proton-decay limits and the three couplings do not meet at one point **[external]**
(X.4); and not every SU(N) is a viable grand unified group, since a GUT must contain SU(3) x SU(2) x U(1), cancel the gauge anomalies
with the observed matter and survive the proton-decay limits, which singles out SU(5) and its extensions, SO(10) and E6.

**X.1.2 The quotient.** The Standard Model fields are all invariant under a cyclic group of order 6 sitting in the centre of
SU(3) x SU(2) x U(1). The gauge group can therefore be taken as the quotient by any subgroup Gamma of Z_6, that is by Z_1, Z_2, Z_3 or
Z_6. All four have the same local physics and the same Feynman rules, and present experiments do not decide between them (Tong 2017)
**[classical]**. The maximal choice Z_6 is what puts electric charge in thirds, correlated with colour. It is what any SU(5) or SO(10)
unification forces, since the SU(5) embedding has exactly this Z_6 as its kernel.

## X.2 The card

The DMP API (`docs/unified/API.md`) gives every problem a well-defined input, a proved structure on it, and one named open step. GU
has that shape, but it is **not a `Problem` card in the Lean API**: its Lean pieces are group-level statements in `General/`, plus the
API's one general statement about the G0 phase field (X.3.3). The table is the card in prose.

| Card element | GU |
|---|---|
| **Well-defined input** | the representation content of one generation and the Higgs: for each field its triality `t`, duality `d` and hypercharge in sixths `q = 6Y` (`smFields`, a definition in Lean). **The hypercharges are input, not output.** |
| **Proved structure** | the centre elements of SU(3) x SU(2) x U(1) that act trivially on all these fields form exactly a cyclic group of order 6, split as 2 x 3; every invariant component has `Q + t/3` an integer (charge in thirds, correlated with colour); the SU(5) block embedding has exactly this group as kernel; a compact U(1) admits only integer charges **[Lean]** |
| **External inputs** | the hypercharge values (fixed by anomaly cancellation, now in Lean, X.7b, or by SU(5)); the measured neutrality of matter, the absence of free fractional charges, proton-decay limits, the failure of coupling unification, the absence of monopoles **[classical]** / **[external]** |
| **The one open step** | a checkable consequence beyond the standard expectation, supplied by DMP **[open]**; for the gate's wording the owner takes uniform charge quantisation (X.5) **[reading]** |
| **Conclusion** (if the step closes) | the Grand Unified half of the release criterion holds |

## X.3 What is proved

All of this is **[Lean]**, standard axioms only (`docs/unified/gu-axioms.log`: 19 declarations on the three standard axioms, one on
`propext` alone, two definitions on none; `docs/unified/gucharge-axioms.log`: all 12 declarations on the three standard axioms; no
`sorry`, `admit`, `native_decide` or `axiom` in either module). The statements are about groups and their characters, that is, about the
possible charges of fields. **Not formalised:** a gauge field theory with this U(1); that the image of the SU(5) map is all of
S(U(3) x U(2)); any lattice or twist-sector statement for the product group; chiral matter.

### X.3.1 The Z_6 (`General/GUCentre.lean`, namespace `ProofPhase.General.GU`)

One generation, with `q = 6Y` and `2t + 3d + q` the exponent of the generator's phase:

| field | rep (SU(3), SU(2)) | Y | q | t | d | `2t + 3d + q` |
|---|---|---|---|---|---|---|
| Q_L | (3, 2) | 1/6 | 1 | 1 | 1 | 6 |
| u_R | (3, 1) | 2/3 | 4 | 1 | 0 | 6 |
| d_R | (3, 1) | -1/3 | -2 | 1 | 0 | 0 |
| L_L | (1, 2) | -1/2 | -3 | 0 | 1 | 0 |
| e_R | (1, 1) | -1 | -6 | 0 | 0 | -6 |
| H | (1, 2) | 1/2 | 3 | 0 | 1 | 6 |

A centre element `(u 1_3, v 1_2, z)` acts on a field by `u^t v^d z^q` (`centrePhase`). Then:

* it acts trivially on all fields exactly when `z^6 = 1`, `u = z^2`, `v = z^3` (`sm_kernel`); equivalently the kernel is generated by
  `(zeta^2, zeta^3, zeta)` with `zeta = e^{2 pi i/6}`, a primitive sixth root (`sm_kernel_cyclic`, `zeta6_prim`); the generator has
  order 6 (`gen_order`) and splits into a primitive cube root and `-1` (`gen_parts`);
* **the CRT split**: the order-2 part `(1, -1, -1)` and the order-3 part `(zeta^4, 1, zeta^2)` each act trivially
  (`sm_kernel_two`, `sm_kernel_three`); at the level of `Z/6` the split is `centre6 : ZMod 6 = ZMod 2 x ZMod 3`
  (`General/SUNTwistPrimes.lean`);
* the generator is trivial on a field exactly when 6 divides `2t + 3d + q`, and this holds for every field in the table
  (`gen_trivial_iff`, `gen_trivial_sm`);
* **charge in thirds**: if 6 divides `2t + 3d + q`, every component with `2 T_3 = s` has charge `Q = (3s + q)/6` and `Q + t/3` is an
  integer (`charge_thirds`, `charge_thirds_sm`). So electric charge modulo 1 is fixed by colour: integer for colour singlets, in
  `-1/3 + Z` for quarks;
* **the falsifiable side**: a colour singlet with a component of non-integer charge is not invariant under the generator
  (`fractional_singlet_breaks`), so it cannot exist if the gauge group is the full quotient by Z_6;
* **SU(5)**: the block map `(A, B, z) -> diag(z^{-2} A, z^3 B)` has determinant 1 and its kernel is exactly
  `{(z^2 1, z^3 1, z) : z^6 = 1}` (`su5Embed`, `su5_embed_det`, `su5_embed_kernel`). So any SU(5) unification forces Gamma = Z_6.

The centres of the factors are also in Lean: for `omega^N = 1` the scalar matrix `omega I` lies in SU(N) and is central; the map
`zeta -> zeta I` is an injective homomorphism from the N-th roots of unity, a copy of Z_N with N elements (`General/Centre.lean`:
`centreHom`, `centreHom_injective`, `centreHom_central`, `card_centre`, `centreHom_rep`). Every SU(N) centre therefore sits as phases
on one common circle.

### X.3.2 Charge quantisation from a compact U(1) (`General/GUCharge.lean`)

If the U(1) of hypercharge is a circle, not a line, it admits only integer charges. In Lean, from Fourier analysis and Parseval's
identity on the circle (Mathlib has neither this classification nor the character shift, so the steps are proved here):

* `fourierCoeff_char_shift`: the Fourier coefficients of a character shift by its value (translation invariance of Haar measure);
* `addCircle_char`: every continuous character `chi` of `AddCircle T` is `x -> toCircle(n x)` for an integer `n`; `addCircle_char_unique`:
  the integer is unique;
* **`circle_char`: every continuous homomorphism from the circle to the circle is `z -> z^n`, with `n` a unique integer**
  (`circle_char_unique`);
* **on a line, every real `a` gives a character `t -> e^{iat}`** (`line_char`), and it factors through the circle exactly when `a` is
  an integer (`line_char_periodic_iff`). So quantisation comes from compactness and from nothing else;
* an N-th root of unity on the circle (an SU(N) centre element) sees `z^n` as `omega^(n mod N)` (`centre_char_mod`).

**The chain** (`g0_charge_thirds`). Input, stated explicitly: a field on which hypercharge acts by a continuous character `chi` of the
circle, with triality `t` and duality `d`, invariant under the generator `(omega, -1, zeta)`. Then `chi = z -> z^q` with `q` an integer
**(derived, from compactness)**, 6 divides `2t + 3d + q`, and `Q + t/3` is an integer for every component. The split into thirds uses
the matter input; the integer `q` does not.

### X.3.3 The G0 link as an API statement (`API.lean`, `API/Phase.lean`)

G0's phase field is one compact U(1), Mathlib's `Circle` (`Phase`). A label carried on it is a continuous character (`PhaseLabel`).
`ChargeQuantisation` names the statement; it is proved with no hypothesis (`chargeQuantisation`), and
`PhaseLabel.integer_charge` says every label on the phase field has an integer charge **[Lean]**. This is the one consequence of the
G0 link that holds for **every** instance of the API, not only for GU. `g0_charge_thirds` is the GU instance of it.

## X.4 What is borrowed

**X.4.1 The hypercharges** **[classical]**. Given the Standard Model representations of one generation, cancellation of the gauge
anomalies and the mixed gauge-gravitational anomaly fixes the hypercharge ratios (Geng and Marshak 1989; Minahan, Ramond and Warner
1990); with a right-handed neutrino a B - L direction opens unless a Majorana mass is assumed (Babu and Mohapatra 1989).
Alternatively the ratios follow from SU(5). Either way they are an **input to the Z_6, not an output of it**. Anomaly cancellation is
now in Lean (X.7b, `ProofPhase/Closures/Anomaly.lean`: `anomaly_fixes_sm`, `anomaly_fixes_Z6`): for one generation the
four anomaly conditions fix the charges up to u <-> d, and with them the Z_6. This is classical physics formalised, not a DMP result.

**X.4.2 The global form** **[classical]**. Which of Z_1, Z_2, Z_3, Z_6 nature uses is not decided by present experiment (Tong,
JHEP 07 (2017) 104). The choice changes which new particles and line operators are allowed:

| Gamma | trivial on a field iff | colour singlet with Q = 1/3 | colour singlet with Q = 1/2 |
|---|---|---|---|
| Z_1 | always | allowed | allowed |
| Z_2 | `q = d` mod 2 | allowed | forbidden |
| Z_3 | `2t + q = 0` mod 3 | forbidden | allowed |
| Z_6 | `2t + 3d + q = 0` mod 6 | forbidden | forbidden |

It also changes the smallest magnetic charge of a monopole and the periodicities of theta angles (Tong 2017), and for Z_6 the
fractional part of the axion-photon coupling is tied to the axion-gluon coupling (Reece 2023; Choi, Forslund, Lam and Shao 2023).
All **[classical]**.

**X.4.3 Experiments** **[external]** (cited as the project notes cite them; not re-read for this draft).

| Check | Result |
|---|---|
| neutrality of matter (one charge unit) | electron-proton charge difference below about 1 part in 10^21 (Bressi et al. 2011) |
| free fractional charges | none found (review: Perl, Lee and Loomba 2009) |
| proton decay | not seen; Super-Kamiokande bound above 10^34 years for p -> e+ pi0; minimal non-supersymmetric SU(5) is excluded |
| coupling unification | the three couplings do not meet at one point; with supersymmetric running they nearly do |
| magnetic monopoles | none found (MACRO, IceCube flux limits; MoEDAL production limits) |

## X.5 The one open step: the gate's "at least one checkable consequence"

**The gate, as worded:** the framework contains SU(3) x SU(2) x U(1) in one structure **with at least one checkable consequence**.
**[open]**

The notes find two candidate consequences. The table states, for each, what is derived, what is input and what the standard
expectation already says. It makes no recommendation.

| | Candidate (a): the selection of Z_6 | Candidate (b): charge quantisation from the G0 link |
|---|---|---|
| **The statement** | the U(1) of G0 is glued to the SU(2) and SU(3) centres as fully as the matter allows, which selects the maximal quotient Z_6 out of the four | every charge on the G0 circle is an integer multiple of one unit, with the unit splitting into thirds for quarks |
| **Checkable by** | a colour singlet with fractional charge (forbidden for Z_6), a monopole's smallest charge, the fractional part of axion couplings | neutrality of matter; the absence of free fractional charges; Dirac quantisation of any monopole |
| **What is derived** | the arithmetic of Z_6 and its consequences, given the hypercharges **[Lean]**; the selection itself is a **[reading]** | the integer charge, from compactness alone **[Lean]**; the thirds, from the input **[Lean]** |
| **What is input** | the hypercharges; that the gluing is "as full as the matter allows" | that the hypercharge U(1) is compact (in DMP the reading "G0's U(1) possibility field", with the centres on one circle in Lean); the hypercharges |
| **Status of the evidence** | no present measurement decides Z_6 against Z_1, Z_2, Z_3 | measured: matter neutral to about 1 part in 10^21 **[external]** |
| **What the standard picture already says** | Z_6 is forced by any SU(5) or SO(10) unification and is the textbook expectation | charge quantisation is the standard expectation of any compact U(1) and of any theory whose U(1) sits in a compact simple group |
| **What would make it DMP-native** | a DMP theorem, stated before the hypercharges, that selects the quotient; **none exists** | it already follows from the link to G0, with the circle as the project's own object |

**Why the project's present pieces cannot see candidate (a).** All twist-sector results (the `SUNTwist` family) are for pure gauge
theory with one group. In pure gauge theory the whole centre is a symmetry; Z_6 is singled out only once matter is added. The
selection lives where the project has nothing yet: matter, and in particular chiral fermions.

**Why 2-then-3 does not give Z_6 as a consequence** **[classical]** + **[Lean]**. That the centre of SU(2) x SU(3) is Z_2 x Z_3 = Z_6
follows once the factors are chosen; the reading "2 first, then 3" restates the choice. Which part of Z_6 is divided out is decided by
the matter, and present experiments do not decide it. Z_6 = Z_2 x Z_3 is symmetric: it has no "first 2, then 3". An order appears only
in the symmetry breaking (X.6).

**The owner's position, recorded.** The owner's reading is that GU comes down to well-defined inputs, which DMP can guarantee, and that
the checkable consequence comes from the link to G0 (candidate (b)).

**The owner's decision (2026-11-24).** "Uniformity is also guaranteed to be constructed by the ODP": the guarantee of "well-defined
inputs, guaranteed" is the same as the one that gives Yang-Mills its lower edge (Part III 4.4). The ODP ends only at a dimensionless 1,
and that 1 is the unit every charge is an integer multiple of. So the checkable consequence for the gate is uniform charge
quantisation, one unit for all matter, checked by the neutrality of matter and the absence of free fractional charges **[reading]**
for the guarantee (X.5f), **[Lean]** for the integer charges on the compact circle (X.3.2), **[external]** for the measurements
(X.4.3a, X.4.3b). Care point: it coincides with the standard expectation of any compact U(1); the paper claims no consequence beyond
it (X.5e stays open).

## X.6 DMP readings attached to this part (all [reading])

* **"G0's U(1) possibility field" selects the maximal quotient.** If every centre phase is a point on the one shared circle, the
  natural gluing identifies the SU(2) and SU(3) centres with hypercharge phases as fully as the matter allows: Gamma = Z_6. This is the
  sharpest DMP-flavoured statement found. It is checkable (X.5) but is not a derivation: "as fully as the matter allows" uses the
  hypercharges, and the conclusion coincides with what SU(5) gives.
* **"The universal quantum running" read as charge quantisation.** The owner's entry, in the coordinator's reading: the link to G0
  makes the phase group a circle, and a circle carries only integer charges. The step from the circle to integer charges is proved
  (X.3.2); that this is what the entry means is the reading.
* **"2 first, then 3, with the hand-over at the state 2, 3."** An order does appear in the symmetry breaking **[classical]**: at the
  electroweak scale the Higgs vacuum (read as the SU(2) "handshake") leaves the unbroken group (SU(3) x U(1)_em)/Z_3. The Z_2 part is
  absorbed, and the Z_3 part survives to low energies as the correlation of charge with colour. In descending energy the 2-part acts
  first and the 3-part remains. This matches the owner's ordering and predicts nothing beyond the standard picture.
* **"SU(5) with a single coupling is G0 at GRH, with a forward arrow independent of scale."** SU(5) is the smallest simple group that
  contains the Z_6 quotient (X.3.1). Its single coupling holds at one scale only, minimal SU(5) is excluded by proton decay, and the
  couplings do not meet exactly (X.4.3). The owner's mapping (one coupling = one G0; the forward arrow = the running from the
  unification scale) is a reading, and a programme beyond Yang-Mills, GRH and NP vs coNP.
* **Every SU(N) as a valid unified theory, indexed by the values of zeta.** On `s > 1` the zeta function decreases continuously from
  infinity to 1, so it takes every integer `N >= 2` exactly once, which follows from continuity and monotonicity **[classical]**. So
  zeta indexes every SU(N), one to one. The project's gauge-group package covers every SU(N) (`General/SUN*.lean`). That every SU(N)
  "describes existence" is the owner's reading; as physical unified theories most SU(N) are not viable (X.1.1).
* **SU(2) as the stable profile** (Appendix A): a statement about the group manifold under Ricci flow, not about the global form of the
  Standard Model group. No link to Z_6 was found.
* **The rigid groups.** Which compact groups are rigid, which carry content across the gate, and the U(1) gate's two hidden witnesses are in Appendix A.5.

## X.7 What would close it

Ranked by how directly each would answer the gate. None is promised.

1. **Derive the selection, not the arithmetic.** A DMP principle, stated before the hypercharges and proved as a theorem about running
   existence spaces, whose consequence is "the centre twists that survive matter are glued to the U(1) maximally". With the
   representation content as input it would output Gamma = Z_6 and hence the three checks of X.4.2. This is the only route found on
   which DMP would contribute a consequence rather than a description.
2. **Anomaly cancellation in Lean** (done, X.7b): from the one-generation representation content the anomaly equations fix the
   hypercharge ratios, hence Z_6 (`Closures/Anomaly.lean`, `anomaly_fixes_sm`, `anomaly_fixes_Z6`). It makes the input a classical
   theorem, not a DMP one, and leaves the card's open step (a checkable consequence) where it was.
3. **Twist sectors of the product group with Z_6-invariant matter**: extend the `SUNTwist` chain to a lattice SU(3) x SU(2) x U(1)
   theory with vector-like matter, so that the Z_6 twist sectors are strictly between nothing and everything, in the project's own
   language. Chiral matter, which the Standard Model needs, is a known hard problem on the lattice and stays out of reach.
4. **The single coupling**: a statement about running couplings needs the continuum theory with matter, beyond Yang-Mills as treated
   here.

Until one of these lands, the paper can say exactly this: the framework contains SU(3) x SU(2) x U(1) / Z_6 as one structure
(classical, Lean-stated); the owner's readings select Z_6, which a fractional-charge discovery, a monopole's charge or an axion's
couplings could refute; charge quantisation from the circle is proved and measured but is also the standard expectation; and no
consequence is derived from DMP beyond what the standard expectation contains. Which of these, if any, counts for the gate is the
owner's decision.

## X.8 The box in the one-box test

**Gate factor and marker.** The ticks are the **points** (the owner's name; he also offers "uniquenesses" and "DoEs"): the labels
carried on G0's phase field. The name is exact: the continuous characters of the circle are the integers, the points of its dual
group **[classical]** (Pontryagin duality). At each point the gate reads inside when the label has an
integer charge; the marker is the claim "inside". This box passes, proved: every continuous character of the circle is z to the n
**[Lean]** (`gu_box`, `ETM/CardBox.lean`; claim X.8a). The GU card's open step, a consequence beyond the standard expectation (X.5e), is not a
statement about this box; the box shows what the G0 link already gives every label, and what stays open lies beyond it **[paper]**.
