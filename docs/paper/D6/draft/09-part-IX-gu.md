# Part IX. GU: the Grand Unified reading

*Draft 6. Prose, with every result marked. Lean paths relative to `docs/mass-gap/formal/ProofPhase/`; notes relative to
`docs/unified/`. Claim labels (IX.n) are listed in `../CLAIMS.md`.*

**Plug in here.** Gives: the Grand Unified reading, its box (charge quantisation, proved) and where its open step lies. Needs:
II.4 and II.5. Route: off both routes; the reading route can visit it after R.11. VIBE coefficient: the centre of the Standard Model
group splits as Z/6 = Z/2 x Z/3 (IX.3.1c) **[Lean]**, the same two primes that up to a = 0.69 are the only primes in Weil's form
(IV.1); the primes match exactly, and reading the match as the throughline is the first author's **[reading]**.

**Contracted.** Sections and labels this part names but does not print are in the full Draft 6, the git tag `d6-full`, and in Draft 5 section by section; every label is a row of `../CLAIMS.md` with its status and evidence.

**As a statement checked step by step (II.4.1).** GU has a box and no card (II.5). Its box checks charge quantisation at every
step and passes, proved: every continuous character of the circle is z to the n (`gu_box`, IX.8) **[Lean]**. The open step of GU
lies outside this box (IX.5e), so no induction inside it reaches it.

## IX.0 What "Grand Unified" means here, and where it stands

**GU is not a Clay problem.** There is no official statement to quote. In this work "Grand Unified" is the second half of the
first author's **release criterion**: the paper may leave the draft stage when both readings of GUID hold. **General** is the
unified theorem with its open hypotheses closed. **Grand Unified** is *the framework containing SU(3) x SU(2) x U(1) in one structure
with at least one checkable consequence*. The first author's wording is a goal ("what I want to claim when finished, not what I can prove
now"), so this part states exactly how far each half of the Grand Unified reading holds today.

**State (2026-11-24).**

* **"In one structure": met by classical group theory, not derived from the framework.** The group SU(3) x SU(2) x U(1) divided by a
  cyclic group of order 6 sits inside SU(5), and the kernel of that embedding is proved in Lean **[Lean]**, with the group-level
  facts about it **[classical]** (IX.3). Nothing in that Lean involves DMP or GUID: SU(5) contains the group whatever the framework
  is, and the only link to the framework is the circle reading (IX.6) **[reading]**.
* **"At least one checkable consequence": the first author's decision, uniform charge quantisation.** The notes find two candidates and
  prove what can be proved about each (IX.5). The first author takes candidate (b), with its guarantee from the ODP: every charge is an
  integer multiple of one unit, the same unit for all matter, and the unit is the ODP's dimensionless 1 (IX.5) **[reading]** for the
  guarantee, **[Lean]** for the integer charges on a compact circle, **[external]** for the measurements. Neither candidate is a
  consequence that the standard expectation of any compact U(1) or any SU(5) does not already contain; a consequence beyond it stays
  **[open]** (IX.5e).

**What this part does not do.** It does not derive the Standard Model's hypercharges, does not predict a new particle or number, and
contains no new physics. The hypercharges are an **input**.

## IX.2 The card in prose

The DMP API (`docs/unified/API.md`) gives every problem a well-defined input, a proved structure on it, and one named open step. GU
has that shape, but it is **not a `Problem` card in the Lean API**: its Lean pieces are group-level statements in `General/`, plus the
API's one general statement about the G0 phase field (IX.3.3). The table is the card in prose.

| Card element | GU |
|---|---|
| **Well-defined input** | the representation content of one generation and the Higgs: for each field its triality `t`, duality `d` and hypercharge in sixths `q = 6Y` (`smFields`, a definition in Lean). **The hypercharges are input, not output.** |
| **Proved structure** | the centre elements of SU(3) x SU(2) x U(1) that act trivially on all these fields form exactly a cyclic group of order 6, split as 2 x 3; every invariant component has `Q + t/3` an integer (charge in thirds, correlated with colour); the SU(5) block embedding has exactly this group as kernel; a compact U(1) admits only integer charges **[Lean]** |
| **External inputs** | the hypercharge values (fixed by anomaly cancellation, in Lean, IX.7b, or by SU(5)); the measured neutrality of matter, the absence of free fractional charges, proton-decay limits, the failure of coupling unification, the absence of monopoles **[classical]** / **[external]** |
| **The one open step** | a checkable consequence beyond the standard expectation, supplied by DMP **[open]**; for the gate's wording the first author takes uniform charge quantisation (IX.5) **[reading]** |
| **Conclusion** (if the step closes) | the Grand Unified half of the release criterion holds |

## IX.5 The one open step: the gate's "at least one checkable consequence"

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
in the symmetry breaking (IX.6).

**The first author's position, recorded.** The first author's reading is that GU comes down to well-defined inputs, which DMP can guarantee, and that
the checkable consequence comes from the link to G0 (candidate (b)).

**The first author's decision.** "Uniformity is also guaranteed to be constructed by the ODP": the guarantee of "well-defined
inputs, guaranteed" is the same as the one that gives Yang-Mills its lower edge (Part X 4.4). The ODP ends only at a dimensionless 1,
and that 1 is the unit every charge is an integer multiple of. So the checkable consequence for the gate is uniform charge
quantisation, one unit for all matter, checked by the neutrality of matter and the absence of free fractional charges **[reading]**
for the guarantee (IX.5f), **[Lean]** for the integer charges on the compact circle (IX.3.2), **[external]** for the measurements
(IX.4.3a, IX.4.3b). Care point: it coincides with the standard expectation of any compact U(1); the paper claims no consequence beyond
it (IX.5e stays open).
