# What M1 rests on outside itself (m1-tools, 2026-11-22)

Every place where M1 uses a result it does not prove: Balaban's papers, the running-coupling input, and the papers
Balaban himself relies on. Each row gives the statement relied on (by equation number, paraphrased, no quotations), where
M1 uses it, and how. Definitions taken from Balaban (the block average [I] (0.3)-(0.4), the inductive form [III] (2.18))
are listed only where M1 relies on a property proved there.

**Numbering key.** `[I]`-`[V]`: Balaban, CMP 109 (1987), 116 (1988), 119 (1988), 122 p. 175 (1989), 122 p. 355 (1989).
`[12]`: averaging operations, CMP 98 (1985). `[13]`: propagators in a background field, CMP 99 (1985) 389-434 (= `[5]` in
`[15]`'s own list). `[14]`: regular configurations and gauge fixing, CMP 99 (1985) 75-102 (= `[6]` in `[15]`'s list).
`[15]`: the variational problem, CMP 102 (1985). `[16]`: as cited in [V] (1.76).

| # | source | statement relied on | used in M1 by | how |
|---|---|---|---|---|
| 1 | [I] Theorem 2 | the effective couplings `g_k` of Balaban's renormalisation-group flow ([I] (0.20), [III] (2.24)) stay below a small `γ` for all scales up to the stopping scale `K`, for small bare coupling; M1 needs in addition `γ ≤ γ0(L)` (`S1-PROOF.md` 5) | `runningCoupling`; every smallness condition | **external**; its proof is unpublished |
| 2 | [I] (1.18), Sects. 1-7 | the small-field effective action: localised analytic E-terms on the domains (2.28), with the bound (1.18), renormalised (vacuum energy, coupling constant) | `Form` (F-e); P2′ input I3; carry-overs E5, E6 | cited as stated |
| 3 | [I] (7.13) | the exponentiated cluster expansion converges for activities with the bound [V] (1.97) | E12 | cited |
| 4 | [II] (2.41); [II] Sect. 2 | cluster-expansion bounds of the fluctuation integral; boundedness and exponential decay of the fluctuation propagators | P2′ inputs I2, I3 | cited as stated (perturbation by the hole: `V1-INPUTS.md`, P2′ Lemma E) |
| 5 | [III] Sect. 2, (2.17)-(2.42); Sect. 3 | the inductive assumptions: characteristic functions (2.17), factorisation of `T` (2.19)-(2.22), E-, R-, B-terms with (2.25)-(2.33), (2.40)-(2.42), the spaces (2.34)-(2.39); Sect. 3: the next `T` | `Form` (definition and bounds); E13 | used as Balaban's induction hypothesis, extended by records (`S1-ROWS.md` 1) |
| 6 | [IV] (1.10)-(1.99) | the preliminary integrations are identities and produce the R-operation input (1.99)-(1.100) | P1 | cited (read in full, `NOTE.md` 1.1) |
| 7 | [IV] (1.74)-(1.75) | restriction `χ_{k,Λ}` and extension of a regular outside field into `Λ` | P2 | cited |
| 8 | [IV] Prop 1, (1.77)-(1.98) | unconstrained minimal orbit with regularity (1.78); background bound (1.80); AL gauge (1.83)-(1.87); `χ''_k = 1` via H-function bounds (1.89)-(1.98) with the delay `N` | V2 | carried over step by step (`ROUTINE-ROWS.md` 3); the H-function decay it uses is `[15]` (190) |
| 9 | [V] (1.12)-(1.69) | expansion of the action around the background; localisation of the E-, R-, B-terms ([I] Sects. 3-6) | E1-E4 | carried over (`S6-START.md`, `E3.md`, `ROUTINE-ROWS.md` 6) |
| 10 | [V] (1.70)-(1.89), p. 380 | normalised operations; analytic extension (1.73)-(1.75); large-field factors (1.76)-(1.79), pointwise from characteristic functions with `[15]` Theorem 1 and [16] (71); entropy induction (1.80)-(1.88); fundamental inequality (1.89); normalisation constants | E5-E9, P4 | carried over (`E5-E9.md`, `ROUTINE-ROWS.md` 5) |
| 11 | [V] (1.90)-(1.104) | Mayer expansion, activity bounds from (1.68), (1.73), (1.89); exponentiation; new R- and B-terms (1.99)-(1.100); form (2.18) at the next scale | E11-E13 | cited, checked (`ROUTINE-ROWS.md` 7) |
| 12 | `[15]` Theorem 1, Props 2-9 | for nested determining sets with regular data: a unique minimal orbit of the Wilson action with fixed averages, regularity (2), analyticity in the data (7), derivative decay (190) | V1 | proof checked section by section with excision (`V1-EXCISION.md`); the modified linear inputs proved (`V1-INPUTS.md`) |
| 13 | `[15]` (9)-(10) | regularity of the fine realisation of a block-field fluctuation | P2′ input I1 | cited as stated (unmodified problem) |
| 14 | `[15]` Theorem 1, lower bound | the action dominates the block field's plaquette deviations | P4 | cited |
| 15 | `[13]` Theorem 3.12 | `|HB| ≤ B0 L^j |B|`, `|∇HB| ≤ B0 L^{j/2}|B|` for the constrained minimiser operator `H` (as `[15]` (46) quotes it) | V1 input (ii) | cited unmodified; `[13]` not at hand; modification proved (Lemma FR) |
| 16 | `[13]` Theorem 3.13; (3.119)-(3.120) | the norm bound of `𝔊` from `|·|_(-3)` to `max{|·|_(-1), |∇·|_(-2)}` (as `[15]` (117) quotes it); the decomposition of the quadratic form | V1 input (ii); Lemma LP | cited unmodified; modification proved (Lemmas FR, LP) |
| 17 | `[14]` Theorem 2 | unique gauge transformation from axial to Landau gauge with the bounds (1.36)-(1.39); its proof's linear bounds: `G'` bounded `|·|_(-2) → |·|`, `|D·|_(-1)` and `R` bounded (from `[14]`'s ref. [4], Theorems 3.1-3.2), `H'` (1.92) | V1 input (i); V2 | cited unmodified; compression proved (Lemma FR(b)); `[14]` Sect. E not re-read line by line |
| 18 | `[14]` (1.65) | regularity of block averages of a regular field in axial gauge | V2 ((1.84)) | cited |
| 19 | `[12]` Proposition 4 | the averaging map's expansion `Q_j(ηA) = L^jη Q_j A + C_j`, `|C_j| ≤ C_2 (L^jη)²|A|²` (as `[15]` (44) quotes it) | V1 (Sect. C of `[15]`) | cited |
| 20 | [16] (71) | the bound used in [V] (1.76) for the large-field factors from `χ^c_j` | E7 (through [V] (1.76)) | cited through [V] |

**Not external.** Exactness, the twisted and excised blockings, dilution, the fibre mass, the Poincaré bound, the
local-modification lemmas, the record bookkeeping: proved here (Lean or paper). The numerical checks (`NOTE.md`,
`NT-B.md`) support claims that are also proved or are off the critical path.

**Summary.** One external input (row 1) is unpublished. Everything else is published work by Balaban, used as he
states it (rows 2-11, 13-20) or with its proof re-checked for M1's modifications (row 12, with rows 15-17 as inputs).
Two papers are used only through Balaban's own quotations: `[13]` (rows 15-16, not at hand) and [16] (row 20).
