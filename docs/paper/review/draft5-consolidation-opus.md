# Review of the Draft 5 consolidation (Opus, medium effort)

Reviewer: an Opus subagent at medium effort, run from the coordinating session on 2026-11-25, on gravity `d5-improve` at `ceab792` and
IM `decode` at `20d2bba`, in fresh clones. Scope: the complex-number ruleset (II.0.1), encoding and decoding with smelly states (II.2.8,
IM `Arsenal/Decode.lean`), the headline's figure and the trust-check row (II.4.1), the readings index (R.0). Its runs of `paper D5` and
`paper` passed; Draft 4 untouched; no control characters; the ledger recounted (700 rows). The coordinator checked C-6 (134 rows carry
a reading mark, 112 lead with it) and C-20 (the duplicated phrase, introduced by the coordinator's own earlier rewrite and already on
main).

Verdict: no blocker; 7 major, 13 minor; the Decode Lean is correct.

| id | sev | problem | disposition |
|---|---|---|---|
| C-1 | major | C8: a unit multiplication only for the line; unitaries in more dimensions | Fixed |
| C-2 | major | "cost" used for the size in II.0g and the C2 pointer | Fixed: the size is the gate factor, the cost minus its log; the pointers corrected |
| C-3 | major | "all the mathematics" | Fixed: "the complex-number steps", the other tools named |
| C-4 | major | `hash_smelly` overclaimed; T.6's runs show preimage resistance, a different property | Fixed in II.2.8 and T.6 |
| C-5 | major | section numbers and claim labels mixed in the ledger and R.0 | Fixed: claim labels in the ledger row and the R.0 table |
| C-6 | major | II.0i missing from the index; 134 against 112 unexplained | Fixed |
| C-7 | major | the caption placed the verify toy among the open parts | Fixed: G2 open (R136a1), the toy all proved |
| C-8 | minor | the dashed maps ended on one step | Fixed: they end on a brace under the whole run, "the one box" |
| C-9 | minor | the trust check is not an induction | Fixed: "a check item by item, with no induction", the canary tests the tools |
| C-10 | minor | decoding by lookup not named | Fixed |
| C-11 | minor | `turn_decodes` is not "completing the turn" | Fixed: `vx_rot_complete` and `turn_decodes` named separately |
| C-12 | minor | `rot_add` is an instance | Fixed |
| C-13 | minor | zeta undefined; 1/N missing | Fixed: the words defined once; C4, C6 with 1/N |
| C-14 | minor | C5 needs holomorphy | Fixed |
| C-15 | minor | sign of the real part; multiples of 2 pi i; converges; z nonzero | Fixed |
| C-16 | minor | w undefined in C1 | Fixed |
| C-17 | minor | "X.69 to X.71" swept in non-readings | Fixed: listed explicitly |
| C-18 | minor | three Draft 5 readings missing from the R.0 table | Fixed: II.0i, IV.1.5c, R.5c added |
| C-19 | minor | TikZ in the shared preamble changed Draft 4's regenerated source | Fixed: TikZ only when a raw block is present; Draft 4 regenerates identically apart from its stamps |
| C-20 | minor | duplicated phrase in the introduction | Fixed |

Suggestions taken for intuition: the words (size, gate factor, cost, angle, turn, half-turn, full turn, zeta) defined once; a run in
polar form worked through; the encoder as the case N = 2; where the rules stop; "Figure 1" referenced, with a note for Markdown readers.
Not taken: a unit-circle figure (left for a later draft).
