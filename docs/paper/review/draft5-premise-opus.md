# Review of Draft 5 under its premise (Opus, medium effort)

Reviewer: an Opus subagent at medium effort, run from the coordinating session on 2026-11-25 at the first author's request ("to see if
the reviewer agrees and what it would like to have in addition or clarified"), on gravity `draft-5` at `67bd0f5` and IM `full-turn` at
`444bbfd`, in fresh clones. Its runs of `tools/reproduce.sh paper D5` and `certs` passed, `sha256_scaled.py` reproduced its log
byte for byte, and Draft 4 was untouched.

**Verdict.** The premise is accepted as mathematics: representation by definition, the route as induction on the tick, every scale
as a pullback along the shared-gate map, falsifiability as modus tollens. As a framing it is coherent and useful. Three wordings were
not accepted: "from it follows a route" (nothing follows; it says what must be shown), "certified universally ... at every scale" (the
content sits in the map), and the one assumption as "the route's shared step" (on the cards no family of scales is defined and the
open content is the start). The coordinator checked the factual findings: Navier-Stokes has three cards (`routeI`, `regularity`,
`abProblem`); `ymBox` and `nsBox` are gravity's own box type; no card has a family of scale boxes in Lean.

| id | sev | problem | disposition |
|---|---|---|---|
| P-1 | major | "Part VI has no card of its own": Navier-Stokes has three cards | Fixed: three cards, each a tick box with the open part in the base case, not assumed; the model box separate |
| P-2 | major | The one assumption as "the shared step": on the cards the open statement is the start | Fixed: Part X's opener and the abstract name the base case; sharing has content only where a family of scales is defined (G2, the toy) |
| P-3 | major | "Step" in three senses | Fixed by the first author's choice of familiar vocabulary: restatement, induction, base case, inductive step; the card's slot keeps its name, the open step |
| P-4 | major | `ymBox`, `nsBox` are gravity's box type, no Lean bridge | Fixed: their reading as observable systems marked [paper] in the II.4.1 table and ledger II.4g, the bridge named as an upgrade |
| P-5 | minor | III opener: quantifiers; `fineOneBox_iff_complete` | Fixed |
| P-6 | minor | VI opener: what fails is the energy ledger as a certificate | Fixed |
| P-7 | minor | IV opener: the certified first scales are inside the statement | Fixed |
| P-8 | minor | GU: a box and no card | Fixed in the IX opener and the table |
| P-9 | minor | "any known rotation" | Fixed: "for example 5 + 21" |
| P-10 | minor | On one bit the induction is free; the content of the sharing is in the map | Fixed in T.2 and II.4.1 |
| P-11 | minor | vxRead past the end vacuous | Fixed in T.5 |
| P-12 | minor | T.6 dependency | Fixed: T.5 |
| P-13 | minor | T.6 counts against expectation | Fixed: the expected counts stated beside the single draws |

Suggestions taken: the "what each word buys" list (II.4.1), the problem-by-problem table (II.4.1), T.6 linked to the headline ("2^256
is the cost of having no induction"), the sentence on why the marker always asserts the claim (`selfMarked_complete` as its vacuous
opposite). Not taken: a figure (left for a later draft).
