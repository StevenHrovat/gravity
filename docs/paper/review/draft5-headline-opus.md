# Review of Draft 5's headline (Opus, medium effort)

Reviewer: an Opus subagent at medium effort, run from the coordinating session on 2026-11-25, on gravity `draft-5` at `cc7a502` and IM
`full-turn` at `c8707b4`, in fresh clones. Scope: the first author's headline (every observable system has a one-box description,
DMP-complete exactly when its claim holds, with a route to the proof certified universally once shown) as stated in the abstract, the
introduction and II.4.1, against IM's `Arsenal/Observable.lean`; `full_turn_slope` and R.8; the abstract's length; Draft 4 untouched.
Its runs of `tools/reproduce.sh paper D5` and `tools/reproduce.sh paper` passed; Draft 4's paths were unchanged against main.

Verdict: the Lean is sound and non-vacuous, and nothing presents a problem as solved; the prose claimed more than the Lean in four
places. The coordinator checked the main finding (H-1) by reading `ETM/CardBox.lean` (`tickBox`, the card box as a constant tick box)
against `Observable.route`, and the reference the reviewer cited from memory (H-10) on its Crossref record.

| id | sev | location | problem | disposition |
|---|---|---|---|---|
| H-1 | major | introduction, II.4.1, abstract | On a card the claim is the same at every tick, so the route's step is free and the whole open statement is the start; "the content is the route's one step" was wrong there | Fixed: a route has a start and a step; on a card the open statement is the start, on the boxes with their own gate factor (Yang-Mills III.12, model Navier-Stokes VI.8) the step carries it; abstract "the route's start or step carries the content" |
| H-2 | major | II.4.1, introduction, ledger II.4g | "Each card of Parts III to IX": Part VI has no card, IX has a tick box; "is the case" not literal (different margins), no Lean link | Fixed: the parts named; Part VI said to have no card; new Lean bridge `tickBox_observable` (`ETM/CardBox.lean`): the tick box passes exactly when the observable system's description is DMP-complete |
| H-3 | minor | II.4.1 | "marker is the system's claim" suggests a varying marker | Fixed: the marker always asserts the claim (inside), the gate reads whether it is true; `correct_iff` cited |
| H-4 | minor | II.4.1, ledger | "decidable" restricts nothing classically | Fixed: said so; every proposition is an observable system with one state |
| H-5 | minor | II.4.1, introduction | `route` is induction; "universally" means every tick and every scale that shares the gate | Fixed: "This is induction on the tick"; the What-is-new bullet says "at every tick ... and at every scale that shares the gate"; the abstract's wording already scoped the scales to the shared gate |
| H-6 | minor | abstract, What-is-new bullet | "exactly when its claim holds" without "at every tick" | Fixed in both |
| H-7 | minor | R.8a | The ratio of two turns needs f holomorphic on a disc, the second radius arbitrary, the 1/(2 pi i) factors | Fixed |
| H-8 | minor | R.8a | Tangent space as derivations of finite dimension holds for smooth (C-infinity) manifolds | Fixed; Lee 2012 still marked "as recalled" (the chapter was not re-read) |
| H-9 | minor | R.8b | The Lean covers the cyclic group; Shor breaks factoring in polynomial time on a quantum computer; the abelian hidden subgroup problem for finite abelian groups | Fixed |
| H-10 | minor | R.8b | Strong Fourier sampling is known to fail for the symmetric groups; "traced to its origin" is not in the Lean | Fixed: Moore-Russell-Schulman 2008 added (reference 219, read on Crossref); [Lean] kept on "every hash has collisions" only, the origin [paper] |
| H-11 | minor | abstract | Only 2 characters to spare | Fixed: now 1,901 characters |
| H-12 | minor | references preamble | Row 217 is an arXiv record | Fixed: "Crossref or arXiv record" |
| H-13 | minor | tools | `reproduce.sh paper` rebuilds Draft 4's PDF with a new stamp; committing it from `draft-5` would touch Draft 4 | Fixed by rule: `D5/README.md` says never to commit that rebuild from a later draft's branch |
