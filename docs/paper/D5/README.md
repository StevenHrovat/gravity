# Draft 5 of GUID v8 (`D5`)

Draft 5 grew from Draft 4 and adds to it. Draft 4 is the merged state and is never edited: it stays whole in `docs/paper`
(`draft/`, `CLAIMS.md`, `references.md`, `latex/guid-v8.pdf`). From Draft 5 on every draft lives whole in its own folder,
`docs/paper/DN`, grown from the draft before it:

| Draft | Folder | Grown from | PDF |
|---|---|---|---|
| 4 (merged, G0) | `docs/paper` | 3 | `docs/paper/latex/guid-v8.pdf` |
| 5 (G0 + 1) | `docs/paper/D5` | 4 | `docs/paper/D5/latex/guid-v8-D5.pdf` |

Draft 4 is the drafts' G0: its merged identity is fixed, and it carries "Merged at Draft 4". Draft 5 is G0 + 1, and from here on
a draft names only its number ("Draft 5"): its merged identity is implied by the draft it grew from.

A draft's folder holds its parts (`draft/`), its claims ledger (`CLAIMS.md`), its bibliography (`references.md`), its outline and
its typeset paper. Shared by all drafts, and only ever added to: the Lean (`docs/mass-gap/formal`, `docs/unified`), the review
record (`../REVIEW.md`, `../review/`) and the reproduction guide (`../REPRODUCE.md`). A draft is reproduced exactly at the commit
its title page names.

**The headline.** Every observable system has a one-box description that is DMP-complete exactly when its claim holds; from it
follows a route to the proof, and once that route is shown its truth is certified universally: at every tick, and, with the gate
shared across scales, at every scale. In Lean this is IM's `Arsenal/Observable.lean`, the API every card instantiates (II.4.1).

**What Draft 5 adds.** One tool, the full turn (one turn around a point, averaged), from the first author's reading of `n!` as a
full turn: IM's `Arsenal/FullTurn.lean`, the SU(N) hand-over over all N centre sectors (`General/SUNFullTurn.lean`), and its use in
II.2.7, II.13.3, II.13.4, III.3.1c, III.5.4d, IV.1.5c, VII.3.5f and Appendix R (R.5c, R.6a, R.7, R.8); the headline in the
abstract, the introduction and II.4.1, each problem part opening with its system as observed; Appendix T, the verify toy on binary
words (IM, `Arsenal/Toy.lean`); every trusted hash proven by rotation (`tools/trust-roundtrip.sh`, R.6b). The one assumption O1 is untouched.

**Build and check**, from the repository root:

```
tools/reproduce.sh paper D5      # ledger, privacy scan, LaTeX and PDF of this draft
python tools/claims-check.py D5  # the ledger check alone
```

`tools/reproduce.sh paper` without a name rebuilds Draft 4's PDF with a new build stamp; never commit that rebuild from a later
draft's branch, so that Draft 4 stays as merged. The other stages (`evidence`, `lean`, `certs`, `kernels`) are shared with Draft 4: `tools/reproduce.sh lean` reruns every axiom
script, including the ones Draft 5 added to.
