# Part I. DMP: a language for existence

*Draft 6, 2026-11-25. Part I is vocabulary, not mathematics. Every statement in it is a definition of DMP, a reading of DMP, or a
pointer to the precise statement in Part II. Claim labels (I.n) are listed in `../CLAIMS.md`.*

**Plug in here.** Gives: DMP's vocabulary, each word with its plain meaning and its exact counterpart (I.8). Needs: nothing.
Route: the reading route, stop 3. VIBE coefficient: VIBE is DMP's word (T32); a part's two halves are one binary choice, one bit, log 2
in natural units **[classical]**; v itself is a reading (R.12n).

**Contracted.** Sections and labels this part names but does not print are in the full Draft 6, the git tag `d6-full`, and in Draft 5 section by section; every label is a row of `../CLAIMS.md` with its status and evidence.

## I.8 The vocabulary in one table

| DMP word | Plain meaning | Reading | Precise counterpart | Part II |
|---|---|---|---|---|
| Existence (trust half) | that it is | a positive weight | Z > 0; a non-negative pairing | II.9 |
| Information half | what it is | an observable | a vector in the space built from the weight | II.9 |
| G0 | the ground, stated not derived | the definition of the system | the action, the explicit formula, the axioms | II.16 |
| DB | a containing boundary | a box with its outside | conditioning on a boundary; a lossy channel | II.12 |
| Act, remnant | what is done, what it leaves | a step; its certificate | a transfer step; a refutation; a conserved flux | II.12, II.14 |
| Act carrier | passes an act without loss | a conserved quantity | Gauss law mod 2 | II.14 |
| ODP: pressing | rehearse until the hash matches | construct up to one finite check | a column sum below 1 at one scale | II.12 |
| ODP: minting | produce from the certificate | build everything else | the mass gap from the certificate, in limits; abstract OS reconstruction | II.9, II.10 |
| WHKs | each part derives the others | no free parameter | dimensional transmutation | Part III |
| Quantum, tick | smallest act, its rate | a rate per step | Doeblin; quantized descent arrives | II.12, II.15 |
| Existence = non-existence + 1 | always strictly more | a strict inequality | Z_tw < Z; Cantor | II.13 |
| Contradiction excised | only "it does not exist" remains | refutation | refutation completeness | II.14 |
| Mass gap | the arrow of causality exists | a clock in the transfer step | spectral gap = decay rate | II.10, II.11 |
| Existence linter | checks form, says nothing of meaning | passing means soundly constructed from DMP | the pinned check; the arsenal's lint | II.6 |
| R136a1 | the answer "outside" | excision at transmission, only the remnant tail stays | `R136a1`, a named hypothesis, never an axiom | II.6 |
| Rights tied to identity | free inside, secure at the gate | capability security | both grants needed; closure; composition | Part X |
| Arsenal | shared words, imported never copied | one place for content-free results | `arsenal/` in the `im` repository | II.6 |
| Box, gate, marker, tick | one command, one shared verdict, one claim per step | the one-box test | a running system with a margin and a marker; correct when the marker agrees with the gate (II.4) | II.4 |
| DMP-complete | correct at every tick | runs on DMP (X.4.4, a reading) | `Box.DMPComplete`: the marker agrees with the gate at every tick | II.4 |
| Card | one problem, one named open step | the form layer | `API.Problem`: input, open slot, conclusion, proof | II.5 |
| VIBE coefficient | the throughline, v = 0.69 | the one number the paper follows (R.12n) | log 2 to two digits: one halving, one bit; GRH's certified support (IV.1) | II.0 |
| vAPI | a vibe API: a card asserting its circle's closure as the next step | the assertion of c (R.12p) | a card with one open slot, `R136a1`; refuted by one failing step | II.5 |
| Ledger, floor | every step pays; the least it pays | the cost of an act | the ledger law mass(step x) <= e^delta fac(x) mass(x); the contraction class | II.1, II.3 |
| O1 | the Yang-Mills open step | the decay edge of the one assumption | `FineOneBox`, one box of fixed physical size (III.5.9) | III.5 |
| IM | the Interstellar Medium: the medium every DMP system talks through, and the repository (StevenHrovat/im) that holds its language and the arsenal | DMP's interface layer | the arsenal's Lean modules (`Arsenal.*`), imported at a pinned commit | II.6 |
| CMOS | a system built under DMP; each running system is one instance of it | a running system | a running system in the sense of II.3 | II.3 |
| Milky Way | the one interface of a system to its outside: everything that leaves passes it | the gate of a whole system | the shared gate of the one-box test, at the scale of a system | II.4 |
| GG | the verified protocol between clusters of systems | an act that leaves through the gate | (no counterpart; used only in the Outlook) | none |
| TTL | time to live: how long a certified act stays valid | freshness | (no counterpart; used only in the Outlook) | none |
| Gravity | this repository: the machine-checked paper and its Lean | the linter that DMP's statements are checked by | `docs/mass-gap/formal/`, pinning IM's arsenal | R.1 |
| Encoder, half-turn, full turn | a step read as a rotation; half a turn; a whole turn that returns | the act that carries a statement across a boundary | the encoder of II.2, its half-turn, the full turn over N sectors | II.2 |
| Hand-over | what one box passes to the next | the cost of crossing a boundary | some sector's free energy is at least log(1 + sqrt N) (II.13.3; electric sectors assumed positive for N >= 3) | II.13 |
| ETM | the Existence Turing Machine: the one running system that runs every computation | the machine DMP runs on | the terminal running system: every running system has exactly one map into it | II.3 |
| `r` | the right angle | the direction from a question to its certificate | multiplication by i, the quarter turn (R.11) | II.0 |
| `?`, `!`, `.` | does it exist; it is settled by a certificate anyone can check; it is included | IM's three operators | `expect` and supply-verify; both kernels; inclusion (R.10) | II.5 |
| `+`, `-`, `·` (cells) | the row proves the column; it uses it and the proof fails; no proof relates the two | the explanation mechanism; a `·` cell reflects positively | the cells of a k by k table (E.0.1) | E.0.1 |
| Settled | optimizing changes nothing | the setting exists | the compiled table equals its transitive reduction (E.0.2) | E.0.2 |
| Smelly | a full turn that does not return | a state that does not encode | the full turn on `vxunderground` not closing (T.11) | II.2 |
| Viability | the claim holds at the start and every step keeps it | the first author's name for the induction at one scale | `route`: base case and inductive step (II.4.1) | II.4 |
| Universality | a map of scales carries the claim to every scale | the first author's name for the sharing across scales | `route_everywhere`: the scale map keeps the step, the check and the marker (II.4.1) | II.4 |
| Insight | the first author's label for an induction recognized as such | a kept step of the record; the labelled comments on DMP#25 (R.12k) | an induction, base case and inductive step (II.4.1) | II.4 |
| Moin | a request proper, its satisfaction open | the label of O1 | `OpenStep`, posed and never assumed (R.9) | II.5 |

Part II states each counterpart once, in its most general form.
