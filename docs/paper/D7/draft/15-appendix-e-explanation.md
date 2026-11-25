# Appendix E. The explanation mechanism applied

*Draft 6, 2026-11-25. The tables of II.0.2 for what Draft 5 establishes, and the optimizer of II.0.3 applied to them (E.9 to E.11).
Lean: IM, `arsenal/core/ArsenalCore/Matrix.lean` (IM `c441ed5`) and `Optimizer.lean` (IM `e9a4057`), on Lean's kernel alone. Tools:
IM's `tools/rebuild matrix` (with `--optimize` from IM `e9a4057`) and `tools/rebuild check`. Claim labels (E.n) are listed in
`../CLAIMS.md`.*

Every table here has the parts as its rows and columns; the cell of a row and a column says whether the row proves the column, that is,
that the use is proven, not that the row ran the proof. A cell where the row uses the column must be `+`; a `·` cell, where no proof
relates the two, reflects positively; a current part's own cell is a use, an earlier version's is `·` (II.0.2).

## E.1 The parts by version: a DAG

Five versions take part, as Gravity `db03d05` (the state Draft 5 was merged at) sees them: DMP `1370dc0` (0.9.6), DMP `4400cce` (0.9.9),
Gravity `4ec1131`, IM `f8baf3d` and Gravity `db03d05`. Gravity `4ec1131` holds DMP `1370dc0`; IM `f8baf3d` holds DMP `1370dc0` and
Gravity `4ec1131`; Gravity `db03d05` holds DMP `4400cce` and pins IM `f8baf3d`. The three earlier versions are frozen, so their own
cells are `·`; the current IM and Gravity run their own round trips. The table is:

| proves → | DMP 1370dc0 | DMP 4400cce | Gravity 4ec1131 | IM f8baf3d | Gravity db03d05 |
|---|---|---|---|---|---|
| **DMP 1370dc0** | · | · | · | · | · |
| **DMP 4400cce** | · | · | · | · | · |
| **Gravity 4ec1131** | + | · | · | · | · |
| **IM f8baf3d** | + | · | + | + | · |
| **Gravity db03d05** | · | + | · | + | + |

Every use points to an earlier version (`versions_dag`), every used cell is proven and every `·` cell reflects positively, so every
cell of the effective table is `+` (`versions_explained`), and no chain of uses returns (`versions_no_return`) **[Lean]**. Each use is
proven by a round trip run on 2026-11-25: IM's, from StevenHrovat/im#25 on, rebuilds its held copies of DMP `1370dc0` and Gravity
`4ec1131` byte for byte and checks the copy of DMP inside Gravity `4ec1131` against its pin; Gravity `db03d05`'s rebuilds its held DMP
`4400cce` and fetches its pinned IM by its id **[paper]** (claim E.1). Collapsed to repositories, IM and Gravity use each other
(`repos_cycle`), so the repositories are not a DAG (`repos_not_dag`) **[Lean]**; the versions are. In the first author's words, two such
parts do not exist at the same time **[reading]** (II.0.2c).

## E.2 The repositories: what the matrix asserts

`tools/rebuild matrix` puts IM and the repositories named into one table, with each current part's own round trip on the diagonal. Run
on 2026-11-25 as `tools/reproduce.sh matrix` from Gravity `bb69b82` (Draft 6's first commit) with the IM it pins, `69004d7`: every
cell of IM and Gravity is `+`; IM holds Gravity `4ec1131`, Gravity pins IM, and each passes its own round trip. Run by the same tool on
clean clones with DMP as a third part: its row is `·` (DMP holds and pins nothing) and reflects positively, its column is `+` (IM and
Gravity hold it, each copy proven back and forth), and its own cell is `-`, since DMP is a current part without a round trip of its
own **[paper]** (claim E.2). Since IM `e9a4057` that cell is `.` (E.11).

| proves → | IM | Gravity | DMP |
|---|---|---|---|
| **IM** | + | + | + |
| **Gravity** | + | + | + |
| **DMP** | · | · | - |

## E.3 Extensibility: what joining costs

Adding DMP to the 2 by 2 of IM and Gravity checks nothing of the 2 by 2 again (`allPlus_succ_iff`) **[Lean]** and costs 2 · 2 + 1 = 5
cells (arithmetic, `new_cells`). Of the five, its row is two `·` cells, its column two `+` cells, and its own cell is the one that is
missing: a round trip of DMP's own, which is DMP's to add **[paper]** (claim E.3). The table shows exactly what a new part owes.

## E.4 The kernels and their targets

Two kernels written separately, Lean's own and nanoda, each check four targets in quick mode, measured on 2026-11-25. The core, the
arsenal and the paper's Lean are Draft 5's claim T.14 (the core now with the Lean of II.0.2); the evidence chain and the module counts
are new in Draft 6.

| checks → | IM core (IM `c441ed5`) | IM arsenal (IM `7881f77`, unchanged since) | the paper's Lean (Gravity `dcafe94`, IM `9686dc8`) | the evidence chain (same run) |
|---|---|---|---|---|
| **Lean's kernel** | + (2 modules; the root only imports) | + (14 modules) | + (364 modules) | + (24 modules) |
| **nanoda** | + (3,673 declarations) | + (82,502) | + (103,546) | + (5,261) |

Every cell is `+` **[numerical]** (claim E.4). As a table over the six parts, every cell where a kernel checks a target is a use and
proven, and every other cell reflects positively.

## E.5 Derivations: explaining a result of Draft 5

Gravity `db03d05` does not use DMP `1370dc0` directly, yet reaches it in one derivation step, through IM
(`gravity_reaches_dmp_through_im`) **[Lean]**. Read in the sense of II.0.2, a result of Draft 5 is explained the same way: claim T.12
(the finite layer, on the kernel alone) by the chain that Gravity pins IM (E.2), both kernels accept IM's core (E.4), and the core holds
the statements T.12 names **[reading]** (claim E.5). Its links are of different kinds (a pin, a kernel check, a holding), so it is a
chain in the reading, not one Lean table.

## E.6 Where the mechanism stops

An open step is a cell that is not `+`. O1 is posed and named, never assumed (`OpenStep`, R.9): its request is proper and its
satisfaction open. Derivation makes a cell `+` only along a chain of cells already `+` (`derive_sound`) **[Lean]**; Draft 5 establishes
no cell from which such a chain reaches O1, which is its one open step (Part X) **[paper]**; and a derived cell explains rather than
proves **[reading]** (claim E.6). So Draft 6 adds no proof of its own; O1 stays the one open step.

## E.7 DMP's statement, and the drafts as a library

**DMP's statement (claim E.7).** The first author: DMP's statement is only `.`, since it can include **[reading]**. Exactly: by
repository DMP uses nothing, its row is empty, and every other part includes it (`dmp_only_included`) **[Lean]**; in E.2 its row is all
`·` and its column all `+` **[paper]**. Under this reading DMP makes no statement for a round trip to prove; the matrix tool still
marked DMP's own cell `-`, since DMP is a current part without a round trip of its own (E.3); since IM `e9a4057` it marks it `.`
(E.11).

**The drafts as a library (claim E.8).** The first author: the Dx papers act as additional readings that keep their transitive
property to G0 at Draft 4, our own extensible library of D-grade tools and insight **[reading]**. Exactly: each draft grows from the
one before, so the drafts form a DAG however many there are (`drafts_dag`) and none reaches itself (`drafts_no_return`); Draft 6 does
not grow from Draft 4 directly yet reaches it through Draft 5 (`draft6_reaches_g0`); in a library of eight drafts every later draft
reaches G0 within three derivation steps (`every_draft_reaches_g0`); and a new draft is one more part, its own row, column and cell,
with nothing earlier checked again (`allPlus_succ_iff`) **[Lean]**. G0 stays as it is: Draft 4 is never edited, and its LaTeX
regenerates identically apart from its build stamps **[paper]**.

## E.9 The optimizer applied: the versions are not settled

The optimizer of II.0.3 on the version table of E.1. IM `f8baf3d` uses DMP `1370dc0` directly, and it also holds Gravity `4ec1131`,
which holds that same DMP. So `?` is answered by `.`: the direct use is redundant (`im_use_of_dmp_redundant`), the table is not settled
(`versions_not_settled`), and its reduction removes exactly that use (`versions_reduced`); the reduced table is settled and reaches
every part the measured table reaches (`versions_settled`) **[Lean]**.

`tools/rebuild matrix --optimize` builds the same table from the repositories as they are, one node per repository at one commit: each
part at its head, each held copy and pinned commit at its pin, a held copy's own held copies, and the uses of a pinned commit read from
the part's history where it is there. Run on 2026-11-25 by `tools/reproduce.sh matrix` from Gravity `3841987` (this draft's branch) with the IM it
pins, `966a016`, it finds the same one redundant use at the current commits, IM's own copy of DMP `1370dc0`, already included through its
copy of Gravity `4ec1131`, and prints the shortest sentences, each a chain of kept uses ending in `!`:

```
use: im@966a016 -> dmp@1370dc0  ? answered by .: redundant, already included through gravity@4ec1131
sentence: gravity@3841987 . dmp@4400cce !
sentence: gravity@3841987 . im@966a016 . gravity@4ec1131 . dmp@1370dc0 !
optimizer: NOT SETTLED, 1 of 5 uses redundant: the optimized form removes them (5 versions)
```

`tools/reproduce.sh matrix` asserts exactly this: every cell `+`, and the versions not settled, by exactly that one use **[paper]**
(claim E.9); a settled result, or any other redundant use, fails the stage until this section is updated. In the first author's reading of II.0.3 the system exists only when it is settled. Settling it means IM
dropping its own copy of DMP and including it through Gravity; that is IM's to decide, and Draft 6 does not do it.

## E.10 The drafts are settled; the repositories cannot be optimized without losing DMP

The drafts are settled however many there are, since each grows from the one before and from nothing else (`drafts_settled`)
**[Lean]**; `D6 . D5 . D4 !` is already the shortest sentence. On the repository table, where IM and Gravity use each other, each use
of DMP is redundant through the other repository, both are removed, and nothing reaches DMP any more (`repos_reduce_loses_dmp`)
**[Lean]** (claim E.10). The optimizer keeps every derivation only on a DAG, which is why it works on versions.

## E.11 DMP's own cell: `.`

The first author: a part that includes nothing settles by `!` alone, so DMP's own cell counts as `.` **[reading]**. From IM `e9a4057`
on, `tools/rebuild matrix` marks the own cell of a part without a round trip whose row is empty as `.`, with the reason that it holds
and pins nothing; a part without a round trip that does use something stays `-`. Run on 2026-11-25 on clean clones of IM, Gravity and
DMP, the 3 by 3 passes **[paper]** (claim E.11):

| proves → | IM | Gravity | DMP |
|---|---|---|---|
| **IM** | + | + | + |
| **Gravity** | + | + | + |
| **DMP** | · | · | . |

This replaces the `-` of E.2, E.3 and E.7: DMP's statement `.` (E.7) is now what its own cell shows.
