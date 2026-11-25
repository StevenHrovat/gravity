# Appendix E. The explanation mechanism applied

*Draft 6, 2026-11-25. The tables of II.0.2 for what Draft 5 establishes. Lean: IM, `arsenal/core/ArsenalCore/Matrix.lean`, on Lean's kernel alone. Tools: IM's
`tools/rebuild matrix` and `tools/rebuild check`. Claim labels (E.n) are listed in `../CLAIMS.md`.*

Every table here has the parts as its rows and columns; the cell of a row and a column says whether the row proves the column. A cell
where the row uses the column must be `+`; a `·` cell, where no proof relates the two, reflects positively (II.0.2).

## E.1 The parts by version: a DAG

Five versions take part: DMP `1370dc0` (0.9.6), DMP `4400cce` (0.9.9), Gravity `4ec1131`, IM `f8baf3d` and Gravity `db03d05`.
Gravity `4ec1131` holds DMP `1370dc0`; IM `f8baf3d` holds DMP `1370dc0` and Gravity `4ec1131`; Gravity `db03d05` holds DMP `4400cce`
and pins IM `f8baf3d`. With the current parts' own round trips on the diagonal, the table is:

| proves → | DMP 1370dc0 | DMP 4400cce | Gravity 4ec1131 | IM f8baf3d | Gravity db03d05 |
|---|---|---|---|---|---|
| **DMP 1370dc0** | · | · | · | · | · |
| **DMP 4400cce** | · | · | · | · | · |
| **Gravity 4ec1131** | + | · | · | · | · |
| **IM f8baf3d** | + | · | + | + | · |
| **Gravity db03d05** | · | + | · | + | + |

Every use points to an earlier version (`versions_dag`), every used cell is proven and every `·` cell reflects positively, so every
cell of the effective table is `+` (`versions_explained`), and no chain of uses returns (`versions_no_return`) **[Lean]**. The proofs behind the cells are the round
trips of 2026-11-25: a held copy rebuilt byte for byte from its commit, the pinned IM fetched by its id and the id recomputed, and the
copy of DMP inside Gravity `4ec1131` hashing to its pin, which IM's round trip proves since StevenHrovat/im#25 **[paper]** (claim
E.1). Collapsed to repositories, IM and Gravity use each other (`repos_cycle`), so the repositories are not a DAG
(`repos_not_dag`) **[Lean]**. In the first author's words, two such parts do not exist at the same time: what relates them is their
versions, and the versions form a DAG.

## E.2 The repositories: what the matrix asserts

`tools/rebuild matrix` puts IM and the repositories named into one table, with each part's own round trip on the diagonal. For IM and
Gravity every cell is `+`: IM holds Gravity `4ec1131`, Gravity pins IM, and each passes its own round trip. With DMP as a third part,
its row is `·` (DMP holds and pins nothing) and reflects positively, its column is `+` (IM and Gravity hold it, each copy proven back
and forth), and its own cell is `-`: DMP has no round trip of its own **[paper]** (claim E.2).

| proves → | IM | Gravity | DMP |
|---|---|---|---|
| **IM** | + | + | + |
| **Gravity** | + | + | + |
| **DMP** | · | · | - |

## E.3 Extensibility: what joining costs

Adding DMP to the 2 by 2 of IM and Gravity costs 2 · 2 + 1 = 5 cells (`new_cells`), and nothing of the 2 by 2 is checked again
(`allPlus_succ_iff`) **[Lean]**. Of the five, its row is two `·` cells, its column two `+` cells, and its own cell is the one that
is missing: a round trip of DMP's own, which is DMP's to add **[paper]** (claim E.3). The table shows exactly what a new part owes.

## E.4 The kernels and their targets

The second table of Draft 5 (T.9): two kernels written separately, Lean's own and nanoda, each checking four targets in quick mode on
2026-11-25.

| checks → | IM core | IM arsenal | the paper's Lean | the evidence chain |
|---|---|---|---|---|
| **Lean's kernel** | + (1 module) | + (14 modules) | + (364 modules) | + (24 modules) |
| **nanoda** | + (3,543 declarations) | + (82,502) | + (103,546) | + (5,261) |

Every cell is `+` **[numerical]** (claim E.4). As a table over the six parts, every cell where a kernel checks a target is a use and
proven, and every other cell reflects positively.

## E.5 Derivations: explaining a result of Draft 5

Today's Gravity does not use DMP `1370dc0` directly, yet reaches it in one derivation step, through IM
(`gravity_reaches_dmp_through_im`) **[Lean]**. A result of Draft 5 is explained the same way. Claim T.12 (the finite layer, on the
kernel alone) is explained by its chain: Gravity pins IM, proven (E.2); IM's core is accepted by both kernels (E.4); the core holds
the statements T.12 names. Every link is a `+` cell of the tables above **[paper]** (claim E.5), and the chain is what
`chain_of_comp` says every derived cell has.

## E.6 Where the mechanism stops

An open step is a cell that is not `+`. O1 is posed and named, never assumed (`OpenStep`, R.9): its request is proper and its
satisfaction open. Derivation cannot make it `+`: every derived cell has a chain of `+` cells (`step_sound`), and on what is
established derivation changes nothing (`step_eq_of_allPlus`) **[Lean]** (claim E.6). So Draft 6 explains what Draft 5 establishes
and adds no proof of its own; O1 stays the one open step.
