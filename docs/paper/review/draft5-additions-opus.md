# Review of the Draft 5 additions: Moin, the leading zero, the finite layer on the kernel alone

Opus subagent at medium effort, 2026-11-25, on gravity `0bb85b5` and IM `fcec0a6`. Scope: Appendix R.9 (claims R.9a, R.9b) with IM's
`ImChannelState` and the leading-zero lemmas; Appendix T.7 and T.8 (claims T.12, T.13) with IM's `arsenal/core`; reference 224.
Read only. Result: 1 blocker, 6 should-fix, 6 nits. Confirmed: the core's 20 declarations, 14 on no axiom (CI run on `fcec0a6`);
137 ledger rows with a reading mark, 115 leading with it; labels unique; the statuses match the prose marks; the pin at `fcec0a6`.

| # | Severity | Where | Finding | Fixed by |
|---|---|---|---|---|
| 1 | blocker | T.8, T.13, IM README and the core's docstring | "Lean trusts no library; the kernel checks every Mathlib proof again" is wrong for the `lake exe cache get` workflow T.7 gives: prebuilt `.olean` files are loaded without a new check. The trusted base also holds the kernel's built-in Nat arithmetic, the prelude and the axioms. | T.7, T.8 and T.13 now say the library *need not* be trusted, that cached files are loaded unchecked and a replay (`lean4checker`, or nanoda over `lean4export`) repeats the check, and what is trusted; IM #22 the same in the README and the docstring |
| 2 | should-fix | T.8 | "Every statement of T.5 ... needs no Mathlib" overclaims; several T.5 results use Mathlib structures. | T.8 names the string facts the core holds |
| 3 | should-fix | IM README, the core's docstring | "decided by evaluation" is false for the general `n`-bit lemmas, which are proved. | IM #22 |
| 4 | should-fix | R.9b care point, ledger R.9b, T.8 | "lossless, nothing spilled" contradicts `rotl_never_smelly`: a rotation never loses a bit. The doubling certifies that no bit wrapped round. | R.9b, T.8, the ledger, IM #22 |
| 5 | should-fix | T.8 / T.13 | the reading says kernel and language "depend on each other", the exact part says one way. | T.8 and T.13 add: exactly, the dependency is one way |
| 6 | should-fix | T.13 care point | the care point holds in the finite layer too (`rotl`, `Smelly`, `rotr`). | T.8 and T.13 |
| 7 | should-fix | R.9a | "the base case of the Yang-Mills card" had no mark after a reading. | marked [reading] |
| 8 | should-fix | IM `ImFrames.cs`, `language.md`, R.9a | no refused state: a refusal leaves the client in Moin until it drops the session. | stated in R.9a, the ledger and IM #22 (a refusal is not a state) |
| 9 | nit | R.9a | `ImChannelState` is the client's view. | "seen from the client" |
| 10 | nit | IM test | the bad accept was only a malformed chain. | IM #22 adds a well-formed accept with a bad signature (`BadGateSignature`) |
| 11 | nit | R.9b | `vx_rotl` in the arsenal is a corollary, not an evaluation. | R.9b says which is which and points to the core's `moin_byte` |
| 12 | nit | R.9a | "never an axiom" is a convention the audit enforces. | "(the axiom audit shows none is assumed)" |
| 13 | nit | T.7 | "on Lean's three standard axioms only" reads as "on all three". | "on no more than" |

Overall (the reviewer): the exact mathematical content is correct and honestly scoped, the rotation statements carry the needed
hypotheses, the axiom count is confirmed by CI, the C# Moin state works the way the prose says, O1 stays open and every reading is
marked; the real problem was the description of Lean's trusted base.
