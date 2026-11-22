# Trapping deep cores (m1-tools, 2026-11-22)

Brief: assess the owner's trapping proposal (`../../PREP.md`, last section, "Trapping must be possible", with its three
addenda): a core that stays deep is **trapped** — frozen as a hole, excluded, only its boundary existence transported,
charged once at its root plus a per-step maintenance cost — instead of being avoided or captured. Questions: does this
close §5.3 of the paper outline without NT′(b′)? What does a trapped balanced (non-centre-valued) star cost and what is
transported for it? Does a fixed 1-2-step trapping delay (one "assertion tick") fit the bookkeeping? Paper level; claim
marks as in `NOTE.md`.

## 0. Result in plain words

1. **Yes, with one design choice: trapped holes must be excised from the block average, not just frozen.** Freezing alone
   is not enough: the coarse bonds at the core's site average paths that start inside the hole, so the hole's frozen
   values still enter logarithms, and for non-centre-valued cores those can sit near the cut (and products of them can,
   at later scales). If instead the block average reads a **canonical smooth filling** of the hole, computed separately
   inside each block from the hole's surroundings in that block, no logarithm ever sees the hole. Then the cut is never
   met, and **NT′(b′), the Cap Lemma and even NT′(a) are not needed** for deep cores. (They remain valid; NT′(a) and the
   Z2 labels of `TWIST.md` become an optional alternative for centre-valued cores.)
2. **The accounting is exactly "root once + summed maintenance", and it closes.** For a trapped core with root at scale
   `h`, action `a/g_h²` (`a ≥ A_min`, deep), hole diameter `D0 ≤ 100 M R_h` (root-scale units):
   * **root (once):** suppression `exp(-a/g_h²)`; the hole's interior is integrated once (entropy `≤ O(1) |H| log g_h^{-2}`,
     polylogarithmic); the first `log_L D0` steps, while the hole is not yet smaller than a block, are carried as a Balaban
     large-field region at polylogarithmic cost per step;
   * **maintenance (per step, for ever):** the frozen hole's back-reaction on the renormalisation of its surroundings,
     bounded by P2′: `|Δ_k| ≤ C [ρ_k^{d-2}(1 + p0(g_k)²) + ρ_k^{(d-2)/2} p0(g_k)(1 + a^{1/2}/g_h)]`, `ρ_k = D0 L^{-(k-h)}`;
   * **total:** `polylog(g_h^{-2}) + C(D0^{d-2} p0(g_h)² + D0^{(d-2)/2} p0(g_h) a^{1/2}/g_h) ≪ a/g_h²`, so every root
     keeps at least `exp(-a/(2 g_h²))`, and the sum over roots is `≤ C exp(-A_min/(2 g_k²)) ≪ exp(-p0(g_k))` (`D-PIN.md`
     4(a), asymptotic freedom making the deep end converge, the owner's "near infinite root cost" at `G0`).
3. **A trapped balanced star costs the same as any trapped core.** Its boundary datum is not a ±1 label but an SU(2)-valued
   record (the hole's frozen content, or equivalently the transports from a base point to its boundary points, modulo
   gauge). With excision this record never enters a later average or integral; it is a label of the term, like Balaban's
   history labels. Its cost is paid at the root (the action and the one-time entropy above) and in the maintenance, which
   depends on the hole's size and the mismatch with its surroundings, not on whether the datum is central.
4. **A fixed delay fits** (and `E7J.md` fixes it at `N_t = 0`: trap at creation, so that no deep variable ever enters a
   block constraint; with the trapping threshold `r0 ≤ c/L²`, still `O(1)` in `g`). Deep cores (some plaquette at
   distance `≥ r0` from the identity) are trapped after a fixed number of steps `N_t` (0, 1 or 2 — one "assertion
   tick"; `N_t = 0` is the choice used from `E7J.md` on); during those steps they are carried as large-field
   regions at polylogarithmic cost, paid by the root. Balaban's delay `N ≈ R` stays as it is for the **moderate** large
   fields (above his threshold `ε_k = g_k p0(g_k)` but below `r0`), which are diluted (Lemma D-mod) and renormalised by the
   conditional step. The two classes do not interfere. Trapping a deep core that would have diluted anyway (most do, in
   2-6 steps) is harmless: it is charged once at its root like any other.
5. **What trapping changes downstream, stated plainly.** With excision, the block field at `L_*` no longer shows trapped
   cores; they live in records. The `L_*` law is then "smooth block field + a rare set of records" — the mixture (defect)
   form that `../c5d-supplier/BALABAN-READING.md` section 5 recommends for UV1 anyway. Observables near a record need its
   interior (rare by the root suppression).
6. **Open checks (all paper, none new in kind):** T1 the per-block filling is well defined and regular (a variational
   problem of `[15]`'s type in one block); T2 the excised blocking keeps link reflection positivity (the per-block rule is
   what makes it work); T3 P2′ applies with excision (yes as written: the surroundings' integrals see the true action with
   the frozen hole; the blocking reads the filling, and exactness holds for any measurable blocking); T4 the mismatch of
   two neighbouring blocks' fillings inside a hole is small-field (it is `O(ε D0)`, polylogarithmic times `g p0`).

## 1. Why freezing alone is not enough

At the scale where the trapped core sits at a block centre `y`, every coarse bond at `y` averages paths `Γ ∈ G(y, x)`
that start at `y`, inside the hole. With the hole frozen, each such path's transport is (frozen transport from `y` to
the hole boundary) × (smooth transport outside). The logarithm of a loop is then evaluated near the frozen relative
element. For a centre-valued core these are `±1` and a Z2 label removes them (`TWIST.md`); for a non-centre-valued core
NT′(a) can put the frozen star's pairwise angles below 168.7°, but once the site is no longer a block centre, paths cross
the hole, and loops contain products of several frozen relative elements, which NT′(a) does not control. Freezing removes
the dynamics (no orbit, so no (b′)), but not the cut.

## 2. Excision

**Rule.** At scale `m`, for each block `B` of the next scale, and each trapped hole `H`: replace the bonds of `H ∩ B` by the
canonical filling `F_B` = the least-action configuration on `H ∩ B` with the bonds of `B \ H` as data (unique modulo gauge
in the small-field regime, by a variational problem of `[15]`'s type; covariant). Balaban's average of the coarse bonds
reads the filled field. The record of `H` (its frozen content) is kept with the term.

**Properties (paper).** Covariant (the filling is); local (each block uses only its own bonds); link reflection positive
(blocks never straddle a reflection plane on block faces, so the half property of `TWIST.md` 3 holds; `rp_map`
assembles it); exact (`map_resample_eq` with the records in the conditioning variable). The filled field is regular near
the hole (its data are), so every logarithm the average takes is of a loop of a regular field: no cut.

## 3. The accounting (as the owner frames it: root once + maintenance per step)

| item | bound | source |
|---|---|---|
| root suppression | `exp(-a/g_h²)`, `a ≥ A_min = c0 r0²` | P4 (`D-PIN.md` 4; `[15]` Thm 1, [V] p. 380) |
| root entropy (interior integrated once) | `≤ O(1) |H| log g_h^{-2}`, `|H| ≤ (100 M R_h)^d` | Balaban's normalisation constants ([V] p. 380) |
| carrying until the hole is subscale (`log_L D0` steps) | `≤ log_L D0 · O(1) M^d R^{d+1}` | `D-N.md` 2 |
| maintenance per step afterwards | `|Δ_k|` of P2′ | `P2-PRIME.md` |
| maintenance summed | `≤ C (D0^{d-2} p0(g_h)² + D0^{(d-2)/2} p0(g_h) a^{1/2}/g_h)` | P2′ corollary |
| **net** | `≤ exp(-a/g_h² + polylog + C a^{1/2} polylog/g_h) ≤ exp(-a/(2 g_h²))` | |
| sum over roots at scale `k` (per cell, `O(R0^d)` positions per scale) | `≤ C exp(-A_min/(2 g_k²)) ≪ exp(-p0(g_k))` | `D-PIN.md` 4(a) |

The same table holds for centre-valued and balanced cores; nothing in it depends on the record's values.

## 4. Effect on the paper outline

§5.3 becomes: **deep cores are trapped and excised** (root + maintenance accounting above), with T1-T4 as the remaining
checks; NT′ (a and the Cap Lemma) and the Z2 labels are kept as an alternative for centre-valued cores and as
statements about the plain average, no longer on the critical path. §7 (rooted cores) absorbs the accounting. The open
new items for deep cores are T1-T4 (about 3 pages, routine-looking) and the P2′ write-up.
