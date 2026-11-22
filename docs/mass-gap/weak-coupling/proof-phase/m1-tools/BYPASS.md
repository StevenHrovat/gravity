# The bypass: persistent flux as costly large-field regions and Z2 labels (m1-tools, 2026-11-22)

Brief (coordinator; owner's choice after `MILESTONE-1.md`; `../../PREP.md`, "The quantum of assertion fixes the
thickness"): inside M1's range every persistent sheet is sub-quantum and costly, so carry it as an ordinary large-field
region, never as a background. One bounded round, stopping at the first failure:
1. sheet bookkeeping at Balaban's real per-cube rates, against the sheet's own action, with the count of sheets per
   coarse cell in physical units;
2. point-like flux as ROUTE-B Z2 labels, with their count under real rates;
3. the flat charged mode;
4. the hand-over at `K`;
5. if 1-4 close, what remains, and an updated `M1-PLAN.md`.

Scripts: `single_flip.py` (log `run_single_flip.log`). Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **Item 1 closes (paper sketch), and more simply than framed.** With the ROUTE-B split blocking (SO(3) part
   averaged, Z2 layer counted mod 2), a sheet born **thick** never enters the Z2 layer. Its flux lives only in the
   SO(3) field, so the sheet is a large-field region only while it is irregular at the current scale. That window
   starts when its curvature reaches `ε_s` and lasts until it has thinned below a block and its SO(3) image has
   diluted: about `(3/4) log g^{-2}/log L` steps, comparable to Balaban's delay. After the window the SO(3) average no
   longer sees it, and it is released into R-terms like any Balaban large-field region. So **no sheet is carried to
   `K`**. Within the window its region shrinks (volume by `L⁴`, then footprint by `L²` per step). The carrying cost at
   Balaban's rate (`O(1) log g_j^{-2}` per site per step, [V] p. 380) is at most `c log g^{-2}/(2 p0²)` (thick phase)
   and `c log g^{-2} (MR)⁴ g²` (thin phase) times the sheet's action. Both are `≪ 1`; the first is Balaban's own
   win condition. The count per coarse cell is that of Balaban's regions (alive only within the window, then
   renormalised), so the F1 trap does not arise.
2. **Item 2 fails: the Z2 labels are not rare.** In the split blocking every coarse label is the mod-2 count of
   **bare** `τ` flips (`τ_{k} = Stokes^k(τ_0)`), and a bare flip reaches scale `k` exactly when it lies on the scale-`k`
   2-skeleton (`6 L^{2k}` bare plaquettes per scale-`k` cell). The cheapest bare flip is not the closed bubble
   (`A = 24`) but a **single plaquette just past the equator**, an act. With its Bianchi compensation spread over the
   20 neighbouring plaquettes it costs at most `A_1 = 10.1/g²` (explicit configuration, `single_flip.py`). With the
   running `g_0^{-2} = g_k^{-2} + b k log L`, `b = 0.0929`, the expected number of flips feeding one coarse cell's
   labels is `≈ 6 e^{-A_1/g_k²} L^{(2 - b A_1) k}`, with `b A_1 ≤ 0.94 < 2`. It **grows without bound as the lattice
   spacing goes to zero**: coarse `τ` becomes the parity of ever more UV events, i.e. noise. (The closed skeleton
   bubbles alone would converge: `24 b = 2.23 > 1`. The open single flips on the 2-skeleton do not.) This is the F1
   counting trap again, in the Z2 layer, and caused by the same object as before: the act at the tie.
3. **Stopped there.** Items 3-5 are not done. M1-PLAN is not updated beyond what earlier rounds did.

## 1. Item 1: an extended persistent sheet

**Birth.** A sheet smooth at scale `j < s` is a regular (small-field) background, inside Balaban's theory. It becomes
irregular at the scale `s` where its curvature `π/T_s²` (scale-`s` units) reaches `ε_s = g_s p0(g_s)`, i.e.
`T_s = (π/ε_s)^{1/2}`.

**Its action** (lower bound: `transverse_lower_bound` per slice, plus the paper group step): per transverse
`T_s × T_s` tile, `≥ (2/π²) π² β/T_s² · T_s² = 2β`, and of order `2π p0/g_s` with the flux spread at curvature `ε_s`.
Per scale-`s` site of the tube about `p0²` (each plaquette at angle `ε_s` costs `ε_s²/g_s² = p0²`). Total
`S ≳ 2π p0(g_s) A_s/g_s` for sheet area `A_s` (scale-`s` units).

**Carrying, at Balaban's rate.** Every large-field domain pays `O(1) log g_j^{-2}` per site per step ([V] p. 380, (1.79),
(1.81), as in `D-N.md` 2), on unions of `M R_j`-cubes.
* **Thick phase** (`T_k = T_s L^{-(k-s)} ≥ M R_k`): the region's volume (scale-`k` units) shrinks by `L⁴` per step;
  total `≤ c log g_s^{-2} A_s T_s²/(1 - L^{-4})`. Against `S`: ratio `≲ c log g^{-2}/(2 p0²)`. This is `≪ 1` by
  Balaban's win condition `A_1² p0² ≥ O(1) M^d L^{d+1} R^{d+2}` ((1.82)), since `M^d R^{d+1} ≥ log g^{-2}` there.
* **Thin phase** (until the SO(3) image is regular): footprint about `A_k (M R)²` sites with `A_k = A_s L^{-2(k-s)}`,
  shrinking by `L²` per step; total `≤ c log g^{-2} (MR)⁴ A_s/T_s²`. Ratio to `S`: `≲ c log g^{-2} (MR)⁴ g²/(2π²) ≪ 1`.
* **Window length:** `log_L T_s + log_L(π/ε) ≈ (3/4) log g^{-2}/log L` steps. The thin phase ends when the fraction
  of averaged paths through the core, about `T_k`, is below `ε_k/π`. The equatorial-core numerics of `ROUTE-B.md`
  (one-step dilution) support this; the general SO(3) off-centre dilution lemma (F5 in SO(3)) is not proved.
* **Splitting the action:** Balaban's own factor uses about `p0²` per cube; the tube has about `p0²` per site, so half
  of `S` pays his factor and half pays the carrying; no suppression is used twice.

**After the window: released, not carried.** The Z2 layer of a thick-born sheet is `+1` at every scale, by induction:
coarse `τ` is counted from finer `τ`, never from coarse holonomies. Once its SO(3) image is regular, the coarse state
does not see it. It is renormalised like any Balaban region; the R-term bookkeeping ([III] (2.30)-(2.33)) handles the
released effects (vacuum subtracted; field dependence of dimension `≥ 4`, `F1-REPAIR.md` 2).

**Count in physical units.** Sheets alive at scale `k` were born within the last window:
`Σ_{j ≤ window} L^{4j} e^{-A_1² p0²} ≤ e^{(3/4)·4 log g^{-2} - A_1² p0²} ≪ 1` per scale-`k` cube. Older ones are
released, exactly as Balaban's regions are. **No F1 trap.**

**Thin-born extended sheets** (bare `τ = −1` along a large surface) are counted `τ` data (item 2). To cross a scale-`k`
coarse plaquette in the bulk they need area `≥ L^{2k}` bare plaquettes at `≥ β_0` each, so their count per cell,
`Σ L^{4k} e^{-4 L^{2k}/g_0²}`, is negligible.

**Status:** paper sketch. It depends on (a) the SO(3) dilution of a sub-block sheet core (F5 in SO(3)), and (b) the
action-to-suppression step inside large-field regions ([V] (1.76) via [16] (71), F6).

## 2. Item 2: the labels' count fails

* **Where labels come from.** In the split blocking `τ_{k+1}(P) = Π_{p ∈ tile(P)} τ_k(p)`, so
  `τ_k = Stokes^k(τ_0)` with `τ_0 = sign tr U_p` at the bare scale. A bare plaquette contributes to `τ_k` iff it lies
  on the scale-`k` 2-skeleton. That is `C(4,2) · L^{2k} = 6 L^{2k}` bare plaquettes per scale-`k` cell.
* **The cheapest flip.** One plaquette `p` at angle `φ` just above `π/2`, made by rotating its four bonds about one
  axis by `± φ/4`. The other 20 plaquettes through those bonds get `φ/4`, so only `p` has `tr < 0`. Cost
  `β[(1 - cos φ) + 20(1 - cos(φ/4))] = 2.525 β = 10.10/g²` at `φ → π/2⁺` (`run_single_flip.log`). This is an upper
  bound; spreading the compensation further only lowers it. The rigorous lower bound is `β = 4/g²` (the plaquette
  itself).
* **The count.** Probability of a flip `≥ e^{-A_1/g_0²}` times a polynomial in `g_0` (Gaussian fluctuations around the
  explicit configuration). With `g_0^{-2} = g_k^{-2} + b k log L` ([I] (0.31), one-loop `b = 2 · 22/(48π²) = 0.0929`
  for SU(2) with `β = 4/g²`), the expected number per scale-`k` cell is
  `≳ 6 e^{-A_1/g_k²} L^{(2 - b A_1) k} · poly`, with `b A_1 ≤ 0.94`. This diverges as `k → ∞` at fixed `g_k`, i.e. as
  the lattice spacing goes to zero at the stopping scale. Convergence would need `A_1 > 2/b ≈ 21.5`. The closed
  bubble on the 1-skeleton (`A = 24`, needs `> 1/b ≈ 10.8`) converges; the single flips are what break it.
* **What it means.** At scales far from the bare lattice the coarse `τ` is the parity of a growing number of UV events
  per tile: noise, not rare labels. The premise of item 2 (labels are rare, carried for free) fails. Whether the noise
  would be harmless is a new question, not routine: it would need a cluster expansion showing that the `τ` parities
  decouple from the SO(3) dynamics, with summable coupling. Changing the counting so that acts are not counted (only
  "full" flips) reintroduces a threshold at the tie, which is where every earlier version broke.
* **Not affected:** item 1 (thick-born flux never enters `τ`).

## 3. Status

* Item 1: closes on paper (sketch), with two named lemmas (F5 in SO(3), F6).
* Item 2: **fails** as specified (label count diverges; `b A_1 ≤ 0.94 < 2`).
* Items 3-5: not done (stopped).
* New files: this note, `single_flip.py`, `run_single_flip.log`. No Lean this round, no build folder used.
