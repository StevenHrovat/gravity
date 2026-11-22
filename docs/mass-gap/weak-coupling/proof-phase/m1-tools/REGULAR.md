# R2: does every released region become regular within Balaban's delay? (m1-tools, 2026-11-22)

Brief (coordinator, item 2 of the open list): every released large-field region becomes regular within Balaban's
delay, by dilution or by growth to a deep core. Read for this note: [III] p. 251 (`R`, `p0`), `D-N.md` (the delay),
`OFFCENTRE.md` (R1), `BYPASS.md` 1. Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **False as stated; true for two of the three kinds of irregularity; the third needs new bookkeeping.**
2. **Localised moderate cores: proved** (from R1). `M` contracts by `θ = 0.284` per step (`L = 13`). The core is
   regular after `n_loc = log(8 r0/ε_k)/log(1/θ) ≈ 0.4 log g^{-2}` steps. Balaban's delay is `R_j`, the smallest power
   of `L` above a power of `log g_j^{-2}` ([III] p. 251; the exponent is unreadable in the scan). Equivalently, by
   `D-N.md`, the retuned delay `N ≈ p0(g)/(d log L)` with `p0 = A0 (log g^{-2})^{p}`, `p ≥ 1`. Both exceed `n_loc` for
   small `g`, given exponent `≥ 1`, or `A0 ≥ 2 d log L` in the retuned form.
3. **Smooth extended moderate fields: proved** (scaling plus Stokes). A field smooth on scales above a block has its
   plaquette angles multiplied by about `L²` per step in block units. It reaches the deep threshold `r0` within
   `log(r0/ε)/(2 log L) ≈ 0.25 log g^{-2}/log L` steps, and is then excised and filled (R3).
4. **Moderate-flux sheets: not regular within the delay.** An extended closed sheet carrying a non-central flux `φ`
   with `ε_k < φ < r0` keeps the coarse plaquettes it pierces at about `φ` at every scale. This is Stokes for loops
   around the sheet, and the flux is not central, so the SO(3) layer does not erase it (unlike Z2 sheets, `BYPASS.md`
   1). It is neither diluted (not localised) nor growing (the flux is conserved), so it stays a moderate large-field
   region until the sheet is smaller than a block, about `log_L(size)` steps, and then R1 applies. For sheets larger than
   `L^{R_j}` this exceeds the delay.
   * **Their cost is fine:** action `≥ c p0² A` (area `A` in plaquettes at birth), carrying `≤ C log g^{-2} (MR)² A`
     summed over the shrinking footprint, ratio `≪ 1` by Balaban's win condition.
   * **The missing piece:** Balaban's entropy induction (E8, [V] (1.80)-(1.88)) lets a factor control a domain for at
     most `n0 - j + R_j` steps. Regions alive longer, paid by their own area action, are outside it. Extending E8 to
     such regions is the missing piece.
5. **No general classification is proved.** That every irregular configuration, after excision of its deep part,
   splits into localised cores, conserved-flux sheets and growing parts is plausible: a moderate "gas" adds fluxes
   like a random walk and grows, about `L φ` per step. It is not proved, and R2 as a lemma needs it.
6. **So R2 proves much harder than marked ("open, sketch").** It needs:
   * (a) a decomposition lemma for moderate irregular configurations;
   * (b) an extension of Balaban's entropy induction to long-lived, geometrically shrinking regions paid by their own
     action.
   
   Per the rules I stop here: R6 and later items are not started.

## 1. What is proved

* **Localised cores** (supports in the stars of a radius-2 ball, `|a| ≤ r0`): `M_{k+n} ≤ θ^n M_k` (`OFFCENTRE.md`).
  Plaquettes within `4M` of the background, so regular once `4 θ^n M_k ≤ ε_{k+n}/2`.
* **Smooth extended fields:** for a field whose curvature varies on scales above `L` (fine units), the coarse plaquette
  angle is the sum of the fine plaquette angles over the coarse plaquette, up to `O(curvature²)` (non-abelian Stokes,
  smooth case). That is `L²` times the fine angle. Deep within `⌈log(r0/ε)/(2 log L)⌉` steps.

## 2. The counterexample to "within the delay"

A straight sheet (directions 3, 4) with a constant U(1)_n field of total flux `φ` through each transverse plaquette
column, `ε_k < φ < r0`, of linear size `ℓ` (scale-`k` units, `ℓ ≫ L^{R_k}`):
* every coarse plaquette (in planes 1-2) that the sheet pierces has holonomy `e^{i f φ n·σ}`, with `f` the fraction of
  averaged loops enclosing the pierce point;
* summed over the coarse plaquettes of a plane, the fractions `f` total 1 (flux conservation), and a pierce point well
  inside a coarse plaquette has `f ≈ 1`;
* so the maximal coarse angle stays `≈ φ` for `log_L ℓ` steps.

Its SO(3) image is the rotation by `2φ`, not the identity.

## 3. What would close R2

1. **Decomposition lemma (new):** after excision of deep plaquettes, every moderate configuration of a large-field
   region is, up to gauge, a sum of (i) localised pieces (R1), (ii) pieces whose block images grow by a fixed factor per
   step, and (iii) conserved-flux sheets, with the sizes controlled. Not attempted.
2. **E8 for long-lived regions (new bookkeeping):** a region whose footprint shrinks geometrically and whose own action
   exceeds `p0²` per initial footprint site may be carried for any number of steps. The entropy is summed over the
   shrinking footprint, `Σ_k L^{-2(k-s)}` or `L^{-4(k-s)}`, against its action. This is the same computation as
   `BYPASS.md` 1, but it has to be inserted into Balaban's `κ_j(Z)` induction ([V] (1.80)-(1.88)), which is written for
   lifetimes `≤ R_j`.
