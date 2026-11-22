# Route (b): the SO(3) × Z2 split, blocking the Z2 flux by mod-2 Stokes (m1-tools, 2026-11-22)

Brief: the owner chose route (b) of `F1-REPAIR.md` in a concrete form (`../../PREP.md`, last entry, "The preserved bit
lives on the boundary"). Split SU(2) into a smooth adjoint SO(3) layer and a Z2 layer on plaquettes; block SO(3) with
Balaban's average and Z2 by exact mod-2 summation over the tile of each coarse plaquette. Checks in order:
(i) do the persistent cores cancel or survive; (ii) the coupling constraint; (iii) Balaban's estimates for the SO(3)
part with a Z2 background; (iv) law preservation and reflection positivity. Stop at the first failing check. Script:
`route_b_cores.py` (log `run_route_b.log`). Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **The rewriting is exact and local** (section 1). With `τ_p = sign tr U_p` (a function of the SU(2) plaquette) and
   the adjoint field `Ad U_b`, the SU(2) Wilson model is an SO(3) field plus a Z2 plaquette layer. Their coupling is
   `exp((β/2) τ_p |tr U_p|)` per plaquette, and the constraint is local: for every 3-cube, the product of `τ` over its
   faces equals the cube's Z2 monopole sign `η_c` of the SO(3) field. This is the form of Mack-Petkova and Tomboulis.
2. **(i) The cores of `Vortex.lean` do not cancel; they survive mod-2 Stokes exactly, and correctly.** The exact
   central core (−1 on the star bonds in directions ±3, ±4 at a block centre) has a **flat** SO(3) part, and its Z2
   layer is `τ = dz`, a tiny closed bubble around the star. The coarse flux of a tile equals `z` along the coarse
   boundary, and that boundary runs through the −1 bond. So the coarse `τ` is −1 on all 16 mixed coarse plaquettes
   at `y` (numerical check: all 16, with the coarse SO(3) field exactly flat). This is not an averaging tie; the
   straight coarse Wilson loop really is −1. Such a bubble survives exactly as long as its bond lies on the coarse
   skeleton. With `A ≥ 24` per bubble (six plaquettes, each at least `β = 4/g²`), the count over skeleton positions,
   `Σ_j L^{(1 - bA)j}`, converges. So **as Z2 data** these cores are harmless.
3. **(ii) The constraint is local and introduces no tie.** Mod-2 Stokes gives, exactly, coarse `dτ` = the number of
   fine monopole cubes inside the coarse cube, mod 2. That is Gauss's law, counted, not averaged. The coarse pair is no
   longer the split of a coarse SU(2) field: coarse `η(V)` and coarse `dτ` can differ. That is allowed (new state
   space, law preserved), but monopoles mark plaquettes at `tr U_p ≈ 0`, which is the SO(3) cut (see 4).
4. **(iii) fails, and this is where I stop.** On a plaquette with `τ_p = −1` the coupling is `exp(-(β/2)|tr U_p|)`. It
   is **largest at the SO(3) cut** (rotation by `π`, `tr U_p = 0`) and **smallest at flat SO(3)**. So:
   * around a thin sheet, flat SO(3) is the minimum of the conditional weight, i.e. a maximum of the action: Balaban's
     flat-background expansion has wrong-sign quadratic terms there;
   * the typical `τ = −1` plaquette of the SU(2) measure sits just past the equator, at `tr ≈ 0⁻` (weight `e^{-β}`, not
     the `e^{-2β}` of a −1 plaquette), i.e. at the SO(3) cut.

   The cost of a Z2 defect does not sit in the Z2 layer: it is shared with an SO(3) large field at the SO(3) cut
   (rotation by `π`, `π_1(SO(3)) = Z2`). This is the same ambiguity the SU(2) average had at −1, moved to the adjoint
   layer. It is intrinsic: a thin −1 plaquette is a maximum of the Wilson action, and no rewriting of the same model
   turns it into a minimum. The cheapest way to carry Z2 flux is a thick vortex, and at the scale of its thickness it
   lives in the SO(3) field near rotation `π`, not in `τ`.
5. **Partly good news for the SO(3) layer.** `Vortex.lean` needs a central element, and SO(3) has none. The SO(3)
   analogue of the core (rotation by `π` on the star bonds ±3, ±4) persists only with the conjugation-covariant
   convention `log := 0` at the cut, which is a measure-zero tie. Off the tie it **dilutes in one step**: coarse SO(3)
   rotation 0.031-0.039 for `δ = 0.6 … 0.02` (`d = 4`, `L = 3`, `run_route_b.log`; the hand calculation agrees: the two
   coarse star bonds get `0.494 θ` and `0.506 θ`). So in the SO(3) layer, cores near the cut behave like the non-centre
   cores of `F1-REPAIR.md` 3 and could be released. But each such core comes with an SO(3) large field at the cut,
   handled by Balaban's machinery with the cut problems (E7.J, filling) of F4, not small-field.
6. **What route (b) achieves, then:** it removes the central persistence (the exact −1 cores become counted Z2 data
   with flat SO(3)). It does not make Z2 defects cheap in the SO(3) layer: wherever flux actually sits at the
   lattice scale, the SO(3) field is at its cut. Physical sheets that cross coarse plaquettes persist (they must, they
   are real flux), and around them the coarse SO(3) field is again not small-field (the sheet relaxes to thick).
   Persistent physical flux is therefore carried as a large-field region, which is the blocker of `F1-REPAIR.md` 4 in
   a new place. Whether that region is cheap enough depends again on a small-field theory around a thick-vortex
   background, i.e. the same missing ingredient.

## 1. The rewriting (exact; derived here, matching Mack-Petkova and Tomboulis as recalled, papers not re-read)

Write each SU(2) bond as `U_b = z_b Û_b`, with `Û_b` a fixed lift of the SO(3) class `Ad U_b` and `z_b ∈ Z2`. Then
`∫ dU F = ∫ d[Ad U] 2^{-|bonds|} Σ_z F`. The Wilson weight is `Π_p exp((β/2) z(∂p) tr Û_p)`. Set
`τ_p = z(∂p) sign tr Û_p = sign tr U_p`. It is independent of the lift. In every 3-cube each bond lies in two faces,
so `Π_{p ∈ ∂c} τ_p = Π_{p ∈ ∂c} sign tr Û_p =: η_c(Ad U)`, the Z2 monopole sign of the SO(3) field (lift-independent).
Conversely, every `τ` with `dτ = η` comes from some `z` (on the torus, up to the global twist sectors). Hence

`Z_SU(2) = Σ_{τ: dτ = η(Ad U)} ∫ d[Ad U] Π_p exp((β/2) τ_p |tr U_p|)` (up to the twist sectors and a constant),

where `|tr U_p|` depends only on the SO(3) plaquette. Both layers are deterministic, measurable, gauge-invariant
(`τ`), resp. gauge-covariant (`Ad U`), functions of the SU(2) field. The tie `tr U_p = 0` has measure zero.

## 2. The checks

| check | result | evidence |
|---|---|---|
| (i) persistent cores | survive, as exact Z2 data with flat SO(3); only at skeleton positions; count converges (`bA ≈ 2.2 > 1`) | Stokes: coarse `τ_P = z(∂P)`; `route_b_cores.py`: 16/16 coarse `τ = −1`, coarse SO(3) rotation 0 |
| (ii) constraint | local, counted (coarse `dτ` = fine monopoles mod 2 per coarse cube); no tie in the Z2 layer; monopoles sit at the SO(3) cut | mod-2 Gauss on the coarse cube |
| (iii) SO(3) with Z2 background | **fails**: on `τ = −1` plaquettes flat SO(3) is a maximum of the action; typical `τ = −1` plaquettes are at the SO(3) cut | the coupling `exp(-(β/2)|tr U_p|)`; weight `e^{-β}` at `tr = 0⁻` vs `e^{-2β}` at `−1` |
| (iv) law, RP | not reached (stopped at (iii)); law preservation holds for any measurable blocking (`Exact.lean`); `τ` is reflection invariant, and the tile product splits into a half and its mirror for coarse plaquettes crossing a plane, so `rp_map` should apply, not checked | — |

## 3. Interaction with the release route and F2-F6

* **Release (`F1-REPAIR.md` 3):** carries over to the SO(3) layer. Cores near the SO(3) cut dilute off-tie
  (numerics above) and need no record; the exact central cores become Z2 data. The counting part of F1 stays repaired.
* **F2 (Bianchi halo):** reappears as the mod-2 Bianchi identity. A `τ = −1` plaquette whose flux does not close forces
  monopole cubes next to it, i.e. SO(3) plaquettes at the cut. Same halo, now in SO(3).
* **F3 (P2′), F6 (P4):** not needed in the split (nothing frozen; large fields pay Balaban's own factor).
* **F4 (filling), F5 (off-centre dilution):** still needed, now for SO(3) fields near rotation `π`, where the
  logarithm is discontinuous; F4 is harder there, not easier.

## 4. What blocks, and what would unblock

* **Blocks:** the cost of Z2 flux cannot be localised in the Z2 layer with the SO(3) layer small-field, because a thin
  −1 plaquette maximises the action. The flux's minimal-action carrier is a thick vortex, which at its own scale is an
  SO(3) large field at the cut. Persistent physical flux is therefore a carried large-field region, as in
  `F1-REPAIR.md` 4.
* **Would unblock (same as before):** a small-field theory around a thick-vortex (twisted-sector) background, with an
  `O(1)` per-step cost, and the rate condition. Route (b) does contribute something to that: the twist sector of a
  coarse plaquette is a counted, local Z2 datum (coarse `τ`, or the 't Hooft twist), which is exactly the label such a
  theory would condition on. So route (b) supplies the bookkeeping for the twisted sectors, but not the estimates.
* **Nothing built.** The script and its log are the only new files besides this note.
