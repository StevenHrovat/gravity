# The closing rule: only closed Z2 sheets feed the coarse bit (m1-tools, 2026-11-22)

Brief (coordinator; owner's reading, `../../PREP.md`, "How an act is composed"): `BYPASS.md` found that closed skeleton
bubbles converge but open single flips (acts) do not. Close every open piece of the Z2 sheet by a minimal filling of its
monopole boundary, with a fixed tie-break, and let only the closed remainder feed the mod-2 Stokes sum (an RG decoder,
as for the toric code). Checks, stopping at the first failure:
1. the definition (measurable, deterministic, local?);
2. the count of closed and open structures in physical units;
3. the release of the absorbed acts into the SO(3) layer;
4. lattice covariance and reflection positivity;
5. if all pass, the remaining bypass items and `M1-PLAN.md`.

Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **Check 1 passes.** The rule is "replace the Z2 layer `τ` (plaquettes) by the nearest closed one". In exact terms:
   `σ = argmin { |τ + σ'| : dσ' = 0 }`, with filling `c = τ + σ` and `dc = dτ`, so `c` is a minimal filling of the
   monopole boundary. Ties go first to the smaller remainder `|σ|` ("absorb on a tie"), then to a fixed order. It is a
   deterministic function of finitely many signs `τ_p = sign tr U_p` (measurable; `tr = 0` has measure zero), so law
   preservation holds (`Exact.lean`). It is applied once, at the bare scale: Stokes sums of closed layers stay closed.
   **It is not strictly local.** Minimal fillings can join nearby monopole loops, but only when the joining tube is
   cheaper than separate discs, i.e. within about a loop's own diameter. A clustered version (fill each cluster of
   loops within its own hull) is local per cluster and agrees with the global rule when clusters are far apart (sketch).
   A lone act (one plaquette past the equator) has the unique minimal filling `c = δ_p`: it is absorbed, remainder 0.
2. **Check 2 passes for the global rule.** In any component the remainder `σ ≠ 0` is chosen over `σ = 0` only if
   `|c| < |τ|`, so the real flips number `|τ| > |σ|/2`. Each real flip costs at least `β = 4/g²`, rigorously (the
   plaquette's own action), up to `O(1)^{|τ|}` normalisation constants that do not grow with the scale. A closed
   remainder feeds a coarse bit only through the coarse **1-skeleton**; the open 2-skeleton route of `BYPASS.md` is
   gone. The smallest closed remainder (6 plaquettes around one bond) needs at least 4 real flips, so `A ≥ 16`. The
   count per scale-`k` cell is `≲ d e^{-16/g_k²} L^{(1 - 16 b) k}`, with `16 b = 1.49 > 1`. It converges, and still
   with the adverse tie-break (`A ≥ 12`, `12 b = 1.11 > 1`). Larger remainders (area `a`, at least `a/2` real flips)
   converge faster. Open structures (monopole loops) never feed a coarse bit. They are bare-scale SO(3) large fields,
   as dense in physical units as Balaban's own regions, and are released like them (check 3). They need not converge
   in physical units and do not.
3. **Check 3 passes at sketch level.** An absorbed act leaves no trace in `τ`. Its SO(3) part (a plaquette at the cut)
   is a bare-scale large field. Integrated, it gives a gauge-invariant local function of the regular surrounding SO(3)
   field, analytic there because the cut sits inside the integrated variables, not in the background. Its
   field-dependence starts at second order in the curvature, because `so(3) ≅ su(2)` has no invariant vector: a
   dimension-4 term, summable over scales (`F1-REPAIR.md` 2). It relies on the same unproved pieces as before: the
   SO(3) off-centre dilution (F5), the filling and the fibre mass near the SO(3) cut (F4, E7.J by excision), and
   [16] (71) (F6).
4. **Check 4 fails, and this is where I stop.** Reflection positivity of the blocked law (link RP on block faces,
   `rp_map`) needs every coarse variable on one side of a reflection plane to be a function of fine variables on that
   side, the crossing variables in product form, and the map commuting with the reflection.
   * **The global decoder is not half-local.** The filling near a coarse plaquette on the left depends on monopole
     loops reaching across the plane, so the coarse `τ` on the left depends on the fine field on the right. Residual
     ties between mirror-image fillings have no reflection-symmetric deterministic resolution; a randomised symmetric
     tie-break would cure covariance, but not half-locality.
   * **The half-local variant fails the count.** Decode per block, letting sheets end on block faces. Then single flips
     straddling a block face (both halves of their monopole boundary lie on the face) are no longer absorbed. They reach
     a coarse bit wherever a tile meets a face: about `L^k` positions per scale-`k` cell. Their cost is still at most
     `A_1 = 10.1/g²` (`single_flip.py`), so the count is `≈ L^{(1 - b A_1) k}` with `b A_1 ≤ 0.94 < 1`: it diverges,
     slowly but without bound.
   * **Deeper:** `τ_p = sign tr U_p` on a plaquette crossing a link-reflection plane is not of the product form
     `f · θf` that link RP needs. So the Z2 layer of ROUTE-B was itself not RP-compatible on crossing plaquettes. My
     remark in `ROUTE-B.md` (iv), "the tile product splits into a half and its mirror", was too quick.
   
   Site-reflection planes through block centres do not help: tiles lie in coarse cell faces, so a decoder that is
   half-local there keeps open pieces on the whole 2-skeleton, which is worse.

## 1. Check 1: definition

* **Objects:** `τ ∈ C²(Λ; Z2)`, `τ_p = 1` iff `tr U_p < 0`; monopole set `η = dτ ∈ C³`; on the dual lattice, `η` is a
  union of closed loops.
* **Rule:** `σ(τ) = argmin_{σ' ∈ Z²} |τ + σ'|`, where `Z²` are the closed 2-cochains, so `σ` lies in the class of
  `τ`'s closure. Tie-break: (i) minimal `|τ + σ'|`; (ii) minimal `|σ'|`; (iii) a fixed total order of `Z²`.
* **Coarse bit:** `τ_1 = Stokes(σ)`, then `τ_{k+1} = Stokes(τ_k)`. Closedness is preserved: `dτ_1(C)` sums `dσ` over
  the fine cubes in `C`, which is 0.
* **Measurability:** a finite minimisation over a finite set, composed with sign functions; the `tr = 0` locus has
  Haar measure zero.
* **Lone act:** `τ = δ_p`. The fillings of `dδ_p` (the four cubes containing `p`) are `δ_p + (closed)`; the smallest
  non-zero closed cochain through `p` has 6 plaquettes, so the next filling has weight `≥ 5`. Hence `c = δ_p` uniquely
  and `σ = 0`.
* **Locality (sketch):** joining two monopole loops by a tube costs about perimeter times distance, against about
  `diameter²` for separate discs. So joins happen only within about a loop's diameter. Clusters are the connected
  components of the loops thickened by their own diameters. Filling per cluster equals the global minimum when cluster
  hulls are separated by more than their diameters squared. Not proved.

## 2. Check 2: counting

* **Closed remainders → coarse bits.** For closed `σ`, `Σ_{tile(P)} σ = Σ_{∂P}` of any primitive (`σ = dz` locally).
  So a small closed remainder flips the coarse bit iff its interior meets the coarse boundary loop, i.e. lies on the
  coarse 1-skeleton (`d L^k` bare bonds per scale-`k` cell).
* **Rigorous cost:** a remainder `σ ≠ 0` with `|σ| = a` needs `|τ| ≥ ⌊a/2⌋ + 1` real flips (absorb on a tie);
  `a ≥ 6`, so at least 4. Each flip costs `≥ β_0 = 4/g_0²`. With the running coupling
  `g_0^{-2} = g_k^{-2} + b k log L`, `b = 0.0929` ([I] (0.31), one loop), the count per cell is
  `Σ_{a ≥ 6} C^a a³ d L^k e^{-4(⌊a/2⌋ + 1)/g_0²} ≲ e^{-16/g_k²} L^{(1 - 16 b) k}` with `16 b = 1.49` for `a = 6`;
  the `a`-sum converges for small `g_k`. The adverse tie-break (`|τ| ≥ a/2`): `12 b = 1.11`. Both `> 1`: **converges**.
  The normalisation `O(1)^{|τ|}` is the standard weak-coupling bound, cited rather than proved here.
* **Bulk-crossing closed sheets** need area `≥ L^{2k}`: negligible.
* **Open structures** (monopole loops of length `ℓ`): each bounds `τ`-area `≥ ℓ/4`, so the cost is `≥ ℓ/g_0²` and the
  count per bare site is `≤ Σ_ℓ 7^ℓ e^{-ℓ/g_0²}` (dense in physical units, like Balaban's large-field regions). They
  are absorbed: they never reach a coarse bit.

## 3. Check 3: the absorbed acts (sketch)

As in section 0.3. The cut is in the integrated variables, not in the background. The released function's gradient at
a flat surrounding field vanishes (no invariant vector in `so(3)`), so its field dependence is of dimension 4 and the
sum over scales converges after vacuum subtraction ([III] (2.30)-(2.33)).

## 4. Check 4: symmetry and positivity — fails

* **Lattice covariance:** exact except on residual ties (step (iii) of the tie-break); a randomised uniform choice
  among residual ties restores covariance in distribution.
* **Reflection positivity:** the bare measure is link and site RP. The blocked law inherits RP (`rp_map`) only if the
  block map is half-local and reflection-covariant, with crossing variables in product form. All three fail:
  * the global decoder is not half-local (loops crossing the plane);
  * `τ_p` on a plaquette crossing a link plane is not of product form;
  * the half-local per-block decoder keeps face-straddling single flips, whose count `L^{(1 - b A_1) k}` diverges.
* **Is there a reflection-symmetric, half-local decoder that still absorbs face-straddling flips?** Not with `τ`
  defined from the crossing plaquette: the decision needs `τ_p`, which mixes both halves. I see no repair inside
  route (b).

## 5. What the owner and coordinator have to decide

* **Does M1 need RP of the blocked laws?** The bare measure is RP whatever the blocking. If the main series uses RP
  only for the bare measure (transfer matrix, Hilbert space) and uses M1's laws only through bounds and expectations,
  then the global decoder (checks 1-3 pass) may be enough, and check 4 is not needed. If the hand-over at `K` needs an
  RP block law (as `TWIST.md` aimed for), the closing rule fails as specified.
* Items 5 (bypass 3-5, `M1-PLAN.md`) are not done.

New files: this note only. No Lean this round, no build folder used.

## 6. Decision (coordinator, 2026-11-22)

Reflection positivity of the bare measure is enough (`LimitRP`; the block-law inputs are decay and transfer
statements; the one-box strong-coupling route uses no reflection positivity). **The closing rule is kept with the
global decoder, and it is not reflection positive**: the blocked laws of M1 carry no RP claim. Checks 1-3 stand at the
levels stated; check 4's failure is recorded and no longer blocks. Follow-up: `HANDOVER.md`, `M1-PLAN.md` 0.
