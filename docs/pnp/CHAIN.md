# Uniformity along the chain: Doeblin and the product of coefficients

Private working note, 2026-11-23. Lean files `ProofPhase/Mixing/Doeblin.lean` and `Chain.lean` (new files only; nothing
existing edited). Claim marks as elsewhere: **[Lean]** is proved in this repository, standard axioms only
(`axioms-chain.sh`, `axioms-chain.log`: 32 declarations, `propext`, `Classical.choice`, `Quot.sound`, no `sorry`, no new
axiom, no build warnings). Context: `docs/OPEN-QUESTIONS-DMP.md` section 0 and the last PREP.md entries of
`docs/mass-gap/weak-coupling/PREP.md`.

## In plain words

A box whose conditional law has a floor (every outcome keeps at least a fixed share `eps` of a reference law, whatever the
outside) loses at most the share `1 - eps` of its memory of the outside per step. Run the same step block after block and
the memory decays like `(1 - eps)^n`. All of this is now a theorem for finite boxes. What it does **not** give: a bound
on the *sum* of the influences of several neighbouring channels (section 4).

## 1. Doeblin's bound **[Lean]**

Setting: a Markov kernel from outsides `X` (any type) to a finite set `Y` (box configurations), as a stochastic matrix.
The contraction coefficient (Dobrushin's coefficient of the kernel) is the largest total-variation distance between two
rows; `Contracts K eta` says it is at most `eta`, and `etaCoef_le_iff` shows this equals `etaCoef K <= eta` (`etaCoef` is the
supremum).

* `contracts_of_doeblin`: if `K x y >= eps * nu y` for all `x`, `y`, with `nu` a probability vector, then
  `Contracts K (1 - eps)`. Proof: two rows overlap in mass at least `eps`, and `tv = 1 - overlap` (`dlt_eq_tv` of
  `Classical.lean`).
* `doeblin_sharp`: the bound is sharp. For every `eps` in `[0, 1]` a two-point kernel has the floor `eps * (uniform)` and
  rows at distance exactly `1 - eps`.
* Not formalised: standard Borel spaces (same statement for measures; the finite case carries the argument).

## 2. The homogeneous chain **[Lean]**

* `tv_pushv_le`: a kernel with coefficient `theta` contracts total variation by `theta`:
  `tv (a K) (b K) <= theta * tv a b` for probability vectors `a`, `b`. Built on the maximal coupling of `Classical.lean`:
  the two outputs differ only where the coupled inputs differ, and there they are at distance at most `theta`.
* `contracts_kcomp` (**submultiplicativity**): coefficients `<= eta` and `<= theta` give `<= eta * theta` for the composite.
* `contracts_kchain`: kernels `K_0, ..., K_{n-1}` with coefficients `<= eta_i` compose to `<= prod eta_i`.
* `contracts_kpow`: the same kernel `n` times (the same transfer step at every block) has coefficient `<= eta^n`.
* `tv_pushv_kpow_le`, `tv_pushv_kpow_le_pow`: two different inputs have outputs after `n` blocks at distance at most
  `eta^n * tv a b <= eta^n`. This is the influence across `n` blocks.
* `contracts_kpow_of_doeblin`: with the floor of section 1, `(1 - eps)^n`.

The chain lives on one finite type `X` at every step (the blocks all carry the same kind of configuration). Different
kernels per step are allowed (`kchain`); the homogeneous case (`kpow`) is the one the uniformity argument needs.

## 3. The box bound **[Lean]**

`box_bound`: the box law as a kernel from outsides `O` to box configurations `B`, with density `f o b` relative to a
reference probability vector `rho` (`law o b = f o b * rho b`) and `f o b >= exp (-C)` for all `o`, `b`. Then `law` is a
Markov kernel and `Contracts law (1 - exp (-C))`: the coefficient is at most `1 - e^{-C}` for every pair of outsides.
The hypothesis (the density floor with the constant `C`) is exactly what the weak-coupling argument supplies per box
(PREP.md: the floor `e^{-C beta L^{d-1}}`); this file takes it as given.

## 4. The honest limit

NOTE. Dobrushin's condition needs the **sum** of the influences over the neighbouring channels to be below `1`, not each
channel on its own. With `k` neighbouring channels of coefficients `eta_1, ..., eta_k` the column sum is
`eta_1 + ... + eta_k` (`column_sum_le`: at most `k (1 - e^{-C})` under the per-channel bound). The per-channel bound
`1 - e^{-C}` cannot be improved from the floor alone (`doeblin_sharp`), and:

* `column_sum_ge_one`: for `k >= 2` and `C >= log 2`, `k (1 - e^{-C}) >= 1`. The per-channel Doeblin bound then gives no
  column sum below `1`.
* `column_sum_lt_one_iff`: the sum of the bounds is below `1` exactly when `1 - 1/k < e^{-C}`, i.e. `C < log (k / (k-1))`
  (for `k = 2`: `C < log 2`, about `0.69`).

So the claim "a per-channel bound `1 - e^{-C}` does not make the sum `< 1` once `k >= 2`" holds from `C = log 2` upward and
is false for smaller `C` (a small floor constant does give a sum below `1`). What is needed in addition for larger `C`:
an estimate for the joint kernel of all `k` channels (a floor for the joint box law, not the product of the per-channel
floors), or an influence bound per channel that shrinks with the number of channels. Neither is in these files.

## 5. What is and is not closed

* Closed for finite boxes, **[Lean]**: Doeblin's bound, sharpness, submultiplicativity, `eta^n` along a homogeneous
  chain, the box bound under a density floor.
* Not closed: (a) the floor constant `C` per box is an input here; (b) the sum over several channels (section 4);
  (c) standard Borel kernels and the continuum limit; (d) the link of `eta` to the physical rate per tick (units).

## 6. Files and checks

* `docs/mass-gap/formal/ProofPhase/Mixing/Doeblin.lean` (imports `Classical.lean`), `Chain.lean` (imports `Doeblin.lean`).
* `docs/pnp/axioms-chain.sh` builds both modules, prints the axioms of all 32 declarations and greps the sources for
  `sorry`, `admit`, `native_decide`, `axiom`; output in `docs/pnp/axioms-chain.log`.
