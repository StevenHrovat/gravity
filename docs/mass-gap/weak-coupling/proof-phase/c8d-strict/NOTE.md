# c8d-strict: the strict reflection bound Z_tw < Z

Lean module: `docs/mass-gap/formal/ProofPhase/Flip/Strict.lean` (namespace `ProofPhase.Flip`, imports only
`ProofPhase.Flip.Bound`). Built with Lean 4 + Mathlib in the project's toolchain; every one of the 91 theorems depends
only on `propext`, `Classical.choice`, `Quot.sound` (`axioms.log`); no `sorry`, no `native_decide`, no new axiom.

## Result in plain words

`Bound.lean` showed that the 't Hooft twist never increases the partition function, `Z_tw <= Z`, and that
`Z - Z_tw` is a reflection-positivity norm. This workstream proves that the inequality is **strict for SU(2) at every
non-zero coupling**: for every `beta != 0`, every spatial size `L >= 1`, every even time extent `T`, every spatial
background twist `P` and every plane position `c`,

    Z_tw < Z,   so   Z_{e=1} = (Z - Z_tw)/2 > 0   and   0 <= p < 1/2.

At `beta = 0` the weight is constant and `Z_tw = Z` exactly, so `beta != 0` cannot be dropped: the statement is sharp.
The target asked for `beta > 0` first and `beta != 0` if cheap; the method below gives `beta != 0` at no extra cost,
because it uses only the symmetry of the transfer matrix, not its positivity.

## What is proved (Lean names)

1. **General strict lemma, boundary-moment form** (`cZtw_lt_cZ_of_moment`). Any chain weight with `K > 0`, any slice
   twist, any even `T`: if one bounded measurable function `eta(a_0, a_{T/2})` of the two fixed slices has
   `Int (A o sigma - A) * eta * B != 0`, then `Z_tw < Z`. Proof: Cauchy-Schwarz for the reflection form
   (`Positivity.cs_of_rp`), since that moment is `<A o sigma - A, eta>` and `<A o sigma - A, A o sigma - A> = 2(Z - Z_tw)`.
   The moment condition is the concrete form of "the half-chain state is not sigma-invariant on a set of positive
   measure".

2. **General strict lemma, one-step form** (`cZtw_lt_cZ_of_step`). Define the one-step transfer operator on one slice,
   `(K f)(a) = Int K(a,b,c) V(c) f(c) db dc` (`kop`), and `<f, h>_V = Int f h V` (`vip`). If
   `<phi, K chi>_V != 0` for one bounded measurable `phi` that is odd under the twist and one bounded measurable `chi`,
   then `Z_tw < Z` **for every even `T`**. The hypothesis does not mention `T`. Steps:
   - `half_chain`: `Int A * phi(a_0) chi(a_{T/2}) * B = <phi, K^{T/2} chi>_V` (integrate out one time step at a time:
     `integral_step`, `chain_aux`; new product-measure tools `integral_mix` (resampling a set of coordinates) and
     `measurePreserving_restrictInj` (marginals)).
   - `moment_odd`: for odd `phi` the boundary moment of item 1 equals `-2 <phi, K^{T/2} chi>_V`.
   - `vip_kop`: `K` is symmetric for `<.,.>_V` (from `K(c, b^-1, a) = K(a, b, c)`).
   - `stepVanish_descend`, `stepVanish_one`: if `K^{j+2}` kills the odd sector then so does `K^{j+1}`, because
     `||K^{j+1} phi||^2 = <phi, K^{j+2} K^j phi>`; hence `K^{T/2}` killing it forces `K` killing it.
   So `Z_tw = Z` would contradict the one-step hypothesis.

3. **SU(2) instance** (`su2_Ztw_lt_Z`, `su2_Ze1_pos`, `su2_flipProb_lt_half`). The one-step hypothesis is discharged
   with `phi = chi = Re tr P(a) / V(a)`, where `P` is the Polyakov line through the origin winding once around the first
   spatial axis (odd under the twist, it crosses the plane `x^1 = c` once):
   - the gauge change `c_e = b(x)^-1 u_e a_e b(x+e)` (`gaugeSub`) turns the step weight into `prod_e exp(beta Re tr u_e)`
     and the line into `Re tr(prod_k u_k a_k)` (telescoping, `polyObs_gaugeSub`);
   - Schur's lemma for SU(2), `Int exp(beta Re tr v) Re tr(v M) dv = lambda(beta) Re tr M` (`schur_SU2`, from
     conjugation by `diag(i,-i)` and `[[0,1],[-1,0]]` and the reality of SU(2) traces), integrates the line link by
     link (`lineInt`);
   - result `<phi, K phi>_V = lambda(beta)^L * kappa * Int (Re tr P)^2` (`su2_vip_polyRatio`) with `kappa > 0` (integral
     of the off-line plaquette factors), `Int (Re tr P)^2 > 0` (continuous, equal to 4 at the identity, Haar measure
     charges open sets) and `lambda(beta) != 0` for `beta != 0` (`schurC_ne_zero`: `Int Re tr v dv = 0` by `v -> -v`, so
     `beta lambda(beta) = 1/2 Int (exp(beta t) - 1) beta t dv > 0`).

## Exact headline statements

```lean
theorem cZtw_lt_cZ_of_moment (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G)) (hinv : ∀ e, Function.Involutive (g e))
    (hV : ∀ a, w.V (sliceMap g a) = w.V a) {η : (E → G) × (E → G) → ℝ} (mη : Measurable η) (bη : IsBdd η)
    (hη : ∫ U, (cA w (flip0 g U) - cA w U) * bdry η U * cB w U ∂(cHaar G E S T) ≠ 0) :
    cZtw (T := T) w g < cZ (T := T) w

theorem cZtw_lt_cZ_of_step (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G)) (hinv : ∀ e, Function.Involutive (g e))
    (hV : ∀ a, w.V (sliceMap g a) = w.V a) {φ χ : (E → G) → ℝ} (hφ : BM φ) (hχ : BM χ) (hodd : OddUnder g φ)
    (hne : vip w φ (kop w χ) ≠ 0) : cZtw (T := T) w g < cZ (T := T) w

theorem su2_Ztw_lt_Z (L : ℕ) [NeZero L] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L)
    {T : ℕ} [NeZero T] (hT : Even T) : su2Ztw L β P c T < su2Z L β P T

theorem su2_Ze1_pos (L : ℕ) [NeZero L] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L)
    {T : ℕ} [NeZero T] (hT : Even T) : 0 < su2Z L β P T - su2Ztw L β P c T

theorem su2_flipProb_lt_half (L : ℕ) [NeZero L] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L))
    (c : ZMod L) {T : ℕ} [NeZero T] (hT : Even T) :
    0 ≤ su2FlipProb L β P c T ∧ su2FlipProb L β P c T < 1 / 2
```

`su2Z`, `su2Ztw`, `su2FlipProb` are the existing definitions of `Bound.lean` (unchanged); `bdry η U = η(a_0, a_{T/2})`,
`BM f` = measurable and bounded, `OddUnder g φ` = `φ(g·a) = -φ(a)`.

## Claim level

- Substantive and sharp in `beta` for the real SU(2) Wilson measure on `Z/TZ x (Z/LZ)^3` with any spatial twist.
- Strict at each fixed finite lattice only. Nothing is said about the size of `Z - Z_tw`: no lower bound uniform in the
  volume, no bound on the flux free energy, hence no confinement or mass-gap content (`p < 1/2` strictly, but `p` may
  still tend to `1/2` or to `0` as the lattice grows).
- Items 1 and 2 are model-blind (any chain weight over any group with an inversion-invariant Haar probability). The
  SU(2)-specific input of item 3 is Schur's lemma for the 2x2 defining representation, the reality of SU(2) traces and
  the sign of `lambda(beta)`; the same argument should work for U(1), Z2 or SU(N) with their own Schur lemma (not
  formalised).
- As in `Bound.lean`, the bridge from the chain to `ProofPhase.RouteB.twistZ` on `(Z/NZ)^4` is not formalised.

## Open

Nothing open for the stated target. Possible follow-ups: the same for other groups (needs their Schur constant), and a
quantitative version (a lower bound on `Z_{e=1}/Z`) which this argument does not give.

## Files and how to rebuild

- `setup.sh`: one-time build folder `~/formal-c8d` in WSL distro `ym-replay` (copies `~/formal/.lake`).
- `build.sh`: `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8d-strict/build.sh ProofPhase.Flip.Strict`
- `axioms.sh`: `#print axioms` on all 91 theorems of `Strict.lean` and a grep for `sorry`/`native_decide`/`axiom`;
  output in `axioms.log`.
- The build folder `~/formal-c8d` was deleted at the end; run `setup.sh` again before `build.sh`.
