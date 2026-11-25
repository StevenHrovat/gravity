# c7b-centre: confinement from one block scale through the binary centre layer (2026-11-22)

Task: a machine-checked comparison of SU(2) with a Z2 gauge theory (c6c candidate F2). Files: this note, `MACK-PETKOVA.md`
(reading), scripts `build.sh`, `check.sh`, `axioms.sh`, `axioms.log`; Lean in `formal/ProofPhase/Centre/`:
`Ginibre.lean`, `Comparison.lean`, `Z2Wilson.lean`, `Combined.lean`. All four build in `~/formal-c7b` (Lean 4.34, Mathlib v4.34.0);
no `sorry`, no `native_decide`, no new axiom (every declaration depends only on propext, Classical.choice, Quot.sound; `axioms.log`).

## 1. In plain words

1. The repo had no Griffiths/Ginibre inequality. It now has one, from scratch: for Ising-type models with any finite family of
   interactions, `|⟨σ_B⟩_J| ≤ ⟨σ_B⟩_K` whenever `|J_k| ≤ K_k`, couplings of **any sign**. Griffiths I and II and monotonicity in the
   ferromagnetic couplings come out of the same proof (monotonicity needs no derivative).
2. Comparison theorem: if the Wilson loop expectation is a mixture over SO(3)-type backgrounds `v` of Z2 correlations with couplings
   `J(v)`, and `|J(v)| ≤ J̄`, then `|⟨W⟩| ≤ M · ⟨σ_C⟩_{J̄}`. For **finitely many backgrounds** the mixture structure is *proved* for any
   positive joint weight (Walsh expansion of the log). For the continuous SO(3) background it is a **named hypothesis** (`PlaqMixture`).
3. Combined with the repo's strong-coupling Z2 area law (made available by giving the repo's interface a Z2 instance and proving
   that the Z2 Wilson expectation is the Ising correlation): `J̄` small in the repo's range ⇒ area law **in every volume**, with
   constants independent of the volume.
4. Honest size of the result: at the **bare** level (`J̄ = 2β`) the combined bound is *identical* to the repo's direct SU(2)
   strong-coupling theorem. The comparison reproduces it and adds nothing there. It becomes new content only for a **block-scale**
   worst-case coupling `J̄(ℓ)` of a plaquette-form effective action; that `J̄(ℓ)` is small is open (c6c, 6 step 1), and a
   block action with multi-plaquette terms needs a Z2 area law the repo does not have.

## 2. Lean: names and exact statements

Setting for all: sites `ι` (finite, decidable equality), spins `σ : ι → Bool` (`sgn false = 1`, `sgn true = -1`), monomial
`mono σ m = ∏_{i∈m} sgn (σ i)` for a multiset `m` of sites, interaction family `κ` (finite) with supports `supp : κ → Multiset ι`,
`energy supp J σ = ∑_k J_k mono σ (supp k)`, `Zf`, `num`, `corr supp J B = num/Zf`.

**Proved** (Ginibre.lean):
* `gks1 : (∀ k, 0 ≤ c k) → 0 ≤ num supp c B` (Griffiths I).
* `ginibre : (∀ k, |J k| ≤ K k) → corr supp J B ≤ corr supp K B ∧ -corr supp J B ≤ corr supp K B`.
* `abs_corr_le : (∀ k, |J k| ≤ K k) → |corr supp J B| ≤ corr supp K B`; `abs_corr_le_abs : |corr supp J B| ≤ corr supp (|J|) B`.
* `corr_mono : 0 ≤ J ≤ K → corr supp J B ≤ corr supp K B` (monotonicity in couplings, GKS II form).
* `griffiths2 : 0 ≤ c → corr supp c A * corr supp c B ≤ corr supp c (A + B)`; `corr_nonneg`.
Proof idea of `ginibre`: two replicas `σ`, `τ = σρ`; the integrand becomes `mono σ B (1 ± mono ρ B) · exp(∑ σ_k (K_k + J_k ρ_k))`, whose coefficients are ≥ 0, so `gks1` applies for each `ρ`.

**Proved** (Comparison.lean):
* `walsh`, `walsh_inv` (Walsh inversion), `exp_walsh : 0 < ω → ω σ = exp (energy allSupp (walsh (log ∘ ω)) σ)`: every positive weight on the
  cube is a Z2 model with all-subset interactions.
* `comparison_finite [Nonempty V] (ω : V → (ι→Bool) → ℝ) (hω : ∀ v σ, 0 < ω v σ) (w) (M) (hw : ∀ v, |w v| ≤ M) (Jbar : Finset ι → ℝ)
  (hJ : ∀ v A, |walsh (log ω v) A| ≤ Jbar A) C : |jointExpect ω w C| ≤ M * corr allSupp Jbar C`.
  `jointExpect = ∑_{v,σ} ω σ_C w(v) / ∑_{v,σ} ω`. No hypothesis on the decomposition.
* `comparison_integral (μ) [IsProbabilityMeasure μ] (J : Ω → κ → ℝ) (w) (M) (hw) (Jbar) (hJ : ∀ v k, |J v k| ≤ Jbar k) C W
  (hmix : W = ∫ v, w v * corr supp (J v) C ∂μ) : |W| ≤ M * corr supp Jbar C`. The decomposition is the hypothesis `hmix`.

**Proved** (Z2Wilson.lean): `Z2` (group of order 2, discrete topology and Borel structure, `HasGaugeTrace Z2 1`, `HasHaarProbability`,
left-invariant); `haar_singleton` (each point 1/2); `integral_productHaar_Z2` (`∫ F = 2^{-|links|} ∑_σ F(σ)`); `xp_Z2`, `wilsonLoop_Z2`
(plaquette and loop observables are monomials); `wilsonRatio_Z2_eq_corr` (the repo's Z2 Wilson ratio `= corr plaqSupp (fun _ => β) (pathSupp C)`);
`wilson_area_law_Z2` (the repo's `wilson_area_law_explicit` for `G = Z2`, `n = 1`):
for `e^β − 1 ≤ 1/(4 e^{16d+1}(16d+1)^4)`, `|⟨W_{R×T}⟩| ≤ e^{2·4d·2(R+T)} (√(e^{16d+1}(e^β − 1)))^{min(RT, N²−RT)}`.

**Combined** (Combined.lean):
* Named hypothesis `PlaqMixture μ J w C W := (W = ∫ v, w v * corr plaqSupp (J v) (pathSupp C) ∂μ)`. For SU(2) with the Wilson action it asserts:
  `U_ℓ = σ_ℓ V_ℓ` (section of SU(2) → SO(3)) turns the product Haar measure into a uniform `σ` times the section law of `V`; `Re tr U_p = σ_p r_p(V)`,
  `|r_p| ≤ 2`; `μ` is the `V`-marginal reweighted by the Z2 partition function. A disintegration of Haar measure; not in the repo, not proved here.
* `centre_area_law (hM : 0 ≤ M) (hw : |w| ≤ M) (hb0 : 0 ≤ b) (hb : ∀ v p, |J v p| ≤ b) (hsmall : e^b − 1 ≤ 1/(4 e^{16d+1}(16d+1)^4)) … (hmix : PlaqMixture …) :
  |W| ≤ M * (e^{2·4d·2(R+T)} (√(e^{16d+1}(e^b − 1)))^{min(RT, N²−RT)})`, for every `N` (constants independent of `N`).
* `su2_area_law_of_mixture` (bare SU(2), `b = 2β`, `M = 2`) with the repo's integral expression for the SU(2) ratio; `su2_bound_eq`: its right side equals the
  repo's `wilson_area_law_SU2` bound exactly.

## 3. What the combined theorem gives and assumes

Gives: (conditional on `PlaqMixture`) an area law for the Wilson loop in all volumes, from one number, the worst-case plaquette-form centre
coupling `b` at one lattice scale, being in the strong-coupling range of 4D Z2. No cross-volume step, no sign problem (Ginibre takes `|J|`).
Assumes: (i) `PlaqMixture` (the disintegration, true for the Wilson action by the argument above, not formalised; for finitely many
backgrounds `comparison_finite` removes it); (ii) `b` small in the repo's range, which at the bare level is exactly the known SU(2)
strong-coupling region, and at a block scale is c6c's open item; (iii) the effective centre action is of single-plaquette form (otherwise
`comparison_finite` applies with all-subset interactions, but no Z2 area law is available for them). Gives confinement, not the gap.

## 4. Unit tests

Lean (`Combined.lean`, toy model one site / one interaction, `corr = tanh J`, `corr_toy`):
* **Z2 itself / sharpness:** `comparison_sharp` (`|corr J C| = corr J C` for `J ≥ 0`): a one-point mixture with `J = J̄ ≥ 0` attains the bound; the constant and `J̄` cannot be improved. `ginibre` is the Z2 case of the theorem.
* **Mixture:** `toy_mixture_cancels` (±a, equal weights: `W = 0 ≤ tanh |a|`); `toy_abs_corr` (`|tanh a| ≤ tanh |a|`); frustration only lowers the left side, the right side is the worst case.
* **Deconfinement / large J̄:** `toy_vacuous` (`tanh b ≥ 1 − 2e^{−2b}`, `< 1`): the bound tends to 1; `toy_monotone`/`corr_mono`: a larger `J̄` only weakens the conclusion. The 4D statement (Z2 at large coupling has a perimeter law, so the bound is empty in a deconfined direction, e.g. temporal plaquettes) is not a Lean theorem.

Paper (not Lean):
* **Photon, U(1).** The decomposition exists for U(1) too (`U = σV`, `V` in the quotient U(1), a double cover) and the bare bound is `J̄ = β`, the same
  inequality. So the theorem is group-blind as an inequality; it does not need a "±1-only centre layer" to hold, but the quotient is *not stateless*: `V` carries the
  photon, and the Z2 layer's worst-case effective coupling does not become small, because a block π-flux costs the scale-invariant Maxwell action (c6c). So `J̄` stays
  at order β_R at every block scale and nothing is claimed. Correct, and the failure is in the size of `J̄`, not in the theorem.
* **2I.** The decomposition exists with centre Z2 (quotient A5). A block vortex needs a fine holonomy −1 around each meridian; with a discrete group some plaquette per
  meridian is ≠ 1, so the worst case stays ≥ cβ at every thickness: `J̄` not small at weak coupling, no claim. SU(2): a thick vortex spreads the angle (classical cost ~ β π²/d² per fine plaquette), so
  `J̄(ℓ)` can fall with ℓ: continuity enters exactly at the size of `J̄(ℓ)`. This is c6c's estimate (not proved).
* **Z2 both phases:** the statement is the Z2 result itself (comparison with itself). **Mixture / Heller endpoint:** F2 may claim the area law and says nothing about the 0⁺⁺ mass.

## 5. Next step

1. **Measure `J̄(ℓ)`** (c6c, 6 step 1): on stored blocked configurations, the worst-case (sup over sampled SO(3) backgrounds) Walsh coefficients of the conditional log-density of the centre
   variables, plaquette-form and multi-plaquette parts separately, against the 4D Z2 strong-coupling constant `e^b − 1 ≤ 1/(4e^{16d+1}(16d+1)^4)` (very small: b of order 10^{-36} at d = 4, so the
   repo's range is tiny; a better Z2 area-law range or a sharper cluster expansion for multi-plaquette couplings is the bottleneck, not the comparison). Add the 2I control.
2. **Formalise `PlaqMixture`** for SU(2) Wilson (Haar disintegration over the section `SU(2) → SO(3)`), or restrict to a discretised background and use `comparison_finite`.
3. **A Z2 area law for general local positive couplings** (multi-plaquette, convergent expansion): needed before any block action with more than single-plaquette terms can use the comparison.
4. Read Mack–Petkova's full text to confirm the route.
