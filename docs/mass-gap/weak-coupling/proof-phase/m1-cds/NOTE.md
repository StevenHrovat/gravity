# M1 tools, write-out 1 in Lean: the coupling-form Dobrushin-Shlosman theorem

Module: `docs/mass-gap/formal/ProofPhase/OneBox/CouplingDS.lean`, namespace `ProofPhase.OneBox`.
Paper: `../m1-tools/UV-TV.md` section 28 (28.1-28.4). Reviews: `../m1-review/REVIEW-3-FOLLOWUP.md` Follow-up 10,
`../m1-review/REVIEW-2-FOLLOWUP.md` Eleventh follow-up.
Build: `FORMAL_DST=~/formal-cds bash sync-build.sh ProofPhase.OneBox.CouplingDS` (Lean 4.34.0, Mathlib v4.34.0).
Axiom check: `axioms.sh`, output in `axioms.log`.

## 1. What is proved

All of 28.1-28.2, with no hypothesis beyond those of 28.1 except the measurability choices in section 3.

* **Step 1** (the averaged update keeps couplings and supports): `CouplingSpec.isSuppCoupling_T`.
* **Step 2** (per-block estimates): `bind_real_disagree_le_of_notMem` (sites off the block keep their pair),
  `good_block_le` ((I) integrated over `π`), `block_le_weight` (a source block costs at most its weight).
* **Step 3** (one step): `phi_T_le`, `Φ(Tπ) ≤ θ Φ(π) + s/N`, `θ = 1 - (1 - γ) c_min / N`.
* **Step 4** (iteration from `μ ⊗ μ'`, finite iterate, no limit): `phi_iter_le`, `eventually_phi_iter_le`,
  `couplingDS_bound`.
* **Step 5** (consequence for test functions): `abs_integral_sub_le_phi`, `couplingDS_integral_bound`.
* **Coordinator addition (one sequence for all weights):** the iterates `C.iter n = T^n (μ ⊗ μ')` are defined from
  `C` alone, so they do not depend on `v`, `K`, `γ`, `c_min` or the good/source split. `phi_iter_le` gives the bound
  with the explicit rate `θ_W^n` for every admissible weight choice `W` at once, and `exists_iter_forall_le` gives one
  `n` that serves a whole finite family of weight choices up to `ε`.

## 2. Exact signatures

Variables throughout: `{ι S β : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] [Fintype β] [DecidableEq β]`.

```lean
def disagree (x : ι) : Set ((ι → S) × (ι → S)) := {p | p.1 x ≠ p.2 x}
def phi (v : ι → ℝ) (π : Measure ((ι → S) × (ι → S))) : ℝ := ∑ x, v x * π.real (disagree x)
def coverage (B : β → Finset ι) (x : ι) : ℕ := (univ.filter fun b => x ∈ B b).card
def srcWeight (good : Finset β) (B : β → Finset ι) (v : ι → ℝ) : ℝ := ∑ b ∈ univ \ good, ∑ y ∈ B b, v y

structure CouplingSpec (μ μ' : Measure (ι → S)) (β : Type*) where
  Ω₀ : Set (ι → S)
  Ω₀' : Set (ι → S)
  meas₀ : MeasurableSet Ω₀
  meas₀' : MeasurableSet Ω₀'
  full₀ : μ Ω₀ᶜ = 0
  full₀' : μ' Ω₀'ᶜ = 0
  B : β → Finset ι
  q : β → Kernel (ι → S) (ι → S)
  q' : β → Kernel (ι → S) (ι → S)
  q_local : ∀ b, ∀ σ ∈ Ω₀, ∀ x ∉ B b, ∀ᵐ ξ ∂(q b σ), ξ x = σ x
  q'_local : ∀ b, ∀ σ ∈ Ω₀', ∀ x ∉ B b, ∀ᵐ ξ ∂(q' b σ), ξ x = σ x
  q_dlr : ∀ b, μ.bind (q b) = μ
  q'_dlr : ∀ b, μ'.bind (q' b) = μ'
  q_supp : ∀ b, ∀ σ ∈ Ω₀, q b σ Ω₀ᶜ = 0
  q'_supp : ∀ b, ∀ σ ∈ Ω₀', q' b σ Ω₀'ᶜ = 0
  Q : β → Kernel ((ι → S) × (ι → S)) ((ι → S) × (ι → S))
  Q_markov : ∀ b, IsMarkovKernel (Q b)
  Q_fst : ∀ b, ∀ σ ∈ Ω₀, ∀ σ' ∈ Ω₀', (Q b (σ, σ')).map Prod.fst = q b σ
  Q_snd : ∀ b, ∀ σ ∈ Ω₀, ∀ σ' ∈ Ω₀', (Q b (σ, σ')).map Prod.snd = q' b σ'

-- in namespace CouplingSpec, C : CouplingSpec μ μ' β
structure IsSuppCoupling (π : Measure ((ι → S) × (ι → S))) : Prop where
  fst : π.map Prod.fst = μ
  snd : π.map Prod.snd = μ'
  supp : π (C.Ω₀ ×ˢ C.Ω₀')ᶜ = 0
def T (π) : Measure ((ι → S) × (ι → S)) := ((Fintype.card β : ℝ≥0∞)⁻¹) • ∑ b, π.bind (C.Q b)
def iter (n : ℕ) : Measure ((ι → S) × (ι → S)) := (C.T)^[n] (μ.prod μ')

theorem isSuppCoupling_T [Nonempty β] {π} (h : C.IsSuppCoupling π) : C.IsSuppCoupling (C.T π)
theorem isSuppCoupling_iter [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Nonempty β] (n : ℕ) :
    C.IsSuppCoupling (C.iter n)

theorem phi_T_le [MeasurableEq S] [IsProbabilityMeasure μ] [Nonempty β] {π} (h : C.IsSuppCoupling π)
    {good : Finset β} {v : ι → ℝ} {K : β → ι → ℝ} {γ cmin : ℝ}
    (hv : ∀ x, 0 ≤ v x) (hγ : γ ≤ 1) (hc : ∀ x, cmin ≤ coverage C.B x)
    (hI : ∀ b ∈ good, ∀ σ ∈ C.Ω₀, ∀ σ' ∈ C.Ω₀',
      ∑ y ∈ C.B b, v y * (C.Q b (σ, σ')).real (disagree y) ≤
        ∑ z ∈ (C.B b)ᶜ, (disagree z).indicator (fun _ => K b z * v z) (σ, σ'))
    (hK : ∀ z, ∑ b ∈ good.filter (fun b => z ∉ C.B b), K b z ≤ γ * coverage C.B z) :
    phi v (C.T π) ≤ (1 - (1 - γ) * cmin / Fintype.card β) * phi v π + srcWeight good C.B v / Fintype.card β

structure DSWeights where   -- admissible weights for C
  good : Finset β; v : ι → ℝ; K : β → ι → ℝ; γ : ℝ; cmin : ℝ
  v_nonneg : ∀ x, 0 ≤ v x; γ_nonneg : 0 ≤ γ; γ_lt_one : γ < 1; cmin_pos : 0 < cmin
  cmin_le : ∀ x, cmin ≤ coverage C.B x
  influence : (hI above, with these good, v, K)
  column : (hK above, with these good, K, γ)
def DSWeights.bound (W) : ℝ := srcWeight W.good C.B W.v / ((1 - W.γ) * W.cmin)
def DSWeights.θ (W) : ℝ := 1 - (1 - W.γ) * W.cmin / Fintype.card β

theorem phi_iter_le [MeasurableEq S] [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Nonempty β]
    (W : C.DSWeights) (n : ℕ) :
    phi W.v (C.iter n) ≤ W.bound + W.θ ^ n * phi W.v (μ.prod μ')
theorem eventually_phi_iter_le [...same...] (W : C.DSWeights) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, phi W.v (C.iter n) ≤ W.bound + ε
theorem exists_iter_forall_le [...same...] {α : Type*} [Finite α] (W : α → C.DSWeights) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, C.IsSuppCoupling (C.iter n) ∧ ∀ a, phi (W a).v (C.iter n) ≤ (W a).bound + ε
-- also: DSWeights.θ_lt_one [Nonempty β], DSWeights.θ_nonneg [Nonempty ι] (so 0 ≤ θ < 1)

theorem couplingDS_bound [MeasurableEq S] {μ μ' : Measure (ι → S)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] [Nonempty β] (C : CouplingSpec μ μ' β)
    (good : Finset β) (v : ι → ℝ) (K : β → ι → ℝ) (γ cmin : ℝ)
    (hv : ∀ x, 0 ≤ v x) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (hcmin : 0 < cmin) (hc : ∀ x, cmin ≤ coverage C.B x)
    (hI : ...as above...) (hK : ...as above...) {ε : ℝ} (hε : 0 < ε) :
    ∃ π : Measure ((ι → S) × (ι → S)), IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = μ' ∧
      π (C.Ω₀ ×ˢ C.Ω₀')ᶜ = 0 ∧
      ∑ x, v x * π.real {p | p.1 x ≠ p.2 x} ≤ srcWeight good C.B v / ((1 - γ) * cmin) + ε

theorem abs_integral_sub_le_phi [MeasurableEq S] {μ μ'} {π} [IsProbabilityMeasure π]
    (hfst : π.map Prod.fst = μ) (hsnd : π.map Prod.snd = μ') {v : ι → ℝ} (hv : ∀ x, 0 ≤ v x)
    (A : Finset ι) {vmin : ℝ} (hvmin : 0 < vmin) (hvA : ∀ x ∈ A, vmin ≤ v x)
    {F : (ι → S) → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ σ, |F σ| ≤ M)
    (hdep : ∀ σ σ' : ι → S, (∀ x ∈ A, σ x = σ' x) → F σ = F σ') :
    |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ 2 * M * vmin⁻¹ * phi v π

theorem couplingDS_integral_bound [...as couplingDS_bound, without ε...]
    (A : Finset ι) {vmin : ℝ} (hvmin : 0 < vmin) (hvA : ∀ x ∈ A, vmin ≤ v x)
    {F : (ι → S) → ℝ} (hF : Measurable F) {M : ℝ} (hFM : ∀ σ, |F σ| ≤ M)
    (hdep : ∀ σ σ' : ι → S, (∀ x ∈ A, σ x = σ' x) → F σ = F σ') :
    |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ 2 * M * vmin⁻¹ * (srcWeight good C.B v / ((1 - γ) * cmin))
```

`(disagree z).indicator (fun _ => K b z * v z) (σ, σ')` is `1{σ_z ≠ σ'_z} K_b(z) v(z)`; `(C.B b)ᶜ` is `z ∉ B_b`;
`good.filter (fun b => z ∉ C.B b)` is `{b ∈ 𝔅_good : z ∉ B_b}`. `M` plays `‖F‖_∞` and `vmin` plays `min_A v`.

## 3. Simplifying choices (each is a hypothesis or a field, none hidden)

* **One single-site space `S`** for all sites (as in `OneScale`), configurations `ι → S` with the product
  sigma-algebra. Site-dependent spaces are not needed for the application.
* **Measurable diagonal:** `[MeasurableEq S]` (Mathlib class: the diagonal of `S × S` is measurable). Holds for
  standard Borel `S` and for countable `S` with measurable singletons, so for compact groups and finite sets. This is
  REVIEW-3 Follow-up 10's Lean NIT. It is used only to make `{p | p.1 x ≠ p.2 x}` measurable; it is not needed for
  `CouplingSpec`, `T` or the marginal/support statements.
* **Measurable block couplings:** `Q b` is a Mathlib `Kernel`, hence measurable in the pair by definition. Its
  existence (the gluing along in-support hybrids with measurable disintegrations, REVIEW-3's second NIT) is not proved
  here; it is hypothesis (C), i.e. the fields `Q`, `Q_markov`, `Q_fst`, `Q_snd`.
* **(S) in the form used.** Locality is "`q b σ` keeps the coordinates off `B b` almost surely", for `σ ∈ Ω₀`. The
  paper's "`q_b(σ, ·)` depends only on `σ` off `B_b`" is never used in the proof and is not assumed; nor is `q b` asked
  to be Markov (on the supports this follows from (C)). Dropping unused hypotheses makes the theorem stronger.
* **Everything only on the supports.** Locality, support preservation, the marginals of `Q b` and (I) are required
  only at `σ ∈ Ω₀`, `σ' ∈ Ω₀'`. The proof never evaluates a kernel off the supports (`IsSuppCoupling` is carried
  along the iteration).
* **Good/source split** as a `Finset` of good blocks; the source blocks are `univ \ good`. Blocks are indexed by a
  `Fintype β` (a multiset of blocks is a non-injective `B`), `N = Fintype.card β`, `[Nonempty β]`.
* **Constants.** `c_min` is any real with `0 < c_min ≤ c(x)` for all `x`; `0 ≤ γ < 1`; `v ≥ 0` (the paper's
  `v > 0` is only needed on `A`, as `vmin > 0`); the paper's `K_b(z) ≥ 0` is not needed. `‖F‖_∞` is any `M` with
  `|F| ≤ M`. "F depends on the coordinates in `A`" is `hdep`.
* **Conclusion not weakened.** `couplingDS_bound` is the 28.1 conclusion verbatim (plus the support of `π`), and
  `couplingDS_integral_bound` is the 28.1 consequence verbatim. No limit coupling is constructed, as in the paper.

## 4. Axiom check

`axioms.log`: every one of the 37 theorems depends only on `[propext, Classical.choice, Quot.sound]`; the grep for
`sorry`, `native_decide` and axiom declarations finds nothing. The module builds with no warnings.

## 5. What is open

Nothing in 28.1-28.2. Outside the module (instantiation, 28.3), and not attempted here:
* constructing the block couplings `Q b` of H3 and Lemma C as measurable kernels with the stated marginals (gluing
  along hybrids, disintegrations on standard Borel spaces);
* checking (I) and (K) for the UV-TV block family (H3, Lemma C, 22.3), and the reviewers' instantiation rules (every
  block whose two specifications differ is a source block; composite boxes contracted only inside `Λ''_j`;
  truncation events as a case split before the theorem, not as blocks);
* the covariance form for (B), applied to conditioned measures inside the supports (REVIEW-2 Eleventh follow-up).
