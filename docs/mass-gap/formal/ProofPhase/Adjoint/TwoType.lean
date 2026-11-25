/-
Cycle 2, workstream A (the adjoint half): Dobrushin's theorem with two site types (2026-11-22). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/proof-phase/c2a-adjoint/NOTE.md`, section 2 (the refined condition D′_ref of
workstream 1, `proof-phase/ws1-routeA/NOTE.md` §1.4).
-/

import Attempts.R3.Robust

/-!
# Two site types: every coordinate split into an adjoint part and a centre part

**Setting.** Configurations `ι → S` (coarse links with values in `S`, e.g. SU(2)), a reference probability `ν` on `S`, and
a measurable split `e : S ≃ᵐ S_A × S_Z` of the single-link space with `ν.map e = ν_A ⊗ ν_Z` (for SU(2):
`U ↦ (Ad U, sign)` through a measurable section `SO(3) → SU(2)`, Haar ↦ Haar ⊗ uniform; the existence of such a split is
elementary and not formalised). Gibbs measure `gibbsMeasure ν V` of local potentials `V`.

The **two-type system** has the sites `ι ⊕ ι` (`inl l`: the adjoint part of link `l`, `inr l`: its centre part), all
with values in `S_A × S_Z` and reference law `ν_A ⊗ ν_Z`; the site `inl l` contributes the first component, `inr l` the
second (`split e`). The other component of each site is an independent dummy.

* **`influence_site_sharp`** (any Gibbs system): Dobrushin's coefficient from the **mixed second difference**: if the change
  of the pair factors when `z` moves, *as a function of the value at `i`*, has oscillation `≤ D_{iz}`, then `tanh(D_{iz}/4)`
  is an influence bound. `pairDiff_of_pairOsc`: it is never worse than the oscillation form (`D ≤ 2S`). For the cross
  terms of the two-type system it is much better (ws1's `tanh β_F` for "adjoint part of `m` → centre part of `l`").
* `decay_of_sharpW`: Theorem A (weighted) from the sharp coefficients.
* `map_split`: the two-type reference measure is mapped to `ν^{⊗ι}` by `split e`; `integral_gibbs_split`: the Gibbs
  measure of `V` is the image of the two-type Gibbs measure of `V ∘ split e` (all integrals agree).
* `typeDist`: the link distance plus a **type shift** `κ` (a quasi-metric: triangle inequality, not symmetric); with it the
  weighted condition D′_λ carries the type weights `e^{±λκ}` of a two-type Dobrushin condition.
* **`schur_weights`**, **`twoType_criterion`**: the **block form** of the condition. With column sums `a` (adjoint →
  adjoint), `b'` (adjoint → centre), `b` (centre → adjoint), `c` (centre → centre), all with the weight `e^{λ d}`: if
  `a < 1`, `c < 1` and `b b' < (1 − a)(1 − c)`, there is a type shift making D′_λ hold on the two-type system.
* **`decay_twoType`**, **`decay_twoType_blocks`**: **Dobrushin's theorem with two site types.** Under the block condition,
  covariances of bounded observables of the original links decay: `|Cov(f, g)| ≤ (1 − γ)⁻¹ (2 ∑ v_a) L_g e^{-λ(R − |κ|)}`.

**Claim level.** Standard (Dobrushin 1968/1970 for products of different standard Borel spaces; the block (Schur) form is
the 2×2 case of "spectral radius of the influence matrix < 1"); formalised here by reduction to the one-type theorem of
`Attempts.R3` (padding with independent dummies), plus the measure identity for the split. Group-blind: no Yang–Mills
content. It turns workstream 1's refined condition D′_ref into a machine-checked sufficient condition for decay of the
coarse block observables at one effective theory.
-/

open MeasureTheory Finset Filter Topology OneScale Attempts.R3

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Adjoint

/-! ## The sharp single-site influence bound -/

section Sharp

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {X : Type*} [Fintype X]

/-- The change of the factors through `i` and `z` when `z` moves to `s`. -/
def pairChange (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (i z : ι) (s : S) (τ : ι → S) : ℝ :=
  ∑ x ∈ pairFactors supp i z, (V x τ - V x (Function.update τ z s))

/-- **Mixed second differences.** For `z ≠ i`, the change of the pair factors when `z` moves, as a function of the value
at `i`, has oscillation at most `D i z`. -/
def PairDiff (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (D : ι → ι → ℝ) : Prop :=
  ∀ i z, z ∉ ({i} : Finset ι) → ∀ (τ : ι → S) (s t u : S),
    pairChange supp V i z s (Function.update τ i t) - pairChange supp V i z s (Function.update τ i u) ≤ D i z

/-- The sharp form is never worse than the oscillation form: `PairOsc S ⇒ PairDiff (2S)`. -/
theorem pairDiff_of_pairOsc {supp : X → Finset ι} {V : X → (ι → S) → ℝ} {Sb : ι → ι → ℝ}
    (h : PairOsc supp V Sb) : PairDiff supp V (fun i z => 2 * Sb i z) := by
  intro i z hz τ s t u
  have h1 := h i z hz (Function.update τ i t) s
  have h2 := h i z hz (Function.update τ i u) s
  unfold pairChange
  have := abs_le.1 h1
  have := abs_le.1 h2
  linarith

theorem splice_singleton (i : ι) (σ ξ : ι → S) : splice {i} σ ξ = Function.update σ i (ξ i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [splice]
  · simp [splice, h]

/-- **Influence bound from mixed second differences (single site, every boundary condition).** -/
theorem influence_site_sharp (ν : Measure S) [IsProbabilityMeasure ν] {supp : X → Finset ι} {V : X → (ι → S) → ℝ}
    (hV : Potential supp V) {i z : ι} (hz : z ∉ ({i} : Finset ι)) {Db : ℝ}
    (hD : ∀ (τ : ι → S) (s t u : S),
      pairChange supp V i z s (Function.update τ i t) - pairChange supp V i z s (Function.update τ i u) ≤ Db) :
    IsInfluenceBound {i} (siteSpec ν supp V i) z (Real.tanh (Db / 4)) := by
  intro σ s F L hF hdep hosc
  set π := prodMeasure (ι := ι) ν
  rw [siteSpec_eq_gibbs, siteSpec_eq_gibbs]
  obtain ⟨hL, hDF⟩ := single_osc hdep hosc σ
  obtain ⟨C, hC⟩ := hF.bdd
  obtain ⟨K, hK⟩ := exists_abs_siteLog_le hV i
  set g : (ι → S) → ℝ := fun ξ => pairChange supp V i z s (splice {i} σ ξ)
  have hdiff : ∀ ξ, siteLog supp V i (splice {i} σ ξ) - siteLog supp V i (splice {i} (Function.update σ z s) ξ) =
      g ξ := by
    intro ξ
    rw [splice_update_left hz]
    exact siteLog_sub_update hV i z _ s
  have hg : ∀ ξ ξ', g ξ - g ξ' ≤ Db := by
    intro ξ ξ'
    simp only [g, splice_singleton]
    exact hD σ s (ξ i) (ξ' i)
  have hbdd : BddBelow (Set.range g) := ⟨g σ - Db, by rintro _ ⟨ξ, rfl⟩; linarith [hg σ ξ]⟩
  haveI : Nonempty (ι → S) := ⟨σ⟩
  set c := ⨅ ξ, g ξ
  have hc1 : ∀ ξ, c ≤ g ξ := fun ξ => ciInf_le hbdd ξ
  have hc2 : ∀ ξ, g ξ ≤ c + Db := fun ξ => by
    have : g ξ - Db ≤ c := le_ciInf fun ξ' => by linarith [hg ξ ξ']
    linarith
  have hb : ∀ τ : ι → S, ∀ ξ, |siteLog supp V i (splice {i} τ ξ)| ≤ K := fun τ ξ => hK _
  have h1 := Influence.tv_gibbs_le_tanh π (measurable_siteLog_splice hV i σ)
    (measurable_siteLog_splice hV i (Function.update σ z s)) (hb σ) (hb _) (c := c) (D := Db)
    (fun ξ => by rw [hdiff ξ]; exact ⟨hc1 ξ, hc2 ξ⟩)
  have h2 := Influence.tv_gibbs_le_tanh π (measurable_siteLog_splice hV i (Function.update σ z s))
    (measurable_siteLog_splice hV i σ) (hb _) (hb σ) (c := -c - Db) (D := Db)
    (fun ξ => by
      have e : siteLog supp V i (splice {i} (Function.update σ z s) ξ) - siteLog supp V i (splice {i} σ ξ) = -g ξ := by
        rw [← hdiff ξ]; ring
      rw [e]; constructor <;> linarith [hc1 ξ, hc2 ξ])
  have := abs_integral_gibbs_sub_le π (measurable_siteLog_splice hV i σ)
    (measurable_siteLog_splice hV i (Function.update σ z s)) (hb σ) (hb _) hF.meas hC hL hDF h1 h2
  rwa [mul_comm] at this

/-- **Theorem A (weighted) from the sharp coefficients:** if the mixed second differences `D` satisfy
`∑_{i ≠ z} tanh(D_{iz}/4) e^{λ dist(z, i)} ≤ γ < 1` (D′_λ for `D/2`), covariances decay. -/
theorem decay_of_sharpW (ν : Measure S) [IsProbabilityMeasure ν] [Nonempty ι] {supp : X → Finset ι}
    {V : X → (ι → S) → ℝ} (hV : Potential supp V) {D : ι → ι → ℝ} (hD : PairDiff supp V D)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {lam : ℝ} (hlam : 0 ≤ lam) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hflat : FlatCriterionW dist lam (fun i z => D i z / 2) γ)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A) (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂(gibbsMeasure ν V) - (∫ σ, f σ ∂(gibbsMeasure ν V)) * ∫ σ, g σ ∂(gibbsMeasure ν V)| ≤
      (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  have := isProbabilityMeasure_gibbsMeasure ν hV
  set P := factorSpec ν supp V hV
  have hk : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (Real.tanh ((D j z / 2) / 2)) := by
    intro j z hz
    rw [show D j z / 2 / 2 = D j z / 4 by ring]
    exact influence_site_sharp ν hV hz (hD j z hz)
  have hcov : ∀ x, coverage P.block x = 1 := coverage_singleton
  have h := theoremA_w P (fun j z => Real.tanh ((D j z / 2) / 2)) hk (cmin := 1) (cmax := 1) (b := 1) le_rfl
    (fun x => (hcov x).ge) (fun x => (hcov x).le) (fun j => by simp [P, factorSpec_block])
    dist hd0 htri (D₀ := 0)
    (fun j x hx y hy => by
      simp only [P, factorSpec_block, mem_singleton] at hx hy
      rw [hx, hy, hd0])
    (fun j x => dist x j)
    (fun j x y _ hy => by
      simp only [P, factorSpec_block, mem_singleton] at hy
      rw [hy])
    hlam hγ0 hγ1
    (fun x => by
      rw [hcov x, Nat.cast_one, mul_one]
      exact hflat x)
    hf hg hfA hgS hvf hLg hvg hR
  refine h.trans (le_of_eq ?_)
  simp only [Nat.cast_one, one_mul, sub_zero, one_div]

end Sharp

/-! ## The split of each coordinate into two sites -/

section Split

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S SA SZ : Type*} [MeasurableSpace S] [MeasurableSpace SA]
  [MeasurableSpace SZ]

/-- The link of a two-type site. -/
def base : ι ⊕ ι → ι := Sum.elim id id

/-- **The split:** the adjoint part of link `l` is read from site `inl l`, its centre part from site `inr l`. -/
def split (e : S ≃ᵐ SA × SZ) (τ : ι ⊕ ι → SA × SZ) : ι → S :=
  fun l => e.symm ((τ (Sum.inl l)).1, (τ (Sum.inr l)).2)

theorem measurable_split (e : S ≃ᵐ SA × SZ) : Measurable (split (ι := ι) e) := by
  refine measurable_pi_iff.2 fun l => e.symm.measurable.comp ?_
  exact (measurable_fst.comp (measurable_pi_apply (Sum.inl l))).prodMk
    (measurable_snd.comp (measurable_pi_apply (Sum.inr l)))

theorem split_update_inl (e : S ≃ᵐ SA × SZ) (τ : ι ⊕ ι → SA × SZ) (l : ι) (p : SA × SZ) :
    split e (Function.update τ (Sum.inl l) p) = Function.update (split e τ) l (e.symm (p.1, (τ (Sum.inr l)).2)) := by
  funext m
  by_cases h : m = l
  · subst h; simp [split]
  · simp [split, h, Function.update_of_ne (Sum.inl_injective.ne h)]

theorem split_update_inr (e : S ≃ᵐ SA × SZ) (τ : ι ⊕ ι → SA × SZ) (l : ι) (p : SA × SZ) :
    split e (Function.update τ (Sum.inr l) p) = Function.update (split e τ) l (e.symm ((τ (Sum.inl l)).1, p.2)) := by
  funext m
  by_cases h : m = l
  · subst h; simp [split]
  · simp [split, h, Function.update_of_ne (Sum.inr_injective.ne h)]

variable (ν : Measure S) (νA : Measure SA) (νZ : Measure SZ) [IsProbabilityMeasure ν] [IsProbabilityMeasure νA]
  [IsProbabilityMeasure νZ]

/-- **The split preserves the reference measures:** if `ν.map e = ν_A ⊗ ν_Z`, the two-type product measure is mapped to
`ν^{⊗ι}` by `split e`. -/
theorem map_split (e : S ≃ᵐ SA × SZ) (hν : ν.map e = νA.prod νZ) :
    (Measure.pi fun _ : ι ⊕ ι => νA.prod νZ).map (split e) = Measure.pi fun _ : ι => ν := by
  set P := νA.prod νZ
  set Φ1 := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => SA × SZ)
  set p1 : (ι → SA × SZ) → (ι → SA) := fun x l => (x l).1
  set p2 : (ι → SA × SZ) → (ι → SZ) := fun x l => (x l).2
  set Φ3 := (MeasurableEquiv.arrowProdEquivProdArrow SA SZ ι).symm
  set Φ4 : (ι → SA × SZ) → (ι → S) := fun x l => e.symm (x l)
  have hp1 : Measurable p1 := measurable_pi_iff.2 fun l => measurable_fst.comp (measurable_pi_apply l)
  have hp2 : Measurable p2 := measurable_pi_iff.2 fun l => measurable_snd.comp (measurable_pi_apply l)
  have hΦ4 : Measurable Φ4 := measurable_pi_iff.2 fun l => e.symm.measurable.comp (measurable_pi_apply l)
  have hsplit : split (ι := ι) e = Φ4 ∘ Φ3 ∘ Prod.map p1 p2 ∘ Φ1 := by
    funext τ l; rfl
  have e1 : (Measure.pi fun _ : ι ⊕ ι => P).map Φ1 = (Measure.pi fun _ : ι => P).prod (Measure.pi fun _ : ι => P) :=
    (measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => P)).map_eq
  have eA : (Measure.pi fun _ : ι => P).map p1 = Measure.pi fun _ : ι => νA := by
    rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
    congr 1; funext _
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have eZ : (Measure.pi fun _ : ι => P).map p2 = Measure.pi fun _ : ι => νZ := by
    rw [Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
    congr 1; funext _
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have e2 : ((Measure.pi fun _ : ι => P).prod (Measure.pi fun _ : ι => P)).map (Prod.map p1 p2) =
      (Measure.pi fun _ : ι => νA).prod (Measure.pi fun _ : ι => νZ) := by
    rw [← Measure.map_prod_map _ _ hp1 hp2, eA, eZ]
  have e3 : ((Measure.pi fun _ : ι => νA).prod (Measure.pi fun _ : ι => νZ)).map Φ3 = Measure.pi fun _ : ι => P :=
    (measurePreserving_arrowProdEquivProdArrow SA SZ ι (fun _ => νA) (fun _ => νZ)).symm.map_eq
  have eν : P.map e.symm = ν := by
    rw [← hν, Measure.map_map e.symm.measurable e.measurable]
    simp
  have e4 : (Measure.pi fun _ : ι => P).map Φ4 = Measure.pi fun _ : ι => ν := by
    rw [Measure.pi_map_pi (fun _ => e.symm.measurable.aemeasurable)]
    congr 1; funext _; exact eν
  rw [hsplit, ← Measure.map_map hΦ4 (Φ3.measurable.comp ((hp1.prodMap hp2).comp Φ1.measurable)),
    ← Measure.map_map Φ3.measurable ((hp1.prodMap hp2).comp Φ1.measurable),
    ← Measure.map_map (hp1.prodMap hp2) Φ1.measurable, e1, e2, e3, e4]

theorem integral_split (e : S ≃ᵐ SA × SZ) (hν : ν.map e = νA.prod νZ) {F : (ι → S) → ℝ} (hF : Measurable F) :
    ∫ τ, F (split e τ) ∂(Measure.pi fun _ : ι ⊕ ι => νA.prod νZ) = ∫ σ, F σ ∂(Measure.pi fun _ : ι => ν) := by
  rw [← map_split ν νA νZ e hν, integral_map (measurable_split e).aemeasurable hF.aestronglyMeasurable]

variable {X : Type*} [Fintype X]

/-- The two-type supports: both sites of every link of the factor. -/
def splitSupp (supp : X → Finset ι) (x : X) : Finset (ι ⊕ ι) := (supp x).disjSum (supp x)

theorem potential_split (e : S ≃ᵐ SA × SZ) {supp : X → Finset ι} {V : X → (ι → S) → ℝ} (hV : Potential supp V) :
    Potential (splitSupp supp) (fun x τ => V x (split e τ)) := by
  obtain ⟨K, hK⟩ := hV.bdd
  refine ⟨fun x => (hV.meas x).comp (measurable_split e), ⟨K, fun x τ => hK x _⟩, fun x τ τ' h => ?_⟩
  refine hV.dep x _ _ fun l hl => ?_
  simp only [split]
  rw [h (Sum.inl l) (Finset.inl_mem_disjSum.2 hl), h (Sum.inr l) (Finset.inr_mem_disjSum.2 hl)]

/-- **The Gibbs measure is the image of the two-type Gibbs measure** (as integrals of bounded measurable functions). -/
theorem integral_gibbs_split (e : S ≃ᵐ SA × SZ) (hν : ν.map e = νA.prod νZ) {supp : X → Finset ι}
    {V : X → (ι → S) → ℝ} (hV : Potential supp V) {h : (ι → S) → ℝ} (hh : Measurable h) :
    ∫ τ, h (split e τ) ∂(gibbsMeasure (νA.prod νZ) (fun x τ => V x (split e τ))) =
      ∫ σ, h σ ∂(gibbsMeasure ν V) := by
  have hbm := hV.bm_exp
  have hbm' := (potential_split e hV).bm_exp
  unfold gibbsMeasure
  rw [integral_weightMeasure (ν := νA.prod νZ) hbm' (fun _ => (Real.exp_pos _).le),
    integral_weightMeasure (ν := ν) hbm (fun _ => (Real.exp_pos _).le)]
  have hZ : ∫ τ, Real.exp (totalLog (fun x τ => V x (split e τ)) τ) ∂(prodMeasure (ι := ι ⊕ ι) (νA.prod νZ)) =
      ∫ σ, Real.exp (totalLog V σ) ∂(prodMeasure (ι := ι) ν) :=
    integral_split ν νA νZ e hν hbm.meas
  rw [hZ]
  exact integral_split ν νA νZ e hν
    (F := fun σ => Real.exp (totalLog V σ) / (∫ σ, Real.exp (totalLog V σ) ∂(prodMeasure (ι := ι) ν)) * h σ)
    (by exact (hbm.meas.div_const _).mul hh)

end Split

/-! ## Type weights and the block (Schur) condition -/

section Blocks

variable {ι : Type*}

/-- The type potential: `0` on adjoint sites, `κ` on centre sites. -/
def typeH (κ : ℝ) : ι ⊕ ι → ℝ := Sum.elim (fun _ => 0) (fun _ => κ)

/-- **The two-type distance:** link distance plus the change of the type potential (a quasi-metric). -/
def typeDist (dist : ι → ι → ℝ) (κ : ℝ) (p q : ι ⊕ ι) : ℝ := dist (base p) (base q) + (typeH κ q - typeH κ p)

theorem typeDist_self {dist : ι → ι → ℝ} (hd0 : ∀ x, dist x x = 0) (κ : ℝ) (p : ι ⊕ ι) : typeDist dist κ p p = 0 := by
  simp [typeDist, hd0]

theorem typeDist_triangle {dist : ι → ι → ℝ} (htri : ∀ x y z, dist x z ≤ dist x y + dist y z) (κ : ℝ)
    (p q r : ι ⊕ ι) : typeDist dist κ p r ≤ typeDist dist κ p q + typeDist dist κ q r := by
  unfold typeDist
  linarith [htri (base p) (base q) (base r)]

theorem typeDist_ge {dist : ι → ι → ℝ} (κ : ℝ) (p q : ι ⊕ ι) : dist (base p) (base q) - |κ| ≤ typeDist dist κ p q := by
  unfold typeDist typeH
  rcases p with p | p <;> rcases q with q | q <;> simp <;> linarith [neg_abs_le κ, le_abs_self κ]

/-- **The 2×2 Schur condition gives type weights.** If `a < 1`, `c < 1` and `b b' < (1 − a)(1 − c)` (all `≥ 0`), there is
`r > 0` with `a + r b' < 1` and `b / r + c < 1`. -/
theorem schur_weights {a b b' c : ℝ} (ha : a < 1) (hc : c < 1) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hs : b * b' < (1 - a) * (1 - c)) : ∃ r : ℝ, 0 < r ∧ a + r * b' < 1 ∧ b / r + c < 1 := by
  have h1c : 0 < 1 - c := by linarith
  have h1a : 0 < 1 - a := by linarith
  rcases hb'.lt_or_eq with hb'0 | hb'0
  · refine ⟨(b / (1 - c) + (1 - a) / b') / 2, ?_, ?_, ?_⟩
    · have : 0 < (1 - a) / b' := div_pos h1a hb'0
      have : 0 ≤ b / (1 - c) := div_nonneg hb h1c.le
      linarith
    · have hlt : b / (1 - c) < (1 - a) / b' := by
        rw [div_lt_div_iff₀ h1c hb'0]; linarith
      have : (b / (1 - c) + (1 - a) / b') / 2 < (1 - a) / b' := by linarith
      have := (lt_div_iff₀ hb'0).1 this
      linarith
    · have hlt : b / (1 - c) < (1 - a) / b' := by
        rw [div_lt_div_iff₀ h1c hb'0]; linarith
      have hr : b / (1 - c) < (b / (1 - c) + (1 - a) / b') / 2 := by linarith
      have hrpos : 0 < (b / (1 - c) + (1 - a) / b') / 2 := lt_of_le_of_lt (div_nonneg hb h1c.le) hr
      have : b / ((b / (1 - c) + (1 - a) / b') / 2) < 1 - c := by
        rw [div_lt_iff₀ hrpos]
        have := (div_lt_iff₀ h1c).1 hr
        linarith
      linarith
  · subst hb'0
    refine ⟨b / (1 - c) + 1, by positivity, by linarith, ?_⟩
    have hrpos : 0 < b / (1 - c) + 1 := by positivity
    have : b / (b / (1 - c) + 1) < 1 - c := by
      rw [div_lt_iff₀ hrpos, mul_add, mul_one, mul_div_cancel₀ _ h1c.ne']
      linarith
    linarith

variable [Fintype ι] [DecidableEq ι]

theorem sum_filter_sum_type (P : ι ⊕ ι → Prop) [DecidablePred P] (F : ι ⊕ ι → ℝ) :
    ∑ p ∈ univ.filter P, F p =
      ∑ l ∈ univ.filter (fun l => P (Sum.inl l)), F (Sum.inl l) +
        ∑ l ∈ univ.filter (fun l => P (Sum.inr l)), F (Sum.inr l) := by
  rw [Finset.sum_filter, Fintype.sum_sum_type, Finset.sum_filter, Finset.sum_filter]

/-- **The two-type condition in block form** (`dist` the link distance; `Db` the two-type sharp coefficients): column
sums adjoint → adjoint `≤ a`, adjoint → centre `≤ b'` (same link included), centre → adjoint `≤ b` (same link included),
centre → centre `≤ c`, all weighted with `e^{λ dist}`. With the type shift `κ` (`e^{λκ} = r`) this is D′_λ on the
two-type system with `γ = max(a + r b', b/r + c)`. -/
theorem twoType_criterion {dist : ι → ι → ℝ} {lam κ : ℝ} {Db : ι ⊕ ι → ι ⊕ ι → ℝ} {a b b' c : ℝ}
    (hAA : ∀ m, ∑ l ∈ univ.filter (fun l => l ≠ m),
      Real.tanh (Db (Sum.inl l) (Sum.inl m) / 4) * Real.exp (lam * dist m l) ≤ a)
    (hAZ : ∀ m, ∑ l, Real.tanh (Db (Sum.inr l) (Sum.inl m) / 4) * Real.exp (lam * dist m l) ≤ b')
    (hZA : ∀ m, ∑ l, Real.tanh (Db (Sum.inl l) (Sum.inr m) / 4) * Real.exp (lam * dist m l) ≤ b)
    (hZZ : ∀ m, ∑ l ∈ univ.filter (fun l => l ≠ m),
      Real.tanh (Db (Sum.inr l) (Sum.inr m) / 4) * Real.exp (lam * dist m l) ≤ c) :
    FlatCriterionW (typeDist dist κ) lam (fun p q => Db p q / 2)
      (max (a + Real.exp (lam * κ) * b') (Real.exp (-(lam * κ)) * b + c)) := by
  intro z
  have hq : ∀ p q : ι ⊕ ι, Db p q / 2 / 2 = Db p q / 4 := fun p q => by ring
  rw [sum_filter_sum_type]
  rcases z with m | m
  · -- column of an adjoint site
    have e1 : univ.filter (fun l => Sum.inl m ∉ ({Sum.inl l} : Finset (ι ⊕ ι))) = univ.filter (fun l => l ≠ m) := by
      ext l; simp [eq_comm]
    have e2 : univ.filter (fun l => Sum.inl m ∉ ({Sum.inr l} : Finset (ι ⊕ ι))) = (univ : Finset ι) := by
      ext l; simp
    rw [e1, e2]
    have hs2 : ∑ l, Real.tanh (Db (Sum.inr l) (Sum.inl m) / 2 / 2) *
        Real.exp (lam * typeDist dist κ (Sum.inl m) (Sum.inr l)) =
        Real.exp (lam * κ) * ∑ l, Real.tanh (Db (Sum.inr l) (Sum.inl m) / 4) * Real.exp (lam * dist m l) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [typeDist, typeH, base, Sum.elim_inl, Sum.elim_inr, id, sub_zero, hq]
      rw [mul_add, Real.exp_add]; ring
    have hs1 : ∑ l ∈ univ.filter (fun l => l ≠ m), Real.tanh (Db (Sum.inl l) (Sum.inl m) / 2 / 2) *
        Real.exp (lam * typeDist dist κ (Sum.inl m) (Sum.inl l)) =
        ∑ l ∈ univ.filter (fun l => l ≠ m), Real.tanh (Db (Sum.inl l) (Sum.inl m) / 4) * Real.exp (lam * dist m l) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [typeDist, typeH, base, Sum.elim_inl, id, sub_self, add_zero, hq]
    rw [hs1, hs2]
    exact le_max_of_le_left (add_le_add (hAA m) (mul_le_mul_of_nonneg_left (hAZ m) (Real.exp_pos _).le))
  · -- column of a centre site
    have e1 : univ.filter (fun l => Sum.inr m ∉ ({Sum.inl l} : Finset (ι ⊕ ι))) = (univ : Finset ι) := by
      ext l; simp
    have e2 : univ.filter (fun l => Sum.inr m ∉ ({Sum.inr l} : Finset (ι ⊕ ι))) = univ.filter (fun l => l ≠ m) := by
      ext l; simp [eq_comm]
    rw [e1, e2]
    have hs1 : ∑ l, Real.tanh (Db (Sum.inl l) (Sum.inr m) / 2 / 2) *
        Real.exp (lam * typeDist dist κ (Sum.inr m) (Sum.inl l)) =
        Real.exp (-(lam * κ)) * ∑ l, Real.tanh (Db (Sum.inl l) (Sum.inr m) / 4) * Real.exp (lam * dist m l) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [typeDist, typeH, base, Sum.elim_inl, Sum.elim_inr, id, zero_sub, hq]
      rw [show lam * (dist m l + -κ) = lam * dist m l + -(lam * κ) by ring, Real.exp_add]; ring
    have hs2 : ∑ l ∈ univ.filter (fun l => l ≠ m), Real.tanh (Db (Sum.inr l) (Sum.inr m) / 2 / 2) *
        Real.exp (lam * typeDist dist κ (Sum.inr m) (Sum.inr l)) =
        ∑ l ∈ univ.filter (fun l => l ≠ m), Real.tanh (Db (Sum.inr l) (Sum.inr m) / 4) * Real.exp (lam * dist m l) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [typeDist, typeH, base, Sum.elim_inr, id, sub_self, add_zero, hq]
    rw [hs1, hs2]
    exact le_max_of_le_right (add_le_add (mul_le_mul_of_nonneg_left (hZA m) (Real.exp_pos _).le) (hZZ m))

end Blocks

/-! ## Dobrushin's theorem with two site types -/

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {S SA SZ : Type*} [MeasurableSpace S]
  [MeasurableSpace SA] [MeasurableSpace SZ] {X : Type*} [Fintype X]

/-- **Dobrushin's theorem with two site types** (D′_λ on the two-type system, any type shift `κ`). Covariances of bounded
observables of the original links decay at rate `λ`, with the factor `2` for the two sites of each link and `e^{λ|κ|}`
for the type shift. -/
theorem decay_twoType (e : S ≃ᵐ SA × SZ) (ν : Measure S) (νA : Measure SA) (νZ : Measure SZ) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure νA] [IsProbabilityMeasure νZ] (hν : ν.map e = νA.prod νZ)
    {supp : X → Finset ι} {V : X → (ι → S) → ℝ} (hV : Potential supp V) {Db : ι ⊕ ι → ι ⊕ ι → ℝ}
    (hD : PairDiff (splitSupp supp) (fun x τ => V x (split e τ)) Db)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {lam κ γ : ℝ} (hlam : 0 ≤ lam) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hcrit : FlatCriterionW (typeDist dist κ) lam (fun p q => Db p q / 2) γ)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A) (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂(gibbsMeasure ν V) - (∫ σ, f σ ∂(gibbsMeasure ν V)) * ∫ σ, g σ ∂(gibbsMeasure ν V)| ≤
      (1 - γ)⁻¹ * (2 * ∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * (R - |κ|))) := by
  have hV' := potential_split e hV
  set μ' := gibbsMeasure (νA.prod νZ) (fun x τ => V x (split e τ))
  have i1 := integral_gibbs_split ν νA νZ e hν hV (h := fun σ => f σ * g σ) (by exact hf.meas.mul hg.meas)
  have i2 := integral_gibbs_split ν νA νZ e hν hV (h := f) hf.meas
  have i3 := integral_gibbs_split ν νA νZ e hν hV (h := g) hg.meas
  rw [← i1, ← i2, ← i3]
  -- the observables on the two-type system
  have hf' : BM (fun τ => f (split e τ)) := ⟨hf.meas.comp (measurable_split e), by
    obtain ⟨C, hC⟩ := hf.bdd; exact ⟨C, fun τ => hC _⟩⟩
  have hg' : BM (fun τ => g (split e τ)) := ⟨hg.meas.comp (measurable_split e), by
    obtain ⟨C, hC⟩ := hg.bdd; exact ⟨C, fun τ => hC _⟩⟩
  have hfA' : DepOn (fun τ => f (split e τ)) (A.disjSum A) := fun τ τ' h => hfA _ _ fun l hl => by
    simp only [split]
    rw [h (Sum.inl l) (Finset.inl_mem_disjSum.2 hl), h (Sum.inr l) (Finset.inr_mem_disjSum.2 hl)]
  have hgS' : DepOn (fun τ => g (split e τ)) (Sg.disjSum Sg) := fun τ τ' h => hgS _ _ fun l hl => by
    simp only [split]
    rw [h (Sum.inl l) (Finset.inl_mem_disjSum.2 hl), h (Sum.inr l) (Finset.inr_mem_disjSum.2 hl)]
  have hvf' : OscBound (fun τ => f (split e τ)) (fun p => vf (base p)) := by
    intro τ p s
    rcases p with l | l
    · simp only [split_update_inl, base, Sum.elim_inl, id]; exact hvf _ _ _
    · simp only [split_update_inr, base, Sum.elim_inr, id]; exact hvf _ _ _
  have hvg' : OscBound (fun τ => g (split e τ)) (fun _ => Lg) := by
    intro τ p s
    rcases p with l | l
    · simp only [split_update_inl]; exact hvg _ _ _
    · simp only [split_update_inr]; exact hvg _ _ _
  have hR' : ∀ a ∈ A.disjSum A, ∀ s ∈ Sg.disjSum Sg, R - |κ| ≤ typeDist dist κ a s := by
    intro a ha s hs
    have hba : base a ∈ A := by
      rcases a with a | a <;> simpa [base] using ha
    have hbs : base s ∈ Sg := by
      rcases s with s | s <;> simpa [base] using hs
    linarith [hR _ hba _ hbs, typeDist_ge (dist := dist) κ a s]
  have h := decay_of_sharpW (νA.prod νZ) hV' hD (typeDist dist κ) (typeDist_self hd0 κ) (typeDist_triangle htri κ)
    hlam hγ0 hγ1 hcrit hf' hg' hfA' hgS' hvf' hLg hvg' hR'
  have hsum : ∑ p ∈ A.disjSum A, vf (base p) = 2 * ∑ a ∈ A, vf a := by
    rw [Finset.sum_disjSum]; simp [base]; ring
  rwa [hsum] at h

/-- **Dobrushin's theorem with two site types, block form.** Column sums `a` (adjoint → adjoint), `b'` (adjoint →
centre), `b` (centre → adjoint), `c` (centre → centre) of the sharp coefficients `tanh(D/4)` with weight `e^{λ dist}`;
if `λ > 0`, `a < 1`, `c < 1` and `b b' < (1 − a)(1 − c)`, covariances decay at rate `λ`. -/
theorem decay_twoType_blocks (e : S ≃ᵐ SA × SZ) (ν : Measure S) (νA : Measure SA) (νZ : Measure SZ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure νA] [IsProbabilityMeasure νZ] (hν : ν.map e = νA.prod νZ)
    {supp : X → Finset ι} {V : X → (ι → S) → ℝ} (hV : Potential supp V) {Db : ι ⊕ ι → ι ⊕ ι → ℝ}
    (hD : PairDiff (splitSupp supp) (fun x τ => V x (split e τ)) Db)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {lam : ℝ} (hlam : 0 < lam) {a b b' c : ℝ} (ha : a < 1) (hc : c < 1) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (ha0 : 0 ≤ a) (hs : b * b' < (1 - a) * (1 - c))
    (hAA : ∀ m, ∑ l ∈ univ.filter (fun l => l ≠ m),
      Real.tanh (Db (Sum.inl l) (Sum.inl m) / 4) * Real.exp (lam * dist m l) ≤ a)
    (hAZ : ∀ m, ∑ l, Real.tanh (Db (Sum.inr l) (Sum.inl m) / 4) * Real.exp (lam * dist m l) ≤ b')
    (hZA : ∀ m, ∑ l, Real.tanh (Db (Sum.inl l) (Sum.inr m) / 4) * Real.exp (lam * dist m l) ≤ b)
    (hZZ : ∀ m, ∑ l ∈ univ.filter (fun l => l ≠ m),
      Real.tanh (Db (Sum.inr l) (Sum.inr m) / 4) * Real.exp (lam * dist m l) ≤ c) :
    ∃ γ C : ℝ, 0 ≤ γ ∧ γ < 1 ∧ 0 ≤ C ∧ ∀ {f g : (ι → S) → ℝ}, BM f → BM g → ∀ {A Sg : Finset ι}, DepOn f A →
      DepOn g Sg → ∀ {vf : ι → ℝ}, OscBound f vf → ∀ {Lg : ℝ}, 0 ≤ Lg → OscBound g (fun _ => Lg) →
      ∀ {R : ℝ}, (∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) →
      |∫ σ, f σ * g σ ∂(gibbsMeasure ν V) - (∫ σ, f σ ∂(gibbsMeasure ν V)) * ∫ σ, g σ ∂(gibbsMeasure ν V)| ≤
        C * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  obtain ⟨r, hr, h1, h2⟩ := schur_weights ha hc hb hb' hs
  set κ := Real.log r / lam
  have hκ : Real.exp (lam * κ) = r := by
    simp only [κ]; rw [mul_div_cancel₀ _ hlam.ne', Real.exp_log hr]
  have hκ' : Real.exp (-(lam * κ)) = r⁻¹ := by rw [Real.exp_neg, hκ]
  have hcrit := twoType_criterion (κ := κ) hAA hAZ hZA hZZ
  rw [hκ, hκ', ← div_eq_inv_mul] at hcrit
  set γ := max (a + r * b') (b / r + c)
  have hγ1 : γ < 1 := max_lt h1 h2
  have hγ0 : 0 ≤ γ := le_max_of_le_left (by have := mul_nonneg hr.le hb'; linarith)
  refine ⟨γ, (1 - γ)⁻¹ * 2 * Real.exp (lam * |κ|), hγ0, hγ1, by
    have : 0 < 1 - γ := by linarith
    positivity, ?_⟩
  intro f g hf hg A Sg hfA hgS vf hvf Lg hLg hvg R hR
  have h := decay_twoType e ν νA νZ hν hV hD dist hd0 htri hlam.le hγ0 hγ1 hcrit hf hg hfA hgS hvf hLg hvg hR
  refine h.trans (le_of_eq ?_)
  rw [show -(lam * (R - |κ|)) = lam * |κ| + -(lam * R) by ring, Real.exp_add]
  ring

end Main

end ProofPhase.Adjoint
