/-
Round 3, attempt 1 (torus robustness): Gibbs measures with local factors, their single-site specification, and
Dobrushin's condition from flat factors (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/r3-robust/NOTE.md`, sections 1 to 3.
-/

import OneScale.SingleLink
import OneScale.Effective.Robust

/-!
# Flat local factors give a boundary-uniform contraction (Dobrushin), and the condition is open

**Setting.** A finite index set `ι` (the coarse cells or coarse links of an effective theory at scale `L₁`), a
single-coordinate space `S` (the block variables) with a probability measure `ν`, and a finite family of **factors**
`x ∈ X` with supports `supp x ⊆ ι` and log-potentials `V x : (ι → S) → ℝ` that depend only on `supp x`
(`Potential`). The effective measure is `gibbsMeasure ν V = Z⁻¹ exp(∑_x V x) ν^{⊗ι}`. Every factor is
`ψ_x = exp(V x)`, and the round-2 soft-swap criterion S′ (`r2-coupling/NOTE.md` §3.4) is stated with
`ψ_min/ψ_max = e^{-osc(V x)}`.

**Contents.**
* `siteSpec`, `factorSpec`: the single-site specification (conditional law of one coordinate given the rest), a
  `BlockSpec` for `gibbsMeasure` with blocks `{i}` (DLR from `OneScale.productBlockSpec`).
* `siteSpec_eq_gibbs`: it is the Gibbs measure `Influence.gibbs π (siteLog ∘ splice)` of the TV lemma.
* **`influence_site`**: for `z ≠ i`, if the factors through both `i` and `z` change their summed log-potential by at most
  `S_{iz}` when `z` moves, then `tanh(S_{iz}/2)` is an H-form influence bound of `z` on `i`, **for every boundary
  condition**. Only the factors meeting both sites enter.
* **`specDist_site`**: if two potentials differ at the site `i` by at most `ε` in summed sup norm, their single-site
  specifications are within `SpecDist ≤ tanh(ε/2)`, uniformly in the boundary condition. Only the factors at `i`
  enter: this is **local**, not extensive in the volume (the answer to D's warning, NOTE §2).
* `siteSpec_isLocal`: the single-site specification depends on the outside only through the factor neighbourhood.
* `FlatCriterion` (the criterion **D′**): `∑_{i ≠ z} tanh(S_{iz}/2) ≤ γ`; `gds_of_flat`: D′ is GDS for single sites.
  `FlatCriterionW`: the weighted version `∑_{i ≠ z} tanh(S_{iz}/2) e^{λ dist(z, i)} ≤ γ` for quasi-local factors.
* `pairOsc_of_osc`, **`flat_of_count`**, `tanh_half_le_one_sub_ratio_sq`: the S′ form implies D′: if every factor has
  oscillation `≤ o₀` and every site has at most `M` (site, factor) pairs, `M (1 - (ψ_min/ψ_max)²) < 1` gives D′; per
  factor D′ is sharper (`tanh(o/2) ≤ 1 - e^{-2o}`). For the plaquette action in `d = 4`, `M = 6(d − 1) = 18` against
  S′'s `4(2d − 3) = 20`, and D′ reproduces `OneScale.SingleLink.gds_single` (`18 tanh(nβ) < 1`).

**Standard, new.** Dobrushin's uniqueness condition and its single-site influence bound for Gibbs measures are
classical (Dobrushin 1968, 1970; Simon's and Georgii's books). New here: the observation that the soft-swap criterion
S′ of round 2 (B) is a pointwise flatness condition and therefore already gives the boundary-uniform condition GDS, so
no torus-only robustness lemma is needed for it (NOTE §1), and the local (volume-free) form of the H1 distance.
-/

open MeasureTheory Finset Filter Topology OneScale Influence

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.R3

section Factors

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {X : Type*} [Fintype X]

/-! ## Factors -/

/-- The factors whose support contains the site `i`. -/
def factorsAt (supp : X → Finset ι) (i : ι) : Finset X := univ.filter fun x => i ∈ supp x

/-- The factors whose support contains both `i` and `z`. -/
def pairFactors (supp : X → Finset ι) (i z : ι) : Finset X := univ.filter fun x => i ∈ supp x ∧ z ∈ supp x

/-- The factor neighbourhood of `i`: all sites sharing a factor with `i` (including `i` if it lies in a factor). -/
def nbhd (supp : X → Finset ι) (i : ι) : Finset ι := (factorsAt supp i).biUnion supp

/-- The log-weight of the factors at `i`. -/
def siteLog (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (i : ι) (σ : ι → S) : ℝ :=
  ∑ x ∈ factorsAt supp i, V x σ

/-- The log-weight of the factors not at `i`. -/
def restLog (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (i : ι) (σ : ι → S) : ℝ :=
  ∑ x ∈ univ.filter (fun x => i ∉ supp x), V x σ

/-- The total log-weight `∑_x V x`. -/
def totalLog (V : X → (ι → S) → ℝ) (σ : ι → S) : ℝ := ∑ x, V x σ

/-- **A local potential.** Every `V x` is measurable, depends only on `supp x`, and the family is bounded. -/
structure Potential (supp : X → Finset ι) (V : X → (ι → S) → ℝ) : Prop where
  meas : ∀ x, Measurable (V x)
  bdd : ∃ K, ∀ x σ, |V x σ| ≤ K
  dep : ∀ x, DepOn (V x) (supp x)

theorem totalLog_eq (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (i : ι) (σ : ι → S) :
    totalLog V σ = siteLog supp V i σ + restLog supp V i σ :=
  (sum_filter_add_sum_filter_not univ (fun x => i ∈ supp x) _).symm

theorem abs_sum_le_card {s : Finset X} {V : X → (ι → S) → ℝ} {K : ℝ} (hK : ∀ x σ, |V x σ| ≤ K) (σ : ι → S) :
    |∑ x ∈ s, V x σ| ≤ s.card * K := by
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ x ∈ s, |V x σ| ≤ ∑ _x ∈ s, K := sum_le_sum fun x _ => hK x σ
    _ = s.card * K := by rw [sum_const, nsmul_eq_mul]

variable {supp : X → Finset ι} {V : X → (ι → S) → ℝ}

theorem Potential.measurable_sum (hV : Potential supp V) (s : Finset X) :
    Measurable (fun σ => ∑ x ∈ s, V x σ) :=
  Finset.measurable_sum s fun x _ => hV.meas x

theorem Potential.localWeight (hV : Potential supp V) (s : Finset X) :
    LocalWeight (fun σ => Real.exp (∑ x ∈ s, V x σ)) := by
  obtain ⟨K, hK⟩ := hV.bdd
  refine ⟨(hV.measurable_sum s).exp, ⟨Real.exp (-(s.card * K)), Real.exp_pos _, fun σ => ?_⟩,
    ⟨Real.exp (s.card * K), fun σ => ?_⟩⟩
  · exact Real.exp_le_exp.2 (neg_le_of_abs_le (abs_sum_le_card hK σ))
  · exact Real.exp_le_exp.2 (le_of_abs_le (abs_sum_le_card hK σ))

theorem Potential.bm_exp (hV : Potential supp V) : BM (fun σ => Real.exp (totalLog V σ)) := by
  obtain ⟨K, hK⟩ := hV.bdd
  refine ⟨(hV.measurable_sum univ).exp, ⟨Real.exp ((univ : Finset X).card * K), fun σ => ?_⟩⟩
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (le_of_abs_le (abs_sum_le_card hK σ))

/-- `siteLog τ - siteLog (τ with z moved)` only involves the factors through both `i` and `z`. -/
theorem siteLog_sub_update (hV : Potential supp V) (i z : ι) (τ : ι → S) (s : S) :
    siteLog supp V i τ - siteLog supp V i (Function.update τ z s) =
      ∑ x ∈ pairFactors supp i z, (V x τ - V x (Function.update τ z s)) := by
  unfold siteLog
  rw [← sum_sub_distrib, ← sum_filter_add_sum_filter_not (factorsAt supp i) (fun x => z ∈ supp x)]
  have h0 : ∑ x ∈ (factorsAt supp i).filter (fun x => ¬ z ∈ supp x),
      (V x τ - V x (Function.update τ z s)) = 0 :=
    sum_eq_zero fun x hx => by rw [(hV.dep x).update_eq (mem_filter.1 hx).2, sub_self]
  rw [h0, add_zero]
  unfold pairFactors factorsAt
  rw [filter_filter]

/-! ## The measure and its single-site specification -/

variable (ν : Measure S) [IsProbabilityMeasure ν]

/-- The effective measure `Z⁻¹ exp(∑_x V x) ν^{⊗ι}`. -/
def gibbsMeasure (V : X → (ι → S) → ℝ) : Measure (ι → S) :=
  weightMeasure ν (fun σ => Real.exp (totalLog V σ))

/-- The local weight of the site `i`. -/
def siteWeight (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (i : ι) (σ : ι → S) : ℝ :=
  Real.exp (siteLog supp V i σ)

/-- The single-site specification: the conditional law of the coordinate `i` given the others. -/
def siteSpec (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (i : ι) : (ι → S) → Measure (ι → S) :=
  locSpec ν {i} (siteWeight supp V i)

theorem isProbabilityMeasure_gibbsMeasure (hV : Potential supp V) :
    IsProbabilityMeasure (gibbsMeasure ν V) := by
  have hbm := hV.bm_exp
  obtain ⟨K, hK⟩ := hV.bdd
  refine isProbabilityMeasure_weightMeasure hbm (fun σ => (Real.exp_pos _).le) ?_
  have h := integral_mono (integrable_const (Real.exp (-((univ : Finset X).card * K))))
    (hbm.integrable (prodMeasure (ι := ι) ν))
    (fun σ => Real.exp_le_exp.2 (neg_le_of_abs_le (abs_sum_le_card (s := univ) hK σ)))
  simp only [integral_const, probReal_univ, one_smul] at h
  exact (Real.exp_pos _).trans_le h

/-- **The single-site block specification of the effective measure** (blocks `{i}`). -/
def factorSpec (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (hV : Potential supp V) :
    BlockSpec (gibbsMeasure ν V) ι :=
  productBlockSpec (ν := ν) (fun σ => Real.exp (totalLog V σ)) (fun i => ({i} : Finset ι)) (siteWeight supp V)
    (fun i σ => Real.exp (restLog supp V i σ)) (fun i => hV.localWeight (factorsAt supp i))
    (fun i σ ξ => by
      congr 1
      refine sum_congr rfl fun x hx => hV.dep x _ _ fun j hj => ?_
      have hx' : i ∉ supp x := (mem_filter.1 hx).2
      have hji : j ∉ ({i} : Finset ι) := by
        rw [mem_singleton]; rintro rfl; exact hx' hj
      exact splice_of_not_mem hji σ ξ)
    (fun i σ => by rw [totalLog_eq supp V i σ, Real.exp_add]; rfl) hV.bm_exp (fun σ => (Real.exp_pos _).le)

theorem factorSpec_block (hV : Potential supp V) (i : ι) : (factorSpec ν supp V hV).block i = {i} := rfl

theorem factorSpec_spec (hV : Potential supp V) (i : ι) :
    (factorSpec ν supp V hV).spec i = siteSpec ν supp V i := rfl

/-- **The single-site specification is the Gibbs measure of the TV lemma.** -/
theorem siteSpec_eq_gibbs (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (i : ι) (σ : ι → S) :
    siteSpec ν supp V i σ =
      gibbs (prodMeasure (ι := ι) ν) (fun ξ => siteLog supp V i (splice {i} σ ξ)) := rfl

theorem measurable_siteLog_splice (hV : Potential supp V) (i : ι) (τ : ι → S) :
    Measurable (fun ξ => siteLog supp V i (splice {i} τ ξ)) :=
  Finset.measurable_sum _ fun x _ => (hV.meas x).comp (measurable_splice_right {i} τ)

theorem exists_abs_siteLog_le (hV : Potential supp V) (i : ι) :
    ∃ K, ∀ τ : ι → S, |siteLog supp V i τ| ≤ K := by
  obtain ⟨K, hK⟩ := hV.bdd
  exact ⟨_, fun τ => abs_sum_le_card hK τ⟩

/-- For `F` depending only on `i` with oscillation `≤ L` there: `L ≥ 0` and `F x - F y ≤ L`. -/
theorem single_osc {i : ι} {F : (ι → S) → ℝ} {L : ℝ} (hdep : DepOn F {i})
    (hosc : ∀ ξ y t, y ∈ ({i} : Finset ι) → |F ξ - F (Function.update ξ y t)| ≤ L) (σ : ι → S) :
    0 ≤ L ∧ ∀ x y, F x - F y ≤ L := by
  refine ⟨?_, fun x y => ?_⟩
  · have := hosc σ i (σ i) (mem_singleton_self i)
    rw [Function.update_eq_self, sub_self, abs_zero] at this
    exact this
  · have : F y = F (Function.update x i (y i)) := by
      apply hdep
      intro j hj
      rw [mem_singleton] at hj
      subst hj
      simp
    rw [this]
    exact (le_abs_self _).trans (hosc x i (y i) (mem_singleton_self i))

/-- **Influence bound from flat factors (single site, H form, every boundary condition).** For `z ≠ i`: if moving `z`
changes the summed log-potential of the factors through both `i` and `z` by at most `S_{iz}` (in absolute value, at
every configuration), then `tanh(S_{iz}/2)` bounds the influence of `z` on the conditional law of `i`. -/
theorem influence_site (hV : Potential supp V) {i z : ι} (hz : z ∉ ({i} : Finset ι)) {Sb : ℝ}
    (hS : ∀ (τ : ι → S) (s : S), |∑ x ∈ pairFactors supp i z, (V x τ - V x (Function.update τ z s))| ≤ Sb) :
    IsInfluenceBound {i} (siteSpec ν supp V i) z (Real.tanh (Sb / 2)) := by
  intro σ s F L hF hdep hosc
  set π := prodMeasure (ι := ι) ν
  rw [siteSpec_eq_gibbs, siteSpec_eq_gibbs]
  obtain ⟨hL, hD⟩ := single_osc hdep hosc σ
  obtain ⟨C, hC⟩ := hF.bdd
  obtain ⟨K, hK⟩ := exists_abs_siteLog_le hV i
  have hdiff : ∀ ξ, siteLog supp V i (splice {i} σ ξ) - siteLog supp V i (splice {i} (Function.update σ z s) ξ) =
      ∑ x ∈ pairFactors supp i z, (V x (splice {i} σ ξ) - V x (Function.update (splice {i} σ ξ) z s)) := by
    intro ξ
    rw [splice_update_left hz]
    exact siteLog_sub_update hV i z _ s
  have hb : ∀ τ : ι → S, ∀ ξ, |siteLog supp V i (splice {i} τ ξ)| ≤ K := fun τ ξ => hK _
  have h1 := tv_gibbs_le_tanh π (measurable_siteLog_splice hV i σ)
    (measurable_siteLog_splice hV i (Function.update σ z s)) (hb σ) (hb _) (c := -Sb) (D := 2 * Sb)
    (fun ξ => by
      have hξ := hS (splice {i} σ ξ) s
      rw [← hdiff ξ] at hξ
      obtain ⟨h₁, h₂⟩ := abs_le.1 hξ
      constructor <;> linarith)
  have h2 := tv_gibbs_le_tanh π (measurable_siteLog_splice hV i (Function.update σ z s))
    (measurable_siteLog_splice hV i σ) (hb _) (hb σ) (c := -Sb) (D := 2 * Sb)
    (fun ξ => by
      have hξ := hS (splice {i} σ ξ) s
      rw [← hdiff ξ] at hξ
      obtain ⟨h₁, h₂⟩ := abs_le.1 hξ
      constructor <;> linarith)
  have := abs_integral_gibbs_sub_le π (measurable_siteLog_splice hV i σ)
    (measurable_siteLog_splice hV i (Function.update σ z s)) (hb σ) (hb _) hF.meas hC hL hD h1 h2
  rwa [show 2 * Sb / 4 = Sb / 2 by ring, mul_comm] at this

/-- **Local closeness of potentials gives closeness of the single-site specifications**, uniformly in the boundary
condition: if `|siteLog V i - siteLog V' i| ≤ ε` everywhere, then `SpecDist {i} ≤ tanh(ε/2)`. -/
theorem specDist_site {V' : X → (ι → S) → ℝ} (hV : Potential supp V) (hV' : Potential supp V') (i : ι) {ε : ℝ}
    (hε : ∀ τ, |siteLog supp V i τ - siteLog supp V' i τ| ≤ ε) :
    Effective.SpecDist {i} (siteSpec ν supp V i) (siteSpec ν supp V' i) (Real.tanh (ε / 2)) := by
  intro σ F L hF hdep hosc
  set π := prodMeasure (ι := ι) ν
  rw [siteSpec_eq_gibbs, siteSpec_eq_gibbs]
  obtain ⟨hL, hD⟩ := single_osc hdep hosc σ
  obtain ⟨C, hC⟩ := hF.bdd
  obtain ⟨K, hK⟩ := exists_abs_siteLog_le hV i
  obtain ⟨K', hK'⟩ := exists_abs_siteLog_le hV' i
  have h1 := tv_gibbs_le_tanh π (measurable_siteLog_splice hV i σ) (measurable_siteLog_splice hV' i σ)
    (fun ξ => hK _) (fun ξ => hK' _) (c := -ε) (D := 2 * ε)
    (fun ξ => by obtain ⟨h₁, h₂⟩ := abs_le.1 (hε (splice {i} σ ξ)); constructor <;> linarith)
  have h2 := tv_gibbs_le_tanh π (measurable_siteLog_splice hV' i σ) (measurable_siteLog_splice hV i σ)
    (fun ξ => hK' _) (fun ξ => hK _) (c := -ε) (D := 2 * ε)
    (fun ξ => by obtain ⟨h₁, h₂⟩ := abs_le.1 (hε (splice {i} σ ξ)); constructor <;> linarith)
  have := abs_integral_gibbs_sub_le π (measurable_siteLog_splice hV i σ) (measurable_siteLog_splice hV' i σ)
    (fun ξ => hK _) (fun ξ => hK' _) hF.meas hC hL hD h1 h2
  rwa [show 2 * ε / 4 = ε / 2 by ring, mul_comm] at this

/-- **Locality.** The single-site specification depends on the outside only through the factor neighbourhood. -/
theorem siteSpec_isLocal (hV : Potential supp V) (i : ι) :
    Effective.IsLocal (nbhd supp i) (siteSpec ν supp V i) := by
  intro σ σ' h
  have hw : ∀ ξ, siteWeight supp V i (splice {i} σ ξ) = siteWeight supp V i (splice {i} σ' ξ) := by
    intro ξ
    unfold siteWeight siteLog
    congr 1
    refine sum_congr rfl fun x hx => hV.dep x _ _ fun j hj => ?_
    by_cases hji : j ∈ ({i} : Finset ι)
    · rw [splice_of_mem hji, splice_of_mem hji]
    · rw [splice_of_not_mem hji, splice_of_not_mem hji]
      exact h j (mem_biUnion.2 ⟨x, hx, hj⟩)
  unfold siteSpec locSpec locZ
  simp_rw [hw]

end Factors

/-! ## The criterion D′ -/

section Criterion

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {X : Type*} [Fintype X]

theorem coverage_singleton (z : ι) : coverage (fun i : ι => ({i} : Finset ι)) z = 1 := by
  unfold coverage
  rw [card_eq_one]
  exact ⟨z, by ext e; simp [eq_comm]⟩

/-- `S` bounds the pair oscillations of `V`: moving `z` changes the summed log-potential of the factors through `i`
and `z` by at most `S i z`. -/
def PairOsc (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (Sb : ι → ι → ℝ) : Prop :=
  ∀ i z, z ∉ ({i} : Finset ι) → ∀ (τ : ι → S) (s : S),
    |∑ x ∈ pairFactors supp i z, (V x τ - V x (Function.update τ z s))| ≤ Sb i z

/-- **The criterion D′** (Dobrushin's condition for flat factors, column form): `∑_{i ≠ z} tanh(S_{iz}/2) ≤ γ`. -/
def FlatCriterion (Sb : ι → ι → ℝ) (γ : ℝ) : Prop :=
  ∀ z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), Real.tanh (Sb i z / 2) ≤ γ

/-- **The weighted criterion D′_λ** (for quasi-local factors): `∑_{i ≠ z} tanh(S_{iz}/2) e^{λ dist(z, i)} ≤ γ`. -/
def FlatCriterionW (dist : ι → ι → ℝ) (lam : ℝ) (Sb : ι → ι → ℝ) (γ : ℝ) : Prop :=
  ∀ z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), Real.tanh (Sb i z / 2) * Real.exp (lam * dist z i) ≤ γ

/-- D′ is GDS for single-site blocks with the coefficients `tanh(S_{iz}/2)`. -/
theorem gds_of_flat {Sb : ι → ι → ℝ} {γ : ℝ} (h : FlatCriterion Sb γ) :
    GDS (fun i : ι => ({i} : Finset ι)) (fun i z => Real.tanh (Sb i z / 2)) γ := by
  intro z
  rw [coverage_singleton, Nat.cast_one, mul_one]
  exact h z

/-- Per-factor oscillation bounds give pair-oscillation bounds: `S_{iz} = ∑_{x ∋ i, z} osc(V x)`. -/
theorem pairOsc_of_osc {supp : X → Finset ι} {V : X → (ι → S) → ℝ} {o : X → ℝ}
    (ho : ∀ x σ σ', V x σ - V x σ' ≤ o x) :
    PairOsc supp V (fun i z => ∑ x ∈ pairFactors supp i z, o x) := by
  intro i z _ τ s
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => abs_le.2 ⟨?_, ho x _ _⟩)
  have := ho x (Function.update τ z s) τ
  linarith

theorem tanh_le_tanh {a b : ℝ} (h : a ≤ b) : Real.tanh a ≤ Real.tanh b := by
  rw [Influence.tanh_eq_exp, Influence.tanh_eq_exp]
  have ha := Real.exp_pos (2 * a)
  have hb := Real.exp_pos (2 * b)
  have hab : Real.exp (2 * a) ≤ Real.exp (2 * b) := Real.exp_le_exp.2 (by linarith)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `tanh x ≤ 2x` for `x ≥ 0` (from `tanh(C/2) ≤ 1 - e^{-C}` and `1 - e^{-C} ≤ C`). -/
theorem tanh_le_two_mul {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ 2 * x := by
  have h1 := Influence.tanh_half_le_lgt (C := 2 * x) (by linarith)
  rw [show 2 * x / 2 = x by ring] at h1
  have h2 := Real.add_one_le_exp (-(2 * x))
  linarith

/-- Per factor, D′ is sharper than S′: `tanh(o/2) ≤ 1 - (ψ_min/ψ_max)²` with `ψ_min/ψ_max = e^{-o}`. -/
theorem tanh_half_le_one_sub_ratio_sq {o : ℝ} (ho : 0 ≤ o) : Real.tanh (o / 2) ≤ 1 - Real.exp (-o) ^ 2 := by
  have h1 := Influence.tanh_half_le_lgt ho
  have h2 : Real.exp (-o) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h3 := Real.exp_pos (-o)
  nlinarith

/-- **S′ form implies D′.** If every factor has oscillation `o x ≤ o₀` (`o₀ ≥ 0`) and, for every `z`, the number of
(site, factor) pairs `∑_{i ≠ z} #{x ∋ i, z}` is at most `M`, then `M tanh(o₀/2) ≤ γ` gives D′ for
`S_{iz} = ∑_{x ∋ i, z} o x`. With `tanh_half_le_one_sub_ratio_sq`, `M (1 - (ψ_min/ψ_max)²) ≤ γ` suffices. -/
theorem flat_of_count {supp : X → Finset ι} {o : X → ℝ} {o₀ : ℝ} (ho₀ : 0 ≤ o₀)
    (hoo : ∀ x, o x ≤ o₀) {M : ℝ}
    (hM : ∀ z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), ((pairFactors supp i z).card : ℝ) ≤ M)
    {γ : ℝ} (hγ : M * Real.tanh (o₀ / 2) ≤ γ) :
    FlatCriterion (fun i z => ∑ x ∈ pairFactors supp i z, o x) γ := by
  intro z
  have ht0 : 0 ≤ Real.tanh (o₀ / 2) := OneScale.SingleLink.tanh_nonneg (by linarith)
  have hterm : ∀ i, Real.tanh ((∑ x ∈ pairFactors supp i z, o x) / 2) ≤
      ((pairFactors supp i z).card : ℝ) * Real.tanh (o₀ / 2) := by
    intro i
    have hs : (∑ x ∈ pairFactors supp i z, o x) / 2 ≤ ((pairFactors supp i z).card : ℝ) * (o₀ / 2) := by
      have : ∑ x ∈ pairFactors supp i z, o x ≤ ∑ _x ∈ pairFactors supp i z, o₀ := sum_le_sum fun x _ => hoo x
      rw [sum_const, nsmul_eq_mul] at this
      linarith
    exact (tanh_le_tanh hs).trans (OneScale.SingleLink.tanh_nat_mul_le (by linarith) _)
  calc ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), Real.tanh ((∑ x ∈ pairFactors supp i z, o x) / 2)
      ≤ ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), ((pairFactors supp i z).card : ℝ) * Real.tanh (o₀ / 2) :=
        sum_le_sum fun i _ => hterm i
    _ = (∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), ((pairFactors supp i z).card : ℝ)) *
          Real.tanh (o₀ / 2) := by rw [sum_mul]
    _ ≤ M * Real.tanh (o₀ / 2) := mul_le_mul_of_nonneg_right (hM z) ht0
    _ ≤ γ := hγ

end Criterion

end Attempts.R3
