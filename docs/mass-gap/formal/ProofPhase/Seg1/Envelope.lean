/-
Proof phase, cycle 4, workstream 2 (c4b-seg1): segment 1 (lattice spacing to L_*): published small-field/large-field
bounds in polymer form plus Kotecky–Preiss give `EnvelopeW` at L_*, uniformly in the level and the volume
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c4b-seg1/NOTE.md`.
-/

import ProofPhase.Seg1.KP
import ProofPhase.H1.Split

/-!
# Segment 1: `EnvelopeW` at `L_*` from a polymer representation

**Abstract part** (`envelopeW_of_kp`, S given `kotecky_preiss`). On any family of finite site sets with a radius
function `rad` (`≥ 0`, `0` on singletons, subadditive on overlapping unions, e.g. a diameter), the weight
`σ = λ'·rad + (|·| − 1)` is admissible, and a family of polymer gases satisfying the Kotecky–Preiss criterion for this `σ`
with one constant has cluster potentials whose envelope satisfies `ProofPhase.H1.EnvelopeW` at rate `λ'` with constant
`log 2`. The factor `|·| − 1` pays for the pair counting in `EnvelopeW` (`∑_{i ≠ z} ∑_{x ∋ i, z} = ∑_{x ∋ z} (|x| − 1)`).

**On the blocked SU(2) lattice laws** (`envelopeW_of_polymerRep`, S given the named hypothesis). `PolymerRepW` is the
named hypothesis carrying the published input (citations in its docstring and in the note): at every level `k` and volume
`j`, the law `ν k j` of the `L_*`-block field on the torus `(ℤ/N_j)⁴` has the density
`exp(∑_X E X) · Z_gas(ζ)` against product Haar, with small-field terms `E X` local on `X` and summable with weight
`e^{σ X}` (constant `M_E`), and large-field activities `ζ γ` local on `γ`, bounded by `ζ̄ γ` satisfying the
Kotecky–Preiss criterion, **all constants independent of `k` and `j`**. Conclusion: every `ν k j` is a Gibbs measure of a
bounded local potential `V = E + clusterPot`, and the sup norms of `V` satisfy `EnvelopeW` with one constant
`M_E + log 2` for all `k` and `j` (the volume family is indexed by pairs `(k, j)`).

`envelopeW_seg1` is the Yang–Mills instance: `ν k j = (T.ym k j).map (B₁ k j)` for an arbitrary measurable blocking
`B₁` from the fine torus to the `L_*` torus.

What this does **not** give: `EnvelopeW` at `L₁` (segment 2, c4c), convergence in `k` (not needed for the gap,
c3d §2), or any decay. It holds for the photon at weak coupling as well (no gap content).
-/

open MeasureTheory Finset Filter Topology OneScale OneScale.LinkDist Attempts.R3 AreaLaw.Concrete

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Seg1

/-! ## The weight `λ'·rad + (|·| − 1)` -/

section WeightAbstract

variable {ι : Type*} [DecidableEq ι]

/-- The envelope weight: `λ'·rad + (|S| − 1)`. -/
def envWeight (rad : Finset ι → ℝ) (lam' : ℝ) (S : Finset ι) : ℝ := lam' * rad S + ((S.card - 1 : ℕ) : ℝ)

/-- Hypotheses on a radius function: nonnegative, zero on singletons, subadditive on overlapping unions. -/
structure RadiusFn (rad : Finset ι → ℝ) : Prop where
  nonneg : ∀ S, 0 ≤ rad S
  single : ∀ v, rad {v} = 0
  glue : ∀ S T : Finset ι, (S ∩ T).Nonempty → rad (S ∪ T) ≤ rad S + rad T

theorem card_union_sub_one_le {S T : Finset ι} (h : (S ∩ T).Nonempty) :
    (S ∪ T).card - 1 ≤ (S.card - 1) + (T.card - 1) := by
  have e := card_union_add_card_inter S T
  have h1 : 1 ≤ (S ∩ T).card := card_pos.2 h
  have hS : 1 ≤ S.card := card_pos.2 (h.mono inter_subset_left)
  have hT : 1 ≤ T.card := card_pos.2 (h.mono inter_subset_right)
  omega

theorem weight_envWeight {rad : Finset ι → ℝ} (hr : RadiusFn rad) {lam' : ℝ} (hlam : 0 ≤ lam') :
    Weight (envWeight rad lam') where
  nonneg S _ := add_nonneg (mul_nonneg hlam (hr.nonneg S)) (Nat.cast_nonneg _)
  single v := by simp [envWeight, hr.single]
  glue S T h := by
    unfold envWeight
    have h1 := hr.glue S T h
    have h2 : (((S ∪ T).card - 1 : ℕ) : ℝ) ≤ ((S.card - 1 : ℕ) : ℝ) + ((T.card - 1 : ℕ) : ℝ) := by
      exact_mod_cast card_union_sub_one_le h
    nlinarith [mul_le_mul_of_nonneg_left h1 hlam]

/-- The pair sum of `EnvelopeW` for factors indexed by sets: `∑_{i ≠ z} ∑_{x ∋ i, z} f x = ∑_{x ∋ z} (|x| − 1) f x`. -/
theorem pairSum_sets_eq [Fintype ι] (f : Finset ι → ℝ) (z : ι) :
    ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), ∑ x ∈ pairFactors (fun A : Finset ι => A) i z, f x =
      ∑ x ∈ univ.filter (fun x : Finset ι => z ∈ x), ((x.card - 1 : ℕ) : ℝ) * f x := by
  unfold pairFactors
  rw [sum_comm' (t' := univ.filter (fun x : Finset ι => z ∈ x)) (s' := fun x => x.erase z)]
  · refine sum_congr rfl fun x hx => ?_
    rw [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_filter.1 hx).2]
  · intro i x
    simp only [mem_filter, mem_univ, true_and, mem_singleton, mem_erase]
    constructor
    · rintro ⟨hzi, hix, hzx⟩; exact ⟨⟨fun e => hzi e.symm, hix⟩, hzx⟩
    · rintro ⟨⟨hiz, hix⟩, hzx⟩; exact ⟨fun e => hiz e.symm, hix, hzx⟩

theorem natCast_le_exp (n : ℕ) : (n : ℝ) ≤ Real.exp n := by
  have := Real.add_one_le_exp (n : ℝ); linarith

/-- The `EnvelopeW` pair sum is dominated by the `σ`-weighted sum through `z`. -/
theorem pairSum_le_weighted [Fintype ι] {rad : Finset ι → ℝ} {lam' : ℝ} {h : Finset ι → ℝ}
    (h0 : ∀ x, 0 ≤ h x) (z : ι) :
    ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), ∑ x ∈ pairFactors (fun A : Finset ι => A) i z,
        h x * Real.exp (lam' * rad x) ≤
      ∑ x ∈ univ.filter (fun x : Finset ι => z ∈ x), h x * Real.exp (envWeight rad lam' x) := by
  rw [pairSum_sets_eq (fun x => h x * Real.exp (lam' * rad x)) z]
  refine sum_le_sum fun x _ => ?_
  unfold envWeight
  rw [Real.exp_add]
  have := natCast_le_exp (x.card - 1)
  have hp : 0 ≤ h x * Real.exp (lam' * rad x) := mul_nonneg (h0 x) (Real.exp_pos _).le
  calc ((x.card - 1 : ℕ) : ℝ) * (h x * Real.exp (lam' * rad x))
      ≤ Real.exp ((x.card - 1 : ℕ) : ℝ) * (h x * Real.exp (lam' * rad x)) := mul_le_mul_of_nonneg_right this hp
    _ = h x * (Real.exp (lam' * rad x) * Real.exp ((x.card - 1 : ℕ) : ℝ)) := by ring

end WeightAbstract

/-! ## Kotecky–Preiss gives `EnvelopeW` (abstract) -/

section EnvAbstract

variable {Vol : Type*} {ι : Vol → Type*} [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]

/-- **KP ⇒ `EnvelopeW`** (S): for a family of polymer gases with the KP criterion for `σ = λ'·rad + (|·| − 1)`, the
envelope `clusterBar` of the cluster potentials satisfies `EnvelopeW` at rate `λ'` with constant `log 2`, for the
whole family at once. -/
theorem envelopeW_of_kp {rad : ∀ v, Finset (ι v) → ℝ} (hr : ∀ v, RadiusFn (rad v)) {lam' : ℝ} (hlam : 0 ≤ lam')
    {Ω : Vol → Type*} {ζ : ∀ v, Finset (ι v) → Ω v → ℝ} {zb : ∀ v, Finset (ι v) → ℝ}
    (hzb : ∀ v γ, 0 ≤ zb v γ) (hz : ∀ v γ ω, |ζ v γ ω| ≤ zb v γ) (hKP : ∀ v, KPCrit (envWeight (rad v) lam') (zb v)) :
    H1.EnvelopeW (fun _ A => A) rad lam' (fun v X => clusterBar (ζ v) X) := by
  refine ⟨Real.log 2, fun v z => ?_⟩
  obtain ⟨-, -, hsum⟩ := kotecky_preiss (weight_envWeight (hr v) hlam) (hzb v) (hz v) (hKP v)
  have h0 : ∀ X, 0 ≤ clusterBar (ζ v) X := fun X => Real.iSup_nonneg fun _ => abs_nonneg _
  refine (pairSum_le_weighted h0 z).trans ?_
  have := hsum univ z (mem_univ z)
  rwa [powerset_univ] at this

end EnvAbstract

/-! ## The lattice: link diameter as a radius -/

section Lattice

variable {N : ℕ} [NeZero N]

theorem linkDiam_single (v : LatticeLink 4 N) : H1.linkDiam ({v} : Finset (LatticeLink 4 N)) = 0 := by
  simp [H1.linkDiam, siteDist_self]

theorem linkDiam_glue (S T : Finset (LatticeLink 4 N)) (h : (S ∩ T).Nonempty) :
    H1.linkDiam (S ∪ T) ≤ H1.linkDiam S + H1.linkDiam T := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨hwS, hwT⟩ := mem_inter.1 hw
  unfold H1.linkDiam
  rw [← Nat.cast_add]
  norm_cast
  refine Finset.sup_le fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := mem_product.1 hp
  have hS : ∀ a ∈ S, ∀ b ∈ S, siteDist a.site b.site ≤ (S ×ˢ S).sup fun p => siteDist p.1.site p.2.site :=
    fun a ha b hb =>
    Finset.le_sup (f := fun p : LatticeLink 4 N × LatticeLink 4 N => siteDist p.1.site p.2.site)
      (s := _ ×ˢ _) (b := (a, b)) (mem_product.2 ⟨ha, hb⟩)
  have hT : ∀ a ∈ T, ∀ b ∈ T, siteDist a.site b.site ≤ (T ×ˢ T).sup fun p => siteDist p.1.site p.2.site :=
    fun a ha b hb =>
    Finset.le_sup (f := fun p : LatticeLink 4 N × LatticeLink 4 N => siteDist p.1.site p.2.site)
      (s := _ ×ˢ _) (b := (a, b)) (mem_product.2 ⟨ha, hb⟩)
  rcases mem_union.1 hp1 with h1 | h1 <;> rcases mem_union.1 hp2 with h2 | h2
  · exact (hS _ h1 _ h2).trans (Nat.le_add_right _ _)
  · exact (siteDist_triangle _ w.site _).trans (add_le_add (hS _ h1 _ hwS) (hT _ hwT _ h2))
  · exact (siteDist_triangle _ w.site _).trans ((add_le_add (hT _ h1 _ hwT) (hS _ hwS _ h2)).trans_eq
      (add_comm _ _))
  · exact (hT _ h1 _ h2).trans (Nat.le_add_left _ _)

theorem radiusFn_linkDiam : RadiusFn (H1.linkDiam (N := N)) where
  nonneg _ := Nat.cast_nonneg _
  single := linkDiam_single
  glue := linkDiam_glue

end Lattice

/-! ## The named hypothesis and the bridge on the real objects -/

section Real

/-- **Segment-1 input: the published small-field / large-field bounds in polymer form (named hypothesis).**

For the laws `ν k j` of the `L_*`-block field on the tori `(ℤ/N_j)⁴` (any family of probability measures; the Yang–Mills
instance is `envelopeW_seg1`): at every level `k` and volume `j` there are
* **small-field terms** `E X` (one per set `X` of `L_*`-links), measurable, depending only on the links in `X`, with
  `|E X| ≤ Ē X`, `Ē ≥ 0`, `Ē ∅ ≤ M_E` and `∑_{X ∋ z} Ē X · e^{σ X} ≤ M_E` for every link `z`;
* **large-field activities** `ζ γ`, measurable, depending only on the links in `γ`, with `|ζ γ| ≤ ζ̄ γ` and the
  Kotecky–Preiss criterion `∑_{γ ∋ z} ζ̄ γ 2^{|γ|} e^{σ γ} ≤ 1`;
* and `ν k j` is the probability measure with density `∝ exp(∑_X E X) · Z_gas(ζ)` against product Haar (`Z_gas` the
  hard-core gas of `KP.lean` on all links);

where `σ = λ'·diam + (|·| − 1)` (`envWeight`, `diam` the `ℓ^∞` diameter of base sites in `L_*` units), and `λ'`, `M_E`
do **not** depend on `k`, `j`.

**What it transcribes and from where** (exact citations and the reading status in the note, §1): this is the form in
which Balaban's renormalisation-group analysis of 4D lattice Yang–Mills states the effective density after `n` blocking
steps at weak coupling: small-field effective action as a sum of local, analytic, exponentially decaying polymer terms
(Balaban, CMP 109 (1987) 249; CMP 116 (1988) 1; CMP 119 (1988) 243) and large-field regions with the R-operation bounds
`e^{−p(g)}` per large-field block (Balaban, CMP 122 (1989) 175 and 355), the constants uniform in the number of steps
while the running coupling stays below a threshold. The same structure, as a Lean statement in a different blocking, is
the OpenAI construction's `Rep.eval` (exp of masked E-activities times a gas of K-activities, budgets `exp(κ·cover)`
uniform in the volume; `../../weak-coupling/H1-OPENAI.md` §2). **Not checked here:** that either source states it with
exactly this hard-core gas and these weights, for the blocking used, with constants uniform in `k`; the note lists the
three translation steps (hard core vs touching, `exp(κ·cover)` vs `e^{σ}`, their blocking vs ours). -/
def PolymerRepW (N : ℕ → ℕ) [∀ j, NeZero (N j)] (ν : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (N j)))
    (lam' ME : ℝ) : Prop :=
  ∀ k j, ∃ (E ζ : Finset (LatticeLink 4 (N j)) → GaugeConnection SU2 4 (N j) → ℝ)
    (Eb zb : Finset (LatticeLink 4 (N j)) → ℝ),
    (∀ X, Measurable (E X)) ∧ (∀ X, DepOn (E X) X) ∧ (∀ X U, |E X U| ≤ Eb X) ∧ (∀ X, 0 ≤ Eb X) ∧
    Eb ∅ ≤ ME ∧ (∀ z, ∑ X ∈ univ.filter (fun X => z ∈ X), Eb X * Real.exp (envWeight H1.linkDiam lam' X) ≤ ME) ∧
    (∀ γ, Measurable (ζ γ)) ∧ (∀ γ, DepOn (ζ γ) γ) ∧ (∀ γ U, |ζ γ U| ≤ zb γ) ∧ (∀ γ, 0 ≤ zb γ) ∧
    KPCrit (envWeight H1.linkDiam lam') zb ∧
    ν k j = weightMeasure (haarG SU2) (fun U => Real.exp (∑ X, E X U) * gasZ (fun γ => ζ γ U) univ)

variable {N : ℕ → ℕ} [∀ j, NeZero (N j)]

theorem measurable_clusterPot {L : ℕ} [NeZero L]
    {ζ : Finset (LatticeLink 4 L) → GaugeConnection SU2 4 L → ℝ} (hζ : ∀ γ, Measurable (ζ γ))
    (X : Finset (LatticeLink 4 L)) : Measurable (fun U => clusterPot ζ U X) := by
  unfold clusterPot mob Zc gasZ
  refine Finset.measurable_sum _ fun Y _ => measurable_const.mul ?_
  exact (Finset.measurable_sum _ fun F _ => Finset.measurable_prod _ fun γ _ => hζ γ).log

/-- **Segment 1, bridge** (S given `PolymerRepW` and `kotecky_preiss`): every `L_*` law is the Gibbs measure of a
bounded local potential `V = E + clusterPot`, and one envelope `h ≥ sup |V|` satisfies `EnvelopeW` at rate `λ'` for all
levels and volumes at once (the family of `EnvelopeW` is indexed by `(k, j)`). -/
theorem envelopeW_of_polymerRep {ν : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (N j))} {lam' ME : ℝ} (hlam : 0 ≤ lam')
    (hrep : PolymerRepW N ν lam' ME) :
    ∃ (V : ℕ → ∀ j, Finset (LatticeLink 4 (N j)) → GaugeConnection SU2 4 (N j) → ℝ)
      (h : ∀ kj : ℕ × ℕ, Finset (LatticeLink 4 (N kj.2)) → ℝ),
      (∀ k j, ν k j = gibbsMeasure (haarG SU2) (V k j) ∧ Potential (fun A => A) (V k j) ∧
        ∀ X U, |V k j X U| ≤ h (k, j) X) ∧
      H1.EnvelopeW (ι := fun kj : ℕ × ℕ => LatticeLink 4 (N kj.2)) (fun _ A => A) (fun _ => H1.linkDiam) lam' h := by
  choose E ζ Eb zb hEm hEd hEb hEb0 hE0 hEsum hζm hζd hζb hzb0 hKP hν using hrep
  have hσ : ∀ j, Weight (envWeight (H1.linkDiam (N := N j)) lam') := fun j =>
    weight_envWeight radiusFn_linkDiam hlam
  have hkp := fun k j => kotecky_preiss (hσ j) (hzb0 k j) (hζb k j) (hKP k j)
  refine ⟨fun k j X U => E k j X U + clusterPot (ζ k j) U X, fun kj X => Eb kj.1 kj.2 X + clusterBar (ζ kj.1 kj.2) X,
    fun k j => ⟨?_, ?_, fun X U => ?_⟩, ?_⟩
  · -- the Gibbs representation
    rw [hν k j]
    unfold gibbsMeasure totalLog
    congr 1
    funext U
    have hpos := (hkp k j).1 U univ
    have hlog := log_gasZ_eq_sum (ζ k j) U univ
    rw [powerset_univ] at hlog
    rw [sum_add_distrib, Real.exp_add, ← hlog, Real.exp_log hpos]
  · -- a bounded local potential
    refine ⟨fun X => (hEm k j X).add (measurable_clusterPot (hζm k j) X), ⟨ME + Real.log 2, fun X U => ?_⟩,
      fun X U U' hUU' => ?_⟩
    · have hbar : |clusterPot (ζ k j) U X| ≤ Real.log 2 := by
        rcases X.eq_empty_or_nonempty with h0 | ⟨z, hz⟩
        · rw [h0, clusterPot_empty, abs_zero]; exact (Real.log_pos one_lt_two).le
        · have hs := (hkp k j).2.2 univ z (mem_univ z)
          have h1 : clusterBar (ζ k j) X * Real.exp (envWeight H1.linkDiam lam' X) ≤ Real.log 2 :=
            (single_le_sum (f := fun X => clusterBar (ζ k j) X * Real.exp (envWeight H1.linkDiam lam' X))
              (fun Y _ => mul_nonneg (Real.iSup_nonneg fun _ => abs_nonneg _) (Real.exp_pos _).le)
              (mem_filter.2 ⟨mem_powerset.2 (subset_univ X), hz⟩)).trans hs
          have h2 : 1 ≤ Real.exp (envWeight H1.linkDiam lam' X) :=
            Real.one_le_exp ((hσ j).nonneg X ⟨z, hz⟩)
          have h3 : |clusterPot (ζ k j) U X| ≤ clusterBar (ζ k j) X := le_ciSup ((hkp k j).2.1 X) U
          have h4 : 0 ≤ clusterBar (ζ k j) X := Real.iSup_nonneg fun _ => abs_nonneg _
          nlinarith [mul_le_mul_of_nonneg_left h2 h4]
      have hE : |E k j X U| ≤ ME := by
        refine (hEb k j X U).trans ?_
        rcases X.eq_empty_or_nonempty with h0 | ⟨z, hz⟩
        · rw [h0]; exact hE0 k j
        · have h1 : Eb k j X * Real.exp (envWeight H1.linkDiam lam' X) ≤ ME :=
            (single_le_sum (f := fun X => Eb k j X * Real.exp (envWeight H1.linkDiam lam' X))
              (fun Y _ => mul_nonneg (hEb0 k j Y) (Real.exp_pos _).le) (mem_filter.2 ⟨mem_univ X, hz⟩)).trans
              (hEsum k j z)
          have h2 : 1 ≤ Real.exp (envWeight H1.linkDiam lam' X) :=
            Real.one_le_exp ((hσ j).nonneg X ⟨z, hz⟩)
          nlinarith [hEb0 k j X]
      exact (abs_add_le _ _).trans (add_le_add hE hbar)
    · show E k j X U + clusterPot (ζ k j) U X = E k j X U' + clusterPot (ζ k j) U' X
      rw [hEd k j X U U' hUU', clusterPot_congr fun γ hγ => hζd k j γ U U' fun i hi => hUU' i (hγ hi)]
  · exact (abs_add_le _ _).trans (add_le_add (hEb k j X U) (le_ciSup ((hkp k j).2.1 X) U))
  · -- the envelope, uniformly in `(k, j)`
    refine ⟨ME + Real.log 2, fun kj z => ?_⟩
    obtain ⟨k, j⟩ := kj
    have h0 : ∀ X, 0 ≤ Eb k j X + clusterBar (ζ k j) X := fun X =>
      add_nonneg (hEb0 k j X) (Real.iSup_nonneg fun _ => abs_nonneg _)
    refine (pairSum_le_weighted (rad := H1.linkDiam) (lam' := lam') h0 z).trans ?_
    have hs := (hkp k j).2.2 univ z (mem_univ z)
    rw [powerset_univ] at hs
    simp_rw [add_mul]
    rw [sum_add_distrib]
    exact add_le_add (hEsum k j z) hs

/-- **Segment 1 for Yang–Mills** (S given `PolymerRepW`): for the SU(2) Wilson measures `T.ym k j` blocked by any
measurable maps `B₁ k j` to the `L_*` tori, the polymer representation gives Gibbs representations with bounded local
potentials and `EnvelopeW` at `L_*`, uniformly in the level `k` and the volume `j`. -/
theorem envelopeW_seg1 (T : Tuning) (B₁ : ∀ k j, GaugeConnection SU2 4 (T.side k j) → GaugeConnection SU2 4 (N j))
    {lam' ME : ℝ} (hlam : 0 ≤ lam') (hrep : PolymerRepW N (fun k j => (T.ym k j).map (B₁ k j)) lam' ME) :
    ∃ (V : ℕ → ∀ j, Finset (LatticeLink 4 (N j)) → GaugeConnection SU2 4 (N j) → ℝ)
      (h : ∀ kj : ℕ × ℕ, Finset (LatticeLink 4 (N kj.2)) → ℝ),
      (∀ k j, (T.ym k j).map (B₁ k j) = gibbsMeasure (haarG SU2) (V k j) ∧ Potential (fun A => A) (V k j) ∧
        ∀ X U, |V k j X U| ≤ h (k, j) X) ∧
      H1.EnvelopeW (ι := fun kj : ℕ × ℕ => LatticeLink 4 (N kj.2)) (fun _ A => A) (fun _ => H1.linkDiam) lam' h :=
  envelopeW_of_polymerRep hlam hrep

end Real

end ProofPhase.Seg1
