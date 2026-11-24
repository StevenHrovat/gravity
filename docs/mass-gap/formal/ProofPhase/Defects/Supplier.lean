/-
Proof phase, cycle 5, workstream 4 (c5d-supplier): the segment-1 supplier in defect form (`UVRepDefect`) and its
translation into the defect law that the rare-defect Dobrushin theorem consumes (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5d-supplier/NOTE.md`, Part A.
-/

import ProofPhase.Seg1.Envelope

/-!
# UV1 in defect form, and the translation to a cylinder-dominated defect law

**Abstract part (S, elementary).**
* `exists_sep_subset`: from any finite set `T` a greedy choice extracts `T' ⊆ T`, pairwise non-conflicting, with
  `|T| ≤ K |T'|`, if every conflict neighbourhood has at most `K` elements (conflict reflexive and symmetric).
* `measure_biInter_le_pow`: if `P(Bad x ∩ E) ≤ p P(E)` for every event `E` of a σ-algebra `𝒢 x` ("everything outside
  the range of `x`"), and `Bad y ∈ 𝒢 x` whenever `y` does not conflict with `x` (locality of the defect events), then
  `P(⋂_{x ∈ T'} Bad x) ≤ p^{|T'|}` for every pairwise non-conflicting `T'` (chain rule).
* `badLaw`, `sum_badLaw_cyl`: the law `q B = P{badSet = B}` of the random defect set, and
  `∑_B q B 1[U ⊆ B] = P(⋂_{x ∈ U} Bad x)`.
* **`cylinder_of_condBound`**: together, `q` is **dominated on cylinders** with `p₀ = p^{1/K}`:
  `∑_B q B 1[U ⊆ B] ≤ (p^{1/K})^{|U|}`. This is exactly the hypothesis `hcyl` of `EffDist.expect_effWeight_le` and
  `Annealed.defect_decay_W` (the Liggett–Schonmann–Stacey-type step, in the cylinder form that the Peierls bound uses;
  no full stochastic domination is needed).

**`UVRepDefect` (named hypothesis, open).** UV1 of the version-4 blueprint, in the form the sources can support
(NOTE.md A.3): for every level `k` and volume `j`, the `L_*` law has a density `e^{−S}` against product Haar; `S` is a
sum of local terms `E X`; off the defect set (`X` meets no bad link) each `E X` is within `ē X` of the reference
action's term `Wref j X` in **sup norm**, with `∑_{X ∋ z} ē X e^{λ' diam X} ≤ ε₀`; the bad events are measurable, local,
and have conditional probability `≤ p` given the σ-algebra `𝒢 x` of the field outside range `rad` of `x`; conflict
neighbourhoods (links within `rad`) have at most `K` links. All constants independent of `k` and `j`.

**`uvRepDefect_cylinder` (S given the hypothesis):** under `UVRepDefect`, for every `k`, `j` the law of the bad set
satisfies the cylinder hypothesis of Part B with `p₀ = p^{1/K}`, and the off-bad closeness clause holds for the same
bad sets. This is the translation lemma: what UV1 hands to the rare-defect theorem.

**Sources (NOTE.md A.1, A.2).** Target form of Balaban, CMP 109 (1987) 249, 116 (1988) 1, 119 (1988) 243, 122 (1989)
175 and 355 (not read in full text: Project Euclid refused automated access); Dimock, arXiv:1212.5562, Thm 3.1 (read,
`φ⁴₃` only: the same partition-of-unity structure, large-field factors with upper bounds only); OpenAI construction
`YM/RG/History.lean:166-181`, `Activities.lean:98-132`, `Masks.lean:31-40` (read in source): density, local `flags`,
small-field budgets uniform in depth and volume, **no probability bound on the flags and no closeness to a fixed action**
(only `β ×` a clipped multi-loop action with summable coefficients). The clause **(B) conditional probability `≤ p`** is
stated by neither source; NOTE.md A.3 says how big the gap is.
-/

open MeasureTheory Finset OneScale OneScale.LinkDist Attempts.R3 AreaLaw.Concrete
open scoped ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Defects

/-! ## A greedy separated subset -/

/-- **Greedy extraction.** Conflict reflexive and symmetric, every conflict neighbourhood of size `≤ K`: every finite
`T` contains a pairwise non-conflicting `T'` with `|T| ≤ K |T'|`. -/
theorem exists_sep_subset {X : Type*} [Fintype X] [DecidableEq X] (conf : X → X → Prop) [DecidableRel conf]
    (hrefl : ∀ x, conf x x) (hsymm : ∀ x y, conf x y → conf y x) {K : ℕ}
    (hK : ∀ x, (univ.filter (conf x)).card ≤ K) (T : Finset X) :
    ∃ T' ⊆ T, (∀ x ∈ T', ∀ y ∈ T', x ≠ y → ¬ conf x y) ∧ T.card ≤ K * T'.card := by
  induction T using Finset.strongInduction with
  | H T ih =>
    rcases T.eq_empty_or_nonempty with hT | ⟨x, hx⟩
    · exact ⟨∅, empty_subset _, by simp, by simp [hT]⟩
    · set T1 := T.filter (fun y => ¬ conf x y)
      have hxT1 : x ∉ T1 := by simp [T1, hrefl x]
      have hsub : T1 ⊂ T := (ssubset_iff_of_subset (filter_subset _ _)).2 ⟨x, hx, hxT1⟩
      obtain ⟨T1', hT1', hsep, hcard⟩ := ih T1 hsub
      refine ⟨insert x T1', ?_, ?_, ?_⟩
      · exact insert_subset hx (hT1'.trans (filter_subset _ _))
      · have hfar : ∀ y ∈ T1', ¬ conf x y := fun y hy => (mem_filter.1 (hT1' hy)).2
        intro a ha b hb hab
        rw [mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact hfar b hb
        · exact fun h => hfar a ha (hsymm _ _ h)
        · exact hsep a ha b hb hab
      · have hxT1' : x ∉ T1' := fun h => hxT1 (hT1' h)
        rw [card_insert_of_notMem hxT1']
        have hsplit : (T.filter (conf x)).card + T1.card = T.card := card_filter_add_card_filter_not (conf x)
        have hnear : (T.filter (conf x)).card ≤ K :=
          (card_le_card (filter_subset_filter _ (subset_univ T))).trans (hK x)
        calc T.card = (T.filter (conf x)).card + T1.card := hsplit.symm
          _ ≤ K + K * T1'.card := Nat.add_le_add hnear hcard
          _ = K * (T1'.card + 1) := by ring

/-! ## The chain rule for conditional bounds -/

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- **Chain rule.** Conditional bounds `P(Bad x ∩ E) ≤ p P(E)` for `E ∈ 𝒢 x`, and `Bad y ∈ 𝒢 x` for non-conflicting
`y ≠ x`: the intersection over a pairwise non-conflicting `T` has probability `≤ p^{|T|}`. -/
theorem measure_biInter_le_pow (P : Measure Ω) [IsProbabilityMeasure P] {X : Type*} [DecidableEq X]
    (Bad : X → Set Ω) (𝒢 : X → MeasurableSpace Ω) {p : ℝ≥0∞}
    (hcond : ∀ x E, MeasurableSet[𝒢 x] E → P (Bad x ∩ E) ≤ p * P E) (conf : X → X → Prop)
    (hloc : ∀ x y, x ≠ y → ¬ conf x y → MeasurableSet[𝒢 x] (Bad y)) (T : Finset X)
    (hT : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ conf x y) :
    P (⋂ x ∈ T, Bad x) ≤ p ^ T.card := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    have hT' : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ¬ conf x y :=
      fun x hx y hy => hT x (mem_insert_of_mem hx) y (mem_insert_of_mem hy)
    have hmeas : MeasurableSet[𝒢 a] (⋂ x ∈ T, Bad x) := by
      refine @Finset.measurableSet_biInter _ _ (𝒢 a) _ _ fun y hy => ?_
      have hya : a ≠ y := fun h => haT (h ▸ hy)
      exact hloc a y hya (hT a (mem_insert_self a T) y (mem_insert_of_mem hy) hya)
    rw [set_biInter_insert, card_insert_of_notMem haT, pow_succ']
    exact (hcond a _ hmeas).trans (by gcongr; exact ih hT')

/-! ## The law of the defect set -/

open Classical in
/-- The random defect set. -/
def badSet {X : Type*} [Fintype X] (Bad : X → Set Ω) (ω : Ω) : Finset X := univ.filter (fun x => ω ∈ Bad x)

/-- The law of the defect set: `q B = P{badSet = B}`. -/
def badLaw {X : Type*} [Fintype X] (P : Measure Ω) (Bad : X → Set Ω) (B : Finset X) : ℝ :=
  (P {ω | badSet Bad ω = B}).toReal

theorem badLaw_nonneg {X : Type*} [Fintype X] (P : Measure Ω) (Bad : X → Set Ω) (B : Finset X) :
    0 ≤ badLaw P Bad B := ENNReal.toReal_nonneg

theorem measurableSet_badSet_eq {X : Type*} [Fintype X] (Bad : X → Set Ω) (hmeas : ∀ x, MeasurableSet (Bad x))
    (B : Finset X) : MeasurableSet {ω | badSet Bad ω = B} := by
  classical
  have e : {ω | badSet Bad ω = B} = ⋂ x, (if x ∈ B then Bad x else (Bad x)ᶜ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, badSet, Finset.ext_iff, mem_filter, mem_univ, true_and]
    refine forall_congr' fun x => ?_
    by_cases hx : x ∈ B <;> simp [hx]
  rw [e]
  refine MeasurableSet.iInter fun x => ?_
  split_ifs
  · exact hmeas x
  · exact (hmeas x).compl

/-- `∑_B q B 1[U ⊆ B] = P(⋂_{x ∈ U} Bad x)`. -/
theorem sum_badLaw_cyl {X : Type*} [Fintype X] [DecidableEq X] (P : Measure Ω) [IsFiniteMeasure P]
    (Bad : X → Set Ω) (hmeas : ∀ x, MeasurableSet (Bad x)) (U : Finset X) :
    ∑ B, badLaw P Bad B * (if U ⊆ B then 1 else 0) = (P (⋂ x ∈ U, Bad x)).toReal := by
  classical
  have h1 : ∑ B, badLaw P Bad B * (if U ⊆ B then 1 else 0) = ∑ B ∈ univ.filter (fun B => U ⊆ B), badLaw P Bad B := by
    rw [sum_filter]; exact sum_congr rfl fun B _ => by split_ifs <;> simp
  have hdisj : (↑(univ.filter (fun B : Finset X => U ⊆ B)) : Set (Finset X)).PairwiseDisjoint
      (fun B => {ω | badSet Bad ω = B}) := by
    intro B _ B' _ hBB'
    refine Set.disjoint_left.2 fun ω h h' => hBB' ?_
    simp only [Set.mem_ofPred_eq] at h h'
    rw [← h, ← h']
  have hU : (⋃ B ∈ univ.filter (fun B : Finset X => U ⊆ B), {ω | badSet Bad ω = B}) = ⋂ x ∈ U, Bad x := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, mem_filter, mem_univ, true_and, exists_prop, Set.mem_iInter]
    constructor
    · rintro ⟨B, hUB, hB⟩ x hx
      have := hUB hx
      rw [← hB] at this
      simpa [badSet] using this
    · intro h
      exact ⟨badSet Bad ω, fun x hx => by simpa [badSet] using h x hx, rfl⟩
  rw [h1, ← hU, measure_biUnion_finset hdisj (fun B _ => measurableSet_badSet_eq Bad hmeas B),
    ENNReal.toReal_sum (fun B _ => measure_ne_top P _)]
  rfl

/-- **Translation: conditional bound with finite range ⇒ cylinder-dominated defect law** (S). -/
theorem cylinder_of_condBound (P : Measure Ω) [IsProbabilityMeasure P] {X : Type*} [Fintype X] [DecidableEq X]
    (Bad : X → Set Ω) (hmeas : ∀ x, MeasurableSet (Bad x)) (𝒢 : X → MeasurableSpace Ω) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hcond : ∀ x E, MeasurableSet[𝒢 x] E → P (Bad x ∩ E) ≤ ENNReal.ofReal p * P E)
    (conf : X → X → Prop) [DecidableRel conf] (hrefl : ∀ x, conf x x) (hsymm : ∀ x y, conf x y → conf y x)
    (hloc : ∀ x y, x ≠ y → ¬ conf x y → MeasurableSet[𝒢 x] (Bad y)) {K : ℕ} (hK0 : 0 < K)
    (hK : ∀ x, (univ.filter (conf x)).card ≤ K) (U : Finset X) :
    ∑ B, badLaw P Bad B * (if U ⊆ B then 1 else 0) ≤ (p ^ ((1 : ℝ) / K)) ^ U.card := by
  rw [sum_badLaw_cyl P Bad hmeas U]
  obtain ⟨U', hU'U, hsep, hcard⟩ := exists_sep_subset conf hrefl hsymm hK U
  have h1 : P (⋂ x ∈ U, Bad x) ≤ P (⋂ x ∈ U', Bad x) :=
    measure_mono (Set.biInter_subset_biInter_left fun x hx => hU'U hx)
  have h2 := measure_biInter_le_pow P Bad 𝒢 hcond conf hloc U' hsep
  have h3 : (P (⋂ x ∈ U, Bad x)).toReal ≤ p ^ U'.card := by
    have := h1.trans h2
    rw [← ENNReal.ofReal_pow hp0.le] at this
    exact ENNReal.toReal_le_of_le_ofReal (pow_nonneg hp0.le _) this
  refine h3.trans (le_of_eq_of_le (b := p ^ (U'.card : ℝ)) ?_ ?_)
  · exact (Real.rpow_natCast p U'.card).symm
  · rw [← Real.rpow_natCast (p ^ ((1 : ℝ) / K)), ← Real.rpow_mul hp0.le]
    refine Real.rpow_le_rpow_of_exponent_ge hp0 hp1 ?_
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK0
    rw [one_div_mul_eq_div, div_le_iff₀ hK']
    have : (U.card : ℝ) ≤ K * U'.card := by exact_mod_cast hcard
    linarith

/-! ## UV1 in defect form on the `L_*` tori -/

/-- **UV1 in defect form** (named hypothesis; open, see the module docstring and NOTE.md A.3 for sources and gaps).
For every level `k` and volume `j`, on the `L_*` torus `(ℤ/N_j)⁴`:
(D) `ν k j = weightMeasure Haar (e^{−S})`, `S` measurable;
(L) `S = ∑_X E X` with `E X` depending only on the links in `X`;
(G) off the defect set (no link of `X` bad) `|E X − Wref j X| ≤ ē X`, `∑_{X ∋ z} ē X e^{λ' diam X} ≤ ε₀`;
(B) bad events measurable, `ν(Bad x ∩ E) ≤ p ν(E)` for `E` in the σ-algebra `𝒢 x` (the field outside range `rad`
of `x`), `Bad y ∈ 𝒢 x` for `linkDist x y > rad` (locality);
(K) at most `K` links within `rad` of any link.
All constants independent of `k`, `j`. -/
def UVRepDefect (N : ℕ → ℕ) [∀ j, NeZero (N j)] (ν : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (N j)))
    (Wref : ∀ j, Finset (LatticeLink 4 (N j)) → GaugeConnection SU2 4 (N j) → ℝ)
    (rad lam' eps0 p : ℝ) (K : ℕ) : Prop :=
  ∀ k j, ∃ (Sact : GaugeConnection SU2 4 (N j) → ℝ)
      (E : Finset (LatticeLink 4 (N j)) → GaugeConnection SU2 4 (N j) → ℝ)
      (eb : Finset (LatticeLink 4 (N j)) → ℝ)
      (Bad : LatticeLink 4 (N j) → Set (GaugeConnection SU2 4 (N j)))
      (𝒢 : LatticeLink 4 (N j) → MeasurableSpace (GaugeConnection SU2 4 (N j))),
    -- (D) density
    (Measurable Sact ∧ ν k j = weightMeasure (haarG SU2) (fun U => Real.exp (-Sact U))) ∧
    -- (L) local terms
    ((∀ X, DepOn (E X) X) ∧ ∀ U, Sact U = ∑ X, E X U) ∧
    -- (G) closeness to the reference action off the defect set, with exponential tails
    ((∀ X U, (∀ x ∈ X, U ∉ Bad x) → |E X U - Wref j X U| ≤ eb X) ∧ (∀ X, 0 ≤ eb X) ∧
      ∀ z, ∑ X ∈ univ.filter (fun X => z ∈ X), eb X * Real.exp (lam' * H1.linkDiam X) ≤ eps0) ∧
    -- (B) defect events: measurable, conditionally rare, local
    ((∀ x, MeasurableSet (Bad x)) ∧
      (∀ x Ev, MeasurableSet[𝒢 x] Ev → ν k j (Bad x ∩ Ev) ≤ ENNReal.ofReal p * ν k j Ev) ∧
      ∀ x y : LatticeLink 4 (N j), rad < linkDist x y → MeasurableSet[𝒢 x] (Bad y)) ∧
    -- (K) conflict neighbourhoods
    ∀ x : LatticeLink 4 (N j), (univ.filter (fun y => linkDist x y ≤ rad ∨ linkDist y x ≤ rad)).card ≤ K

/-- **The translation lemma** (S given `UVRepDefect`): for every `k`, `j` there is a defect family for which
(i) the off-defect closeness clause (G) holds, and (ii) the law of the defect set is dominated on cylinders with
`p₀ = p^{1/K}`, i.e. satisfies the hypothesis `hcyl` of `defect_decay_W`. -/
theorem uvRepDefect_cylinder {N : ℕ → ℕ} [∀ j, NeZero (N j)] {ν : ℕ → ∀ j, Measure (GaugeConnection SU2 4 (N j))}
    [∀ k j, IsProbabilityMeasure (ν k j)]
    {Wref : ∀ j, Finset (LatticeLink 4 (N j)) → GaugeConnection SU2 4 (N j) → ℝ} {rad lam' eps0 p : ℝ} {K : ℕ}
    (hrad : 0 ≤ rad) (hp0 : 0 < p) (hp1 : p ≤ 1) (hK0 : 0 < K) (h : UVRepDefect N ν Wref rad lam' eps0 p K)
    (k j : ℕ) :
    ∃ (E : Finset (LatticeLink 4 (N j)) → GaugeConnection SU2 4 (N j) → ℝ)
      (eb : Finset (LatticeLink 4 (N j)) → ℝ) (Bad : LatticeLink 4 (N j) → Set (GaugeConnection SU2 4 (N j))),
      (∀ X U, (∀ x ∈ X, U ∉ Bad x) → |E X U - Wref j X U| ≤ eb X) ∧
      (∀ z, ∑ X ∈ univ.filter (fun X => z ∈ X), eb X * Real.exp (lam' * H1.linkDiam X) ≤ eps0) ∧
      ∀ U : Finset (LatticeLink 4 (N j)),
        ∑ B, badLaw (ν k j) Bad B * (if U ⊆ B then 1 else 0) ≤ (p ^ ((1 : ℝ) / K)) ^ U.card := by
  classical
  obtain ⟨_, E, eb, Bad, 𝒢, _, _, ⟨hG, _, hsum⟩, ⟨hmeas, hcond, hloc⟩, hK⟩ := h k j
  refine ⟨E, eb, Bad, hG, hsum, fun U => ?_⟩
  let conf : LatticeLink 4 (N j) → LatticeLink 4 (N j) → Prop := fun x y => linkDist x y ≤ rad ∨ linkDist y x ≤ rad
  have hrefl : ∀ x, conf x x := fun x => Or.inl (by simp [linkDist, siteDist_self, hrad])
  have hsymm : ∀ x y, conf x y → conf y x := fun x y h => h.symm
  have hloc' : ∀ x y, x ≠ y → ¬ conf x y → MeasurableSet[𝒢 x] (Bad y) := by
    intro x y _ hc
    refine hloc x y ?_
    by_contra hle
    exact hc (Or.inl (not_lt.1 hle))
  exact cylinder_of_condBound (ν k j) Bad hmeas 𝒢 hp0 hp1 hcond conf hrefl hsymm hloc' hK0 hK U

end ProofPhase.Defects
