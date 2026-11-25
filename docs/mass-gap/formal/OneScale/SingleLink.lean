/-
The one-scale reduction, non-vacuity at strong coupling (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §8 (Proposition 8.1) and §1.1 (the neighbour fact).
-/

import OneScale.Gauge
import OneScale.Decay
import OneScale.OscTV

/-!
# Non-vacuity: single-link blocks for the Wilson measure (Proposition 8.1, H variant)

Blocks are single links, `B_e = {e}`, for the Wilson weight `φ(x) = e^{β x}`, `β ≥ 0`, on the torus `(ℤ/Nℤ)^d`.

* `gaugeSpec_single_eq_gibbs`: the conditional law of one link given the rest (the block specification of
  `OneScale.Gauge`) is the Gibbs measure `Influence.gibbs π (β ∑_{p ∋ e} Re tr U_p)` of the TV lemma.
* `influence_single`: for `z ≠ e`, `k_{e}(z) = tanh(m(e, z) n β)` is an influence bound, where `m(e, z)` is the number of
  plaquettes containing both `e` and `z` (`common`). Proof: `Influence.tv_single_link_le_tanh` (only the `m(e, z)`
  common plaquettes change) and Lemma 2.4 (`OneScale.abs_integral_gibbs_sub_le`).
* `card_plaqsAt_le`: a link lies in at most `2(d - 1)` plaquettes (new lattice lemma; sharper than
  `AreaLaw.Concrete.card_plaqsAt_le`).
* `sum_common_le`: `∑_{e ≠ z} m(e, z) ≤ 6(d - 1)` (each plaquette through `z` has at most 3 other links).
* `gds_single`: **GDS for single links with `γ = 6(d - 1) tanh(n β)`**, using `tanh(m x) ≤ m tanh x`.
  This holds for every `N ≥ 1`: for `N = 2`, where two links can share two plaquettes, the multiplicity `m(e, z)`
  accounts for it, so the note's standing assumption `N ≥ 3` is not needed here.
* `wilson_singleLink_decay`: **Theorem A applied to the Wilson torus measure** in the window
  `6(d - 1) tanh(n β) e^{λ} < 1`, for any distance on links with neighbours (links sharing a plaquette) at distance
  `≤ 1`; `exists_rate` gives such a `λ > 0` whenever `6(d - 1) tanh(n β) < 1`, the hypothesis of
  `Influence.dobrushin_single_link`.

Standard: Dobrushin's uniqueness condition at high temperature (Dobrushin 1968, 1970); its application to lattice gauge
fields at strong coupling is classical. The formalisation, the block-spec identification and the counting are ours.
-/

open MeasureTheory Finset AreaLaw.Concrete Influence

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale.SingleLink

open OneScale.Gauge

variable {d N : ℕ} [NeZero N]

/-! ## `tanh` -/

theorem tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.2 hx) (Real.cosh_pos x).le

theorem tanh_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.tanh (a + b) ≤ Real.tanh a + Real.tanh b := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_add,
    Real.cosh_add, div_add_div _ _ (Real.cosh_pos a).ne' (Real.cosh_pos b).ne']
  have sa := Real.sinh_nonneg_iff.2 ha
  have sb := Real.sinh_nonneg_iff.2 hb
  have ca := Real.cosh_pos a
  have cb := Real.cosh_pos b
  refine div_le_div_of_nonneg_left (by positivity) (mul_pos ca cb) ?_
  nlinarith [mul_nonneg sa sb]

theorem tanh_nat_mul_le {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : Real.tanh (m * x) ≤ m * Real.tanh x := by
  induction m with
  | zero => simp
  | succ m ih =>
    push_cast
    rw [add_mul, one_mul]
    calc Real.tanh (m * x + x) ≤ Real.tanh (m * x) + Real.tanh x :=
          tanh_add_le (mul_nonneg (Nat.cast_nonneg _) hx) hx
      _ ≤ m * Real.tanh x + Real.tanh x := by linarith
      _ = (m + 1) * Real.tanh x := by ring

/-! ## Counting plaquettes -/

/-- The number of plaquettes containing both `e` and `z`. -/
def common (e z : LatticeLink d N) : ℕ :=
  (univ.filter fun p : LatticePlaquette d N => e ∈ plaqLinks p ∧ z ∈ plaqLinks p).card

theorem touching_singleton (e : LatticeLink d N) : touching ({e} : Finset (LatticeLink d N)) = plaqsAt e := by
  ext p; simp [touching, plaqsAt]

/-- The direction of a plaquette other than `μ` (meaningful when one of its directions is `μ`). -/
def otherOf (μ : Fin d) (q : LatticePlaquette d N) : Fin d := if q.dir1 = μ then q.dir2 else q.dir1

theorem card_slots03_le (l : LatticeLink d N) : (plaqsAtSlot l 0 ∪ plaqsAtSlot l 3).card ≤ d - 1 := by
  obtain ⟨ls, lμ⟩ := l
  have h : (plaqsAtSlot ⟨ls, lμ⟩ 0 ∪ plaqsAtSlot ⟨ls, lμ⟩ 3).card ≤ ((univ : Finset (Fin d)).erase lμ).card := by
    refine card_le_card_of_injOn (otherOf lμ) (fun q hq => ?_) ?_
    · simp only [coe_union, Set.mem_union, mem_coe, plaqsAtSlot, mem_filter, mem_univ, true_and] at hq
      simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      have hlt := q.h_lt
      rcases hq with h | h <;> simp only [LatticePlaquette.boundaryLinks, LatticeLink.mk.injEq] at h
      · simp only [otherOf, h.2, ite_true]; intro he; rw [he, ← h.2] at hlt; exact lt_irrefl _ hlt
      · have : q.dir1 ≠ lμ := by rw [← h.2]; exact ne_of_lt hlt
        simp only [otherOf, this, ite_false]; exact not_false
    · intro q hq q' hq' he
      simp only [coe_union, Set.mem_union, mem_coe, plaqsAtSlot, mem_filter, mem_univ, true_and] at hq hq'
      have hlt := q.h_lt
      have hlt' := q'.h_lt
      rcases hq with h | h <;> rcases hq' with h' | h' <;>
        simp only [LatticePlaquette.boundaryLinks, LatticeLink.mk.injEq] at h h'
      · simp only [otherOf, h.2, h'.2, ite_true] at he
        exact plaq_ext (h.1.trans h'.1.symm) (h.2.trans h'.2.symm) he
      · exfalso
        have : q'.dir1 ≠ lμ := by rw [← h'.2]; exact ne_of_lt hlt'
        simp only [otherOf, h.2, this, ite_true, ite_false] at he
        rw [h.2] at hlt; rw [h'.2] at hlt'; rw [he] at hlt
        exact lt_asymm hlt hlt'
      · exfalso
        have : q.dir1 ≠ lμ := by rw [← h.2]; exact ne_of_lt hlt
        simp only [otherOf, h'.2, this, ite_true, ite_false] at he
        rw [h.2] at hlt; rw [h'.2] at hlt'; rw [← he] at hlt'
        exact lt_asymm hlt hlt'
      · have h1 : q.dir1 ≠ lμ := by rw [← h.2]; exact ne_of_lt hlt
        have h1' : q'.dir1 ≠ lμ := by rw [← h'.2]; exact ne_of_lt hlt'
        simp only [otherOf, h1, h1', ite_false] at he
        exact plaq_ext (h.1.trans h'.1.symm) he (h.2.trans h'.2.symm)
  simpa using h

theorem card_slots12_le (l : LatticeLink d N) : (plaqsAtSlot l 1 ∪ plaqsAtSlot l 2).card ≤ d - 1 := by
  obtain ⟨ls, lμ⟩ := l
  have h : (plaqsAtSlot ⟨ls, lμ⟩ 1 ∪ plaqsAtSlot ⟨ls, lμ⟩ 2).card ≤ ((univ : Finset (Fin d)).erase lμ).card := by
    refine card_le_card_of_injOn (otherOf lμ) (fun q hq => ?_) ?_
    · simp only [coe_union, Set.mem_union, mem_coe, plaqsAtSlot, mem_filter, mem_univ, true_and] at hq
      simp only [coe_erase, coe_univ, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      have hlt := q.h_lt
      rcases hq with h | h <;> simp only [LatticePlaquette.boundaryLinks, LatticeLink.mk.injEq] at h
      · have : q.dir1 ≠ lμ := by rw [← h.2]; exact ne_of_lt hlt
        simp only [otherOf, this, ite_false]; exact not_false
      · simp only [otherOf, h.2, ite_true]; intro he; rw [he, ← h.2] at hlt; exact lt_irrefl _ hlt
    · intro q hq q' hq' he
      simp only [coe_union, Set.mem_union, mem_coe, plaqsAtSlot, mem_filter, mem_univ, true_and] at hq hq'
      have hlt := q.h_lt
      have hlt' := q'.h_lt
      rcases hq with h | h <;> rcases hq' with h' | h' <;>
        simp only [LatticePlaquette.boundaryLinks, LatticeLink.mk.injEq] at h h'
      · have h1 : q.dir1 ≠ lμ := by rw [← h.2]; exact ne_of_lt hlt
        have h1' : q'.dir1 ≠ lμ := by rw [← h'.2]; exact ne_of_lt hlt'
        simp only [otherOf, h1, h1', ite_false] at he
        rw [he] at h
        exact plaq_ext (siteShift_injective _ (h.1.trans h'.1.symm)) he (h.2.trans h'.2.symm)
      · exfalso
        have h1 : q.dir1 ≠ lμ := by rw [← h.2]; exact ne_of_lt hlt
        simp only [otherOf, h1, h'.2, ite_true, ite_false] at he
        rw [h.2] at hlt; rw [h'.2] at hlt'; rw [← he] at hlt'
        exact lt_asymm hlt hlt'
      · exfalso
        have h1' : q'.dir1 ≠ lμ := by rw [← h'.2]; exact ne_of_lt hlt'
        simp only [otherOf, h.2, h1', ite_true, ite_false] at he
        rw [h.2] at hlt; rw [h'.2] at hlt'; rw [he] at hlt
        exact lt_asymm hlt hlt'
      · simp only [otherOf, h.2, h'.2, ite_true] at he
        rw [he] at h
        exact plaq_ext (siteShift_injective _ (h.1.trans h'.1.symm)) (h.2.trans h'.2.symm) he
  simpa using h

/-- **A link lies in at most `2(d - 1)` plaquettes.** -/
theorem card_plaqsAt_le (l : LatticeLink d N) : (plaqsAt l).card ≤ 2 * (d - 1) := by
  have hsub : plaqsAt l ⊆ (plaqsAtSlot l 0 ∪ plaqsAtSlot l 3) ∪ (plaqsAtSlot l 1 ∪ plaqsAtSlot l 2) := by
    intro q hq
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 (plaqsAt_subset l hq)
    fin_cases i <;> simp_all
  calc (plaqsAt l).card ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ (d - 1) + (d - 1) := add_le_add (card_slots03_le l) (card_slots12_le l)
    _ = 2 * (d - 1) := by ring

/-- `∑_{e ≠ z} m(e, z) ≤ 6(d - 1)`. -/
theorem sum_common_le (z : LatticeLink d N) :
    ∑ e ∈ univ.filter (fun e => z ∉ ({e} : Finset (LatticeLink d N))), common e z ≤ 6 * (d - 1) := by
  set E := univ.filter (fun e => z ∉ ({e} : Finset (LatticeLink d N)))
  have e1 : ∀ e, common e z = ∑ p : LatticePlaquette d N,
      if (e ∈ plaqLinks p ∧ z ∈ plaqLinks p) then 1 else 0 := by
    intro e; unfold common; rw [card_filter]
  simp_rw [e1]
  rw [sum_comm]
  have e2 : ∀ p : LatticePlaquette d N,
      ∑ e ∈ E, (if (e ∈ plaqLinks p ∧ z ∈ plaqLinks p) then 1 else 0) ≤ if z ∈ plaqLinks p then 3 else 0 := by
    intro p
    rw [← card_filter]
    by_cases hz : z ∈ plaqLinks p
    · rw [show (if z ∈ plaqLinks p then 3 else 0) = 3 by simp [hz]]
      have hsub : E.filter (fun e => e ∈ plaqLinks p ∧ z ∈ plaqLinks p) ⊆ (plaqLinks p).erase z := by
        intro e he
        simp only [E, mem_filter, mem_univ, true_and, mem_singleton] at he
        exact mem_erase.2 ⟨fun h => he.1 h.symm, he.2.1⟩
      calc _ ≤ ((plaqLinks p).erase z).card := card_le_card hsub
        _ = (plaqLinks p).card - 1 := card_erase_of_mem hz
        _ ≤ 3 := by have := card_plaqLinks_le p; omega
    · rw [show (if z ∈ plaqLinks p then 3 else 0) = 0 by simp [hz]]
      simp [hz]
  calc ∑ p : LatticePlaquette d N, ∑ e ∈ E, (if (e ∈ plaqLinks p ∧ z ∈ plaqLinks p) then 1 else 0)
      ≤ ∑ p : LatticePlaquette d N, (if z ∈ plaqLinks p then 3 else 0) := sum_le_sum fun p _ => e2 p
    _ = 3 * (plaqsAt z).card := by
        rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]; rfl
    _ ≤ 3 * (2 * (d - 1)) := Nat.mul_le_mul_left _ (card_plaqsAt_le z)
    _ = 6 * (d - 1) := by ring

/-! ## The single-link specification is a Gibbs measure -/

section Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] {n : ℕ} [HasGaugeTrace G n]

/-- The log-weight `ξ ↦ β ∑_{p ∋ e} Re tr U_p(splice e U ξ)` of the single-link specification. -/
def logW (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (e : LatticeLink d N) (U ξ : GaugeConnection G d N) : ℝ :=
  ∑ p ∈ plaqsAt e, β * xp n p (splice {e} U ξ)

/-- **The conditional law of one link given the others is the Gibbs measure of the TV lemma.** -/
theorem gaugeSpec_single_eq_gibbs (β : ℝ) (e : LatticeLink d N) (U : GaugeConnection G d N) :
    gaugeSpec n (fun x => Real.exp (β * x)) {e} U =
      gibbs (prodMeasure (ι := LatticeLink d N) (haarG G)) (logW n β e U) := by
  have hW : ∀ ξ, plaqProd n (fun x => Real.exp (β * x)) (touching {e}) (splice {e} U ξ) =
      Real.exp (logW n β e U ξ) := by
    intro ξ
    simp only [plaqProd, logW, touching_singleton, Real.exp_sum]
  unfold gaugeSpec locSpec gibbs partitionFn locZ
  simp_rw [hW]

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

/-- The changing part: plaquettes through `e` and `z`. -/
def fPart (n : ℕ) [HasGaugeTrace G n] (e z : LatticeLink d N) (U ξ : GaugeConnection G d N) : ℝ :=
  ∑ p ∈ (plaqsAt e).filter (fun p => z ∈ plaqLinks p), xp n p (splice {e} U ξ)

/-- The common part: plaquettes through `e` but not `z`. -/
def psiPart (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (e z : LatticeLink d N) (U ξ : GaugeConnection G d N) : ℝ :=
  ∑ p ∈ (plaqsAt e).filter (fun p => z ∉ plaqLinks p), β * xp n p (splice {e} U ξ)

theorem logW_eq (β : ℝ) (e z : LatticeLink d N) (U : GaugeConnection G d N) :
    logW n β e U = fun ξ => β * fPart n e z U ξ + psiPart n β e z U ξ := by
  funext ξ
  unfold logW fPart psiPart
  rw [mul_sum, sum_filter_add_sum_filter_not]

theorem psiPart_update {e z : LatticeLink d N} (hz : z ∉ ({e} : Finset (LatticeLink d N))) (β : ℝ)
    (U : GaugeConnection G d N) (s : G) : psiPart n β e z (Function.update U z s) = psiPart n β e z U := by
  funext ξ
  unfold psiPart
  refine sum_congr rfl fun p hp => ?_
  simp only [mem_filter] at hp
  rw [splice_update_left hz]
  have hx : xp n p (Function.update (splice {e} U ξ) z s) = xp n p (splice {e} U ξ) := by
    unfold xp
    congr 1
    refine plaquetteHolonomy_dependsOn p _ _ fun l hl => ?_
    have : l ≠ z := fun h => hp.2 (h ▸ hl)
    simp [Function.update_of_ne this]
  rw [hx]

theorem card_filter_eq_common (e z : LatticeLink d N) :
    ((plaqsAt e).filter (fun p => z ∈ plaqLinks p)).card = common e z := by
  unfold common plaqsAt
  rw [filter_filter]

include hU in
theorem abs_fPart_le (e z : LatticeLink d N) (U ξ : GaugeConnection G d N) :
    |fPart n e z U ξ| ≤ (common e z : ℝ) * n := by
  unfold fPart
  rw [← card_filter_eq_common]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ (plaqsAt e).filter (fun p => z ∈ plaqLinks p), |xp n p (splice {e} U ξ)|
      ≤ ∑ _p ∈ (plaqsAt e).filter (fun p => z ∈ plaqLinks p), (n : ℝ) :=
        sum_le_sum fun p _ => abs_xp_le hU p _
    _ = _ := by rw [sum_const, nsmul_eq_mul]

include hU in
theorem abs_logW_le (β : ℝ) (e : LatticeLink d N) (U ξ : GaugeConnection G d N) :
    |logW n β e U ξ| ≤ (plaqsAt e).card * (|β| * n) := by
  unfold logW
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ plaqsAt e, |β * xp n p (splice {e} U ξ)| ≤ ∑ _p ∈ plaqsAt e, |β| * n :=
        sum_le_sum fun p _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_xp_le hU p _) (abs_nonneg _)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

include hU in
theorem abs_psiPart_le (β : ℝ) (e z : LatticeLink d N) (U ξ : GaugeConnection G d N) :
    |psiPart n β e z U ξ| ≤ (plaqsAt e).card * (|β| * n) := by
  unfold psiPart
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ p ∈ (plaqsAt e).filter (fun p => z ∉ plaqLinks p), |β * xp n p (splice {e} U ξ)|
      ≤ ∑ _p ∈ plaqsAt e, |β| * n := by
        refine (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => abs_nonneg _).trans ?_
        exact sum_le_sum fun p _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_xp_le hU p _) (abs_nonneg _)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

include hc in
theorem measurable_fPart (e z : LatticeLink d N) (U : GaugeConnection G d N) : Measurable (fPart n e z U) :=
  Finset.measurable_sum _ fun p _ => (measurable_xp hc p).comp (measurable_splice_right {e} U)

include hc in
theorem measurable_psiPart (β : ℝ) (e z : LatticeLink d N) (U : GaugeConnection G d N) :
    Measurable (psiPart n β e z U) :=
  Finset.measurable_sum _ fun p _ => measurable_const.mul ((measurable_xp hc p).comp (measurable_splice_right {e} U))

include hc in
theorem measurable_logW (β : ℝ) (e : LatticeLink d N) (U : GaugeConnection G d N) : Measurable (logW n β e U) :=
  Finset.measurable_sum _ fun p _ => measurable_const.mul ((measurable_xp hc p).comp (measurable_splice_right {e} U))

include hc hU in
/-- **Influence of a neighbour on one link** (Proposition 8.1): for `z ≠ e` and `β ≥ 0`,
`k_{e}(z) = tanh(m(e, z) n β)` is an influence bound for the single-link specification of the Wilson measure. -/
theorem influence_single {β : ℝ} (hβ : 0 ≤ β) (e z : LatticeLink d N) (hz : z ∉ ({e} : Finset (LatticeLink d N))) :
    IsInfluenceBound {e} (gaugeSpec (G := G) n (fun x => Real.exp (β * x)) {e}) z
      (Real.tanh (common e z * n * β)) := by
  intro U s F L hF hdep hosc
  set U' := Function.update U z s
  set π := prodMeasure (ι := LatticeLink d N) (haarG G)
  rw [gaugeSpec_single_eq_gibbs, gaugeSpec_single_eq_gibbs]
  have hL : 0 ≤ L := by
    have := hosc U e (U e) (mem_singleton_self e)
    rw [Function.update_eq_self, sub_self, abs_zero] at this
    exact this
  have hD : ∀ x y, F x - F y ≤ L := by
    intro x y
    have : F y = F (Function.update x e (y e)) := by
      apply hdep
      intro i hi
      rw [mem_singleton] at hi
      subst hi
      simp
    rw [this]
    exact (le_abs_self _).trans (hosc x e (y e) (mem_singleton_self e))
  obtain ⟨C, hC⟩ := hF.bdd
  -- the two TV bounds, from the TV lemma with the `m(e, z)` changing plaquettes
  have hψ : psiPart n β e z U' = psiPart n β e z U := psiPart_update hz β U s
  have htv : ∀ V V' : GaugeConnection G d N, psiPart n β e z V' = psiPart n β e z V →
      tv (gibbs π (logW n β e V)) (gibbs π (logW n β e V')) ≤ Real.tanh (common e z * n * β) := by
    intro V V' hVV'
    rw [logW_eq β e z V, logW_eq β e z V', hVV']
    have := tv_single_link_le_tanh π (measurable_fPart hc e z V) (measurable_fPart hc e z V')
      (measurable_psiPart hc β e z V) (n := (common e z : ℝ) * n) hβ (abs_fPart_le hU e z V)
      (abs_fPart_le hU e z V') (abs_psiPart_le hU β e z V)
    simpa [mul_assoc] using this
  have h1 := htv U U' hψ
  have h2 := htv U' U hψ.symm
  have := abs_integral_gibbs_sub_le π (measurable_logW hc β e U) (measurable_logW hc β e U')
    (abs_logW_le hU β e U) (abs_logW_le hU β e U') hF.meas hC hL hD h1 h2
  rwa [mul_comm] at this

/-- The single-link influence coefficients `k_e(z) = tanh(m(e, z) n β)`. -/
def kSingle (n : ℕ) (β : ℝ) (e z : LatticeLink d N) : ℝ := Real.tanh (common e z * n * β)

/-- **GDS for single links with `γ = 6(d - 1) tanh(n β)`** (Proposition 8.1). -/
theorem gds_single {β : ℝ} (hβ : 0 ≤ β) :
    GDS (fun e : LatticeLink d N => ({e} : Finset (LatticeLink d N))) (kSingle (d := d) (N := N) n β)
      (((6 * (d - 1) : ℕ) : ℝ) * Real.tanh (n * β)) := by
  intro z
  have hcov : coverage (fun e : LatticeLink d N => ({e} : Finset (LatticeLink d N))) z = 1 := by
    unfold coverage
    rw [card_eq_one]
    exact ⟨z, by ext e; simp [eq_comm]⟩
  rw [hcov, Nat.cast_one, mul_one]
  have hnb : 0 ≤ (n : ℝ) * β := mul_nonneg (Nat.cast_nonneg _) hβ
  have ht0 := tanh_nonneg hnb
  calc ∑ e ∈ univ.filter (fun e => z ∉ ({e} : Finset (LatticeLink d N))), kSingle n β e z
      ≤ ∑ e ∈ univ.filter (fun e => z ∉ ({e} : Finset (LatticeLink d N))), (common e z : ℝ) * Real.tanh (n * β) :=
        sum_le_sum fun e _ => by
          unfold kSingle
          rw [mul_assoc]
          exact tanh_nat_mul_le hnb _
    _ = (∑ e ∈ univ.filter (fun e => z ∉ ({e} : Finset (LatticeLink d N))), (common e z : ℝ)) *
          Real.tanh (n * β) := by rw [sum_mul]
    _ ≤ ((6 * (d - 1) : ℕ) : ℝ) * Real.tanh (n * β) := by
        refine mul_le_mul_of_nonneg_right ?_ ht0
        rw [← Nat.cast_sum]
        exact_mod_cast sum_common_le z

/-- A rate `λ > 0` with `γ e^{λ} < 1` exists whenever `0 ≤ γ < 1`. -/
theorem exists_rate {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < 1) : ∃ lam : ℝ, 0 < lam ∧ γ * Real.exp lam < 1 := by
  refine ⟨Real.log (2 / (1 + γ)), Real.log_pos (by rw [lt_div_iff₀ (by linarith)]; linarith), ?_⟩
  rw [Real.exp_log (div_pos two_pos (by linarith)), mul_div_assoc', div_lt_one (by linarith)]
  linarith

include hc hU in
/-- **Theorem A for the Wilson torus measure at strong coupling** (Proposition 8.1 with Theorem A, H variant).
Single-link blocks, `β ≥ 0`, any distance on links with `dist e e = 0`, the triangle inequality, and links sharing a
plaquette at distance `≤ 1`. If `γ = 6(d - 1) tanh(n β)` and `λ ≥ 0` satisfy `γ e^{λ} < 1`, then for bounded
measurable `f` (depending on `A`, `δ_a(f) ≤ v_a`) and `g` (depending on `S_g`, `δ_x(g) ≤ L_g`), with
`R ≤ dist(a, s)` on `A × S_g`:
`|μ(f g) - μ(f) μ(g)| ≤ (1 - γ e^{λ})⁻¹ · ∑_{a ∈ A} v_a · L_g · e^{-λ R}`,
uniformly in the torus size `N`. -/
theorem wilson_singleLink_decay [NeZero d] {β : ℝ} (hβ : 0 ≤ β)
    (dist : LatticeLink d N → LatticeLink d N → ℝ) (hd0 : ∀ x, dist x x = 0)
    (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    (hnb : ∀ (e z : LatticeLink d N) (p : LatticePlaquette d N), e ∈ plaqLinks p → z ∈ plaqLinks p → dist z e ≤ 1)
    {lam : ℝ} (hlam : 0 ≤ lam) (hρ : ((6 * (d - 1) : ℕ) : ℝ) * Real.tanh (n * β) * Real.exp lam < 1)
    {f g : GaugeConnection G d N → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset (LatticeLink d N)}
    (hfA : DepOn f A) (hgS : DepOn g Sg) {vf : LatticeLink d N → ℝ} (hvf : OscBound f vf) {Lg : ℝ}
    (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg)) {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ U, f U * g U ∂(gaugeMeasure n (fun x => Real.exp (β * x))) -
        (∫ U, f U ∂(gaugeMeasure n (fun x => Real.exp (β * x)))) *
          ∫ U, g U ∂(gaugeMeasure n (fun x => Real.exp (β * x)))| ≤
      (1 - ((6 * (d - 1) : ℕ) : ℝ) * Real.tanh (n * β) * Real.exp lam)⁻¹ * (∑ a ∈ A, vf a) * Lg *
        Real.exp (-(lam * R)) := by
  have := isProbabilityMeasure_gaugeMeasure (d := d) (N := N) hc hU (posWeight_exp n β)
  have : Nonempty (LatticeLink d N) := ⟨⟨fun _ => 0, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩⟩
  set P := gaugeBlockSpec (d := d) (N := N) hc hU (posWeight_exp n β)
    (fun e : LatticeLink d N => ({e} : Finset (LatticeLink d N)))
  have hk : ∀ j z, z ∉ P.block j → IsInfluenceBound (P.block j) (P.spec j) z (kSingle n β j z) :=
    fun j z hz => influence_single hc hU hβ j z hz
  have hγ0 : 0 ≤ ((6 * (d - 1) : ℕ) : ℝ) * Real.tanh (n * β) :=
    mul_nonneg (Nat.cast_nonneg _) (tanh_nonneg (mul_nonneg (Nat.cast_nonneg _) hβ))
  have hcov : ∀ x, coverage P.block x = 1 := by
    intro x
    unfold coverage
    rw [card_eq_one]
    exact ⟨x, by ext e; simp [P, gaugeBlockSpec_block, eq_comm]⟩
  have h := P.theoremA_H (kSingle n β) hk hγ0 (gds_single hβ) (cmin := 1) (cmax := 1) (b := 1) le_rfl
    (fun x => (hcov x).ge) (fun x => (hcov x).le) (fun j => by simp [P, gaugeBlockSpec_block])
    dist hd0 htri (D₀ := 0) (D₁ := 1)
    (fun j x hx y hy => by
      simp only [P, gaugeBlockSpec_block, mem_singleton] at hx hy
      rw [hx, hy, hd0])
    (fun j x y hx hy hkx => by
      simp only [P, gaugeBlockSpec_block, mem_singleton] at hx hy
      rw [hy]
      have hm : common j x ≠ 0 := by
        intro h0
        apply hkx
        simp [kSingle, h0]
      obtain ⟨p, hp⟩ := card_ne_zero.1 hm
      simp only [mem_filter, mem_univ, true_and] at hp
      exact hnb j x p hp.1 hp.2)
    hlam (by rwa [mul_one]) hf hg hfA hgS hvf hLg hvg hR
  refine h.trans (le_of_eq ?_)
  simp only [Nat.cast_one, one_mul, mul_one, sub_zero, one_div]

end Measure

end OneScale.SingleLink
