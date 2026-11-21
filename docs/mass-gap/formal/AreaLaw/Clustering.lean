/-
Exponential clustering (the strong-coupling mass gap) for lattice gauge theory (area-law project, 2026-11-21). Released under
Apache 2.0.

Proof idea as in B. G. Srivats, fisher-lorentz-formalization, Confinement/Clustering.lean; written independently here, in this
project's framework (`AreaLaw.Lattice`, `productHaar`, `LinkDep`, `Integrals`, the plaquette graph and the animal bound).

# Statement

For any group `G` with a probability measure on a link and a representation with `|Re tr| ≤ n` (no centre and no invariance of
the measure are needed), any `β`, and bounded measurable observables `f`, `g` (`|f|, |g| ≤ 1`) depending on disjoint link sets
`L_F`, `L_G`, whose touching plaquettes are at distance at least `r` in the plaquette graph:

  |⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ 2 |R_F| · p · q^r / (1 − q),   p = 1 − e^{−4n|β|},  q = Δ² p < 1,

with `R_F` the plaquettes touching `L_F` and `Δ` a degree bound of the plaquette graph (`16 d`, so the window is
`(16d)² (1 − e^{−4n|β|}) < 1`). `⟨·⟩` is the normalised Wilson measure, as in the area law. Nothing depends on the lattice size.

# Proof

1. **Two independent copies** (`two_copies_weighted`, `cov_two_copies`): `Z N_{fg} − N_f N_g = ½ ∫∫ (f(U) − f(V)) (g(U) − g(V))
   W(U) W(V)`, with `W` the Wilson weight.
2. Store the pair `(U, V)` link by link (`Dup`, `dupMeasure`). The weight of plaquette `p` in both copies is `e^{−2n|β|} (1 + h_p)`
   with `0 ≤ h_p ≤ p (1 + h_p)` (`hP`). Expand `∏ (1 + h_p)` over plaquette sets `A`.
3. **Exchange** (`term_vanish`): let `K` be the plaquettes of `A` joined inside `A` to a plaquette touching `L_F` and `C` the links
   of `L_F` and of `K`. If `K` touches no link of `L_G`, exchanging the copies on `C` (`swapOn`, measure preserving) flips the
   sign of `f(U) − f(V)` and leaves everything else in the term unchanged, so the term is zero.
4. **Counting** (`sum_joining_pow_le`): a surviving `A` contains a connected set of plaquettes meeting both `R_F` and `R_G`; it has
   at least `r + 1` plaquettes, and `∑_{A ⊇ X} ∏_A h ≤ p^{|X|} ∏ (1 + h)`. The animal bound (`sum_animals_le`) sums the rest.

The theorem is the strong-coupling regime only (known physics, Osterwalder–Seiler 1978); it says nothing about weak coupling or the
continuum limit.
-/

import AreaLaw.Concrete

open scoped Classical

open Finset MeasureTheory SimpleGraph Balaban.Polymer AreaLaw.Assembly

set_option linter.unusedSectionVars false

noncomputable section

namespace AreaLaw.Clustering

/-! ## 1. Two independent copies -/

section TwoCopies

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **Two independent copies, with a weight.** For integrable `w`, `F w`, `G w`, `F G w`:
    `∫∫ (F x − F y)(G x − G y) w x w y = 2 (∫ w · ∫ F G w − ∫ F w · ∫ G w)`. -/
theorem two_copies_weighted (F G w : Ω → ℝ) (hw : Integrable w μ) (hFw : Integrable (fun x => F x * w x) μ)
    (hGw : Integrable (fun x => G x * w x) μ) (hFGw : Integrable (fun x => F x * G x * w x) μ) :
    ∫ z, (F z.1 - F z.2) * (G z.1 - G z.2) * (w z.1 * w z.2) ∂(μ.prod μ) =
      2 * ((∫ x, w x ∂μ) * (∫ x, F x * G x * w x ∂μ) - (∫ x, F x * w x ∂μ) * (∫ x, G x * w x ∂μ)) := by
  have i1 : Integrable (fun z : Ω × Ω => F z.1 * G z.1 * w z.1 * w z.2) (μ.prod μ) := hFGw.mul_prod hw
  have i2 : Integrable (fun z : Ω × Ω => F z.1 * w z.1 * (G z.2 * w z.2)) (μ.prod μ) := hFw.mul_prod hGw
  have i3 : Integrable (fun z : Ω × Ω => G z.1 * w z.1 * (F z.2 * w z.2)) (μ.prod μ) := hGw.mul_prod hFw
  have i4 : Integrable (fun z : Ω × Ω => w z.1 * (F z.2 * G z.2 * w z.2)) (μ.prod μ) := hw.mul_prod hFGw
  have e1 : ∫ z, F z.1 * G z.1 * w z.1 * w z.2 ∂(μ.prod μ) = (∫ x, F x * G x * w x ∂μ) * ∫ x, w x ∂μ :=
    integral_prod_mul (fun x => F x * G x * w x) w
  have e2 : ∫ z, F z.1 * w z.1 * (G z.2 * w z.2) ∂(μ.prod μ) = (∫ x, F x * w x ∂μ) * ∫ x, G x * w x ∂μ :=
    integral_prod_mul (fun x => F x * w x) (fun x => G x * w x)
  have e3 : ∫ z, G z.1 * w z.1 * (F z.2 * w z.2) ∂(μ.prod μ) = (∫ x, G x * w x ∂μ) * ∫ x, F x * w x ∂μ :=
    integral_prod_mul (fun x => G x * w x) (fun x => F x * w x)
  have e4 : ∫ z, w z.1 * (F z.2 * G z.2 * w z.2) ∂(μ.prod μ) = (∫ x, w x ∂μ) * ∫ x, F x * G x * w x ∂μ :=
    integral_prod_mul w (fun x => F x * G x * w x)
  have hexp : (fun z : Ω × Ω => (F z.1 - F z.2) * (G z.1 - G z.2) * (w z.1 * w z.2)) =
      fun z => F z.1 * G z.1 * w z.1 * w z.2 - F z.1 * w z.1 * (G z.2 * w z.2) - G z.1 * w z.1 * (F z.2 * w z.2)
        + w z.1 * (F z.2 * G z.2 * w z.2) := funext fun z => by ring
  have i12 : Integrable (fun z : Ω × Ω => F z.1 * G z.1 * w z.1 * w z.2 - F z.1 * w z.1 * (G z.2 * w z.2))
      (μ.prod μ) := i1.sub i2
  have i123 : Integrable (fun z : Ω × Ω => F z.1 * G z.1 * w z.1 * w z.2 - F z.1 * w z.1 * (G z.2 * w z.2)
      - G z.1 * w z.1 * (F z.2 * w z.2)) (μ.prod μ) := i12.sub i3
  rw [hexp, integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2, e1, e2, e3, e4]
  ring

/-- **Two independent copies.** For a probability measure: `Cov(f, g) = ½ E[(f − f')(g − g')]`, where `(x, y)` are two
    independent samples (the product measure `μ × μ`). -/
theorem cov_two_copies (f g : Ω → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) - (∫ x, f x ∂μ) * (∫ x, g x ∂μ) =
      (1 / 2) * ∫ z, (f z.1 - f z.2) * (g z.1 - g z.2) ∂(μ.prod μ) := by
  have h := two_copies_weighted μ f g (fun _ => 1) (integrable_const 1) (by simpa using hf) (by simpa using hg)
    (by simpa using hfg)
  simp only [mul_one, integral_const, probReal_univ, one_smul, one_mul] at h
  rw [h]; ring

end TwoCopies

/-! ## 2. Doubled link configurations and the exchange -/

section Dup

variable {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G] {d N : ℕ} [Fintype (LatticeLink d N)]

/-- Two configurations, stored link by link. -/
abbrev Dup (G : Type*) (d N : ℕ) := LatticeLink d N → G × G

/-- The law of two independent configurations. -/
def dupMeasure (G : Type*) [MeasurableSpace G] [HasHaarProbability G] (d N : ℕ) [Fintype (LatticeLink d N)] :
    Measure (Dup G d N) :=
  Measure.pi (fun _ => (haarG G).prod (haarG G))

instance : IsProbabilityMeasure (dupMeasure G d N) := by unfold dupMeasure; infer_instance

/-- The first configuration. -/
def fstC (ω : Dup G d N) : GaugeConnection G d N := fun l => (ω l).1

/-- The second configuration. -/
def sndC (ω : Dup G d N) : GaugeConnection G d N := fun l => (ω l).2

theorem measurable_fstC : Measurable (fstC (G := G) (d := d) (N := N)) :=
  measurable_pi_iff.mpr fun l => measurable_fst.comp (measurable_pi_apply l)

theorem measurable_sndC : Measurable (sndC (G := G) (d := d) (N := N)) :=
  measurable_pi_iff.mpr fun l => measurable_snd.comp (measurable_pi_apply l)

/-- Integrals over the doubled configuration are integrals over two independent copies of `productHaar`. -/
theorem integral_dup (Ψ : GaugeConnection G d N × GaugeConnection G d N → ℝ) :
    ∫ ω, Ψ (fstC ω, sndC ω) ∂(dupMeasure G d N) =
      ∫ z, Ψ z ∂((productHaar G d N).prod (productHaar G d N)) :=
  (measurePreserving_arrowProdEquivProdArrow G G (LatticeLink d N) (fun _ => haarG G)
    (fun _ => haarG G)).integral_comp' Ψ

/-- Exchange the two configurations on the links of `C`. -/
def swapOn (C : Finset (LatticeLink d N)) (ω : Dup G d N) : Dup G d N :=
  fun l => (if l ∈ C then Prod.swap else id) (ω l)

theorem fstC_swapOn (C : Finset (LatticeLink d N)) (ω : Dup G d N) (l : LatticeLink d N) :
    fstC (swapOn C ω) l = if l ∈ C then sndC ω l else fstC ω l := by
  unfold fstC sndC swapOn; split_ifs <;> rfl

theorem sndC_swapOn (C : Finset (LatticeLink d N)) (ω : Dup G d N) (l : LatticeLink d N) :
    sndC (swapOn C ω) l = if l ∈ C then fstC ω l else sndC ω l := by
  unfold fstC sndC swapOn; split_ifs <;> rfl

/-- The exchange preserves the law of the two copies. -/
theorem measurePreserving_swapOn (C : Finset (LatticeLink d N)) :
    MeasurePreserving (swapOn (G := G) C) (dupMeasure G d N) (dupMeasure G d N) := by
  refine measurePreserving_pi (fun _ => (haarG G).prod (haarG G)) (fun _ => (haarG G).prod (haarG G)) (fun l => ?_)
  split_ifs
  · exact Measure.measurePreserving_swap
  · exact MeasurePreserving.id _

/-- An integrand that changes sign under an exchange integrates to zero. -/
theorem integral_eq_zero_of_swap_odd (C : Finset (LatticeLink d N)) (Ψ : Dup G d N → ℝ) (hΨ : Measurable Ψ)
    (hodd : ∀ ω, Ψ (swapOn C ω) = -Ψ ω) : ∫ ω, Ψ ω ∂(dupMeasure G d N) = 0 := by
  have hmp := measurePreserving_swapOn (G := G) C
  have h1 : ∫ ω, Ψ ω ∂(dupMeasure G d N) = ∫ ω, Ψ (swapOn C ω) ∂(dupMeasure G d N) := by
    conv_lhs => rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable hΨ.aestronglyMeasurable
  simp_rw [hodd, integral_neg] at h1
  linarith

end Dup

/-! ## 3. Combinatorics on the plaquette graph -/

section Comb

variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)

/-- The connected sets meeting both `RF` and `RG`. -/
def joining (RF RG : Finset V) : Finset (BlockPolymer H) :=
  univ.filter (fun X => (X.1 ∩ RF).Nonempty ∧ (X.1 ∩ RG).Nonempty)

/-- A connected set meeting `RF` and `RG`, at distance at least `r`, has at least `r + 1` vertices. -/
theorem card_joining_ge {RF RG : Finset V} {r : ℕ} (hr : ∀ a ∈ RF, ∀ b ∈ RG, r ≤ H.dist a b)
    {X : BlockPolymer H} (hX : X ∈ joining H RF RG) : r + 1 ≤ X.1.card := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (mem_filter.mp hX).2
  rw [mem_inter] at ha hb
  obtain ⟨w, hw⟩ := walkIn_of_isAnimal H X.2 ha.1 hb.1
  have hpath := w.bypass_isPath
  have hsub : w.bypass.support.toFinset ⊆ X.1 := fun v hv =>
    hw v (w.support_bypass_subset_support (List.mem_toFinset.mp hv))
  have hcard : w.bypass.support.toFinset.card = w.bypass.length + 1 := by
    rw [List.toFinset_card_of_nodup hpath.support_nodup, Walk.length_support]
  have h1 := card_le_card hsub
  have h2 := (hr a ha.2 b hb.2).trans (dist_le w.bypass)
  omega

/-- A set `A` whose part joined to `RF` meets `RG` contains a connected set meeting both. -/
theorem exists_joining_of_not_disjoint {RF RG A : Finset V}
    (hA : ¬ Disjoint (splitOff (G := H) (RF : Set V) A) RG) : ∃ X ∈ joining H RF RG, X.1 ⊆ A := by
  obtain ⟨q, hqK, hqG⟩ := not_disjoint_iff.mp hA
  simp only [splitOff, mem_filter] at hqK
  obtain ⟨hqA, w, hw, hqw⟩ := hqK
  refine ⟨⟨compOf H A q, isAnimal_compOf H hqA⟩, mem_filter.mpr ⟨mem_univ _, ⟨w, ?_⟩, ⟨q, ?_⟩⟩,
    compOf_subset H A q⟩
  · exact mem_inter.mpr ⟨(mem_compOf H).mpr ⟨hqw.mem_right, hqw⟩, by simpa using hw⟩
  · exact mem_inter.mpr ⟨self_mem_compOf H hqA, hqG⟩

/-- Sums over the sets `A` whose part joined to `RF` meets `RG` are dominated by sums over supersets of joining sets. -/
theorem sum_joining_le_sum (RF RG : Finset V) (I : Finset V → ℝ) (hI : ∀ A, 0 ≤ I A) :
    ∑ A ∈ (univ : Finset V).powerset.filter (fun A => ¬ Disjoint (splitOff (G := H) (RF : Set V) A) RG), I A ≤
      ∑ X ∈ joining H RF RG, ∑ A ∈ (univ : Finset V).powerset.filter (fun A => X.1 ⊆ A), I A := by
  have hite : ∀ (A : Finset V) (X : BlockPolymer H), 0 ≤ (if X.1 ⊆ A then I A else 0) := fun A X => by
    split_ifs <;> [exact hI A; exact le_rfl]
  calc ∑ A ∈ (univ : Finset V).powerset.filter (fun A => ¬ Disjoint (splitOff (G := H) (RF : Set V) A) RG), I A
      ≤ ∑ A ∈ (univ : Finset V).powerset.filter (fun A => ¬ Disjoint (splitOff (G := H) (RF : Set V) A) RG),
          ∑ X ∈ joining H RF RG, (if X.1 ⊆ A then I A else 0) := by
        refine sum_le_sum fun A hA => ?_
        obtain ⟨X, hX, hXA⟩ := exists_joining_of_not_disjoint H (mem_filter.mp hA).2
        calc I A = (if X.1 ⊆ A then I A else 0) := by rw [if_pos hXA]
          _ ≤ _ := single_le_sum (f := fun X : BlockPolymer H => if X.1 ⊆ A then I A else 0)
              (fun X _ => hite A X) hX
    _ ≤ ∑ A ∈ (univ : Finset V).powerset, ∑ X ∈ joining H RF RG, (if X.1 ⊆ A then I A else 0) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun A _ _ => sum_nonneg fun X _ => hite A X
    _ = ∑ X ∈ joining H RF RG, ∑ A ∈ (univ : Finset V).powerset, (if X.1 ⊆ A then I A else 0) := sum_comm
    _ = _ := sum_congr rfl fun X _ => by rw [sum_filter]

/-- `∑_{A ⊇ X} ∏_A h ≤ p^{|X|} ∏ (1 + h)` when `0 ≤ h ≤ p (1 + h)`. -/
theorem sum_superset_le (h : V → ℝ) {p : ℝ} (h0 : ∀ v, 0 ≤ h v) (hle : ∀ v, h v ≤ p * (1 + h v)) (X : Finset V) :
    ∑ A ∈ (univ : Finset V).powerset.filter (fun A => X ⊆ A), ∏ v ∈ A, h v ≤
      p ^ X.card * ∏ v, (1 + h v) := by
  have key : ∑ A ∈ (univ : Finset V).powerset.filter (fun A => X ⊆ A), ∏ v ∈ A, h v =
      ∏ v, (h v + if v ∈ X then 0 else 1) := by
    rw [prod_add, sum_filter]
    refine sum_congr rfl fun A _ => ?_
    by_cases hXA : X ⊆ A
    · have h1 : ∏ v ∈ univ \ A, (if v ∈ X then (0 : ℝ) else 1) = 1 :=
        prod_eq_one fun v hv => by rw [if_neg (fun hvX => (mem_sdiff.mp hv).2 (hXA hvX))]
      rw [if_pos hXA, h1, mul_one]
    · obtain ⟨v, hvX, hvA⟩ := not_subset.mp hXA
      have h1 : ∏ v ∈ univ \ A, (if v ∈ X then (0 : ℝ) else 1) = 0 :=
        prod_eq_zero (i := v) (mem_sdiff.mpr ⟨mem_univ _, hvA⟩) (by rw [if_pos hvX])
      rw [if_neg hXA, h1, mul_zero]
  rw [key]
  calc ∏ v, (h v + if v ∈ X then 0 else 1) ≤ ∏ v, ((if v ∈ X then p else 1) * (1 + h v)) := by
        refine prod_le_prod₀ (fun v _ => by have := h0 v; split_ifs <;> linarith) (fun v _ => ?_)
        have := hle v
        split_ifs <;> linarith
    _ = p ^ X.card * ∏ v, (1 + h v) := by
        rw [prod_mul_distrib, prod_ite_mem, univ_inter, prod_const]

/-- `∑_{n < M, n ≥ r} q^n ≤ q^r / (1 − q)`. -/
theorem sum_tail_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (r M : ℕ) :
    ∑ n ∈ range M, (if r ≤ n then q ^ n else 0) ≤ q ^ r / (1 - q) := by
  rw [← sum_filter]
  have hf : (range M).filter (fun n => r ≤ n) = Ico r M := by
    ext n; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [hf, sum_Ico_eq_sum_range]
  simp_rw [pow_add]
  rw [← mul_sum, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left
    (sum_le_hasSum _ (fun i _ => by positivity) (hasSum_geometric_of_lt_one hq0 hq1)) (by positivity)

/-- **The count of joining sets.** `∑_{X joining} p^{|X|} ≤ |RF| · p q^r / (1 − q)`, `q = Δ² p`. -/
theorem sum_joining_pow_le {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) (RF RG : Finset V) {p : ℝ} (hp0 : 0 ≤ p)
    (hq : (Δ : ℝ) ^ 2 * p < 1) {r : ℕ} (hr : ∀ a ∈ RF, ∀ b ∈ RG, r ≤ H.dist a b) :
    ∑ X ∈ joining H RF RG, p ^ X.1.card ≤ RF.card * (p * ((Δ : ℝ) ^ 2 * p) ^ r / (1 - (Δ : ℝ) ^ 2 * p)) := by
  set q : ℝ := (Δ : ℝ) ^ 2 * p with hqdef
  have hq0 : 0 ≤ q := by positivity
  set f : ℕ → ℝ := fun m => if r + 1 ≤ m then p ^ m else 0 with hfdef
  have hf0 : ∀ m, 0 ≤ f m := fun m => by simp only [hfdef]; split_ifs <;> positivity
  have hterm0 : ∀ (a : V) (X : BlockPolymer H), 0 ≤ (if a ∈ X.1 then f X.1.card else 0) := fun a X => by
    split_ifs <;> [exact hf0 _; exact le_rfl]
  have hinner : ∑ n ∈ range (Fintype.card V), (Δ : ℝ) ^ (2 * n) * f (n + 1) ≤ p * q ^ r / (1 - q) := by
    have he : ∀ n, (Δ : ℝ) ^ (2 * n) * f (n + 1) = p * (if r ≤ n then q ^ n else 0) := by
      intro n
      simp only [hfdef, hqdef]
      by_cases hn : r ≤ n
      · rw [if_pos (by omega), if_pos hn, mul_pow, pow_mul, pow_succ]; ring
      · rw [if_neg (by omega), if_neg hn]; ring
    simp_rw [he]
    rw [← mul_sum, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (sum_tail_le hq0 hq r _) hp0
  calc ∑ X ∈ joining H RF RG, p ^ X.1.card
      ≤ ∑ X ∈ joining H RF RG, ∑ a ∈ RF, (if a ∈ X.1 then f X.1.card else 0) := by
        refine sum_le_sum fun X hX => ?_
        obtain ⟨⟨a, ha⟩, -⟩ := (mem_filter.mp hX).2
        rw [mem_inter] at ha
        have hc := card_joining_ge H hr hX
        calc p ^ X.1.card = (if a ∈ X.1 then f X.1.card else 0) := by
              rw [if_pos ha.1]; simp only [hfdef]; rw [if_pos hc]
          _ ≤ _ := single_le_sum (f := fun a => if a ∈ X.1 then f X.1.card else 0)
              (fun a _ => hterm0 a X) ha.2
    _ ≤ ∑ X : BlockPolymer H, ∑ a ∈ RF, (if a ∈ X.1 then f X.1.card else 0) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun X _ _ => sum_nonneg fun a _ => hterm0 a X
    _ = ∑ a ∈ RF, ∑ X : BlockPolymer H, (if a ∈ X.1 then f X.1.card else 0) := sum_comm
    _ ≤ ∑ _a ∈ RF, p * q ^ r / (1 - q) :=
        sum_le_sum fun a _ => le_trans (le_of_eq (sum_congr rfl fun X _ => by split_ifs <;> rfl))
          ((sum_animals_le H hdeg a f hf0).trans hinner)
    _ = RF.card * (p * q ^ r / (1 - q)) := by rw [sum_const, nsmul_eq_mul]

end Comb

/-! ## 4. The lattice -/

section Lattice

variable {d N : ℕ} [Fintype (LatticePlaquette d N)]

/-- The plaquettes containing a link of `L`. -/
def touchPlaqs (L : Finset (LatticeLink d N)) : Finset (LatticePlaquette d N) :=
  univ.filter (fun p => (plaqLinks p ∩ L).Nonempty)

theorem mem_touchPlaqs {L : Finset (LatticeLink d N)} {p : LatticePlaquette d N} :
    p ∈ touchPlaqs L ↔ (plaqLinks p ∩ L).Nonempty := by simp [touchPlaqs]

/-- At most `4 d` plaquettes per link. -/
theorem card_touchPlaqs_le (L : Finset (LatticeLink d N)) : (touchPlaqs L).card ≤ 4 * d * L.card := by
  refine le_trans (card_le_card ?_) (AreaLaw.Concrete.card_biUnion_plaqsAt_le L)
  intro q hq
  obtain ⟨l, hl⟩ := mem_touchPlaqs.mp hq
  rw [mem_inter] at hl
  exact mem_biUnion.mpr ⟨l, hl.2, by simp [AreaLaw.Concrete.plaqsAt, hl.1]⟩

variable {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G] {n : ℕ} [HasGaugeTrace G n]
  [Fintype (LatticeLink d N)]

/-- The normalised Wilson expectation `∫ F ∏_p e^{β x_p} / ∫ ∏_p e^{β x_p}`, as in the area law. -/
def wilsonExpect (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (F : GaugeConnection G d N → ℝ) : ℝ :=
  (∫ U, F U * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N)) /
    (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N))

/-- The weight of plaquette `p` in both copies, minus one, normalised to be `≥ 0`:
    `e^{β x_p(U) + β x_p(V) + 2 n |β|} − 1`. -/
def hP (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (p : LatticePlaquette d N) (ω : Dup G d N) : ℝ :=
  Real.exp (β * xp n p (fstC ω) + β * xp n p (sndC ω) + 2 * n * |β|) - 1

variable (hbd : ∀ g : G, |gaugeReTr G n g| ≤ n)
variable (hmeas : ∀ p : LatticePlaquette d N, Measurable (xp (G := G) n p))

include hbd in
theorem abs_mul_xp_le (β : ℝ) (p : LatticePlaquette d N) (U : GaugeConnection G d N) :
    |β * xp n p U| ≤ n * |β| := by
  rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hbd _) (abs_nonneg β)

include hbd in
theorem expo_bounds (β : ℝ) (p : LatticePlaquette d N) (ω : Dup G d N) :
    0 ≤ β * xp n p (fstC ω) + β * xp n p (sndC ω) + 2 * n * |β| ∧
      β * xp n p (fstC ω) + β * xp n p (sndC ω) + 2 * n * |β| ≤ 4 * n * |β| := by
  have h1 := abs_le.mp (abs_mul_xp_le hbd β p (fstC ω))
  have h2 := abs_le.mp (abs_mul_xp_le hbd β p (sndC ω))
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

include hbd in
theorem hP_nonneg (β : ℝ) (p : LatticePlaquette d N) (ω : Dup G d N) : 0 ≤ hP n β p ω := by
  unfold hP; linarith [Real.one_le_exp (expo_bounds hbd β p ω).1]

include hbd in
theorem hP_le (β : ℝ) (p : LatticePlaquette d N) (ω : Dup G d N) : hP n β p ω ≤ Real.exp (4 * n * |β|) - 1 := by
  unfold hP; linarith [Real.exp_le_exp.mpr (expo_bounds hbd β p ω).2]

include hbd in
theorem hP_le_mul (β : ℝ) (p : LatticePlaquette d N) (ω : Dup G d N) :
    hP n β p ω ≤ (1 - Real.exp (-(4 * n * |β|))) * (1 + hP n β p ω) := by
  unfold hP
  set s := β * xp n p (fstC ω) + β * xp n p (sndC ω) + 2 * n * |β|
  have hs := (expo_bounds hbd β p ω).2
  have h1 : Real.exp s * Real.exp (-(4 * n * |β|)) ≤ 1 := by
    rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith)
  nlinarith

include hmeas in
theorem measurable_hP (β : ℝ) (p : LatticePlaquette d N) : Measurable (hP (G := G) n β p) := by
  unfold hP
  exact ((((hmeas p).comp measurable_fstC).const_mul β).add (((hmeas p).comp measurable_sndC).const_mul β)
    |>.add_const _).exp.sub_const 1

theorem one_add_hP (β : ℝ) (p : LatticePlaquette d N) (ω : Dup G d N) :
    1 + hP n β p ω = Real.exp (2 * n * |β|) * (Real.exp (β * xp n p (fstC ω)) * Real.exp (β * xp n p (sndC ω))) := by
  unfold hP
  rw [add_sub_cancel, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

include hmeas in
/-- **The exchange.** If the plaquettes of `A` joined inside `A` to a plaquette touching `L_F` touch no link of `L_G`, the term
    of `A` vanishes: exchanging the two copies on the links of `L_F` and of that cluster flips its sign. -/
theorem term_vanish (β : ℝ) {f g : GaugeConnection G d N → ℝ} {LF LG : Finset (LatticeLink d N)}
    (hfd : LinkDep f LF) (hgd : LinkDep g LG) (mf : Measurable f) (mg : Measurable g) (hdisj : Disjoint LF LG)
    (A : Finset (LatticePlaquette d N))
    (hA : Disjoint (splitOff (G := plaqGraph d N) ((touchPlaqs LF : Finset _) : Set (LatticePlaquette d N)) A)
      (touchPlaqs LG)) :
    ∫ ω, (f (fstC ω) - f (sndC ω)) * (g (fstC ω) - g (sndC ω)) * ∏ p ∈ A, hP n β p ω ∂(dupMeasure G d N) = 0 := by
  set K := splitOff (G := plaqGraph d N) ((touchPlaqs LF : Finset _) : Set (LatticePlaquette d N)) A with hK
  set C : Finset (LatticeLink d N) := LF ∪ linksOf K with hC
  have hKmem : ∀ {p}, p ∈ K ↔ p ∈ A ∧ ∃ w ∈ ((touchPlaqs LF : Finset _) : Set (LatticePlaquette d N)),
      WalkIn (plaqGraph d N) A p w := by
    intro p; rw [hK]; simp only [splitOff, mem_filter]
  have hFC : ∀ l ∈ LF, l ∈ C := fun l hl => mem_union_left _ hl
  have hin : ∀ p ∈ K, ∀ l ∈ plaqLinks p, l ∈ C := fun p hp l hl =>
    mem_union_right _ (mem_biUnion.mpr ⟨p, hp, hl⟩)
  have hout : ∀ p ∈ A, p ∉ K → ∀ l ∈ plaqLinks p, l ∉ C := by
    intro p hpA hpK l hl hlC
    apply hpK
    rcases mem_union.mp hlC with hlF | hlK
    · exact hKmem.mpr ⟨hpA, p, by simpa using mem_touchPlaqs.mpr ⟨l, mem_inter.mpr ⟨hl, hlF⟩⟩, WalkIn.refl hpA⟩
    · obtain ⟨q, hqK, hlq⟩ := mem_biUnion.mp hlK
      by_cases hpq : p = q
      · exact hpq ▸ hqK
      · obtain ⟨hqA, w, hw, hqw⟩ := hKmem.mp hqK
        exact hKmem.mpr ⟨hpA, w, hw, (walkIn_adj (plaqGraph d N) hpA hqA ⟨hpq, l, mem_inter.mpr ⟨hl, hlq⟩⟩).trans hqw⟩
  have hGC : ∀ l ∈ LG, l ∉ C := by
    intro l hl hlC
    rcases mem_union.mp hlC with hlF | hlK
    · exact disjoint_left.mp hdisj hlF hl
    · obtain ⟨q, hqK, hlq⟩ := mem_biUnion.mp hlK
      exact disjoint_left.mp hA hqK (mem_touchPlaqs.mpr ⟨l, mem_inter.mpr ⟨hlq, hl⟩⟩)
  refine integral_eq_zero_of_swap_odd C _ ?_ (fun ω => ?_)
  · exact (((mf.comp measurable_fstC).sub (mf.comp measurable_sndC)).mul
      ((mg.comp measurable_fstC).sub (mg.comp measurable_sndC))).mul
      (Finset.measurable_prod _ fun p _ => measurable_hP hmeas β p)
  · have e1 : f (fstC (swapOn C ω)) = f (sndC ω) := hfd _ _ fun l hl => by rw [fstC_swapOn, if_pos (hFC l hl)]
    have e2 : f (sndC (swapOn C ω)) = f (fstC ω) := hfd _ _ fun l hl => by rw [sndC_swapOn, if_pos (hFC l hl)]
    have e3 : g (fstC (swapOn C ω)) = g (fstC ω) := hgd _ _ fun l hl => by rw [fstC_swapOn, if_neg (hGC l hl)]
    have e4 : g (sndC (swapOn C ω)) = g (sndC ω) := hgd _ _ fun l hl => by rw [sndC_swapOn, if_neg (hGC l hl)]
    have e5 : ∏ p ∈ A, hP n β p (swapOn C ω) = ∏ p ∈ A, hP n β p ω := by
      refine prod_congr rfl fun p hp => ?_
      by_cases hpK : p ∈ K
      · have x1 : xp n p (fstC (swapOn C ω)) = xp n p (sndC ω) :=
          xp_linkDep p _ _ fun l hl => by rw [fstC_swapOn, if_pos (hin p hpK l hl)]
        have x2 : xp n p (sndC (swapOn C ω)) = xp n p (fstC ω) :=
          xp_linkDep p _ _ fun l hl => by rw [sndC_swapOn, if_pos (hin p hpK l hl)]
        simp only [hP, x1, x2]
        congr 2; ring
      · have x1 : xp n p (fstC (swapOn C ω)) = xp n p (fstC ω) :=
          xp_linkDep p _ _ fun l hl => by rw [fstC_swapOn, if_neg (hout p hp hpK l hl)]
        have x2 : xp n p (sndC (swapOn C ω)) = xp n p (sndC ω) :=
          xp_linkDep p _ _ fun l hl => by rw [sndC_swapOn, if_neg (hout p hp hpK l hl)]
        simp only [hP, x1, x2]
    rw [e1, e2, e3, e4, e5]; ring

include hbd hmeas in
/-- **The doubled expansion bound.** With `p = 1 − e^{−4n|β|}`:
    `|∫ Φ ∏(1 + h)| ≤ 4 (∑_{X joining} p^{|X|}) ∫ ∏(1 + h)`, `Φ = (f(U) − f(V))(g(U) − g(V))`. -/
theorem dup_bound (β : ℝ) {f g : GaugeConnection G d N → ℝ} {LF LG : Finset (LatticeLink d N)}
    (hfd : LinkDep f LF) (hgd : LinkDep g LG) (mf : Measurable f) (mg : Measurable g)
    (hf1 : ∀ U, |f U| ≤ 1) (hg1 : ∀ U, |g U| ≤ 1) (hdisj : Disjoint LF LG) :
    |∫ ω, (f (fstC ω) - f (sndC ω)) * (g (fstC ω) - g (sndC ω)) * ∏ p, (1 + hP n β p ω) ∂(dupMeasure G d N)| ≤
      4 * (∑ X ∈ joining (plaqGraph d N) (touchPlaqs LF) (touchPlaqs LG),
        (1 - Real.exp (-(4 * n * |β|))) ^ X.1.card) * ∫ ω, ∏ p, (1 + hP n β p ω) ∂(dupMeasure G d N) := by
  set pr := 1 - Real.exp (-(4 * n * |β|)) with hpr
  set M := Real.exp (4 * n * |β|) - 1 with hM
  set ν := dupMeasure G d N
  set Φ : Dup G d N → ℝ := fun ω => (f (fstC ω) - f (sndC ω)) * (g (fstC ω) - g (sndC ω)) with hΦ
  have hM0 : 0 ≤ M := by
    have : (0 : ℝ) ≤ 4 * n * |β| := by positivity
    linarith [Real.one_le_exp this]
  have mΦ : Measurable Φ := ((mf.comp measurable_fstC).sub (mf.comp measurable_sndC)).mul
    ((mg.comp measurable_fstC).sub (mg.comp measurable_sndC))
  have hΦb : ∀ ω, |Φ ω| ≤ 4 := by
    intro ω
    simp only [hΦ, abs_mul]
    have a1 : |f (fstC ω) - f (sndC ω)| ≤ 2 := (abs_sub _ _).trans (by linarith [hf1 (fstC ω), hf1 (sndC ω)])
    have a2 : |g (fstC ω) - g (sndC ω)| ≤ 2 := (abs_sub _ _).trans (by linarith [hg1 (fstC ω), hg1 (sndC ω)])
    nlinarith [abs_nonneg (f (fstC ω) - f (sndC ω)), abs_nonneg (g (fstC ω) - g (sndC ω))]
  have mprod : ∀ A : Finset (LatticePlaquette d N), Measurable fun ω => ∏ p ∈ A, hP n β p ω :=
    fun A => Finset.measurable_prod _ fun p _ => measurable_hP hmeas β p
  have hprod0 : ∀ A : Finset (LatticePlaquette d N), ∀ ω, 0 ≤ ∏ p ∈ A, hP n β p ω :=
    fun A ω => prod_nonneg fun p _ => hP_nonneg hbd β p ω
  have hprodM : ∀ A : Finset (LatticePlaquette d N), ∀ ω, ∏ p ∈ A, hP n β p ω ≤ M ^ A.card := fun A ω => by
    rw [← prod_const]; exact prod_le_prod₀ (fun p _ => hP_nonneg hbd β p ω) (fun p _ => hP_le hbd β p ω)
  have intA : ∀ A : Finset (LatticePlaquette d N), Integrable (fun ω => ∏ p ∈ A, hP n β p ω) ν := fun A =>
    Integrable.of_bound (mprod A).aestronglyMeasurable (M ^ A.card) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hprod0 A ω)]; exact hprodM A ω)
  have intΦA : ∀ A : Finset (LatticePlaquette d N), Integrable (fun ω => Φ ω * ∏ p ∈ A, hP n β p ω) ν := fun A =>
    Integrable.of_bound (mΦ.mul (mprod A)).aestronglyMeasurable (4 * M ^ A.card)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hprod0 A ω)]
        exact mul_le_mul (hΦb ω) (hprodM A ω) (hprod0 A ω) (by norm_num))
  set I : Finset (LatticePlaquette d N) → ℝ := fun A => ∫ ω, ∏ p ∈ A, hP n β p ω ∂ν with hI
  have hI0 : ∀ A, 0 ≤ I A := fun A => integral_nonneg fun ω => hprod0 A ω
  set T : Finset (LatticePlaquette d N) → ℝ := fun A => ∫ ω, Φ ω * ∏ p ∈ A, hP n β p ω ∂ν with hT
  have hTb : ∀ A, |T A| ≤ 4 * I A := by
    intro A
    refine (abs_integral_le_integral_abs).trans ?_
    rw [hI, ← integral_const_mul]
    refine integral_mono (intΦA A).abs ((intA A).const_mul 4) fun ω => ?_
    simp only [abs_mul, abs_of_nonneg (hprod0 A ω)]
    exact mul_le_mul_of_nonneg_right (hΦb ω) (hprod0 A ω)
  have hT0 : ∀ A, Disjoint (splitOff (G := plaqGraph d N) ((touchPlaqs LF : Finset _) : Set (LatticePlaquette d N)) A)
      (touchPlaqs LG) → T A = 0 := fun A hA => term_vanish hmeas β hfd hgd mf mg hdisj A hA
  have hexp : ∫ ω, Φ ω * ∏ p, (1 + hP n β p ω) ∂ν = ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset, T A := by
    simp_rw [prod_one_add, mul_sum]
    exact integral_finsetSum _ fun A _ => intΦA A
  have hD : ∀ ω : Dup G d N, ∏ p, (1 + hP n β p ω) = ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset, ∏ p ∈ A, hP n β p ω :=
    fun ω => prod_one_add _
  have intD : Integrable (fun ω => ∏ p, (1 + hP n β p ω)) ν := by
    simp_rw [hD]; exact integrable_finsetSum _ fun A _ => intA A
  have hsup : ∀ X : Finset (LatticePlaquette d N),
      ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter (fun A => X ⊆ A), 4 * I A ≤
        4 * (pr ^ X.card * ∫ ω, ∏ p, (1 + hP n β p ω) ∂ν) := by
    intro X
    have hpt : ∀ ω : Dup G d N,
        ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter (fun A => X ⊆ A), ∏ p ∈ A, hP n β p ω ≤
          pr ^ X.card * ∏ p, (1 + hP n β p ω) := fun ω =>
      sum_superset_le (h := fun p => hP n β p ω) (p := pr) (fun p => hP_nonneg hbd β p ω)
        (fun p => hP_le_mul hbd β p ω) X
    have hint1 : Integrable (fun ω : Dup G d N =>
        ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter (fun A => X ⊆ A), ∏ p ∈ A, hP n β p ω) ν :=
      integrable_finsetSum _ fun A _ => intA A
    have hint2 : Integrable (fun ω : Dup G d N => pr ^ X.card * ∏ p, (1 + hP n β p ω)) ν := intD.const_mul _
    have h1 := integral_mono hint1 hint2 hpt
    rw [integral_finsetSum _ fun A _ => intA A, integral_const_mul] at h1
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  rw [hexp]
  calc |∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset, T A|
      ≤ ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset, |T A| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset,
          (if ¬ Disjoint (splitOff (G := plaqGraph d N) ((touchPlaqs LF : Finset _) : Set (LatticePlaquette d N)) A)
            (touchPlaqs LG) then 4 * I A else 0) := by
        refine sum_le_sum fun A _ => ?_
        split_ifs with h
        · rw [hT0 A h, abs_zero]
        · exact hTb A
    _ = ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter (fun A =>
          ¬ Disjoint (splitOff (G := plaqGraph d N) ((touchPlaqs LF : Finset _) : Set (LatticePlaquette d N)) A)
            (touchPlaqs LG)), 4 * I A := (sum_filter _ _).symm
    _ ≤ ∑ X ∈ joining (plaqGraph d N) (touchPlaqs LF) (touchPlaqs LG),
          ∑ A ∈ (univ : Finset (LatticePlaquette d N)).powerset.filter (fun A => X.1 ⊆ A), 4 * I A :=
        sum_joining_le_sum (plaqGraph d N) (touchPlaqs LF) (touchPlaqs LG) (fun A => 4 * I A)
          (fun A => by have := hI0 A; positivity)
    _ ≤ ∑ X ∈ joining (plaqGraph d N) (touchPlaqs LF) (touchPlaqs LG),
          4 * (pr ^ X.1.card * ∫ ω, ∏ p, (1 + hP n β p ω) ∂ν) := sum_le_sum fun X _ => hsup X.1
    _ = _ := by rw [← mul_sum, ← sum_mul]; ring

/-- The Wilson weight `W(U) = ∏_p e^{β x_p(U)}`. -/
def wW (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (U : GaugeConnection G d N) : ℝ :=
  ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)

include hbd in
theorem wW_bounds (β : ℝ) (U : GaugeConnection G d N) :
    Real.exp (-(n * |β|)) ^ Fintype.card (LatticePlaquette d N) ≤ wW n β U ∧
      wW n β U ≤ Real.exp (n * |β|) ^ Fintype.card (LatticePlaquette d N) := by
  unfold wW
  rw [← card_univ, ← prod_const, ← prod_const]
  constructor
  · exact prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) fun p _ =>
      Real.exp_le_exp.mpr (by linarith [(abs_le.mp (abs_mul_xp_le hbd β p U)).1])
  · exact prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) fun p _ =>
      Real.exp_le_exp.mpr (le_of_abs_le (abs_mul_xp_le hbd β p U))

include hmeas in
theorem measurable_wW (β : ℝ) : Measurable (wW (G := G) (d := d) (N := N) n β) := by
  unfold wW
  exact Finset.measurable_prod _ fun p _ => ((hmeas p).const_mul β).exp

include hbd in
theorem prod_one_add_hP (β : ℝ) (ω : Dup G d N) :
    ∏ p, (1 + hP n β p ω) =
      Real.exp (2 * n * |β|) ^ Fintype.card (LatticePlaquette d N) * (wW n β (fstC ω) * wW n β (sndC ω)) := by
  simp_rw [one_add_hP]
  rw [prod_mul_distrib, prod_const, prod_mul_distrib, card_univ]
  rfl

include hbd hmeas in
/-- **Exponential clustering, abstract degree bound.** For any `β` with `q = Δ² (1 − e^{−4n|β|}) < 1`, bounded measurable `f`, `g`
    depending on disjoint link sets `LF`, `LG` whose touching plaquettes are at plaquette-graph distance at least `r`:
    the partition function is positive and `|⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ 2 |R_F| p q^r / (1 − q)`, `p = 1 − e^{−4n|β|}`. -/
theorem wilson_clustering (β : ℝ) {Δ : ℕ} (hdeg : ∀ p, (plaqGraph d N).degree p ≤ Δ)
    (hq : (Δ : ℝ) ^ 2 * (1 - Real.exp (-(4 * n * |β|))) < 1)
    {f g : GaugeConnection G d N → ℝ} {LF LG : Finset (LatticeLink d N)}
    (hfd : LinkDep f LF) (hgd : LinkDep g LG) (mf : Measurable f) (mg : Measurable g)
    (hf1 : ∀ U, |f U| ≤ 1) (hg1 : ∀ U, |g U| ≤ 1) (hdisj : Disjoint LF LG) {r : ℕ}
    (hr : ∀ a ∈ touchPlaqs LF, ∀ b ∈ touchPlaqs LG, r ≤ (plaqGraph d N).dist a b) :
    0 < ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N) ∧
    |wilsonExpect n β (fun U => f U * g U) - wilsonExpect n β f * wilsonExpect n β g| ≤
      2 * (touchPlaqs LF).card * ((1 - Real.exp (-(4 * n * |β|))) *
        ((Δ : ℝ) ^ 2 * (1 - Real.exp (-(4 * n * |β|)))) ^ r / (1 - (Δ : ℝ) ^ 2 * (1 - Real.exp (-(4 * n * |β|))))) := by
  set pr := 1 - Real.exp (-(4 * n * |β|)) with hpr
  have hpr0 : 0 ≤ pr := by
    have : Real.exp (-(4 * n * |β|)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : (0 : ℝ) ≤ 4 * n * |β| := by positivity
      linarith)
    linarith
  set μ := productHaar G d N
  set W := wW (G := G) (d := d) (N := N) n β with hWdef
  set c := Fintype.card (LatticePlaquette d N)
  set E := Real.exp (2 * n * |β|) ^ c with hE
  have hE0 : 0 < E := by positivity
  have mW : Measurable W := measurable_wW hmeas β
  have hWb := wW_bounds hbd (d := d) (N := N) β
  have hW0 : ∀ U, 0 ≤ W U := fun U => (pow_nonneg (Real.exp_pos _).le _).trans (hWb U).1
  have hbound : ∀ {F : GaugeConnection G d N → ℝ}, Measurable F → (∀ U, |F U| ≤ 1) →
      Integrable (fun U => F U * W U) μ := by
    intro F hF hF1
    refine Integrable.of_bound (hF.mul mW).aestronglyMeasurable (Real.exp (n * |β|) ^ c)
      (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hW0 U)]
    calc |F U| * W U ≤ 1 * W U := mul_le_mul_of_nonneg_right (hF1 U) (hW0 U)
      _ ≤ _ := by rw [one_mul]; exact (hWb U).2
  have iW : Integrable W μ := by
    simpa using hbound (F := fun _ => 1) measurable_const (fun _ => by simp)
  have ifW := hbound mf hf1
  have igW := hbound mg hg1
  have ifgW : Integrable (fun U => f U * g U * W U) μ := hbound (mf.mul mg) fun U => by
    rw [abs_mul]; nlinarith [hf1 U, hg1 U, abs_nonneg (f U), abs_nonneg (g U)]
  set Z := ∫ U, W U ∂μ with hZ
  have hZ0 : 0 < Z := by
    have h1 : ∫ _U, Real.exp (-(n * |β|)) ^ c ∂μ ≤ Z := integral_mono (integrable_const _) iW fun U => (hWb U).1
    have h2 : ∫ _U, Real.exp (-(n * |β|)) ^ c ∂μ = Real.exp (-(n * |β|)) ^ c := by simp
    have h3 : 0 < Real.exp (-(n * |β|)) ^ c := by positivity
    linarith
  set Nf := ∫ U, f U * W U ∂μ
  set Ng := ∫ U, g U * W U ∂μ
  set Nfg := ∫ U, f U * g U * W U ∂μ
  -- the two-copies identities
  have hnum : ∫ ω, (f (fstC ω) - f (sndC ω)) * (g (fstC ω) - g (sndC ω)) * ∏ p, (1 + hP n β p ω)
      ∂(dupMeasure G d N) = E * (2 * (Z * Nfg - Nf * Ng)) := by
    simp_rw [prod_one_add_hP hbd β]
    have hd := integral_dup (G := G) (d := d) (N := N)
      (fun z : GaugeConnection G d N × GaugeConnection G d N => (f z.1 - f z.2) * (g z.1 - g z.2) * (W z.1 * W z.2))
    have hw := two_copies_weighted μ f g W iW ifW igW ifgW
    calc ∫ ω, (f (fstC ω) - f (sndC ω)) * (g (fstC ω) - g (sndC ω)) * (E * (W (fstC ω) * W (sndC ω)))
          ∂(dupMeasure G d N)
        = ∫ ω, E * ((f (fstC ω) - f (sndC ω)) * (g (fstC ω) - g (sndC ω)) * (W (fstC ω) * W (sndC ω)))
          ∂(dupMeasure G d N) := by
          congr 1; funext ω; ring
      _ = E * ∫ ω, (f (fstC ω) - f (sndC ω)) * (g (fstC ω) - g (sndC ω)) * (W (fstC ω) * W (sndC ω))
          ∂(dupMeasure G d N) := integral_const_mul _ _
      _ = E * (2 * (Z * Nfg - Nf * Ng)) := congrArg (E * ·) (hd.trans hw)
  have hden : ∫ ω, ∏ p, (1 + hP n β p ω) ∂(dupMeasure G d N) = E * (Z * Z) := by
    simp_rw [prod_one_add_hP hbd β]
    rw [integral_const_mul]
    congr 1
    exact (integral_dup (G := G) (d := d) (N := N)
      (fun z : GaugeConnection G d N × GaugeConnection G d N => W z.1 * W z.2)).trans (integral_prod_mul W W)
  have hmain := dup_bound hbd hmeas β hfd hgd mf mg hf1 hg1 hdisj
  rw [hnum, hden] at hmain
  set S := ∑ X ∈ joining (plaqGraph d N) (touchPlaqs LF) (touchPlaqs LG), pr ^ X.1.card with hS
  have hcount : S ≤ (touchPlaqs LF).card * (pr * ((Δ : ℝ) ^ 2 * pr) ^ r / (1 - (Δ : ℝ) ^ 2 * pr)) :=
    sum_joining_pow_le (plaqGraph d N) hdeg (touchPlaqs LF) (touchPlaqs LG) hpr0 hq hr
  refine ⟨hZ0, ?_⟩
  have hcov : wilsonExpect n β (fun U => f U * g U) - wilsonExpect n β f * wilsonExpect n β g =
      (Z * Nfg - Nf * Ng) / (Z * Z) := by
    have e1 : wilsonExpect n β (fun U => f U * g U) = Nfg / Z := rfl
    have e2 : wilsonExpect n β f = Nf / Z := rfl
    have e3 : wilsonExpect n β g = Ng / Z := rfl
    rw [e1, e2, e3]
    field_simp
  have hZZ : 0 < Z * Z := mul_pos hZ0 hZ0
  rw [hcov, abs_div, abs_of_pos hZZ, div_le_iff₀ hZZ]
  have h1 : |E * (2 * (Z * Nfg - Nf * Ng))| = E * (2 * |Z * Nfg - Nf * Ng|) := by
    rw [abs_mul, abs_mul, abs_of_pos hE0]; norm_num
  rw [h1] at hmain
  have h2 : 2 * |Z * Nfg - Nf * Ng| ≤ 4 * S * (Z * Z) := by
    have h3 : E * (2 * |Z * Nfg - Nf * Ng|) ≤ E * (4 * S * (Z * Z)) := by linarith [hmain]
    exact le_of_mul_le_mul_left h3 hE0
  have hS0 : 0 ≤ S := sum_nonneg fun X _ => pow_nonneg hpr0 _
  nlinarith

end Lattice

/-! ## 5. Explicit constants, SU(2) and U(n) -/

section Explicit

open AreaLaw.Concrete TopologicalSpace

variable {d N : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n]

/-- The decay ratio `q = (16 d)² (1 − e^{−4n|β|})`. -/
def qClust (d n : ℕ) (β : ℝ) : ℝ := (16 * d : ℝ) ^ 2 * (1 - Real.exp (-(4 * n * |β|)))

theorem qClust_nonneg (d n : ℕ) (β : ℝ) : 0 ≤ qClust d n β := by
  unfold qClust
  have : Real.exp (-(4 * n * |β|)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : (0 : ℝ) ≤ 4 * n * |β| := by positivity
    linarith)
  have : (0 : ℝ) ≤ 1 - Real.exp (-(4 * n * |β|)) := by linarith
  positivity

/-- **Exponential clustering, explicit.** For a group with a continuous representation, `|Re tr| ≤ n` and a probability measure
    on a link (no invariance or centre needed), any `β` with `q = (16 d)² (1 − e^{−4n|β|}) < 1`, and bounded measurable `f`, `g`
    depending on disjoint link sets `LF`, `LG` at plaquette distance at least `r`:
    `|⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ 8 d |LF| q^r / (1 − q)`, uniformly in the lattice size `N`. -/
theorem wilson_clustering_explicit [NeZero N] [HasHaarProbability G]
    (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n))) (hbd : ∀ g : G, |gaugeReTr G n g| ≤ n)
    (β : ℝ) (hq : qClust d n β < 1)
    {f g : GaugeConnection G d N → ℝ} {LF LG : Finset (LatticeLink d N)}
    (hfd : LinkDep f LF) (hgd : LinkDep g LG) (mf : Measurable f) (mg : Measurable g)
    (hf1 : ∀ U, |f U| ≤ 1) (hg1 : ∀ U, |g U| ≤ 1) (hdisj : Disjoint LF LG) {r : ℕ}
    (hr : ∀ a ∈ touchPlaqs LF, ∀ b ∈ touchPlaqs LG, r ≤ (plaqGraph d N).dist a b) :
    0 < ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N) ∧
    |wilsonExpect n β (fun U => f U * g U) - wilsonExpect n β f * wilsonExpect n β g| ≤
      8 * d * LF.card * qClust d n β ^ r / (1 - qClust d n β) := by
  have hq' : (((16 * d : ℕ) : ℝ)) ^ 2 * (1 - Real.exp (-(4 * n * |β|))) < 1 := by
    have : (((16 * d : ℕ) : ℝ)) ^ 2 * (1 - Real.exp (-(4 * n * |β|))) = qClust d n β := by
      unfold qClust; push_cast; ring
    rw [this]; exact hq
  obtain ⟨h0, h1⟩ := wilson_clustering hbd (measurable_xp hc) β (Δ := 16 * d) plaqGraph_degree_le hq' hfd hgd mf mg
    hf1 hg1 hdisj hr
  refine ⟨h0, h1.trans ?_⟩
  have e : (((16 * d : ℕ) : ℝ)) ^ 2 * (1 - Real.exp (-(4 * n * |β|))) = qClust d n β := by
    unfold qClust; push_cast; ring
  rw [e]
  set q := qClust d n β
  set pr := 1 - Real.exp (-(4 * n * |β|))
  have hq0 : 0 ≤ q := qClust_nonneg d n β
  have hd : 0 < 1 - q := by linarith
  have hpr0 : 0 ≤ pr := by
    have : Real.exp (-(4 * n * |β|)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : (0 : ℝ) ≤ 4 * n * |β| := by positivity
      linarith)
    simp only [pr]; linarith
  have hpr1 : pr ≤ 1 := by simp only [pr]; linarith [Real.exp_pos (-(4 * n * |β|))]
  have hcard : ((touchPlaqs LF).card : ℝ) ≤ 4 * d * LF.card := by exact_mod_cast card_touchPlaqs_le LF
  have hqr : 0 ≤ q ^ r / (1 - q) := div_nonneg (pow_nonneg hq0 _) hd.le
  calc 2 * ((touchPlaqs LF).card : ℝ) * (pr * q ^ r / (1 - q))
      = 2 * ((touchPlaqs LF).card : ℝ) * pr * (q ^ r / (1 - q)) := by ring
    _ ≤ 2 * (4 * d * LF.card) * 1 * (q ^ r / (1 - q)) := by gcongr
    _ = 8 * d * LF.card * q ^ r / (1 - q) := by ring

/-- **Exponential clustering for SU(2) lattice gauge theory** (Wilson action `β Re tr U_p`, normalised Haar measure, periodic
    lattice `(ℤ/Nℤ)^d`): for `q = (16 d)² (1 − e^{−8|β|}) < 1`, `|⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ 8 d |LF| q^r / (1 − q)`. -/
theorem wilson_clustering_SU2 [NeZero N] (β : ℝ) (hq : qClust d 2 β < 1)
    {f g : GaugeConnection SU2 d N → ℝ} {LF LG : Finset (LatticeLink d N)}
    (hfd : LinkDep f LF) (hgd : LinkDep g LG) (mf : Measurable f) (mg : Measurable g)
    (hf1 : ∀ U, |f U| ≤ 1) (hg1 : ∀ U, |g U| ≤ 1) (hdisj : Disjoint LF LG) {r : ℕ}
    (hr : ∀ a ∈ touchPlaqs LF, ∀ b ∈ touchPlaqs LG, r ≤ (plaqGraph d N).dist a b) :
    0 < ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U) ∂(productHaar SU2 d N) ∧
    |wilsonExpect 2 β (fun U => f U * g U) - wilsonExpect 2 β f * wilsonExpect 2 β g| ≤
      8 * d * LF.card * qClust d 2 β ^ r / (1 - qClust d 2 β) := by
  have hc : Continuous (HasGaugeTrace.rep (G := SU2) (n := 2)) := continuous_subtype_val
  have hbd : ∀ g : SU2, |gaugeReTr SU2 2 g| ≤ (2 : ℕ) :=
    fun g => abs_re_trace_le_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)
  exact wilson_clustering_explicit hc hbd β hq hfd hgd mf mg hf1 hg1 hdisj hr

/-- **Exponential clustering for U(n) lattice gauge theory**: for `q = (16 d)² (1 − e^{−4n|β|}) < 1`,
    `|⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ 8 d |LF| q^r / (1 − q)`. -/
theorem wilson_clustering_Un [NeZero N] (n : ℕ) (β : ℝ) (hq : qClust d n β < 1)
    {f g : GaugeConnection (Un n) d N → ℝ} {LF LG : Finset (LatticeLink d N)}
    (hfd : LinkDep f LF) (hgd : LinkDep g LG) (mf : Measurable f) (mg : Measurable g)
    (hf1 : ∀ U, |f U| ≤ 1) (hg1 : ∀ U, |g U| ≤ 1) (hdisj : Disjoint LF LG) {r : ℕ}
    (hr : ∀ a ∈ touchPlaqs LF, ∀ b ∈ touchPlaqs LG, r ≤ (plaqGraph d N).dist a b) :
    0 < ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar (Un n) d N) ∧
    |wilsonExpect n β (fun U => f U * g U) - wilsonExpect n β f * wilsonExpect n β g| ≤
      8 * d * LF.card * qClust d n β ^ r / (1 - qClust d n β) := by
  have hc : Continuous (HasGaugeTrace.rep (G := Un n) (n := n)) := continuous_subtype_val
  have hbd : ∀ g : Un n, |gaugeReTr (Un n) n g| ≤ n := fun g => abs_re_trace_le_of_unitary g.2
  exact wilson_clustering_explicit hc hbd β hq hfd hgd mf mg hf1 hg1 hdisj hr

end Explicit

end AreaLaw.Clustering
