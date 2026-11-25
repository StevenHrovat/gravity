/-
Toward the strong-coupling area law (area-law project, 2026-11-21). Released under Apache 2.0.

# P8: the cluster ratio bound

A polymer gas on a finite graph `H` of maximum degree `≤ Δ`: polymers are the nonempty `H`-connected vertex sets
(`Balaban.Polymer.BlockPolymer H`), activities `K : polymer → ℂ`. For a vertex set `S`, `XiAvoid inc supp S K` is the
partition function of the gas restricted to the polymers disjoint from `S` (activities set to zero on the polymers meeting
`S`; `XiAvoid_eq` checks that this is the sum over pairwise compatible families of polymers disjoint from `S`).

* `ratio_generic`: for any reflexive incompatibility with the Kotecký–Preiss condition and a per-vertex bound `β` on the
  KP weights, `Xi ≠ 0` and `‖XiAvoid S‖ ≤ exp (β |S|) ‖Xi‖`. Proof: `Ξ = exp L` for both gases (`pe_xi_eq_exp`),
  `L = Σ_Y P(Y)` (`logSeries_eq_sum_PY`), the local terms of the restricted gas are those of the full gas on the supports
  avoiding `S` and zero on the others, and `Σ_{Y ∋ b} |P(Y)| ≤ β` (`pe_PY_bound`).
* `cluster_ratio_overlap`: the incompatibility of `pe_lattice` (polymers share a vertex).
* `cluster_ratio_touch`: the incompatibility "share or neighbour a vertex" (`touch`, i.e. the union is connected), which
  is what a gas of plaquettes with "share a link" adjacency needs; `cluster_ratio_touch_explicit` with
  `ε ≤ 1 / (2 e (Δ + 1)²)` and `α = 1`.
-/

import AreaLaw.Vendor.Lattice

open scoped Classical

open Finset Balaban.Polymer

set_option linter.unusedSectionVars false

noncomputable section

namespace AreaLaw.ClusterRatio

section Generic

variable {P : Type*} [Fintype P] (inc : P → P → Prop) {V : Type*} [Fintype V] (supp : P → Finset V)

/-- The activities with the polymers meeting `S` switched off. -/
def restrictK (S : Finset V) (K : P → ℂ) : P → ℂ := fun x => if Disjoint (supp x) S then K x else 0

/-- The partition function of the polymers avoiding `S`. -/
def XiAvoid (S : Finset V) (K : P → ℂ) : ℂ := Xi inc (restrictK supp S K)

theorem XiAvoid_empty (K : P → ℂ) : XiAvoid inc supp ∅ K = Xi inc K := by
  unfold XiAvoid restrictK
  simp

/-- `XiAvoid` is the sum over the pairwise compatible families of polymers disjoint from `S`. -/
theorem XiAvoid_eq (S : Finset V) (K : P → ℂ) :
    XiAvoid inc supp S K = ∑ Γ ∈ (Finset.univ : Finset (Finset P)).filter
      (fun Γ => Compat inc Γ ∧ ∀ x ∈ Γ, Disjoint (supp x) S), ∏ x ∈ Γ, K x := by
  unfold XiAvoid Xi
  conv_rhs => rw [← Finset.filter_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Γ _ => ?_)
  by_cases h : ∀ x ∈ Γ, Disjoint (supp x) S
  · rw [ite_eq_left h]
    exact Finset.prod_congr rfl (fun x hx => by simp [restrictK, h x hx])
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨x, hx, hd⟩ := h
    exact Finset.prod_eq_zero hx (by simp [restrictK, hd])

theorem norm_restrictK_le {w : P → ℝ} (hw : ∀ x, 0 ≤ w x) (S : Finset V) (K : P → ℂ)
    (hK : ∀ x, ‖K x‖ ≤ w x) (x : P) : ‖restrictK supp S K x‖ ≤ w x := by
  unfold restrictK
  split_ifs
  · exact hK x
  · simpa using hw x

theorem PY_restrictK_of_disjoint (S : Finset V) (K : P → ℂ) (Y : Finset V) (hY : Disjoint Y S) :
    PY inc supp (restrictK supp S K) Y = PY inc supp K Y :=
  PY_congr inc supp Y (fun x hx => by simp [restrictK, hY.mono_left hx])

theorem PY_restrictK_of_not_disjoint (S : Finset V) (K : P → ℂ) (Y : Finset V) (hY : ¬ Disjoint Y S) :
    PY inc supp (restrictK supp S K) Y = 0 := by
  obtain ⟨b, hbY, hbS⟩ := Finset.not_disjoint_iff.mp hY
  have h0 : ∀ n, Pterm inc supp (restrictK supp S K) Y n = 0 := by
    intro n
    unfold Pterm
    rw [Finset.sum_eq_zero, mul_zero]
    intro X hX
    rw [Finset.mem_filter] at hX
    have hb : b ∈ unionOf supp X := hX.2 ▸ hbY
    unfold unionOf at hb
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hb
    have hnd : ¬ Disjoint (supp (X i)) S := Finset.not_disjoint_iff.mpr ⟨b, hi, hbS⟩
    have hz : restrictK supp S K (X i) = 0 := by simp [restrictK, hnd]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]
  unfold PY
  simp [h0]

/-- **The cluster ratio bound, abstract form.** -/
theorem ratio_generic (hrefl : ∀ x, inc x x) {w a : P → ℝ} (hKP : KPCond inc w a) {β : ℝ}
    (hent : ∀ b : V, ∑ x, (if b ∈ supp x then w x * Real.exp (a x) else 0) ≤ β)
    (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ w x) (S : Finset V) :
    Xi inc K ≠ 0 ∧ ‖XiAvoid inc supp S K‖ ≤ Real.exp (β * S.card) * ‖Xi inc K‖ := by
  set K' := restrictK supp S K with hK'def
  have hK' := norm_restrictK_le supp hKP.nonneg S K hK
  have hX := pe_xi_eq_exp inc hKP hrefl K hK
  have hX' := pe_xi_eq_exp inc hKP hrefl K' hK'
  have hL := logSeries_eq_sum_PY inc supp hKP K hK
  have hL' := logSeries_eq_sum_PY inc supp hKP K' hK'
  have hdiff : logSeries inc K - logSeries inc K' =
      ∑ Y : Finset V, (if Disjoint Y S then 0 else PY inc supp K Y) := by
    rw [hL, hL', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun Y _ => ?_)
    by_cases hY : Disjoint Y S
    · rw [ite_eq_left hY, hK'def, PY_restrictK_of_disjoint inc supp S K Y hY, sub_self]
    · rw [ite_eq_right hY, hK'def, PY_restrictK_of_not_disjoint inc supp S K Y hY, sub_zero]
  have hPYb : ∀ b, ∑ Y ∈ (univ : Finset (Finset V)).filter (fun Y => b ∈ Y),
      ‖PY inc supp K Y‖ ≤ β := by
    intro b
    have h1 := pe_PY_bound inc supp (κ0 := w) (κ := w) (fun _ => 0) 0 le_rfl (fun _ => le_rfl)
      (fun n X _ => by simp) (fun x => by simp) hKP K hK b
    refine le_trans (le_of_eq ?_) (h1.trans (hent b))
    exact Finset.sum_congr rfl (fun Y _ => by simp)
  have hbound : ‖logSeries inc K - logSeries inc K'‖ ≤ β * S.card := by
    rw [hdiff]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ Y : Finset V, ‖(if Disjoint Y S then 0 else PY inc supp K Y)‖
        ≤ ∑ Y : Finset V, ∑ b ∈ S, (if b ∈ Y then ‖PY inc supp K Y‖ else 0) := by
          refine Finset.sum_le_sum (fun Y _ => ?_)
          by_cases hY : Disjoint Y S
          · rw [ite_eq_left hY, norm_zero]
            exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> simp)
          · rw [ite_eq_right hY]
            obtain ⟨b, hbY, hbS⟩ := Finset.not_disjoint_iff.mp hY
            calc ‖PY inc supp K Y‖ = (if b ∈ Y then ‖PY inc supp K Y‖ else 0) := by rw [ite_eq_left hbY]
              _ ≤ _ := Finset.single_le_sum (f := fun b => if b ∈ Y then ‖PY inc supp K Y‖ else 0)
                  (fun _ _ => by split_ifs <;> simp) hbS
      _ = ∑ b ∈ S, ∑ Y ∈ (univ : Finset (Finset V)).filter (fun Y => b ∈ Y), ‖PY inc supp K Y‖ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.sum_filter]
      _ ≤ ∑ _b ∈ S, β := Finset.sum_le_sum (fun b _ => hPYb b)
      _ = β * S.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  refine ⟨by rw [hX]; exact Complex.exp_ne_zero _, ?_⟩
  unfold XiAvoid
  rw [← hK'def, hX', hX, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (logSeries inc K').re = (logSeries inc K).re - (logSeries inc K - logSeries inc K').re := by
    rw [Complex.sub_re]; ring
  have h2 := Complex.abs_re_le_norm (logSeries inc K - logSeries inc K')
  linarith [(abs_le.mp h2).1]

/-- The ratio form of `ratio_generic`. -/
theorem ratio_generic_div (hrefl : ∀ x, inc x x) {w a : P → ℝ} (hKP : KPCond inc w a) {β : ℝ}
    (hent : ∀ b : V, ∑ x, (if b ∈ supp x then w x * Real.exp (a x) else 0) ≤ β)
    (K : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ w x) (S : Finset V) :
    Xi inc K ≠ 0 ∧ ‖XiAvoid inc supp S K / Xi inc K‖ ≤ Real.exp (β * S.card) := by
  obtain ⟨h0, h⟩ := ratio_generic inc supp hrefl hKP hent K hK S
  refine ⟨h0, ?_⟩
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr h0)]
  exact h

end Generic

section Lattice

variable {V : Type*} [Fintype V] (H : SimpleGraph V)

/-! ### Incompatibility = sharing a vertex (the one of `pe_lattice`) -/

/-- **P8, overlap version.** Polymers are incompatible iff they share a vertex (`overlap`, as in `pe_lattice`). -/
theorem cluster_ratio_overlap {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) {ε κ α : ℝ} (hε : 0 ≤ ε)
    (hq : (Δ : ℝ) ^ 2 * Real.exp (-(κ - α)) < 1)
    (hcond : ε * Real.exp (-(κ - α)) / (1 - (Δ : ℝ) ^ 2 * Real.exp (-(κ - α))) ≤ α)
    (K : BlockPolymer H → ℂ) (hK : ∀ X, ‖K X‖ ≤ ε * Real.exp (-κ * X.1.card)) (S : Finset V) :
    Xi (overlap H) K ≠ 0 ∧
      ‖XiAvoid (overlap H) (fun X : BlockPolymer H => X.1) S K / Xi (overlap H) K‖ ≤
        Real.exp (α * S.card) := by
  have hq' : (Δ : ℝ) ^ 2 * Real.exp (-(κ - 0 - α)) < 1 := by rw [sub_zero]; exact hq
  have hcond' : ε * Real.exp (-(κ - 0 - α)) / (1 - (Δ : ℝ) ^ 2 * Real.exp (-(κ - 0 - α))) ≤ α := by
    rw [sub_zero]; exact hcond
  refine ratio_generic_div (overlap H) (fun X : BlockPolymer H => X.1) (overlap_refl H)
    (lattice_kp H hdeg hε hq' hcond') (lattice_entropy_W H hdeg hε hq' hcond') K (fun X => ?_) S
  refine (hK X).trans (le_of_eq ?_)
  unfold latticeW
  simp

/-! ### Incompatibility = sharing or neighbouring a vertex -/

/-- Two polymers touch iff they share a vertex or a vertex of one is adjacent to a vertex of the other (for connected
    polymers this is "the union is connected"; that equivalence is not formalised here). -/
def touch (X Y : BlockPolymer H) : Prop := ∃ u ∈ X.1, ∃ v ∈ Y.1, u = v ∨ H.Adj u v

omit [Fintype V] in
theorem touch_refl (X : BlockPolymer H) : touch H X X := by
  obtain ⟨b, hb⟩ := X.2.1
  exact ⟨b, hb, b, hb, Or.inl rfl⟩

omit [Fintype V] in
theorem touch_symm {X Y : BlockPolymer H} (h : touch H X Y) : touch H Y X := by
  obtain ⟨u, hu, v, hv, h⟩ := h
  exact ⟨v, hv, u, hu, h.elim (fun e => Or.inl e.symm) (fun a => Or.inr a.symm)⟩

/-- The Kotecký–Preiss condition for `touch`, with the per-vertex bound `α / (Δ + 1)`. -/
theorem touch_kp {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) {ε κ α : ℝ} (hε : 0 ≤ ε)
    (hq : (Δ : ℝ) ^ 2 * Real.exp (-(κ - α)) < 1)
    (hcond : ((Δ : ℝ) + 1) * ε * Real.exp (-(κ - α)) / (1 - (Δ : ℝ) ^ 2 * Real.exp (-(κ - α))) ≤ α) :
    0 ≤ α ∧ KPCond (touch H) (latticeW H ε κ 0) (fun X => α * X.1.card) ∧
      ∀ b : V, ∑ Y : BlockPolymer H, (if b ∈ Y.1 then latticeW H ε κ 0 Y * Real.exp (α * Y.1.card) else 0)
        ≤ α / ((Δ : ℝ) + 1) := by
  have hD : (0 : ℝ) < (Δ : ℝ) + 1 := by positivity
  have hα : 0 ≤ α := le_trans (div_nonneg (by positivity) (by linarith)) hcond
  have hq' : (Δ : ℝ) ^ 2 * Real.exp (-(κ - 0 - α)) < 1 := by rw [sub_zero]; exact hq
  have hcond' : ((Δ : ℝ) + 1) * ε * Real.exp (-(κ - 0 - α)) /
      (1 - (Δ : ℝ) ^ 2 * Real.exp (-(κ - 0 - α))) ≤ α := by
    rw [sub_zero]; exact hcond
  have hw0 : ∀ Y : BlockPolymer H, 0 ≤ latticeW H ε κ 0 Y := fun Y => by unfold latticeW; positivity
  have hent : ∀ b : V, ∑ Y : BlockPolymer H,
      (if b ∈ Y.1 then latticeW H ε κ 0 Y * Real.exp (α * Y.1.card) else 0) ≤ α / ((Δ : ℝ) + 1) := by
    intro b
    have h1 := lattice_entropy_W H hdeg (ε := ((Δ : ℝ) + 1) * ε) (by positivity) hq' hcond' b
    rw [le_div_iff₀ hD, mul_comm, Finset.mul_sum]
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun Y _ => ?_))) h1
    split_ifs
    · unfold latticeW; ring
    · ring
  refine ⟨hα, ⟨hw0, fun Y => ?_⟩, hent⟩
  set E : V → ℝ := fun b => ∑ Y' : BlockPolymer H,
    (if b ∈ Y'.1 then latticeW H ε κ 0 Y' * Real.exp (α * Y'.1.card) else 0) with hE
  have hE0 : ∀ b, 0 ≤ E b := fun b =>
    Finset.sum_nonneg (fun Y' _ => by split_ifs <;> [exact mul_nonneg (hw0 _) (Real.exp_pos _).le; rfl])
  have hterm0 : ∀ (v : V) (Y' : BlockPolymer H),
      0 ≤ (if v ∈ Y'.1 then latticeW H ε κ 0 Y' * Real.exp (α * Y'.1.card) else 0) := fun v Y' => by
    split_ifs
    · exact mul_nonneg (hw0 _) (Real.exp_pos _).le
    · exact le_rfl
  calc ∑ Y' : BlockPolymer H, (if lnk (touch H) Y Y' then latticeW H ε κ 0 Y' * Real.exp (α * Y'.1.card) else 0)
      ≤ ∑ Y' : BlockPolymer H, ∑ u ∈ Y.1, ∑ v ∈ insert u (H.neighborFinset u),
          (if v ∈ Y'.1 then latticeW H ε κ 0 Y' * Real.exp (α * Y'.1.card) else 0) := by
        refine Finset.sum_le_sum (fun Y' _ => ?_)
        by_cases hl : lnk (touch H) Y Y'
        · rw [ite_eq_left hl]
          have ht : touch H Y Y' := hl.elim id (touch_symm H)
          obtain ⟨u, hu, v, hv, huv⟩ := ht
          have hvN : v ∈ insert u (H.neighborFinset u) := Finset.mem_insert.mpr
            (huv.elim (fun e => Or.inl e.symm) (fun a => Or.inr ((H.mem_neighborFinset u v).mpr a)))
          calc latticeW H ε κ 0 Y' * Real.exp (α * Y'.1.card)
              = (if v ∈ Y'.1 then latticeW H ε κ 0 Y' * Real.exp (α * Y'.1.card) else 0) := by
                rw [ite_eq_left hv]
            _ ≤ ∑ v ∈ insert u (H.neighborFinset u),
                (if v ∈ Y'.1 then latticeW H ε κ 0 Y' * Real.exp (α * Y'.1.card) else 0) :=
                Finset.single_le_sum (f := fun v => (if v ∈ Y'.1 then latticeW H ε κ 0 Y' *
                  Real.exp (α * Y'.1.card) else 0)) (fun v _ => hterm0 v Y') hvN
            _ ≤ _ := Finset.single_le_sum (f := fun u => ∑ v ∈ insert u (H.neighborFinset u),
                  (if v ∈ Y'.1 then latticeW H ε κ 0 Y' * Real.exp (α * Y'.1.card) else 0))
                  (fun u _ => Finset.sum_nonneg (fun v _ => hterm0 v Y')) hu
        · rw [ite_eq_right hl]
          exact Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ => hterm0 v Y'))
    _ = ∑ u ∈ Y.1, ∑ v ∈ insert u (H.neighborFinset u), E v := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [Finset.sum_comm]
    _ ≤ ∑ u ∈ Y.1, ∑ _v ∈ insert u (H.neighborFinset u), α / ((Δ : ℝ) + 1) :=
        Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hent v))
    _ ≤ ∑ _u ∈ Y.1, α := by
        refine Finset.sum_le_sum (fun u _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc : ((insert u (H.neighborFinset u)).card : ℝ) ≤ (Δ : ℝ) + 1 := by
          have h1 := Finset.card_insert_le u (H.neighborFinset u)
          rw [SimpleGraph.card_neighborFinset_eq_degree] at h1
          have h2 := hdeg u
          exact_mod_cast (show (insert u (H.neighborFinset u)).card ≤ Δ + 1 by omega)
        calc ((insert u (H.neighborFinset u)).card : ℝ) * (α / ((Δ : ℝ) + 1))
            ≤ ((Δ : ℝ) + 1) * (α / ((Δ : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right hc (div_nonneg hα hD.le)
          _ = α := by field_simp
    _ = α * Y.1.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **P8, touch version.** Polymers are incompatible iff they share or neighbour a vertex (`touch`). -/
theorem cluster_ratio_touch {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) {ε κ α : ℝ} (hε : 0 ≤ ε)
    (hq : (Δ : ℝ) ^ 2 * Real.exp (-(κ - α)) < 1)
    (hcond : ((Δ : ℝ) + 1) * ε * Real.exp (-(κ - α)) / (1 - (Δ : ℝ) ^ 2 * Real.exp (-(κ - α))) ≤ α)
    (K : BlockPolymer H → ℂ) (hK : ∀ X, ‖K X‖ ≤ ε * Real.exp (-κ * X.1.card)) (S : Finset V) :
    Xi (touch H) K ≠ 0 ∧
      ‖XiAvoid (touch H) (fun X : BlockPolymer H => X.1) S K / Xi (touch H) K‖ ≤
        Real.exp (α * S.card) := by
  obtain ⟨hα, hKP, hent⟩ := touch_kp H hdeg hε hq hcond
  have hD : (1 : ℝ) ≤ (Δ : ℝ) + 1 := by have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg Δ; linarith
  refine ratio_generic_div (touch H) (fun X : BlockPolymer H => X.1) (touch_refl H) hKP
    (fun b => (hent b).trans (div_le_self hα hD)) K (fun X => ?_) S
  refine (hK X).trans (le_of_eq ?_)
  unfold latticeW
  simp

/-- **P8, explicit constants.** `touch` incompatibility, `‖K γ‖ ≤ ε ^ |γ|` with `ε ≤ 1 / (2 e (Δ + 1)²)`, `α = 1`. -/
theorem cluster_ratio_touch_explicit {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / (2 * Real.exp 1 * ((Δ : ℝ) + 1) ^ 2))
    (K : BlockPolymer H → ℂ) (hK : ∀ X, ‖K X‖ ≤ ε ^ X.1.card) (S : Finset V) :
    Xi (touch H) K ≠ 0 ∧
      ‖XiAvoid (touch H) (fun X : BlockPolymer H => X.1) S K / Xi (touch H) K‖ ≤
        Real.exp (S.card : ℝ) := by
  set D : ℝ := (Δ : ℝ) + 1 with hDdef
  have hΔ0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg Δ
  have hD1 : 1 ≤ D := by rw [hDdef]; linarith
  set ε0 : ℝ := 1 / (2 * Real.exp 1 * D ^ 2) with hε0def
  have hε0pos : 0 < ε0 := by rw [hε0def]; positivity
  set κ : ℝ := -Real.log ε0 with hκ
  set t : ℝ := ε0 * Real.exp 1 with htdef
  have hE : Real.exp (-(κ - 1)) = t := by
    rw [show -(κ - 1) = Real.log ε0 + 1 by rw [hκ]; ring, Real.exp_add, Real.exp_log hε0pos]
  have ht : t * (2 * D ^ 2) = 1 := by
    rw [htdef, hε0def]
    have := Real.exp_pos 1
    field_simp
  have htpos : 0 < t := by rw [htdef]; positivity
  have hq : (Δ : ℝ) ^ 2 * Real.exp (-(κ - 1)) < 1 := by
    rw [hE]
    have h1 : (Δ : ℝ) ^ 2 < 2 * D ^ 2 := by rw [hDdef]; nlinarith
    nlinarith
  have hcond : ((Δ : ℝ) + 1) * 1 * Real.exp (-(κ - 1)) / (1 - (Δ : ℝ) ^ 2 * Real.exp (-(κ - 1))) ≤ 1 := by
    rw [hE, ← hDdef]
    have hpos : 0 < 1 - (Δ : ℝ) ^ 2 * t := by rw [hE] at hq; linarith
    rw [div_le_one hpos]
    have h1 : D + (Δ : ℝ) ^ 2 ≤ 2 * D ^ 2 := by rw [hDdef]; nlinarith
    nlinarith
  have hK' : ∀ X : BlockPolymer H, ‖K X‖ ≤ 1 * Real.exp (-κ * X.1.card) := by
    intro X
    refine (hK X).trans ?_
    rw [one_mul, hκ, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hε0pos]
    exact pow_le_pow_left₀ hε0 (by rw [hε0def, hDdef]; exact hε) _
  have := cluster_ratio_touch H hdeg (ε := 1) (κ := κ) (α := 1) zero_le_one hq hcond K hK' S
  simpa using this

-- #print axioms cluster_ratio_touch_explicit  -- [propext, Classical.choice, Quot.sound]
-- #print axioms cluster_ratio_overlap         -- [propext, Classical.choice, Quot.sound]
-- #print axioms XiAvoid_eq                    -- [propext, Classical.choice, Quot.sound]

end Lattice

end AreaLaw.ClusterRatio
