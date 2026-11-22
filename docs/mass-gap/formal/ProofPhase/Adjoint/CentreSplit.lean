/-
Cycle 2, workstream A (the adjoint half): the centre split of the coarse potentials and the halves of D′ (2026-11-22).
Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/proof-phase/c2a-adjoint/NOTE.md`, section 1.
-/

import ProofPhase.RouteA.BlockedSlab

/-!
# The adjoint half and the centre half of D′, and why together they give `LimitDprime`

**Setting.** Coarse potentials `V : Finset ι → (ι → G) → ℝ` (one log-factor per set of coarse links, depending on that set,
as `ProofPhase.CoarsePot`), a group `G` and a central element `c` with `c * c = 1` (for SU(2): `c = −1`, `negOneSU2`).
Flipping the links of a set `F` (`centreFlip c F U`: `U_l ↦ c U_l` for `l ∈ F`) is the local centre action.

* `centreAvg c V A U = 2^{-|A|} ∑_{F ⊆ A} V A (centreFlip c F U)`: the **centre-blind (adjoint) part** of the factor `A`,
  the projection on the trivial character of `Z₂^A`. `centreAvg_flip`: it is invariant under the flip of any single link
  (so it is a function of the adjoint images of the links); `centreAvg_of_blind`: a factor that is already centre-blind
  is its own centre-blind part; `centreAvg_eq_zero_of_odd`: a factor that is odd under the flip of one of its links
  (the fundamental Wilson plaquette, the U(1) plaquette `cos θ_p`, the Z₂ plaquette) has centre-blind part `0`.
* `centrePart c V = V − centreAvg c V`: the **centre-charged part**; `centreAvg_centrePart`: its centre-blind part is `0`.
* `pairOsc_add`, `tanh_half_add_le`, `flatW_add`: pair oscillations and the weighted criterion D′_λ are subadditive
  under a sum of potentials.
* **`AdjointHalf lam γA Vinf`**: the centre-blind parts of the limit potentials at `L₁` satisfy D′_λ with `γA` in every
  volume; **`CentreHalf lam γC Vinf`**: the centre-charged parts satisfy D′_λ with `γC`.
* **`limitDprime_of_halves`**: `AdjointHalf γA ∧ CentreHalf γC ∧ γA + γC < 1 ⇒ LimitDprime` (P4.1′'s open hypothesis).
* **`slabDecay_of_halves`**, **`massGap_of_goodBlocking_halves`**, **`blockedTorusRoute_of_halves`**,
  `blockedSlabRoute_of_halves`: the blocked routes (and the assembly's `BlockedTorusRoute` disjunct) with the two halves
  in place of `LimitDprime`.

**Claim level.** The split and its properties are elementary (Fourier analysis on `Z₂^A`); `limitDprime_of_halves` is
substantive-elementary (subadditivity of the Dobrushin coefficients); the route theorems are compositions with
workstream 1's `slabDecay_of_blockedRoute`. All Yang–Mills content is in the hypotheses `H1Local`, `AdjointHalf`,
`CentreHalf`, `ObsTransfer`, which are open. The halves are a sufficient condition for `LimitDprime`, not equivalent to
it (`LimitDprime` uses the oscillation of the whole factor, which can be smaller than the sum of the two).

**Unit tests in Lean form.** `centreAvg_eq_zero_of_odd`: for every action whose factors are odd under a single centre flip
(4D U(1) Wilson, Z₂ Wilson, SU(2) fundamental Wilson) the adjoint half holds trivially (`γA = 0`), so for them the halves
criterion is the centre half alone; the photon and weak-coupling Z₂ fail it there (their centre-charged couplings are of
order one at every scale). A centre-blind condition alone cannot see the photon (workstream 1, §1.3).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.LinkDist Attempts.R3

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Adjoint

/-! ## The local centre action -/

section Flip

variable {ι G : Type*} [DecidableEq ι] [Group G]

/-- Flip the links of `F` by the central element `c`: `U_l ↦ c U_l` for `l ∈ F`. -/
def centreFlip (c : G) (F : Finset ι) (U : ι → G) : ι → G := fun l => if l ∈ F then c * U l else U l

theorem centreFlip_empty (c : G) (U : ι → G) : centreFlip c ∅ U = U := by
  funext l; simp [centreFlip]

theorem centreFlip_centreFlip {c : G} (hc : c * c = 1) (F F' : Finset ι) (U : ι → G) :
    centreFlip c F (centreFlip c F' U) = centreFlip c (symmDiff F F') U := by
  funext l
  simp only [centreFlip, Finset.mem_symmDiff]
  by_cases h1 : l ∈ F <;> by_cases h2 : l ∈ F' <;> simp [h1, h2, ← mul_assoc, hc]

theorem centreFlip_eqOn {c : G} {F : Finset ι} {A : Finset ι} {U U' : ι → G} (h : ∀ l ∈ A, U l = U' l) :
    ∀ l ∈ A, centreFlip c F U l = centreFlip c F U' l := by
  intro l hl
  simp only [centreFlip, h l hl]

/-- A factor potential depends only on its own link set. -/
def FactorDep (V : Finset ι → (ι → G) → ℝ) : Prop :=
  ∀ A (U U' : ι → G), (∀ l ∈ A, U l = U' l) → V A U = V A U'

/-- The symmetric difference with a member of `A` is an involution of `A.powerset`. -/
theorem sum_powerset_symmDiff {A : Finset ι} {l : ι} (hl : l ∈ A) (φ : Finset ι → ℝ) :
    ∑ F ∈ A.powerset, φ (symmDiff F {l}) = ∑ F ∈ A.powerset, φ F := by
  refine Finset.sum_nbij' (fun F => symmDiff F {l}) (fun F => symmDiff F {l}) ?_ ?_ ?_ ?_ ?_
  · intro F hF
    simp only [Finset.mem_coe, Finset.mem_powerset] at hF ⊢
    intro x hx
    rcases Finset.mem_symmDiff.1 hx with ⟨hx1, -⟩ | ⟨hx1, -⟩
    · exact hF hx1
    · rw [Finset.mem_singleton.1 hx1]; exact hl
  · intro F hF
    simp only [Finset.mem_coe, Finset.mem_powerset] at hF ⊢
    intro x hx
    rcases Finset.mem_symmDiff.1 hx with ⟨hx1, -⟩ | ⟨hx1, -⟩
    · exact hF hx1
    · rw [Finset.mem_singleton.1 hx1]; exact hl
  · intro F _; simp [symmDiff_symmDiff_cancel_right]
  · intro F _; simp [symmDiff_symmDiff_cancel_right]
  · intro F _; rfl

/-! ## The centre-blind (adjoint) part and the centre-charged part -/

/-- **The centre-blind (adjoint) part** of the factor `A`: the average over the `2^{|A|}` centre flips of its links. -/
def centreAvg (c : G) (V : Finset ι → (ι → G) → ℝ) (A : Finset ι) (U : ι → G) : ℝ :=
  ((2 : ℝ) ^ A.card)⁻¹ * ∑ F ∈ A.powerset, V A (centreFlip c F U)

/-- **The centre-charged part** of the factor `A`: the rest. -/
def centrePart (c : G) (V : Finset ι → (ι → G) → ℝ) (A : Finset ι) (U : ι → G) : ℝ :=
  V A U - centreAvg c V A U

theorem centreAvg_add_centrePart (c : G) (V : Finset ι → (ι → G) → ℝ) (A : Finset ι) (U : ι → G) :
    centreAvg c V A U + centrePart c V A U = V A U := by
  unfold centrePart; ring

/-- **The centre-blind part is centre-blind:** invariant under the flip of any single link. -/
theorem centreAvg_flip {c : G} (hc : c * c = 1) {V : Finset ι → (ι → G) → ℝ} (hV : FactorDep V) (A : Finset ι)
    (l : ι) (U : ι → G) : centreAvg c V A (centreFlip c {l} U) = centreAvg c V A U := by
  unfold centreAvg
  congr 1
  by_cases hl : l ∈ A
  · simp_rw [centreFlip_centreFlip hc]
    exact sum_powerset_symmDiff hl (fun F => V A (centreFlip c F U))
  · refine Finset.sum_congr rfl fun F _ => hV A _ _ ?_
    refine centreFlip_eqOn (fun x hx => ?_)
    have hxl : x ≠ l := fun h => hl (h ▸ hx)
    simp [centreFlip, hxl]

/-- A factor that is already centre-blind is its own centre-blind part. -/
theorem centreAvg_of_blind {c : G} {V : Finset ι → (ι → G) → ℝ} {A : Finset ι}
    (hb : ∀ F U, V A (centreFlip c F U) = V A U) (U : ι → G) : centreAvg c V A U = V A U := by
  unfold centreAvg
  simp_rw [hb]
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  push_cast
  field_simp

/-- **A factor odd under the flip of one of its links has centre-blind part `0`** (the fundamental plaquette of SU(2), the
U(1) plaquette `cos θ_p`, the Z₂ plaquette: the unit tests' actions have no adjoint half). -/
theorem centreAvg_eq_zero_of_odd {c : G} (hc : c * c = 1) {V : Finset ι → (ι → G) → ℝ} {A : Finset ι} {l : ι}
    (hl : l ∈ A) (hodd : ∀ U, V A (centreFlip c {l} U) = -V A U) (U : ι → G) : centreAvg c V A U = 0 := by
  unfold centreAvg
  have h := sum_powerset_symmDiff hl (fun F => V A (centreFlip c F U))
  have h2 : ∑ F ∈ A.powerset, V A (centreFlip c (symmDiff F {l}) U) =
      -∑ F ∈ A.powerset, V A (centreFlip c F U) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [symmDiff_comm, ← centreFlip_centreFlip hc, hodd]
  have : ∑ F ∈ A.powerset, V A (centreFlip c F U) = 0 := by linarith
  rw [this, mul_zero]

/-- The centre-charged part has centre-blind part `0`. -/
theorem centreAvg_centrePart {c : G} (hc : c * c = 1) {V : Finset ι → (ι → G) → ℝ} (hV : FactorDep V)
    (A : Finset ι) (U : ι → G) : centreAvg c (centrePart c V) A U = 0 := by
  have hblind : ∀ F (U : ι → G), centreAvg c V A (centreFlip c F U) = centreAvg c V A U := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro U; rw [centreFlip_empty]
    | insert a s ha ih =>
      intro U
      have : centreFlip c (insert a s) U = centreFlip c {a} (centreFlip c s U) := by
        rw [centreFlip_centreFlip hc]
        congr 1
        ext x
        simp only [Finset.mem_insert, Finset.mem_symmDiff, Finset.mem_singleton]
        constructor
        · rintro (rfl | hx)
          · exact Or.inl ⟨rfl, ha⟩
          · exact Or.inr ⟨hx, fun h => ha (h ▸ hx)⟩
        · rintro (⟨rfl, -⟩ | ⟨hx, -⟩)
          · exact Or.inl rfl
          · exact Or.inr hx
      rw [this, centreAvg_flip hc hV, ih]
  unfold centreAvg centrePart
  rw [Finset.sum_sub_distrib]
  simp_rw [hblind]
  have hcard : ((2 : ℝ) ^ A.card)⁻¹ * ∑ F ∈ A.powerset, centreAvg c V A U = centreAvg c V A U := by
    rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
    push_cast
    field_simp
  rw [mul_sub, hcard]
  unfold centreAvg
  ring

end Flip

/-! ## Subadditivity of D′ -/

section Subadd

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] {X : Type*} [Fintype X]

/-- Pair oscillations are subadditive under a sum of potentials. -/
theorem pairOsc_add {supp : X → Finset ι} {V₁ V₂ : X → (ι → S) → ℝ} {S₁ S₂ : ι → ι → ℝ}
    (h₁ : PairOsc supp V₁ S₁) (h₂ : PairOsc supp V₂ S₂) :
    PairOsc supp (fun x σ => V₁ x σ + V₂ x σ) (fun i z => S₁ i z + S₂ i z) := by
  intro i z hz τ s
  have e : ∑ x ∈ pairFactors supp i z, (V₁ x τ + V₂ x τ - (V₁ x (Function.update τ z s) + V₂ x (Function.update τ z s))) =
      ∑ x ∈ pairFactors supp i z, (V₁ x τ - V₁ x (Function.update τ z s)) +
        ∑ x ∈ pairFactors supp i z, (V₂ x τ - V₂ x (Function.update τ z s)) := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun x _ => ?_; ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add (h₁ i z hz τ s) (h₂ i z hz τ s))

theorem tanh_half_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.tanh ((a + b) / 2) ≤ Real.tanh (a / 2) + Real.tanh (b / 2) := by
  rw [show (a + b) / 2 = a / 2 + b / 2 by ring]
  exact OneScale.SingleLink.tanh_add_le (by linarith) (by linarith)

/-- **D′_λ is subadditive:** criteria with `γ₁` for `S₁` and `γ₂` for `S₂` give the criterion with `γ₁ + γ₂` for
`S₁ + S₂`. -/
theorem flatW_add {dist : ι → ι → ℝ} {lam : ℝ} {S₁ S₂ : ι → ι → ℝ} {γ₁ γ₂ : ℝ} (h0₁ : ∀ i z, 0 ≤ S₁ i z)
    (h0₂ : ∀ i z, 0 ≤ S₂ i z) (h₁ : FlatCriterionW dist lam S₁ γ₁) (h₂ : FlatCriterionW dist lam S₂ γ₂) :
    FlatCriterionW dist lam (fun i z => S₁ i z + S₂ i z) (γ₁ + γ₂) := by
  intro z
  calc ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), Real.tanh ((S₁ i z + S₂ i z) / 2) * Real.exp (lam * dist z i)
      ≤ ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)),
          (Real.tanh (S₁ i z / 2) * Real.exp (lam * dist z i) + Real.tanh (S₂ i z / 2) * Real.exp (lam * dist z i)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (tanh_half_add_le (h0₁ i z) (h0₂ i z)) (Real.exp_pos _).le
    _ = _ := Finset.sum_add_distrib
    _ ≤ γ₁ + γ₂ := add_le_add (h₁ z) (h₂ z)

end Subadd

/-! ## The halves for the limit theory at `L₁` -/

/-- **The adjoint half (open).** The centre-blind parts of the limit potentials at `L₁` satisfy D′_λ with `γA`, the
same `γA` in every volume. -/
def AdjointHalf (lam γA : ℝ) (Vinf : ∀ j, CoarsePot j) : Prop :=
  ∃ Sb : ∀ j, LatticeLink 4 (coarseSide j) → LatticeLink 4 (coarseSide j) → ℝ, (∀ j i z, 0 ≤ Sb j i z) ∧
    ∀ j, PairOsc (fun A => A) (centreAvg negOneSU2 (Vinf j)) (Sb j) ∧ FlatCriterionW linkDist lam (Sb j) γA

/-- **The centre half (open; confinement-type).** The centre-charged parts of the limit potentials at `L₁` satisfy D′_λ
with `γC`, the same `γC` in every volume. -/
def CentreHalf (lam γC : ℝ) (Vinf : ∀ j, CoarsePot j) : Prop :=
  ∃ Sb : ∀ j, LatticeLink 4 (coarseSide j) → LatticeLink 4 (coarseSide j) → ℝ, (∀ j i z, 0 ≤ Sb j i z) ∧
    ∀ j, PairOsc (fun A => A) (centrePart negOneSU2 (Vinf j)) (Sb j) ∧ FlatCriterionW linkDist lam (Sb j) γC

/-- **The two halves give `LimitDprime`.** -/
theorem limitDprime_of_halves {lam γA γC : ℝ} {Vinf : ∀ j, CoarsePot j} (hA : AdjointHalf lam γA Vinf)
    (hC : CentreHalf lam γC Vinf) (h0 : 0 ≤ γA + γC) (h1 : γA + γC < 1) : LimitDprime lam Vinf := by
  obtain ⟨SA, hSA0, hSA⟩ := hA
  obtain ⟨SC, hSC0, hSC⟩ := hC
  refine ⟨γA + γC, h0, h1, fun j i z => SA j i z + SC j i z, fun j i z => add_nonneg (hSA0 j i z) (hSC0 j i z),
    fun j => ⟨?_, flatW_add (hSA0 j) (hSC0 j) (hSA j).2 (hSC j).2⟩⟩
  have e : Vinf j = fun A U => centreAvg negOneSU2 (Vinf j) A U + centrePart negOneSU2 (Vinf j) A U := by
    funext A U; rw [centreAvg_add_centrePart]
  rw [e]
  exact pairOsc_add (hSA j).1 (hSC j).1

/-- **The blocked route with the two halves** (`SlabDecay` from `H1Local`, the adjoint half, the centre half and
`ObsTransfer`). -/
theorem slabDecay_of_halves {T : Tuning} (B : BlockingFamily T) {lam γA γC : ℝ} (hlam : 0 < lam)
    {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf)
    (hA : AdjointHalf lam γA Vinf) (hC : CentreHalf lam γC Vinf) (h0 : 0 ≤ γA + γC) (hlt : γA + γC < 1)
    (h3 : ObsTransfer T B) : SlabDecay T :=
  RouteA.slabDecay_of_blockedRoute B hlam h1 (limitDprime_of_halves hA hC h0 hlt) h3

/-- **The same with the concrete good blocking, to the mass gap** (on a line of constant physics). -/
theorem massGap_of_goodBlocking_halves {T : Tuning} (hL : OnLCP T) (w : ℝ) (nk : ℕ → ℕ)
    (hn : ∀ k, T.ℓ k = 2 ^ nk k) {lam γA γC : ℝ} (hlam : 0 < lam) {Vk : ∀ j, ℕ → CoarsePot j}
    {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T (RouteA.goodBlocking T w nk hn) lam Vk Vinf)
    (hA : AdjointHalf lam γA Vinf) (hC : CentreHalf lam γC Vinf) (h0 : 0 ≤ γA + γC) (hlt : γA + γC < 1)
    (h3 : ObsTransfer T (RouteA.goodBlocking T w nk hn)) : MassGap T ∧ LatticeGap T ∧ LimitRP T :=
  RouteA.massGap_of_goodBlocking hL w nk hn hlam h1 (limitDprime_of_halves hA hC h0 hlt) h3

/-- **The torus route of the assembly from the two halves** (`OpenPieces.crossover`, first disjunct): `H1Local`, the
adjoint half, the centre half and `ObsTransferPhys` give `BlockedTorusRoute`. -/
theorem blockedTorusRoute_of_halves {T : Tuning} (B : BlockingFamily T) {lam γA γC : ℝ} (hlam : 0 < lam)
    {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf)
    (hA : AdjointHalf lam γA Vinf) (hC : CentreHalf lam γC Vinf) (h0 : 0 ≤ γA + γC) (hlt : γA + γC < 1)
    (h3 : ObsTransferPhys T B) : BlockedTorusRoute T :=
  ⟨B, lam, Vk, Vinf, hlam, h1, limitDprime_of_halves hA hC h0 hlt, h3⟩

/-- The slab route of the assembly from the two halves (second disjunct). -/
theorem blockedSlabRoute_of_halves {T : Tuning} (B : BlockingFamily T) {lam γA γC : ℝ} (hlam : 0 < lam)
    {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf)
    (hA : AdjointHalf lam γA Vinf) (hC : CentreHalf lam γC Vinf) (h0 : 0 ≤ γA + γC) (hlt : γA + γC < 1)
    (h3 : ObsTransfer T B) : BlockedSlabRoute T :=
  ⟨B, lam, Vk, Vinf, hlam, h1, limitDprime_of_halves hA hC h0 hlt, h3⟩

end ProofPhase.Adjoint
