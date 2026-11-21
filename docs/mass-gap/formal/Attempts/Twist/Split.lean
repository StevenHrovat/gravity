/-
Twist route, attempt round (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/twist/NOTE.md`, section 2 (Proposition T1).
-/

import OneScale.Blocks

/-!
# The influence splits into a twist part and a coset part

Abstract setting of `OneScale.Blocks`: configurations `ι → S` with `S` a group, a block `B`, a specification `q`, an outside
coordinate `z`, and a finite set `Z ⊆ S` containing `1` (in the application: a finite subgroup of the centre).

* `IsTwistInfluenceBound B q z Z k`: the response of the block to replacing the boundary value `σ z` by `c · σ z`, `c ∈ Z`
  (a centre twist of the single link `z`), is at most `k L` on every block observable with single-link oscillations `≤ L`.
* `cosetAvg q z Z σ F g = |Z|⁻¹ ∑_{c ∈ Z} q^{σ[z ↦ c g]}(F)`: the response averaged over the `Z`-coset of the boundary value;
  it depends on `g` only through its class in `Z \ S` when `Z` is a subgroup.
* `IsCosetInfluenceBound B q z Z k`: the influence of `z` through its coset (the twist-blind, "adjoint" part).
* `isInfluenceBound_of_split` (**Proposition T1**): `k^H ≤ k_coset + 2 (1 - 1/|Z|) k_twist`.
* `twist_le`, `coset_le`: conversely both parts are at most `k^H`. So `max(k_coset, k_twist) ≤ k^H ≤ k_coset + 2 k_twist`:
  the twist sees exactly the central part of the influence, up to a factor 2, and nothing of the coset part.
* `cosetInfluence_univ`, `isInfluenceBound_of_twist_univ`: for a finite group with `Z = S` (e.g. `Z₂` gauge theory) the coset
  part vanishes and the whole influence is a twist response: `k^H ≤ 2 (1 - 1/|S|) k_twist` (`= k_twist` for `Z₂`).
-/

open MeasureTheory Finset OneScale

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.Twist

variable {ι S : Type*} [DecidableEq ι] [MeasurableSpace S] [Group S]

/-- The block response to a centre twist of the single outside coordinate `z` by `c ∈ Z`. -/
def IsTwistInfluenceBound (B : Finset ι) (q : (ι → S) → Measure (ι → S)) (z : ι) (Z : Finset S) (k : ℝ) : Prop :=
  ∀ (σ : ι → S) (c : S), c ∈ Z → ∀ (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B →
    (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) →
    |∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q (Function.update σ z (c * σ z)))| ≤ k * L

/-- The block response averaged over the `Z`-coset `{c g : c ∈ Z}` of the boundary value at `z`. -/
def cosetAvg (q : (ι → S) → Measure (ι → S)) (z : ι) (Z : Finset S) (σ : ι → S) (F : (ι → S) → ℝ) (g : S) : ℝ :=
  (∑ c ∈ Z, ∫ ξ, F ξ ∂(q (Function.update σ z (c * g)))) / Z.card

/-- The influence of `z` through its `Z`-coset only (the part a centre twist cannot see). -/
def IsCosetInfluenceBound (B : Finset ι) (q : (ι → S) → Measure (ι → S)) (z : ι) (Z : Finset S) (k : ℝ) : Prop :=
  ∀ (σ : ι → S) (g g' : S) (F : (ι → S) → ℝ) (L : ℝ), BM F → DepOn F B →
    (∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) →
    |cosetAvg q z Z σ F g - cosetAvg q z Z σ F g'| ≤ k * L

variable {B : Finset ι} {q : (ι → S) → Measure (ι → S)} {z : ι} {Z : Finset S}

/-- The response as a function of the boundary value at `z`. -/
private def resp (q : (ι → S) → Measure (ι → S)) (z : ι) (σ : ι → S) (F : (ι → S) → ℝ) (g : S) : ℝ :=
  ∫ ξ, F ξ ∂(q (Function.update σ z g))

/-- The response differs from its coset average by at most `(|Z| - 1)/|Z| · k_twist · L`. -/
theorem abs_resp_sub_cosetAvg_le [DecidableEq S] (h1 : (1 : S) ∈ Z) {kT : ℝ} (hT : IsTwistInfluenceBound B q z Z kT)
    (σ : ι → S) (F : (ι → S) → ℝ) (L : ℝ) (hF : BM F) (hdep : DepOn F B)
    (hosc : ∀ ξ y t, y ∈ B → |F ξ - F (Function.update ξ y t)| ≤ L) (g : S) :
    |resp q z σ F g - cosetAvg q z Z σ F g| ≤ ((Z.card - 1 : ℝ) / Z.card) * (kT * L) := by
  have hcard : (0 : ℝ) < Z.card := by exact_mod_cast Finset.card_pos.2 ⟨1, h1⟩
  -- each twisted response is within `kT L` of the untwisted one
  have hterm : ∀ c ∈ Z, |resp q z σ F g - resp q z σ F (c * g)| ≤ kT * L := by
    intro c hc
    have := hT (Function.update σ z g) c hc F L hF hdep hosc
    simpa [resp, Function.update_idem, Function.update_self] using this
  have hkL : 0 ≤ kT * L := (abs_nonneg _).trans (hterm 1 h1)
  have hc : cosetAvg q z Z σ F g = (∑ c ∈ Z, resp q z σ F (c * g)) / Z.card := rfl
  have hsum : resp q z σ F g - cosetAvg q z Z σ F g =
      (∑ c ∈ Z, (resp q z σ F g - resp q z σ F (c * g))) / Z.card := by
    rw [hc, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, eq_div_iff hcard.ne', sub_mul,
      div_mul_cancel₀ _ hcard.ne']
    ring
  have h1' : resp q z σ F g - resp q z σ F (1 * g) = 0 := by simp
  have hbound : |∑ c ∈ Z, (resp q z σ F g - resp q z σ F (c * g))| ≤ ((Z.card - 1 : ℝ)) * (kT * L) :=
    calc |∑ c ∈ Z, (resp q z σ F g - resp q z σ F (c * g))|
        ≤ ∑ c ∈ Z, |resp q z σ F g - resp q z σ F (c * g)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ c ∈ Z.erase 1, |resp q z σ F g - resp q z σ F (c * g)| := by
          rw [← Finset.add_sum_erase Z _ h1, h1', abs_zero, zero_add]
      _ ≤ ∑ c ∈ Z.erase 1, kT * L := Finset.sum_le_sum fun c hc => hterm c (Finset.mem_of_mem_erase hc)
      _ = ((Z.card - 1 : ℝ)) * (kT * L) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem h1,
            Nat.cast_sub (Finset.card_pos.2 ⟨1, h1⟩), Nat.cast_one]
  rw [hsum, abs_div, abs_of_pos hcard]
  calc |∑ c ∈ Z, (resp q z σ F g - resp q z σ F (c * g))| / Z.card
      ≤ ((Z.card - 1 : ℝ)) * (kT * L) / Z.card := div_le_div_of_nonneg_right hbound hcard.le
    _ = ((Z.card - 1 : ℝ) / Z.card) * (kT * L) := by ring

/-- **Proposition T1 (split of the influence).** If the twist part is bounded by `kT` and the coset part by `kA`, the full
dual-form influence coefficient is at most `kA + 2 (1 - 1/|Z|) kT`. -/
theorem isInfluenceBound_of_split [DecidableEq S] (h1 : (1 : S) ∈ Z) {kT kA : ℝ} (hT : IsTwistInfluenceBound B q z Z kT)
    (hA : IsCosetInfluenceBound B q z Z kA) :
    IsInfluenceBound B q z (kA + 2 * ((Z.card - 1 : ℝ) / Z.card) * kT) := by
  intro σ s F L hF hdep hosc
  have e0 : q σ = q (Function.update σ z (σ z)) := by rw [Function.update_eq_self]
  have ha := abs_resp_sub_cosetAvg_le h1 hT σ F L hF hdep hosc (σ z)
  have hb := abs_resp_sub_cosetAvg_le h1 hT σ F L hF hdep hosc s
  have hc := hA σ (σ z) s F L hF hdep hosc
  have : ∫ ξ, F ξ ∂(q σ) - ∫ ξ, F ξ ∂(q (Function.update σ z s)) =
      (resp q z σ F (σ z) - cosetAvg q z Z σ F (σ z)) +
        (cosetAvg q z Z σ F (σ z) - cosetAvg q z Z σ F s) - (resp q z σ F s - cosetAvg q z Z σ F s) := by
    simp only [resp]; rw [← e0]; ring
  rw [this]
  set X := resp q z σ F (σ z) - cosetAvg q z Z σ F (σ z)
  set Y := cosetAvg q z Z σ F (σ z) - cosetAvg q z Z σ F s
  set V := resp q z σ F s - cosetAvg q z Z σ F s
  have htri : |X + Y - V| ≤ |X| + |Y| + |V| :=
    (abs_sub (X + Y) V).trans (add_le_add (abs_add_le X Y) le_rfl)
  refine htri.trans ?_
  calc |X| + |Y| + |V|
      ≤ ((Z.card - 1 : ℝ) / Z.card) * (kT * L) + kA * L + ((Z.card - 1 : ℝ) / Z.card) * (kT * L) :=
        add_le_add (add_le_add ha hc) hb
    _ = (kA + 2 * ((Z.card - 1 : ℝ) / Z.card) * kT) * L := by ring

/-- The twist part is at most the full influence. -/
theorem twist_le {k : ℝ} (h : IsInfluenceBound B q z k) : IsTwistInfluenceBound B q z Z k :=
  fun σ c _ F L hF hdep hosc => h σ (c * σ z) F L hF hdep hosc

/-- The coset part is at most the full influence. -/
theorem coset_le (hZ : Z.Nonempty) {k : ℝ} (h : IsInfluenceBound B q z k) : IsCosetInfluenceBound B q z Z k := by
  intro σ g g' F L hF hdep hosc
  have hcard : (0 : ℝ) < Z.card := by exact_mod_cast Finset.card_pos.2 hZ
  unfold cosetAvg
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
  calc _ ≤ ∑ c ∈ Z, |∫ ξ, F ξ ∂(q (Function.update σ z (c * g))) - ∫ ξ, F ξ ∂(q (Function.update σ z (c * g')))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ Z, k * L := Finset.sum_le_sum fun c _ => by
        have := h (Function.update σ z (c * g)) (c * g') F L hF hdep hosc
        simpa [Function.update_idem] using this
    _ = k * L * Z.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- For a finite group and `Z = S`, the coset average does not depend on the boundary value: the coset part vanishes. -/
theorem cosetInfluence_univ [Fintype S] : IsCosetInfluenceBound B q z (Finset.univ : Finset S) 0 := by
  intro σ g g' F L _ _ _
  have : cosetAvg q z Finset.univ σ F g = cosetAvg q z Finset.univ σ F g' := by
    unfold cosetAvg
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight (g * g'⁻¹)) _ _ fun c => by simp [mul_assoc]
  simp [this]

/-- **Abelian finite case (e.g. `Z₂` gauge theory).** For a finite group with `Z = S` the whole influence is a twist
response: `k^H ≤ 2 (1 - 1/|S|) k_twist` (equal to `k_twist` for `|S| = 2`). -/
theorem isInfluenceBound_of_twist_univ [Fintype S] [DecidableEq S] {kT : ℝ}
    (hT : IsTwistInfluenceBound B q z (Finset.univ : Finset S) kT) :
    IsInfluenceBound B q z (2 * ((Fintype.card S - 1 : ℝ) / Fintype.card S) * kT) := by
  have := isInfluenceBound_of_split (Finset.mem_univ (1 : S)) hT (cosetInfluence_univ (B := B) (q := q) (z := z))
  simpa [Finset.card_univ] using this

end Attempts.Twist
