/-
The time reflection between time slices (positivity project, 2026-11-21). Released under Apache 2.0.

# The link reflection `t ↦ −1 − t` on (ℤ/Nℤ)^d

Direction `0` is time, `N` even, `M = N/2`. The reflection `t ↦ −1 − t (mod N)` fixes no site; it maps the slices
`0, …, M − 1` (the positive half) onto `M, …, N − 1` and back. Its planes lie between the slices `M − 1 | M` and
`N − 1 | 0`. Links:

- positive: spatial links with `t < M`, temporal links from `t` to `t + 1` with `t + 2 ≤ M` (both ends positive);
- crossing: temporal links from `t = M − 1` and from `t = N − 1` (they cross a reflection plane; the reflection maps each
  to itself, reversed);
- negative: the rest (the mirror images of the positive links).

Plaquettes: positive (all four links positive), crossing (temporal plaquettes starting at `t = M − 1` or `t = N − 1`;
two crossing links, one positive and one negative spatial link), negative (mirrors of the positive ones).

On connections `(Θ U)(l) = U(mirror l)⁻¹` for temporal `l` and `U(mirror l)` for spatial `l` (`thetaL`), and
`Re tr U_q(Θ U) = Re tr U_{mirror q}(U)` (`xp_thetaL`).
-/

import Positivity.Reflection

open MeasureTheory
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Positivity

variable {d N : ℕ}

theorem val_neg_sub_two [NeZero N] (a : ZMod N) :
    (-a - 2).val = if a.val + 2 ≤ N then N - 2 - a.val else 2 * N - 2 - a.val := by
  have ha := ZMod.val_lt a
  split_ifs with h
  · apply zmod_val_eq_of_cast (by omega)
    have h1 := congrArg (Nat.cast : ℕ → ZMod N) (show (N - 2 - a.val) + a.val + 2 = N by omega)
    push_cast [ZMod.natCast_self, ZMod.natCast_zmod_val] at h1
    linear_combination h1
  · apply zmod_val_eq_of_cast (by omega)
    have h1 := congrArg (Nat.cast : ℕ → ZMod N) (show (2 * N - 2 - a.val) + a.val + 2 = 2 * N by omega)
    push_cast [ZMod.natCast_self, ZMod.natCast_zmod_val, mul_zero] at h1
    linear_combination h1

theorem val_add_one_eq [NeZero N] (a : ZMod N) : (a + 1).val = if a.val + 1 = N then 0 else a.val + 1 := by
  have ha := ZMod.val_lt a
  split_ifs with h
  · apply zmod_val_eq_of_cast (Nat.pos_of_ne_zero (NeZero.ne N))
    have h1 := congrArg (Nat.cast : ℕ → ZMod N) h
    push_cast [ZMod.natCast_self, ZMod.natCast_zmod_val] at h1
    rw [h1, Nat.cast_zero]
  · exact val_add_one_of_lt a (by omega)

/-! ## The flips `t ↦ −t − k` -/

variable [NeZero d]

/-- The site with time coordinate `−t − k`. -/
def flipK (k : ZMod N) (x : FinLatticeSites d N) : FinLatticeSites d N := Function.update x 0 (-(x 0) - k)

theorem flipK_zero (k : ZMod N) (x : FinLatticeSites d N) : flipK k x 0 = -(x 0) - k := by simp [flipK]

theorem flipK_siteShift (k : ZMod N) (x : FinLatticeSites d N) {μ : Fin d} (hμ : μ ≠ 0) :
    flipK k (siteShift d N x μ) = siteShift d N (flipK k x) μ := by
  funext i
  simp only [flipK, siteShift, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem flipK_one_siteShift_zero (x : FinLatticeSites d N) : flipK 1 (siteShift d N x 0) = flipK 2 x := by
  funext i
  simp only [flipK, siteShift, Function.update_apply]
  split_ifs <;> simp_all; ring

theorem siteShift_flipK_two_zero (x : FinLatticeSites d N) : siteShift d N (flipK 2 x) 0 = flipK 1 x := by
  funext i
  simp only [flipK, siteShift, Function.update_apply]
  split_ifs <;> (try simp_all) <;> ring

theorem flipK_flipK (k : ZMod N) (x : FinLatticeSites d N) : flipK k (flipK k x) = x := by
  funext i
  simp only [flipK, Function.update_apply]
  split_ifs <;> simp_all

theorem flip1_time [NeZero N] (x : FinLatticeSites d N) : (flipK 1 x 0).val = N - 1 - (x 0).val := by
  rw [flipK_zero, val_neg_sub_one]

theorem flip2_time [NeZero N] (x : FinLatticeSites d N) :
    (flipK 2 x 0).val = if (x 0).val + 2 ≤ N then N - 2 - (x 0).val else 2 * N - 2 - (x 0).val := by
  rw [flipK_zero, val_neg_sub_two]

/-! ## Mirror links and plaquettes -/

/-- The mirror image of a link under `t ↦ −1 − t` (temporal links are reversed). -/
def mirrorL (l : LatticeLink d N) : LatticeLink d N :=
  if l.dir = 0 then ⟨flipK 2 l.site, l.dir⟩ else ⟨flipK 1 l.site, l.dir⟩

/-- The mirror image of a plaquette under `t ↦ −1 − t`. -/
def mirrorPL (p : LatticePlaquette d N) : LatticePlaquette d N :=
  if p.dir1 = 0 then ⟨flipK 2 p.site, p.dir1, p.dir2, p.h_lt⟩ else ⟨flipK 1 p.site, p.dir1, p.dir2, p.h_lt⟩

theorem mirrorL_involutive : Function.Involutive (mirrorL (d := d) (N := N)) := by
  rintro ⟨s, μ⟩
  by_cases h : μ = 0 <;> simp [mirrorL, h, flipK_flipK]

theorem mirrorPL_involutive : Function.Involutive (mirrorPL (d := d) (N := N)) := by
  rintro ⟨s, μ, ν, h⟩
  by_cases hμ : μ = 0 <;> simp [mirrorPL, hμ, flipK_flipK]

theorem mirrorL_dir (l : LatticeLink d N) : (mirrorL l).dir = l.dir := by
  unfold mirrorL; split_ifs <;> rfl

/-! ## Positive, crossing and negative links and plaquettes -/

/-- Positive links: spatial with `t < N/2`, temporal from `t` to `t + 1` with `t + 2 ≤ N/2`. -/
def IsPosL (l : LatticeLink d N) : Prop :=
  (l.dir ≠ 0 ∧ (l.site 0).val < N / 2) ∨ (l.dir = 0 ∧ (l.site 0).val + 2 ≤ N / 2)

/-- Crossing links: temporal links from `t = N/2 − 1` or from `t = N − 1`. -/
def IsCrossL (l : LatticeLink d N) : Prop :=
  l.dir = 0 ∧ ((l.site 0).val + 1 = N / 2 ∨ (l.site 0).val + 1 = N)

/-- Positive plaquettes: spatial with `t < N/2`, temporal with `t + 2 ≤ N/2`. -/
def IsPosPL (p : LatticePlaquette d N) : Prop :=
  (p.dir1 ≠ 0 ∧ (p.site 0).val < N / 2) ∨ (p.dir1 = 0 ∧ (p.site 0).val + 2 ≤ N / 2)

/-- Crossing plaquettes: temporal plaquettes starting at `t = N/2 − 1` or at `t = N − 1`. -/
def IsCrossPL (p : LatticePlaquette d N) : Prop :=
  p.dir1 = 0 ∧ ((p.site 0).val + 1 = N / 2 ∨ (p.site 0).val + 1 = N)

variable [NeZero N]

theorem not_cross_of_posL {l : LatticeLink d N} (h : IsPosL l) : ¬IsCrossL l := by
  unfold IsPosL IsCrossL at *; omega

theorem not_crossPL_of_posPL {p : LatticePlaquette d N} (h : IsPosPL p) : ¬IsCrossPL p := by
  unfold IsPosPL IsCrossPL at *; omega

theorem posL_mirror (hN : Even N) {l : LatticeLink d N} (h : IsPosL l) :
    ¬IsPosL (mirrorL l) ∧ ¬IsCrossL (mirrorL l) := by
  obtain ⟨k, hk⟩ := hN
  rcases l with ⟨s, μ⟩
  have ht := ZMod.val_lt (s 0)
  have h0 : ((0 : Fin d) : ℕ) = 0 := Fin.val_zero d
  by_cases hμ : μ = 0
  · subst hμ
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorL, IsPosL, IsCrossL, flip2_time] at h ⊢
    (try split_ifs) <;> omega
  · have hμv : (μ : ℕ) ≠ 0 := fun h => hμ (Fin.ext (by rw [h, h0]))
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorL, hμ, IsPosL, IsCrossL, flip1_time] at h ⊢
    omega

theorem negL_mirror (hN : Even N) {l : LatticeLink d N} (h1 : ¬IsPosL l) (h2 : ¬IsCrossL l) :
    IsPosL (mirrorL l) := by
  obtain ⟨k, hk⟩ := hN
  rcases l with ⟨s, μ⟩
  have ht := ZMod.val_lt (s 0)
  have h0 : ((0 : Fin d) : ℕ) = 0 := Fin.val_zero d
  by_cases hμ : μ = 0
  · subst hμ
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorL, IsPosL, IsCrossL, flip2_time] at h1 h2 ⊢
    (try split_ifs) <;> omega
  · have hμv : (μ : ℕ) ≠ 0 := fun h => hμ (Fin.ext (by rw [h, h0]))
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorL, hμ, IsPosL, IsCrossL, flip1_time] at h1 h2 ⊢
    omega

theorem flipK_two_eq_self (hN : Even N) (x : FinLatticeSites d N)
    (h : (x 0).val + 1 = N / 2 ∨ (x 0).val + 1 = N) : flipK 2 x = x := by
  obtain ⟨k, hk⟩ := hN
  have ht := ZMod.val_lt (x 0)
  have hneg : -(x 0) - 2 = x 0 := ZMod.val_injective N (by rw [val_neg_sub_two]; split_ifs <;> omega)
  simp only [flipK, hneg, Function.update_eq_self]

theorem crossL_mirror (hN : Even N) {l : LatticeLink d N} (h : IsCrossL l) : mirrorL l = l := by
  rcases l with ⟨s, μ⟩
  obtain ⟨hμ, ht⟩ := h
  dsimp only at hμ ht
  subst hμ
  simp only [mirrorL, ite_true, flipK_two_eq_self hN s ht]

theorem crossL_mirror_iff (hN : Even N) (l : LatticeLink d N) : IsCrossL (mirrorL l) ↔ IsCrossL l := by
  by_cases hc : IsCrossL l
  · rw [crossL_mirror hN hc]
  · refine iff_of_false ?_ hc
    by_cases hp : IsPosL l
    · exact (posL_mirror hN hp).2
    · exact not_cross_of_posL (negL_mirror hN hp hc)

theorem posPL_mirror (hN : Even N) {p : LatticePlaquette d N} (h : IsPosPL p) :
    ¬IsPosPL (mirrorPL p) ∧ ¬IsCrossPL (mirrorPL p) := by
  obtain ⟨k, hk⟩ := hN
  rcases p with ⟨s, μ, ν, hlt⟩
  have ht := ZMod.val_lt (s 0)
  have h0 : ((0 : Fin d) : ℕ) = 0 := Fin.val_zero d
  by_cases hμ : μ = 0
  · subst hμ
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorPL, IsPosPL, IsCrossPL, flip2_time] at h ⊢
    (try split_ifs) <;> omega
  · have hμv : (μ : ℕ) ≠ 0 := fun h => hμ (Fin.ext (by rw [h, h0]))
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorPL, hμ, IsPosPL, IsCrossPL, flip1_time] at h ⊢
    omega

theorem negPL_mirror (hN : Even N) {p : LatticePlaquette d N} (h1 : ¬IsPosPL p) (h2 : ¬IsCrossPL p) :
    IsPosPL (mirrorPL p) := by
  obtain ⟨k, hk⟩ := hN
  rcases p with ⟨s, μ, ν, hlt⟩
  have ht := ZMod.val_lt (s 0)
  have h0 : ((0 : Fin d) : ℕ) = 0 := Fin.val_zero d
  by_cases hμ : μ = 0
  · subst hμ
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorPL, IsPosPL, IsCrossPL, flip2_time] at h1 h2 ⊢
    (try split_ifs) <;> omega
  · have hμv : (μ : ℕ) ≠ 0 := fun h => hμ (Fin.ext (by rw [h, h0]))
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorPL, hμ, IsPosPL, IsCrossPL, flip1_time] at h1 h2 ⊢
    omega

/-- **Positive plaquettes have positive links only.** -/
theorem posPL_links (hN : Even N) {p : LatticePlaquette d N} (h : IsPosPL p) (i : Fin 4) :
    IsPosL (p.boundaryLinks i) := by
  obtain ⟨k, hk⟩ := hN
  rcases p with ⟨s, μ, ν, hlt⟩
  have hν : ν ≠ 0 := LatticePlaquette.dir2_ne_zero ⟨s, μ, ν, hlt⟩
  have ht := ZMod.val_lt (s 0)
  by_cases hμ : μ = 0
  · subst hμ
    simp only [IsPosPL, ne_eq, not_true_eq_false, false_and, true_and, false_or] at h
    have h1 : (s 0 + 1).val = (s 0).val + 1 := val_add_one_of_lt _ (by omega)
    fin_cases i <;>
      simp [-ZMod.val_eq_zero, -ZMod.val_pos, LatticePlaquette.boundaryLinks, IsPosL, siteShift_zero_of_ne _ hν,
        siteShift_zero_zero, h1, hν] <;> omega
  · simp only [IsPosPL, hμ, ne_eq, not_false_eq_true, true_and, false_and, or_false] at h
    fin_cases i <;>
      simp [-ZMod.val_eq_zero, -ZMod.val_pos, LatticePlaquette.boundaryLinks, IsPosL, siteShift_zero_of_ne _ hν,
        siteShift_zero_of_ne _ hμ, hν, hμ] <;> omega

/-! ## Crossing plaquettes -/

/-- Type A crossing (the plane `M − 1 | M`): the plaquette starts at `t = N/2 − 1`. -/
def IsCrossA (p : LatticePlaquette d N) : Prop := (p.site 0).val + 1 = N / 2

theorem crossPL_bl0 {p : LatticePlaquette d N} (h : IsCrossPL p) : IsCrossL (p.boundaryLinks 0) := h

theorem crossPL_bl2 {p : LatticePlaquette d N} (h : IsCrossPL p) : IsCrossL (p.boundaryLinks 2) := by
  have hν : p.dir2 ≠ 0 := LatticePlaquette.dir2_ne_zero p
  refine ⟨h.1, ?_⟩
  simp only [LatticePlaquette.boundaryLinks, siteShift_zero_of_ne _ hν]
  exact h.2

theorem crossPL_bl0_typeA {p : LatticePlaquette d N} : ((p.boundaryLinks 0).site 0).val = (p.site 0).val := rfl

theorem crossPL_bl2_time {p : LatticePlaquette d N} :
    ((p.boundaryLinks 2).site 0).val = (p.site 0).val := by
  have hν : p.dir2 ≠ 0 := LatticePlaquette.dir2_ne_zero p
  simp only [LatticePlaquette.boundaryLinks, siteShift_zero_of_ne _ hν]

theorem spatial_not_cross {l : LatticeLink d N} (h : l.dir ≠ 0) : ¬IsCrossL l := fun hc => h hc.1

/-- Type A crossing plaquettes: the link `3` (at `t = M − 1`) is positive, the link `1` (at `t = M`) is its mirror. -/
theorem crossA_links (hN : Even N) {p : LatticePlaquette d N} (h : IsCrossPL p) (hA : IsCrossA p) :
    IsPosL (p.boundaryLinks 3) ∧ mirrorL (p.boundaryLinks 3) = p.boundaryLinks 1 := by
  obtain ⟨k, hk⟩ := hN
  rcases p with ⟨s, μ, ν, hlt⟩
  have hν : ν ≠ 0 := LatticePlaquette.dir2_ne_zero ⟨s, μ, ν, hlt⟩
  obtain ⟨hμ, -⟩ := h
  simp only [IsCrossA] at hA hμ
  subst hμ
  have ht := ZMod.val_lt (s 0)
  refine ⟨Or.inl ⟨hν, by simp only [LatticePlaquette.boundaryLinks]; omega⟩, ?_⟩
  have heq : -(s 0) - 1 = s 0 + 1 := ZMod.val_injective N (by
    rw [val_neg_sub_one, val_add_one_of_lt _ (by omega)]; omega)
  simp only [LatticePlaquette.boundaryLinks, mirrorL, hν, ite_false, flipK, siteShift, heq]

/-- Type B crossing plaquettes: the link `1` (at `t = 0`) is positive, the link `3` (at `t = N − 1`) is its mirror. -/
theorem crossB_links (hN : Even N) {p : LatticePlaquette d N} (h : IsCrossPL p) (hA : ¬IsCrossA p) :
    IsPosL (p.boundaryLinks 1) ∧ mirrorL (p.boundaryLinks 1) = p.boundaryLinks 3 := by
  obtain ⟨k, hk⟩ := hN
  rcases p with ⟨s, μ, ν, hlt⟩
  have hν : ν ≠ 0 := LatticePlaquette.dir2_ne_zero ⟨s, μ, ν, hlt⟩
  obtain ⟨hμ, ht'⟩ := h
  simp only [IsCrossA] at hA hμ ht'
  subst hμ
  have ht := ZMod.val_lt (s 0)
  have htN : (s 0).val + 1 = N := by omega
  refine ⟨Or.inl ⟨hν, ?_⟩, ?_⟩
  · simp only [LatticePlaquette.boundaryLinks, siteShift_zero_zero, val_add_one_eq, htN, ite_true]
    omega
  · simp only [LatticePlaquette.boundaryLinks, mirrorL, hν, ite_false, flipK_one_siteShift_zero,
      flipK_two_eq_self ⟨k, hk⟩ s (Or.inr htN)]

/-! ## The reflection of connections -/

section Theta

variable {G : Type*} [Group G]

/-- The link reflection of a connection: `(Θ U)(l) = U(mirror l)⁻¹` for temporal `l`, `U(mirror l)` for spatial `l`. -/
def thetaL (U : GaugeConnection G d N) : GaugeConnection G d N := fun l => linkTwist l (U (mirrorL l))

theorem thetaL_involutive : Function.Involutive (thetaL (G := G) (d := d) (N := N)) := by
  intro U; funext l
  simp only [thetaL, linkTwist, mirrorL_dir, mirrorL_involutive l]
  split_ifs <;> simp

theorem linkTwist_of_dir_eq {l : LatticeLink d N} (h : l.dir = 0) (g : G) : linkTwist l g = g⁻¹ := by
  simp [linkTwist, h]

theorem linkTwist_of_dir_ne {l : LatticeLink d N} (h : l.dir ≠ 0) (g : G) : linkTwist l g = g := by
  simp [linkTwist, h]

private theorem conj_inv_identity' (a b c e : G) :
    a⁻¹ * b * c⁻¹⁻¹ * e⁻¹ = a⁻¹ * (a * e * c⁻¹ * b⁻¹)⁻¹ * a⁻¹⁻¹ := by
  group

variable {n : ℕ} [HasGaugeTrace G n]

/-- `Re tr U_q(Θ U) = Re tr U_{mirror q}(U)` for the link reflection. -/
theorem xp_thetaL (hinv : ∀ g : G, gaugeReTr G n g⁻¹ = gaugeReTr G n g) (U : GaugeConnection G d N)
    (q : LatticePlaquette d N) : xp n q (thetaL U) = xp n (mirrorPL q) U := by
  rcases q with ⟨s, μ, ν, hlt⟩
  have hν : ν ≠ 0 := LatticePlaquette.dir2_ne_zero ⟨s, μ, ν, hlt⟩
  by_cases hμ : μ = 0
  · subst hμ
    simp only [xp, plaquetteHolonomy, LatticePlaquette.boundaryLinks, mirrorPL, thetaL, mirrorL,
      ite_true, hν, ite_false, linkTwist_of_dir_eq, linkTwist_of_dir_ne, ne_eq, not_false_eq_true, flipK_one_siteShift_zero, flipK_siteShift _ _ hν, siteShift_flipK_two_zero]
    rw [conj_inv_identity', gaugeReTr_conj, hinv]
  · simp only [xp, plaquetteHolonomy, LatticePlaquette.boundaryLinks, mirrorPL, thetaL, mirrorL, hμ, hν,
      ite_false, linkTwist_of_dir_ne, ne_eq, not_false_eq_true, flipK_siteShift _ _ hμ, flipK_siteShift _ _ hν]

/-- The link reflection preserves the product Haar measure (the single-link measure is inversion invariant). -/
theorem measurePreserving_thetaL [MeasurableSpace G] [MeasurableInv G] [HasHaarProbability G]
    [(haarG G).IsInvInvariant] [Fintype (LatticeLink d N)] :
    MeasurePreserving (thetaL (G := G) (d := d) (N := N)) (productHaar G d N) (productHaar G d N) := by
  have h1 := measurePreserving_reindex (haarG G) (Function.Involutive.toPerm _ (mirrorL_involutive (d := d) (N := N)))
  have h2 := measurePreserving_pi (fun _ : LatticeLink d N => haarG G) (fun _ => haarG G)
    (f := fun l => linkTwist (G := G) l) (fun l => by
      unfold linkTwist
      split_ifs
      · exact Measure.measurePreserving_inv _
      · exact MeasurePreserving.id _)
  have h := h2.comp h1
  unfold productHaar
  convert h using 1
  funext U l
  simp only [Function.comp, Function.Involutive.coe_toPerm, thetaL]

end Theta

end Positivity
