/-
The time reflection of the periodic lattice (positivity project, 2026-11-21). Released under Apache 2.0.

# The site reflection `t ↦ −t` on (ℤ/Nℤ)^d

Direction `0` is time. On the periodic lattice with `N` even the reflection `t ↦ −t (mod N)` fixes the two time slices
`t = 0` and `t = N/2`. It acts on links and plaquettes:

- a spatial link at `(x, t)` goes to the spatial link at `(x, −t)`;
- the temporal link from `t` to `t + 1` goes to the temporal link from `−t − 1` to `−t`, traversed backwards: on
  connections, `(Θ U)(l) = U(mirror l)⁻¹` for temporal `l` and `U(mirror l)` for spatial `l` (`thetaConn`);
- a plaquette goes to its mirror image (`mirrorPlaq`).

We classify links into fixed (spatial, `t ∈ {0, N/2}`), positive (spatial with `0 < t < N/2`, temporal with `t < N/2`) and
negative (the rest), and plaquettes into fixed (spatial, `t ∈ {0, N/2}`), positive and negative, and prove:

- the mirror maps are involutions, swap positive and negative, and fix the fixed links (`link_pos_mirror`,
  `link_neg_mirror`, `link_fixed_mirror`, and the plaquette versions);
- every positive plaquette has its four links in the closed positive half, every fixed plaquette in the fixed planes
  (`plaq_pos_links`, `plaq_fixed_links`);
- `Re tr` of the plaquette holonomy of `Θ U` at `q` equals that of `U` at `mirror q` (`xp_thetaConn`), for any
  representation with `Re tr (g⁻¹) = Re tr g` (true for unitary representations, `gaugeReTr_inv_of_unitary`);
- `Θ` preserves the product Haar measure when the single-link measure is inversion invariant
  (`measurePreserving_thetaConn`), and `Θ ∘ Θ = id`;
- the links split as fixed ⊕ positive ⊕ mirror(positive) (`linkSplit`), and `Θ` is a reflection in the sense of
  `Positivity.Product` (`isReflection_thetaConn`).
-/

import AreaLaw.Concrete
import Positivity.Product

open MeasureTheory
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Positivity

variable {d N : ℕ}

/-! ## Time arithmetic in `ZMod N` -/

theorem zmod_val_eq_of_cast [NeZero N] {a : ZMod N} {m : ℕ} (hm : m < N) (h : (m : ZMod N) = a) : a.val = m := by
  rw [← h, ZMod.val_cast_of_lt hm]

theorem val_neg_sub_one [NeZero N] (a : ZMod N) : (-a - 1).val = N - 1 - a.val := by
  have ha := ZMod.val_lt a
  apply zmod_val_eq_of_cast (by omega)
  have h1 := congrArg (Nat.cast : ℕ → ZMod N) (show (N - 1 - a.val) + a.val + 1 = N by omega)
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, ZMod.natCast_zmod_val] at h1
  linear_combination h1

theorem val_neg_eq [NeZero N] (a : ZMod N) : (-a).val = if a.val = 0 then 0 else N - a.val := by
  have ha := ZMod.val_lt a
  split_ifs with h
  · rw [(ZMod.val_eq_zero a).mp h, neg_zero, ZMod.val_zero]
  · apply zmod_val_eq_of_cast (by omega)
    have h1 := congrArg (Nat.cast : ℕ → ZMod N) (show (N - a.val) + a.val = N by omega)
    rw [Nat.cast_add, ZMod.natCast_self, ZMod.natCast_zmod_val] at h1
    linear_combination h1

theorem val_add_one_of_lt [NeZero N] (a : ZMod N) (h : a.val + 1 < N) : (a + 1).val = a.val + 1 := by
  apply zmod_val_eq_of_cast h
  rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]

theorem neg_eq_self_of_val_half [NeZero N] (hN : Even N) (a : ZMod N) (h : a.val = N / 2) : -a = a := by
  obtain ⟨k, hk⟩ := hN
  have h2 : a + a = 0 := by
    rw [← ZMod.natCast_zmod_val a, h, ← Nat.cast_add, show N / 2 + N / 2 = N by omega, ZMod.natCast_self]
  linear_combination -h2

/-! ## Reflected sites -/

variable [NeZero d]

/-- The site reflected through the time slice `t = 0`: `t ↦ −t`. -/
def reflSite (x : FinLatticeSites d N) : FinLatticeSites d N := Function.update x 0 (-(x 0))

/-- The time coordinate `t ↦ −t − 1` (the start of the reversed mirror of a temporal link). -/
def tflipSite (x : FinLatticeSites d N) : FinLatticeSites d N := Function.update x 0 (-(x 0) - 1)

theorem reflSite_zero (x : FinLatticeSites d N) : reflSite x 0 = -(x 0) := by simp [reflSite]

theorem tflipSite_zero (x : FinLatticeSites d N) : tflipSite x 0 = -(x 0) - 1 := by simp [tflipSite]

theorem siteShift_zero_of_ne (x : FinLatticeSites d N) {μ : Fin d} (hμ : μ ≠ 0) : siteShift d N x μ 0 = x 0 := by
  simp [siteShift, Function.update_of_ne (Ne.symm hμ)]

theorem siteShift_zero_zero (x : FinLatticeSites d N) : siteShift d N x 0 0 = x 0 + 1 := by simp [siteShift]

theorem reflSite_siteShift (x : FinLatticeSites d N) {μ : Fin d} (hμ : μ ≠ 0) :
    reflSite (siteShift d N x μ) = siteShift d N (reflSite x) μ := by
  funext i
  simp only [reflSite, siteShift, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem tflipSite_siteShift (x : FinLatticeSites d N) {μ : Fin d} (hμ : μ ≠ 0) :
    tflipSite (siteShift d N x μ) = siteShift d N (tflipSite x) μ := by
  funext i
  simp only [tflipSite, siteShift, Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

theorem reflSite_siteShift_zero (x : FinLatticeSites d N) : reflSite (siteShift d N x 0) = tflipSite x := by
  funext i
  simp only [reflSite, tflipSite, siteShift, Function.update_apply]
  split_ifs <;> simp_all; ring

theorem siteShift_tflipSite_zero (x : FinLatticeSites d N) : siteShift d N (tflipSite x) 0 = reflSite x := by
  funext i
  simp only [reflSite, tflipSite, siteShift, Function.update_apply]
  split_ifs <;> simp_all

theorem reflSite_reflSite (x : FinLatticeSites d N) : reflSite (reflSite x) = x := by
  funext i
  simp only [reflSite, Function.update_apply]
  split_ifs <;> simp_all

theorem tflipSite_tflipSite (x : FinLatticeSites d N) : tflipSite (tflipSite x) = x := by
  funext i
  simp only [tflipSite, Function.update_apply]
  split_ifs <;> simp_all

theorem refl_time [NeZero N] (x : FinLatticeSites d N) :
    (reflSite x 0).val = if (x 0).val = 0 then 0 else N - (x 0).val := by
  rw [reflSite_zero, val_neg_eq]

theorem tflip_time [NeZero N] (x : FinLatticeSites d N) : (tflipSite x 0).val = N - 1 - (x 0).val := by
  rw [tflipSite_zero, val_neg_sub_one]

/-! ## Mirror links and plaquettes -/

/-- The mirror image of a link (as an unoriented edge; temporal links are reversed). -/
def mirrorLink (l : LatticeLink d N) : LatticeLink d N :=
  if l.dir = 0 then ⟨tflipSite l.site, l.dir⟩ else ⟨reflSite l.site, l.dir⟩

/-- The mirror image of a plaquette. -/
def mirrorPlaq (p : LatticePlaquette d N) : LatticePlaquette d N :=
  if p.dir1 = 0 then ⟨tflipSite p.site, p.dir1, p.dir2, p.h_lt⟩ else ⟨reflSite p.site, p.dir1, p.dir2, p.h_lt⟩

theorem mirrorLink_involutive : Function.Involutive (mirrorLink (d := d) (N := N)) := by
  rintro ⟨s, μ⟩
  by_cases h : μ = 0 <;> simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorLink, h, tflipSite_tflipSite, reflSite_reflSite]

theorem mirrorPlaq_involutive : Function.Involutive (mirrorPlaq (d := d) (N := N)) := by
  rintro ⟨s, μ, ν, h⟩
  by_cases hμ : μ = 0 <;> simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorPlaq, hμ, tflipSite_tflipSite, reflSite_reflSite]

theorem mirrorLink_dir (l : LatticeLink d N) : (mirrorLink l).dir = l.dir := by
  unfold mirrorLink; split_ifs <;> rfl

theorem _root_.LatticePlaquette.dir2_ne_zero (p : LatticePlaquette d N) : p.dir2 ≠ 0 := by
  intro h
  have := Fin.lt_def.mp p.h_lt
  rw [h] at this
  simp at this

/-! ## Positive, fixed and negative links and plaquettes -/

/-- Links in the fixed time slices: spatial links at `t = 0` or `t = N/2`. -/
def IsFixedLink (l : LatticeLink d N) : Prop := l.dir ≠ 0 ∧ ((l.site 0).val = 0 ∨ (l.site 0).val = N / 2)

/-- Links of the open positive half: spatial links with `0 < t < N/2`, temporal links from `t < N/2` to `t + 1`. -/
def IsPosLink (l : LatticeLink d N) : Prop :=
  (l.dir ≠ 0 ∧ 0 < (l.site 0).val ∧ (l.site 0).val < N / 2) ∨ (l.dir = 0 ∧ (l.site 0).val < N / 2)

/-- Plaquettes in the fixed time slices (spatial, `t ∈ {0, N/2}`). -/
def IsFixedPlaq (p : LatticePlaquette d N) : Prop :=
  p.dir1 ≠ 0 ∧ ((p.site 0).val = 0 ∨ (p.site 0).val = N / 2)

/-- Positive plaquettes: spatial with `0 < t < N/2`, or temporal with `t < N/2` (between the slices `t` and `t + 1`). -/
def IsPosPlaq (p : LatticePlaquette d N) : Prop :=
  (p.dir1 ≠ 0 ∧ 0 < (p.site 0).val ∧ (p.site 0).val < N / 2) ∨ (p.dir1 = 0 ∧ (p.site 0).val < N / 2)

variable [NeZero N]

theorem not_fixed_of_pos {l : LatticeLink d N} (h : IsPosLink l) : ¬IsFixedLink l := by
  unfold IsPosLink IsFixedLink at *; omega

theorem link_pos_mirror (hN : Even N) {l : LatticeLink d N} (h : IsPosLink l) :
    ¬IsFixedLink (mirrorLink l) ∧ ¬IsPosLink (mirrorLink l) := by
  obtain ⟨k, hk⟩ := hN
  rcases l with ⟨s, μ⟩
  have ht := ZMod.val_lt (s 0)
  have h0 : ((0 : Fin d) : ℕ) = 0 := Fin.val_zero d
  by_cases hμ : μ = 0
  · subst hμ
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorLink, IsPosLink, IsFixedLink, tflip_time] at h ⊢
    omega
  · have hμv : (μ : ℕ) ≠ 0 := fun h => hμ (Fin.ext (by rw [h, h0]))
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorLink, hμ, IsPosLink, IsFixedLink, refl_time] at h ⊢
    (try split_ifs) <;> omega

theorem link_neg_mirror (hN : Even N) {l : LatticeLink d N} (h1 : ¬IsFixedLink l) (h2 : ¬IsPosLink l) :
    IsPosLink (mirrorLink l) := by
  obtain ⟨k, hk⟩ := hN
  rcases l with ⟨s, μ⟩
  have ht := ZMod.val_lt (s 0)
  have h0 : ((0 : Fin d) : ℕ) = 0 := Fin.val_zero d
  by_cases hμ : μ = 0
  · subst hμ
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorLink, IsPosLink, IsFixedLink, tflip_time] at h1 h2 ⊢
    omega
  · have hμv : (μ : ℕ) ≠ 0 := fun h => hμ (Fin.ext (by rw [h, h0]))
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorLink, hμ, IsPosLink, IsFixedLink, refl_time] at h1 h2 ⊢
    (try split_ifs) <;> omega

theorem link_fixed_mirror (hN : Even N) {l : LatticeLink d N} (h : IsFixedLink l) : mirrorLink l = l := by
  rcases l with ⟨s, μ⟩
  obtain ⟨hμ, ht⟩ := h
  dsimp only at hμ ht
  have hneg : -(s 0) = s 0 := by
    rcases ht with ht | ht
    · rw [(ZMod.val_eq_zero _).mp ht, neg_zero]
    · exact neg_eq_self_of_val_half hN _ ht
  simp only [mirrorLink, hμ, ite_false, reflSite, hneg, Function.update_eq_self]

theorem not_fixedPlaq_of_pos {p : LatticePlaquette d N} (h : IsPosPlaq p) : ¬IsFixedPlaq p := by
  unfold IsPosPlaq IsFixedPlaq at *; omega

theorem plaq_pos_mirror (hN : Even N) {p : LatticePlaquette d N} (h : IsPosPlaq p) :
    ¬IsFixedPlaq (mirrorPlaq p) ∧ ¬IsPosPlaq (mirrorPlaq p) := by
  obtain ⟨k, hk⟩ := hN
  rcases p with ⟨s, μ, ν, hlt⟩
  have ht := ZMod.val_lt (s 0)
  have h0 : ((0 : Fin d) : ℕ) = 0 := Fin.val_zero d
  by_cases hμ : μ = 0
  · subst hμ
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorPlaq, IsPosPlaq, IsFixedPlaq, tflip_time] at h ⊢
    omega
  · have hμv : (μ : ℕ) ≠ 0 := fun h => hμ (Fin.ext (by rw [h, h0]))
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorPlaq, hμ, IsPosPlaq, IsFixedPlaq, refl_time] at h ⊢
    (try split_ifs) <;> omega

theorem plaq_neg_mirror (hN : Even N) {p : LatticePlaquette d N} (h1 : ¬IsFixedPlaq p) (h2 : ¬IsPosPlaq p) :
    IsPosPlaq (mirrorPlaq p) := by
  obtain ⟨k, hk⟩ := hN
  rcases p with ⟨s, μ, ν, hlt⟩
  have ht := ZMod.val_lt (s 0)
  have h0 : ((0 : Fin d) : ℕ) = 0 := Fin.val_zero d
  by_cases hμ : μ = 0
  · subst hμ
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorPlaq, IsPosPlaq, IsFixedPlaq, tflip_time] at h1 h2 ⊢
    omega
  · have hμv : (μ : ℕ) ≠ 0 := fun h => hμ (Fin.ext (by rw [h, h0]))
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, mirrorPlaq, hμ, IsPosPlaq, IsFixedPlaq, refl_time] at h1 h2 ⊢
    (try split_ifs) <;> omega

/-- **Every positive plaquette lies in the closed positive half.** -/
theorem plaq_pos_links (hN : Even N) {p : LatticePlaquette d N} (h : IsPosPlaq p) (i : Fin 4) :
    IsPosLink (p.boundaryLinks i) ∨ IsFixedLink (p.boundaryLinks i) := by
  obtain ⟨k, hk⟩ := hN
  rcases p with ⟨s, μ, ν, hlt⟩
  have hν : ν ≠ 0 := LatticePlaquette.dir2_ne_zero ⟨s, μ, ν, hlt⟩
  have ht := ZMod.val_lt (s 0)
  have h0 : ((0 : Fin d) : ℕ) = 0 := Fin.val_zero d
  by_cases hμ : μ = 0
  · subst hμ
    simp only [IsPosPlaq, ne_eq, not_true_eq_false, false_and, true_and, false_or] at h
    have h1 : (s 0 + 1).val = (s 0).val + 1 := val_add_one_of_lt _ (by omega)
    fin_cases i <;>
      simp [-ZMod.val_eq_zero, -ZMod.val_pos, LatticePlaquette.boundaryLinks, IsPosLink, IsFixedLink, siteShift_zero_of_ne _ hν,
        siteShift_zero_zero, h1, hν] <;> omega
  · simp only [IsPosPlaq, hμ, ne_eq, not_false_eq_true, true_and, false_and, or_false] at h
    fin_cases i <;>
      simp [-ZMod.val_eq_zero, -ZMod.val_pos, LatticePlaquette.boundaryLinks, IsPosLink, IsFixedLink, siteShift_zero_of_ne _ hν,
        siteShift_zero_of_ne _ hμ, hν, hμ] <;> omega

/-- **Every fixed plaquette lies in the fixed time slices.** -/
theorem plaq_fixed_links {p : LatticePlaquette d N} (h : IsFixedPlaq p) (i : Fin 4) :
    IsFixedLink (p.boundaryLinks i) := by
  rcases p with ⟨s, μ, ν, hlt⟩
  have hν : ν ≠ 0 := LatticePlaquette.dir2_ne_zero ⟨s, μ, ν, hlt⟩
  obtain ⟨hμ, ht⟩ := h
  fin_cases i <;>
    simp [-ZMod.val_eq_zero, -ZMod.val_pos, LatticePlaquette.boundaryLinks, IsFixedLink, siteShift_zero_of_ne _ hν, siteShift_zero_of_ne _ hμ,
      hν, hμ] <;> simpa using ht

/-! ## The reflection of connections -/

section Theta

variable {G : Type*} [Group G]

/-- The reflection of a connection: `(Θ U)(l) = U(mirror l)⁻¹` for temporal links (the mirror is traversed backwards),
    `U(mirror l)` for spatial links. -/
def thetaConn (U : GaugeConnection G d N) : GaugeConnection G d N :=
  fun l => if l.dir = 0 then (U (mirrorLink l))⁻¹ else U (mirrorLink l)

/-- The twist applied on link `l`: inversion for temporal links, identity for spatial ones. -/
def linkTwist (l : LatticeLink d N) : G → G := if l.dir = 0 then (·⁻¹) else id

theorem thetaConn_eq (U : GaugeConnection G d N) (l : LatticeLink d N) :
    thetaConn U l = linkTwist l (U (mirrorLink l)) := by
  unfold thetaConn linkTwist; split_ifs <;> rfl

/-- `Θ` is an involution. -/
theorem thetaConn_involutive : Function.Involutive (thetaConn (G := G) (d := d) (N := N)) := by
  intro U; funext l
  simp only [thetaConn, mirrorLink_dir, mirrorLink_involutive l]
  split_ifs <;> simp

private theorem conj_inv_identity (a b c e : G) : a⁻¹ * b * c⁻¹⁻¹ * e⁻¹ = a⁻¹ * (a * e * c⁻¹ * b⁻¹)⁻¹ * a⁻¹⁻¹ := by
  group

variable {n : ℕ} [HasGaugeTrace G n]

/-- **Plaquettes of the reflected connection.** `Re tr U_q(Θ U) = Re tr U_{mirror q}(U)`: for spatial plaquettes the
    holonomies agree; for temporal ones the holonomy of `Θ U` is conjugate to the inverse of the mirrored holonomy. -/
theorem xp_thetaConn (hinv : ∀ g : G, gaugeReTr G n g⁻¹ = gaugeReTr G n g) (U : GaugeConnection G d N)
    (q : LatticePlaquette d N) : xp n q (thetaConn U) = xp n (mirrorPlaq q) U := by
  rcases q with ⟨s, μ, ν, hlt⟩
  have hν : ν ≠ 0 := LatticePlaquette.dir2_ne_zero ⟨s, μ, ν, hlt⟩
  by_cases hμ : μ = 0
  · subst hμ
    simp only [xp, plaquetteHolonomy, LatticePlaquette.boundaryLinks, mirrorPlaq, thetaConn, mirrorLink, ite_true,
      hν, ite_false, reflSite_siteShift_zero, tflipSite_siteShift _ hν, siteShift_tflipSite_zero, siteShift_zero_of_ne,
      siteShift_zero_zero]
    rw [conj_inv_identity, gaugeReTr_conj, hinv]
  · simp only [xp, plaquetteHolonomy, LatticePlaquette.boundaryLinks, mirrorPlaq, thetaConn, mirrorLink, hμ, hν,
      ite_false, reflSite_siteShift _ hμ, reflSite_siteShift _ hν]

/-- For a unitary representation, `Re tr (g⁻¹) = Re tr g`. -/
theorem gaugeReTr_inv_of_unitary (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : G) : gaugeReTr G n g⁻¹ = gaugeReTr G n g := by
  have h1 : HasGaugeTrace.rep (G := G) (n := n) g⁻¹ = star (HasGaugeTrace.rep (G := G) (n := n) g) := by
    have hu := (Matrix.mem_unitaryGroup_iff).mp (hU g)
    calc HasGaugeTrace.rep (G := G) (n := n) g⁻¹
        = HasGaugeTrace.rep (G := G) (n := n) g⁻¹ * (HasGaugeTrace.rep (G := G) (n := n) g *
            star (HasGaugeTrace.rep (G := G) (n := n) g)) := by rw [hu, mul_one]
      _ = star (HasGaugeTrace.rep (G := G) (n := n) g) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  simp only [gaugeReTr, gaugeTrace, h1, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
  exact Complex.conj_re _

/-- The reflection preserves the product Haar measure (the single-link measure is inversion invariant). -/
theorem measurePreserving_thetaConn [MeasurableSpace G] [MeasurableInv G] [HasHaarProbability G]
    [(haarG G).IsInvInvariant] [Fintype (LatticeLink d N)] :
    MeasurePreserving (thetaConn (G := G) (d := d) (N := N)) (productHaar G d N) (productHaar G d N) := by
  have h1 := measurePreserving_reindex (haarG G) (Function.Involutive.toPerm _ (mirrorLink_involutive (d := d) (N := N)))
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
  simp only [Function.comp, Function.Involutive.coe_toPerm, thetaConn_eq]

end Theta

/-! ## The splitting of links -/

/-- Fixed links. -/
abbrev FixLink (d N : ℕ) [NeZero d] := {l : LatticeLink d N // IsFixedLink l}

/-- Positive links. -/
abbrev PosLink (d N : ℕ) [NeZero d] := {l : LatticeLink d N // IsPosLink l}

/-- Fixed links, positive links, and the mirrors of positive links. -/
def linkSplitFun : FixLink d N ⊕ (PosLink d N ⊕ PosLink d N) → LatticeLink d N :=
  Sum.elim Subtype.val (Sum.elim Subtype.val (fun x => mirrorLink x.1))

theorem linkSplitFun_bijective (hN : Even N) : Function.Bijective (linkSplitFun (d := d) (N := N)) := by
  constructor
  · rintro (c | x | x) (c' | y | y) h <;> simp only [linkSplitFun, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg _ (Subtype.ext h)
    · exact absurd c.2 (h ▸ not_fixed_of_pos y.2)
    · exact absurd c.2 (h ▸ (link_pos_mirror hN y.2).1)
    · exact absurd c'.2 (h ▸ not_fixed_of_pos x.2)
    · exact congrArg _ (congrArg _ (Subtype.ext h))
    · exact absurd x.2 (h ▸ (link_pos_mirror hN y.2).2)
    · exact absurd c'.2 (h.symm ▸ (link_pos_mirror hN x.2).1)
    · exact absurd y.2 (h.symm ▸ (link_pos_mirror hN x.2).2)
    · exact congrArg _ (congrArg _ (Subtype.ext (mirrorLink_involutive.injective h)))
  · intro l
    by_cases h1 : IsFixedLink l
    · exact ⟨.inl ⟨l, h1⟩, rfl⟩
    by_cases h2 : IsPosLink l
    · exact ⟨.inr (.inl ⟨l, h2⟩), rfl⟩
    exact ⟨.inr (.inr ⟨mirrorLink l, link_neg_mirror hN h1 h2⟩), mirrorLink_involutive l⟩

/-- The links split as fixed ⊕ positive ⊕ mirror(positive). -/
def linkSplit (hN : Even N) : FixLink d N ⊕ (PosLink d N ⊕ PosLink d N) ≃ LatticeLink d N :=
  Equiv.ofBijective _ (linkSplitFun_bijective hN)

/-- The links of the closed positive half `0 ≤ t ≤ N/2`: positive links and fixed links. -/
def posHalfLinks (d N : ℕ) [NeZero d] [Fintype (LatticeLink d N)] : Finset (LatticeLink d N) :=
  Finset.univ.filter (fun l => IsPosLink l ∨ IsFixedLink l)

theorem depPos_of_linkDep {G : Type*} [Group G] [Fintype (LatticeLink d N)] (hN : Even N) {α : Type*}
    {F : GaugeConnection G d N → α} (hF : LinkDep F (posHalfLinks d N)) : DepPos (linkSplit hN) F := by
  intro U V h0 h1
  apply hF
  intro l hl
  simp only [posHalfLinks, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  rcases hl with hp | hf
  · exact h1 ⟨l, hp⟩
  · exact h0 ⟨l, hf⟩

theorem isReflection_thetaConn {G : Type*} [Group G] (hN : Even N) :
    IsReflection (linkSplit (d := d) hN) (fun x => linkTwist (G := G) x.1) thetaConn where
  fix U c := by
    show thetaConn U c.1 = U c.1
    rw [thetaConn_eq, link_fixed_mirror hN c.2]
    simp [linkTwist, c.2.1]
  pos U x := thetaConn_eq U x.1

end Positivity
