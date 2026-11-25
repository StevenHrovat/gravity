/-
Reflection positivity of the Wilson lattice gauge measure, link reflection (positivity project, 2026-11-21). Released
under Apache 2.0.

Osterwalder and Seiler proved reflection positivity of the Wilson action for reflections through planes of sites and
through planes between sites in 1978 (Ann. Phys. 110, 440). This file is an independent formalisation of the second case
on the periodic lattice, done on the actual Wilson measure (no gauge fixing).

# The Wilson measure is reflection positive for the link reflection `t ↦ −1 − t` (`β ≥ 0`)

Notation of `Positivity.LinkReflection`. The proof:

1. **Splitting the crossing links.** Adjoin an independent Haar variable `w_l` for every crossing link `l`. The map
   `recombine` sends `(U, w)` to the connection that agrees with `U` off the crossing links and equals `U_l w_l⁻¹`
   (plane `M − 1 | M`) or `w_l U_l⁻¹` (plane `N − 1 | 0`) on them. It carries the product Haar measure on the extended
   space to the product Haar measure (`measurePreserving_recombine`: for fixed `w` each coordinate map preserves Haar
   measure, which uses left and right invariance and inversion invariance). In the extended space `U_l` is a positive and
   `w_l` a negative variable; the extended reflection `thetaExt` swaps them, and `recombine ∘ thetaExt = Θ ∘ recombine`.
2. **Weight.** The positive and negative plaquettes give `A · (A ∘ θ)` as for the site reflection. A crossing plaquette
   gives `Re tr U_p = Re tr (P · (θ P)⁻¹)` with `P = s₀⁻¹ a s₂` built from positive variables only (`xp_cross`), and
   `Re tr (P Q⁻¹) = ∑ᵢⱼ (Re Pᵢⱼ Re Qᵢⱼ + Im Pᵢⱼ Im Qᵢⱼ)` for a unitary representation. So the crossing weight is
   `exp (β ∑ⱼ gⱼ · (gⱼ ∘ θ))` with bounded measurable positive features `gⱼ`.
3. **Kernel positivity** (`Positivity.Kernel.config_rp_kernel`) gives, for `β ≥ 0` and every bounded measurable `F` of the
   links of the open positive half (both ends in `0 ≤ t ≤ N/2 − 1`), `∫ F · (F ∘ Θ) · e^{−S} d(productHaar) ≥ 0`
   (`wilson_rp_link`; SU(2) and U(n): `wilson_rp_link_SU2`, `wilson_rp_link_Un`).
-/

import Positivity.LinkReflection
import Positivity.Kernel
import Positivity.Concrete

open MeasureTheory Finset
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Positivity

open AreaLaw.Concrete

variable {d N : ℕ} [NeZero d] [NeZero N]

/-- Crossing links. -/
abbrev CrossLink (d N : ℕ) [NeZero d] := {l : LatticeLink d N // IsCrossL l}

/-- Positive links of the link reflection. -/
abbrev PosLinkL (d N : ℕ) [NeZero d] := {l : LatticeLink d N // IsPosL l}

/-- The extended index set: all links, and a second copy of each crossing link. -/
abbrev ExtIdx (d N : ℕ) [NeZero d] := LatticeLink d N ⊕ CrossLink d N

/-- Crossing links of the plane `M − 1 | M` (they start at `t = N/2 − 1`). -/
def IsCrossAL (l : LatticeLink d N) : Prop := (l.site 0).val + 1 = N / 2

/-- The links of the open positive half of the link reflection. -/
def posLinksL (d N : ℕ) [NeZero d] [NeZero N] : Finset (LatticeLink d N) := univ.filter IsPosL

section Group

variable {G : Type*} [Group G]

/-- Recombine an extended configuration into a connection. -/
def recombinePair (w : CrossLink d N → G) (U : GaugeConnection G d N) : GaugeConnection G d N := fun l =>
  if h : IsCrossL l then (if IsCrossAL l then U l * (w ⟨l, h⟩)⁻¹ else w ⟨l, h⟩ * (U l)⁻¹) else U l

/-- Recombine an extended configuration into a connection. -/
def recombine (ω : ExtIdx d N → G) : GaugeConnection G d N :=
  recombinePair (fun c => ω (.inr c)) (fun l => ω (.inl l))

/-- The extended reflection. -/
def thetaExt (ω : ExtIdx d N → G) : ExtIdx d N → G
  | .inl l => if h : IsCrossL l then ω (.inr ⟨l, h⟩) else linkTwist l (ω (.inl (mirrorL l)))
  | .inr c => ω (.inl c.1)

theorem recombine_of_not_cross (ω : ExtIdx d N → G) {l : LatticeLink d N} (h : ¬IsCrossL l) :
    recombine ω l = ω (.inl l) := by
  simp [recombine, recombinePair, h]

theorem recombine_thetaExt (hN : Even N) (ω : ExtIdx d N → G) : recombine (thetaExt ω) = thetaL (recombine ω) := by
  funext l
  by_cases h : IsCrossL l
  · have hm := crossL_mirror hN h
    simp only [recombine, recombinePair, thetaL, hm, h, dite_true, thetaExt, linkTwist_of_dir_eq h.1]
    split_ifs <;> group
  · have hm : ¬IsCrossL (mirrorL l) := fun hc => h ((crossL_mirror_iff hN l).mp hc)
    simp only [recombine, recombinePair, thetaL, h, hm, dite_false, thetaExt]

/-! ### The splitting of the extended index set -/

/-- Positive coordinates (positive links and the positive copies of crossing links) and their mirrors. -/
def extSplitFun : Empty ⊕ ((PosLinkL d N ⊕ CrossLink d N) ⊕ (PosLinkL d N ⊕ CrossLink d N)) → ExtIdx d N
  | .inl e => e.elim
  | .inr (.inl (.inl x)) => .inl x.1
  | .inr (.inl (.inr c)) => .inl c.1
  | .inr (.inr (.inl x)) => .inl (mirrorL x.1)
  | .inr (.inr (.inr c)) => .inr c

theorem extSplitFun_bijective (hN : Even N) : Function.Bijective (extSplitFun (d := d) (N := N)) := by
  constructor
  · rintro (e | (x | c) | (x | c)) (e' | (y | c') | (y | c')) h <;>
      first
      | exact e.elim
      | exact e'.elim
      | simp only [extSplitFun, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
    · exact congrArg _ (congrArg _ (congrArg _ (Subtype.ext h)))
    · exact absurd c'.2 (h ▸ not_cross_of_posL x.2)
    · exact absurd x.2 (h ▸ (posL_mirror hN y.2).1)
    · exact absurd c.2 (h ▸ not_cross_of_posL y.2)
    · exact congrArg _ (congrArg _ (congrArg _ (Subtype.ext h)))
    · exact absurd c.2 (h ▸ (posL_mirror hN y.2).2)
    · exact absurd y.2 (h.symm ▸ (posL_mirror hN x.2).1)
    · exact absurd c'.2 (h.symm ▸ (posL_mirror hN x.2).2)
    · exact congrArg _ (congrArg _ (congrArg _ (Subtype.ext (mirrorL_involutive.injective h))))
    · exact congrArg _ (congrArg _ (congrArg _ h))
  · rintro (l | c)
    · by_cases hp : IsPosL l
      · exact ⟨.inr (.inl (.inl ⟨l, hp⟩)), rfl⟩
      by_cases hc : IsCrossL l
      · exact ⟨.inr (.inl (.inr ⟨l, hc⟩)), rfl⟩
      exact ⟨.inr (.inr (.inl ⟨mirrorL l, negL_mirror hN hp hc⟩)),
        congrArg Sum.inl (mirrorL_involutive l)⟩
    · exact ⟨.inr (.inr (.inr c)), rfl⟩

/-- The splitting of the extended index set (no fixed coordinates). -/
def extSplit (hN : Even N) : Empty ⊕ ((PosLinkL d N ⊕ CrossLink d N) ⊕ (PosLinkL d N ⊕ CrossLink d N)) ≃ ExtIdx d N :=
  Equiv.ofBijective _ (extSplitFun_bijective hN)

/-- The twists: inversion on temporal positive links, identity on spatial ones and on crossing copies. -/
def extTwist : PosLinkL d N ⊕ CrossLink d N → G → G
  | .inl x => linkTwist x.1
  | .inr _ => id

theorem isReflection_thetaExt (hN : Even N) :
    IsReflection (extSplit (d := d) (N := N) hN) (extTwist (G := G)) thetaExt where
  fix _ c := c.elim
  pos U x := by
    rcases x with x | c
    · show thetaExt U (.inl x.1) = linkTwist x.1 (U (.inl (mirrorL x.1)))
      simp [thetaExt, not_cross_of_posL x.2]
    · show thetaExt U (.inl c.1) = U (.inr c)
      simp [thetaExt, c.2]

theorem depPos_comp_recombine (hN : Even N) {α : Type*} {F : GaugeConnection G d N → α}
    (hF : LinkDep F (posLinksL d N)) : DepPos (extSplit hN) (fun ω => F (recombine ω)) := by
  intro U V _ h1
  apply hF
  intro l hl
  simp only [posLinksL, mem_filter, mem_univ, true_and] at hl
  rw [recombine_of_not_cross U (not_cross_of_posL hl), recombine_of_not_cross V (not_cross_of_posL hl)]
  exact h1 (.inl ⟨l, hl⟩)

/-! ### Crossing plaquettes -/

/-- The positive spatial link of a crossing plaquette. -/
def posSp (p : LatticePlaquette d N) : LatticeLink d N :=
  if IsCrossA p then p.boundaryLinks 3 else p.boundaryLinks 1

/-- The group element `P = s₀⁻¹ a s₂` of a crossing plaquette, built from positive variables. -/
def Pmat (p : LatticePlaquette d N) (ω : ExtIdx d N → G) : G :=
  (ω (.inl (p.boundaryLinks 0)))⁻¹ * ω (.inl (posSp p)) * ω (.inl (p.boundaryLinks 2))

private theorem cross_identity_A (s₀ t₀ b s₂ t₂ a : G) :
    s₀ * t₀⁻¹ * b * (s₂ * t₂⁻¹)⁻¹ * a⁻¹ = s₀ * (s₀⁻¹ * a * s₂ * (t₀⁻¹ * b * t₂)⁻¹)⁻¹ * s₀⁻¹ := by
  group

private theorem cross_identity_B (s₀ t₀ a s₂ t₂ b : G) :
    t₀ * s₀⁻¹ * a * (t₂ * s₂⁻¹)⁻¹ * b⁻¹ = t₀ * (s₀⁻¹ * a * s₂ * (t₀⁻¹ * b * t₂)⁻¹) * t₀⁻¹ := by
  group

variable {n : ℕ} [HasGaugeTrace G n]

/-- **The crossing plaquettes.** `Re tr U_p(recombine ω) = Re tr (P(ω) · P(θ ω)⁻¹)`. -/
theorem xp_cross (hN : Even N) (hinv : ∀ g : G, gaugeReTr G n g⁻¹ = gaugeReTr G n g) {p : LatticePlaquette d N}
    (h : IsCrossPL p) (ω : ExtIdx d N → G) :
    xp n p (recombine ω) = gaugeReTr G n (Pmat p ω * (Pmat p (thetaExt ω))⁻¹) := by
  have c0 := crossPL_bl0 h
  have c2 := crossPL_bl2 h
  have hν : p.dir2 ≠ 0 := LatticePlaquette.dir2_ne_zero p
  have n1 : ¬IsCrossL (p.boundaryLinks 1) := spatial_not_cross hν
  have n3 : ¬IsCrossL (p.boundaryLinks 3) := spatial_not_cross hν
  have hA0 : IsCrossAL (p.boundaryLinks 0) ↔ IsCrossA p := Iff.rfl
  have hA2 : IsCrossAL (p.boundaryLinks 2) ↔ IsCrossA p := by
    unfold IsCrossAL IsCrossA; rw [crossPL_bl2_time]
  by_cases hA : IsCrossA p
  · obtain ⟨hp3, hm3⟩ := crossA_links hN h hA
    have hs : posSp p = p.boundaryLinks 3 := ite_eq_left hA
    have ht3 : thetaExt ω (.inl (p.boundaryLinks 3)) = ω (.inl (p.boundaryLinks 1)) := by
      simp only [thetaExt, n3, dite_false, hm3]
      exact linkTwist_of_dir_ne (show (p.boundaryLinks 3).dir ≠ 0 from hν) _
    simp only [xp, plaquetteHolonomy, Pmat, hs, ht3]
    simp only [recombine, recombinePair, c0, c2, n1, n3, dite_true, dite_false, hA0.mpr hA, hA2.mpr hA, ite_true,
      thetaExt]
    rw [cross_identity_A, gaugeReTr_conj, hinv]
  · obtain ⟨hp1, hm1⟩ := crossB_links hN h hA
    have hs : posSp p = p.boundaryLinks 1 := ite_eq_right hA
    have ht1 : thetaExt ω (.inl (p.boundaryLinks 1)) = ω (.inl (p.boundaryLinks 3)) := by
      simp only [thetaExt, n1, dite_false, hm1]
      exact linkTwist_of_dir_ne (show (p.boundaryLinks 1).dir ≠ 0 from hν) _
    have nA0 : ¬IsCrossAL (p.boundaryLinks 0) := fun h' => hA (hA0.mp h')
    have nA2 : ¬IsCrossAL (p.boundaryLinks 2) := fun h' => hA (hA2.mp h')
    simp only [xp, plaquetteHolonomy, Pmat, hs, ht1]
    simp only [recombine, recombinePair, c0, c2, n1, n3, dite_true, dite_false, nA0, nA2, ite_false, thetaExt]
    rw [cross_identity_B, gaugeReTr_conj]

/-- For a unitary representation, `rep (g⁻¹) = (rep g)ᴴ`. -/
theorem rep_inv_of_unitary (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : G) : HasGaugeTrace.rep (G := G) (n := n) g⁻¹ = star (HasGaugeTrace.rep (G := G) (n := n) g) := by
  have hu := (Matrix.mem_unitaryGroup_iff).mp (hU g)
  calc HasGaugeTrace.rep (G := G) (n := n) g⁻¹
      = HasGaugeTrace.rep (G := G) (n := n) g⁻¹ * (HasGaugeTrace.rep (G := G) (n := n) g *
          star (HasGaugeTrace.rep (G := G) (n := n) g)) := by rw [hu, mul_one]
    _ = star (HasGaugeTrace.rep (G := G) (n := n) g) := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

/-- `Re tr (A B⁻¹) = ∑ᵢⱼ (Re Aᵢⱼ Re Bᵢⱼ + Im Aᵢⱼ Im Bᵢⱼ)` (the real Frobenius inner product) for a unitary
    representation. -/
theorem reTr_mul_inv (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (A B : G) : gaugeReTr G n (A * B⁻¹) = ∑ i : Fin n, ∑ j : Fin n,
      ((HasGaugeTrace.rep (G := G) (n := n) A i j).re * (HasGaugeTrace.rep (G := G) (n := n) B i j).re +
        (HasGaugeTrace.rep (G := G) (n := n) A i j).im * (HasGaugeTrace.rep (G := G) (n := n) B i j).im) := by
  simp only [gaugeReTr, gaugeTrace, map_mul, rep_inv_of_unitary hU, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Complex.re_sum, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The features of the crossing plaquettes: real and imaginary parts of the matrix entries of `rep P`. -/
def crossFeat (n : ℕ) [HasGaugeTrace G n] (j : LatticePlaquette d N × Fin n × Fin n × Bool) (ω : ExtIdx d N → G) :
    ℝ :=
  if IsCrossPL j.1 then
    (if j.2.2.2 then (HasGaugeTrace.rep (G := G) (n := n) (Pmat j.1 ω) j.2.1 j.2.2.1).re
      else (HasGaugeTrace.rep (G := G) (n := n) (Pmat j.1 ω) j.2.1 j.2.2.1).im)
  else 0

theorem sum_cross_xp (hN : Even N) (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (ω : ExtIdx d N → G) :
    ∑ p ∈ (univ : Finset (LatticePlaquette d N)).filter IsCrossPL, xp n p (recombine ω) =
      ∑ j, crossFeat n j ω * crossFeat n j (thetaExt ω) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.sum_prod_type]
  by_cases hp : IsCrossPL p
  · rw [ite_eq_left hp, xp_cross hN (gaugeReTr_inv_of_unitary hU) hp, reTr_mul_inv hU]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fintype.sum_bool, crossFeat, ite_eq_left hp, ite_true, Bool.false_eq_true, ite_false]
  · simp [hp, crossFeat]

theorem crossFeat_depPos (hN : Even N) (j : LatticePlaquette d N × Fin n × Fin n × Bool) :
    DepPos (extSplit (d := d) (N := N) hN) (crossFeat (G := G) n j) := by
  intro U V _ h1
  unfold crossFeat
  by_cases hp : IsCrossPL j.1
  · have hP : Pmat j.1 U = Pmat j.1 V := by
      have e0 := h1 (.inr ⟨_, crossPL_bl0 hp⟩)
      have e2 := h1 (.inr ⟨_, crossPL_bl2 hp⟩)
      have es : U (.inl (posSp j.1)) = V (.inl (posSp j.1)) := by
        unfold posSp
        split_ifs with hA
        · exact h1 (.inl ⟨_, (crossA_links hN hp hA).1⟩)
        · exact h1 (.inl ⟨_, (crossB_links hN hp hA).1⟩)
      simp only [Pmat]
      rw [es]
      exact congrArg₂ (fun a b => a⁻¹ * V (.inl (posSp j.1)) * b) e0 e2
    simp only [hp, ite_true, hP]
  · simp only [hp, ite_false]

end Group

/-! ### Measure theory -/

section Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n] [HasHaarProbability G]

theorem measurable_recombinePair :
    Measurable (Function.uncurry (recombinePair (G := G) (d := d) (N := N))) := by
  refine measurable_pi_iff.mpr fun l => ?_
  show Measurable fun p : (CrossLink d N → G) × GaugeConnection G d N => recombinePair p.1 p.2 l
  by_cases h : IsCrossL l
  · by_cases hA : IsCrossAL l
    · simp only [recombinePair, h, hA, dite_true, ite_true]
      exact ((measurable_pi_apply l).comp measurable_snd).mul ((measurable_pi_apply _).comp measurable_fst).inv
    · simp only [recombinePair, h, hA, dite_true, ite_false]
      exact ((measurable_pi_apply _).comp measurable_fst).mul ((measurable_pi_apply l).comp measurable_snd).inv
  · simp only [recombinePair, h, dite_false]
    exact (measurable_pi_apply l).comp measurable_snd

variable [(haarG G).IsMulLeftInvariant] [(haarG G).IsMulRightInvariant] [(haarG G).IsInvInvariant]

/-- **Splitting the crossing links preserves the product Haar measure.** -/
theorem measurePreserving_recombine :
    MeasurePreserving (recombine (G := G) (d := d) (N := N)) (Measure.pi fun _ : ExtIdx d N => haarG G)
      (productHaar G d N) := by
  have hτ : ∀ (w : CrossLink d N → G) (l : LatticeLink d N), MeasurePreserving
      (fun g : G => if h : IsCrossL l then (if IsCrossAL l then g * (w ⟨l, h⟩)⁻¹ else w ⟨l, h⟩ * g⁻¹) else g)
      (haarG G) (haarG G) := by
    intro w l
    by_cases h : IsCrossL l
    · by_cases hA : IsCrossAL l
      · simp only [h, hA, dite_true, ite_true]
        exact measurePreserving_mul_right _ _
      · simp only [h, hA, dite_true, ite_false]
        exact (measurePreserving_mul_left _ _).comp (Measure.measurePreserving_inv _)
    · simp only [h, dite_false]
      exact MeasurePreserving.id _
  have hΨ : ∀ w : CrossLink d N → G, MeasurePreserving (recombinePair w) (productHaar G d N) (productHaar G d N) :=
    fun w => measurePreserving_pi (fun _ => haarG G) (fun _ => haarG G) (hτ w)
  have hskew := MeasurePreserving.skew_product (μa := Measure.pi fun _ : CrossLink d N => haarG G)
    (μc := productHaar G d N) (μd := productHaar G d N) (MeasurePreserving.id _) measurable_recombinePair
    (ae_of_all _ fun w => (hΨ w).map_eq)
  have hsnd := measurePreserving_snd (μ := Measure.pi fun _ : CrossLink d N => haarG G) (ν := productHaar G d N)
  have hsum := measurePreserving_sumPiEquivProdPi (X := fun _ : ExtIdx d N => G) (fun _ => haarG G)
  have hswap := Measure.measurePreserving_swap (μ := productHaar G d N)
    (ν := Measure.pi fun _ : CrossLink d N => haarG G)
  have h := hsnd.comp (hskew.comp (hswap.comp hsum))
  convert h using 1
  funext ω; rfl

theorem measurable_thetaL : Measurable (thetaL (G := G) (d := d) (N := N)) := by
  refine measurable_pi_iff.mpr fun l => ?_
  simp only [thetaL, linkTwist]
  split_ifs
  · exact (measurable_pi_apply _).inv
  · exact measurable_pi_apply _

theorem measurable_Pmat (p : LatticePlaquette d N) : Measurable (Pmat (G := G) p) := by
  show Measurable fun ω : ExtIdx d N → G =>
    (ω (.inl (p.boundaryLinks 0)))⁻¹ * ω (.inl (posSp p)) * ω (.inl (p.boundaryLinks 2))
  exact (((measurable_pi_apply (Sum.inl (p.boundaryLinks 0))).inv).mul
    (measurable_pi_apply (Sum.inl (posSp p)))).mul (measurable_pi_apply (Sum.inl (p.boundaryLinks 2)))

theorem measurable_crossFeat (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (j : LatticePlaquette d N × Fin n × Fin n × Bool) : Measurable (crossFeat (G := G) (d := d) (N := N) n j) := by
  have he : Continuous fun g : G => HasGaugeTrace.rep (G := G) (n := n) g j.2.1 j.2.2.1 :=
    (continuous_apply _).comp ((continuous_apply _).comp hc)
  unfold crossFeat
  split_ifs
  · exact (Complex.continuous_re.comp he).measurable.comp (measurable_Pmat _)
  · exact (Complex.continuous_im.comp he).measurable.comp (measurable_Pmat _)
  · exact measurable_const

theorem isBdd_crossFeat (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (j : LatticePlaquette d N × Fin n × Fin n × Bool) : IsBdd (crossFeat (G := G) (d := d) (N := N) n j) := by
  refine ⟨1, fun ω => ?_⟩
  have hb := entry_norm_bound_of_unitary (hU (Pmat j.1 ω)) j.2.1 j.2.2.1
  unfold crossFeat
  split_ifs
  · exact (Complex.abs_re_le_norm _).trans hb
  · exact (Complex.abs_im_le_norm _).trans hb
  · simp

/-- The weight of the positive plaquettes of the link reflection. -/
def posWeightL (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (U : GaugeConnection G d N) : ℝ :=
  ∏ p ∈ (univ : Finset (LatticePlaquette d N)).filter IsPosPL, Real.exp (β * xp n p U)

theorem posWeightL_linkDep (hN : Even N) (β : ℝ) :
    LinkDep (posWeightL (G := G) (d := d) (N := N) n β) (posLinksL d N) := by
  intro U V h
  unfold posWeightL
  refine prod_congr rfl fun p hp => ?_
  simp only [mem_filter, mem_univ, true_and] at hp
  have hl : ∀ i, U (p.boundaryLinks i) = V (p.boundaryLinks i) := fun i =>
    h _ (by simp only [posLinksL, mem_filter, mem_univ, true_and]; exact posPL_links hN hp i)
  simp only [xp, plaquetteHolonomy, hl]

variable (hN : Even N) (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
include hN hc hU

/-- **The Wilson weight on the extended space.** -/
theorem wilson_weight_factor_ext (β : ℝ) (ω : ExtIdx d N → G) :
    ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p (recombine ω)) =
      posWeightL n β (recombine ω) * posWeightL n β (recombine (thetaExt ω)) *
        Real.exp (β * ∑ j, crossFeat n j ω * crossFeat n j (thetaExt ω)) := by
  have hinv := gaugeReTr_inv_of_unitary hU
  rw [← prod_filter_mul_prod_filter_not univ IsPosPL,
    ← prod_filter_mul_prod_filter_not ((univ : Finset (LatticePlaquette d N)).filter (fun p => ¬IsPosPL p))
      IsCrossPL]
  have hcr : ((univ : Finset (LatticePlaquette d N)).filter (fun p => ¬IsPosPL p)).filter IsCrossPL =
      univ.filter IsCrossPL := by
    ext p
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    intro hc hp
    exact not_crossPL_of_posPL hp hc
  have hneg : ∏ p ∈ ((univ : Finset (LatticePlaquette d N)).filter (fun p => ¬IsPosPL p)).filter
      (fun p => ¬IsCrossPL p), Real.exp (β * xp n p (recombine ω)) = posWeightL n β (recombine (thetaExt ω)) := by
    unfold posWeightL
    simp_rw [recombine_thetaExt hN, xp_thetaL hinv]
    symm
    refine prod_nbij' mirrorPL mirrorPL (fun q hq => ?_) (fun p hp => ?_) (fun q _ => mirrorPL_involutive q)
      (fun p _ => mirrorPL_involutive p) (fun q _ => rfl)
    · simp only [mem_filter, mem_univ, true_and] at hq ⊢
      exact ⟨(posPL_mirror hN hq).1, (posPL_mirror hN hq).2⟩
    · simp only [mem_filter, mem_univ, true_and] at hp ⊢
      exact negPL_mirror hN hp.1 hp.2
  have hcross : ∏ p ∈ (univ : Finset (LatticePlaquette d N)).filter IsCrossPL, Real.exp (β * xp n p (recombine ω)) =
      Real.exp (β * ∑ j, crossFeat n j ω * crossFeat n j (thetaExt ω)) := by
    rw [← Real.exp_sum, ← Finset.mul_sum, sum_cross_xp hN hU]
  rw [hcr, hneg, hcross]
  unfold posWeightL
  ring

/-- **Reflection positivity of the Wilson measure for the link reflection** (`β ≥ 0`). For every bounded measurable `F`
    depending only on the links of the open positive half (spatial links with `t < N/2`, temporal links from `t` to
    `t + 1` with `t + 2 ≤ N/2`): `∫ F · (F ∘ Θ) · ∏_p exp(β Re tr U_p) d(productHaar) ≥ 0`, with `Θ` the link reflection
    `t ↦ −1 − t` (temporal links reversed). -/
theorem wilson_rp_link {β : ℝ} (hβ : 0 ≤ β) {F : GaugeConnection G d N → ℝ} (hF : LinkDep F (posLinksL d N))
    (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaL U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
      ∂(productHaar G d N) := by
  have : Nonempty G := ⟨1⟩
  have mW := measurable_wilsonWeight hc β (univ : Finset (LatticePlaquette d N))
  have mWp := measurable_wilsonWeight hc β ((univ : Finset (LatticePlaquette d N)).filter IsPosPL)
  rw [← integral_comp_of_measurePreserving measurePreserving_recombine
    (g := fun U => F U * F (thetaL U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U))
    ((mF.mul (mF.comp measurable_thetaL)).mul mW).aestronglyMeasurable]
  have key : ∀ ω : ExtIdx d N → G,
      F (recombine ω) * F (thetaL (recombine ω)) *
        ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p (recombine ω)) =
      (F (recombine ω) * posWeightL n β (recombine ω)) *
        (F (recombine (thetaExt ω)) * posWeightL n β (recombine (thetaExt ω))) * (fun _ => (1 : ℝ)) ω *
          Real.exp (β * ∑ j, crossFeat n j ω * crossFeat n j (thetaExt ω)) := by
    intro ω
    rw [wilson_weight_factor_ext hN hc hU β ω, ← recombine_thetaExt hN]
    ring
  simp_rw [key]
  have hrec : Measurable (recombine (G := G) (d := d) (N := N)) := measurePreserving_recombine.measurable
  exact config_rp_kernel (haarG G) (fun x => by
      rcases x with x | c
      · exact linkTwist_measurePreserving x.1
      · exact MeasurePreserving.id _)
    (isReflection_thetaExt hN)
    (F := fun ω => F (recombine ω) * posWeightL n β (recombine ω)) (B := fun _ => 1)
    ((depPos_comp_recombine hN hF).mul (depPos_comp_recombine hN (posWeightL_linkDep hN β)))
    (fun _ _ _ => rfl) ((mF.comp hrec).mul (mWp.comp hrec)) measurable_const
    (((IsBdd.of_abs bF).comp _).mul ((isBdd_wilsonWeight hU β _).comp _)) (IsBdd.const 1)
    (fun _ => zero_le_one) (crossFeat_depPos hN) (measurable_crossFeat hc) (isBdd_crossFeat hU) hβ

end Measure

/-! ### SU(2) and U(n) -/

instance : (haarG SU2).IsMulRightInvariant := by
  show (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SU2)).IsMulRightInvariant
  have := isProbabilityMeasure_haarMeasure_top (G := SU2)
  exact isMulRightInvariant_of_compact _

instance (n : ℕ) : (haarG (Un n)).IsMulRightInvariant := by
  show (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (Un n))).IsMulRightInvariant
  have := isProbabilityMeasure_haarMeasure_top (G := Un n)
  exact isMulRightInvariant_of_compact _

/-- **Reflection positivity of SU(2) lattice gauge theory for the link reflection** (`β ≥ 0`). -/
theorem wilson_rp_link_SU2 (hN : Even N) {β : ℝ} (hβ : 0 ≤ β) {F : GaugeConnection SU2 d N → ℝ}
    (hF : LinkDep F (posLinksL d N)) (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaL U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 2 p U)
      ∂(productHaar SU2 d N) :=
  wilson_rp_link hN continuous_subtype_val (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) hβ hF mF bF

/-- **Reflection positivity of U(n) lattice gauge theory for the link reflection** (`β ≥ 0`). -/
theorem wilson_rp_link_Un (n : ℕ) (hN : Even N) {β : ℝ} (hβ : 0 ≤ β) {F : GaugeConnection (Un n) d N → ℝ}
    (hF : LinkDep F (posLinksL d N)) (mF : Measurable F) (bF : ∃ M, ∀ U, |F U| ≤ M) :
    0 ≤ ∫ U, F U * F (thetaL U) * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
      ∂(productHaar (Un n) d N) :=
  wilson_rp_link hN continuous_subtype_val (fun g => g.2) hβ hF mF bF

end Positivity
