/-
Proof phase, cycle 6, workstream 1 (c6a-flip): the flip probability of the centre sector and the reflection bound
`p ≤ 1/2` on the real 4D SU(2) Wilson measure (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c6a-flip/NOTE.md`, section 1.
-/

import ProofPhase.RouteB.FluxEnergy

/-!
# `Z_tw ≤ Z`: the twisted partition function never exceeds the periodic one (reflection positivity)

**Setting.** The time chain of `ProofPhase.RouteB.Chain` (`ℤ/Tℤ × spatial graph`, `T` even, any chain weight
`W = ∏_t V(a_t) K(a_t, b_t, a_{t+1})`). A **slice twist** is a linkwise map `g e : G → G` of the spatial links of one
slice (`sliceMap g`), measure preserving and involutive on each link, that leaves the slice weight `V` invariant. The
**twisted weight** `twWeight` replaces, in the single time step `t = 0`, the factor `K(a_0, b_0, a_1)` by
`K(g·a_0, b_0, a_1)`; `cZtw = ∫ twWeight`.

For the Wilson chain (`wilsonChain`) and `g` = multiplication of the first-direction links of the plane `x¹ = c` by a
central `z` with `rep z = −1`, `z² = 1` (SU(2): `z = −1`), the twisted weight is exactly the Wilson weight with the
temporal plaquettes of the `(t, x¹)` plane at `t = 0`, `x¹ = c` (all `x², x³`) entering with `−β`
(`stepK_flipA_left`): the 't Hooft twist in the plane `(0, 1)`. Its `Z₂` Fourier transform gives the electric-flux
partition functions `Z_{e=0,1} = (Z ± Z_tw)/2` (not formalised here, standard).

**Theorem (`cZtw_le_cZ`).** For every chain weight with `K > 0`, every slice twist and every even `T`:
`Z_tw ≤ Z`. Proof: with `A`, `B` of `cweight_factor` and `σ` the twist of slice `0` (a fixed slice of the reflection),
`Z_tw = ⟨A∘σ, A⟩`, `Z = ⟨A, A⟩ = ⟨A∘σ, A∘σ⟩` for the reflection form `⟨F, F'⟩ = ∫ F · (F'∘Θ) · B`, and the form is
positive (`Positivity.config_rp`) and symmetric under `σ`; so `0 ≤ ⟨A∘σ − A, A∘σ − A⟩ = 2Z − 2Z_tw`. Moreover
`Z − Z_tw = ½ ⟨A∘σ − A, A∘σ − A⟩` exactly (`cZ_sub_cZtw_eq`): **the electric-flux partition function `Z_{e=1}` is a
reflection-positivity norm.**

**SU(2) (`su2_Ztw_le_Z`, `su2_flipProb_le_half`).** On `ℤ/Tℤ × (ℤ/Lℤ)³` with any spatial (magnetic) twist `P` as
background, every `β ∈ ℝ`, every `L ≥ 1`, every even `T`, every plane position `c`:
`Z_tw ≤ Z`, hence the flip probability `p = Z_tw/(Z_tw + Z) ∈ [0, ½]`, and `0 < Z_tw`, `0 < Z`.

**Claim discipline.** Substantive (lattice, reflection positivity) but **group-blind**: true for every compact group with
such a centre element (U(1), Z₂, Q8, 2T, 2O, 2I), so `p ≤ ½` carries no Yang–Mills content. It needs one even extent
in a direction of the twist plane: for odd extents in both twist directions it fails in general at `β < 0` (2D Z₂ and
SU(2), exact formulas in the note); for `β ≥ 0` and odd extents it holds by positivity of the transfer matrix (paper).
Not formalised: the bridge from this chain to `ProofPhase.RouteB.twistZ` on `(ℤ/Nℤ)⁴` (with `T = L` the chain is that
lattice; on it all six planes have the same `Z_tw` by `twistZ_perm`).
-/

open MeasureTheory Finset Positivity AreaLaw.Concrete ProofPhase.RouteB

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Flip

/-! ## The twisted chain weight -/

section Chain

variable {G : Type*} [Group G] [MeasurableSpace G] {E S : Type*} [Fintype E] [Fintype S] {T : ℕ} [NeZero T]

/-- A linkwise map of one slice's spatial links. -/
def sliceMap (g : E → G → G) (a : E → G) : E → G := fun e => g e (a e)

/-- Apply the slice twist `g` to the spatial links of slice `0` (all other links unchanged). -/
def flip0 (g : E → G → G) (U : CCfg G E S T) : CCfg G E S T
  | (t, .inl e) => if t = 0 then g e (U (t, .inl e)) else U (t, .inl e)
  | (t, .inr s) => U (t, .inr s)

theorem sp_flip0 (g : E → G → G) (U : CCfg G E S T) (t : ZMod T) :
    sp (flip0 g U) t = if t = 0 then sliceMap g (sp U t) else sp U t := by
  funext e
  by_cases h : t = 0
  · subst h; simp only [ite_true]; show flip0 g U (0, .inl e) = _; simp [flip0, sliceMap, sp]
  · simp only [h, ite_false]; show flip0 g U (t, .inl e) = U (t, .inl e); simp [flip0, h]

theorem sp_flip0_zero (g : E → G → G) (U : CCfg G E S T) : sp (flip0 g U) 0 = sliceMap g (sp U 0) := by
  rw [sp_flip0]; simp

theorem sp_flip0_ne (g : E → G → G) (U : CCfg G E S T) {t : ZMod T} (ht : t ≠ 0) : sp (flip0 g U) t = sp U t := by
  rw [sp_flip0]; simp [ht]

theorem tm_flip0 (g : E → G → G) (U : CCfg G E S T) (t : ZMod T) : tm (flip0 g U) t = tm U t := rfl

theorem flip0_flip0 {g : E → G → G} (hinv : ∀ e, Function.Involutive (g e)) (U : CCfg G E S T) :
    flip0 g (flip0 g U) = U := by
  funext l
  rcases l with ⟨t, e | s⟩
  · by_cases h : t = 0
    · simp [flip0, h, hinv e _]
    · simp [flip0, h]
  · rfl

theorem ctheta_flip0 (g : E → G → G) (U : CCfg G E S T) : ctheta (flip0 g U) = flip0 g (ctheta U) := by
  funext l
  rcases l with ⟨t, e | s⟩
  · show ctwist (t, Sum.inl e) (flip0 g U (cmirror (t, .inl e))) = flip0 g (ctheta U) (t, .inl e)
    simp only [cmirror, ctwist, id, flip0, neg_eq_zero]
    rfl
  · rfl

theorem flip0_agree {g : E → G → G} {U V : CCfg G E S T} {P : CLink E S T → Prop} (h : ∀ l, P l → U l = V l) :
    ∀ l, P l → flip0 g U l = flip0 g V l := by
  rintro ⟨t, e | s⟩ hl
  · simp only [flip0]; rw [h _ hl]
  · simp only [flip0]; exact h _ hl

theorem measurable_flip0 {g : E → G → G} (hg : ∀ e, Measurable (g e)) :
    Measurable (flip0 (S := S) (T := T) g) := by
  refine measurable_pi_iff.mpr fun l => ?_
  rcases l with ⟨t, e | s⟩
  · by_cases h : t = 0
    · simp only [flip0, h, ite_true]; exact (hg e).comp (measurable_pi_apply _)
    · simp only [flip0, h, ite_false]; exact measurable_pi_apply _
  · exact measurable_pi_apply _

variable [HasHaarProbability G]

theorem measurePreserving_flip0 {g : E → G → G} (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G)) :
    MeasurePreserving (flip0 (S := S) (T := T) g) (cHaar G E S T) (cHaar G E S T) := by
  have h := measurePreserving_pi (fun _ : CLink E S T => haarG G) (fun _ => haarG G)
    (f := fun l => match l with
      | (t, .inl e) => if t = 0 then g e else id
      | (_, .inr _) => id) (fun l => by
      rcases l with ⟨t, e | s⟩
      · dsimp only
        split_ifs
        · exact hg e
        · exact MeasurePreserving.id _
      · exact MeasurePreserving.id _)
  unfold cHaar
  convert h using 1
  funext U l
  rcases l with ⟨t, e | s⟩
  · simp only [flip0]; split_ifs <;> rfl
  · rfl

variable (w : ChainWeight G E S) (g : E → G → G)

/-- One time step of the twisted weight: the step `t = 0` sees the twisted slice `g · a_0` on its left. -/
def twStep (U : CCfg G E S T) (t : ZMod T) : ℝ :=
  w.V (sp U t) * w.K (if t = 0 then sliceMap g (sp U t) else sp U t) (tm U t) (sp U (t + 1))

/-- **The twisted weight**: one twisted time step (`t = 0`), all other steps as in `cweight`. -/
def twWeight (U : CCfg G E S T) : ℝ := ∏ t, twStep w g U t

/-- **The twisted partition function** `Z_tw = ∫ twWeight`. -/
def cZtw : ℝ := ∫ U, twWeight (T := T) w g U ∂(cHaar G E S T)

theorem twWeight_nonneg (U : CCfg G E S T) : 0 ≤ twWeight w g U :=
  prod_nonneg fun _ _ => mul_nonneg (w.V_nonneg _) (w.K_nonneg _ _ _)

theorem cZtw_nonneg : 0 ≤ cZtw (T := T) w g := integral_nonneg fun U => twWeight_nonneg w g U

theorem two_le_of_even (hT : Even T) : 2 ≤ T := by
  obtain ⟨k, hk⟩ := hT
  have := NeZero.ne T
  omega

theorem one_ne_zero_of_even (hT : Even T) : (1 : ZMod T) ≠ 0 := by
  have h2 := two_le_of_even hT
  intro h
  have := congrArg ZMod.val h
  rw [ZMod.val_one'' (by omega), ZMod.val_zero] at this
  exact one_ne_zero this

/-- Twisted and untwisted weights differ only in the step `t = 0`. -/
theorem twWeight_mul (U : CCfg G E S T) :
    twWeight w g U * w.K (sp U 0) (tm U 0) (sp U 1) =
      cweight w U * w.K (sliceMap g (sp U 0)) (tm U 0) (sp U 1) := by
  unfold twWeight cweight
  rw [← mul_prod_erase univ _ (mem_univ (0 : ZMod T)), ← mul_prod_erase univ _ (mem_univ (0 : ZMod T))]
  have hrest : ∏ t ∈ univ.erase (0 : ZMod T), twStep w g U t = ∏ t ∈ univ.erase (0 : ZMod T), cstep w U t :=
    prod_congr rfl fun t ht => by
      simp only [twStep, cstep, (mem_erase.1 ht).1, ite_false]
  rw [hrest]
  simp only [twStep, cstep, ite_true, zero_add]
  ring

/-- The open positive half of the twisted configuration differs from that of `U` only in the step `t = 0`. -/
theorem cA_flip0_mul (hT : Even T) (U : CCfg G E S T) :
    cA w (flip0 g U) * w.K (sp U 0) (tm U 0) (sp U 1) =
      cA w U * w.K (sliceMap g (sp U 0)) (tm U 0) (sp U 1) := by
  have h2 := two_le_of_even hT
  obtain ⟨k, hk⟩ := hT
  have h0 : (0 : ZMod T) ∈ tLow T := by
    simp only [tLow, mem_filter, mem_univ, true_and, ZMod.val_zero]; omega
  unfold cA
  have hV : ∏ t ∈ tPos T, w.V (sp (flip0 g U) t) = ∏ t ∈ tPos T, w.V (sp U t) :=
    prod_congr rfl fun t ht => by
      have : t ≠ 0 := by
        rintro rfl; simp [tPos] at ht
      rw [sp_flip0_ne g U this]
  rw [hV, ← mul_prod_erase _ _ h0, ← mul_prod_erase _ _ h0]
  have hrest : ∏ t ∈ (tLow T).erase 0, w.K (sp (flip0 g U) t) (tm (flip0 g U) t) (sp (flip0 g U) (t + 1)) =
      ∏ t ∈ (tLow T).erase 0, w.K (sp U t) (tm U t) (sp U (t + 1)) :=
    prod_congr rfl fun t ht => by
      have ht0 := (mem_erase.1 ht).1
      have htl := (mem_erase.1 ht).2
      simp only [tLow, mem_filter, mem_univ, true_and] at htl
      have h1 : t + 1 ≠ 0 := by
        intro h
        have hv := val_add_one_of_lt t (by omega)
        rw [h, ZMod.val_zero] at hv
        omega
      rw [sp_flip0_ne g U ht0, sp_flip0_ne g U h1, tm_flip0]
  rw [hrest, zero_add, sp_flip0_zero, sp_flip0_ne g U (one_ne_zero_of_even ⟨k, hk⟩), tm_flip0]
  ring

/-- The slice twist leaves the fixed-slice weight unchanged. -/
theorem cB_flip0 (hT : Even T) (hV : ∀ a, w.V (sliceMap g a) = w.V a) (U : CCfg G E S T) :
    cB w (flip0 g U) = cB w U := by
  unfold cB
  refine prod_congr rfl fun t _ => ?_
  by_cases h : t = 0
  · subst h; rw [sp_flip0_zero, hV]
  · rw [sp_flip0_ne g U h]

/-- **The twisted weight factorises** (for `K > 0`): `twWeight U = A(σU) · A(ΘU) · B(U)`. -/
theorem twWeight_factor (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c) (U : CCfg G E S T) :
    twWeight w g U = cA w (flip0 g U) * cA w (ctheta U) * cB w U := by
  have hk := hK (sp U 0) (tm U 0) (sp U 1)
  have e1 := twWeight_mul w g U
  have e2 := cA_flip0_mul w g hT U
  rw [cweight_factor w hT] at e1
  apply mul_right_cancel₀ hk.ne'
  calc twWeight w g U * w.K (sp U 0) (tm U 0) (sp U 1)
      = cA w U * cA w (ctheta U) * cB w U * w.K (sliceMap g (sp U 0)) (tm U 0) (sp U 1) := e1
    _ = (cA w U * w.K (sliceMap g (sp U 0)) (tm U 0) (sp U 1)) * cA w (ctheta U) * cB w U := by ring
    _ = (cA w (flip0 g U) * w.K (sp U 0) (tm U 0) (sp U 1)) * cA w (ctheta U) * cB w U := by rw [e2]
    _ = cA w (flip0 g U) * cA w (ctheta U) * cB w U * w.K (sp U 0) (tm U 0) (sp U 1) := by ring

theorem measurable_twWeight (hg : ∀ e, Measurable (g e)) : Measurable (twWeight (T := T) w g) := by
  refine Finset.measurable_prod _ fun t _ => ?_
  have hsl : Measurable fun U : CCfg G E S T => (if t = 0 then sliceMap g (sp U t) else sp U t) := by
    by_cases h : t = 0
    · simp only [h, ite_true]
      exact measurable_pi_iff.mpr fun e => (hg e).comp ((measurable_pi_apply e).comp (measurable_sp 0))
    · simp only [h, ite_false]; exact measurable_sp t
  exact (w.measV.comp (measurable_sp t)).mul
    (w.measK.comp (hsl.prodMk ((measurable_tm t).prodMk (measurable_sp (t + 1)))))

variable [MeasurableInv G] [(haarG G).IsInvInvariant]

/-- **The electric-flux partition function is a reflection-positivity norm:**
`Z − Z_tw = ½ ∫ F · (F ∘ Θ) · B` with `F = A∘σ − A` (`T` even, `K > 0`, `g` a slice twist). -/
theorem cZ_sub_cZtw_eq (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G)) (hinv : ∀ e, Function.Involutive (g e))
    (hV : ∀ a, w.V (sliceMap g a) = w.V a) :
    2 * (cZ (T := T) w - cZtw (T := T) w g) =
      ∫ U, (cA w (flip0 g U) - cA w U) * (cA w (flip0 g (ctheta U)) - cA w (ctheta U)) * cB w U
        ∂(cHaar G E S T) := by
  have hmp := measurePreserving_flip0 (S := S) (T := T) hg
  have mg : ∀ e, Measurable (g e) := fun e => (hg e).measurable
  have mA := measurable_cA (T := T) w
  have mB := measurable_cB (T := T) w
  have mth := (measurePreserving_ctheta (G := G) (E := E) (S := S) (T := T)).measurable
  have mfl := measurable_flip0 (S := S) (T := T) mg
  have bA := cA_isBdd (T := T) w
  have bB := cB_isBdd (T := T) w
  -- the four pieces
  set f1 : CCfg G E S T → ℝ := fun U => cweight w (flip0 g U)
  set f2 : CCfg G E S T → ℝ := fun U => twWeight w g U
  set f3 : CCfg G E S T → ℝ := fun U => cA w U * cA w (flip0 g (ctheta U)) * cB w U
  set f4 : CCfg G E S T → ℝ := fun U => cweight w U
  have hpt : ∀ U, (cA w (flip0 g U) - cA w U) * (cA w (flip0 g (ctheta U)) - cA w (ctheta U)) * cB w U =
      f1 U - f2 U - f3 U + f4 U := by
    intro U
    simp only [f1, f2, f3, f4]
    rw [cweight_factor w hT (flip0 g U), ctheta_flip0, cB_flip0 w g hT hV, twWeight_factor w g hT hK,
      cweight_factor w hT U]
    ring
  have i1 : Integrable f1 (cHaar G E S T) :=
    IsBdd.integrable ((cweight_isBdd (T := T) w).comp _) ((measurable_cweight w).comp mfl).aestronglyMeasurable
  have i2 : Integrable f2 (cHaar G E S T) := by
    refine IsBdd.integrable ?_ (measurable_twWeight w g mg).aestronglyMeasurable
    obtain ⟨M1, hM1⟩ := bA
    obtain ⟨M2, hM2⟩ := bB
    refine ⟨M1 * M1 * M2, fun U => ?_⟩
    have := twWeight_factor w g hT hK U
    simp only [f2]
    rw [this, norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hM1 _) (hM1 _) (norm_nonneg _) ((norm_nonneg _).trans (hM1 U)))
      (hM2 U) (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans (hM1 U)) ((norm_nonneg _).trans (hM1 U)))
  have i3 : Integrable f3 (cHaar G E S T) :=
    IsBdd.integrable ((bA.mul (bA.comp _)).mul bB)
      ((mA.mul (mA.comp (mfl.comp mth))).mul mB).aestronglyMeasurable
  have i4 : Integrable f4 (cHaar G E S T) :=
    IsBdd.integrable (cweight_isBdd (T := T) w) (measurable_cweight w).aestronglyMeasurable
  -- f1 integrates to Z, f3 to Z_tw
  have I1 : ∫ U, f1 U ∂(cHaar G E S T) = cZ (T := T) w :=
    integral_comp_of_measurePreserving hmp (measurable_cweight w).aestronglyMeasurable
  have hf3 : ∀ U, f3 (flip0 g U) = f2 U := by
    intro U
    simp only [f3, f2]
    rw [← ctheta_flip0, flip0_flip0 hinv, cB_flip0 w g hT hV, twWeight_factor w g hT hK]
  have I3 : ∫ U, f3 U ∂(cHaar G E S T) = cZtw (T := T) w g := by
    rw [← integral_comp_of_measurePreserving hmp i3.aestronglyMeasurable]
    simp_rw [hf3]
    rfl
  simp_rw [hpt]
  have a1 := integral_add ((i1.sub i2).sub i3) i4
  have a2 := integral_sub (i1.sub i2) i3
  have a3 := integral_sub i1 i2
  simp only [Pi.sub_apply] at a1 a2 a3
  rw [a1, a2, a3, I1, I3]
  unfold cZ cZtw
  simp only [f2, f4]
  ring

/-- **The reflection bound `Z_tw ≤ Z`** for every chain weight with `K > 0`, every slice twist (linkwise, measure
preserving, involutive, `V`-invariant) and every even time extent. -/
theorem cZtw_le_cZ (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G)) (hinv : ∀ e, Function.Involutive (g e))
    (hV : ∀ a, w.V (sliceMap g a) = w.V a) : cZtw (T := T) w g ≤ cZ (T := T) w := by
  have : Nonempty G := ⟨1⟩
  have h := cZ_sub_cZtw_eq w g hT hK hg hinv hV
  have mg : ∀ e, Measurable (g e) := fun e => (hg e).measurable
  have hFd : CDep (fun U : CCfg G E S T => cA w (flip0 g U) - cA w U) CHalf := fun U V hUV => by
    simp only []
    rw [cA_dep w hT U V hUV, cA_dep w hT _ _ (flip0_agree hUV)]
  have bF : IsBdd (fun U : CCfg G E S T => cA w (flip0 g U) - cA w U) := by
    obtain ⟨M, hM⟩ := cA_isBdd (T := T) w
    exact ⟨M + M, fun U => (norm_sub_le _ _).trans (add_le_add (hM _) (hM _))⟩
  have hrp := config_rp (haarG G) (fun x => by
      rcases x with ⟨⟨t, e | s⟩, hx⟩
      · exact MeasurePreserving.id _
      · exact Measure.measurePreserving_inv _)
    (isReflection_ctheta (G := G) (E := E) (S := S) hT) (F := fun U : CCfg G E S T => cA w (flip0 g U) - cA w U)
    (depPos_of_cdep hT hFd) (cB_depFix w hT)
    (((measurable_cA w).comp (measurable_flip0 mg)).sub (measurable_cA w)) (measurable_cB w)
    bF (cB_isBdd w) (cB_nonneg w)
  have h2 : 0 ≤ 2 * (cZ (T := T) w - cZtw (T := T) w g) := le_of_le_of_eq hrp h.symm
  linarith

end Chain

/-! ## The SU(2) (any compact group) Wilson chain: the 't Hooft twist in the plane `(t, x¹)` -/

section Wilson

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n]
variable (L : ℕ) [NeZero L]

/-- The linkwise centre flip of the plane `x¹ = c` (first spatial direction), as a slice twist. -/
def flipG (z : G) (c : ZMod L) : LatticeLink 3 L → G → G :=
  fun e => if e.dir = 0 ∧ e.site 0 = c then (z * ·) else id

theorem sliceMap_flipG (z : G) (c : ZMod L) (a : GaugeConnection G 3 L) :
    sliceMap (flipG L z c) a = flipA L z c a := by
  funext e
  simp only [sliceMap, flipG, flipA]
  split_ifs <;> rfl

variable {z : G} (hz : ∀ g : G, Commute z g) (hzz : z * z = 1)
  (hrep : HasGaugeTrace.rep (G := G) (n := n) z = -1)

include hz hzz hrep in
/-- **The twisted step is the 't Hooft twist:** flipping slice `0` on the left of `stepK` multiplies the weight of the
temporal plaquette over the link `e` by `e^{−2β Re tr}` exactly when `e` is a first-direction link of the plane `x¹ = c`,
i.e. those plaquettes enter with `−β`. -/
theorem stepK_flipA_left (β : ℝ) (c : ZMod L) (a : GaugeConnection G 3 L) (b : FinLatticeSites 3 L → G)
    (c' : GaugeConnection G 3 L) :
    stepK L n β (flipA L z c a) b c' =
      ∏ e, Real.exp (β * (if e.dir = 0 ∧ e.site 0 = c then -1 else 1) * gaugeReTr G n (tempHol L a b c' e)) := by
  unfold stepK
  refine prod_congr rfl fun e _ => ?_
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  by_cases h : e.dir = 0 ∧ e.site 0 = c
  · have key : ∀ x y : G, x * (z * y)⁻¹ = z * (x * y⁻¹) := by
      intro x y; rw [mul_inv_rev, hzi, ← mul_assoc]; exact ((hz (x * y⁻¹)).eq).symm
    have ht : tempHol L (flipA L z c a) b c' e = z * tempHol L a b c' e := by
      simp only [tempHol, flipA, h, and_self, ite_true]
      exact key _ _
    rw [ht, gaugeReTr_mul_central hrep, ite_eq_left h]; ring_nf
  · have ht : tempHol L (flipA L z c a) b c' e = tempHol L a b c' e := by
      simp only [tempHol, flipA, h, ite_false]
    rw [ht, ite_eq_right h]; ring_nf

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

theorem stepK_pos (β : ℝ) (a : GaugeConnection G 3 L) (b : FinLatticeSites 3 L → G) (c : GaugeConnection G 3 L) :
    0 < stepK L n β a b c :=
  prod_pos fun _ _ => Real.exp_pos _

variable [HasHaarProbability G] [MeasurableInv G] [(haarG G).IsInvInvariant] [(haarG G).IsMulLeftInvariant]

include hz hzz in
/-- **`Z_tw ≤ Z` for the Wilson chain** (any compact group with a central involution `z`): the 't Hooft twist in the
plane `(t, x¹)`, at the plane `x¹ = c`, on top of any spatial twist `P`, every `β`, every even `T`. -/
theorem wilson_Ztw_le_Z (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ} [NeZero T] (hT : Even T) :
    cZtw (T := T) (wilsonChain L hc hU β P) (flipG L z c) ≤ cZ (T := T) (wilsonChain L hc hU β P) := by
  refine cZtw_le_cZ _ _ hT (fun a b c => stepK_pos L β a b c) (fun e => ?_) (fun e => ?_) (fun a => ?_)
  · unfold flipG; split_ifs
    · exact measurePreserving_mul_left (haarG G) z
    · exact MeasurePreserving.id _
  · unfold flipG; split_ifs
    · intro x; simp only [← mul_assoc, hzz, one_mul]
    · exact fun x => rfl
  · show sliceV L n β P (sliceMap (flipG L z c) a) = sliceV L n β P a
    rw [sliceMap_flipG, sliceV_flip L hz]

end Wilson

/-! ## SU(2) -/

/-- `−1 · −1 = 1` in SU(2). -/
theorem negOneSU2_mul_self : negOneSU2 * negOneSU2 = 1 :=
  Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * -1 = 1 by simp)

theorem negOneSU2_central (g : SU2) : Commute negOneSU2 g :=
  Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * g.val = g.val * -1 by simp)

/-- The periodic SU(2) partition function of `ℤ/Tℤ × (ℤ/Lℤ)³` (coupling `β`, spatial twist `P`). -/
def su2Z (L : ℕ) [NeZero L] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (T : ℕ) [NeZero T] : ℝ :=
  cZ (T := T) (wilsonChain (G := SU2) (n := 2) L continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β P)

/-- The SU(2) partition function with the 't Hooft twist in the plane `(t, x¹)` at `x¹ = c` (on top of `P`). -/
def su2Ztw (L : ℕ) [NeZero L] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T] : ℝ :=
  cZtw (T := T) (wilsonChain (G := SU2) (n := 2) L continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β P) (flipG L negOneSU2 c)

/-- **The reflection bound for SU(2): `Z_tw ≤ Z`**, every `β ∈ ℝ`, every `L`, every even `T`, every spatial
background twist `P`, every plane position `c`. -/
theorem su2_Ztw_le_Z (L : ℕ) [NeZero L] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ} [NeZero T]
    (hT : Even T) : su2Ztw L β P c T ≤ su2Z L β P T :=
  wilson_Ztw_le_Z L negOneSU2_central negOneSU2_mul_self continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β P c hT

theorem su2Ztw_nonneg (L : ℕ) [NeZero L] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ)
    [NeZero T] : 0 ≤ su2Ztw L β P c T :=
  cZtw_nonneg _ _

/-- **The flip probability** of the centre sector: `p = Z_tw / (Z_tw + Z)`. -/
def su2FlipProb (L : ℕ) [NeZero L] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T] : ℝ :=
  su2Ztw L β P c T / (su2Ztw L β P c T + su2Z L β P T)

/-- **`0 ≤ p ≤ ½`** on the real SU(2) Wilson measure (every `β`, `L`, `P`, `c`; `T` even). -/
theorem su2_flipProb_le_half (L : ℕ) [NeZero L] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ}
    [NeZero T] (hT : Even T) : 0 ≤ su2FlipProb L β P c T ∧ su2FlipProb L β P c T ≤ 1 / 2 := by
  have h1 := su2_Ztw_le_Z L β P c hT
  have h0 := su2Ztw_nonneg L β P c T
  unfold su2FlipProb
  refine ⟨div_nonneg h0 (by linarith), ?_⟩
  rcases (add_nonneg h0 (h0.trans h1)).eq_or_lt with hz | hpos
  · rw [← hz, div_zero]; norm_num
  · rw [div_le_iff₀ hpos]; linarith

end ProofPhase.Flip
