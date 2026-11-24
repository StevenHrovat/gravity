/-
SU(N) primes round (sun-primes): the reflection bound for a non-involutive twist and the `Z_N` electric sectors as
reflection-positivity norms (2026-11-23). Released under Apache 2.0.

Note: `docs/unified/SUN-PRIMES.md`, section 2.
-/

import ProofPhase.Flip.Strict

/-!
# The twist bound for `Z_N`: non-involutive twists, electric sectors as norms

**Setting.** The time chain and reflection of `ProofPhase.Flip.Bound` (`T` even, any chain weight with `K > 0`). There a
slice twist was **involutive** (`Z_2`, SU(2)). Here a twist `g` only needs a **left inverse** `h` (`g e (h e x) = x`),
both measure preserving, `V`-invariant. This is the case of a centre element `ω^k` of SU(N), whose inverse is `ω^{-k}`.

**1. The unitary identity (`cZ_sub_cZtw_eq_u`, `cZtw_eq_inv`, `cZtw_le_cZ_u`).** With `A`, `B`, `Θ` of `cweight_factor`
and `σ = flip0 g`:
* `∫ A · (A∘σ∘Θ) · B = Z_tw(h)` (`integral_cross_eq`): the reflected pairing of `A∘σ` with `A` is the partition
  function twisted by the **inverse** element;
* `Z_tw(g) = Z_tw(h)` (`cZtw_eq_inv`): the symmetry of the reflection form exchanges the twist with its inverse. For SU(N)
  this is `Z_tw,k = Z_tw,N−k` (conjugation pairs `k` with `N − k`);
* `2 (Z − Z_tw(g)) = ⟨A∘σ − A, A∘σ − A⟩` (the form `⟨F, F'⟩ = ∫ F · (F'∘Θ) · B`), hence `Z_tw(g) ≤ Z`.
This is the unitary form `Z − Re⟨A, A∘σ⟩ = ½ ‖A∘σ − A‖²` of the brief; on the real chain the "real part" is automatic,
because `Z_tw(g) = Z_tw(h)` makes the pairing symmetric.

**2. Strict bound (`cZtw_lt_cZ_of_moment_u`, `cZtw_lt_cZ_of_step_u`).** As in `ProofPhase.Flip.Strict`, with the odd
sector replaced by the **difference sector** `{φ∘h − φ}` (charge under the twist, `Z_N` instead of `Z_2`): if
`⟨φ∘h − φ, 𝒦 χ⟩_V ≠ 0` for some bounded measurable `φ`, `χ`, then `Z_tw(g) < Z` for every even `T`. The descent
argument (`secVanish_descend`) is the one of `Strict`, for any sector predicate.

**3. A cyclic family of twists (`ZFam`): the electric sectors are norms (`elec_rp`).** For a family `g_k`, `k ∈ ZMod N`,
with `g_k ∘ g_l = g_{k+l}` and `g_0 = id` (the centre `Z_N` acting on the twist plane), write `Z_k = Z_tw(g_k)`:
* `∫ A(σ_k U) · A(σ_l Θ U) · B(U) = Z_{k−l}` (`integral_pair_eq`);
* for every `e` and `ψ` the standard additive character of `ZMod N` (`ψ(x) = e^{2πi x/N}`),
  `N · Re 𝓕Z(e) = ⟨f_re, f_re⟩ + ⟨f_im, f_im⟩ ≥ 0` with `f = Σ_k ψ(−k e) · A∘σ_k` (`elec_rp`, `elec_nonneg`), where
  `𝓕Z(e) = Σ_k ψ(−k e) Z_k` is the discrete Fourier transform (Mathlib's `ZMod.dft`). So the electric-sector partition
  function `Z_e = (1/N) 𝓕Z(e)` has **nonnegative real part by reflection positivity alone**; with
  `Z_k = Z_{−k}` it is real (`ProofPhase.General.SUNTwistSectors`), hence `Z_e ≥ 0`. This is the `Z_N` version of
  "`Z_{e=1} = ½ ‖A∘σ − A‖²`" in `Bound`, and it needs no transfer-matrix reading.

**Claim discipline.** Model-blind (any chain weight, any compact group, any twist with an inverse). Strictness at each
finite lattice, no size control: no lower bound on `Z − Z_tw` uniform in the volume, no flux free energy, no
confinement or mass-gap content. As in `Bound`, the bridge from this chain to `ProofPhase.RouteB.twistZ` on `(ℤ/Nℤ)⁴` is
not formalised.
-/

open MeasureTheory Finset Positivity AreaLaw.Concrete ProofPhase.RouteB ProofPhase.Flip

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

/-! ## Twists with a left inverse -/

section UChain

variable {G : Type*} [Group G] [MeasurableSpace G] {E S : Type*} [Fintype E] [Fintype S] {T : ℕ} [NeZero T]

theorem flip0_flip0_of_left_inv {g h : E → G → G} (hgh : ∀ e x, g e (h e x) = x) (U : CCfg G E S T) :
    flip0 g (flip0 h U) = U := by
  funext l
  rcases l with ⟨t, e | s⟩
  · by_cases ht : t = 0
    · simp [flip0, ht, hgh e _]
    · simp [flip0, ht]
  · rfl

theorem sliceMap_sliceMap_of_left_inv {g h : E → G → G} (hgh : ∀ e x, g e (h e x) = x) (a : E → G) :
    sliceMap g (sliceMap h a) = a :=
  funext fun e => hgh e (a e)

theorem V_sliceMap_of_left_inv {w : ChainWeight G E S} {g h : E → G → G} (hgh : ∀ e x, g e (h e x) = x)
    (hV : ∀ a, w.V (sliceMap g a) = w.V a) (a : E → G) : w.V (sliceMap h a) = w.V a := by
  have := hV (sliceMap h a)
  rw [sliceMap_sliceMap_of_left_inv hgh] at this
  exact this.symm

theorem measurable_sliceMap {g : E → G → G} (hg : ∀ e, Measurable (g e)) : Measurable (sliceMap g) :=
  measurable_pi_iff.mpr fun e => (hg e).comp (measurable_pi_apply e)

variable [HasHaarProbability G] [MeasurableInv G] [(haarG G).IsInvInvariant]
variable (w : ChainWeight G E S) (g h : E → G → G)

theorem cA_flip0_depPos (hT : Even T) :
    DepPos (csplit (E := E) (S := S) hT) (fun U : CCfg G E S T => cA w (flip0 g U)) :=
  depPos_of_cdep hT fun U V hUV => cA_dep w hT _ _ (flip0_agree hUV)

theorem cA_depPos (hT : Even T) : DepPos (csplit (E := E) (S := S) hT) (cA (G := G) (T := T) w) :=
  depPos_of_cdep hT fun U V hUV => cA_dep w hT _ _ hUV

/-- **The reflected pairing is the inverse twist**: `∫ A · (A∘σ_g∘Θ) · B = Z_tw(h)` when `h` is a right inverse of `g`. -/
theorem integral_cross_eq (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, Measurable (g e)) (hh : ∀ e, MeasurePreserving (h e) (haarG G) (haarG G))
    (hgh : ∀ e x, g e (h e x) = x) (hV : ∀ a, w.V (sliceMap g a) = w.V a) :
    ∫ U, cA w U * cA w (flip0 g (ctheta U)) * cB w U ∂(cHaar G E S T) = cZtw (T := T) w h := by
  have hmp := measurePreserving_flip0 (S := S) (T := T) hh
  have mA := measurable_cA (T := T) w
  have mth := (measurePreserving_ctheta (G := G) (E := E) (S := S) (T := T)).measurable
  have i3 : Integrable (fun U => cA w U * cA w (flip0 g (ctheta U)) * cB w U) (cHaar G E S T) :=
    IsBdd.integrable (((cA_isBdd (T := T) w).mul ((cA_isBdd (T := T) w).comp _)).mul (cB_isBdd w))
      ((mA.mul (mA.comp ((measurable_flip0 hg).comp mth))).mul (measurable_cB w)).aestronglyMeasurable
  rw [← integral_comp_of_measurePreserving hmp i3.aestronglyMeasurable]
  show _ = ∫ U, twWeight w h U ∂(cHaar G E S T)
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only []
  rw [ctheta_flip0 h U, flip0_flip0_of_left_inv hgh, cB_flip0 w h hT (V_sliceMap_of_left_inv hgh hV),
    twWeight_factor w h hT hK]

/-- **The twist and its inverse give the same partition function**, `Z_tw(g) = Z_tw(h)` (symmetry of the reflection
form). For SU(N): `Z_tw,k = Z_tw,N−k`. -/
theorem cZtw_eq_inv (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, Measurable (g e)) (hh : ∀ e, MeasurePreserving (h e) (haarG G) (haarG G))
    (hgh : ∀ e x, g e (h e x) = x) (hV : ∀ a, w.V (sliceMap g a) = w.V a) :
    cZtw (T := T) w g = cZtw (T := T) w h := by
  have hΘ := isReflection_ctheta (G := G) (E := E) (S := S) hT
  have hs := config_symm (haarG G) measurePreserving_ctwist hΘ (cA_flip0_depPos w g hT) (cA_depPos w hT)
    (cB_depFix w hT) ((measurable_cA w).comp (measurable_flip0 hg)) (measurable_cA w) (measurable_cB w)
    ((cA_isBdd (T := T) w).comp _) (cA_isBdd w) (cB_isBdd w)
  rw [← integral_cross_eq w g h hT hK hg hh hgh hV]
  refine Eq.trans ?_ hs
  unfold cZtw
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  exact twWeight_factor w g hT hK U

/-- **The unitary identity**: `2 Z − Z_tw(g) − Z_tw(h) = ⟨A∘σ − A, A∘σ − A⟩`. -/
theorem cZ2_sub_eq (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G)) (hh : ∀ e, MeasurePreserving (h e) (haarG G) (haarG G))
    (hgh : ∀ e x, g e (h e x) = x) (hV : ∀ a, w.V (sliceMap g a) = w.V a) :
    2 * cZ (T := T) w - cZtw (T := T) w g - cZtw (T := T) w h =
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
  have I1 : ∫ U, f1 U ∂(cHaar G E S T) = cZ (T := T) w :=
    integral_comp_of_measurePreserving hmp (measurable_cweight w).aestronglyMeasurable
  have I3 : ∫ U, f3 U ∂(cHaar G E S T) = cZtw (T := T) w h := integral_cross_eq w g h hT hK mg hh hgh hV
  simp_rw [hpt]
  have a1 := integral_add ((i1.sub i2).sub i3) i4
  have a2 := integral_sub (i1.sub i2) i3
  have a3 := integral_sub i1 i2
  simp only [Pi.sub_apply] at a1 a2 a3
  rw [a1, a2, a3, I1, I3]
  unfold cZ cZtw
  simp only [f2, f4]
  ring

/-- **The electric-flux identity for a non-involutive twist**: `2 (Z − Z_tw(g)) = ⟨A∘σ − A, A∘σ − A⟩`. -/
theorem cZ_sub_cZtw_eq_u (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G)) (hh : ∀ e, MeasurePreserving (h e) (haarG G) (haarG G))
    (hgh : ∀ e x, g e (h e x) = x) (hV : ∀ a, w.V (sliceMap g a) = w.V a) :
    2 * (cZ (T := T) w - cZtw (T := T) w g) =
      ∫ U, (cA w (flip0 g U) - cA w U) * (cA w (flip0 g (ctheta U)) - cA w (ctheta U)) * cB w U
        ∂(cHaar G E S T) := by
  rw [← cZ2_sub_eq w g h hT hK hg hh hgh hV, ← cZtw_eq_inv w g h hT hK (fun e => (hg e).measurable) hh hgh hV]
  ring

/-- **`Z_tw(g) ≤ Z`** for every twist with a right inverse (measure preserving, `V`-invariant), every even `T`. -/
theorem cZtw_le_cZ_u (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G)) (hh : ∀ e, MeasurePreserving (h e) (haarG G) (haarG G))
    (hgh : ∀ e x, g e (h e x) = x) (hV : ∀ a, w.V (sliceMap g a) = w.V a) :
    cZtw (T := T) w g ≤ cZ (T := T) w := by
  have : Nonempty G := ⟨1⟩
  have mg : ∀ e, Measurable (g e) := fun e => (hg e).measurable
  have bF : IsBdd (fun U : CCfg G E S T => cA w (flip0 g U) - cA w U) := by
    obtain ⟨M, hM⟩ := cA_isBdd (T := T) w
    exact ⟨M + M, fun U => (norm_sub_le _ _).trans (add_le_add (hM _) (hM _))⟩
  have hrp := config_rp (haarG G) measurePreserving_ctwist
    (isReflection_ctheta (G := G) (E := E) (S := S) hT) (F := fun U : CCfg G E S T => cA w (flip0 g U) - cA w U)
    (depPos_of_cdep hT fun U V hUV => by
      rw [cA_dep w hT U V hUV, cA_dep w hT _ _ (flip0_agree hUV)]) (cB_depFix w hT)
    (((measurable_cA w).comp (measurable_flip0 mg)).sub (measurable_cA w)) (measurable_cB w)
    bF (cB_isBdd w) (cB_nonneg w)
  have h2 := cZ_sub_cZtw_eq_u w g h hT hK hg hh hgh hV
  have : 0 ≤ 2 * (cZ (T := T) w - cZtw (T := T) w g) := le_of_le_of_eq hrp h2.symm
  linarith

/-- **The strict bound from one boundary moment** (non-involutive twist). -/
theorem cZtw_lt_cZ_of_moment_u (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G)) (hh : ∀ e, MeasurePreserving (h e) (haarG G) (haarG G))
    (hgh : ∀ e x, g e (h e x) = x) (hV : ∀ a, w.V (sliceMap g a) = w.V a)
    {η : (E → G) × (E → G) → ℝ} (mη : Measurable η) (bη : IsBdd η)
    (hη : ∫ U, (cA w (flip0 g U) - cA w U) * bdry η U * cB w U ∂(cHaar G E S T) ≠ 0) :
    cZtw (T := T) w g < cZ (T := T) w := by
  have : Nonempty G := ⟨1⟩
  have mg : ∀ e, Measurable (g e) := fun e => (hg e).measurable
  set F : CCfg G E S T → ℝ := fun U => cA w (flip0 g U) - cA w U with hFdef
  have hFd : CDep F CHalf := fun U V hUV => by
    simp only [hFdef]
    rw [cA_dep w hT U V hUV, cA_dep w hT _ _ (flip0_agree hUV)]
  have bF : IsBdd F := by
    obtain ⟨M, hM⟩ := cA_isBdd (T := T) w
    exact ⟨M + M, fun U => (norm_sub_le _ _).trans (add_le_add (hM _) (hM _))⟩
  have mF : Measurable F := ((measurable_cA w).comp (measurable_flip0 mg)).sub (measurable_cA w)
  have hΘ := isReflection_ctheta (G := G) (E := E) (S := S) hT
  let Adm : (CCfg G E S T → ℝ) → Prop := fun Φ => DepPos (csplit hT) Φ ∧ Measurable Φ ∧ IsBdd Φ
  have hAF : Adm F := ⟨depPos_of_cdep hT hFd, mF, bF⟩
  have hAH : Adm (bdry η) := ⟨bdry_depPos hT η, measurable_bdry mη, bη.comp _⟩
  have hcs := cs_of_rp ctheta (cB w) Adm (μ := cHaar G E S T)
    ⟨fun _ _ _ _ => rfl, measurable_zero, IsBdd.const 0⟩
    (fun F1 F2 hF hG => ⟨fun U V h0 h1 => by simp only [Pi.add_apply]; rw [hF.1 U V h0 h1, hG.1 U V h0 h1],
      hF.2.1.add hG.2.1, hF.2.2.add hG.2.2⟩)
    (fun t F1 hF => ⟨fun U V h0 h1 => by simp only [Pi.smul_apply]; rw [hF.1 U V h0 h1], hF.2.1.const_smul t,
      hF.2.2.const_mul t⟩)
    (fun F1 F2 hF hG => config_integrable (haarG G) measurePreserving_ctwist hΘ hG.1 hF.2.1 hG.2.1
      (measurable_cB w) hF.2.2 hG.2.2 (cB_isBdd w))
    (fun F1 hF => config_rp (haarG G) measurePreserving_ctwist hΘ hF.1 (cB_depFix w hT) hF.2.1 (measurable_cB w)
      hF.2.2 (cB_isBdd w) (cB_nonneg w))
    (fun F1 F2 hF hG => config_symm (haarG G) measurePreserving_ctwist hΘ hF.1 hG.1 (cB_depFix w hT) hF.2.1 hG.2.1
      (measurable_cB w) hF.2.2 hG.2.2 (cB_isBdd w))
    hAF hAH
  have hFF : 0 ≤ ∫ U, F U * F (ctheta U) * cB w U ∂(cHaar G E S T) :=
    config_rp (haarG G) measurePreserving_ctwist hΘ hAF.1 (cB_depFix w hT) mF (measurable_cB w) bF (cB_isBdd w)
      (cB_nonneg w)
  have hFH : ∫ U, F U * bdry η (ctheta U) * cB w U ∂(cHaar G E S T) =
      ∫ U, (cA w (flip0 g U) - cA w U) * bdry η U * cB w U ∂(cHaar G E S T) := by
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    simp only [bdry_ctheta hT, hFdef]
  rw [hFH] at hcs
  have hpos : 0 < ∫ U, F U * F (ctheta U) * cB w U ∂(cHaar G E S T) := by
    rcases hFF.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hcs
      exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hcs (sq_nonneg _)))
        (abs_ne_zero.2 hη)
    · exact h0
  have h2 := cZ_sub_cZtw_eq_u w g h hT hK hg hh hgh hV
  have h3 : ∫ U, F U * F (ctheta U) * cB w U ∂(cHaar G E S T) = 2 * (cZ (T := T) w - cZtw (T := T) w g) := h2.symm
  linarith

end UChain

/-! ## The difference sector and the strict bound from one transfer step -/

section USector

variable {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G] [MeasurableInv G]
  [(haarG G).IsInvInvariant] {E S : Type*} [Fintype E] [Fintype S] {T : ℕ} [NeZero T]
variable (w : ChainWeight G E S) (g h : E → G → G)

/-- **The charge of `φ` under the twist** `h`: the difference `φ∘h − φ` (for `Z_2` and `φ` odd this is `−2φ`). -/
def twDiff (φ : (E → G) → ℝ) (a : E → G) : ℝ := φ (sliceMap h a) - φ a

theorem bm_twDiff {φ : (E → G) → ℝ} (mh : ∀ e, Measurable (h e)) (hφ : BM φ) : BM (twDiff h φ) :=
  ⟨(hφ.1.comp (measurable_sliceMap mh)).sub hφ.1, ⟨_, fun a => (norm_sub_le _ _).trans
    (add_le_add (hφ.2.choose_spec _) (hφ.2.choose_spec _))⟩⟩

/-- **The boundary moment of a product observable** is the pairing of the difference sector:
`∫ (A∘σ_g − A) · φ(a₀) χ(a_{T/2}) · B = ⟨φ∘h − φ, 𝒦^{T/2} χ⟩_V`. -/
theorem moment_u (hT : Even T) (hg : ∀ e, Measurable (g e))
    (hh : ∀ e, MeasurePreserving (h e) (haarG G) (haarG G)) (hgh : ∀ e x, g e (h e x) = x)
    (hV : ∀ a, w.V (sliceMap g a) = w.V a) {φ χ : (E → G) → ℝ} (hφ : BM φ) (hχ : BM χ) :
    ∫ U, (cA w (flip0 g U) - cA w U) * bdry (fun p => φ p.1 * χ p.2) U * cB w U ∂(cHaar G E S T) =
      vip w (twDiff h φ) ((kop w)^[T / 2] χ) := by
  have mh : ∀ e, Measurable (h e) := fun e => (hh e).measurable
  have hmp := measurePreserving_flip0 (S := S) (T := T) hh
  set Φ : CCfg G E S T → ℝ := fun U => bdry (fun p => φ p.1 * χ p.2) U * cB w U with hΦdef
  have mΦ : Measurable Φ :=
    (measurable_bdry ((hφ.1.comp measurable_fst).mul (hχ.1.comp measurable_snd))).mul (measurable_cB w)
  have bΦ : IsBdd Φ := (((hφ.2.comp _).mul (hχ.2.comp _)).comp _).mul (cB_isBdd w)
  have mA := measurable_cA (T := T) w
  have bA := cA_isBdd (T := T) w
  have i1 : Integrable (fun U => cA w (flip0 g U) * Φ U) (cHaar G E S T) :=
    IsBdd.integrable ((bA.comp _).mul bΦ) ((mA.comp (measurable_flip0 hg)).mul mΦ).aestronglyMeasurable
  have i2 : Integrable (fun U => cA w U * Φ U) (cHaar G E S T) :=
    IsBdd.integrable (bA.mul bΦ) (mA.mul mΦ).aestronglyMeasurable
  have i3 : Integrable (fun U => cA w U * Φ (flip0 h U)) (cHaar G E S T) :=
    IsBdd.integrable (bA.mul (bΦ.comp _)) (mA.mul (mΦ.comp (measurable_flip0 mh))).aestronglyMeasurable
  have e1 : ∫ U, cA w (flip0 g U) * Φ U ∂(cHaar G E S T) = ∫ U, cA w U * Φ (flip0 h U) ∂(cHaar G E S T) := by
    rw [← integral_comp_of_measurePreserving hmp i1.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun U => ?_)
    simp only [flip0_flip0_of_left_inv hgh]
  have e0 : ∀ U, (cA w (flip0 g U) - cA w U) * bdry (fun p => φ p.1 * χ p.2) U * cB w U =
      cA w (flip0 g U) * Φ U - cA w U * Φ U := fun U => by simp only [hΦdef]; ring
  simp_rw [e0]
  rw [integral_sub i1 i2, e1, ← integral_sub i3 i2]
  have hd := half_chain w hT (bm_twDiff h mh hφ) hχ
  rw [← hd]
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only [hΦdef, bdry, twDiff]
  rw [sp_flip0_zero, sp_flip0_ne h U (halfT_ne_zero hT), cB_flip0 w h hT (V_sliceMap_of_left_inv hgh hV)]
  ring

/-- `j` transfer steps never connect the sector `P` to anything. -/
def SecVanish (P : ((E → G) → ℝ) → Prop) (j : ℕ) : Prop :=
  ∀ ψ χ : (E → G) → ℝ, BM ψ → BM χ → P ψ → vip w ψ ((kop w)^[j] χ) = 0

/-- **Descent** (self-adjointness), for any sector. -/
theorem secVanish_descend (P : ((E → G) → ℝ) → Prop) (j : ℕ) (hj : SecVanish w P (j + 2)) :
    SecVanish w P (j + 1) := by
  intro φ χ hφ hχ hP
  have hψ := bm_kop_iter w hφ (j + 1)
  have h0 : vip w ((kop w)^[j + 1] φ) ((kop w)^[j + 1] φ) = 0 := by
    rw [← vip_kop_iter w hφ hψ (j + 1), ← Function.iterate_add_apply,
      show j + 1 + (j + 1) = (j + 2) + j by ring, Function.iterate_add_apply]
    exact hj φ _ hφ (bm_kop_iter w hφ j) hP
  rw [vip_kop_iter w hφ hχ]
  exact vip_eq_zero_of_self w hψ h0 χ

theorem secVanish_one (P : ((E → G) → ℝ) → Prop) {n : ℕ} (hn : 1 ≤ n) (hP : SecVanish w P n) :
    SecVanish w P 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction k with
  | zero => exact hP
  | succ k ih => exact ih (secVanish_descend w P k hP)

/-- **The strict reflection bound from one transfer step, non-involutive twist** (every even `T`): if the one-step
transfer operator connects the charge `φ∘h − φ` of some bounded observable to some bounded `χ`,
`⟨φ∘h − φ, 𝒦 χ⟩_V ≠ 0`, then `Z_tw(g) < Z`. The hypothesis does not involve `T`. -/
theorem cZtw_lt_cZ_of_step_u (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c)
    (hg : ∀ e, MeasurePreserving (g e) (haarG G) (haarG G)) (hh : ∀ e, MeasurePreserving (h e) (haarG G) (haarG G))
    (hgh : ∀ e x, g e (h e x) = x) (hV : ∀ a, w.V (sliceMap g a) = w.V a) {φ χ : (E → G) → ℝ} (hφ : BM φ)
    (hχ : BM χ) (hne : vip w (twDiff h φ) (kop w χ) ≠ 0) : cZtw (T := T) w g < cZ (T := T) w := by
  have mh : ∀ e, Measurable (h e) := fun e => (hh e).measurable
  by_contra hlt
  let P : ((E → G) → ℝ) → Prop := fun ψ => ∃ φ', BM φ' ∧ ψ = twDiff h φ'
  have hS : SecVanish w P (T / 2) := by
    rintro ψ χ' - hχ' ⟨φ', hφ', rfl⟩
    by_contra hne'
    apply hlt
    refine cZtw_lt_cZ_of_moment_u w g h hT hK hg hh hgh hV (η := fun p => φ' p.1 * χ' p.2)
      ((hφ'.1.comp measurable_fst).mul (hχ'.1.comp measurable_snd)) ((hφ'.2.comp _).mul (hχ'.2.comp _)) ?_
    rw [moment_u w g h hT (fun e => (hg e).measurable) hh hgh hV hφ' hχ']
    exact hne'
  have h1 := secVanish_one w P (n := T / 2) (by have := two_le_of_even hT; omega) hS
  exact hne (h1 _ χ (bm_twDiff h mh hφ) hχ ⟨φ, hφ, rfl⟩)

end USector

/-! ## A cyclic family of twists: the electric sectors are reflection-positivity norms -/

section ZFamily

variable {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G] [MeasurableInv G]
  [(haarG G).IsInvInvariant] {E S : Type*} [Fintype E] [Fintype S] {T : ℕ} [NeZero T]
variable (w : ChainWeight G E S) {N : ℕ} [NeZero N]

/-- **A `Z_N` family of slice twists**: `g_k ∘ g_l = g_{k+l}`, `g_0 = id`, each measure preserving and `V`-invariant
(the centre `Z_N` of SU(N) acting on the twist plane). -/
structure ZFam (w : ChainWeight G E S) (N : ℕ) where
  /-- The twist by the `k`-th centre element. -/
  g : ZMod N → E → G → G
  comp : ∀ k l e x, g k e (g l e x) = g (k + l) e x
  zero : ∀ e x, g 0 e x = x
  mp : ∀ k e, MeasurePreserving (g k e) (haarG G) (haarG G)
  inv : ∀ k a, w.V (sliceMap (g k) a) = w.V a

variable {w}

theorem ZFam.flip0_comp (F : ZFam w N) (k l : ZMod N) (U : CCfg G E S T) :
    flip0 (F.g k) (flip0 (F.g l) U) = flip0 (F.g (k + l)) U := by
  funext x
  rcases x with ⟨t, e | s⟩
  · by_cases ht : t = 0
    · simp [flip0, ht, F.comp]
    · simp [flip0, ht]
  · rfl

theorem ZFam.left_inv (F : ZFam w N) (k : ZMod N) : ∀ e x, F.g k e (F.g (-k) e x) = x := by
  intro e x; rw [F.comp, add_neg_cancel, F.zero]

/-- The twisted partition functions `Z_k = Z_tw(g_k)`. -/
def ZFam.Zk (F : ZFam w N) (T : ℕ) [NeZero T] (k : ZMod N) : ℝ := cZtw (T := T) w (F.g k)

theorem ZFam.Zk_zero (F : ZFam w N) : F.Zk T 0 = cZ (T := T) w := by
  unfold ZFam.Zk cZtw cZ
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  unfold twWeight cweight
  refine prod_congr rfl fun t _ => ?_
  simp only [twStep, cstep]
  split_ifs
  · rw [show sliceMap (F.g 0) (sp U t) = sp U t from funext fun e => F.zero e _]
  · rfl

/-- **`Z_k = Z_{−k}`** (conjugation pairs `k` with `N − k`). -/
theorem ZFam.Zk_neg (F : ZFam w N) (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c) (k : ZMod N) :
    F.Zk T (-k) = F.Zk T k :=
  (cZtw_eq_inv w (F.g k) (F.g (-k)) hT hK (fun e => (F.mp k e).measurable) (F.mp (-k)) (F.left_inv k)
    (F.inv k)).symm

/-- **`Z_k ≤ Z`** for every `k`. -/
theorem ZFam.Zk_le (F : ZFam w N) (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c) (k : ZMod N) :
    F.Zk T k ≤ cZ (T := T) w :=
  cZtw_le_cZ_u w (F.g k) (F.g (-k)) hT hK (F.mp k) (F.mp (-k)) (F.left_inv k) (F.inv k)

/-- **The pairing of two twisted halves**: `∫ A(σ_k U) · A(σ_l Θ U) · B(U) = Z_{k−l}`. -/
theorem ZFam.integral_pair_eq (F : ZFam w N) (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c) (k l : ZMod N) :
    ∫ U, cA w (flip0 (F.g k) U) * cA w (flip0 (F.g l) (ctheta U)) * cB w U ∂(cHaar G E S T) = F.Zk T (k - l) := by
  have hmp := measurePreserving_flip0 (S := S) (T := T) (F.mp (-l))
  have mA := measurable_cA (T := T) w
  have mth := (measurePreserving_ctheta (G := G) (E := E) (S := S) (T := T)).measurable
  have mg : ∀ k, Measurable (flip0 (S := S) (T := T) (F.g k)) :=
    fun k => measurable_flip0 fun e => (F.mp k e).measurable
  have bA := cA_isBdd (T := T) w
  have i3 : Integrable (fun U => cA w (flip0 (F.g k) U) * cA w (flip0 (F.g l) (ctheta U)) * cB w U)
      (cHaar G E S T) :=
    IsBdd.integrable (((bA.comp _).mul (bA.comp _)).mul (cB_isBdd w))
      (((mA.comp (mg k)).mul (mA.comp ((mg l).comp mth))).mul (measurable_cB w)).aestronglyMeasurable
  rw [← integral_comp_of_measurePreserving hmp i3.aestronglyMeasurable]
  show _ = ∫ U, twWeight w (F.g (k - l)) U ∂(cHaar G E S T)
  refine integral_congr_ae (ae_of_all _ fun U => ?_)
  simp only []
  rw [ctheta_flip0, F.flip0_comp, F.flip0_comp, add_neg_cancel, cB_flip0 w _ hT (F.inv (-l)),
    twWeight_factor w _ hT hK, ← sub_eq_add_neg]
  have h0 : flip0 (F.g 0) (ctheta U) = ctheta U := by
    funext x
    rcases x with ⟨t, e | s⟩
    · by_cases ht : t = 0
      · simp [flip0, ht, F.zero]
      · simp [flip0, ht]
    · rfl
  rw [h0]

/-- The reflection form of a sum of twisted halves `f = Σ_k a_k A∘σ_k`: `⟨f, f⟩ = Σ_{k,l} a_k a_l Z_{k−l}`. -/
theorem ZFam.form_sum (F : ZFam w N) (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c) (a : ZMod N → ℝ) :
    ∫ U, (∑ k, a k * cA w (flip0 (F.g k) U)) * (∑ l, a l * cA w (flip0 (F.g l) (ctheta U))) * cB w U
        ∂(cHaar G E S T) = ∑ k, ∑ l, a k * a l * F.Zk T (k - l) := by
  have mA := measurable_cA (T := T) w
  have mth := (measurePreserving_ctheta (G := G) (E := E) (S := S) (T := T)).measurable
  have mg : ∀ k, Measurable (flip0 (S := S) (T := T) (F.g k)) :=
    fun k => measurable_flip0 fun e => (F.mp k e).measurable
  have bA := cA_isBdd (T := T) w
  have it : ∀ k l, Integrable (fun U => a k * a l * (cA w (flip0 (F.g k) U) * cA w (flip0 (F.g l) (ctheta U)) *
      cB w U)) (cHaar G E S T) := fun k l =>
    (IsBdd.integrable (((bA.comp _).mul (bA.comp _)).mul (cB_isBdd w))
      (((mA.comp (mg k)).mul (mA.comp ((mg l).comp mth))).mul (measurable_cB w)).aestronglyMeasurable).const_mul _
  have e : ∀ U : CCfg G E S T, (∑ k, a k * cA w (flip0 (F.g k) U)) * (∑ l, a l * cA w (flip0 (F.g l) (ctheta U))) * cB w U =
      ∑ k, ∑ l, a k * a l * (cA w (flip0 (F.g k) U) * cA w (flip0 (F.g l) (ctheta U)) * cB w U) := by
    intro U
    rw [sum_mul_sum, sum_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_mul]
    refine sum_congr rfl fun l _ => ?_
    ring
  simp_rw [e]
  rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => it k l]
  refine sum_congr rfl fun k _ => ?_
  rw [integral_finset_sum _ fun l _ => it k l]
  refine sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, F.integral_pair_eq hT hK]

/-- Reflection positivity for a sum of twisted halves: `Σ_{k,l} a_k a_l Z_{k−l} ≥ 0` (the matrix `Z_{k−l}` is
positive semidefinite). -/
theorem ZFam.form_sum_nonneg (F : ZFam w N) (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c) (a : ZMod N → ℝ) :
    0 ≤ ∑ k, ∑ l, a k * a l * F.Zk T (k - l) := by
  have : Nonempty G := ⟨1⟩
  rw [← F.form_sum hT hK a]
  have mg : ∀ k, Measurable (flip0 (S := S) (T := T) (F.g k)) :=
    fun k => measurable_flip0 fun e => (F.mp k e).measurable
  have bA := cA_isBdd (T := T) w
  obtain ⟨M, hM⟩ := bA
  refine config_rp (haarG G) measurePreserving_ctwist (isReflection_ctheta (G := G) (E := E) (S := S) hT)
    (F := fun U : CCfg G E S T => ∑ k, a k * cA w (flip0 (F.g k) U))
    (depPos_of_cdep hT fun U V hUV => by
      exact sum_congr rfl fun k _ => by rw [cA_dep w hT _ _ (flip0_agree hUV)]) (cB_depFix w hT)
    (Finset.measurable_sum _ fun k _ => measurable_const.mul ((measurable_cA w).comp (mg k))) (measurable_cB w)
    ⟨∑ k, |a k| * M, fun U => (norm_sum_le _ _).trans (sum_le_sum fun k _ => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _))⟩ (cB_isBdd w) (cB_nonneg w)

/-- **The electric sectors are reflection-positivity norms.** For every `e ∈ ZMod N`, with `𝓕Z(e) = Σ_k ψ(−k e) Z_k`
the discrete Fourier transform (`ψ` the standard additive character, `ψ(x) = e^{2πi x/N}`):
`N · Re 𝓕Z(e) = Σ_{k,l} (Re c_k Re c_l + Im c_k Im c_l) Z_{k−l} ≥ 0`, `c_k = ψ(−k e)`. -/
theorem ZFam.elec_nonneg (F : ZFam w N) (hT : Even T) (hK : ∀ a b c, 0 < w.K a b c) (e : ZMod N) :
    0 ≤ (∑ k, ZMod.stdAddChar (-(k * e)) * (F.Zk T k : ℂ)).re := by
  set c : ZMod N → ℂ := fun k => ZMod.stdAddChar (-(k * e)) with hc
  have h1 := F.form_sum_nonneg hT hK (fun k => (c k).re)
  have h2 := F.form_sum_nonneg hT hK (fun k => (c k).im)
  -- `Re c_k Re c_l + Im c_k Im c_l = Re (c_k conj c_l) = Re ψ(−(k − l) e)`
  have hcc : ∀ k l, (c k).re * (c l).re + (c k).im * (c l).im = (c (k - l)).re := by
    intro k l
    have : c (k - l) = c k * (starRingEnd ℂ) (c l) := by
      simp only [hc]
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
      congr 1; ring
    rw [this, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hsum : ∑ k, ∑ l, (c k).re * (c l).re * F.Zk T (k - l) + ∑ k, ∑ l, (c k).im * (c l).im * F.Zk T (k - l) =
      (N : ℝ) * (∑ d, c d * (F.Zk T d : ℂ)).re := by
    rw [← sum_add_distrib]
    simp_rw [← sum_add_distrib, ← add_mul, hcc]
    have hre : ∀ d, (c d).re * F.Zk T d = (c d * (F.Zk T d : ℂ)).re := fun d => by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    have hk : ∀ k : ZMod N, ∑ l, (c (k - l)).re * F.Zk T (k - l) = ∑ d, (c d).re * F.Zk T d := fun k =>
      Fintype.sum_equiv (Equiv.subLeft k) _ _ fun l => rfl
    simp_rw [hk, sum_const, card_univ, ZMod.card, nsmul_eq_mul, Complex.re_sum, hre]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have := add_nonneg h1 h2
  rw [hsum] at this
  exact (mul_nonneg_iff_of_pos_left hN).1 this

end ZFamily

end ProofPhase.General
