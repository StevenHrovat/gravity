/-
Proof phase, workstream 2 (Route B): anisotropic tori as time chains, reflection positivity, the Hankel identity
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/ws2-routeB/NOTE.md`, section 1.
-/

import ProofPhase.RouteB.HankelRate
import Positivity

/-!
# Anisotropic tori `ℤ/Tℤ × (spatial box)` as time chains: reflection positivity and the Hankel identity

The existing tori `LatticeLink d N` have one side length. A flux energy needs a **fixed spatial box and a time extent
`T → ∞`**. This file builds the anisotropic lattice directly, for an arbitrary finite spatial graph:

* **Links** `CLink E S T = ℤ/Tℤ × (E ⊕ S)`: `(t, inl e)` is the spatial link `e` of the time slice `t`, `(t, inr s)` the
  temporal link from `(t, s)` to `(t + 1, s)`. `E` = spatial links, `S` = spatial sites (any finite types).
* **Weight** (`ChainWeight`): `W(U) = ∏_t V(a_t) · K(a_t, b_t, a_{t+1})`, `a_t` the spatial links of slice `t`, `b_t` the
  temporal links leaving slice `t`. `V ≥ 0` collects the plaquettes inside a slice (it may be plaquette dependent: a
  magnetic twist enters here), `K ≥ 0` the plaquettes between two slices, with the reflection symmetry
  `K(c, b⁻¹, a) = K(a, b, c)`. For the Wilson action these are exactly the plaquettes of `ℤ/Tℤ × (spatial box)`
  (`ProofPhase.RouteB.FluxEnergy.su2Weight`).
* **Reflection** `Θ` through the slices `t = 0` and `t = T/2` (`T` even): `a_t ↦ a_{−t}`, `b_t ↦ b_{−t−1}⁻¹`.

Proved (all for every group with an inversion-invariant probability measure and every chain weight):
* `chain_rp`: **reflection positivity** `∫ F · (F ∘ Θ) · W ≥ 0` for bounded measurable `F` of the closed positive half
  (via `Positivity.config_rp`; the weight factorisation `cweight_factor` is the only lattice input).
* `cweight_cshift`, `measurePreserving_cshift`: time-translation invariance.
* `cform_slice`: **the Hankel identity** for slice observables, `⟨f(a_j), Θ f(a_k)⟩ = C(j + k)` with
  `C(t) = ∫ f(a_t) f(a_0) W`.
* `ccorr_cs`, `ccorr_nonneg`: Hankel Cauchy–Schwarz `C(j+k)² ≤ C(2j) C(2k)`, `C(2j) ≥ 0` for `j, k ≤ T/2`.
* `nCorr` (normalised by `Z = ∫ W`), its bound and Cauchy–Schwarz; the time family `T = 2(M+1)` (`corrSeq`), its limit
  points (`IsTimeLimit`, `exists_isTimeLimit`) and **`rpSeq_of_isTimeLimit`: every limit is an `RPSeq`**, so the
  effective-mass theory of `ProofPhase.RouteB.HankelRate` applies.

**Claim discipline.** Group-blind and model-blind (every compact group, every chain weight): reflection positivity and
its consequences, the structure of the problem, no physics content. What is new is the object: a lattice with a fixed
spatial box and an arbitrary even time extent, on which a flux energy can be defined from the 4D measure itself.
Osterwalder–Seiler (1978) for reflection positivity; formalisation ours.
-/

open MeasureTheory Finset Filter Topology Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.RouteB

/-! ## Links -/

section Geometry

variable {E S : Type*} {T : ℕ}

/-- Links of the chain lattice: `(t, inl e)` spatial link `e` of slice `t`; `(t, inr s)` temporal link at site `s`. -/
abbrev CLink (E S : Type*) (T : ℕ) := ZMod T × (E ⊕ S)

/-- Fixed links: spatial links of the slices `t = 0` and `t = T/2`. -/
def CFix : CLink E S T → Prop
  | (t, .inl _) => t.val = 0 ∨ t.val = T / 2
  | (_, .inr _) => False

/-- Positive links: spatial links with `0 < t < T/2`, temporal links leaving `t < T/2`. -/
def CPos : CLink E S T → Prop
  | (t, .inl _) => 0 < t.val ∧ t.val < T / 2
  | (t, .inr _) => t.val < T / 2

/-- The closed positive half. -/
def CHalf (l : CLink E S T) : Prop := CPos l ∨ CFix l

/-- The mirror image of a link: `t ↦ −t` for spatial links, `t ↦ −t − 1` for temporal ones. -/
def cmirror : CLink E S T → CLink E S T
  | (t, .inl e) => (-t, .inl e)
  | (t, .inr s) => (-t - 1, .inr s)

theorem cmirror_involutive : Function.Involutive (cmirror (E := E) (S := S) (T := T)) := by
  rintro ⟨t, e | s⟩
  · show ((-(-t) : ZMod T), (Sum.inl e : E ⊕ S)) = (t, Sum.inl e); rw [neg_neg]
  · show ((-(-t - 1) - 1 : ZMod T), (Sum.inr s : E ⊕ S)) = (t, Sum.inr s); congr 1; ring

variable [NeZero T]

theorem not_fix_of_pos {l : CLink E S T} (h : CPos l) : ¬CFix l := by
  rcases l with ⟨t, e | s⟩
  · simp only [CPos, CFix] at *; omega
  · simp [CFix]

theorem pos_mirror (hT : Even T) {l : CLink E S T} (h : CPos l) : ¬CFix (cmirror l) ∧ ¬CPos (cmirror l) := by
  obtain ⟨k, hk⟩ := hT
  rcases l with ⟨t, e | s⟩
  · have ht := ZMod.val_lt t
    simp only [CPos, CFix, cmirror, val_neg_eq] at h ⊢
    split_ifs <;> omega
  · have ht := ZMod.val_lt t
    simp only [CPos, CFix, cmirror, val_neg_sub_one, not_false_eq_true, true_and] at h ⊢
    omega

theorem neg_mirror (hT : Even T) {l : CLink E S T} (h1 : ¬CFix l) (h2 : ¬CPos l) : CPos (cmirror l) := by
  obtain ⟨k, hk⟩ := hT
  rcases l with ⟨t, e | s⟩
  · have ht := ZMod.val_lt t
    simp only [CPos, CFix, cmirror, val_neg_eq] at h1 h2 ⊢
    split_ifs <;> omega
  · have ht := ZMod.val_lt t
    simp only [CPos, cmirror, val_neg_sub_one] at h2 ⊢
    omega

theorem fixed_mirror (hT : Even T) {l : CLink E S T} (h : CFix l) : cmirror l = l := by
  rcases l with ⟨t, e | s⟩
  · simp only [CFix] at h
    show ((-t : ZMod T), (Sum.inl e : E ⊕ S)) = (t, Sum.inl e)
    rcases h with h | h
    · rw [(ZMod.val_eq_zero t).mp h, neg_zero]
    · rw [neg_eq_self_of_val_half hT t h]
  · exact h.elim

/-- Fixed links. -/
abbrev CFixL (E S : Type*) (T : ℕ) := {l : CLink E S T // CFix l}

/-- Positive links. -/
abbrev CPosL (E S : Type*) (T : ℕ) := {l : CLink E S T // CPos l}

/-- Fixed links, positive links and the mirrors of the positive links. -/
def csplitFun : CFixL E S T ⊕ (CPosL E S T ⊕ CPosL E S T) → CLink E S T :=
  Sum.elim Subtype.val (Sum.elim Subtype.val (fun x => cmirror x.1))

theorem csplitFun_bijective (hT : Even T) : Function.Bijective (csplitFun (E := E) (S := S) (T := T)) := by
  constructor
  · rintro (c | x | x) (c' | y | y) h <;> simp only [csplitFun, Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg _ (Subtype.ext h)
    · exact absurd c.2 (h ▸ not_fix_of_pos y.2)
    · exact absurd c.2 (h ▸ (pos_mirror hT y.2).1)
    · exact absurd c'.2 (h ▸ not_fix_of_pos x.2)
    · exact congrArg _ (congrArg _ (Subtype.ext h))
    · exact absurd x.2 (h ▸ (pos_mirror hT y.2).2)
    · exact absurd c'.2 (h.symm ▸ (pos_mirror hT x.2).1)
    · exact absurd y.2 (h.symm ▸ (pos_mirror hT x.2).2)
    · exact congrArg _ (congrArg _ (Subtype.ext (cmirror_involutive.injective h)))
  · intro l
    by_cases h1 : CFix l
    · exact ⟨.inl ⟨l, h1⟩, rfl⟩
    by_cases h2 : CPos l
    · exact ⟨.inr (.inl ⟨l, h2⟩), rfl⟩
    exact ⟨.inr (.inr ⟨cmirror l, neg_mirror hT h1 h2⟩), cmirror_involutive l⟩

/-- The links split as fixed ⊕ positive ⊕ mirror(positive). -/
def csplit (hT : Even T) : CFixL E S T ⊕ (CPosL E S T ⊕ CPosL E S T) ≃ CLink E S T :=
  Equiv.ofBijective _ (csplitFun_bijective hT)

end Geometry

/-! ## Configurations, reflection, time shift -/

section Conf

variable {G : Type*} [Group G] {E S : Type*} {T : ℕ}

/-- A configuration of the chain lattice. -/
abbrev CCfg (G E S : Type*) (T : ℕ) := CLink E S T → G

/-- The spatial links of slice `t`. -/
def sp (U : CCfg G E S T) (t : ZMod T) : E → G := fun e => U (t, .inl e)

/-- The temporal links leaving slice `t`. -/
def tm (U : CCfg G E S T) (t : ZMod T) : S → G := fun s => U (t, .inr s)

/-- The twist of the reflection: identity on spatial links, inversion on temporal ones. -/
def ctwist : CLink E S T → G → G
  | (_, .inl _) => id
  | (_, .inr _) => (·⁻¹)

/-- **The time reflection** `Θ`: `a_t ↦ a_{−t}`, `b_t ↦ b_{−t−1}⁻¹`. -/
def ctheta (U : CCfg G E S T) : CCfg G E S T := fun l => ctwist l (U (cmirror l))

theorem sp_ctheta (U : CCfg G E S T) (t : ZMod T) : sp (ctheta U) t = sp U (-t) := rfl

theorem tm_ctheta (U : CCfg G E S T) (t : ZMod T) : tm (ctheta U) t = fun s => (tm U (-t - 1) s)⁻¹ := rfl

/-- The time translation of links. -/
def cshiftL (j : ZMod T) (l : CLink E S T) : CLink E S T := (l.1 + j, l.2)

/-- The time translation of links as a permutation. -/
def cshiftEquiv (j : ZMod T) : CLink E S T ≃ CLink E S T where
  toFun := cshiftL j
  invFun := cshiftL (-j)
  left_inv l := by simp [cshiftL]
  right_inv l := by simp [cshiftL]

/-- **The time translation** `(S_j U)(t, x) = U(t + j, x)`. -/
def cshift (j : ZMod T) (U : CCfg G E S T) : CCfg G E S T := fun l => U (cshiftL j l)

theorem sp_cshift (j : ZMod T) (U : CCfg G E S T) (t : ZMod T) : sp (cshift j U) t = sp U (t + j) := rfl

theorem tm_cshift (j : ZMod T) (U : CCfg G E S T) (t : ZMod T) : tm (cshift j U) t = tm U (t + j) := rfl

theorem isReflection_ctheta [NeZero T] (hT : Even T) :
    IsReflection (csplit (E := E) (S := S) hT) (fun x => ctwist (G := G) x.1) ctheta where
  fix U c := by
    show ctwist c.1 (U (cmirror c.1)) = U c.1
    rw [fixed_mirror hT c.2]
    rcases c with ⟨⟨t, e | s⟩, hc⟩
    · rfl
    · exact hc.elim
  pos U x := rfl

variable [MeasurableSpace G]

theorem measurable_sp (t : ZMod T) : Measurable fun U : CCfg G E S T => sp U t :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

theorem measurable_tm (t : ZMod T) : Measurable fun U : CCfg G E S T => tm U t :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

variable [HasHaarProbability G] [Fintype E] [Fintype S] [NeZero T]

/-- The product Haar measure on configurations. -/
def cHaar (G E S : Type*) [MeasurableSpace G] [HasHaarProbability G] [Fintype E] [Fintype S] (T : ℕ) [NeZero T] :
    Measure (CCfg G E S T) :=
  Measure.pi fun _ : CLink E S T => haarG G

instance : IsProbabilityMeasure (cHaar G E S T) := by unfold cHaar; infer_instance

theorem measurePreserving_cshift (j : ZMod T) :
    MeasurePreserving (cshift (G := G) (E := E) (S := S) j) (cHaar G E S T) (cHaar G E S T) :=
  measurePreserving_reindex (haarG G) (cshiftEquiv j)

theorem measurePreserving_ctheta [MeasurableInv G] [(haarG G).IsInvInvariant] :
    MeasurePreserving (ctheta (G := G) (E := E) (S := S) (T := T)) (cHaar G E S T) (cHaar G E S T) := by
  have h1 := measurePreserving_reindex (haarG G)
    (Function.Involutive.toPerm _ (cmirror_involutive (E := E) (S := S) (T := T)))
  have h2 := measurePreserving_pi (fun _ : CLink E S T => haarG G) (fun _ => haarG G)
    (f := fun l => ctwist (G := G) l) (fun l => by
      rcases l with ⟨t, e | s⟩
      · exact MeasurePreserving.id _
      · exact Measure.measurePreserving_inv _)
  have h := h2.comp h1
  unfold cHaar
  convert h using 1
  funext U l
  rfl


end Conf

/-! ## Chain weights -/

/-- **A chain weight**: the plaquettes inside a slice (`V`) and between two slices (`K`), nonnegative, bounded,
measurable, with the reflection symmetry `K(c, b⁻¹, a) = K(a, b, c)`. -/
structure ChainWeight (G E S : Type*) [Group G] [MeasurableSpace G] where
  V : (E → G) → ℝ
  K : (E → G) → (S → G) → (E → G) → ℝ
  measV : Measurable V
  measK : Measurable fun p : (E → G) × (S → G) × (E → G) => K p.1 p.2.1 p.2.2
  V_nonneg : ∀ a, 0 ≤ V a
  K_nonneg : ∀ a b c, 0 ≤ K a b c
  V_bdd : ∃ M, ∀ a, V a ≤ M
  K_bdd : ∃ M, ∀ a b c, K a b c ≤ M
  K_symm : ∀ a b c, K c (fun s => (b s)⁻¹) a = K a b c

section Weight

variable {G : Type*} [Group G] [MeasurableSpace G] {E S : Type*} [Fintype E] [Fintype S] {T : ℕ} [NeZero T]
variable (w : ChainWeight G E S)

/-- One time step of the weight: `V(a_t) K(a_t, b_t, a_{t+1})`. -/
def cstep (U : CCfg G E S T) (t : ZMod T) : ℝ := w.V (sp U t) * w.K (sp U t) (tm U t) (sp U (t + 1))

/-- **The weight** `W(U) = ∏_t V(a_t) K(a_t, b_t, a_{t+1})`. -/
def cweight (U : CCfg G E S T) : ℝ := ∏ t, cstep w U t

theorem measurable_cstep (t : ZMod T) : Measurable fun U : CCfg G E S T => cstep w U t :=
  (w.measV.comp (measurable_sp t)).mul
    (w.measK.comp ((measurable_sp t).prodMk ((measurable_tm t).prodMk (measurable_sp (t + 1)))))

theorem measurable_cweight : Measurable (cweight (T := T) w) :=
  Finset.measurable_prod _ fun t _ => measurable_cstep w t

theorem cweight_nonneg (U : CCfg G E S T) : 0 ≤ cweight w U :=
  prod_nonneg fun t _ => mul_nonneg (w.V_nonneg _) (w.K_nonneg _ _ _)

theorem cweight_isBdd : IsBdd (cweight (T := T) w) := by
  obtain ⟨MV, hMV⟩ := w.V_bdd
  obtain ⟨MK, hMK⟩ := w.K_bdd
  refine IsBdd.prod _ fun t => ⟨MV * MK, fun U => ?_⟩
  show ‖cstep w U t‖ ≤ MV * MK
  unfold cstep
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (w.V_nonneg _) (w.K_nonneg _ _ _))]
  exact mul_le_mul (hMV _) (hMK _ _ _) (w.K_nonneg _ _ _) ((w.V_nonneg (sp U t)).trans (hMV (sp U t)))

/-- **Time-translation invariance of the weight.** -/
theorem cweight_cshift (j : ZMod T) (U : CCfg G E S T) : cweight w (cshift j U) = cweight w U := by
  unfold cweight
  have e : ∀ t, cstep w (cshift j U) t = cstep w U (t + j) := by
    intro t
    simp only [cstep, sp_cshift, tm_cshift]
    rw [show t + 1 + j = t + j + 1 by ring]
  simp_rw [e]
  exact Equiv.prod_comp (Equiv.addRight j) (fun t => cstep w U t)

/-- Times `0 < t < T/2`. -/
def tPos (T : ℕ) [NeZero T] : Finset (ZMod T) := univ.filter fun t => 0 < t.val ∧ t.val < T / 2

/-- Times `t < T/2`. -/
def tLow (T : ℕ) [NeZero T] : Finset (ZMod T) := univ.filter fun t => t.val < T / 2

/-- The fixed times `t ∈ {0, T/2}`. -/
def tFix (T : ℕ) [NeZero T] : Finset (ZMod T) := univ.filter fun t => t.val = 0 ∨ t.val = T / 2

/-- The weight of the open positive half. -/
def cA (U : CCfg G E S T) : ℝ :=
  (∏ t ∈ tPos T, w.V (sp U t)) * ∏ t ∈ tLow T, w.K (sp U t) (tm U t) (sp U (t + 1))

/-- The weight of the fixed slices. -/
def cB (U : CCfg G E S T) : ℝ := ∏ t ∈ tFix T, w.V (sp U t)

/-- **Factorisation of the weight**: `W(U) = A(U) · A(Θ U) · B(U)`. -/
theorem cweight_factor (hT : Even T) (U : CCfg G E S T) : cweight w U = cA w U * cA w (ctheta U) * cB w U := by
  obtain ⟨k, hk⟩ := hT
  unfold cweight cstep cA cB
  rw [prod_mul_distrib]
  -- the slice part
  have hV : ∏ t, w.V (sp U t) =
      (∏ t ∈ tPos T, w.V (sp U t)) * (∏ t ∈ tPos T, w.V (sp (ctheta U) t)) * ∏ t ∈ tFix T, w.V (sp U t) := by
    rw [← prod_filter_mul_prod_filter_not univ (fun t : ZMod T => 0 < t.val ∧ t.val < T / 2),
      ← prod_filter_mul_prod_filter_not (univ.filter fun t : ZMod T => ¬(0 < t.val ∧ t.val < T / 2))
        (fun t : ZMod T => t.val = 0 ∨ t.val = T / 2)]
    have hfix : (univ.filter fun t : ZMod T => ¬(0 < t.val ∧ t.val < T / 2)).filter
        (fun t : ZMod T => t.val = 0 ∨ t.val = T / 2) = tFix T := by
      ext t; simp only [tFix, mem_filter, mem_univ, true_and]; omega
    have hneg : ∏ t ∈ (univ.filter fun t : ZMod T => ¬(0 < t.val ∧ t.val < T / 2)).filter
        (fun t : ZMod T => ¬(t.val = 0 ∨ t.val = T / 2)), w.V (sp U t) =
        ∏ t ∈ tPos T, w.V (sp (ctheta U) t) := by
      refine prod_nbij' (fun t => -t) (fun t => -t) (fun t ht => ?_) (fun t ht => ?_) (fun t _ => neg_neg t)
        (fun t _ => neg_neg t) (fun t _ => ?_)
      · have := ZMod.val_lt t
        simp only [tPos, mem_filter, mem_univ, true_and, val_neg_eq] at ht ⊢
        split_ifs <;> omega
      · have := ZMod.val_lt t
        simp only [tPos, mem_filter, mem_univ, true_and, val_neg_eq] at ht ⊢
        split_ifs <;> omega
      · rw [sp_ctheta, neg_neg]
    rw [hfix, hneg, tPos]
    ring
  -- the step part
  have hK : ∏ t, w.K (sp U t) (tm U t) (sp U (t + 1)) =
      (∏ t ∈ tLow T, w.K (sp U t) (tm U t) (sp U (t + 1))) *
        ∏ t ∈ tLow T, w.K (sp (ctheta U) t) (tm (ctheta U) t) (sp (ctheta U) (t + 1)) := by
    rw [← prod_filter_mul_prod_filter_not univ (fun t : ZMod T => t.val < T / 2)]
    congr 1
    refine prod_nbij' (fun t => -t - 1) (fun t => -t - 1) (fun t ht => ?_) (fun t ht => ?_)
      (fun t _ => by ring) (fun t _ => by ring) (fun t _ => ?_)
    · have := ZMod.val_lt t
      simp only [tLow, mem_filter, mem_univ, true_and, val_neg_sub_one] at ht ⊢
      omega
    · have := ZMod.val_lt t
      simp only [tLow, mem_filter, mem_univ, true_and, val_neg_sub_one] at ht ⊢
      omega
    · have e1 : -(-t - 1) = t + 1 := by ring
      have e2 : -(-t - 1 + 1) = t := by ring
      have e3 : -(-t - 1) - 1 = t := by ring
      have e4 : t + 1 - 1 = t := by ring
      simp only [sp_ctheta, tm_ctheta, e1, e2, e4]
      exact (w.K_symm _ _ _).symm
  rw [hV, hK, tLow]
  ring

/-! ## Dependence on the halves -/

/-- `F` depends only on the links in `P`. -/
def CDep {α : Type*} (F : CCfg G E S T → α) (P : CLink E S T → Prop) : Prop :=
  ∀ U V : CCfg G E S T, (∀ l, P l → U l = V l) → F U = F V

theorem depPos_of_cdep (hT : Even T) {α : Type*} {F : CCfg G E S T → α} (hF : CDep F CHalf) :
    DepPos (csplit (E := E) (S := S) hT) F := by
  intro U V h0 h1
  apply hF
  intro l hl
  rcases hl with hp | hf
  · exact h1 ⟨l, hp⟩
  · exact h0 ⟨l, hf⟩

theorem sp_eq_of_half {U V : CCfg G E S T} (h : ∀ l, CHalf l → U l = V l) {t : ZMod T} (ht : t.val ≤ T / 2) :
    sp U t = sp V t := by
  funext e
  apply h
  show CPos (t, Sum.inl e) ∨ CFix (t, Sum.inl e)
  simp only [CPos, CFix]
  omega

theorem cA_dep (hT : Even T) : CDep (cA (T := T) w) CHalf := by
  obtain ⟨k, hk⟩ := hT
  intro U V h
  unfold cA
  congr 1
  · refine prod_congr rfl fun t ht => ?_
    simp only [tPos, mem_filter, mem_univ, true_and] at ht
    rw [sp_eq_of_half h (by omega)]
  · refine prod_congr rfl fun t ht => ?_
    simp only [tLow, mem_filter, mem_univ, true_and] at ht
    have h1 : (t + 1).val = t.val + 1 := val_add_one_of_lt t (by omega)
    have htm : tm U t = tm V t := by
      funext s; apply h; show CPos (t, Sum.inr s) ∨ CFix (t, Sum.inr s); left; exact ht
    rw [sp_eq_of_half h (by omega), sp_eq_of_half h (t := t + 1) (by omega), htm]

theorem cB_depFix (hT : Even T) : DepFix (csplit (E := E) (S := S) hT) (cB (G := G) (T := T) w) := by
  intro U V h0
  unfold cB
  refine prod_congr rfl fun t ht => ?_
  simp only [tFix, mem_filter, mem_univ, true_and] at ht
  congr 1
  funext e
  exact h0 ⟨(t, Sum.inl e), ht⟩

theorem measurable_cA : Measurable (cA (T := T) w) :=
  (Finset.measurable_prod _ fun t _ => w.measV.comp (measurable_sp t)).mul
    (Finset.measurable_prod _ fun t _ =>
      w.measK.comp ((measurable_sp t).prodMk ((measurable_tm t).prodMk (measurable_sp (t + 1)))))

theorem measurable_cB : Measurable (cB (T := T) w) :=
  Finset.measurable_prod _ fun t _ => w.measV.comp (measurable_sp t)

theorem cA_isBdd : IsBdd (cA (T := T) w) := by
  obtain ⟨MV, hMV⟩ := w.V_bdd
  obtain ⟨MK, hMK⟩ := w.K_bdd
  refine IsBdd.mul (IsBdd.prod _ fun t => ⟨MV, fun U => ?_⟩) (IsBdd.prod _ fun t => ⟨MK, fun U => ?_⟩)
  · rw [Real.norm_eq_abs, abs_of_nonneg (w.V_nonneg _)]; exact hMV _
  · rw [Real.norm_eq_abs, abs_of_nonneg (w.K_nonneg _ _ _)]; exact hMK _ _ _

theorem cB_isBdd : IsBdd (cB (T := T) w) := by
  obtain ⟨MV, hMV⟩ := w.V_bdd
  refine IsBdd.prod _ fun t => ⟨MV, fun U => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (w.V_nonneg _)]; exact hMV _

theorem cB_nonneg (U : CCfg G E S T) : 0 ≤ cB w U := prod_nonneg fun t _ => w.V_nonneg _

/-! ## Reflection positivity -/

variable [HasHaarProbability G] [MeasurableInv G] [(haarG G).IsInvInvariant]

/-- **Reflection positivity of every chain weight** (site reflection through `t = 0`, `T/2`). -/
theorem chain_rp (hT : Even T) {F : CCfg G E S T → ℝ} (hF : CDep F CHalf) (mF : Measurable F) (bF : IsBdd F) :
    0 ≤ ∫ U, F U * F (ctheta U) * cweight w U ∂(cHaar G E S T) := by
  have : Nonempty G := ⟨1⟩
  have e : ∀ U, F U * F (ctheta U) * cweight w U =
      (F U * cA w U) * ((fun V => F V * cA w V) (ctheta U)) * cB w U := by
    intro U; rw [cweight_factor w hT]; ring
  simp_rw [e]
  have hFA : CDep (fun V => F V * cA w V) CHalf := fun U V h => by
    simp only []; rw [hF U V h, cA_dep w hT U V h]
  exact config_rp (haarG G) (fun x => by
      rcases x with ⟨⟨t, e | s⟩, hx⟩
      · exact MeasurePreserving.id _
      · exact Measure.measurePreserving_inv _)
    (isReflection_ctheta hT) (depPos_of_cdep hT hFA) (cB_depFix w hT) (mF.mul (measurable_cA w))
    (measurable_cB w) (bF.mul (cA_isBdd w)) (cB_isBdd w) (cB_nonneg w)

/-- The reflected form. -/
def cform (F F' : CCfg G E S T → ℝ) : ℝ := ∫ U, F U * F' (ctheta U) * cweight w U ∂(cHaar G E S T)

/-- **The slice correlation** `C(t) = ∫ f(a_t) f(a_0) W` (unnormalised). -/
def ccorr (f : (E → G) → ℝ) (t : ℕ) : ℝ := ∫ U, f (sp U (t : ZMod T)) * f (sp U 0) * cweight w U ∂(cHaar G E S T)

/-- **The Hankel identity**: `⟨f(a_j), Θ f(a_k)⟩ = C(j + k)`. -/
theorem cform_slice {f : (E → G) → ℝ} (mf : Measurable f) (j k : ℕ) :
    cform w (fun U => f (sp U (j : ZMod T))) (fun U => f (sp U (k : ZMod T))) = ccorr (T := T) w f (j + k) := by
  unfold cform ccorr
  set g : CCfg G E S T → ℝ := fun U => f (sp U ((j + k : ℕ) : ZMod T)) * f (sp U 0) * cweight w U with hg
  have mg : Measurable g :=
    ((mf.comp (measurable_sp _)).mul (mf.comp (measurable_sp _))).mul (measurable_cweight w)
  have hpt : ∀ U, f (sp U (j : ZMod T)) * f (sp (ctheta U) (k : ZMod T)) * cweight w U =
      g (cshift (-(k : ZMod T)) U) := by
    intro U
    simp only [hg, sp_cshift, sp_ctheta, cweight_cshift]
    congr 3
    · push_cast; ring
    · ring
  simp_rw [hpt]
  exact integral_comp_of_measurePreserving (measurePreserving_cshift _) mg.aestronglyMeasurable

/-- The admissible observables: bounded measurable functions of the closed positive half. -/
def CAdm (F : CCfg G E S T → ℝ) : Prop := CDep F CHalf ∧ Measurable F ∧ IsBdd F

theorem slice_cAdm {f : (E → G) → ℝ} (mf : Measurable f) (bf : IsBdd f) {j : ℕ} (hj : j ≤ T / 2) :
    CAdm (fun U : CCfg G E S T => f (sp U (j : ZMod T))) := by
  have hT0 : 0 < T := Nat.pos_of_ne_zero (NeZero.ne T)
  have hjv : (j : ZMod T).val = j := ZMod.val_cast_of_lt (by omega)
  refine ⟨fun U V h => ?_, mf.comp (measurable_sp _), bf.comp _⟩
  simp only []
  rw [sp_eq_of_half h (by rw [hjv]; exact hj)]

theorem cform_integrable {F F' : CCfg G E S T → ℝ} (hF : CAdm F) (hF' : CAdm F') :
    Integrable (fun U => F U * F' (ctheta U) * cweight w U) (cHaar G E S T) :=
  IsBdd.integrable ((hF.2.2.mul (hF'.2.2.comp _)).mul (cweight_isBdd w))
    ((hF.2.1.mul (hF'.2.1.comp measurePreserving_ctheta.measurable)).mul
      (measurable_cweight w)).aestronglyMeasurable

/-- **Hankel Cauchy–Schwarz** for slice correlations: `C(j+k)² ≤ C(2j) C(2k)` and `C(2j) ≥ 0` for `j, k ≤ T/2`. -/
theorem ccorr_cs (hT : Even T) {f : (E → G) → ℝ} (mf : Measurable f) (bf : IsBdd f) {j k : ℕ}
    (hj : j ≤ T / 2) (hk : k ≤ T / 2) : ccorr (T := T) w f (j + k) ^ 2 ≤ ccorr (T := T) w f (2 * j) * ccorr (T := T) w f (2 * k) := by
  have hq : ∀ x : ℝ, 0 ≤ ccorr (T := T) w f (2 * j) * (x * x) + 2 * ccorr (T := T) w f (j + k) * x + ccorr (T := T) w f (2 * k) := by
    intro x
    have h := gram_of_rp (μ := cHaar G E S T) ctheta (cweight w) CAdm
      ⟨fun _ _ _ => rfl, measurable_const, IsBdd.const 0⟩
      (fun F F' hF hF' => ⟨fun U V h => by simp only [Pi.add_apply]; rw [hF.1 U V h, hF'.1 U V h],
        hF.2.1.add hF'.2.1, hF.2.2.add hF'.2.2⟩)
      (fun t F hF => ⟨fun U V h => by simp only [Pi.smul_apply]; rw [hF.1 U V h], hF.2.1.const_smul t,
        hF.2.2.const_mul t⟩)
      (fun F F' hF hF' => cform_integrable w hF hF')
      (fun F hF => chain_rp w hT hF.1 hF.2.1 hF.2.2)
      (univ : Finset (Fin 2)) ![fun U => f (sp U (j : ZMod T)), fun U => f (sp U (k : ZMod T))]
      (by intro i _; fin_cases i
          · exact slice_cAdm mf bf hj
          · exact slice_cAdm mf bf hk) ![x, 1]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have e1 := cform_slice w (T := T) mf j j
    have e2 := cform_slice w (T := T) mf j k
    have e3 := cform_slice w (T := T) mf k j
    have e4 := cform_slice w (T := T) mf k k
    unfold cform at e1 e2 e3 e4
    rw [e1, e2, e3, e4, add_comm k j, ← two_mul, ← two_mul] at h
    nlinarith [h]
  have := sq_le_mul_of_quadratic_nonneg hq
  linarith [mul_comm (ccorr (T := T) w f (2 * k)) (ccorr (T := T) w f (2 * j))]

theorem ccorr_nonneg (hT : Even T) {f : (E → G) → ℝ} (mf : Measurable f) (bf : IsBdd f) {j : ℕ}
    (hj : j ≤ T / 2) : 0 ≤ ccorr (T := T) w f (2 * j) := by
  have h := chain_rp w hT (slice_cAdm mf bf hj).1 (slice_cAdm mf bf hj).2.1 (slice_cAdm mf bf hj).2.2
  have e := cform_slice w (T := T) mf j j
  unfold cform at e
  rwa [e, ← two_mul] at h

/-! ## Normalisation -/

/-- The partition function `Z = ∫ W`. -/
def cZ : ℝ := ∫ U, cweight w U ∂(cHaar G E S T)

theorem cZ_nonneg : 0 ≤ cZ (T := T) w := integral_nonneg fun U => cweight_nonneg w U

/-- **The normalised slice correlation** `⟨f(a_t) f(a_0)⟩ = C(t)/Z`. -/
def nCorr (f : (E → G) → ℝ) (t : ℕ) : ℝ := ccorr (T := T) w f t / cZ (T := T) w

theorem abs_ccorr_le {f : (E → G) → ℝ} (mf : Measurable f) {M : ℝ} (hM : ∀ a, |f a| ≤ M) (t : ℕ) :
    |ccorr (T := T) w f t| ≤ M ^ 2 * cZ (T := T) w := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (fun _ => 1))
  unfold ccorr cZ
  rw [← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (Eventually.of_forall fun U => abs_nonneg _)
    ((IsBdd.integrable (cweight_isBdd w) (measurable_cweight w).aestronglyMeasurable).const_mul _)
    (Eventually.of_forall fun U => ?_))
  dsimp only
  rw [abs_mul, abs_mul, abs_of_nonneg (cweight_nonneg w U), sq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul (hM _) (hM _) (abs_nonneg _) hM0) (cweight_nonneg w U)

theorem abs_nCorr_le {f : (E → G) → ℝ} (mf : Measurable f) {M : ℝ} (hM : ∀ a, |f a| ≤ M) (t : ℕ) :
    |nCorr (T := T) w f t| ≤ M ^ 2 := by
  unfold nCorr
  rcases (cZ_nonneg (T := T) w).eq_or_lt with h | h
  · rw [← h, div_zero, abs_zero]; exact sq_nonneg _
  · rw [abs_div, abs_of_pos h, div_le_iff₀ h]; exact abs_ccorr_le w mf hM t

theorem nCorr_cs (hT : Even T) {f : (E → G) → ℝ} (mf : Measurable f) (bf : IsBdd f) {j k : ℕ}
    (hj : j ≤ T / 2) (hk : k ≤ T / 2) :
    nCorr (T := T) w f (j + k) ^ 2 ≤ nCorr (T := T) w f (2 * j) * nCorr (T := T) w f (2 * k) := by
  unfold nCorr
  rw [div_pow, div_mul_div_comm, ← sq]
  exact div_le_div_of_nonneg_right (ccorr_cs w hT mf bf hj hk) (sq_nonneg _)

theorem nCorr_nonneg (hT : Even T) {f : (E → G) → ℝ} (mf : Measurable f) (bf : IsBdd f) {j : ℕ}
    (hj : j ≤ T / 2) : 0 ≤ nCorr (T := T) w f (2 * j) :=
  div_nonneg (ccorr_nonneg w hT mf bf hj) (cZ_nonneg w)

end Weight

/-! ## The time extent to infinity -/

/-- The time extents `T_M = 2(M + 1)`. -/
def chainT (M : ℕ) : ℕ := 2 * (M + 1)

instance (M : ℕ) : NeZero (chainT M) := ⟨by unfold chainT; omega⟩

theorem even_chainT (M : ℕ) : Even (chainT M) := by unfold chainT; exact even_two_mul _

theorem chainT_half (M : ℕ) : chainT M / 2 = M + 1 := by unfold chainT; omega

section Limit

variable {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G] [MeasurableInv G]
  [(haarG G).IsInvInvariant] {E S : Type*} [Fintype E] [Fintype S] (w : ChainWeight G E S)

/-- The normalised slice correlation at time extent `T_M`. -/
def corrSeq (f : (E → G) → ℝ) (M t : ℕ) : ℝ := nCorr (T := chainT M) w f t

/-- **`h` is a time limit** of the slice correlation of `f`: the pointwise limit along a subsequence of time extents
`T_M → ∞`, at fixed spatial box and weight. -/
def IsTimeLimit (f : (E → G) → ℝ) (h : ℕ → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ t, Tendsto (fun M => corrSeq w f (φ M) t) atTop (𝓝 (h t))

/-- **Time limits exist** for every bounded measurable slice observable. -/
theorem exists_isTimeLimit {f : (E → G) → ℝ} (mf : Measurable f) {M : ℝ} (hM : ∀ a, |f a| ≤ M) :
    ∃ h, IsTimeLimit w f h := by
  obtain ⟨φ, hφ, h, ht⟩ := exists_limit (H := corrSeq w f) (C := M ^ 2) fun n t => abs_nCorr_le (T := chainT n) w mf hM t
  exact ⟨h, φ, hφ, ht⟩

/-- **Every time limit is a reflection-positive Hankel sequence**, so `HankelRate` applies: effective masses decrease
to a rate `E ≥ 0` and `|h(t)| ≤ h(0) e^{−E t}` (or `h` vanishes from some even time on). -/
theorem rpSeq_of_isTimeLimit {f : (E → G) → ℝ} (mf : Measurable f) {M : ℝ} (hM : ∀ a, |f a| ≤ M) {h : ℕ → ℝ}
    (hh : IsTimeLimit w f h) : RPSeq h := by
  obtain ⟨φ, hφ, ht⟩ := hh
  have bf : IsBdd f := ⟨M, fun a => by rw [Real.norm_eq_abs]; exact hM a⟩
  have hK : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  refine rpSeq_of_limit (H := corrSeq w f) (K := fun n => n + 1) hK (C := M ^ 2) (fun n j k hj hk => ?_)
    (fun n j hj => ?_) (fun n t => abs_nCorr_le (T := chainT n) w mf hM t) hφ ht
  · exact nCorr_cs (T := chainT n) w (even_chainT n) mf bf (by rw [chainT_half]; exact hj)
      (by rw [chainT_half]; exact hk)
  · exact nCorr_nonneg (T := chainT n) w (even_chainT n) mf bf (by rw [chainT_half]; exact hj)

end Limit

end ProofPhase.RouteB
