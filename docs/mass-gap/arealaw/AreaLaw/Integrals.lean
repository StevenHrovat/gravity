/-
The measure layer of the area law (BLUEPRINT.md, P1, P2, P4, P6). Area-law project, 2026-11-21. Released under Apache 2.0.

With g(x) = e^{βx} − 1, the Wilson weight ∏_p e^{β x_p} is ∑_{X ⊆ P} ∏_{p ∈ X} g(x_p). This file defines the integrals
I(X) = ∫ ∏_X g dμ and I_C(X) = ∫ W_C ∏_X g dμ and proves: the expansion of numerator and denominator into these (`integral_expand`);
factorisation over link-disjoint sets (`I_union`, `IC_union`); the bounds |I(X)| ≤ ε^|X| and |I_C(X)| ≤ n ε^|X| with
ε = e^{nβ} − 1 (`abs_I_le`, `abs_IC_le`); and the parity vanishing: I_C(X) = 0 unless some O ⊆ X forms, together with C, a closed
surface mod 2 (`IC_eq_zero_of_no_parity`).
-/

import AreaLaw.Expansion

open MeasureTheory ProbabilityTheory Real

noncomputable section

variable {G : Type*} [Group G] {d N : ℕ}

/-! ## Dependence on a set of links, and factorisation -/

/-- `F` depends only on the links in `S`. -/
def LinkDep {α : Type*} (F : GaugeConnection G d N → α) (S : Finset (LatticeLink d N)) : Prop :=
  ∀ U V : GaugeConnection G d N, (∀ l ∈ S, U l = V l) → F U = F V

theorem LinkDep.mono {α : Type*} {F : GaugeConnection G d N → α} {S T : Finset (LatticeLink d N)} (h : LinkDep F S)
    (hST : S ⊆ T) : LinkDep F T := fun U V hUV => h U V (fun l hl => hUV l (hST hl))

theorem LinkDep.mul {F F' : GaugeConnection G d N → ℝ} {S T : Finset (LatticeLink d N)} [DecidableEq (LatticeLink d N)]
    (h : LinkDep F S) (h' : LinkDep F' T) : LinkDep (fun U => F U * F' U) (S ∪ T) := fun U V hUV => by
  have e1 : F U = F V := h U V (fun l hl => hUV l (Finset.mem_union_left _ hl))
  have e2 : F' U = F' V := h' U V (fun l hl => hUV l (Finset.mem_union_right _ hl))
  simp only [e1, e2]

theorem LinkDep.prod {ι : Type*} [DecidableEq (LatticeLink d N)] (s : Finset ι) (F : ι → GaugeConnection G d N → ℝ)
    (S : ι → Finset (LatticeLink d N)) (h : ∀ i ∈ s, LinkDep (F i) (S i)) :
    LinkDep (fun U => ∏ i ∈ s, F i U) (s.biUnion S) := fun U V hUV => by
  apply Finset.prod_congr rfl
  intro i hi
  exact h i hi U V (fun l hl => hUV l (Finset.mem_biUnion.mpr ⟨i, hi, hl⟩))

section Factor

variable [MeasurableSpace G] [HasHaarProbability G] [Fintype (LatticeLink d N)] [DecidableEq (LatticeLink d N)]

/-- Extend a configuration on `S` by the identity elsewhere. -/
def extendOne (S : Finset (LatticeLink d N)) (u : S → G) : GaugeConnection G d N :=
  fun l => if h : l ∈ S then u ⟨l, h⟩ else 1

theorem measurable_extendOne (S : Finset (LatticeLink d N)) : Measurable (extendOne (G := G) S) := by
  apply measurable_pi_iff.mpr
  intro l
  by_cases h : l ∈ S
  · simp only [extendOne, h, dite_true]; exact measurable_pi_apply _
  · simp only [extendOne, h, dite_false]; exact measurable_const

theorem measurable_restrict' (S : Finset (LatticeLink d N)) :
    Measurable (fun (U : GaugeConnection G d N) (i : S) => U i) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply (i : LatticeLink d N))

theorem LinkDep.comp_eq {F : GaugeConnection G d N → ℝ} {S : Finset (LatticeLink d N)} (h : LinkDep F S) :
    (fun U => F (extendOne S (fun i : S => U i))) = F := by
  funext U
  apply h
  intro l hl
  simp [extendOne, hl]

/-- **Factorisation.** Measurable functions of disjoint sets of links are independent under the product measure, so the integral of
    their product is the product of their integrals. -/
theorem integral_mul_of_disjoint {F F' : GaugeConnection G d N → ℝ} {S T : Finset (LatticeLink d N)}
    (hF : LinkDep F S) (hF' : LinkDep F' T) (hST : Disjoint S T) (mF : Measurable F) (mF' : Measurable F') :
    ∫ U, F U * F' U ∂(productHaar G d N) = (∫ U, F U ∂(productHaar G d N)) * ∫ U, F' U ∂(productHaar G d N) := by
  have hind : iIndepFun (fun (l : LatticeLink d N) (U : GaugeConnection G d N) => U l) (productHaar G d N) :=
    iIndepFun_pi (μ := fun _ : LatticeLink d N => haarG G) (X := fun _ (g : G) => g) (fun _ => measurable_id.aemeasurable)
  have h2 := hind.indepFun_finset S T hST (fun l => measurable_pi_apply l)
  have mφ : Measurable (F ∘ extendOne S) := mF.comp (measurable_extendOne S)
  have mψ : Measurable (F' ∘ extendOne T) := mF'.comp (measurable_extendOne T)
  have h3 := h2.comp mφ mψ
  have := h3.integral_fun_mul_eq_mul_integral (mφ.comp (measurable_restrict' S)).aestronglyMeasurable
    (mψ.comp (measurable_restrict' T)).aestronglyMeasurable
  simp only [Function.comp] at this
  have h1 : ∀ U : GaugeConnection G d N, F (extendOne S (fun i : S => U i)) = F U := fun U => congrFun hF.comp_eq U
  have h2 : ∀ U : GaugeConnection G d N, F' (extendOne T (fun i : T => U i)) = F' U := fun U => congrFun hF'.comp_eq U
  simp only [h1, h2] at this
  exact this

end Factor

/-! ## Links of plaquettes and loops -/

variable [DecidableEq (LatticeLink d N)]

/-- The four links of a plaquette. -/
def plaqLinks (p : LatticePlaquette d N) : Finset (LatticeLink d N) := Finset.univ.image p.boundaryLinks

/-- The links of a set of plaquettes. -/
def linksOf (X : Finset (LatticePlaquette d N)) : Finset (LatticeLink d N) := X.biUnion plaqLinks

/-- The links a path visits. -/
def pathLinks (C : List (PathStep d N)) : Finset (LatticeLink d N) := (C.map PathStep.link).toFinset

theorem plaquetteHolonomy_dependsOn (p : LatticePlaquette d N) :
    LinkDep (G := G) (fun U => plaquetteHolonomy U p) (plaqLinks p) := fun U V h => by
  have hl : ∀ i : Fin 4, U (p.boundaryLinks i) = V (p.boundaryLinks i) :=
    fun i => h _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  simp only [plaquetteHolonomy, hl]

theorem pathHol_dependsOn (C : List (PathStep d N)) : LinkDep (G := G) (fun U => pathHol U C) (pathLinks C) := by
  induction C with
  | nil => intro U V _; rfl
  | cons s rest ih =>
    intro U V h
    have hs : U s.link = V s.link := h _ (by simp [pathLinks])
    have hr : pathHol U rest = pathHol V rest := ih U V (fun l hl => h l (by simp [pathLinks] at hl ⊢; exact Or.inr hl))
    simp only [pathHol, PathStep.hol, hs, hr]

/-! ## The integrals and their expansion -/

variable {n : ℕ} [HasGaugeTrace G n]

/-- The plaquette variable x_p(U) = Re tr U_p. -/
def xp (n : ℕ) [HasGaugeTrace G n] (p : LatticePlaquette d N) (U : GaugeConnection G d N) : ℝ :=
  gaugeReTr G n (plaquetteHolonomy U p)

/-- g(x) = e^{βx} − 1 and its centre-even and centre-odd parts. -/
def gfun (β x : ℝ) : ℝ := exp (β * x) - 1
def gplus (β x : ℝ) : ℝ := cosh (β * x) - 1
def gminus (β x : ℝ) : ℝ := sinh (β * x)

theorem gfun_eq (β x : ℝ) : gfun β x = gminus β x + gplus β x := by
  simp only [gfun, gplus, gminus]; rw [← cosh_add_sinh]; ring

theorem one_add_gfun (β x : ℝ) : 1 + gfun β x = exp (β * x) := by simp [gfun]

section Integrals

variable [MeasurableSpace G] [HasHaarProbability G] [Fintype (LatticeLink d N)]

instance : IsProbabilityMeasure (productHaar G d N) := by unfold productHaar; infer_instance

/-- I(X) = ∫ ∏_{p ∈ X} g(x_p). -/
def Iint (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (X : Finset (LatticePlaquette d N)) : ℝ :=
  ∫ U, ∏ p ∈ X, gfun β (xp n p U) ∂(productHaar G d N)

/-- I_C(X) = ∫ W_C ∏_{p ∈ X} g(x_p). -/
def ICint (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (C : List (PathStep d N)) (X : Finset (LatticePlaquette d N)) : ℝ :=
  ∫ U, wilsonLoop n C U * ∏ p ∈ X, gfun β (xp n p U) ∂(productHaar G d N)

variable (hbd : ∀ g : G, |gaugeReTr G n g| ≤ n)
variable (hmeas : ∀ p : LatticePlaquette d N, Measurable (xp (G := G) n p))

/-- ε = e^{nβ} − 1 bounds |g|, |g⁺|, |g⁻| on [−n, n] for β ≥ 0. -/
theorem abs_gfun_le {β x : ℝ} (hβ : 0 ≤ β) (hx : |x| ≤ n) : |gfun β x| ≤ exp (n * β) - 1 := by
  have h1 : β * x ≤ n * β := by nlinarith [le_abs_self x]
  have h2 : -(n * β) ≤ β * x := by nlinarith [neg_abs_le x]
  have e1 : exp (β * x) ≤ exp (n * β) := exp_le_exp.mpr h1
  have e2 : exp (-(n * β)) ≤ exp (β * x) := exp_le_exp.mpr h2
  have hprod : exp (n * β) * exp (-(n * β)) = 1 := by rw [← exp_add]; simp
  have e3 : 2 ≤ exp (n * β) + exp (-(n * β)) := by
    nlinarith [mul_nonneg (sq_nonneg (exp (n * β) - 1)) (exp_pos (-(n * β))).le, hprod]
  rw [abs_le]; simp only [gfun]; constructor <;> linarith

theorem gminus_odd (β x : ℝ) : gminus β (-x) = -gminus β x := by simp [gminus, mul_neg, sinh_neg]
theorem gplus_even (β x : ℝ) : gplus β (-x) = gplus β x := by simp [gplus, mul_neg, cosh_neg]

include hbd in
theorem abs_xp_le (p : LatticePlaquette d N) (U : GaugeConnection G d N) : |xp n p U| ≤ n := hbd _

include hbd in
theorem abs_prod_gfun_le {β : ℝ} (hβ : 0 ≤ β) (X : Finset (LatticePlaquette d N)) (U : GaugeConnection G d N) :
    |∏ p ∈ X, gfun β (xp n p U)| ≤ (exp (n * β) - 1) ^ X.card := by
  rw [Finset.abs_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun p _ => abs_nonneg _) (fun p _ => abs_gfun_le hβ (abs_xp_le hbd p U))

include hmeas in
theorem measurable_prod_gfun (β : ℝ) (X : Finset (LatticePlaquette d N)) :
    Measurable (fun U : GaugeConnection G d N => ∏ p ∈ X, gfun β (xp n p U)) := by
  apply Finset.measurable_prod
  intro p _
  exact (show Measurable (fun x : ℝ => exp (β * x) - 1) by fun_prop).comp (hmeas p)

include hbd in
/-- |I(X)| ≤ ε^|X|. -/
theorem abs_I_le {β : ℝ} (hβ : 0 ≤ β) (X : Finset (LatticePlaquette d N)) :
    |Iint (G := G) n β X| ≤ (exp (n * β) - 1) ^ X.card := by
  have h := norm_integral_le_of_norm_le_const (μ := productHaar G d N)
    (f := fun U => ∏ p ∈ X, gfun β (xp n p U)) (C := (exp (n * β) - 1) ^ X.card)
    (Filter.Eventually.of_forall (fun U => by rw [Real.norm_eq_abs]; exact abs_prod_gfun_le hbd hβ X U))
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
  exact h

include hbd in
/-- |I_C(X)| ≤ n ε^|X|. -/
theorem abs_IC_le {β : ℝ} (hβ : 0 ≤ β) (C : List (PathStep d N)) (X : Finset (LatticePlaquette d N)) :
    |ICint (G := G) n β C X| ≤ n * (exp (n * β) - 1) ^ X.card := by
  have hb : ∀ U : GaugeConnection G d N, |wilsonLoop n C U * ∏ p ∈ X, gfun β (xp n p U)| ≤ n * (exp (n * β) - 1) ^ X.card := by
    intro U
    rw [abs_mul]
    exact mul_le_mul (hbd _) (abs_prod_gfun_le hbd hβ X U) (abs_nonneg _) (by positivity)
  have h := norm_integral_le_of_norm_le_const (μ := productHaar G d N)
    (f := fun U => wilsonLoop n C U * ∏ p ∈ X, gfun β (xp n p U)) (C := n * (exp (n * β) - 1) ^ X.card)
    (Filter.Eventually.of_forall (fun U => by rw [Real.norm_eq_abs]; exact hb U))
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at h
  exact h

end Integrals

end
