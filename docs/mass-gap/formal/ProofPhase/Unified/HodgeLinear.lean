/-
The Hodge round: the Mathlib-only core (2026-11-24).
Released under Apache 2.0.

Paper: `docs/unified/HODGE.md`. This file imports Mathlib and nothing else (the IM rule: what the Hodge instance needs
and Mathlib lacks goes into a Mathlib-only module). The instance itself is `Unified/HodgeAPI.lean`.
-/

import Mathlib

/-!
# Hodge: the finite-dimensional core that Mathlib can reach

Mathlib (v4.34.0) has no complex manifolds beyond holomorphic functions, no Kaehler metric, no de Rham theorem, no Hodge
decomposition and no cycle class map. What is reachable is the linear algebra that the Hodge-Riemann positivity and the
Hodge index theorem reduce to, and the diagram chases of the Lefschetz (1,1) theorem. Everything here is classical
mathematics, proved in Lean; nothing here touches the Hodge conjecture itself.

* **Section 1, a polarised Hodge structure** (`PolHS`), in Deligne's form: a real representation of the circle (the
  Hodge types are its characters), an invariant symmetric form `Q`, and the Hodge-Riemann positivity `Q (C x) x > 0` with
  `C` the Weil operator. The Hodge classes are the vectors fixed by the circle. Proved: `Q` is positive definite on Hodge
  classes (`hodge_pos`), it satisfies Cauchy-Schwarz there (`hodge_cs`, the encoder bound), and the Hodge classes split
  off orthogonally (`hodge_isCompl`).
* **Section 2, the Hodge index theorem as linear algebra**: a form of signature `(1, *)` is nonpositive on the orthogonal
  of a positive class (`hodgeIndex_of_sigPos`), and that gives the reversed Cauchy-Schwarz inequality
  (`reverse_cs`), the Lorentzian twin of the encoder bound.
* **Section 3, Weil's Riemann hypothesis for curves from the Hodge index theorem** (the route of Weil, Mattuck-Tate and
  Grothendieck): with the intersection numbers of the fibres, the graph of Frobenius and the diagonal on `C x C`, the
  Hodge index property gives the Castelnuovo-Severi inequality (`castelnuovo_severi`) and the bound
  `|N - q - 1| <= 2 g sqrt q` (`weil_bound`, `weil_bound_abs`). Positivity makes the system run and certifies the line.
* **Section 4, a positive form puts eigenvalues on a circle** (`eigen_on_circle`): if Frobenius scales a positive-definite
  norm by `q^w`, every eigenvalue has absolute value `q^(w/2)`. This is the shape of the standard-conjecture route to
  the Weil conjectures.
* **Section 5, Lefschetz (1,1) and its neighbours, as diagram chases**: exactness at `H^2` gives the integral statement
  (`lefschetz11`), a multiple gives the rational one (`rational_descent`), hard Lefschetz carries it to curves
  (`transfer`), and the integral version needs every torsion class to be algebraic (`integral_needs_torsion`), which
  Atiyah and Hirzebruch showed fails.
-/

noncomputable section

namespace ProofPhase.Hodge

/-! ## 0. Cauchy-Schwarz on a nonnegative subspace (any ordered field) -/

section CS

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The square of a symmetric bilinear form at `x + t y`, expanded. -/
theorem sq_add_smul (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x) (x y : V) (t : K) :
    B (x + t • y) (x + t • y) = B y y * (t * t) + 2 * B x y * t + B x x := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hB y x]
  ring

/-- **Cauchy-Schwarz on a subspace where the form is nonnegative**: `B(x, y)^2 <= B(x, x) B(y, y)`. -/
theorem cs_of_nonneg [LinearOrder K] [IsStrictOrderedRing K] (B : LinearMap.BilinForm K V) (hB : ∀ x y, B x y = B y x) (S : Submodule K V)
    (hS : ∀ x ∈ S, 0 ≤ B x x) {x y : V} (hx : x ∈ S) (hy : y ∈ S) : B x y ^ 2 ≤ B x x * B y y := by
  have h : ∀ t : K, 0 ≤ B y y * (t * t) + 2 * B x y * t + B x x := fun t => by
    rw [← sq_add_smul B hB]
    exact hS _ (S.add_mem hx (S.smul_mem t hy))
  have := discrim_le_zero h
  rw [discrim] at this
  nlinarith

end CS

/-! ## 1. A polarised Hodge structure, and positivity on its Hodge classes -/

section PolHS

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **A polarised real Hodge structure of weight 0**, in Deligne's form (a Tate twist brings weight `2p` to weight 0):
a real representation `h` of the circle, whose characters `z ↦ z^(p-q)` are the Hodge types `(p, q)` (so a Hodge type
is a charge on the circle); a symmetric form `Q` invariant under the circle; and the **Hodge-Riemann positivity**:
`Q (C x) x > 0` for every `x ≠ 0`, where `C = h(i)` is the Weil operator. For the cohomology of a smooth projective
variety, with `Q` built from the cup product and an ample class (with the Lefschetz signs), this positivity is the
Hodge-Riemann bilinear relations, a theorem of Hodge theory (not in Mathlib). -/
structure PolHS (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The circle action; its characters are the Hodge types. -/
  h : Circle →* Module.End ℝ V
  /-- The polarisation. -/
  Q : LinearMap.BilinForm ℝ V
  symm : ∀ x y, Q x y = Q y x
  /-- `Q` is a morphism of Hodge structures to the trivial one. -/
  inv : ∀ z x y, Q (h z x) (h z y) = Q x y
  /-- The point `i` of the circle; `h weil` is the Weil operator. -/
  weil : Circle
  weil_eq : (weil : ℂ) = Complex.I
  /-- **Hodge-Riemann positivity**: `Q (C x) x > 0` for `x ≠ 0`. -/
  pos : ∀ x, x ≠ 0 → 0 < Q (h weil x) x

namespace PolHS

variable (P : PolHS V)

/-- **The Hodge classes**: the vectors fixed by the whole circle, i.e. of type `(0, 0)` (charge 0). After the Tate twist
these are the real `(p, p)` classes. -/
def hodge : Submodule ℝ V where
  carrier := {x | ∀ z, P.h z x = x}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    intro z
    rw [map_add, hx z, hy z]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    intro z
    exact map_zero _
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at *
    intro z
    rw [map_smul, hx z]

theorem mem_hodge {x : V} : x ∈ P.hodge ↔ ∀ z, P.h z x = x := Iff.rfl

/-- **Hodge-Riemann positivity on Hodge classes**: the polarisation is positive definite there (the Weil operator is
the identity on a fixed vector). -/
theorem hodge_pos {x : V} (hx : x ∈ P.hodge) (h0 : x ≠ 0) : 0 < P.Q x x := by
  have := P.pos x h0
  rwa [(P.mem_hodge.1 hx) P.weil] at this

theorem hodge_nonneg {x : V} (hx : x ∈ P.hodge) : 0 ≤ P.Q x x := by
  by_cases h0 : x = 0
  · simp [h0]
  · exact (P.hodge_pos hx h0).le

/-- **The encoder bound on Hodge classes**: Cauchy-Schwarz for the polarisation, `Q(x, y)^2 <= Q(x, x) Q(y, y)`. -/
theorem hodge_cs {x y : V} (hx : x ∈ P.hodge) (hy : y ∈ P.hodge) : P.Q x y ^ 2 ≤ P.Q x x * P.Q y y :=
  cs_of_nonneg P.Q P.symm P.hodge (fun _ hz => P.hodge_nonneg hz) hx hy

/-- **The Hodge classes split off**: `V` is the direct sum of the Hodge classes and their `Q`-orthogonal (the
restriction of `Q` to the Hodge classes is nondegenerate, because it is definite). -/
theorem hodge_isCompl [FiniteDimensional ℝ V] : IsCompl P.hodge (P.Q.orthogonal P.hodge) := by
  apply LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
  · intro x y hxy
    rw [P.symm]
    exact hxy
  · apply LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal
    · intro x y hxy
      rw [P.symm]
      exact hxy
    · rw [Submodule.disjoint_def]
      intro x hx hxo
      by_contra h0
      have h2 : P.Q x x = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hxo) x hx
      exact (P.hodge_pos hx h0).ne' h2

end PolHS

end PolHS

/-! ## 2. The Hodge index theorem as linear algebra -/

section Index

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- **The Hodge index property at `H`**: every class orthogonal to `H` has nonpositive square. For the intersection form
on the Neron-Severi group of a surface and `H` ample this is the Hodge index theorem (Hodge 1937; Grothendieck 1958 in
every characteristic); in the language of the standard conjectures it is the Hodge standard conjecture for a surface. -/
def HodgeIndex (B : LinearMap.BilinForm ℝ W) (H : W) : Prop := ∀ E, B E H = 0 → B E E ≤ 0

/-- **Signature `(1, *)` gives the Hodge index property**: if no plane is positive definite, a class orthogonal to a
positive class cannot be positive. -/
theorem hodgeIndex_of_sigPos [FiniteDimensional ℝ W] (B : LinearMap.BilinForm ℝ W) (hB : ∀ x y, B x y = B y x)
    {H : W} (hH : 0 < B H H) (hsig : sigPos (LinearMap.BilinMap.toQuadraticMap B) ≤ 1) :
    HodgeIndex B H := by
  intro E hEH
  by_contra hc'
  have hc : 0 < B E E := not_le.1 hc'
  have hHE : B H E = 0 := by rw [hB]; exact hEH
  have hquad : ∀ a b : ℝ, B (a • H + b • E) (a • H + b • E) = a ^ 2 * B H H + b ^ 2 * B E E := by
    intro a b
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hEH, hHE]
    ring
  have hli : LinearIndependent ℝ ![H, E] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : B (s • H + t • E) H = s * B H H := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hEH]
      ring
    rw [hst, map_zero, LinearMap.zero_apply] at h1
    have hs : s = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact h
      · exact absurd h hH.ne'
    refine ⟨hs, ?_⟩
    rw [hs, zero_smul, zero_add] at hst
    rcases smul_eq_zero.1 hst with h | h
    · exact h
    · simp [h] at hc
  have hpos : ((LinearMap.BilinMap.toQuadraticMap B).restrict (Submodule.span ℝ {H, E})).PosDef := by
    intro v hv
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 v.2
    simp only [QuadraticMap.restrict_apply, LinearMap.BilinMap.toQuadraticMap_apply]
    rw [← hab, hquad]
    by_cases ha : a = 0
    · have hb : b ≠ 0 := by
        intro hb
        apply hv
        apply Subtype.ext
        rw [← hab, ha, hb, zero_smul, zero_smul, add_zero]
        rfl
      rw [ha]
      have : 0 < b ^ 2 := by positivity
      nlinarith
    · have : 0 < a ^ 2 := by positivity
      have : 0 ≤ b ^ 2 := sq_nonneg b
      nlinarith
  have h2 := le_sigPos_of_posDef _ hpos
  have hr : Module.finrank ℝ (Submodule.span ℝ {H, E}) = 2 := by
    have e : Set.range ![H, E] = {H, E} := by
      ext v
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    have := finrank_span_eq_card hli
    rw [e] at this
    simpa using this
  omega

/-- **The reversed Cauchy-Schwarz inequality** (Lorentzian): under the Hodge index property at a positive class `H`,
`B(D, D) B(H, H) <= B(D, H)^2` for every `D`. -/
theorem reverse_cs (B : LinearMap.BilinForm ℝ W) (hB : ∀ x y, B x y = B y x) {H : W} (hH : 0 < B H H)
    (hI : HodgeIndex B H) (D : W) : B D D * B H H ≤ B D H ^ 2 := by
  have hE : B (B H H • D - B D H • H) H = 0 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have h := hI _ hE
  have e : B (B H H • D - B D H • H) (B H H • D - B D H • H) = B H H * (B D D * B H H - B D H ^ 2) := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hB H D]
    ring
  rw [e] at h
  have hX : B D D * B H H - B D H ^ 2 ≤ 0 := by
    by_contra hc'
    have hc := not_le.1 hc'
    have := mul_pos hH hc
    linarith
  linarith

end Index

/-! ## 3. Weil's Riemann hypothesis for curves from the Hodge index theorem -/

section Weil

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

/-- **Castelnuovo-Severi inequality**: on `C x C` with fibre classes `f₁` (of `{pt} x C`) and `f₂` (of `C x {pt}`),
`f₁^2 = f₂^2 = 0`, `f₁ f₂ = 1`, the Hodge index property at the ample class `f₁ + f₂` gives
`D^2 <= 2 (D f₁)(D f₂)` for every class `D`. -/
theorem castelnuovo_severi (B : LinearMap.BilinForm ℝ W) (hB : ∀ x y, B x y = B y x) {f₁ f₂ : W}
    (h11 : B f₁ f₁ = 0) (h22 : B f₂ f₂ = 0) (h12 : B f₁ f₂ = 1) (hI : HodgeIndex B (f₁ + f₂)) (D : W) :
    B D D ≤ 2 * B D f₁ * B D f₂ := by
  have h21 : B f₂ f₁ = 1 := by rw [hB]; exact h12
  have hE : B (D - B D f₂ • f₁ - B D f₁ • f₂) (f₁ + f₂) = 0 := by
    simp only [map_sub, map_smul, map_add, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h11, h22, h12,
      h21]
    ring
  have h := hI _ hE
  have e : B (D - B D f₂ • f₁ - B D f₁ • f₂) (D - B D f₂ • f₁ - B D f₁ • f₂) = B D D - 2 * B D f₁ * B D f₂ := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h11, h22, h12, h21,
      hB f₁ D, hB f₂ D]
    ring
  linarith

/-- The quadratic form the Castelnuovo-Severi inequality leaves on the span of the graph of Frobenius and the diagonal:
`g q a^2 - a b (N - q - 1) + g b^2 >= 0` for all real `a`, `b`. -/
theorem weil_form (B : LinearMap.BilinForm ℝ W) (hB : ∀ x y, B x y = B y x) {f₁ f₂ Γ Δ : W} {g q N : ℝ}
    (h11 : B f₁ f₁ = 0) (h22 : B f₂ f₂ = 0) (h12 : B f₁ f₂ = 1) (hI : HodgeIndex B (f₁ + f₂))
    (hΓ1 : B Γ f₁ = 1) (hΓ2 : B Γ f₂ = q) (hΔ1 : B Δ f₁ = 1) (hΔ2 : B Δ f₂ = 1)
    (hΓΓ : B Γ Γ = q * (2 - 2 * g)) (hΔΔ : B Δ Δ = 2 - 2 * g) (hΓΔ : B Γ Δ = N) (a b : ℝ) :
    0 ≤ g * q * a ^ 2 - a * b * (N - q - 1) + g * b ^ 2 := by
  have h := castelnuovo_severi B hB h11 h22 h12 hI (a • Γ + b • Δ)
  have hΔΓ : B Δ Γ = N := by rw [hB]; exact hΓΔ
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hΓ1, hΓ2, hΔ1, hΔ2, hΓΓ,
    hΔΔ, hΓΔ, hΔΓ] at h
  nlinarith

/-- **Weil's bound** (the Riemann hypothesis for a curve of genus `g` over `F_q`, in the form of the point count):
`(N - q - 1)^2 <= 4 g^2 q`, where `N` is the number of `F_q`-points (the intersection of the graph of Frobenius with the
diagonal). The inputs are the intersection numbers on `C x C` and the Hodge index property. -/
theorem weil_bound (B : LinearMap.BilinForm ℝ W) (hB : ∀ x y, B x y = B y x) {f₁ f₂ Γ Δ : W} {g q N : ℝ}
    (hg : 0 ≤ g) (hq : 0 < q)
    (h11 : B f₁ f₁ = 0) (h22 : B f₂ f₂ = 0) (h12 : B f₁ f₂ = 1) (hI : HodgeIndex B (f₁ + f₂))
    (hΓ1 : B Γ f₁ = 1) (hΓ2 : B Γ f₂ = q) (hΔ1 : B Δ f₁ = 1) (hΔ2 : B Δ f₂ = 1)
    (hΓΓ : B Γ Γ = q * (2 - 2 * g)) (hΔΔ : B Δ Δ = 2 - 2 * g) (hΓΔ : B Γ Δ = N) :
    (N - q - 1) ^ 2 ≤ 4 * g ^ 2 * q := by
  have key := weil_form B hB h11 h22 h12 hI hΓ1 hΓ2 hΔ1 hΔ2 hΓΓ hΔΔ hΓΔ
  rcases hg.eq_or_lt with h0 | hpos
  · have := key 1 (N - q - 1)
    rw [← h0] at this ⊢
    nlinarith
  · have := key (N - q - 1) (2 * g * q)
    have hgq : 0 < g * q := mul_pos hpos hq
    have e : g * q * (N - q - 1) ^ 2 - (N - q - 1) * (2 * g * q) * (N - q - 1) + g * (2 * g * q) ^ 2 =
        g * q * (4 * g ^ 2 * q - (N - q - 1) ^ 2) := by ring
    rw [e] at this
    by_contra hc'
    have hc := not_le.1 hc'
    have : g * q * (4 * g ^ 2 * q - (N - q - 1) ^ 2) < 0 := mul_neg_of_pos_of_neg hgq (by linarith)
    linarith

/-- **Weil's bound, absolute form**: `|N - (q + 1)| <= 2 g sqrt q`. -/
theorem weil_bound_abs (B : LinearMap.BilinForm ℝ W) (hB : ∀ x y, B x y = B y x) {f₁ f₂ Γ Δ : W} {g q N : ℝ}
    (hg : 0 ≤ g) (hq : 0 < q)
    (h11 : B f₁ f₁ = 0) (h22 : B f₂ f₂ = 0) (h12 : B f₁ f₂ = 1) (hI : HodgeIndex B (f₁ + f₂))
    (hΓ1 : B Γ f₁ = 1) (hΓ2 : B Γ f₂ = q) (hΔ1 : B Δ f₁ = 1) (hΔ2 : B Δ f₂ = 1)
    (hΓΓ : B Γ Γ = q * (2 - 2 * g)) (hΔΔ : B Δ Δ = 2 - 2 * g) (hΓΔ : B Γ Δ = N) :
    |N - (q + 1)| ≤ 2 * g * Real.sqrt q := by
  have h := weil_bound B hB hg hq h11 h22 h12 hI hΓ1 hΓ2 hΔ1 hΔ2 hΓΓ hΔΔ hΓΔ
  have h' := Real.sqrt_le_sqrt h
  rw [show N - (q + 1) = N - q - 1 by ring, ← Real.sqrt_sq_eq_abs]
  rwa [show 4 * g ^ 2 * q = (2 * g) ^ 2 * q by ring, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (show (0 : ℝ) ≤ 2 * g by linarith)] at h'

end Weil

/-! ## 4. A positive form puts the eigenvalues on a circle -/

/-- **Positivity puts the eigenvalues on the circle of radius `sqrt c`**: if `F` scales a positive-definite norm by `c`
(`‖F x‖^2 = c ‖x‖^2`, a similitude), every eigenvalue `μ` of `F` has `|μ|^2 = c`. With `c = q^w` (Frobenius on
weight-`w` cohomology, made a similitude by a positive form) this is the Riemann hypothesis part of the Weil
conjectures; the positive form is what the Hodge standard conjecture would supply. -/
theorem eigen_on_circle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Module.End ℂ E) {c : ℝ}
    (hF : ∀ x, ‖F x‖ ^ 2 = c * ‖x‖ ^ 2) {μ : ℂ} (hμ : F.HasEigenvalue μ) : ‖μ‖ ^ 2 = c := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have h := hF v
  rw [hv.apply_eq_smul, norm_smul, mul_pow] at h
  have hn : 0 < ‖v‖ ^ 2 := by positivity
  exact mul_right_cancel₀ hn.ne' h

/-- **The same with a positive-definite Hermitian form** `S` (the form the Hodge standard conjecture would supply): if
`S (F x) (F y) = c S(x, y)`, every eigenvalue `μ` of `F` has `|μ|^2 = c`. -/
theorem eigen_on_circle_form {E : Type*} [AddCommGroup E] [Module ℂ E] (S : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ)
    (hpos : ∀ x, x ≠ 0 → 0 < (S x x).re) (F : Module.End ℂ E) {c : ℝ} (hF : ∀ x y, S (F x) (F y) = (c : ℂ) * S x y)
    {μ : ℂ} (hμ : F.HasEigenvalue μ) : ‖μ‖ ^ 2 = c := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have h := hF v v
  rw [hv.apply_eq_smul, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc] at h
  have hs : S v v ≠ 0 := by
    intro h0
    have := hpos v hv0
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have h2 : (starRingEnd ℂ) μ * μ = (c : ℂ) := mul_right_cancel₀ hs h
  rw [Complex.conj_mul'] at h2
  exact_mod_cast h2

/-! ## 5. Lefschetz (1,1) and its neighbours, as diagram chases -/

section Lefschetz

/-- **Lefschetz (1,1), the chase**: if `Pic → H^2(X, Z) → H^{0,2}` is exact at `H^2` (the exponential sequence) and an
integral class is of type `(1,1)` exactly when its `(0,2)` part vanishes (Hodge symmetry), every integral `(1,1)` class is
the first Chern class of a line bundle. -/
theorem lefschetz11 {Pic H2 H02 : Type*} [AddCommGroup Pic] [AddCommGroup H2] [AddCommGroup H02] (c₁ : Pic →+ H2)
    (π : H2 →+ H02) (exact : ∀ x, π x = 0 → x ∈ c₁.range) {x : H2} (hx : π x = 0) : ∃ L, c₁ L = x :=
  AddMonoidHom.mem_range.1 (exact x hx)

/-- **Rational descent**: a rational class with a positive multiple equal to the image of a class in `S` lies in the
rational span of the image of `S`. -/
theorem rational_descent {A Q : Type*} [AddCommGroup A] [AddCommGroup Q] [Module ℚ Q] (ι : A →+ Q) (S : Set A)
    {y : Q} {n : ℕ} (hn : 0 < n) {x : A} (hx : x ∈ S) (hxy : ι x = n • y) : y ∈ Submodule.span ℚ (ι '' S) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have e : y = (n : ℚ)⁻¹ • ι x := by
    rw [hxy, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn', one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, hx, rfl⟩)

/-- **Transfer along an isomorphism of Hodge structures** (hard Lefschetz `L^{n-2} : H^2 ≅ H^{2n-2}`): if the inverse
maps Hodge classes to Hodge classes and the map sends algebraic classes to algebraic classes, the Hodge statement on
the source gives it on the target. -/
theorem transfer {K A B : Type*} [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] (e : A ≃ₗ[K] B)
    {hA algA : Submodule K A} {hB algB : Submodule K B} (hodge_back : ∀ y ∈ hB, e.symm y ∈ hA)
    (alg_fwd : algA.map e.toLinearMap ≤ algB) (h : hA ≤ algA) : hB ≤ algB := by
  intro y hy
  have h1 : e.symm y ∈ algA := h (hodge_back y hy)
  have h2 := Submodule.mem_map_of_mem (f := e.toLinearMap) h1
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
  exact alg_fwd h2

/-- **The integral version needs every torsion class**: a torsion class maps to `0` in rational cohomology, which is a
Hodge class; so "every integral class whose rational image is Hodge is algebraic" makes every torsion class algebraic.
Atiyah and Hirzebruch found torsion classes that are not (`HodgeAPI`, `integralCard`). -/
theorem integral_needs_torsion {A Q : Type*} [AddCommGroup A] [AddCommGroup Q] [Module ℚ Q] (ι : A →+ Q)
    (hodgeQ : Submodule ℚ Q) (alg : Set A) (hInt : ∀ x, ι x ∈ hodgeQ → x ∈ alg) {x : A} {n : ℕ} (hn : 0 < n)
    (ht : n • x = 0) : x ∈ alg := by
  apply hInt
  have h1 : (n : ℚ) • ι x = 0 := by rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, ht, map_zero]
  rcases smul_eq_zero.1 h1 with h | h
  · exact absurd h (Nat.cast_ne_zero.2 hn.ne')
  · rw [h]
    exact hodgeQ.zero_mem

end Lefschetz

end ProofPhase.Hodge
