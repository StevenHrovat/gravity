/-
SU(N) primes round (sun-primes): the strict twist bound `0 < Z_tw,k < Z` for the SU(N) Wilson action, every centre
element `ω^k ≠ 1`, and the electric sectors on the lattice (2026-11-23). Released under Apache 2.0.

Note: `docs/unified/SUN-PRIMES.md`, section 2.
-/

import ProofPhase.General.SUNTwistSchur
import ProofPhase.General.SUNTwistSectors

/-!
# `0 < Z_tw,k < Z` for SU(N): the strict twist bound for every centre element

**Setting.** The SU(N) Wilson action on `ℤ/Tℤ × (ℤ/Lℤ)³` as a chain weight (`sunW`, coupling `β`, any spatial
background twist `P`), and the 't Hooft twist in the plane `(t, x¹)` at `x¹ = c` by the centre element
`ω^k = e^{2πik/N}` (`zFamN`: the linkwise map `flipG` with `zN k`). `Z = sunZ`, `Z_tw,k = sunZtw … k`.

**Theorems (every `N ≥ 2`, every `L ≥ 1`, every even `T`, every `P`, every `c`).**
* `sunZtw_zero`: `Z_tw,0 = Z`;
* `sunZtw_neg`: `Z_tw,−k = Z_tw,k`, i.e. `Z_tw,k = Z_tw,N−k` (every `β`);
* `sunZtw_pos`, `sunZtw_le`: `0 < Z_tw,k ≤ Z` (every `β`);
* **`sunZtw_lt`: `Z_tw,k < Z` for every `β ≠ 0` and every `k ≠ 0`**;
* `sunTwistRatio_mem`: `c_k = Z_tw,k / Z ∈ (0, 1)` for `β ≠ 0`, `k ≠ 0`;
* the electric sectors `Z_e = (1/N) Σ_k ω^{−ek} Z_tw,k` (`sunZe`) are real, `Z_e = Z_{−e}`, `Z_e ≥ 0` (reflection
  positivity, `ZFam.elec_nonneg`, **not** a hypothesis), `Σ_e Z_e = Z`, and for `β ≠ 0` some sector `e ≠ 0` has
  `Z_e > 0` (`exists_sunZe_pos`).

**Proof of strictness.** `cZtw_lt_cZ_of_step_u` with the charge `φ∘h − φ` of the Polyakov ratio `φ = Re tr P / V`
(`P` the Polyakov line through the origin along the first spatial axis; it crosses the twist plane once, so the twist
multiplies it by `ω^{−k}`): `φ∘h − φ = (Re tr(ω^{−k} P) − Re tr P)/V`. One transfer step integrates the line link by
link with Schur's lemma on SU(N) (`schur_SUN`, `lineIntN`), so
`⟨φ∘h − φ, 𝒦(φ∘h − φ)⟩_V = λ_N(β)^L κ ∫ (Re tr(ω^{−k} P) − Re tr P)² ≠ 0`: `λ_N(β) ≠ 0` for `β ≠ 0`
(`schurCN_ne_zero`), `κ > 0`, and the integrand is continuous, nonnegative, and at the trivial connection equals
`(N Re ω^{−k} − N)² > 0` (`reTr_zN_ne`). This is `Flip/Strict`'s SU(2) proof with `Z_2` replaced by `Z_N`.

**Claim discipline.** Strict at each finite lattice, no size control: no lower bound on `Z − Z_tw,k` uniform in the
volume, so no flux free energy, no confinement, no mass gap. In particular this is **not** O1 (the uniform one-box bound
`c ≥ 0.743` stays open). The bridge from this chain to `ProofPhase.RouteB.twistZ` on `(ℤ/Nℤ)⁴` is not formalised (as for
SU(2)).
-/

open MeasureTheory Finset Positivity AreaLaw.Concrete ProofPhase.RouteB ProofPhase.Flip

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

/-! ## Positivity of a twisted partition function (any chain with positive weights) -/

section Pos

variable {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G] {E S : Type*} [Fintype E] [Fintype S]
  {T : ℕ} [NeZero T]

theorem cZtw_pos (w : ChainWeight G E S) (g : E → G → G) (hg : ∀ e, Measurable (g e)) (hV : ∀ a, 0 < w.V a)
    (hK : ∀ a b c, 0 < w.K a b c) : 0 < cZtw (T := T) w g := by
  obtain ⟨MV, hMV⟩ := w.V_bdd
  obtain ⟨MK, hMK⟩ := w.K_bdd
  have hpos : ∀ U, 0 < twWeight (T := T) w g U := fun U => prod_pos fun t _ => mul_pos (hV _) (hK _ _ _)
  have hle : ∀ U, twWeight (T := T) w g U ≤ ∏ _t : ZMod T, MV * MK := fun U => by
    unfold twWeight twStep
    exact Finset.prod_le_prod₀ (h0 := fun t _ => mul_nonneg (w.V_nonneg _) (w.K_nonneg _ _ _))
      (h1 := fun t _ => mul_le_mul (hMV _) (hMK _ _ _) (w.K_nonneg _ _ _) ((w.V_nonneg 1).trans (hMV 1)))
  have hi : Integrable (twWeight (T := T) w g) (cHaar G E S T) :=
    IsBdd.integrable ⟨_, fun U => by rw [Real.norm_of_nonneg (hpos U).le]; exact hle U⟩
      (measurable_twWeight w g hg).aestronglyMeasurable
  unfold cZtw
  rw [integral_pos_iff_support_of_nonneg (fun U => (hpos U).le) hi]
  have hs : Function.support (twWeight (T := T) w g) = Set.univ :=
    Set.eq_univ_of_forall fun U => (hpos U).ne'
  rw [hs, measure_univ]
  exact one_pos

end Pos

/-! ## SU(N): integrating a Wilson line against independent plaquette factors -/

section LineIntN

variable {N : ℕ} [NeZero N] {E : Type*} [Fintype E] [DecidableEq E]

/-- **Line integral on SU(N).** Integrating out the links of a (duplicate-free) list `ls` against independent plaquette
factors `e^{β Re tr u_e}` turns `Re tr(X · ∏ u_e a_e)` into `λ_N(β)^{|ls|} Re tr(X · ∏ a_e)`. -/
theorem lineIntN (β : ℝ) (a : E → SUN N) (ls : List E) :
    ∀ (s : Finset E) (X : SUN N), ls.Nodup → (∀ e ∈ ls, e ∈ s) →
      ∫ u, (∏ e ∈ s, bwN β (u e)) * gaugeReTr (SUN N) N (X * (ls.map fun e => u e * a e).prod)
          ∂(sliceHaar (SUN N) E) =
        schurCN (N := N) β ^ ls.length * (∫ u, ∏ e ∈ s \ ls.toFinset, bwN β (u e) ∂(sliceHaar (SUN N) E)) *
          gaugeReTr (SUN N) N (X * (ls.map a).prod) := by
  induction ls with
  | nil =>
    intro s X _ _
    simp only [List.map_nil, List.prod_nil, mul_one, List.length_nil, pow_zero, one_mul, List.toFinset_nil,
      Finset.sdiff_empty]
    exact integral_mul_const _ _
  | cons e ls ih =>
    intro s X hnd hs
    obtain ⟨he_ls, hnd'⟩ := List.nodup_cons.1 hnd
    have hes : e ∈ s := hs e List.mem_cons_self
    have hs' : ∀ e' ∈ ls, e' ∈ s.erase e := fun e' he' =>
      Finset.mem_erase.2 ⟨fun h : e' = e => he_ls (h ▸ he'), hs e' (List.mem_cons_of_mem _ he')⟩
    have hcont : Continuous fun u : E → SUN N =>
        (∏ e' ∈ s, bwN β (u e')) * gaugeReTr (SUN N) N (X * ((e :: ls).map fun e' => u e' * a e').prod) :=
      (continuous_finsetProd _ fun e' _ => (continuous_bwN β).comp (continuous_apply e')).mul
        (continuous_trN.comp (continuous_const.mul
          (continuous_list_prod _ fun e' _ => (continuous_apply e').mul continuous_const)))
    rw [integral_update (haarG (SUN N)) e hcont.measurable (isBdd_of_continuous hcont)]
    set Q : (E → SUN N) → SUN N := fun u => (ls.map fun e' => u e' * a e').prod with hQ
    set R : (E → SUN N) → ℝ := fun u => ∏ e' ∈ s.erase e, bwN β (u e') with hR
    have pt : ∀ (u : E → SUN N) (v : SUN N),
        (∏ e' ∈ s, bwN β (Function.update u e v e')) *
          gaugeReTr (SUN N) N (X * ((e :: ls).map fun e' => Function.update u e v e' * a e').prod) =
        R u * (bwN β v * gaugeReTr (SUN N) N (v * (a e * Q u * X))) := by
      intro u v
      rw [← Finset.mul_prod_erase s _ hes, Function.update_self]
      have hpr : ∏ e' ∈ s.erase e, bwN β (Function.update u e v e') = R u :=
        prod_congr rfl fun e' he' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase he')]
      have hls : (ls.map fun e' => Function.update u e v e' * a e') = ls.map fun e' => u e' * a e' :=
        List.map_congr_left fun e' he' => by
          rw [Function.update_of_ne (fun h : e' = e => he_ls (h ▸ he'))]
      rw [hpr, List.map_cons, List.prod_cons, hls, Function.update_self]
      have hc : X * (v * a e * Q u) = X * (v * (a e * Q u * X)) * X⁻¹ := by group
      rw [hc, gaugeReTr_conj]
      ring
    have inner : ∀ u : E → SUN N,
        ∫ v, (∏ e' ∈ s, bwN β (Function.update u e v e')) *
          gaugeReTr (SUN N) N (X * ((e :: ls).map fun e' => Function.update u e v e' * a e').prod)
            ∂(haarG (SUN N)) =
        schurCN (N := N) β * (R u * gaugeReTr (SUN N) N ((X * a e) * Q u)) := by
      intro u
      simp_rw [pt u]
      rw [integral_const_mul, schur_SUN]
      have hc : X * a e * Q u = X * (a e * Q u * X) * X⁻¹ := by group
      rw [hc, gaugeReTr_conj]
      ring
    simp_rw [inner]
    rw [integral_const_mul, ih (s.erase e) (X * a e) hnd' hs']
    have hset : s.erase e \ ls.toFinset = s \ (e :: ls).toFinset := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset, List.mem_cons]
      tauto
    rw [hset, List.length_cons, pow_succ, List.map_cons, List.prod_cons, mul_assoc X]
    ring

end LineIntN

/-! ## The SU(N) Wilson chain and the centre twists -/

section WilsonSUN

variable (N : ℕ) [NeZero N] (L : ℕ) [NeZero L]

/-- The SU(N) Wilson chain weight on `ℤ/Tℤ × (ℤ/Lℤ)³` (coupling `β`, spatial twist `P`). -/
abbrev sunW (β : ℝ) (P : Finset (LatticePlaquette 3 L)) :
    ChainWeight (SUN N) (LatticeLink 3 L) (FinLatticeSites 3 L) :=
  wilsonChain (G := SUN N) (n := N) L continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β P

theorem sliceV_posN (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (a : GaugeConnection (SUN N) 3 L) :
    0 < sliceV L N β P a := prod_pos fun _ _ => Real.exp_pos _

/-- **The centre twists as a `Z_N` family**: `g_k` multiplies the first-direction links of the plane `x¹ = c` by
`ω^k`. -/
def zFamN (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) : ZFam (sunW N L β P) N where
  g k := flipG L (zN k) c
  comp k l e x := by
    unfold flipG
    split_ifs
    · show zN k * (zN l * x) = zN (k + l) * x
      rw [zN_add, mul_assoc]
    · rfl
  zero e x := by
    unfold flipG
    split_ifs
    · show zN 0 * x = x
      rw [zN_zero, one_mul]
    · rfl
  mp k e := by
    unfold flipG
    split_ifs
    · exact measurePreserving_mul_left (haarG (SUN N)) (zN k)
    · exact MeasurePreserving.id _
  inv k a := by
    show sliceV L N β P (sliceMap (flipG L (zN k) c) a) = sliceV L N β P a
    rw [sliceMap_flipG, sliceV_flip L (zN_central k)]

/-- The periodic SU(N) partition function. -/
def sunZ (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (T : ℕ) [NeZero T] : ℝ := cZ (T := T) (sunW N L β P)

/-- **The twisted SU(N) partition function** `Z_tw,k`: the 't Hooft twist by `ω^k` in the plane `(t, x¹)` at `x¹ = c`. -/
def sunZtw (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T] (k : ZMod N) : ℝ :=
  (zFamN N L β P c).Zk T k

theorem sunZtw_eq (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T] (k : ZMod N) :
    sunZtw N L β P c T k = cZtw (T := T) (sunW N L β P) (flipG L (zN k) c) := rfl

theorem sunZtw_zero (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T] :
    sunZtw N L β P c T 0 = sunZ N L β P T := (zFamN N L β P c).Zk_zero

/-- **`Z_tw,k = Z_tw,N−k`** (every `β`, `T` even). -/
theorem sunZtw_neg (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ} [NeZero T] (hT : Even T)
    (k : ZMod N) : sunZtw N L β P c T (-k) = sunZtw N L β P c T k :=
  (zFamN N L β P c).Zk_neg hT (fun a b c => stepK_pos L β a b c) k

/-- **`Z_tw,k ≤ Z`** (every `β`, `T` even). -/
theorem sunZtw_le (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ} [NeZero T] (hT : Even T)
    (k : ZMod N) : sunZtw N L β P c T k ≤ sunZ N L β P T :=
  (zFamN N L β P c).Zk_le hT (fun a b c => stepK_pos L β a b c) k

/-- **`0 < Z_tw,k`** (every `β`, every `T`). -/
theorem sunZtw_pos (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T] (k : ZMod N) :
    0 < sunZtw N L β P c T k :=
  cZtw_pos _ _ (fun e => ((zFamN N L β P c).mp k e).measurable) (fun a => sliceV_posN N L β P a)
    (fun a b c => stepK_pos L β a b c)

theorem sunZ_pos (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (T : ℕ) [NeZero T] : 0 < sunZ N L β P T := by
  rw [← sunZtw_zero N L β P 0]; exact sunZtw_pos N L β P 0 T 0

/-! ### The Polyakov line -/

theorem polyLine_eqN (a : GaugeConnection (SUN N) 3 L) : polyLine L a 0 = ((lineLinks L).map a).prod := by
  unfold polyLine lineLinks; rw [List.map_map]; rfl

/-- The Polyakov line with a central prefactor: `Re tr(X P(a))`. -/
def polyObsN (X : SUN N) (a : GaugeConnection (SUN N) 3 L) : ℝ := gaugeReTr (SUN N) N (X * polyLine L a 0)

theorem continuous_polyObsN (X : SUN N) : Continuous (polyObsN N L X) := by
  unfold polyObsN polyLine
  exact continuous_trN.comp (continuous_const.mul (continuous_list_prod _ fun k _ => continuous_apply _))

/-- The gauge change that absorbs the temporal links of one step. -/
def gaugeSubN (a : GaugeConnection (SUN N) 3 L) (b : FinLatticeSites 3 L → SUN N) (u : GaugeConnection (SUN N) 3 L) :
    GaugeConnection (SUN N) 3 L :=
  fun e => (b e.site)⁻¹ * u e * (a e * b e.target)

theorem measurePreserving_gaugeSubN (a : GaugeConnection (SUN N) 3 L) (b : FinLatticeSites 3 L → SUN N) :
    MeasurePreserving (gaugeSubN N L a b) (sliceHaar (SUN N) (LatticeLink 3 L))
      (sliceHaar (SUN N) (LatticeLink 3 L)) :=
  measurePreserving_pi (fun _ => haarG (SUN N)) (fun _ => haarG (SUN N)) (fun e =>
    (measurePreserving_mul_right (haarG (SUN N)) (a e * b e.target)).comp
      (measurePreserving_mul_left (haarG (SUN N)) (b e.site)⁻¹))

theorem stepK_gaugeSubN (β : ℝ) (a : GaugeConnection (SUN N) 3 L) (b : FinLatticeSites 3 L → SUN N)
    (u : GaugeConnection (SUN N) 3 L) : stepK L N β a b (gaugeSubN N L a b u) = ∏ e, bwN β (u e) := by
  unfold stepK
  refine prod_congr rfl fun e _ => ?_
  unfold bwN tempHol gaugeSubN
  congr 3
  group

theorem polyObs_gaugeSubN {X : SUN N} (hX : ∀ g : SUN N, Commute X g) (a : GaugeConnection (SUN N) 3 L)
    (b : FinLatticeSites 3 L → SUN N) (u : GaugeConnection (SUN N) 3 L) :
    polyObsN N L X (gaugeSubN N L a b u) =
      gaugeReTr (SUN N) N (X * ((lineLinks L).map fun e => u e * a e).prod) := by
  unfold polyObsN
  rw [polyLine_eqN]
  have e1 : (lineLinks L).map (gaugeSubN N L a b u) = (List.range L).map fun k =>
      (b (lineSite L 0 k))⁻¹ * (u ⟨lineSite L 0 k, 0⟩ * a ⟨lineSite L 0 k, 0⟩) * b (lineSite L 0 (k + 1)) := by
    unfold lineLinks
    rw [List.map_map]
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp, gaugeSubN, line_target]
    group
  rw [e1, prod_telescope, lineSite_L]
  have e2 : ((List.range L).map fun k => u ⟨lineSite L 0 k, 0⟩ * a ⟨lineSite L 0 k, 0⟩) =
      (lineLinks L).map fun e => u e * a e := by
    unfold lineLinks; rw [List.map_map]; rfl
  rw [e2]
  set B := b (lineSite L 0 0)
  set Q := ((lineLinks L).map fun e => u e * a e).prod
  have hc : X * (B⁻¹ * Q * B) = B⁻¹ * (X * Q) * B⁻¹⁻¹ := by
    calc X * (B⁻¹ * Q * B) = (X * B⁻¹) * Q * B := by group
      _ = (B⁻¹ * X) * Q * B := by rw [(hX B⁻¹).eq]
      _ = B⁻¹ * (X * Q) * B⁻¹⁻¹ := by group
  rw [hc, gaugeReTr_conj]

theorem continuous_stepKN (β : ℝ) :
    Continuous fun z : GaugeConnection (SUN N) 3 L × (FinLatticeSites 3 L → SUN N) × GaugeConnection (SUN N) 3 L =>
      stepK L N β z.1 z.2.1 z.2.2 := by
  unfold stepK tempHol
  refine continuous_finsetProd _ fun e _ => Real.continuous_exp.comp (continuous_const.mul
    (continuous_trN.comp ?_))
  fun_prop

/-- The product of the plaquette factors off the line. -/
def lineConstN (β : ℝ) : ℝ :=
  ∫ u, ∏ e ∈ univ \ (lineLinks L).toFinset, bwN β (u e) ∂(sliceHaar (SUN N) (LatticeLink 3 L))

theorem lineConstN_pos (β : ℝ) : 0 < lineConstN N L β :=
  integral_pos_of_continuous (continuous_finsetProd _ fun e _ => (continuous_bwN β).comp (continuous_apply e))
    (fun _ => (prod_pos fun _ _ => bwN_pos β _).le) (x0 := 1) (prod_pos fun _ _ => bwN_pos β _)

/-- **One transfer step of the Polyakov line on SU(N)**: `∫ K(a, b, c) Re tr(X P(c)) dc = λ_N(β)^L κ Re tr(X P(a))`
for every central `X`. -/
theorem stepK_polyObsN {X : SUN N} (hX : ∀ g : SUN N, Commute X g) (β : ℝ) (a : GaugeConnection (SUN N) 3 L)
    (b : FinLatticeSites 3 L → SUN N) :
    ∫ c, stepK L N β a b c * polyObsN N L X c ∂(sliceHaar (SUN N) (LatticeLink 3 L)) =
      schurCN (N := N) β ^ L * lineConstN N L β * polyObsN N L X a := by
  have hc : Continuous fun c => stepK L N β a b c * polyObsN N L X c :=
    ((continuous_stepKN N L β).comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).mul
      (continuous_polyObsN N L X)
  refine (integral_comp_of_measurePreserving (measurePreserving_gaugeSubN N L a b)
    (g := fun c => stepK L N β a b c * polyObsN N L X c) hc.aestronglyMeasurable).symm.trans ?_
  simp only [stepK_gaugeSubN, polyObs_gaugeSubN N L hX]
  rw [lineIntN β a (lineLinks L) univ X (lineLinks_nodup L) (fun e _ => mem_univ e)]
  unfold lineConstN polyObsN
  rw [polyLine_eqN, lineLinks, List.length_map, List.length_range]

theorem continuous_sliceVN (β : ℝ) (P : Finset (LatticePlaquette 3 L)) :
    Continuous (sliceV (G := SUN N) L N β P) := by
  unfold sliceV xp
  refine continuous_finsetProd _ fun p _ => Real.continuous_exp.comp (continuous_const.mul
    (continuous_trN.comp ?_))
  show Continuous fun U : GaugeConnection (SUN N) 3 L => U (p.boundaryLinks 0) * U (p.boundaryLinks 1) *
    (U (p.boundaryLinks 2))⁻¹ * (U (p.boundaryLinks 3))⁻¹
  fun_prop

/-- The Polyakov ratio `Re tr(X P) / V`. -/
def polyRatioN (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (X : SUN N) (a : GaugeConnection (SUN N) 3 L) : ℝ :=
  polyObsN N L X a / sliceV L N β P a

theorem continuous_polyRatioN (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (X : SUN N) :
    Continuous (polyRatioN N L β P X) :=
  (continuous_polyObsN N L X).div (continuous_sliceVN N L β P) fun a => (sliceV_posN N L β P a).ne'

theorem bm_polyRatioN (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (X : SUN N) : BM (polyRatioN N L β P X) :=
  ⟨(continuous_polyRatioN N L β P X).measurable, isBdd_of_continuous (continuous_polyRatioN N L β P X)⟩

/-- The charge of the Polyakov ratio under the twist by `ω^{−k}`: `(Re tr(ω^{−k} P) − Re tr P)/V`. -/
theorem twDiff_polyRatioN (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (k : ZMod N)
    (a : GaugeConnection (SUN N) 3 L) :
    twDiff (flipG L (zN (-k)) c) (polyRatioN N L β P 1) a =
      (polyObsN N L (zN (-k)) a - polyObsN N L 1 a) / sliceV L N β P a := by
  unfold twDiff polyRatioN polyObsN
  rw [sliceMap_flipG, polyLine_flip L (zN_central (-k)), sliceV_flip L (zN_central (-k))]
  simp only [one_mul]
  rw [sub_div]

/-- One transfer step of the charge: `𝒦 (φ∘h − φ) = λ_N(β)^L κ (Re tr(ω^{−k} P) − Re tr P)`. -/
theorem kop_twDiffN (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (k : ZMod N)
    (a : GaugeConnection (SUN N) 3 L) :
    kop (sunW N L β P) (twDiff (flipG L (zN (-k)) c) (polyRatioN N L β P 1)) a =
      schurCN (N := N) β ^ L * lineConstN N L β * (polyObsN N L (zN (-k)) a - polyObsN N L 1 a) := by
  unfold kop
  have e : ∀ q : (FinLatticeSites 3 L → SUN N) × GaugeConnection (SUN N) 3 L,
      (sunW N L β P).K a q.1 q.2 * (sunW N L β P).V q.2 *
          twDiff (flipG L (zN (-k)) c) (polyRatioN N L β P 1) q.2 =
        stepK L N β a q.1 q.2 * polyObsN N L (zN (-k)) q.2 - stepK L N β a q.1 q.2 * polyObsN N L 1 q.2 := by
    intro q
    rw [twDiff_polyRatioN]
    show stepK L N β a q.1 q.2 * sliceV L N β P q.2 *
      ((polyObsN N L (zN (-k)) q.2 - polyObsN N L 1 q.2) / sliceV L N β P q.2) = _
    field_simp [(sliceV_posN N L β P q.2).ne']
    try ring
  simp_rw [e]
  have hcz : ∀ X : SUN N, Continuous fun q : (FinLatticeSites 3 L → SUN N) × GaugeConnection (SUN N) 3 L =>
      stepK L N β a q.1 q.2 * polyObsN N L X q.2 := fun X =>
    ((continuous_stepKN N L β).comp (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))).mul
      ((continuous_polyObsN N L X).comp continuous_snd)
  rw [integral_sub (integrable_of_continuous (hcz _)) (integrable_of_continuous (hcz _)),
    integral_prod _ (integrable_of_continuous (hcz _)), integral_prod _ (integrable_of_continuous (hcz _))]
  simp only [stepK_polyObsN N L (zN_central (-k)), stepK_polyObsN N L (fun g => Commute.one_left g)]
  simp only [integral_const, probReal_univ, one_smul]
  ring

theorem polyLine_one : polyLine L (1 : GaugeConnection (SUN N) 3 L) 0 = 1 := by
  unfold polyLine
  simp

/-- **The one-step non-degeneracy on SU(N)**, every `β ≠ 0`, `k ≠ 0`, `L ≥ 1`, `P`, `c`. -/
theorem sun_vip_twDiff [Fact (1 < N)] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L)
    {k : ZMod N} (hk : k ≠ 0) :
    vip (sunW N L β P) (twDiff (flipG L (zN (-k)) c) (polyRatioN N L β P 1))
      (kop (sunW N L β P) (twDiff (flipG L (zN (-k)) c) (polyRatioN N L β P 1))) ≠ 0 := by
  set D : GaugeConnection (SUN N) 3 L → ℝ := fun a => polyObsN N L (zN (-k)) a - polyObsN N L 1 a with hD
  have e : vip (sunW N L β P) (twDiff (flipG L (zN (-k)) c) (polyRatioN N L β P 1))
      (kop (sunW N L β P) (twDiff (flipG L (zN (-k)) c) (polyRatioN N L β P 1))) =
      schurCN (N := N) β ^ L * lineConstN N L β * ∫ a, D a ^ 2 ∂(sliceHaar (SUN N) (LatticeLink 3 L)) := by
    unfold vip
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    show twDiff (flipG L (zN (-k)) c) (polyRatioN N L β P 1) a *
        kop (sunW N L β P) (twDiff (flipG L (zN (-k)) c) (polyRatioN N L β P 1)) a * sliceV L N β P a = _
    rw [kop_twDiffN, twDiff_polyRatioN]
    simp only [hD]
    field_simp [(sliceV_posN N L β P a).ne']
    try ring
  rw [e]
  have hcD : Continuous D := (continuous_polyObsN N L _).sub (continuous_polyObsN N L _)
  have hsq : 0 < ∫ a, D a ^ 2 ∂(sliceHaar (SUN N) (LatticeLink 3 L)) := by
    refine integral_pos_of_continuous (hcD.pow 2) (fun a => sq_nonneg _) (x0 := 1) ?_
    have h1 : D 1 = gaugeReTr (SUN N) N (zN (-k)) - N := by
      simp only [hD, polyObsN, polyLine_one, mul_one, trN_one]
    rw [h1]
    exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.2 (reTr_zN_ne (neg_ne_zero.2 hk)))))
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (schurCN_ne_zero hβ)) (lineConstN_pos N L β).ne') hsq.ne'

/-- **The strict twist bound for SU(N): `Z_tw,k < Z`** for every `β ≠ 0`, every centre element `ω^k ≠ 1`, every
`L ≥ 1`, every even `T`, every spatial background twist `P`, every plane position `c`. -/
theorem sunZtw_lt [Fact (1 < N)] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L)
    {T : ℕ} [NeZero T] (hT : Even T) {k : ZMod N} (hk : k ≠ 0) : sunZtw N L β P c T k < sunZ N L β P T :=
  cZtw_lt_cZ_of_step_u (sunW N L β P) (flipG L (zN k) c) (flipG L (zN (-k)) c) hT
    (fun a b c => stepK_pos L β a b c) ((zFamN N L β P c).mp k) ((zFamN N L β P c).mp (-k))
    ((zFamN N L β P c).left_inv k) ((zFamN N L β P c).inv k) (bm_polyRatioN N L β P 1)
    (bm_twDiff _ (fun e => ((zFamN N L β P c).mp (-k) e).measurable) (bm_polyRatioN N L β P 1))
    (sun_vip_twDiff N L hβ P c hk)

/-- **The twist ratio `c_k = Z_tw,k / Z` lies strictly between 0 and 1** (SU(N), `β ≠ 0`, `k ≠ 0`, `T` even). -/
theorem sunTwistRatio_mem [Fact (1 < N)] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L)
    {T : ℕ} [NeZero T] (hT : Even T) {k : ZMod N} (hk : k ≠ 0) :
    0 < sunZtw N L β P c T k / sunZ N L β P T ∧ sunZtw N L β P c T k / sunZ N L β P T < 1 := by
  have hZ := sunZ_pos N L β P T
  refine ⟨div_pos (sunZtw_pos N L β P c T k) hZ, ?_⟩
  rw [div_lt_one hZ]
  exact sunZtw_lt N L hβ P c hT hk

/-! ### The electric sectors on the lattice -/

/-- **The SU(N) electric-sector partition function** `Z_e = (1/N) Σ_k ω^{−ek} Z_tw,k`. -/
def sunZe (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T] (e : ZMod N) : ℂ :=
  elecZ (sunZtw N L β P c T) e

/-- `Z_e` is real. -/
theorem sunZe_im (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ} [NeZero T] (hT : Even T)
    (e : ZMod N) : (sunZe N L β P c T e).im = 0 :=
  elecZ_im _ (sunZtw_neg N L β P c hT) e

/-- `Z_e = Z_{N−e}`. -/
theorem sunZe_neg (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ} [NeZero T] (hT : Even T)
    (e : ZMod N) : sunZe N L β P c T (-e) = sunZe N L β P c T e :=
  elecZ_neg _ (sunZtw_neg N L β P c hT) e

/-- **`Z_e ≥ 0`, by reflection positivity** (every `β`, every `e`, `T` even). -/
theorem sunZe_nonneg (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ} [NeZero T] (hT : Even T)
    (e : ZMod N) : 0 ≤ (sunZe N L β P c T e).re := by
  unfold sunZe
  rw [elecZ_eq, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))
    ((zFamN N L β P c).elec_nonneg hT (fun a b c => stepK_pos L β a b c) e)

/-- **`Σ_e Z_e = Z`.** -/
theorem sum_sunZe (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (T : ℕ) [NeZero T] :
    ∑ e, sunZe N L β P c T e = (sunZ N L β P T : ℂ) := by
  unfold sunZe
  rw [sum_elecZ, sunZtw_zero]

/-- **The twisted box carries electric flux**: for `β ≠ 0` some sector `e ≠ 0` has `Z_e > 0`. -/
theorem exists_sunZe_pos [Fact (1 < N)] {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L)
    {T : ℕ} [NeZero T] (hT : Even T) : ∃ e : ZMod N, e ≠ 0 ∧ 0 < (sunZe N L β P c T e).re := by
  by_contra hne
  simp only [not_exists, not_and, not_lt] at hne
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  -- `Re Z_0 = (1/N) Σ_k Z_tw,k < Z`
  have h0 : (sunZe N L β P c T 0).re = (N : ℝ)⁻¹ * ∑ k, sunZtw N L β P c T k := by
    unfold sunZe
    rw [elecZ_eq, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]
    congr 1
    rw [Complex.re_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul, Complex.ofReal_re]
  have hlt : ∑ k, sunZtw N L β P c T k < ∑ _k : ZMod N, sunZ N L β P T :=
    sum_lt_sum (fun k _ => sunZtw_le N L β P c hT k)
      ⟨1, mem_univ _, sunZtw_lt N L hβ P c hT one_ne_zero⟩
  rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul] at hlt
  have h0lt : (sunZe N L β P c T 0).re < sunZ N L β P T := by
    rw [h0, inv_mul_lt_iff₀ hN]; exact hlt
  have hsum := congrArg Complex.re (sum_sunZe N L β P c T)
  rw [Complex.re_sum, Complex.ofReal_re, ← add_sum_erase _ _ (mem_univ (0 : ZMod N))] at hsum
  have hrest : ∑ e ∈ univ.erase (0 : ZMod N), (sunZe N L β P c T e).re ≤ 0 :=
    sum_nonpos fun e he => hne e (ne_of_mem_erase he)
  linarith

end WilsonSUN

end ProofPhase.General
