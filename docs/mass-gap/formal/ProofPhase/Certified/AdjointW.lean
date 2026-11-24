/-
Cycle 3, workstream 3 (c3c): the W₁ form of the adjoint half, with the certified window (2026-11-22).
Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/proof-phase/c3c-certified/NOTE.md`.
-/

import ProofPhase.Adjoint.CentreSplit
import OneScale.Lipschitz
import OneScale.LinkDist

/-!
# The adjoint half in W₁ form: the certified window of the two-coupling plaquette action

**Setting.** The coarse lattice at `L₁` is the 4D torus `(ℤ/Nℤ)⁴` with SU(2) links; the effective action is the
**two-coupling plaquette action** (Leg C's fitted family, `c2a-adjoint/NOTE.md` §1.2): the factor of the plaquette `p` is
`φ(t_p) = β_F t_p + (β_A/3)(4 t_p² − 1)`, `t_p = ½ Re tr U_p`; its centre-charged part is `β_F t_p`, its centre-blind
(adjoint) part `(β_A/3)(4 t_p² − 1) = (β_A/3) χ₁(U_p)`. The effective measure is `Z⁻¹ exp(∑_p φ(t_p)) ∏ dHaar`
(`Attempts.R3.gibbsMeasure`), and its single-link conditional laws are `Attempts.R3.siteSpec`. The cost on SU(2) is the
geodesic distance of `S³`, `geodSU2 a b = arccos(½ Re tr(a b⁻¹))`.

* `SiteInfluenceW`: single-link W influence bounds (`OneScale.IsInfluenceBoundW`) of the effective measure.
* `decay_of_siteW`: **Dobrushin's theorem with W₁ coefficients for single sites** (finite range): column sums
  `∑_{i ≠ z} k_{iz} ≤ γ` with `γ e^{λ D₁} < 1` give `|Cov(f, g)| ≤ D_c (1 − γ e^{λD₁})⁻¹ (∑ v_a) L_g e^{−λR}` for `f`
  bounded and `g` Lipschitz. A wrapper of `OneScale.BlockSpec.theoremA_W` with the single-site specification
  `Attempts.R3.factorSpec`.
* `twoCoupling`, `potential_twoCoupling`: the action as a local potential (measurable, bounded, local).
* **`CertifiedAdjointW`: the computational input, a single named hypothesis.** For each corner `c` of the certified
  window (`cornerA c`, `cornerF c`) and every action with `|β_A| ≤ cornerA c`, `|β_F| ≤ cornerF c`, on every torus with
  `N ≥ 2`, a link `z` influences a link `i` by at most `cornerK c` per plaquette they share (W₁, geodesic cost). What it
  asserts and how it is certified: NOTE.md §3 (an analytic reduction, proved on paper, to a supremum over the eigenvalues
  of the Bingham conditional laws, enclosed by interval arithmetic in `cert_adjoint.py`).
* `cornerColumn_lt_one`: `18 · cornerK c < 1` for every corner, **by `norm_num`**.
* **`limitDprimeW_twoCoupling`**: under `CertifiedAdjointW`, every action in the window satisfies the W₁ form of D′
  (`LimitDprimeW`: single-link W₁ influences, column sum `≤ γ < 1`, the same `γ` in every volume). With `β_F = 0` this is
  the **W₁ adjoint half** (the centre-charged part vanishes); with `β_F > 0` it bounds the sum of both halves.
* **`twoCoupling_decay`**: hence exponential decay of covariances of bounded and Lipschitz block observables, uniformly in
  the volume, at every rate `λ` with `18 · cornerK c · e^λ < 1`.

**Claim level.** Everything here is proved in Lean except `CertifiedAdjointW`, which is the computer-assisted statement
(paper reduction + interval arithmetic). The theorems are about the **two-coupling effective action** on the coarse
torus (SU(2), 4D, the fitted family), not about the Wilson measure: connecting them to Yang–Mills needs `H1` (that the
limit potentials at `L₁` are in this family or close to it in a Lipschitz norm) and `ObsTransfer`, which are open.

**Why not the sup-form `AdjointHalf` of `CentreSplit.lean`.** For this family the sup-form adjoint column is exactly
`18 tanh(2|β_A|/3)` (c2a §1.4), `< 1` iff `|β_A| < 0.0834`. The certified W₁ window reaches `|β_A| ≤ 0.21` (at `β_F = 0`); between the
two the sup-form `AdjointHalf` is false, so no certificate can imply it there. The W₁ form replaces it (NOTE.md §4).

**Unit tests.** The photon: U(1) has no adjoint part (`centreAvg_eq_zero_of_odd`), so the adjoint half passes it trivially;
the W₁ criterion with `β_F ≠ 0` is only certified for `|β_F| ≤ cornerF c ≤ 0.0685`, far below the U(1) weak-coupling
couplings, and the photon's own single-link W₁ column is `18 · (2/π) β ≥ 1` for `β ≥ π/36`
(`r2-curvature/NOTE.md` §2.4): it is excluded by the centre (fundamental) part, never by the adjoint half.
-/

open MeasureTheory Finset OneScale Attempts.R3 AreaLaw.Concrete

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Certified

/-! ## 1. Dobrushin's theorem with W₁ coefficients for single sites -/

section Generic

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace S] {X : Type*} [Fintype X]
  (ν : Measure S) [IsProbabilityMeasure ν]

/-- **Single-site W₁ influence bounds** of the effective measure `gibbsMeasure ν V` for the cost `c`: moving `z` by
`c`-distance `δ` moves the conditional law of `i` by at most `k i z · δ` in the dual (Kantorovich–Rubinstein) norm. -/
def SiteInfluenceW (supp : X → Finset ι) (V : X → (ι → S) → ℝ) (c : S → S → ℝ) (k : ι → ι → ℝ) : Prop :=
  ∀ i z, z ∉ ({i} : Finset ι) → IsInfluenceBoundW c {i} (siteSpec ν supp V i) z (k i z)

/-- **Dobrushin's theorem with W₁ coefficients, single sites, finite range.** -/
theorem decay_of_siteW [Nonempty ι] {supp : X → Finset ι} {V : X → (ι → S) → ℝ} (hV : Potential supp V)
    {c : S → S → ℝ} (hc0 : ∀ a b, 0 ≤ c a b) {Dc : ℝ} (hcD : ∀ a b, c a b ≤ Dc)
    {k : ι → ι → ℝ} (hk : SiteInfluenceW ν supp V c k) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hcol : ∀ z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)), k i z ≤ γ)
    (dist : ι → ι → ℝ) (hd0 : ∀ x, dist x x = 0) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z)
    {D₁ : ℝ} (hD₁ : ∀ i z, z ∉ ({i} : Finset ι) → k i z ≠ 0 → dist z i ≤ D₁)
    {lam : ℝ} (hlam : 0 ≤ lam) (hρ : γ * Real.exp (lam * D₁) < 1)
    {f g : (ι → S) → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset ι} (hfA : DepOn f A) (hgS : DepOn g Sg)
    {vf : ι → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : LipBound c g (fun _ => Lg))
    {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ dist a s) :
    |∫ σ, f σ * g σ ∂(gibbsMeasure ν V) - (∫ σ, f σ ∂(gibbsMeasure ν V)) * ∫ σ, g σ ∂(gibbsMeasure ν V)| ≤
      Dc / (1 - γ * Real.exp (lam * D₁)) * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  have := isProbabilityMeasure_gibbsMeasure ν hV
  set P := factorSpec ν supp V hV
  have hk' : ∀ j z, z ∉ P.block j → IsInfluenceBoundW c (P.block j) (P.spec j) z (k j z) := by
    intro j z hz
    rw [factorSpec_block] at hz ⊢
    rw [factorSpec_spec]
    exact hk j z hz
  have hcov : ∀ x, coverage P.block x = 1 := coverage_singleton
  have hgds : GDS P.block k γ := by
    intro z
    rw [hcov z, Nat.cast_one, mul_one]
    exact hcol z
  have h := P.theoremA_W hc0 hcD k hk' hγ0 hgds (cmin := 1) (cmax := 1) (b := 1) le_rfl
    (fun x => (hcov x).ge) (fun x => (hcov x).le) (fun j => by simp [P, factorSpec_block])
    dist hd0 htri (D₀ := 0) (D₁ := D₁)
    (fun j x hx y hy => by
      simp only [P, factorSpec_block, mem_singleton] at hx hy
      rw [hx, hy, hd0])
    (fun j x y hx hy hkx => by
      simp only [P, factorSpec_block, mem_singleton] at hy
      rw [hy]
      exact hD₁ j x (by simpa [P, factorSpec_block] using hx) hkx)
    hlam hρ hf hg hfA hgS hvf hLg hvg hR
  refine h.trans (le_of_eq ?_)
  simp only [Nat.cast_one, one_mul, sub_zero]

end Generic

/-! ## 2. The coarse two-coupling plaquette action -/

section TwoCoupling

variable {N : ℕ} [NeZero N]

/-- The defining representation of SU(2) is continuous. -/
theorem su2_rep_continuous : Continuous (HasGaugeTrace.rep (G := SU2) (n := 2)) := continuous_subtype_val

/-- The defining representation of SU(2) is unitary. -/
theorem su2_rep_unitary : ∀ g : SU2, HasGaugeTrace.rep (G := SU2) (n := 2) g ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2

/-- The plaquette variable `t_p = ½ Re tr U_p`. -/
def tp (p : LatticePlaquette 4 N) (U : GaugeConnection SU2 4 N) : ℝ := xp (G := SU2) 2 p U / 2

theorem abs_tp_le (p : LatticePlaquette 4 N) (U : GaugeConnection SU2 4 N) : |tp p U| ≤ 1 := by
  have h := OneScale.Gauge.abs_xp_le (G := SU2) (n := 2) su2_rep_unitary p U
  have h2 : |xp (G := SU2) 2 p U| ≤ 2 := by exact_mod_cast h
  unfold tp
  rw [abs_div, abs_two]
  linarith

/-- **The two-coupling plaquette factor** `φ(t_p) = β_F t_p + (β_A/3)(4 t_p² − 1)`. -/
def twoCoupling (βF βA : ℝ) (p : LatticePlaquette 4 N) (U : GaugeConnection SU2 4 N) : ℝ :=
  βF * tp p U + βA / 3 * (4 * tp p U ^ 2 - 1)

/-- The factor support: the four links of the plaquette. -/
abbrev plaqSupp : LatticePlaquette 4 N → Finset (LatticeLink 4 N) := fun p => plaqLinks p

theorem abs_twoCoupling_le (βF βA : ℝ) (p : LatticePlaquette 4 N) (U : GaugeConnection SU2 4 N) :
    |twoCoupling βF βA p U| ≤ |βF| + |βA| := by
  have ht := abs_tp_le p U
  have ht2 : tp p U ^ 2 ≤ 1 := by nlinarith [abs_le.1 ht, sq_abs (tp p U)]
  have h4 : |4 * tp p U ^ 2 - 1| ≤ 3 := abs_le.2 ⟨by nlinarith [sq_nonneg (tp p U)], by linarith⟩
  unfold twoCoupling
  calc |βF * tp p U + βA / 3 * (4 * tp p U ^ 2 - 1)|
      ≤ |βF * tp p U| + |βA / 3 * (4 * tp p U ^ 2 - 1)| := abs_add_le _ _
    _ = |βF| * |tp p U| + |βA| / 3 * |4 * tp p U ^ 2 - 1| := by
        rw [abs_mul, abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    _ ≤ |βF| * 1 + |βA| / 3 * 3 := by
        gcongr
    _ = |βF| + |βA| := by ring

/-- **The two-coupling action is a local potential** (measurable, bounded, each factor reads only its plaquette). -/
theorem potential_twoCoupling (βF βA : ℝ) : Potential (plaqSupp (N := N)) (twoCoupling βF βA) where
  meas p := by
    have h : Measurable (tp (N := N) p) := (measurable_xp su2_rep_continuous p).div_const 2
    exact (h.const_mul βF).add ((((h.pow_const 2).const_mul 4).sub_const 1).const_mul (βA / 3))
  bdd := ⟨|βF| + |βA|, fun p U => abs_twoCoupling_le βF βA p U⟩
  dep p U U' h := by
    have e : tp p U = tp p U' := by
      have hh : plaquetteHolonomy U p = plaquetteHolonomy U' p := plaquetteHolonomy_dependsOn p U U' h
      unfold tp xp
      rw [hh]
    unfold twoCoupling
    rw [e]

/-- The geodesic distance of `S³` on SU(2): `arccos(½ Re tr(a b⁻¹))`. -/
def geodSU2 (a b : SU2) : ℝ := Real.arccos (gaugeReTr SU2 2 (a * b⁻¹) / 2)

theorem geodSU2_nonneg (a b : SU2) : 0 ≤ geodSU2 a b := Real.arccos_nonneg _

theorem geodSU2_le_pi (a b : SU2) : geodSU2 a b ≤ Real.pi := Real.arccos_le_pi _

end TwoCoupling

/-! ## 3. The certified window -/

/-- Corners of the certified window: `|β_A| ≤ cornerA c`, `|β_F| ≤ cornerF c` (`window2.json`). -/
def cornerA : Fin 6 → ℝ := ![21 / 100, 20 / 100, 15 / 100, 10 / 100, 5 / 100, 0]

def cornerF : Fin 6 → ℝ := ![0, 20 / 10000, 145 / 10000, 265 / 10000, 425 / 10000, 685 / 10000]

/-- Certified per-plaquette W₁ influence bound at each corner, rounded up to `10⁻⁷` (NOTE.md §3–4, `window2.json`). -/
def cornerK : Fin 6 → ℝ :=
  ![555539 / 10000000, 551020 / 10000000, 554286 / 10000000, 547064 / 10000000, 553026 / 10000000, 550391 / 10000000]

theorem cornerK_nonneg (c : Fin 6) : 0 ≤ cornerK c := by
  fin_cases c <;> norm_num [cornerK]

/-- **The certified column sums are below `1`** (`norm_num`). -/
theorem cornerColumn_lt_one (c : Fin 6) : 18 * cornerK c < 1 := by
  fin_cases c <;> norm_num [cornerK]

/-- **The computational input (computer-assisted; NOTE.md §3, `cert_adjoint.py`, `cert_window.json`).** For every corner
`c`, every two-coupling action with `|β_A| ≤ cornerA c` and `|β_F| ≤ cornerF c`, and every torus `(ℤ/Nℤ)⁴` with `N ≥ 2`:
a link `z` influences the single-link conditional law of a link `i` by at most `cornerK c` per plaquette containing both
(W₁ for the geodesic cost). -/
def CertifiedAdjointW : Prop :=
  ∀ (c : Fin 6) (N : ℕ) [NeZero N], 2 ≤ N → ∀ βF βA : ℝ, |βA| ≤ cornerA c → |βF| ≤ cornerF c →
    SiteInfluenceW (haarG SU2) (plaqSupp (N := N)) (twoCoupling βF βA) geodSU2
      (fun i z => cornerK c * OneScale.SingleLink.common i z)

/-- The column sum of the certified coefficients: at most `18 · cornerK c` (each link shares a plaquette with at most
18 others, counted with multiplicity). -/
theorem column_le {N : ℕ} [NeZero N] (c : Fin 6) (z : LatticeLink 4 N) :
    ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (LatticeLink 4 N))),
      cornerK c * (OneScale.SingleLink.common i z : ℝ) ≤ 18 * cornerK c := by
  rw [← mul_sum, mul_comm (18 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (cornerK_nonneg c)
  have h := OneScale.SingleLink.sum_common_le (d := 4) (N := N) z
  have h' : ((∑ e ∈ univ.filter (fun e => z ∉ ({e} : Finset (LatticeLink 4 N))),
      OneScale.SingleLink.common e z : ℕ) : ℝ) ≤ 18 := by exact_mod_cast h
  simpa [Nat.cast_sum] using h'

/-- Links with a positive certified coefficient share a plaquette, so they are at distance at most `1`. -/
theorem dist_le_of_common {N : ℕ} [NeZero N] (c : Fin 6) {i z : LatticeLink 4 N}
    (h : cornerK c * (OneScale.SingleLink.common i z : ℝ) ≠ 0) : OneScale.LinkDist.linkDist z i ≤ 1 := by
  have hc : OneScale.SingleLink.common i z ≠ 0 := by
    intro h0; apply h; rw [h0, Nat.cast_zero, mul_zero]
  obtain ⟨p, hp⟩ := Finset.card_ne_zero.1 hc
  simp only [mem_filter, mem_univ, true_and] at hp
  exact OneScale.LinkDist.linkDist_le_one_of_plaq hp.1 hp.2

/-- **D′ in W₁ form, single links, uniform in the volume** (the W₁ analogue of `LimitDprime`): for each coarse volume
`j` the single-link W₁ influences of the effective measure of `V j` have column sums `≤ γ < 1` and range `1`. With a
centre-blind `V` (β_F = 0) this is the W₁ adjoint half. -/
def LimitDprimeW (V : ∀ j : ℕ, LatticePlaquette 4 (coarseSide j) → GaugeConnection SU2 4 (coarseSide j) → ℝ) :
    Prop :=
  ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∀ j, ∃ k : LatticeLink 4 (coarseSide j) → LatticeLink 4 (coarseSide j) → ℝ,
    SiteInfluenceW (haarG SU2) (plaqSupp (N := coarseSide j)) (V j) geodSU2 k ∧
    (∀ z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset _)), k i z ≤ γ) ∧
    (∀ i z, k i z ≠ 0 → OneScale.LinkDist.linkDist z i ≤ 1)

theorem two_le_coarseSide (j : ℕ) : 2 ≤ coarseSide j := by unfold coarseSide; omega

/-- **The certified window gives the W₁ form of D′ (the W₁ adjoint half, and with `β_F > 0` both halves together)**
for every two-coupling action in the window, in every coarse volume, with `γ = 18 · cornerK c < 1`. -/
theorem limitDprimeW_twoCoupling (hcert : CertifiedAdjointW) (c : Fin 6) {βF βA : ℝ} (hA : |βA| ≤ cornerA c)
    (hF : |βF| ≤ cornerF c) : LimitDprimeW (fun _ => twoCoupling βF βA) :=
  ⟨18 * cornerK c, mul_nonneg (by norm_num) (cornerK_nonneg c), cornerColumn_lt_one c, fun j =>
    ⟨fun i z => cornerK c * OneScale.SingleLink.common i z, hcert c (coarseSide j) (two_le_coarseSide j) βF βA hA hF,
      fun z => column_le c z, fun i z h => dist_le_of_common c h⟩⟩

/-- **Exponential decay for every two-coupling action in the certified window**, uniformly in the torus size `N ≥ 2`:
for `f` bounded (single-link oscillations `v`) depending on `A`, `g` Lipschitz (constant `L_g` per link for the geodesic
cost) depending on `S_g`, at link distance `≥ R`, and every `λ ≥ 0` with `18 · cornerK c · e^λ < 1`:
`|Cov(f, g)| ≤ π (1 − 18 · cornerK c · e^λ)⁻¹ (∑ v_a) L_g e^{−λR}`. -/
theorem twoCoupling_decay (hcert : CertifiedAdjointW) (c : Fin 6) {N : ℕ} [NeZero N] (hN : 2 ≤ N) {βF βA : ℝ}
    (hA : |βA| ≤ cornerA c) (hF : |βF| ≤ cornerF c) {lam : ℝ} (hlam : 0 ≤ lam)
    (hρ : 18 * cornerK c * Real.exp lam < 1)
    {f g : GaugeConnection SU2 4 N → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset (LatticeLink 4 N)} (hfA : DepOn f A)
    (hgS : DepOn g Sg) {vf : LatticeLink 4 N → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg)
    (hvg : LipBound geodSU2 g (fun _ => Lg)) {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ OneScale.LinkDist.linkDist a s) :
    |∫ σ, f σ * g σ ∂(gibbsMeasure (haarG SU2) (twoCoupling βF βA)) -
        (∫ σ, f σ ∂(gibbsMeasure (haarG SU2) (twoCoupling βF βA))) *
          ∫ σ, g σ ∂(gibbsMeasure (haarG SU2) (twoCoupling βF βA))| ≤
      Real.pi / (1 - 18 * cornerK c * Real.exp lam) * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  have : Nonempty (LatticeLink 4 N) := ⟨⟨0, 0⟩⟩
  have h := decay_of_siteW (haarG SU2) (potential_twoCoupling (N := N) βF βA) geodSU2_nonneg geodSU2_le_pi
    (hcert c N hN βF βA hA hF) (mul_nonneg (by norm_num) (cornerK_nonneg c)) (fun z => column_le c z)
    OneScale.LinkDist.linkDist OneScale.LinkDist.linkDist_self OneScale.LinkDist.linkDist_triangle (D₁ := 1)
    (fun i z _ h => dist_le_of_common c h) hlam (by rw [mul_one]; exact hρ) hf hg hfA hgS hvf hLg hvg hR
  simpa only [mul_one] using h

/-- A positive rate exists at every corner. -/
theorem exists_rate_corner (c : Fin 6) : ∃ lam : ℝ, 0 < lam ∧ 18 * cornerK c * Real.exp lam < 1 :=
  OneScale.SingleLink.exists_rate (mul_nonneg (by norm_num) (cornerK_nonneg c)) (cornerColumn_lt_one c)

end ProofPhase.Certified
