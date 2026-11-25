/-
SU(n) for every n ≥ 2 as a gauge group of the area-law project (2026-11-21). Released under Apache 2.0.

# SU(n), and SU(3) in particular

`Concrete.lean` treats SU(2) and U(n). Here the same instances are given for `SUn n = Matrix.specialUnitaryGroup (Fin n) ℂ`, every
`n`: topological group, compact, second countable, the defining representation (`HasGaugeTrace (SUn n) n`), normalised Haar measure
and its left invariance. The strong-coupling results that need no centre element then hold for SU(n) at once:

* `wilson_clustering_SUn`, `wilson_clustering_SU3`: exponential clustering (the strong-coupling gap) from
  `wilson_clustering_explicit`;
* `strong_coupling_has_reach_SUn`, `strong_coupling_existence_floor_SUn`, `strong_coupling_existence_floor_SU3`: the reach and the
  existence floor from `Reach.lean`.

The centre: `centreSUn n = ω · I` with `ω = e^{2πi/n}` (`omegaN`). `omegaN_pow : ω ^ n = 1`, `omegaN_ne_one : ω ≠ 1` for `n ≥ 2`,
`det (ω I) = ωⁿ = 1`, and `centreSUn_central`. This is the `Z_n` centre used by the centre-twist area law (`TwistAreaLaw.lean`).

The SU(3) statements are the strong-coupling regime of the gauge group of the strong force (known physics, Osterwalder–Seiler
1978); they say nothing about weak coupling or the continuum limit.
-/

import AreaLaw.Reach

open scoped Classical

open Finset MeasureTheory AreaLaw.Assembly AreaLaw.Clustering AreaLaw.Concrete AreaLaw.Reach

set_option linter.unusedSectionVars false

noncomputable section

namespace AreaLaw.ConcreteSUn

/-! ## The group SU(n) -/

/-- SU(n), with the topology and the (Borel) measurable structure inherited from the n × n complex matrices. -/
abbrev SUn (n : ℕ) : Type := Matrix.specialUnitaryGroup (Fin n) ℂ

instance (n : ℕ) : IsTopologicalGroup (SUn n) where
  continuous_mul := by
    apply continuous_induced_rng.2
    exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    apply continuous_induced_rng.2
    exact continuous_subtype_val.star

theorem isCompact_SUn (n : ℕ) :
    IsCompact (Matrix.specialUnitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  refine (isCompact_unitaryGroup n).of_isClosed_subset ?_
    (fun A hA => (Matrix.mem_specialUnitaryGroup_iff.mp hA).1)
  have hcl : IsClosed (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := isClosed_unitary
  have hdet : IsClosed {A : Matrix (Fin n) (Fin n) ℂ | A.det = 1} :=
    isClosed_eq continuous_id.matrix_det continuous_const
  convert hcl.inter hdet using 1
  ext A
  simp only [SetLike.mem_coe, Matrix.mem_specialUnitaryGroup_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]

instance (n : ℕ) : CompactSpace (SUn n) := isCompact_iff_compactSpace.mp (isCompact_SUn n)

instance (n : ℕ) : SecondCountableTopology (SUn n) :=
  inferInstanceAs (SecondCountableTopology (Matrix.specialUnitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)))

/-- The defining representation SU(n) ⊆ Mₙ(ℂ). -/
instance (n : ℕ) : HasGaugeTrace (SUn n) n := ⟨(Matrix.specialUnitaryGroup (Fin n) ℂ).subtype⟩

/-- Haar measure on SU(n), normalised to a probability measure. -/
instance (n : ℕ) : HasHaarProbability (SUn n) := haarProbability (SUn n)

instance (n : ℕ) : (haarG (SUn n)).IsMulLeftInvariant := by
  show (Measure.haarMeasure ⊤).IsMulLeftInvariant; infer_instance

theorem continuous_rep_SUn (n : ℕ) : Continuous (HasGaugeTrace.rep (G := SUn n) (n := n)) := continuous_subtype_val

theorem abs_reTr_SUn_le (n : ℕ) (g : SUn n) : |gaugeReTr (SUn n) n g| ≤ n :=
  abs_re_trace_le_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)

/-- `‖tr A‖ ≤ n` for a unitary `n × n` matrix. -/
theorem norm_trace_le_of_unitary {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    ‖A.trace‖ ≤ n := by
  calc ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := by unfold Matrix.trace; exact norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := sum_le_sum (fun i _ => entry_norm_bound_of_unitary hA i i)
    _ = n := by simp

theorem norm_trace_SUn_le (n : ℕ) (g : SUn n) : ‖gaugeTrace (SUn n) n g‖ ≤ n :=
  norm_trace_le_of_unitary (Matrix.specialUnitaryGroup_le_unitaryGroup g.2)

/-! ## The centre `Z_n`: `ω I` with `ω = e^{2πi/n}` -/

/-- The primitive `n`-th root of unity `ω = e^{2πi/n}`. -/
def omegaN (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

theorem omegaN_isPrimitiveRoot {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (omegaN n) n :=
  Complex.isPrimitiveRoot_exp n hn

/-- `ωⁿ = 1`. -/
theorem omegaN_pow (n : ℕ) : omegaN n ^ n = 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · exact (omegaN_isPrimitiveRoot h.ne').pow_eq_one

/-- `ω ≠ 1` for `n ≥ 2`. -/
theorem omegaN_ne_one {n : ℕ} (hn : 2 ≤ n) : omegaN n ≠ 1 :=
  (omegaN_isPrimitiveRoot (by omega)).ne_one (by omega)

theorem norm_omegaN (n : ℕ) : ‖omegaN n‖ = 1 := by
  unfold omegaN
  rw [Complex.norm_exp]
  have : (2 * Real.pi * Complex.I / n).re = 0 := by
    rw [show (2 * Real.pi * Complex.I / n : ℂ) = ((2 * Real.pi / n : ℝ) : ℂ) * Complex.I by push_cast; ring]
    simp
  rw [this, Real.exp_zero]

theorem star_omegaN_mul (n : ℕ) : star (omegaN n) * omegaN n = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, norm_omegaN]; simp

/-- `det (ω I) = ωⁿ = 1`. -/
theorem det_omegaN_smul_one (n : ℕ) : (omegaN n • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, omegaN_pow]

theorem omegaN_smul_one_mem (n : ℕ) :
    omegaN n • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.specialUnitaryGroup (Fin n) ℂ := by
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨?_, det_omegaN_smul_one n⟩
  rw [Matrix.mem_unitaryGroup_iff]
  rw [star_smul, star_one, smul_mul_smul_comm, one_mul, show omegaN n * star (omegaN n) = 1 by
    rw [mul_comm]; exact star_omegaN_mul n, one_smul]

/-- The centre element `ω I` of SU(n), `ω = e^{2πi/n}`. -/
def centreSUn (n : ℕ) : SUn n := ⟨omegaN n • 1, omegaN_smul_one_mem n⟩

theorem rep_centreSUn (n : ℕ) : HasGaugeTrace.rep (G := SUn n) (n := n) (centreSUn n) = omegaN n • 1 := rfl

/-- `ω I` is central. -/
theorem centreSUn_central (n : ℕ) (g : SUn n) : Commute (centreSUn n) g :=
  Subtype.ext (show omegaN n • (1 : Matrix (Fin n) (Fin n) ℂ) * g.val = g.val * omegaN n • 1 by simp)

/-- `(ω I)ⁿ = 1` in SU(n). -/
theorem centreSUn_pow (n : ℕ) : centreSUn n ^ n = 1 := by
  apply Subtype.ext
  show (omegaN n • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ n = 1
  rw [smul_pow, one_pow, omegaN_pow, one_smul]

/-- `ω I ≠ I` for `n ≥ 2`. -/
theorem centreSUn_ne_one {n : ℕ} (hn : 2 ≤ n) : centreSUn n ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : SUn n => (g.val : Matrix (Fin n) (Fin n) ℂ) ⟨0, by omega⟩ ⟨0, by omega⟩) h
  simp [centreSUn] at h1
  exact omegaN_ne_one hn h1

/-! ## Clustering, reach and the existence floor for SU(n) -/

variable {d N : ℕ}

/-- **Exponential clustering for SU(n) lattice gauge theory** (Wilson action `β Re tr U_p`, normalised Haar measure, periodic
    lattice `(ℤ/Nℤ)^d`): for `q = (16 d)² (1 − e^{−4n|β|}) < 1`, `|⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ 8 d |LF| q^r / (1 − q)`. -/
theorem wilson_clustering_SUn [NeZero N] (n : ℕ) (β : ℝ) (hq : qClust d n β < 1)
    {f g : GaugeConnection (SUn n) d N → ℝ} {LF LG : Finset (LatticeLink d N)}
    (hfd : LinkDep f LF) (hgd : LinkDep g LG) (mf : Measurable f) (mg : Measurable g)
    (hf1 : ∀ U, |f U| ≤ 1) (hg1 : ∀ U, |g U| ≤ 1) (hdisj : Disjoint LF LG) {r : ℕ}
    (hr : ∀ a ∈ touchPlaqs LF, ∀ b ∈ touchPlaqs LG, r ≤ (plaqGraph d N).dist a b) :
    0 < ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar (SUn n) d N) ∧
    |wilsonExpect n β (fun U => f U * g U) - wilsonExpect n β f * wilsonExpect n β g| ≤
      8 * d * LF.card * qClust d n β ^ r / (1 - qClust d n β) :=
  wilson_clustering_explicit (continuous_rep_SUn n) (abs_reTr_SUn_le n) β hq hfd hgd mf mg hf1 hg1 hdisj hr

/-- **Exponential clustering for SU(3) lattice gauge theory**: for `q = (16 d)² (1 − e^{−12|β|}) < 1`,
    `|⟨f g⟩ − ⟨f⟩⟨g⟩| ≤ 8 d |LF| q^r / (1 − q)`. -/
theorem wilson_clustering_SU3 [NeZero N] (β : ℝ) (hq : qClust d 3 β < 1)
    {f g : GaugeConnection (SUn 3) d N → ℝ} {LF LG : Finset (LatticeLink d N)}
    (hfd : LinkDep f LF) (hgd : LinkDep g LG) (mf : Measurable f) (mg : Measurable g)
    (hf1 : ∀ U, |f U| ≤ 1) (hg1 : ∀ U, |g U| ≤ 1) (hdisj : Disjoint LF LG) {r : ℕ}
    (hr : ∀ a ∈ touchPlaqs LF, ∀ b ∈ touchPlaqs LG, r ≤ (plaqGraph d N).dist a b) :
    0 < ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp 3 p U) ∂(productHaar (SUn 3) d N) ∧
    |wilsonExpect 3 β (fun U => f U * g U) - wilsonExpect 3 β f * wilsonExpect 3 β g| ≤
      8 * d * LF.card * qClust d 3 β ^ r / (1 - qClust d 3 β) :=
  wilson_clustering_SUn 3 β hq hfd hgd mf mg hf1 hg1 hdisj hr

/-- **SU(n) has reach at strong coupling**: `0 < q = (16 d)² (1 − e^{−4n|β|}) < 1` gives reach `ξ = 1 / log(1/q)`, uniformly in
    `N`. -/
theorem strong_coupling_has_reach_SUn (n : ℕ) (β : ℝ) (h0 : 0 < qClust d n β) (hq : qClust d n β < 1) :
    ∀ (N : ℕ) [NeZero N], HasReach (G := SUn n) (d := d) (N := N) (wilsonExpect n β) (1 / -Real.log (qClust d n β))
      (fun a _ => 8 * d * a / (1 - qClust d n β)) :=
  strong_coupling_has_reach (G := SUn n) (continuous_rep_SUn n) (abs_reTr_SUn_le n) β h0 hq

/-- **SU(3) has reach at strong coupling**: `0 < q = (16 d)² (1 − e^{−12|β|}) < 1` gives reach `ξ = 1 / log(1/q)`. -/
theorem strong_coupling_has_reach_SU3 (β : ℝ) (h0 : 0 < qClust d 3 β) (hq : qClust d 3 β < 1) :
    ∀ (N : ℕ) [NeZero N], HasReach (G := SUn 3) (d := d) (N := N) (wilsonExpect 3 β) (1 / -Real.log (qClust d 3 β))
      (fun a _ => 8 * d * a / (1 - qClust d 3 β)) :=
  strong_coupling_has_reach_SUn 3 β h0 hq

/-- **The existence floor for SU(n) at strong coupling**: existence at least `log(1/q)` in lattice units. -/
theorem strong_coupling_existence_floor_SUn (n : ℕ) (β : ℝ) (h0 : 0 < qClust d n β) (hq : qClust d n β < 1) :
    0 < -Real.log (qClust d n β) ∧
    (∀ (N : ℕ) [NeZero N], HasReach (G := SUn n) (d := d) (N := N) (wilsonExpect n β) (1 / -Real.log (qClust d n β))
      (fun a _ => 8 * d * a / (1 - qClust d n β))) ∧
    ∀ x e : ℝ, 0 < e → e ≤ 1 / -Real.log (qClust d n β) → x * e = 1 → -Real.log (qClust d n β) ≤ x :=
  strong_coupling_existence_floor (G := SUn n) (continuous_rep_SUn n) (abs_reTr_SUn_le n) β h0 hq

/-- **The existence floor for SU(3) at strong coupling** (the gauge group of the strong force): for
    `0 < q = (16 d)² (1 − e^{−12|β|}) < 1`, the Wilson measure has reach `1 / log(1/q)` uniformly in the lattice size, and existence
    is at least `log(1/q)` in lattice units. -/
theorem strong_coupling_existence_floor_SU3 (β : ℝ) (h0 : 0 < qClust d 3 β) (hq : qClust d 3 β < 1) :
    0 < -Real.log (qClust d 3 β) ∧
    (∀ (N : ℕ) [NeZero N], HasReach (G := SUn 3) (d := d) (N := N) (wilsonExpect 3 β) (1 / -Real.log (qClust d 3 β))
      (fun a _ => 8 * d * a / (1 - qClust d 3 β))) ∧
    ∀ x e : ℝ, 0 < e → e ≤ 1 / -Real.log (qClust d 3 β) → x * e = 1 → -Real.log (qClust d 3 β) ≤ x :=
  strong_coupling_existence_floor_SUn 3 β h0 hq

end AreaLaw.ConcreteSUn
