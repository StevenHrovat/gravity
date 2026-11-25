/-
Proof phase, workstream 2 (Route B): the electric-flux energy from the 4D Wilson measure (free win 1, 2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/ws2-routeB/NOTE.md`, section 1.
-/

import ProofPhase.RouteB.Chain

/-!
# The flux energy as a decay rate on the real 4D Wilson measure (no temporal gauge, no Gauss projection)

**The lattice.** `ℤ/Tℤ × (ℤ/Lℤ)³` (time extent `T`, spatial box `L³`), as a time chain (`ProofPhase.RouteB.Chain`)
over the spatial graph `E = LatticeLink 3 L` (spatial links), `S = FinLatticeSites 3 L` (spatial sites). The plaquettes
of the 4D lattice are of two kinds, and the Wilson weight `∏_p e^{β s_p Re tr U_p}` is exactly the chain weight
`wilsonChain`:
* spatial plaquettes inside slice `t`: `sliceV β P a_t = ∏_{p} e^{β s_p Re tr U_p(a_t)}`, with `s_p = −1` on a set `P`
  of spatial plaquettes (a **magnetic twist**, e.g. the `xy`-plaquettes at `(x, y) = (L−1, L−1)` for all `z`; `P = ∅` is
  the periodic box) and `s_p = 1` otherwise;
* temporal plaquettes between slices `t` and `t+1`, one per spatial link `e` from `x` to `x + î`: holonomy
  `U_{(t,x),0} U_{(t+1,x),i} U_{(t,x+î),0}⁻¹ U_{(t,x),i}⁻¹ = b(x) c(e) b(x+î)⁻¹ a(e)⁻¹` (`tempHol`), weight `stepK`.
The reflection symmetry of `stepK` (`stepK_symm`) is conjugation invariance of `Re tr` plus `Re tr g⁻¹ = Re tr g`.

**The observable.** `polySum a = Σ_y Re tr P_y(a)`, the sum over all sites `y` of the slice of the Wilson line winding
once around the first spatial direction (`polyLine`). It is **centre-odd**: multiplying the first-direction links of the
plane `x₀ = c` by a central `z` with `rep z = −1` (for SU(2): `−1`) changes its sign (`polySum_flip`), while the weight
is unchanged (`sliceV_flip`, `stepK_flip`): it creates one unit of electric flux along the first axis.

**The flux energy** (`fluxRate`): for every time limit `h` of the normalised correlation `⟨Φ(a_t) Φ(a_0)⟩_T` as
`T → ∞` at fixed `L, β, P` (`IsFluxLimit`; limits exist, `exists_fluxLimit`), `fluxRate h = inf_s m_eff(s)`.
`fluxEnergy_props`: `h` is reflection-positive Hankel; either `h` vanishes from some even time on, or every
`h(2s) > 0`, the effective masses decrease to `fluxRate h ≥ 0`, and `|h(t)| ≤ h(0) e^{−fluxRate(h) t}` for all `t`
(no prefactor), with `fluxRate` the exact exponential rate (`RPSeq.rate_sharp`).

**Claim discipline (what is substantive, what is not).**
* Substantive (lattice, Lean): reflection positivity of the anisotropic Wilson measure with any spatial twist, the
  Hankel identity on it, and the closedness of the Hankel structure in the limit `T → ∞`: together they make the flux
  energy a well-defined, nonnegative, RP-controlled decay rate of the 4D measure, approached from above by effective
  masses.
* Group-blind: every statement holds for every compact group with a unitary representation (U(1), Z₂, finite subgroups
  of SU(2) included; for Z₂ and U(1) take any central `z` with `rep z = −1`). No statement is Yang–Mills-specific and none
  says `fluxRate > 0` (P1.7) or anything about its size or growth (P4.2).
* Not proved: the identification with `ProofPhase.fluxE` (the temporal-gauge transfer operator with Gauss-law states:
  `Z = tr(P_G Tⁿ)` and the spectral decomposition); uniqueness of the time limit (it holds when the transfer matrix has a
  simple top eigenvalue, Perron–Frobenius, not formalised). The proposal of the note is to use `fluxRate` itself as the
  flux energy of the assembly (it needs neither).
-/

open MeasureTheory Finset Filter Topology Positivity AreaLaw.Concrete

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.RouteB

section Wilson

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n]
variable (L : ℕ) [NeZero L]

/-- The sign of a spatial plaquette: `−1` on the twist set `P`, `+1` otherwise. -/
def twistSign (P : Finset (LatticePlaquette 3 L)) (p : LatticePlaquette 3 L) : ℝ := if p ∈ P then -1 else 1

theorem abs_twistSign (P : Finset (LatticePlaquette 3 L)) (p : LatticePlaquette 3 L) : |twistSign L P p| = 1 := by
  unfold twistSign; split_ifs <;> simp

/-- **The spatial plaquettes of one slice**, magnetic twist `P`: `∏_p e^{β s_p Re tr U_p}`. -/
def sliceV (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (a : GaugeConnection G 3 L) : ℝ :=
  ∏ p, Real.exp (β * twistSign L P p * xp n p a)

/-- The holonomy of the temporal plaquette over the spatial link `e` between slices with spatial links `a`, `c` and
temporal links `b`. -/
def tempHol (a : GaugeConnection G 3 L) (b : FinLatticeSites 3 L → G) (c : GaugeConnection G 3 L)
    (e : LatticeLink 3 L) : G :=
  b e.site * c e * (b e.target)⁻¹ * (a e)⁻¹

/-- **The temporal plaquettes between two slices**: `∏_e e^{β Re tr(tempHol)}`. -/
def stepK (n : ℕ) [HasGaugeTrace G n] (β : ℝ) (a : GaugeConnection G 3 L) (b : FinLatticeSites 3 L → G)
    (c : GaugeConnection G 3 L) : ℝ :=
  ∏ e, Real.exp (β * gaugeReTr G n (tempHol L a b c e))

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

include hU in
theorem stepK_symm (β : ℝ) (a : GaugeConnection G 3 L) (b : FinLatticeSites 3 L → G) (c : GaugeConnection G 3 L) :
    stepK L n β c (fun s => (b s)⁻¹) a = stepK L n β a b c := by
  unfold stepK
  refine prod_congr rfl fun e _ => ?_
  congr 2
  unfold tempHol
  have hid : (b e.site)⁻¹ * a e * ((b e.target)⁻¹)⁻¹ * (c e)⁻¹ =
      (b e.site)⁻¹ * (b e.site * c e * (b e.target)⁻¹ * (a e)⁻¹)⁻¹ * ((b e.site)⁻¹)⁻¹ := by group
  rw [hid, gaugeReTr_conj, gaugeReTr_inv_of_unitary hU]

include hc in
theorem measurable_sliceV (β : ℝ) (P : Finset (LatticePlaquette 3 L)) :
    Measurable (sliceV (G := G) L n β P) :=
  Finset.measurable_prod _ fun p _ =>
    Real.measurable_exp.comp (measurable_const.mul (measurable_xp hc p))

include hc in
theorem measurable_stepK (β : ℝ) :
    Measurable fun q : GaugeConnection G 3 L × (FinLatticeSites 3 L → G) × GaugeConnection G 3 L =>
      stepK L n β q.1 q.2.1 q.2.2 := by
  refine Finset.measurable_prod _ fun e _ => Real.measurable_exp.comp (measurable_const.mul ?_)
  exact (continuous_gaugeReTr hc).measurable.comp
    (((((measurable_pi_apply e.site).comp measurable_snd.fst).mul ((measurable_pi_apply e).comp measurable_snd.snd)).mul
      ((measurable_pi_apply e.target).comp measurable_snd.fst).inv).mul ((measurable_pi_apply e).comp measurable_fst).inv)

theorem exp_le_of_abs_le {β x : ℝ} {m : ℝ} (hx : |x| ≤ m) : Real.exp (β * x) ≤ Real.exp (|β| * m) := by
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)

include hU in
theorem sliceV_le (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (a : GaugeConnection G 3 L) :
    sliceV L n β P a ≤ Real.exp (|β| * n) ^ Fintype.card (LatticePlaquette 3 L) := by
  unfold sliceV
  rw [← Finset.card_univ, ← prod_const]
  refine Finset.prod_le_prod₀ (h0 := fun p _ => (Real.exp_pos _).le) (h1 := fun p _ => ?_)
  rw [mul_assoc]
  refine exp_le_of_abs_le ?_
  rw [abs_mul, abs_twistSign, one_mul]
  exact xp_abs_le hU p a

include hU in
theorem stepK_le (β : ℝ) (a : GaugeConnection G 3 L) (b : FinLatticeSites 3 L → G) (c : GaugeConnection G 3 L) :
    stepK L n β a b c ≤ Real.exp (|β| * n) ^ Fintype.card (LatticeLink 3 L) := by
  unfold stepK
  rw [← Finset.card_univ, ← prod_const]
  exact Finset.prod_le_prod₀ (h0 := fun e _ => (Real.exp_pos _).le)
    (h1 := fun e _ => exp_le_of_abs_le (abs_re_trace_le_of_unitary (hU _)))

/-- **The SU(2) (any compact group) Wilson action on `ℤ/Tℤ × (ℤ/Lℤ)³` as a chain weight**, coupling `β`, magnetic
twist `P`. -/
def wilsonChain (β : ℝ) (P : Finset (LatticePlaquette 3 L)) : ChainWeight G (LatticeLink 3 L) (FinLatticeSites 3 L) where
  V := sliceV L n β P
  K := stepK L n β
  measV := measurable_sliceV L hc β P
  measK := measurable_stepK L hc β
  V_nonneg a := prod_nonneg fun _ _ => (Real.exp_pos _).le
  K_nonneg a b c := prod_nonneg fun _ _ => (Real.exp_pos _).le
  V_bdd := ⟨_, sliceV_le L hU β P⟩
  K_bdd := ⟨_, stepK_le L hU β⟩
  K_symm a b c := stepK_symm L hU β a b c

/-! ## The centre-odd observable: the spatially summed Wilson line around the first spatial direction -/

/-- The `k`-th site of the line through `y` along the first spatial axis. -/
def lineSite (y : FinLatticeSites 3 L) (k : ℕ) : FinLatticeSites 3 L := Function.update y 0 (k : ZMod L)

/-- The Wilson line winding once around the first spatial direction, through the transverse position of `y`. -/
def polyLine (a : GaugeConnection G 3 L) (y : FinLatticeSites 3 L) : G :=
  ((List.range L).map fun k => a ⟨lineSite L y k, 0⟩).prod

/-- **The flux-creating observable** `Φ = Σ_y Re tr P_y`. -/
def polySum (n : ℕ) [HasGaugeTrace G n] (a : GaugeConnection G 3 L) : ℝ :=
  ∑ y : FinLatticeSites 3 L, gaugeReTr G n (polyLine L a y)

include hc in
theorem measurable_polySum : Measurable (polySum (G := G) L n) := by
  refine Finset.measurable_sum _ fun y _ => ?_
  refine (continuous_gaugeReTr hc).measurable.comp ?_
  exact (continuous_list_prod (f := fun k (a : GaugeConnection G 3 L) => a ⟨lineSite L y k, 0⟩) (List.range L)
    fun k _ => continuous_apply _).measurable

include hU in
theorem abs_polySum_le (a : GaugeConnection G 3 L) :
    |polySum L n a| ≤ n * Fintype.card (FinLatticeSites 3 L) := by
  unfold polySum
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ y, |gaugeReTr G n (polyLine L a y)| ≤ ∑ _y : FinLatticeSites 3 L, (n : ℝ) :=
        sum_le_sum fun y _ => abs_re_trace_le_of_unitary (hU _)
    _ = n * Fintype.card (FinLatticeSites 3 L) := by rw [sum_const, card_univ, nsmul_eq_mul]; ring

/-! ## Centre symmetry: the weight is invariant, `Φ` is odd -/

section Centre

variable {z : G} (hz : ∀ g : G, Commute z g)

/-- The centre flip of a slice: multiply the first-direction links of the plane `x₀ = c` by `z`. -/
def flipA (z : G) (c : ZMod L) (a : GaugeConnection G 3 L) : GaugeConnection G 3 L :=
  fun l => if l.dir = 0 ∧ l.site 0 = c then z * a l else a l

include hz in
theorem central_cancel₁ (x y w v : G) : z * x * y * (z * w)⁻¹ * v⁻¹ = x * y * w⁻¹ * v⁻¹ := by
  have e : z * x * y * (z * w)⁻¹ * v⁻¹ = z * (x * y * w⁻¹) * z⁻¹ * v⁻¹ := by group
  rw [e, (hz _).eq]; group

include hz in
theorem central_cancel₂ (x y w v : G) : x * (z * y) * w⁻¹ * (z * v)⁻¹ = x * y * w⁻¹ * v⁻¹ := by
  have e : x * (z * y) * w⁻¹ * (z * v)⁻¹ = (x * z) * (y * w⁻¹ * v⁻¹) * z⁻¹ := by group
  rw [e, ← (hz x).eq]
  have e2 : z * x * (y * w⁻¹ * v⁻¹) * z⁻¹ = z * (x * y * w⁻¹ * v⁻¹) * z⁻¹ := by group
  rw [e2, (hz _).eq]; group

include hz in
theorem plaquetteHolonomy_flipA (c : ZMod L) (a : GaugeConnection G 3 L) (p : LatticePlaquette 3 L) :
    plaquetteHolonomy (flipA L z c a) p = plaquetteHolonomy a p := by
  have h2 : p.dir2 ≠ 0 := p.dir2_ne_zero
  have hs2 : siteShift 3 L p.site p.dir2 0 = p.site 0 := siteShift_zero_of_ne _ h2
  have e1 : flipA L z c a (p.boundaryLinks 1) = a (p.boundaryLinks 1) := by
    simp [flipA, LatticePlaquette.boundaryLinks, h2]
  have e3 : flipA L z c a (p.boundaryLinks 3) = a (p.boundaryLinks 3) := by
    simp [flipA, LatticePlaquette.boundaryLinks, h2]
  by_cases h1 : p.dir1 = 0 ∧ p.site 0 = c
  · have e0 : flipA L z c a (p.boundaryLinks 0) = z * a (p.boundaryLinks 0) := by
      simp [flipA, LatticePlaquette.boundaryLinks, h1.1, h1.2]
    have e2 : flipA L z c a (p.boundaryLinks 2) = z * a (p.boundaryLinks 2) := by
      simp [flipA, LatticePlaquette.boundaryLinks, h1.1, hs2, h1.2]
    simp only [plaquetteHolonomy, e0, e1, e2, e3]
    exact central_cancel₁ hz _ _ _ _
  · have e0 : flipA L z c a (p.boundaryLinks 0) = a (p.boundaryLinks 0) := by
      unfold flipA
      split_ifs with h
      · exact absurd (by simpa [LatticePlaquette.boundaryLinks] using h) h1
      · rfl
    have e2 : flipA L z c a (p.boundaryLinks 2) = a (p.boundaryLinks 2) := by
      unfold flipA
      split_ifs with h
      · exact absurd (by simpa [LatticePlaquette.boundaryLinks, hs2] using h) h1
      · rfl
    simp only [plaquetteHolonomy, e0, e1, e2, e3]

include hz in
theorem sliceV_flip (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) (a : GaugeConnection G 3 L) :
    sliceV L n β P (flipA L z c a) = sliceV L n β P a := by
  unfold sliceV xp
  simp_rw [plaquetteHolonomy_flipA L hz]

include hz in
theorem stepK_flip (β : ℝ) (c : ZMod L) (a : GaugeConnection G 3 L) (b : FinLatticeSites 3 L → G)
    (c' : GaugeConnection G 3 L) : stepK L n β (flipA L z c a) b (flipA L z c c') = stepK L n β a b c' := by
  unfold stepK
  refine prod_congr rfl fun e _ => ?_
  congr 3
  unfold tempHol flipA
  split_ifs
  · exact central_cancel₂ hz _ _ _ _
  · rfl

include hz in
theorem prod_map_ite (q : ℕ → Bool) (g : ℕ → G) (l : List ℕ) :
    (l.map fun k => if q k then z * g k else g k).prod = z ^ (l.countP q) * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons k l ih =>
    have hc := ((hz (g k)).pow_left (l.countP q)).eq
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.countP_cons]
    by_cases hk : q k
    · simp only [hk, ite_true, pow_succ]
      rw [← (Commute.self_pow z (l.countP q)).eq]
      simp only [mul_assoc]
      rw [← mul_assoc (g k), ← hc, mul_assoc]
    · simp only [hk, Bool.false_eq_true, ite_false, add_zero]
      rw [← mul_assoc, ← hc, mul_assoc]

include hz in
theorem polyLine_flip (c : ZMod L) (a : GaugeConnection G 3 L) (y : FinLatticeSites 3 L) :
    polyLine L (flipA L z c a) y = z * polyLine L a y := by
  unfold polyLine
  have e : ((List.range L).map fun k => flipA L z c a ⟨lineSite L y k, 0⟩) =
      (List.range L).map fun k => if (k == c.val) then z * a ⟨lineSite L y k, 0⟩ else a ⟨lineSite L y k, 0⟩ := by
    refine List.map_congr_left fun k hk => ?_
    have hkL := List.mem_range.1 hk
    have hiff : ((k : ZMod L) = c) ↔ k = c.val := by
      constructor
      · intro h; rw [← h, ZMod.val_cast_of_lt hkL]
      · intro h; rw [h, ZMod.natCast_zmod_val]
    simp only [flipA, lineSite, Function.update_self, true_and, hiff, beq_iff_eq]
  rw [e, prod_map_ite hz]
  have h1 : (List.range L).countP (fun k => k == c.val) = 1 :=
    List.count_eq_one_of_mem List.nodup_range (List.mem_range.2 (ZMod.val_lt c))
  rw [h1, pow_one]

variable (hrep : HasGaugeTrace.rep (G := G) (n := n) z = -1)

include hrep in
theorem gaugeReTr_mul_central (g : G) : gaugeReTr G n (z * g) = -gaugeReTr G n g := by
  unfold gaugeReTr gaugeTrace
  rw [map_mul, hrep, neg_one_mul, Matrix.trace_neg, Complex.neg_re]

include hz hrep in
/-- **Φ is centre-odd.** -/
theorem polySum_flip (c : ZMod L) (a : GaugeConnection G 3 L) : polySum L n (flipA L z c a) = -polySum L n a := by
  unfold polySum
  rw [← Finset.sum_neg_distrib]
  refine sum_congr rfl fun y _ => ?_
  rw [polyLine_flip L hz, gaugeReTr_mul_central hrep]

end Centre

/-! ## The flux energy -/

variable [HasHaarProbability G] [(haarG G).IsInvInvariant]

/-- **`h` is a flux time limit**: a limit, as the time extent `T → ∞` along a subsequence, of the normalised correlation
`⟨Φ(a_t) Φ(a_0)⟩_T` of the Wilson measure on `ℤ/Tℤ × (ℤ/Lℤ)³` at coupling `β` with magnetic twist `P`. -/
def IsFluxLimit (β : ℝ) (P : Finset (LatticePlaquette 3 L)) (h : ℕ → ℝ) : Prop :=
  IsTimeLimit (wilsonChain L hc hU β P) (polySum L n) h

/-- **The flux energy** (lattice units) of a flux time limit: the decay rate of the centre-odd correlation. -/
def fluxRate (h : ℕ → ℝ) : ℝ := rate h

/-- Flux time limits exist. -/
theorem exists_fluxLimit (β : ℝ) (P : Finset (LatticePlaquette 3 L)) : ∃ h, IsFluxLimit L hc hU β P h :=
  exists_isTimeLimit _ (measurable_polySum L hc) (abs_polySum_le L hU)

/-- **The flux energy on the real 4D measure (free win 1).** For every flux time limit `h`: `h` is a
reflection-positive Hankel sequence; either it vanishes from some even time on (infinite energy), or all `h(2s) > 0`,
the effective masses `m(s) = ½ log(h(2s)/h(2s+2))` decrease and converge to `fluxRate h ≥ 0`, every effective mass is
an upper bound for it, and `|h(t)| ≤ h(0) e^{−fluxRate(h)·t}` for all `t` (no prefactor). -/
theorem fluxEnergy_props (β : ℝ) (P : Finset (LatticePlaquette 3 L)) {h : ℕ → ℝ} (hh : IsFluxLimit L hc hU β P h) :
    RPSeq h ∧
      ((∃ s, ∀ t, 2 * s ≤ t → h t = 0) ∨
        ((∀ s, 0 < h (2 * s)) ∧ 0 ≤ fluxRate h ∧ Antitone (effMass h) ∧
          Tendsto (effMass h) atTop (𝓝 (fluxRate h)) ∧ (∀ s, fluxRate h ≤ effMass h s) ∧
          ∀ t : ℕ, |h t| ≤ h 0 * Real.exp (-(fluxRate h * t)))) := by
  have H : RPSeq h := rpSeq_of_isTimeLimit _ (measurable_polySum L hc) (abs_polySum_le L hU) hh
  refine ⟨H, ?_⟩
  by_cases hz : ∃ s, h (2 * s) = 0
  · obtain ⟨s, hs⟩ := hz
    exact Or.inl ⟨s, fun t ht => H.eq_zero_of_le hs ht⟩
  · push Not at hz
    have hp : ∀ s, 0 < h (2 * s) := fun s => lt_of_le_of_ne (H.nonneg s) (hz s).symm
    exact Or.inr ⟨hp, H.rate_nonneg hp, H.effMass_antitone hp, H.tendsto_effMass hp, H.rate_le_effMass hp,
      H.abs_le_rate hp⟩

/-! ## Φ has mean zero on the 4D measure (centre symmetry), so its correlation is connected -/

/-- The centre flip on a chain configuration: every slice flipped (lipA), temporal links unchanged. -/
def flipCfg {T : ℕ} (z : G) (c : ZMod L) (U : CCfg G (LatticeLink 3 L) (FinLatticeSites 3 L) T) :
    CCfg G (LatticeLink 3 L) (FinLatticeSites 3 L) T
  | (t, .inl e) => if e.dir = 0 ∧ e.site 0 = c then z * U (t, .inl e) else U (t, .inl e)
  | (t, .inr s) => U (t, .inr s)

theorem sp_flipCfg {T : ℕ} (z : G) (c : ZMod L) (U : CCfg G (LatticeLink 3 L) (FinLatticeSites 3 L) T)
    (t : ZMod T) : sp (flipCfg L z c U) t = flipA L z c (sp U t) := rfl

theorem tm_flipCfg {T : ℕ} (z : G) (c : ZMod L) (U : CCfg G (LatticeLink 3 L) (FinLatticeSites 3 L) T)
    (t : ZMod T) : tm (flipCfg L z c U) t = tm U t := rfl

theorem measurePreserving_flipCfg [(haarG G).IsMulLeftInvariant] {T : ℕ} [NeZero T] (z : G) (c : ZMod L) :
    MeasurePreserving (flipCfg (T := T) L z c) (cHaar G (LatticeLink 3 L) (FinLatticeSites 3 L) T)
      (cHaar G (LatticeLink 3 L) (FinLatticeSites 3 L) T) := by
  have h := measurePreserving_pi (fun _ : CLink (LatticeLink 3 L) (FinLatticeSites 3 L) T => haarG G)
    (fun _ => haarG G)
    (f := fun l => match l with
      | (_, .inl e) => if e.dir = 0 ∧ e.site 0 = c then (z * ·) else id
      | (_, .inr _) => id) (fun l => by
      rcases l with ⟨t, e | s⟩
      · dsimp only
        split_ifs
        · exact measurePreserving_mul_left _ z
        · exact MeasurePreserving.id _
      · exact MeasurePreserving.id _)
  unfold cHaar
  convert h using 1
  funext U l
  rcases l with ⟨t, e | s⟩
  · simp only [flipCfg]; split_ifs <;> rfl
  · rfl

variable {z : G} (hz : ∀ g : G, Commute z g) (hrep : HasGaugeTrace.rep (G := G) (n := n) z = -1)

include hz in
theorem cweight_flipCfg (β : ℝ) (P : Finset (LatticePlaquette 3 L)) {T : ℕ} [NeZero T] (c : ZMod L)
    (U : CCfg G (LatticeLink 3 L) (FinLatticeSites 3 L) T) :
    cweight (wilsonChain L hc hU β P) (flipCfg L z c U) = cweight (wilsonChain L hc hU β P) U := by
  unfold cweight
  refine prod_congr rfl fun t _ => ?_
  show sliceV L n β P (sp (flipCfg L z c U) t) *
      stepK L n β (sp (flipCfg L z c U) t) (tm (flipCfg L z c U) t) (sp (flipCfg L z c U) (t + 1)) =
    sliceV L n β P (sp U t) * stepK L n β (sp U t) (tm U t) (sp U (t + 1))
  rw [sp_flipCfg, sp_flipCfg, tm_flipCfg, sliceV_flip L hz, stepK_flip L hz]

include hz hrep in
/-- **Centre symmetry of the 4D measure: ⟨Φ(a_t)⟩ = 0** (unnormalised, every time extent, every slice), for every
central z with ep z = −1. So the slice correlation of Φ is its connected correlation, and its decay rate is the
energy of the lowest state Φ creates from the vacuum: one unit of electric flux. -/
theorem polySum_mean_zero [(haarG G).IsMulLeftInvariant] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) {T : ℕ}
    [NeZero T] (t : ZMod T) :
    ∫ U, polySum L n (sp U t) * cweight (wilsonChain L hc hU β P) U
      ∂(cHaar G (LatticeLink 3 L) (FinLatticeSites 3 L) T) = 0 := by
  set g : CCfg G (LatticeLink 3 L) (FinLatticeSites 3 L) T → ℝ :=
    fun U => polySum L n (sp U t) * cweight (wilsonChain L hc hU β P) U with hg
  have mg : Measurable g := ((measurable_polySum L hc).comp (measurable_sp t)).mul (measurable_cweight _)
  have hflip : ∀ U, g (flipCfg L z 0 U) = -g U := by
    intro U
    simp only [hg, sp_flipCfg, polySum_flip L hz hrep, cweight_flipCfg L hc hU hz]
    ring
  have h := integral_comp_of_measurePreserving (measurePreserving_flipCfg L (T := T) z 0) mg.aestronglyMeasurable
  simp_rw [hflip, integral_neg] at h
  linarith

end Wilson

/-! ## SU(2) -/

open AreaLaw.Concrete in
/-- **The SU(2) flux energy, stated for the real SU(2) Wilson measure on `ℤ/Tℤ × (ℤ/Lℤ)³`.** -/
theorem su2_fluxEnergy_props (L : ℕ) [NeZero L] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) {h : ℕ → ℝ}
    (hh : IsFluxLimit (G := SU2) (n := 2) L continuous_subtype_val
      (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β P h) :
    RPSeq h ∧
      ((∃ s, ∀ t, 2 * s ≤ t → h t = 0) ∨
        ((∀ s, 0 < h (2 * s)) ∧ 0 ≤ fluxRate h ∧ Antitone (effMass h) ∧
          Tendsto (effMass h) atTop (𝓝 (fluxRate h)) ∧ (∀ s, fluxRate h ≤ effMass h s) ∧
          ∀ t : ℕ, |h t| ≤ h 0 * Real.exp (-(fluxRate h * t)))) :=
  fluxEnergy_props L _ _ β P hh

/-- **SU(2): the flux observable has mean zero** (centre element −1). -/
theorem su2_polySum_mean_zero (L : ℕ) [NeZero L] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) {T : ℕ} [NeZero T]
    (t : ZMod T) :
    ∫ U, polySum L 2 (sp U t) * cweight (wilsonChain (G := SU2) (n := 2) L continuous_subtype_val
      (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β P) U
      ∂(cHaar SU2 (LatticeLink 3 L) (FinLatticeSites 3 L) T) = 0 :=
  polySum_mean_zero L _ _ (z := negOneSU2)
    (fun g => Subtype.ext (show (-1 : Matrix (Fin 2) (Fin 2) ℂ) * g.val = g.val * -1 by simp)) rfl β P t

end ProofPhase.RouteB