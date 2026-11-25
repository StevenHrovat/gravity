/-
Proof phase, cycle 5, workstream 5 (the DMP-native line): the vacuum act number `z₀ = L · E₀(L)` on the real 4D SU(2)
Wilson measure, next to `fluxRate`; D-S and D-T as named hypotheses; the doubling theorem for the periodic boxes
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5e-dmp/NOTE.md`.
-/

import ProofPhase.RouteB.FluxEnergy
import ProofPhase.DMP.Doubling

/-!
# The vacuum act number on the lattice, and the doubling theorem for periodic boxes

**The lattice** is `ℤ/Tℤ × (ℤ/Lℤ)³` with `T → ∞` at fixed `L` (`ProofPhase.RouteB`'s time chain, the transfer-matrix
setting): `su2W L β P` is the SU(2) Wilson chain weight with magnetic twist `P` (`P = ∅`: the periodic box).

**Connected correlations** (new, generic). For a bounded measurable slice observable `f`, `connSeq` is the normalised slice
correlation of the centred observable `f − ⟨f⟩_T` at time extent `T_M = 2(M+1)`, where `⟨f⟩_T` is the normalised slice mean
(`nMean`); `IsConnLimit f h`: `h` is a pointwise limit of `connSeq` along a subsequence `T → ∞`. Limits exist
(`exists_isConnLimit`) and **every limit is a reflection-positive Hankel sequence** (`rpSeq_of_isConnLimit`), so the
effective-mass theory of `HankelRate` applies to it exactly as to `fluxRate`.

**The vacuum sector.** `VacObs L`: bounded measurable observables of one time slice that are **centre-even**, invariant under
multiplying the direction-`i` links of any plane `xᵢ = c` by the centre element `−1` (`centreFlip`), for all three
directions. This excludes the odd flux sectors (one torelon); it keeps everything else, in particular the zero-flux states and
flux pairs (two units of Z₂ flux are none).

**Gap predicates and numbers.** `DecayLB H E`: every `h ∈ H` obeys `|h t| ≤ h 0 · e^{−E t}` for all `t`. `gapOf H` is the
supremum of such `E`. For the periodic box:
* `E0 β L = gapOf (vacLimits β L)`: the **vacuum energy gap** of the box (lattice units), the best rate that bounds every
  connected vacuum-sector correlation; `z0 β L = L · E0 β L`: **the vacuum act number**.
* `Ee β L P = gapOf (fluxLimits β L P)`: the best uniform flux decay rate (`fluxRate` of every flux limit is `≥ Ee`,
  `Ee_le_fluxRate`); `ze β L P = L · Ee β L P`: **the flux act number**, the same object as `actRate` of `Objects.lean`.
* `E0_le_rate`: `E0` is a lower bound for the decay rate (`rate`) of every non-vanishing vacuum limit, and
  `decayLB_E0`/`decayLB_of_le_E0` say it is attained: **`E0` is exactly the box gap in the sense of decay rates.**

**Hypotheses (named, exact), for boxes of side `2ⁿ L₀` (`side L₀ n`), coupling `β`, flux twist family `P`.**
* `DS β P L₀ ζ₀ ζe` (D-S): `ζ₀ ≤ z0 β L₀ ∧ ζe ≤ ze β L₀ (P L₀)`.
* `DT β P L₀ ζ₀ ζe η` (D-T): `DoublingLaw` for `n ↦ z0 β (2ⁿL₀)` and `n ↦ ze β (2ⁿL₀) (P (2ⁿL₀))`.
* D-ID on the lattice is a theorem (`latticeBoxGaps`: the objects exist and the predicates are attained), at fixed `β`.

**Theorem (`su2_box_gap_of_DS_DT`).** `DS ∧ DT ∧ AdmissibleLoss η ⇒ ∃ m > 0, ∀ n`, every centre-even slice observable `f` of
the box `2ⁿL₀` and every connected time limit `h` of its correlation: `|h t| ≤ h 0 · e^{−m t}` for all `t`. That is: one
energy gap `m` (lattice units) for all dyadic periodic boxes. With `decay_of_limit` the bound passes to every limit of such
correlations as `n → ∞`.

**Claim discipline.** Substantive (Lean, lattice): connected correlations of the 4D SU(2) Wilson measure in a fixed box with
`T → ∞` are RP Hankel sequences, so `E0` is a well-defined box gap, attained, and the doubling theorem holds for it.
Definitional: that `z0 = L · E0` is "the act number" and that D-T is "the doubling law" (it is the gap along dyadic boxes,
`doubling_of_antitone_gap`). Group-blind: everything except the SU(2) instantiation holds for every compact group with a
central element of trace sign `−1`. Not formalised: the continuum (spacing first) version of D-ID; the order of limits
`T → ∞` then `L → ∞` against the symmetric tori of `MassGapMFLoc`; the identification of `E0` with the smallest nonzero
eigenvalue gap of the transfer matrix (Perron-Frobenius; not needed).
-/

open MeasureTheory Finset Filter Topology Positivity AreaLaw.Concrete ProofPhase.RouteB

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.DMP

/-! ## Connected correlations of a time chain -/

section Conn

variable {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G] [MeasurableInv G]
  [(haarG G).IsInvInvariant] {E S : Type*} [Fintype E] [Fintype S] (w : ChainWeight G E S)

/-- The normalised slice mean `⟨f(a_0)⟩_T`. -/
def nMean (T : ℕ) [NeZero T] (f : (E → G) → ℝ) : ℝ :=
  (∫ U, f (sp U 0) * cweight w U ∂(cHaar G E S T)) / cZ (T := T) w

theorem abs_nMean_le (T : ℕ) [NeZero T] {f : (E → G) → ℝ} {M : ℝ} (hM : ∀ a, |f a| ≤ M) :
    |nMean w T f| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (fun _ => 1))
  have hint : |∫ U, f (sp U 0) * cweight w U ∂(cHaar G E S T)| ≤ M * cZ (T := T) w := by
    unfold cZ
    rw [← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (Eventually.of_forall fun U => abs_nonneg _)
      ((IsBdd.integrable (cweight_isBdd w) (measurable_cweight w).aestronglyMeasurable).const_mul _)
      (Eventually.of_forall fun U => ?_))
    dsimp only
    rw [abs_mul, abs_of_nonneg (cweight_nonneg w U)]
    exact mul_le_mul_of_nonneg_right (hM _) (cweight_nonneg w U)
  unfold nMean
  rcases (cZ_nonneg (T := T) w).eq_or_lt with h | h
  · rw [← h, div_zero, abs_zero]; exact hM0
  · rw [abs_div, abs_of_pos h, div_le_iff₀ h]; exact hint

/-- The observable centred at `c`. -/
def centred (f : (E → G) → ℝ) (c : ℝ) : (E → G) → ℝ := fun a => f a - c

/-- **The connected slice correlation** at time extent `T_M = 2(M+1)`: the correlation of `f − ⟨f⟩_{T_M}`. -/
def connSeq (f : (E → G) → ℝ) (M t : ℕ) : ℝ :=
  nCorr (T := chainT M) w (centred f (nMean w (chainT M) f)) t

/-- **`h` is a connected time limit** of `f`: a pointwise limit of `connSeq` along a subsequence of time extents. -/
def IsConnLimit (f : (E → G) → ℝ) (h : ℕ → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ t, Tendsto (fun M => connSeq w f (φ M) t) atTop (𝓝 (h t))

theorem abs_centred_le {f : (E → G) → ℝ} {M c : ℝ} (hM : ∀ a, |f a| ≤ M) (hc : |c| ≤ M) (a : E → G) :
    |centred f c a| ≤ 2 * M := by
  unfold centred
  calc |f a - c| ≤ |f a| + |c| := abs_sub _ _
    _ ≤ 2 * M := by linarith [hM a]

theorem abs_connSeq_le {f : (E → G) → ℝ} (mf : Measurable f) {M : ℝ} (hM : ∀ a, |f a| ≤ M) (K t : ℕ) :
    |connSeq w f K t| ≤ (2 * M) ^ 2 :=
  abs_nCorr_le (T := chainT K) w (mf.sub measurable_const)
    (abs_centred_le hM (abs_nMean_le w (chainT K) hM)) t

/-- Connected time limits exist. -/
theorem exists_isConnLimit {f : (E → G) → ℝ} (mf : Measurable f) {M : ℝ} (hM : ∀ a, |f a| ≤ M) :
    ∃ h, IsConnLimit w f h := by
  obtain ⟨φ, hφ, h, ht⟩ := exists_limit (H := connSeq w f) (C := (2 * M) ^ 2) fun n t => abs_connSeq_le w mf hM n t
  exact ⟨h, φ, hφ, ht⟩

/-- **Every connected time limit is a reflection-positive Hankel sequence.** -/
theorem rpSeq_of_isConnLimit {f : (E → G) → ℝ} (mf : Measurable f) {M : ℝ} (hM : ∀ a, |f a| ≤ M) {h : ℕ → ℝ}
    (hh : IsConnLimit w f h) : RPSeq h := by
  obtain ⟨φ, hφ, ht⟩ := hh
  have hK : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_atTop_mono (fun n => Nat.le_succ n) tendsto_id
  have mc : ∀ c : ℝ, Measurable (centred f c) := fun c => mf.sub measurable_const
  have bc : ∀ n, IsBdd (centred f (nMean w (chainT n) f)) := fun n =>
    ⟨2 * M, fun a => by rw [Real.norm_eq_abs]; exact abs_centred_le hM (abs_nMean_le w (chainT n) hM) a⟩
  refine rpSeq_of_limit (H := connSeq w f) (K := fun n => n + 1) hK (C := (2 * M) ^ 2) (fun n j k hj hk => ?_)
    (fun n j hj => ?_) (fun n t => abs_connSeq_le w mf hM n t) hφ ht
  · exact nCorr_cs (T := chainT n) w (even_chainT n) (mc _) (bc n) (by rw [chainT_half]; exact hj)
      (by rw [chainT_half]; exact hk)
  · exact nCorr_nonneg (T := chainT n) w (even_chainT n) (mc _) (bc n) (by rw [chainT_half]; exact hj)

end Conn

/-! ## Gap predicates and their suprema (generic) -/

/-- **`E` is a uniform decay rate for the family `H`**: `|h t| ≤ h 0 · e^{−E t}` for all `h ∈ H`, `t`. -/
def DecayLB (H : Set (ℕ → ℝ)) (E : ℝ) : Prop := ∀ h ∈ H, ∀ t : ℕ, |h t| ≤ h 0 * Real.exp (-(E * t))

/-- **The gap of a family**: the supremum of its uniform decay rates. -/
def gapOf (H : Set (ℕ → ℝ)) : ℝ := sSup {E | DecayLB H E}

theorem DecayLB.mono {H : Set (ℕ → ℝ)} (h0 : ∀ h ∈ H, 0 ≤ h 0) {E E' : ℝ} (hE : DecayLB H E) (hle : E' ≤ E) :
    DecayLB H E' := fun h hh t =>
  (hE h hh t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith)) (h0 h hh))

theorem nonempty_bdd_of_gapOf_pos {H : Set (ℕ → ℝ)} (hpos : 0 < gapOf H) :
    {E | DecayLB H E}.Nonempty ∧ BddAbove {E | DecayLB H E} := by
  constructor
  · by_contra hS
    rw [Set.not_nonempty_iff_eq_empty] at hS
    rw [gapOf, hS, Real.sSup_empty] at hpos
    exact lt_irrefl _ hpos
  · by_contra hS
    rw [gapOf, csSup_of_not_bddAbove hS, Real.sSup_empty] at hpos
    exact lt_irrefl _ hpos

/-- **The gap is attained** when positive. -/
theorem decayLB_gapOf {H : Set (ℕ → ℝ)} (hpos : 0 < gapOf H) : DecayLB H (gapOf H) := by
  obtain ⟨hne, hbdd⟩ := nonempty_bdd_of_gapOf_pos hpos
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup hne hbdd
  intro h hh t
  have hlim : Tendsto (fun n => h 0 * Real.exp (-(u n * t))) atTop (𝓝 (h 0 * Real.exp (-(gapOf H * t)))) :=
    ((Real.continuous_exp.tendsto _).comp ((hu.mul_const _).neg)).const_mul _
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => huS n h hh t)

/-- Every uniform decay rate is at most the gap (when the rates are bounded). -/
theorem le_gapOf {H : Set (ℕ → ℝ)} (hb : BddAbove {E | DecayLB H E}) {E : ℝ} (hE : DecayLB H E) : E ≤ gapOf H :=
  le_csSup hb hE

/-- **The gap bounds every decay rate from below**: for an RP Hankel `h ∈ H` that does not vanish (`h(2s) > 0`), the
uniform rate `gapOf H` is at most `rate h`. -/
theorem gapOf_le_rate {H : Set (ℕ → ℝ)} (hpos : 0 < gapOf H) {h : ℕ → ℝ} (hh : h ∈ H) (hR : RPSeq h)
    (hp : ∀ s, 0 < h (2 * s)) : gapOf H ≤ rate h := by
  by_contra hlt
  push Not at hlt
  set g := gapOf H
  set ε := (g - rate h) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨s₀, hs₀⟩ := hR.rate_sharp hp hε0
  have hD := decayLB_gapOf hpos
  have h0pos : 0 < h 0 := by simpa using hp 0
  -- lower bound h(2(s₀+n)) ≥ h(2 s₀) e^{−2(rate+ε)n}, upper bound h(2(s₀+n)) ≤ h 0 e^{−2 g (s₀+n)}
  have key : ∀ n : ℕ, h (2 * s₀) * Real.exp (2 * g * s₀) ≤ h 0 * Real.exp (-(2 * (g - rate h - ε) * n)) := by
    intro n
    have lo := hs₀ n
    have up := (le_abs_self _).trans (hD h hh (2 * (s₀ + n)))
    have e1 : Real.exp (-(2 * (rate h + ε) * n)) * Real.exp (-(2 * (g - rate h - ε) * n)) =
        Real.exp (-(2 * g * n)) := by rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(g * ((2 * (s₀ + n) : ℕ) : ℝ))) = Real.exp (-(2 * g * s₀)) * Real.exp (-(2 * g * n)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    have hpos' : 0 < Real.exp (-(2 * (g - rate h - ε) * n)) := Real.exp_pos _
    have h3 : h (2 * s₀) * Real.exp (-(2 * g * n)) ≤ h 0 * Real.exp (-(2 * g * s₀)) * Real.exp (-(2 * g * n)) *
        Real.exp (-(2 * (g - rate h - ε) * n)) := by
      calc h (2 * s₀) * Real.exp (-(2 * g * n)) =
            h (2 * s₀) * Real.exp (-(2 * (rate h + ε) * n)) * Real.exp (-(2 * (g - rate h - ε) * n)) := by
            rw [mul_assoc (h (2 * s₀)), e1]
        _ ≤ h (2 * (s₀ + n)) * Real.exp (-(2 * (g - rate h - ε) * n)) :=
            mul_le_mul_of_nonneg_right lo hpos'.le
        _ ≤ h 0 * Real.exp (-(g * ((2 * (s₀ + n) : ℕ) : ℝ))) * Real.exp (-(2 * (g - rate h - ε) * n)) :=
            mul_le_mul_of_nonneg_right up hpos'.le
        _ = h 0 * Real.exp (-(2 * g * s₀)) * Real.exp (-(2 * g * n)) * Real.exp (-(2 * (g - rate h - ε) * n)) := by
            rw [e2]; ring
    have hEn : 0 < Real.exp (-(2 * g * n)) := Real.exp_pos _
    have h4 : h (2 * s₀) ≤ h 0 * Real.exp (-(2 * g * s₀)) * Real.exp (-(2 * (g - rate h - ε) * n)) := by
      have := h3
      rw [mul_comm (h 0 * Real.exp (-(2 * g * s₀))) (Real.exp (-(2 * g * n))), mul_assoc] at this
      nlinarith [this]
    have e3 : Real.exp (2 * g * s₀) * Real.exp (-(2 * g * s₀)) = 1 := by rw [← Real.exp_add]; simp
    calc h (2 * s₀) * Real.exp (2 * g * s₀) ≤
          h 0 * Real.exp (-(2 * g * s₀)) * Real.exp (-(2 * (g - rate h - ε) * n)) * Real.exp (2 * g * s₀) :=
          mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
      _ = h 0 * Real.exp (-(2 * (g - rate h - ε) * n)) * (Real.exp (2 * g * s₀) * Real.exp (-(2 * g * s₀))) := by ring
      _ = h 0 * Real.exp (-(2 * (g - rate h - ε) * n)) := by rw [e3, mul_one]
  have hlhs : 0 < h (2 * s₀) * Real.exp (2 * g * s₀) := mul_pos (hp s₀) (Real.exp_pos _)
  have hrate : 0 < 2 * (g - rate h - ε) := by rw [hε]; linarith
  have hlim : Tendsto (fun n : ℕ => h 0 * Real.exp (-(2 * (g - rate h - ε) * n))) atTop (𝓝 (h 0 * 0)) := by
    refine Tendsto.const_mul _ ?_
    have : Tendsto (fun n : ℕ => -(2 * (g - rate h - ε) * n)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hrate)
    exact Real.tendsto_exp_atBot.comp this
  rw [mul_zero] at hlim
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hlim).2 _ hlhs).exists
  linarith [key n]

/-! ## The periodic SU(2) box -/

/-- The SU(2) Wilson chain weight on `ℤ/Tℤ × (ℤ/Lℤ)³`, coupling `β`, magnetic twist `P`. -/
def su2W (L : ℕ) [NeZero L] (β : ℝ) (P : Finset (LatticePlaquette 3 L)) :
    ChainWeight SU2 (LatticeLink 3 L) (FinLatticeSites 3 L) :=
  wilsonChain (G := SU2) (n := 2) L continuous_subtype_val (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β P

/-- Multiply the direction-`i` links of the plane `xᵢ = c` by `z` (a centre transformation for central `z`). -/
def centreFlip {G : Type*} [Group G] {L : ℕ} (z : G) (i : Fin 3) (c : ZMod L) (a : GaugeConnection G 3 L) :
    GaugeConnection G 3 L :=
  fun l => if l.dir = i ∧ l.site i = c then z * a l else a l

/-- **Centre-even** slice observables: invariant under every centre flip (all three directions, all planes). -/
def CentreEven {G : Type*} [Group G] {L : ℕ} (z : G) (f : GaugeConnection G 3 L → ℝ) : Prop :=
  ∀ i c a, f (centreFlip z i c a) = f a

/-- **Vacuum-sector observables** of the box `L³`: bounded, measurable, centre-even slice observables. -/
structure VacObs (L : ℕ) where
  f : GaugeConnection SU2 3 L → ℝ
  meas : Measurable f
  bound : ℝ
  bdd : ∀ a, |f a| ≤ bound
  even : CentreEven negOneSU2 f

/-- The connected vacuum-sector time limits of the periodic box. -/
def vacLimits (β : ℝ) (L : ℕ) [NeZero L] : Set (ℕ → ℝ) :=
  {h | ∃ O : VacObs L, IsConnLimit (su2W L β ∅) O.f h}

/-- The flux time limits of the box with twist `P` (the objects of `fluxRate`). -/
def fluxLimits (β : ℝ) (L : ℕ) [NeZero L] (P : Finset (LatticePlaquette 3 L)) : Set (ℕ → ℝ) :=
  {h | IsFluxLimit (G := SU2) (n := 2) L continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) β P h}

theorem rpSeq_of_vacLimits {β : ℝ} {L : ℕ} [NeZero L] {h : ℕ → ℝ} (hh : h ∈ vacLimits β L) : RPSeq h := by
  obtain ⟨O, hO⟩ := hh
  exact rpSeq_of_isConnLimit _ O.meas O.bdd hO

theorem rpSeq_of_fluxLimits {β : ℝ} {L : ℕ} [NeZero L] {P : Finset (LatticePlaquette 3 L)} {h : ℕ → ℝ}
    (hh : h ∈ fluxLimits β L P) : RPSeq h :=
  (su2_fluxEnergy_props L β P hh).1

theorem nonneg_zero_of_rpSeq {h : ℕ → ℝ} (H : RPSeq h) : 0 ≤ h 0 := by simpa using H.nonneg 0

/-- **The vacuum energy gap** of the periodic box `L³` (lattice units). -/
def E0 (β : ℝ) (L : ℕ) [NeZero L] : ℝ := gapOf (vacLimits β L)

/-- **The vacuum act number** `z₀ = L · E₀(L)`. -/
def z0 (β : ℝ) (L : ℕ) [NeZero L] : ℝ := L * E0 β L

/-- **The flux energy gap** of the box with twist `P`: the best uniform decay rate of its flux limits. -/
def Ee (β : ℝ) (L : ℕ) [NeZero L] (P : Finset (LatticePlaquette 3 L)) : ℝ := gapOf (fluxLimits β L P)

/-- **The flux act number** `z_e = L · E_e(L)` (`actRate` of `Objects.lean`, made uniform over time limits). -/
def ze (β : ℝ) (L : ℕ) [NeZero L] (P : Finset (LatticePlaquette 3 L)) : ℝ := L * Ee β L P

/-- `E0` is attained: if positive, every vacuum-sector connected correlation decays at least at rate `E0`. -/
theorem decayLB_E0 {β : ℝ} {L : ℕ} [NeZero L] (hpos : 0 < E0 β L) : DecayLB (vacLimits β L) (E0 β L) :=
  decayLB_gapOf hpos

/-- Any smaller rate also bounds every vacuum-sector correlation. -/
theorem decayLB_of_le_E0 {β : ℝ} {L : ℕ} [NeZero L] (hpos : 0 < E0 β L) {m : ℝ} (hm : m ≤ E0 β L) :
    DecayLB (vacLimits β L) m :=
  (decayLB_E0 hpos).mono (fun _ hh => nonneg_zero_of_rpSeq (rpSeq_of_vacLimits hh)) hm

/-- **`E0` is the box gap**: no non-vanishing vacuum-sector correlation decays slower than `E0`. -/
theorem E0_le_rate {β : ℝ} {L : ℕ} [NeZero L] (hpos : 0 < E0 β L) {h : ℕ → ℝ} (hh : h ∈ vacLimits β L)
    (hp : ∀ s, 0 < h (2 * s)) : E0 β L ≤ rate h :=
  gapOf_le_rate hpos hh (rpSeq_of_vacLimits hh) hp

/-- The same for the flux gap: `Ee ≤ fluxRate h` for every non-vanishing flux limit. -/
theorem Ee_le_fluxRate {β : ℝ} {L : ℕ} [NeZero L] {P : Finset (LatticePlaquette 3 L)} (hpos : 0 < Ee β L P)
    {h : ℕ → ℝ} (hh : h ∈ fluxLimits β L P) (hp : ∀ s, 0 < h (2 * s)) : Ee β L P ≤ fluxRate h :=
  gapOf_le_rate hpos hh (rpSeq_of_fluxLimits hh) hp

/-! ## Dyadic boxes; D-ID on the lattice; D-S and D-T -/

/-- The side of the `n`-th dyadic box. -/
def side (L₀ n : ℕ) : ℕ := 2 ^ n * L₀

instance (L₀ n : ℕ) [NeZero L₀] : NeZero (side L₀ n) :=
  ⟨by unfold side; exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (NeZero.ne L₀)⟩

/-- **D-ID on the lattice is a theorem**: at fixed `β`, the dyadic periodic boxes with "every vacuum-sector correlation
decays at rate `E`" form a `BoxGaps` (downward closed, attained). -/
def latticeBoxGaps (β : ℝ) (L₀ : ℕ) [NeZero L₀] : BoxGaps where
  Q n E := DecayLB (vacLimits β (side L₀ n)) E
  mono _ _ _ hle hE := hE.mono (fun _ hh => nonneg_zero_of_rpSeq (rpSeq_of_vacLimits hh)) hle
  attained _ hpos := decayLB_gapOf hpos

theorem latticeBoxGaps_act (β : ℝ) (L₀ : ℕ) [NeZero L₀] (n : ℕ) :
    (latticeBoxGaps β L₀).act L₀ n = z0 β (side L₀ n) := by
  simp only [BoxGaps.act, BoxGaps.gap, latticeBoxGaps, z0, E0, gapOf, side]
  push_cast; ring

/-- **D-S** (start): at the box `L₀` both act numbers are above their thresholds. -/
def DS (β : ℝ) (P : (L : ℕ) → Finset (LatticePlaquette 3 L)) (L₀ : ℕ) [NeZero L₀] (ζ₀ ζe : ℝ) : Prop :=
  DoublingStart (fun n => z0 β (side L₀ n)) (fun n => ze β (side L₀ n) (P (side L₀ n))) ζ₀ ζe

/-- **D-T** (doubling law) along the dyadic boxes `2ⁿ L₀`, with loss `η`. -/
def DT (β : ℝ) (P : (L : ℕ) → Finset (LatticePlaquette 3 L)) (L₀ : ℕ) [NeZero L₀] (ζ₀ ζe : ℝ) (η : ℕ → ℝ) : Prop :=
  DoublingLaw (fun n => z0 β (side L₀ n)) (fun n => ze β (side L₀ n) (P (side L₀ n))) ζ₀ ζe η

/-- **The doubling theorem for the periodic SU(2) boxes.** D-S ∧ D-T with an admissible loss ⇒ one energy gap `m > 0` for
all dyadic periodic boxes: every connected time limit `h` of every centre-even slice observable of the box `2ⁿ L₀` obeys
`|h t| ≤ h 0 · e^{−m t}`; explicitly `m = (ζ₀ / L₀) e^{−2 Σ η}`. -/
theorem su2_box_gap_of_DS_DT {β : ℝ} {P : (L : ℕ) → Finset (LatticePlaquette 3 L)} {L₀ : ℕ} [NeZero L₀]
    {ζ₀ ζe : ℝ} {η : ℕ → ℝ} (hζ : 0 < ζ₀) (hη : AdmissibleLoss η) (hS : DS β P L₀ ζ₀ ζe) (hT : DT β P L₀ ζ₀ ζe η) :
    ∃ m : ℝ, 0 < m ∧ ∀ n, ∀ O : VacObs (side L₀ n), ∀ h, IsConnLimit (su2W (side L₀ n) β ∅) O.f h →
      ∀ t : ℕ, |h t| ≤ h 0 * Real.exp (-(m * t)) := by
  have hL : (0 : ℝ) < L₀ := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne L₀))
  have hact : (latticeBoxGaps β L₀).act L₀ = fun n => z0 β (side L₀ n) :=
    funext fun n => latticeBoxGaps_act β L₀ n
  have hS' : DoublingStart ((latticeBoxGaps β L₀).act L₀) (fun n => ze β (side L₀ n) (P (side L₀ n))) ζ₀ ζe := by
    rw [hact]; exact hS
  have hT' : DoublingLaw ((latticeBoxGaps β L₀).act L₀) (fun n => ze β (side L₀ n) (P (side L₀ n))) ζ₀ ζe η := by
    rw [hact]; exact hT
  obtain ⟨m, hm, hQ⟩ := (latticeBoxGaps β L₀).floor hL hζ hη hS' hT'
  exact ⟨m, hm, fun n O h hh t => hQ n h ⟨O, hh⟩ t⟩

end ProofPhase.DMP
