/-
Proof phase (round 5), the assembly theorem (2026-11-22). Released under Apache 2.0.

Field-by-field map to the blueprint: `docs/mass-gap/weak-coupling/proof-phase/ASSEMBLY.md`.
-/

import ProofPhase.Objects
import Attempts.R3.Robust

/-!
# The assembly: SU(2) Yang–Mills inside the hypotheses, every open piece a named hypothesis, the mass gap as conclusion

**The open pieces** (`OpenPieces T` for a tuning `T`, all about the objects of `ProofPhase.Objects`):

* `lcp : OnLCP T` — **P6.6** (and P1.7 in its finite-volume form): the family lies on a line of constant physics:
  (i) `ℓ_k → ∞` (the lattice spacing `a_k = L₁/ℓ_k` goes to zero), (ii) the bare coupling follows the one-loop running of
  SU(2), `β_k / log ℓ_k → 11/(3π²)` (asymptotic freedom; `β = 4/g²`, `b₀ = 11/(24π²)`), (iii) the renormalisation
  condition: the act number of the box of side `L₁`, `z_k = ℓ_k · E_e(β_k, ℓ_k)` (Gauss-law flux energy of the transfer
  operator, `ProofPhase.actZ`), converges to a value `z⋆ > 0`. (iii) is what makes `L₁` a physical length.
* `nontrivial : NonTrivial T` — **P6.2** (identification, non-triviality part): some slab correlation at a positive
  physical time has all its continuum limit points bounded away from zero (the limit is not pure noise, not ultralocal).
* `crossover : SlabDecay T ∨ (ConjW T ∧ SectorTransfer T)` — the two routes through the crossover:
  * **Route A, `SlabDecay T`** (P4.1 in gap strength, after the round-4 review): the reflected slab correlations of the
    SU(2) Wilson measure along `T` decay at one physical rate `m > 0`, with any constant depending on the level (not on
    the volume), from some level on. Exactly gap strength: Theorem C (reflection positivity, `OneScale.TorusRP`) removes
    the constant (`latticeGap_of_slabDecay`). D′ is one sufficient condition for it, proved as a lemma
    (`slabDecay_of_uniformGDS`: the fine-level worst-case Dobrushin condition with thin cubes of physical size `L₀`).
  * **Route B, `ConjW T ∧ SectorTransfer T`** (P4.2 + P5.1): Conjecture W in doubling form along the line (the act number
    grows by a factor `(1+δ)²` per doubling of the box, at every level), and the sector transfer: flux confinement
    (`FluxGrowth`) implies `MassGap`. The Lean content of route B is only `fluxGrowth_of_conjW` (W + the renormalisation
    condition ⇒ geometric growth of the act number); **P5.1 carries the whole vacuum-sector content and is stated as an
    implication because no weaker precise form is known.** Route B does not use any of route A's Lean.

**The theorems.**
* `assembly_routeA : OnLCP T → SlabDecay T → MassGap T ∧ LatticeGap T ∧ LimitRP T` (route A).
* `assembly_routeB : OnLCP T → ConjW T → SectorTransfer T → MassGap T ∧ LimitRP T` (route B).
* **`yang_mills_assembly : OpenPieces T → MassGap T ∧ LimitRP T ∧ NonTrivial T`** (the top-level theorem, by cases on the
  route; `NonTrivial` is passed through, it is not derived).
* `not_trivial`: the pure-noise family `β_k = 0` (and every family with bounded bare coupling, strong coupling included)
  does **not** satisfy `OpenPieces` (it fails P6.6 (ii)). `slabDecay`-type decay alone does not exclude it: pure noise has
  an infinite gap; the identification with Yang–Mills sits in P6.6 and P6.2, which is why they are fields.
* `bareRunning_witness`: P6.6 (i)–(ii) are satisfiable (an explicit tuning); no witness is given for (iii), P6.2,
  `SlabDecay`, `ConjW`, `SectorTransfer` (joint consistency of the fields is the open problem itself).

**What is used.** `OnLCP` (i) is used by both routes (`a_k → 0`), (iii) by route B; (ii) and `NonTrivial` are not used by
any proof: they are there so that the hypotheses identify Yang–Mills (without them a mistuned or trivial family would
satisfy the rest). Reflection positivity of the limit (`LimitRP`) is proved, not assumed.

**Not fields, and why** (see `ASSEMBLY.md`): Euclidean (rotation) invariance P6.4 and the Osterwalder–Schrader
regularity/reconstruction P6.5 cannot be stated about these objects (rotations act on continuum fields; the lattice has
only the hypercubic group); the conclusion does not claim them. Uniqueness of the limit (the other half of P6.2) cannot be
stated for arbitrary observable families either (it needs a notion of "the same observable at every level").
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift OneScale.CorollaryB OneScale.CubeChain Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase

/-! ## P6.6: the line of constant physics -/

/-- The one-loop slope of the SU(2) bare coupling: `β = 4/g²`, `1/g²(1/a) ≈ 2 b₀ log(1/(aΛ))`, `b₀ = 11/(24π²)`, so
`β_k ≈ 8 b₀ log ℓ_k = (11/(3π²)) log ℓ_k`. -/
def oneLoopSlope : ℝ := 11 / (3 * Real.pi ^ 2)

theorem oneLoopSlope_pos : 0 < oneLoopSlope := by unfold oneLoopSlope; positivity

/-- **P6.6, the line of constant physics (open).** (i) the resolution `ℓ_k → ∞`; (ii) asymptotic freedom of the bare
coupling, `β_k / log ℓ_k → 11/(3π²)`; (iii) the renormalisation condition: the act number of the box of physical side
`L₁` converges to some `z⋆ > 0` (this fixes `L₁` as a physical length, and contains P1.7, strict `E_e > 0`, eventually). -/
structure OnLCP (T : Tuning) : Prop where
  resolution : Tendsto T.ℓ atTop atTop
  running : Tendsto (fun k => T.β k / Real.log (T.ℓ k)) atTop (𝓝 oneLoopSlope)
  scheme : ∃ zstar : ℝ, 0 < zstar ∧ Tendsto (fun k => actZ (T.β k) (T.box k 0)) atTop (𝓝 zstar)

theorem OnLCP.tendsto_a {T : Tuning} (h : OnLCP T) : Tendsto T.a atTop (𝓝 0) := by
  have h1 : Tendsto (fun k => (T.ℓ k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp h.resolution
  show Tendsto (fun k => T.L₁ / (T.ℓ k : ℝ)) atTop (𝓝 0)
  exact h1.const_div_atTop T.L₁

/-! ## P6.2: non-triviality of the limit -/

/-- **P6.2, non-triviality (open).** There is a slab observable family and a physical time `τ > 0` at which every
continuum limit point (volume first, then spacing) of the reflected correlation has modulus at least `c > 0`: the
limit is not pure noise. -/
def NonTrivial (T : Tuning) : Prop :=
  ∃ (s : ℝ) (V : ℕ → ℕ) (O : SlabObs T s V) (τ c : ℝ), 0 < τ ∧ 0 < c ∧ ∀ (h : ℕ → ℝ) (g : ℝ),
    (∀ k, IsLimitPoint (fun j => T.wcorr k j (O.F k j) (T.steps k τ)) (h k)) → IsLimitPoint h g → c ≤ |g|

/-! ## Route A: slab decay at one physical rate -/

/-- **Route A's crossover piece in gap strength (open).** One physical rate `m > 0`; for every thickness `s` and support
bound `V`, from some level `k₀` on there is a constant `C` (depending on the level, not on the volume) such that on every
torus and for every slab observable, `|Cov(F ∘ S_n, F ∘ Θ)| ≤ C e^{-m n a_k}` whenever `2n + 2⌈s/a_k⌉ + 2 ≤ N`. -/
def SlabDecay (T : Tuning) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ (s : ℝ) (V : ℕ → ℕ), ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (j : ℕ) (O : SlabObs T s V) (n : ℕ), 2 * n + 2 * T.thick k s + 2 ≤ T.side k j →
      |T.wcorr k j (O.F k j) n| ≤ C * Real.exp (-(m * (n * T.a k)))

section FiniteVolume

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {n : ℕ} [HasGaugeTrace G n] [HasHaarProbability G] [(haarG G).IsInvInvariant]
variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ) (hN : Even N)

include hc hU hN in
/-- **Theorem C removes the constant** (finite volume, additive error). If the reflected correlation of a slab
observable `|F| ≤ 1` on `[0, s]` decays like `C e^{-λ t}` for all `t` with `2t + 2s + 2 ≤ N`, then for `r ≥ 1` and
`N ≥ 2^{r+1} t + 2s + 2`: `|H(t)| ≤ (2 + 2^{-r} C) e^{-λ t}`. -/
theorem corr_le_of_decay {φ : ℝ → ℝ} (hφ : PosWeight n φ) {F : GaugeConnection G d N → ℝ} (hFm : Measurable F)
    (hF1 : ∀ U, |F U| ≤ 1) {s : ℕ} (hFs : DepOn F (timeSlab 0 s)) {C lam : ℝ} (hC : 0 ≤ C)
    (hdec : ∀ t : ℕ, 2 * t + 2 * s + 2 ≤ N → |corr n φ F t| ≤ C * Real.exp (-(lam * t)))
    {t r : ℕ} (hr : 1 ≤ r) (hNr : 2 ^ (r + 1) * t + 2 * s + 2 ≤ N) :
    |corr n φ F t| ≤ (2 + (1 / 2 : ℝ) ^ r * C) * Real.exp (-(lam * t)) := by
  have hF : BM F := ⟨hFm, 1, hF1⟩
  set K := 2 ^ (r - 1) * t with hK
  have hpow : 2 ^ (r + 1) * t = 4 * K := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [hK, Nat.add_sub_cancel, pow_succ]
    ring
  have hNK : 4 * K + 2 * s + 2 ≤ N := by rw [← hpow]; exact hNr
  have hpos : ∀ j, j ≤ K → LinkDep (fun U => F (tShift (j : ZMod N) U)) (posHalfLinks d N) :=
    fun j hj => linkDep_tShift_of_slab hFs (by omega)
  have hdecay := hdec (2 ^ r * t) (by rw [show 2 * (2 ^ r * t) = 2 ^ (r + 1) * t by ring]; exact hNr)
  obtain ⟨h0, h⟩ := torus_theoremC_corr hc hU hN hφ hF hpos hr le_rfl hC hdecay
  have h2 : corr n φ F 0 ≤ 2 := (le_abs_self _).trans (abs_corr_le_two hc hU hφ hFm hF1 0)
  set q : ℝ := (1 / 2 : ℝ) ^ r
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hy := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.2 hq1) hq0 h0 hC (by ring)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  nlinarith [mul_nonneg hq0 h0]

end FiniteVolume

/-- **Route A, step 1: `SlabDecay` ⇒ `LatticeGap`** (infinite-volume limit at each level, Theorem C removes the
constant, which then disappears as the torus grows). -/
theorem latticeGap_of_slabDecay {T : Tuning} (h : SlabDecay T) : LatticeGap T := by
  obtain ⟨m, hm, hdec⟩ := h
  refine ⟨m, hm, fun s V => ?_⟩
  obtain ⟨k₀, hk₀⟩ := hdec s V
  refine ⟨k₀, fun k hk O t g hg => ?_⟩
  obtain ⟨C, hC, hCk⟩ := hk₀ k hk
  set E := Real.exp (-(m * (t * T.a k)))
  have hE : Real.exp (-((m * T.a k) * t)) = E := by congr 1; ring
  -- for each `r ≥ 1`, eventually in the volume
  have hr_bound : ∀ r : ℕ, 1 ≤ r → |g| ≤ (2 + (1 / 2 : ℝ) ^ r * C) * E := by
    intro r hr
    refine hg.abs_le ?_
    filter_upwards [tendsto_atTop.1 (T.tendsto_side k) (2 ^ (r + 1) * t + 2 * T.thick k s + 2)] with j hj
    have := corr_le_of_decay (d := 4) (N := T.side k j) (G := SU2) continuous_subtype_val
      (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (T.even_side k j) (posWeight_wilson 2 (T.β k))
      (O.meas k j) (O.bdd k j) (O.slab k j) hC (lam := m * T.a k)
      (fun t' ht' => by
        have := hCk j O t' ht'
        rw [show -(m * T.a k * t') = -(m * (t' * T.a k)) by ring]
        exact this) hr hj
    rw [hE] at this
    exact this
  have hq : Tendsto (fun r : ℕ => (2 + (1 / 2 : ℝ) ^ r * C) * E) atTop (𝓝 ((2 + 0 * C) * E)) :=
    (tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const C)).mul_const E
  rw [zero_mul, add_zero] at hq
  exact ge_of_tendsto hq (eventually_atTop.2 ⟨1, fun r hr => hr_bound r hr⟩)

/-- **Assembly, route A.** On a line of constant physics, slab decay at one physical rate gives the lattice-uniform
gap, the mass gap of every continuum limit point, and reflection positivity of every limit point. -/
theorem assembly_routeA {T : Tuning} (hL : OnLCP T) (hA : SlabDecay T) :
    MassGap T ∧ LatticeGap T ∧ LimitRP T :=
  ⟨massGap_of_latticeGap hL.tendsto_a (latticeGap_of_slabDecay hA), latticeGap_of_slabDecay hA, limitRP T⟩

/-! ### D′ is one sufficient condition for `SlabDecay` -/

/-- **Fine-level D′ ⇒ `SlabDecay`.** If on every torus of the family the SU(2) Wilson measure at `β_k` satisfies the
worst-case Dobrushin condition for thin cubes of physical size `L₀` with one `γ ∈ (0, 1)` (`UniformGDS`, H form, the
project's original open hypothesis), then `SlabDecay` holds with the physical rate `log(1/γ)/(4L₀)`. A sufficient
condition only: D′ is strictly stronger than the gap (worst case over boundaries; false below `1/T_c`). -/
theorem slabDecay_of_uniformGDS {T : Tuning} (ha0 : Tendsto T.a atTop (𝓝 0)) {L₀ γ : ℝ} (hL₀ : 0 < L₀)
    (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hGDS : ∀ j, UniformGDS (d := 4) (G := SU2) 2 (fun k => T.side k j) (fun k => wilsonWeight (T.β k)) L₀ γ T.a) :
    SlabDecay T := by
  have hlog : 0 < Real.log (1 / γ) := Real.log_pos (by rw [lt_div_iff₀ hγ0]; linarith)
  set m := Real.log (1 / γ) / (4 * L₀)
  refine ⟨m, by positivity, fun s V => ?_⟩
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((tendsto_order.1 ha0).2 L₀ hL₀)
  refine ⟨k₀, fun k hk => ?_⟩
  have hak := T.a_pos k
  have hakL := hk₀ k hk
  set ℓ' := side L₀ T.a k
  have hℓ : 1 ≤ ℓ' := Nat.ceil_pos.2 (div_pos hL₀ hak)
  set lam := m * T.a k
  have hlam0 : 0 ≤ lam := by positivity
  have hside := side_mul_le hL₀.le T.a_pos k
  have hlamlt : lam < Real.log (1 / γ) / ((ℓ' : ℝ) + 1) := by
    rw [lt_div_iff₀ (by positivity)]
    calc lam * ((ℓ' : ℝ) + 1) = m * (((ℓ' : ℝ) + 1) * T.a k) := by ring
      _ ≤ m * (L₀ + 2 * T.a k) := mul_le_mul_of_nonneg_left hside (by positivity)
      _ < m * (4 * L₀) := mul_lt_mul_of_pos_left (by linarith) (by positivity)
      _ = Real.log (1 / γ) := by simp only [m]; field_simp
  have hρ : γ * Real.exp (lam * ((ℓ' : ℝ) + 1)) < 1 := rate_lt_of_lt hγ0 (by positivity) hlamlt
  have hD : 0 < 1 - γ * Real.exp (lam * ((ℓ' : ℝ) + 1)) := by linarith
  refine ⟨cubeConst 4 ℓ' γ lam (2 * V k) 2, cubeConst_nonneg hD (by positivity) (by norm_num), ?_⟩
  intro j O t ht
  obtain ⟨κ, hκ, hg⟩ := hGDS j k
  set v : LatticeLink 4 (T.side k j) → ℝ := fun l => if l ∈ O.supp k j then 2 else 0
  have hv : OscBound (O.F k j) v := by
    intro σ x s'
    by_cases hx : x ∈ O.supp k j
    · simp only [v, hx, ite_true]
      have := O.bdd k j σ; have := O.bdd k j (Function.update σ x s')
      exact (abs_sub _ _).trans (by linarith)
    · simp only [v, hx, ite_false]
      have : O.F k j σ = O.F k j (Function.update σ x s') :=
        O.dep k j _ _ fun i hi => by rw [Function.update_of_ne (by rintro rfl; exact hx hi)]
      rw [this, sub_self, abs_zero]
  have hV : ∑ l, v l ≤ 2 * V k := by
    calc ∑ l, v l = ∑ l ∈ O.supp k j, (2 : ℝ) := by
          simp only [v]; rw [Finset.sum_ite_mem, Finset.univ_inter]
      _ = 2 * (O.supp k j).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 2 * V k := by have := O.supp_card k j; gcongr
  have hL : ∀ l, v l ≤ 2 := fun l => by simp only [v]; split_ifs <;> norm_num
  have := corr_decay_cubes (d := 4) (N := T.side k j) (G := SU2) continuous_subtype_val
    (fun g => Matrix.specialUnitaryGroup_le_unitaryGroup g.2) (posWeight_wilson 2 (T.β k)) hℓ hκ hγ0.le hg hlam0
    hρ (O.bm k j) (O.slab k j) hv hV hL ht
  refine this.trans (le_of_eq ?_)
  congr 2; simp only [lam]; ring

/-! ## Route B: the flux sector and Conjecture W -/

/-- **P4.2, Conjecture W in doubling form along the line (open).** There is `δ > 0` such that at every level `k` and for
every box of side `2^j ℓ_k` (physical side `2^j L₁`), doubling the box multiplies the act number by at least `(1+δ)²`
(the per-move form of `r4-conjw/NOTE.md` needs anisotropic boxes, not available in these objects). -/
def ConjW (T : Tuning) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ k j, (1 + δ) ^ 2 * actZ (T.β k) (T.box k j) ≤ actZ (T.β k) (T.box k (j + 1))

/-- **Flux confinement**: the act number grows geometrically with the physical box size, uniformly in the level. -/
def FluxGrowth (T : Tuning) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ z₀ : ℝ, 0 < z₀ ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j : ℕ,
    z₀ * (1 + δ) ^ (2 * j) ≤ actZ (T.β k) (T.box k j)

/-- **P5.1, the sector transfer (open; no known route).** Flux confinement implies the mass gap of the vacuum sector.
Stated as an implication: it carries the whole vacuum-sector content of route B. -/
def SectorTransfer (T : Tuning) : Prop := FluxGrowth T → MassGap T

/-- **W + the renormalisation condition give flux confinement** (the Lean content of route B). -/
theorem fluxGrowth_of_conjW {T : Tuning} (hL : OnLCP T) (hW : ConjW T) : FluxGrowth T := by
  obtain ⟨δ, hδ, hW⟩ := hW
  obtain ⟨zs, hzs, hz⟩ := hL.scheme
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((tendsto_order.1 hz).1 (zs / 2) (by linarith))
  refine ⟨δ, hδ, zs / 2, by linarith, k₀, fun k hk j => ?_⟩
  induction j with
  | zero => simpa using (hk₀ k hk).le
  | succ j ih =>
    calc zs / 2 * (1 + δ) ^ (2 * (j + 1)) = (1 + δ) ^ 2 * (zs / 2 * (1 + δ) ^ (2 * j)) := by ring
      _ ≤ (1 + δ) ^ 2 * actZ (T.β k) (T.box k j) := mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ actZ (T.β k) (T.box k (j + 1)) := hW k j

/-- **Assembly, route B.** On a line of constant physics, Conjecture W and the sector transfer give the mass gap;
reflection positivity of the limit is proved independently. -/
theorem assembly_routeB {T : Tuning} (hL : OnLCP T) (hW : ConjW T) (hS : SectorTransfer T) :
    MassGap T ∧ LimitRP T :=
  ⟨hS (fluxGrowth_of_conjW hL hW), limitRP T⟩

/-! ## The open pieces and the top-level theorem -/

/-- **The open pieces of the proof**, one field per piece (see `ASSEMBLY.md` for the blueprint map). -/
structure OpenPieces (T : Tuning) : Prop where
  /-- P6.6 (with P1.7 inside its renormalisation condition): the line of constant physics. -/
  lcp : OnLCP T
  /-- P6.2 (non-triviality): the limit is not pure noise. -/
  nontrivial : NonTrivial T
  /-- The crossover: route A (P4.1 in gap strength) or route B (P4.2 Conjecture W + P5.1 sector transfer). -/
  crossover : SlabDecay T ∨ (ConjW T ∧ SectorTransfer T)

/-- **The assembly theorem.** For SU(2) lattice Yang–Mills (Wilson action, 4D tori) along a tuning `T`: if the open
pieces hold, every continuum limit point has a mass gap (`MassGap`, precise form in `ProofPhase.Objects`), is reflection
positive (`LimitRP`, proved), and is non-trivial (`NonTrivial`, passed through from P6.2). -/
theorem yang_mills_assembly {T : Tuning} (P : OpenPieces T) : MassGap T ∧ LimitRP T ∧ NonTrivial T := by
  rcases P.crossover with hA | ⟨hW, hS⟩
  · exact ⟨(assembly_routeA P.lcp hA).1, limitRP T, P.nontrivial⟩
  · exact ⟨(assembly_routeB P.lcp hW hS).1, limitRP T, P.nontrivial⟩

/-! ## The blocked route at L₁ (a second sufficient condition for `SlabDecay`; its last link is not in Lean)

Round 3's chain, restated about the real blocked Yang–Mills laws (it was stated for abstract Gibbs systems,
`Attempts.R3.Robust`). Coarse torus `j`: `(ℤ/2(j+1)ℤ)⁴`, one coarse link per cell of `ℓ_k⁴` fine sites (physical size
`L₁`); the blocking is a family of reflection-respecting maps (`RPBlocking`), so every blocked layer is reflection
positive (`blocked_wilson_rp`). The pieces:

* `H1Local` — **P3.2/P3.3 in lattice-uniform form** (paper in parts, open as stated): every blocked law is the Gibbs
  measure of coarse potentials `V_{k,j}` (one per set of coarse links), converging locally to limit potentials `V_{∞,j}`
  with weighted pair sums `→ 0` uniformly in the volume (`Attempts.R3.LocalConvergenceW`).
* `LimitDprime` — **P4.1 (D′ at L₁, open; stronger than the gap)**: the limit potentials satisfy D′_λ with one `γ < 1`
  in every volume (`Attempts.R3.LimitFlatW`).
* `blockGap_of_blockedRoute` (**proved**): then for all levels `k ≥ k₀` and all volumes, block observables of the
  Wilson measure, `f ∘ Φ` and `g ∘ Φ`, at coarse distance `R` (physical distance `R L₁`) have covariance at most
  `(1 − γ')⁻¹ (∑ v_f) L_g e^{-λR}`.
* `ObsTransfer` — **P5.2 (H1-fine, open)**: conditional decoupling of fine observables given the block variables and
  quasi-locality of their conditional expectations, stated with `MeasureTheory.condExp`.

**Missing Lean link L1:** `H1Local ∧ LimitDprime ∧ ObsTransfer ⇒ SlabDecay` is on paper (`r3-robust/NOTE.md` §6, the law of
total covariance) and is not formalised here; so this route is not part of `OpenPieces`. -/

/-- The coarse side `2(j+1)` of volume `j` (cells of physical size `L₁`). -/
def coarseSide (j : ℕ) : ℕ := 2 * (j + 1)

instance (j : ℕ) : NeZero (coarseSide j) := ⟨by unfold coarseSide; omega⟩

/-- A blocking family: at every level and volume, a reflection-respecting blocking of the fine torus onto the coarse one. -/
abbrev BlockingFamily (T : Tuning) := ∀ k j, RPBlocking SU2 4 (T.side k j) (coarseSide j)

/-- The blocked law at level `k`, volume `j`: the image of the SU(2) Wilson measure. -/
def blockedLaw (T : Tuning) (B : BlockingFamily T) (k j : ℕ) : Measure (GaugeConnection SU2 4 (coarseSide j)) :=
  (T.ym k j).map (B k j).B

/-- Coarse potentials of volume `j`: one function per set of coarse links (depending only on that set). -/
abbrev CoarsePot (j : ℕ) := Finset (LatticeLink 4 (coarseSide j)) → GaugeConnection SU2 4 (coarseSide j) → ℝ

/-- **P3.2/P3.3, lattice-uniform form (open as stated).** -/
def H1Local (T : Tuning) (B : BlockingFamily T) (lam : ℝ) (Vk : ∀ j, ℕ → CoarsePot j) (Vinf : ∀ j, CoarsePot j) :
    Prop :=
  (∀ k j, blockedLaw T B k j = Attempts.R3.gibbsMeasure (haarG SU2) (Vk j k)) ∧
  (∀ j k, Attempts.R3.Potential (fun A => A) (Vk j k)) ∧
  Attempts.R3.LocalConvergenceW (fun _ A => A) (fun _ => linkDist) lam Vk Vinf

/-- **P4.1, D′_λ for the limit theory at L₁ (open).** -/
def LimitDprime (lam : ℝ) (Vinf : ∀ j, CoarsePot j) : Prop :=
  Attempts.R3.LimitFlatW (fun _ A => A) (fun _ => linkDist) lam Vinf

/-- **The blocked route gives decay of block observables of the real Wilson measure**, uniformly in the level
(`k ≥ k₀`) and the volume, at rate `λ` per coarse unit (`λ/L₁` physical). -/
theorem blockGap_of_blockedRoute {T : Tuning} (B : BlockingFamily T) {lam : ℝ} (hlam : 0 ≤ lam)
    {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j} (h1 : H1Local T B lam Vk Vinf)
    (h2 : LimitDprime lam Vinf) :
    ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
      (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
      (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg R : ℝ),
      BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → OscBound g (fun _ => Lg) →
      (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
      |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
          (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
        (1 - γ)⁻¹ * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  obtain ⟨hgibbs, hpot, hconv⟩ := h1
  obtain ⟨γ, hγ0, hγ1, k₀, hlev⟩ := Attempts.R3.levelFlat_of_local (fun _ A => A) (fun _ => linkDist) Vk Vinf hconv h2
  refine ⟨Effective.effGamma γ, (Effective.effGamma_pos hγ0).le, Effective.effGamma_lt_one hγ1, k₀,
    fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ?_⟩
  obtain ⟨Sb, hS, hflat⟩ := hlev k hk j
  have : Nonempty (LatticeLink 4 (coarseSide j)) := ⟨⟨fun _ => 0, 0⟩⟩
  rw [Effective.cov_map (T.ym k j) (B k j).meas hf hg]
  have e : (T.ym k j).map (B k j).B = Attempts.R3.gibbsMeasure (haarG SU2) (Vk j k) := hgibbs k j
  rw [e]
  exact Attempts.R3.decay_of_flatW (haarG SU2) (hpot j k) hS linkDist linkDist_self linkDist_triangle hlam
    (Effective.effGamma_pos hγ0).le (Effective.effGamma_lt_one hγ1) hflat hf hg hfA hgS hvf hLg hvg hR

/-- **P5.2, H1-fine (open).** For fine observables `F`, `G` (`|·| ≤ 1`, measurable, gauge invariant, depending on link
sets at physical distance `≥ D`) there are block observables `f`, `g` near their supports (at most
`K (|A₀| + 1)(1 + D/L₁)⁴` coarse links, at physical distance `≥ D/2`) such that (i) `f ∘ Φ` is `L¹`-close to the
conditional expectation `E[F | Φ]` (quasi-locality), and (ii) `F` and `G` decouple given the block variables:
`|E[F G] − E[E[F|Φ] E[G|Φ]]| ≤ c e^{-m D}` (conditional decoupling). The choice `f = g = 0` is excluded by (i): this is
an ultraviolet statement, not the gap. -/
def ObsTransfer (T : Tuning) (B : BlockingFamily T) : Prop :=
  ∃ c m : ℝ, 0 ≤ c ∧ 0 < m ∧ ∃ K : ℝ, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection SU2 4 (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink 4 (T.side k j))) (D : ℝ),
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * linkDist e e') →
    ∃ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (A'.card : ℝ) ≤ K * (A₀.card + 1) * (1 + D / T.L₁) ^ 4 ∧
      (B'.card : ℝ) ≤ K * (B₀.card + 1) * (1 + D / T.L₁) ^ 4 ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U - f ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U - g ((B k j).B U)| ∂(T.ym k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(T.ym k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) G U ∂(T.ym k j)|
        ≤ c * Real.exp (-(m * D))

/-! ## Non-triviality of the hypotheses -/

/-- **Bounded bare coupling is not on a line of constant physics.** Every family with `|β_k| ≤ B` (strong coupling, and
pure noise `β = 0`) violates asymptotic freedom (P6.6 (ii)). -/
theorem not_onLCP_of_bounded {T : Tuning} {B : ℝ} (hB : ∀ k, |T.β k| ≤ B) : ¬ OnLCP T := by
  intro hL
  have hlog : Tendsto (fun k => Real.log (T.ℓ k)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hL.resolution)
  have h0 : Tendsto (fun k => T.β k / Real.log (T.ℓ k)) atTop (𝓝 0) := by
    have hB' : Tendsto (fun k => B / Real.log (T.ℓ k)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero (fun k => abs_nonneg _) (fun k => ?_) (tendsto_zero_iff_abs_tendsto_zero _ |>.1 hB')
    show |T.β k / Real.log (T.ℓ k)| ≤ |B / Real.log (T.ℓ k)|
    rw [abs_div, abs_div]
    exact div_le_div_of_nonneg_right ((hB k).trans (le_abs_self B)) (abs_nonneg _)
  have := tendsto_nhds_unique h0 hL.running
  exact oneLoopSlope_pos.ne this

/-- **The pure-noise theory does not satisfy the open pieces** (closing review finding 2 of round 3): the family with
`β_k = 0` at every level (product Haar measure, the zero potential at every scale) is not on a line of constant physics,
whatever the resolution. -/
theorem not_trivial (T : Tuning) (h0 : ∀ k, T.β k = 0) : ¬ OpenPieces T := fun P =>
  not_onLCP_of_bounded (B := 0) (fun k => by rw [h0 k, abs_zero]) P.lcp

/-- **P6.6 (i)–(ii) are satisfiable**: the tuning `ℓ_k = k + 2`, `β_k = (11/(3π²)) log ℓ_k`. -/
theorem bareRunning_witness : ∃ T : Tuning,
    Tendsto T.ℓ atTop atTop ∧ Tendsto (fun k => T.β k / Real.log (T.ℓ k)) atTop (𝓝 oneLoopSlope) := by
  refine ⟨⟨1, one_pos, fun k => k + 2, fun k => by omega, fun k => oneLoopSlope * Real.log ((k + 2 : ℕ) : ℝ)⟩,
    tendsto_atTop_mono (fun k => show k ≤ k + 2 by omega) tendsto_id, ?_⟩
  refine tendsto_const_nhds.congr fun k => ?_
  have : 0 < Real.log ((k + 2 : ℕ) : ℝ) := Real.log_pos (by norm_cast; omega)
  simp only
  field_simp

end ProofPhase
