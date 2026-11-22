/-
Proof phase, cycle 3, workstream D (c3d-h1): what `H1Local` asks beyond the per-volume theorem (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c3d-h1/NOTE.md`.
-/

import ProofPhase.Assembly

/-!
# `H1Local` split into its per-volume part and its two uniformities

`H1Local T B λ Vk Vinf` (`ProofPhase.Assembly`) has three clauses: every blocked law is a Gibbs measure of bounded coarse
potentials `V_{k,j}` (**representation**), and the weighted pair sums of the sup distances `η_k(x) ≥ sup|V_{k,j}(x) −
V_{∞,j}(x)|`, `∑_{i ≠ z} (∑_{x ∋ i, z} η_k(x)) e^{λ d(z, i)}`, are `≤ ε_k → 0` **uniformly in the volume**
(`Attempts.R3.LocalConvergenceW`). The per-volume theorem of cycle 1 (`ProofPhase.Quantum.PerVolume`) and round 3's noise
lemma give, for a noisy blocking, the representation and convergence **in each volume separately** (a finite system;
along subsequences, or along the full sequence when the mesh limit is unique). This file states exactly what the
uniformity in the volume adds.

**Abstract part (any family of finite Gibbs systems; elementary, mark D).** Fix a factor radius `rad` with
`dist(z, i) ≤ rad x` whenever `i, z ∈ supp x` (for the coarse torus: the `ℓ^∞` diameter `linkDiam`). Split every
weighted pair sum into the **near part** (factors of radius `≤ r`) and the **far part** (radius `> r`).

* `localConvergenceW_iff`: `LocalConvergenceW ↔ ∃ η ≥ |ΔV|` with `PairSumBdd` (at each level the weighted pair sums of
  `η` are bounded uniformly in the volume), `TailSmall` (for `ε > 0` there are `r` and `K` with far part `≤ ε` for all
  `k ≥ K`, all volumes, all sites) and `NearUniform` (for every `r` the near part tends to `0` uniformly in the volume).
* `tailSmall_of_envelope` (**uniform quasi-locality ⇒ small tails**): if `0 ≤ η ≤ h` for an envelope `h` whose pair sums
  weighted by `e^{λ' rad}`, `λ' > λ ≥ 0`, are bounded uniformly in the volume (`EnvelopeW`), the far part is
  `≤ M e^{-(λ' − λ) r}`; `pairSumBdd_of_envelope`: then also `PairSumBdd`.
* `nearUniform_of_stable` (**per-volume convergence + volume stabilisation ⇒ uniform near convergence**, a Moore–Osgood
  step): if every factor converges in every volume (`η_k(x) → 0`, the per-volume statement) and the near parts are
  dominated by `b_k + ζ_v` with `b_k → 0` (a volume-independent near distance) and `ζ_v → 0` along the cofinite filter
  (finite-size corrections), the near part tends to `0` uniformly in the volume.
* `flatW_far_le` (**D′ already contains the tails**): `FlatCriterionW dist λ S γ` with `S ≥ 0` gives, for `λ' ≤ λ`, far
  pair-oscillation sums (pairs at distance `> r`) at rate `λ'` of at most `γ e^{-(λ − λ') r}`.

**On the real objects.** `h1Local_iff_split` restates `H1Local` for the SU(2) Wilson blocked laws with these clauses,
and `h1Local_of_quasiLocal` proves `H1Local` from: the representation, a uniform envelope of the coarse potentials
(`EnvelopeW` at a rate `λ' > λ` for factor diameters), per-volume sup convergence of every coarse potential, and volume
stabilisation of the near parts (`NearStable`). These four inputs are named hypotheses about the blocked SU(2) Wilson
laws; none is proved here. The note says which literature result supplies which part.
-/

open MeasureTheory Finset Filter Topology OneScale OneScale.LinkDist Attempts.R3 AreaLaw.Concrete

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.H1

section Abstract

variable {Vol : Type*} {ι : Vol → Type*} [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)] {S : Type*}
  {X : Vol → Type*} [∀ v, Fintype (X v)]

/-- The weighted pair sum of a factor weight `w` at the site `z` of volume `v` (the quantity `LocalConvergenceW`
bounds). -/
def pairSum (supp : ∀ v, X v → Finset (ι v)) (dist : ∀ v, ι v → ι v → ℝ) (lam : ℝ) (w : ∀ v, X v → ℝ) (v : Vol)
    (z : ι v) : ℝ :=
  ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (ι v))),
    (∑ x ∈ pairFactors (supp v) i z, w v x) * Real.exp (lam * dist v z i)

/-- Its **near part**: factors of radius `≤ r`. -/
def nearSum (supp : ∀ v, X v → Finset (ι v)) (dist : ∀ v, ι v → ι v → ℝ) (lam : ℝ) (rad : ∀ v, X v → ℝ) (r : ℝ)
    (w : ∀ v, X v → ℝ) (v : Vol) (z : ι v) : ℝ :=
  ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (ι v))),
    (∑ x ∈ (pairFactors (supp v) i z).filter (fun x => rad v x ≤ r), w v x) * Real.exp (lam * dist v z i)

/-- Its **far part**: factors of radius `> r`. -/
def farSum (supp : ∀ v, X v → Finset (ι v)) (dist : ∀ v, ι v → ι v → ℝ) (lam : ℝ) (rad : ∀ v, X v → ℝ) (r : ℝ)
    (w : ∀ v, X v → ℝ) (v : Vol) (z : ι v) : ℝ :=
  ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (ι v))),
    (∑ x ∈ (pairFactors (supp v) i z).filter (fun x => ¬ rad v x ≤ r), w v x) * Real.exp (lam * dist v z i)

variable {supp : ∀ v, X v → Finset (ι v)} {dist : ∀ v, ι v → ι v → ℝ} {lam : ℝ} {rad : ∀ v, X v → ℝ}

theorem pairSum_eq_near_add_far (r : ℝ) (w : ∀ v, X v → ℝ) (v : Vol) (z : ι v) :
    pairSum supp dist lam w v z = nearSum supp dist lam rad r w v z + farSum supp dist lam rad r w v z := by
  unfold pairSum nearSum farSum
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← add_mul, sum_filter_add_sum_filter_not]

theorem nearSum_nonneg (r : ℝ) {w : ∀ v, X v → ℝ} (hw : ∀ v x, 0 ≤ w v x) (v : Vol) (z : ι v) :
    0 ≤ nearSum supp dist lam rad r w v z :=
  sum_nonneg fun _ _ => mul_nonneg (sum_nonneg fun x _ => hw v x) (Real.exp_pos _).le

theorem farSum_nonneg (r : ℝ) {w : ∀ v, X v → ℝ} (hw : ∀ v x, 0 ≤ w v x) (v : Vol) (z : ι v) :
    0 ≤ farSum supp dist lam rad r w v z :=
  sum_nonneg fun _ _ => mul_nonneg (sum_nonneg fun x _ => hw v x) (Real.exp_pos _).le

/-- **(PairSumBdd)** At each level the weighted pair sums are bounded uniformly in the volume. -/
def PairSumBdd (supp : ∀ v, X v → Finset (ι v)) (dist : ∀ v, ι v → ι v → ℝ) (lam : ℝ) (η : ∀ v, ℕ → X v → ℝ) :
    Prop :=
  ∀ k, ∃ M : ℝ, ∀ v z, pairSum supp dist lam (fun v => η v k) v z ≤ M

/-- **(TailSmall)** The far parts are eventually small, uniformly in the volume and the site. -/
def TailSmall (supp : ∀ v, X v → Finset (ι v)) (dist : ∀ v, ι v → ι v → ℝ) (lam : ℝ) (rad : ∀ v, X v → ℝ)
    (η : ∀ v, ℕ → X v → ℝ) : Prop :=
  ∀ ε > 0, ∃ r : ℝ, ∃ K : ℕ, ∀ k ≥ K, ∀ v z, farSum supp dist lam rad r (fun v => η v k) v z ≤ ε

/-- **(NearUniform)** For every radius the near parts tend to zero uniformly in the volume and the site. -/
def NearUniform (supp : ∀ v, X v → Finset (ι v)) (dist : ∀ v, ι v → ι v → ℝ) (lam : ℝ) (rad : ∀ v, X v → ℝ)
    (η : ∀ v, ℕ → X v → ℝ) : Prop :=
  ∀ r : ℝ, ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ v z, nearSum supp dist lam rad r (fun v => η v k) v z ≤ ε

/-- A family bounded at each index and eventually uniformly small is dominated by one null sequence. -/
theorem exists_seq_of_unif {P : Type*} (a : ℕ → P → ℝ) (hb : ∀ k, ∃ M, ∀ p, a k p ≤ M)
    (hu : ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ p, a k p ≤ ε) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ k p, a k p ≤ e k := by
  refine ⟨fun k => max 0 (sSup (Set.range (a k))), ?_, fun k p => ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := hu (ε / 2) (by linarith)
    refine ⟨K, fun k hk => ?_⟩
    have h1 : sSup (Set.range (a k)) ≤ ε / 2 :=
      Real.sSup_le (by rintro _ ⟨p, rfl⟩; exact hK k hk p) (by linarith)
    have h2 : 0 ≤ max 0 (sSup (Set.range (a k))) := le_max_left _ _
    have h3 : max 0 (sSup (Set.range (a k))) ≤ ε / 2 := max_le (by linarith) h1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h2]
    linarith
  · obtain ⟨M, hM⟩ := hb k
    have hbdd : BddAbove (Set.range (a k)) := ⟨M, by rintro _ ⟨q, rfl⟩; exact hM q⟩
    exact (le_csSup hbdd ⟨p, rfl⟩).trans (le_max_right _ _)

/-- **The exact content of `LocalConvergenceW`** (D): local convergence uniform in the volume is equivalent to the
existence of sup distances `η` with bounded pair sums at each level, uniformly small tails and uniformly vanishing near
parts. -/
theorem localConvergenceW_iff (rad : ∀ v, X v → ℝ) (Vk : ∀ v, ℕ → X v → (ι v → S) → ℝ)
    (Vinf : ∀ v, X v → (ι v → S) → ℝ) :
    LocalConvergenceW supp dist lam Vk Vinf ↔
      ∃ η : ∀ v, ℕ → X v → ℝ, (∀ v k x, 0 ≤ η v k x) ∧ (∀ v k x σ, |Vk v k x σ - Vinf v x σ| ≤ η v k x) ∧
        PairSumBdd supp dist lam η ∧ TailSmall supp dist lam rad η ∧ NearUniform supp dist lam rad η := by
  constructor
  · rintro ⟨η, h0, hη, ε, hε, hsum⟩
    have hsum' : ∀ v k z, pairSum supp dist lam (fun v => η v k) v z ≤ ε k := hsum
    have hev : ∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ε k ≤ δ := fun δ hδ =>
      eventually_atTop.1 ((tendsto_order.1 hε).2 δ hδ |>.mono fun _ h => h.le)
    refine ⟨η, h0, hη, fun k => ⟨ε k, fun v z => hsum' v k z⟩, fun δ hδ => ?_, fun r δ hδ => ?_⟩
    · obtain ⟨K, hK⟩ := hev δ hδ
      refine ⟨0, K, fun k hk v z => ?_⟩
      have := pairSum_eq_near_add_far (supp := supp) (dist := dist) (lam := lam) (rad := rad) 0 (fun v => η v k) v z
      have hn := nearSum_nonneg (supp := supp) (dist := dist) (lam := lam) (rad := rad) 0
        (w := fun v => η v k) (fun v x => h0 v k x) v z
      linarith [hsum' v k z, hK k hk]
    · obtain ⟨K, hK⟩ := hev δ hδ
      refine ⟨K, fun k hk v z => ?_⟩
      have := pairSum_eq_near_add_far (supp := supp) (dist := dist) (lam := lam) (rad := rad) r (fun v => η v k) v z
      have hf := farSum_nonneg (supp := supp) (dist := dist) (lam := lam) (rad := rad) r
        (w := fun v => η v k) (fun v x => h0 v k x) v z
      linarith [hsum' v k z, hK k hk]
  · rintro ⟨η, h0, hη, hB, hT, hN⟩
    obtain ⟨e, he, hle⟩ := exists_seq_of_unif (P := Σ v, ι v)
      (fun k p => pairSum supp dist lam (fun v => η v k) p.1 p.2)
      (fun k => by obtain ⟨M, hM⟩ := hB k; exact ⟨M, fun p => hM p.1 p.2⟩)
      (fun δ hδ => by
        obtain ⟨r, K₁, hK₁⟩ := hT (δ / 2) (by linarith)
        obtain ⟨K₂, hK₂⟩ := hN r (δ / 2) (by linarith)
        refine ⟨max K₁ K₂, fun k hk p => ?_⟩
        rw [pairSum_eq_near_add_far (rad := rad) r]
        linarith [hK₁ k ((le_max_left _ _).trans hk) p.1 p.2, hK₂ k ((le_max_right _ _).trans hk) p.1 p.2])
    exact ⟨η, h0, hη, e, he, fun v k z => hle k ⟨v, z⟩⟩

/-- **(EnvelopeW)** Uniform quasi-locality: an envelope `h` whose pair sums, each factor weighted by
`e^{λ' rad x}`, are bounded uniformly in the volume. -/
def EnvelopeW (supp : ∀ v, X v → Finset (ι v)) (rad : ∀ v, X v → ℝ) (lam' : ℝ) (h : ∀ v, X v → ℝ) : Prop :=
  ∃ M : ℝ, ∀ v z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (ι v))),
    ∑ x ∈ pairFactors (supp v) i z, h v x * Real.exp (lam' * rad v x) ≤ M

theorem mem_pairFactors {v : Vol} {i z : ι v} {x : X v} (hx : x ∈ pairFactors (supp v) i z) : i ∈ supp v x ∧ z ∈ supp v x :=
  (mem_filter.1 hx).2

/-- **Uniform quasi-locality gives small tails** (S, elementary): far parts `≤ M e^{-(λ' − λ) r}`. -/
theorem tailSmall_of_envelope (hrad : ∀ v x i z, i ∈ supp v x → z ∈ supp v x → dist v z i ≤ rad v x)
    {lam' : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < lam') {h : ∀ v, X v → ℝ} {η : ∀ v, ℕ → X v → ℝ}
    (hη0 : ∀ v k x, 0 ≤ η v k x) (hηh : ∀ v k x, η v k x ≤ h v x) (hE : EnvelopeW supp rad lam' h) :
    TailSmall supp dist lam rad η := by
  obtain ⟨M, hM⟩ := hE
  have hc : 0 < lam' - lam := by linarith
  have hfar : ∀ r v k z, farSum supp dist lam rad r (fun v => η v k) v z ≤
      Real.exp (-((lam' - lam) * r)) * M := by
    intro r v k z
    unfold farSum
    calc ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (ι v))),
          (∑ x ∈ (pairFactors (supp v) i z).filter (fun x => ¬ rad v x ≤ r), η v k x) * Real.exp (lam * dist v z i)
        = ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (ι v))),
            ∑ x ∈ (pairFactors (supp v) i z).filter (fun x => ¬ rad v x ≤ r),
              η v k x * Real.exp (lam * dist v z i) := by
          refine sum_congr rfl fun i _ => ?_; rw [sum_mul]
      _ ≤ ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (ι v))),
            ∑ x ∈ (pairFactors (supp v) i z).filter (fun x => ¬ rad v x ≤ r),
              Real.exp (-((lam' - lam) * r)) * (h v x * Real.exp (lam' * rad v x)) := by
          refine sum_le_sum fun i _ => sum_le_sum fun x hx => ?_
          obtain ⟨hxp, hxr⟩ := mem_filter.1 hx
          obtain ⟨hi, hz⟩ := mem_pairFactors hxp
          have hd := hrad v x i z hi hz
          have hr : r < rad v x := lt_of_not_ge hxr
          have hh : 0 ≤ h v x := (hη0 v k x).trans (hηh v k x)
          have e1 : Real.exp (lam * dist v z i) ≤ Real.exp (-((lam' - lam) * r)) * Real.exp (lam' * rad v x) := by
            rw [← Real.exp_add]
            apply Real.exp_le_exp.2
            nlinarith [mul_le_mul_of_nonneg_left hd hlam0, mul_lt_mul_of_pos_left hr hc]
          calc η v k x * Real.exp (lam * dist v z i) ≤ h v x * Real.exp (lam * dist v z i) :=
                mul_le_mul_of_nonneg_right (hηh v k x) (Real.exp_pos _).le
            _ ≤ h v x * (Real.exp (-((lam' - lam) * r)) * Real.exp (lam' * rad v x)) :=
                mul_le_mul_of_nonneg_left e1 hh
            _ = _ := by ring
      _ ≤ ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (ι v))),
            ∑ x ∈ pairFactors (supp v) i z, Real.exp (-((lam' - lam) * r)) * (h v x * Real.exp (lam' * rad v x)) := by
          refine sum_le_sum fun i _ => sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun x hx _ => ?_
          have hh : 0 ≤ h v x := (hη0 v 0 x).trans (hηh v 0 x)
          positivity
      _ = Real.exp (-((lam' - lam) * r)) * ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (ι v))),
            ∑ x ∈ pairFactors (supp v) i z, h v x * Real.exp (lam' * rad v x) := by
          rw [mul_sum]; refine sum_congr rfl fun i _ => ?_; rw [mul_sum]
      _ ≤ Real.exp (-((lam' - lam) * r)) * M := mul_le_mul_of_nonneg_left (hM v z) (Real.exp_pos _).le
  intro ε hε
  have hT : Tendsto (fun r : ℝ => Real.exp (-((lam' - lam) * r)) * M) atTop (𝓝 (0 * M)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)).mul_const M
  rw [zero_mul] at hT
  obtain ⟨r, hr⟩ := ((tendsto_order.1 hT).2 ε hε).exists
  exact ⟨r, 0, fun k _ v z => (hfar r v k z).trans hr.le⟩

/-- Uniform quasi-locality also bounds the full pair sums at every level (S, elementary). -/
theorem pairSumBdd_of_envelope (hrad : ∀ v x i z, i ∈ supp v x → z ∈ supp v x → dist v z i ≤ rad v x)
    (hd0 : ∀ v a b, 0 ≤ dist v a b) {lam' : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ lam') {h : ∀ v, X v → ℝ}
    {η : ∀ v, ℕ → X v → ℝ} (hη0 : ∀ v k x, 0 ≤ η v k x) (hηh : ∀ v k x, η v k x ≤ h v x)
    (hE : EnvelopeW supp rad lam' h) : PairSumBdd supp dist lam η := by
  obtain ⟨M, hM⟩ := hE
  refine fun k => ⟨M, fun v z => ?_⟩
  unfold pairSum
  refine le_trans ?_ (hM v z)
  refine sum_le_sum fun i _ => ?_
  rw [sum_mul]
  refine sum_le_sum fun x hx => ?_
  obtain ⟨hi, hz⟩ := mem_pairFactors hx
  have hd := hrad v x i z hi hz
  have hh : 0 ≤ h v x := (hη0 v k x).trans (hηh v k x)
  have hrad0 : 0 ≤ rad v x := (hd0 v z i).trans hd
  have e1 : Real.exp (lam * dist v z i) ≤ Real.exp (lam' * rad v x) :=
    Real.exp_le_exp.2 ((mul_le_mul_of_nonneg_left hd hlam0).trans (mul_le_mul_of_nonneg_right hlam hrad0))
  exact (mul_le_mul_of_nonneg_right (hηh v k x) (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_left e1 hh)

/-- **Per-volume convergence plus volume stabilisation give uniform near convergence** (S, elementary; a
Moore–Osgood step). `hconv` is the per-volume statement (every factor converges in every volume); `hstab` says the
near part at radius `r` is dominated by a volume-independent null sequence `b` plus a finite-size correction `ζ_v` that
is small outside finitely many volumes. -/
theorem nearUniform_of_stable {η : ∀ v, ℕ → X v → ℝ}
    (hconv : ∀ v x, Tendsto (fun k => η v k x) atTop (𝓝 0))
    (hstab : ∀ r : ℝ, ∃ b : ℕ → ℝ, ∃ ζ : Vol → ℝ, Tendsto b atTop (𝓝 0) ∧ Tendsto ζ cofinite (𝓝 0) ∧
      ∀ v k z, nearSum supp dist lam rad r (fun v => η v k) v z ≤ b k + ζ v) :
    NearUniform supp dist lam rad η := by
  intro r ε hε
  obtain ⟨b, ζ, hb, hζ, hdom⟩ := hstab r
  have hF : {v | ¬ ζ v < ε / 2}.Finite := Filter.eventually_cofinite.1 ((tendsto_order.1 hζ).2 (ε / 2) (by linarith))
  -- per volume, the near part tends to zero (a finite sum of convergent sequences)
  have hper : ∀ v (z : ι v), Tendsto (fun k => nearSum supp dist lam rad r (fun v => η v k) v z) atTop (𝓝 0) := by
    intro v z
    unfold nearSum
    have : Tendsto (fun k => ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (ι v))),
        (∑ x ∈ (pairFactors (supp v) i z).filter (fun x => rad v x ≤ r), η v k x) * Real.exp (lam * dist v z i))
        atTop (𝓝 (∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (ι v))),
          (∑ x ∈ (pairFactors (supp v) i z).filter (fun x => rad v x ≤ r), (0 : ℝ)) *
            Real.exp (lam * dist v z i))) :=
      tendsto_finsetSum _ fun i _ => (tendsto_finsetSum _ fun x _ => hconv v x).mul_const _
    simpa using this
  have hev1 : ∀ᶠ k in atTop, b k < ε / 2 := (tendsto_order.1 hb).2 (ε / 2) (by linarith)
  have hev2 : ∀ᶠ k in atTop, ∀ v ∈ {v | ¬ ζ v < ε / 2}, ∀ z : ι v,
      nearSum supp dist lam rad r (fun v => η v k) v z < ε :=
    (Filter.eventually_all_finite hF).2 fun v _ => Filter.eventually_all.2 fun z => (tendsto_order.1 (hper v z)).2 ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hev1.and hev2)
  refine ⟨K, fun k hk v z => ?_⟩
  obtain ⟨h1, h2⟩ := hK k hk
  by_cases hv : ζ v < ε / 2
  · linarith [hdom v k z]
  · exact (h2 v hv z).le

end Abstract

section Criterion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **D′ already contains uniform tails** (D): the weighted criterion at rate `λ` bounds the far pair-oscillation sums
(pairs at distance `> r`) at any rate `λ' ≤ λ` by `γ e^{-(λ − λ') r}`. So the quasi-locality part of `H1Local` (for the
pair oscillations) is implied by D′ for the same theory: it is weaker than what the crossover's Dobrushin condition
needs. -/
theorem flatW_far_le {dist : ι → ι → ℝ} {lam lam' γ : ℝ} {Sb : ι → ι → ℝ} (hS0 : ∀ i z, 0 ≤ Sb i z)
    (hflat : FlatCriterionW dist lam Sb γ) (hlam : lam' ≤ lam) (r : ℝ) (z : ι) :
    ∑ i ∈ (univ.filter (fun i => z ∉ ({i} : Finset ι))).filter (fun i => r < dist z i),
      Real.tanh (Sb i z / 2) * Real.exp (lam' * dist z i) ≤ Real.exp (-((lam - lam') * r)) * γ := by
  have ht : ∀ i, 0 ≤ Real.tanh (Sb i z / 2) := fun i => OneScale.SingleLink.tanh_nonneg (by linarith [hS0 i z])
  calc ∑ i ∈ (univ.filter (fun i => z ∉ ({i} : Finset ι))).filter (fun i => r < dist z i),
        Real.tanh (Sb i z / 2) * Real.exp (lam' * dist z i)
      ≤ ∑ i ∈ (univ.filter (fun i => z ∉ ({i} : Finset ι))).filter (fun i => r < dist z i),
          Real.exp (-((lam - lam') * r)) * (Real.tanh (Sb i z / 2) * Real.exp (lam * dist z i)) := by
        refine sum_le_sum fun i hi => ?_
        have hr : r < dist z i := (mem_filter.1 hi).2
        have e1 : Real.exp (lam' * dist z i) ≤ Real.exp (-((lam - lam') * r)) * Real.exp (lam * dist z i) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith [mul_le_mul_of_nonneg_left hr.le (sub_nonneg.2 hlam)]
        calc Real.tanh (Sb i z / 2) * Real.exp (lam' * dist z i)
            ≤ Real.tanh (Sb i z / 2) * (Real.exp (-((lam - lam') * r)) * Real.exp (lam * dist z i)) :=
              mul_le_mul_of_nonneg_left e1 (ht i)
          _ = _ := by ring
    _ ≤ ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)),
          Real.exp (-((lam - lam') * r)) * (Real.tanh (Sb i z / 2) * Real.exp (lam * dist z i)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ => by have := ht i; positivity
    _ = Real.exp (-((lam - lam') * r)) * ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset ι)),
          Real.tanh (Sb i z / 2) * Real.exp (lam * dist z i) := by rw [mul_sum]
    _ ≤ Real.exp (-((lam - lam') * r)) * γ := mul_le_mul_of_nonneg_left (hflat z) (Real.exp_pos _).le

end Criterion

/-! ## On the real objects: the blocked SU(2) Wilson laws -/

section Real

/-- The `ℓ^∞` diameter of a set of coarse links (in coarse units). -/
def linkDiam {N : ℕ} [NeZero N] (A : Finset (LatticeLink 4 N)) : ℝ :=
  (((A ×ˢ A).sup fun p => siteDist p.1.site p.2.site : ℕ) : ℝ)

theorem linkDist_le_linkDiam {N : ℕ} [NeZero N] {A : Finset (LatticeLink 4 N)} {e e' : LatticeLink 4 N}
    (he : e ∈ A) (he' : e' ∈ A) : linkDist e e' ≤ linkDiam A := by
  unfold linkDist linkDiam
  have h := Finset.le_sup (f := fun p : LatticeLink 4 N × LatticeLink 4 N => siteDist p.1.site p.2.site)
    (s := A ×ˢ A) (b := (e, e')) (mem_product.2 ⟨he, he'⟩)
  exact_mod_cast h

/-- The sup distance of two coarse potential terms. -/
def supDist {j : ℕ} (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) : ℝ := ⨆ σ, |f σ - g σ|

theorem le_supDist {j : ℕ} {f g : GaugeConnection SU2 4 (coarseSide j) → ℝ} {M : ℝ} (hM : ∀ σ, |f σ - g σ| ≤ M)
    (σ : GaugeConnection SU2 4 (coarseSide j)) : |f σ - g σ| ≤ supDist f g :=
  le_ciSup ⟨M, by rintro _ ⟨τ, rfl⟩; exact hM τ⟩ σ

theorem supDist_nonneg {j : ℕ} (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) : 0 ≤ supDist f g :=
  Real.iSup_nonneg fun _ => abs_nonneg _

theorem supDist_le {j : ℕ} {f g : GaugeConnection SU2 4 (coarseSide j) → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ σ, |f σ - g σ| ≤ M) : supDist f g ≤ M :=
  Real.iSup_le hM hM0

/-- The coarse supports and distances of `H1Local`. -/
abbrev csupp : ∀ j, Finset (LatticeLink 4 (coarseSide j)) → Finset (LatticeLink 4 (coarseSide j)) := fun _ A => A
abbrev cdist : ∀ j, LatticeLink 4 (coarseSide j) → LatticeLink 4 (coarseSide j) → ℝ := fun _ => linkDist
abbrev crad : ∀ j, Finset (LatticeLink 4 (coarseSide j)) → ℝ := fun _ => linkDiam

theorem crad_spec (j : ℕ) (A : Finset (LatticeLink 4 (coarseSide j))) (i z : LatticeLink 4 (coarseSide j))
    (hi : i ∈ csupp j A) (hz : z ∈ csupp j A) : cdist j z i ≤ crad j A :=
  linkDist_le_linkDiam hz hi

/-- **`H1Local`, split** (D): the representation, and local convergence uniform in the volume in the form "bounded pair
sums at each level, small tails, uniformly vanishing near parts", with the near/far split by coarse diameter. -/
theorem h1Local_iff_split (T : Tuning) (B : BlockingFamily T) (lam : ℝ) (Vk : ∀ j, ℕ → CoarsePot j)
    (Vinf : ∀ j, CoarsePot j) :
    H1Local T B lam Vk Vinf ↔
      (∀ k j, blockedLaw T B k j = gibbsMeasure (haarG SU2) (Vk j k)) ∧ (∀ j k, Potential (fun A => A) (Vk j k)) ∧
      ∃ η : ∀ j, ℕ → Finset (LatticeLink 4 (coarseSide j)) → ℝ, (∀ j k A, 0 ≤ η j k A) ∧
        (∀ j k A σ, |Vk j k A σ - Vinf j A σ| ≤ η j k A) ∧ PairSumBdd csupp cdist lam η ∧
        TailSmall csupp cdist lam crad η ∧ NearUniform csupp cdist lam crad η := by
  unfold H1Local
  rw [localConvergenceW_iff crad Vk Vinf]

/-- **Volume stabilisation of the near parts (named hypothesis, open).** For every coarse radius `r`, the near parts
of the per-factor sup distances are dominated by a volume-independent null sequence plus finite-size corrections that
vanish outside finitely many volumes. On the torus family this is what "the effective action at `L₁` near a link does not
depend on the far torus, up to `ζ_j → 0`, and its local part converges" means. -/
def NearStable (lam : ℝ) (Vk : ∀ j, ℕ → CoarsePot j) (Vinf : ∀ j, CoarsePot j) : Prop :=
  ∀ r : ℝ, ∃ b : ℕ → ℝ, ∃ ζ : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧ Tendsto ζ cofinite (𝓝 0) ∧
    ∀ j k z, nearSum csupp cdist lam crad r (fun j A => supDist (Vk j k A) (Vinf j A)) j z ≤ b k + ζ j

/-- **`H1Local` from uniform quasi-locality, per-volume convergence and volume stabilisation** (S, elementary given
the named hypotheses). Hypotheses, all about the blocked SU(2) Wilson laws along `T` and their coarse potentials:
* `hgibbs`, `hpot`: the representation (each blocked law is a Gibbs measure of bounded coarse potentials);
* `hVk`, `hVinf`, `hE`: **uniform quasi-locality** at a rate `λ' > λ`: one envelope `h` for all levels, with pair sums
  weighted by `e^{λ' diam}` bounded uniformly in the volume (`EnvelopeW`);
* `hconv`: **per-volume convergence** of every coarse potential term in sup norm (the per-volume statement);
* `hstab`: `NearStable`. -/
theorem h1Local_of_quasiLocal {T : Tuning} {B : BlockingFamily T} {lam lam' : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : lam < lam') {Vk : ∀ j, ℕ → CoarsePot j} {Vinf : ∀ j, CoarsePot j}
    (hgibbs : ∀ k j, blockedLaw T B k j = gibbsMeasure (haarG SU2) (Vk j k))
    (hpot : ∀ j k, Potential (fun A => A) (Vk j k))
    {h : ∀ j, Finset (LatticeLink 4 (coarseSide j)) → ℝ} (hVk : ∀ j k A σ, |Vk j k A σ| ≤ h j A)
    (hVinf : ∀ j A σ, |Vinf j A σ| ≤ h j A) (hE : EnvelopeW csupp crad lam' (fun j A => 2 * h j A))
    (hconv : ∀ j A, Tendsto (fun k => supDist (Vk j k A) (Vinf j A)) atTop (𝓝 0))
    (hstab : NearStable lam Vk Vinf) : H1Local T B lam Vk Vinf := by
  rw [h1Local_iff_split]
  set η : ∀ j, ℕ → Finset (LatticeLink 4 (coarseSide j)) → ℝ := fun j k A => supDist (Vk j k A) (Vinf j A)
  have hb : ∀ j k A σ, |Vk j k A σ - Vinf j A σ| ≤ 2 * h j A := fun j k A σ => by
    have := abs_sub (Vk j k A σ) (Vinf j A σ)
    linarith [hVk j k A σ, hVinf j A σ]
  have hh0 : ∀ j A, 0 ≤ 2 * h j A := fun j A => by
    have := hVinf j A (fun _ => 1); linarith [abs_nonneg (Vinf j A (fun _ => 1))]
  have hη0 : ∀ j k A, 0 ≤ η j k A := fun j k A => supDist_nonneg _ _
  have hηh : ∀ j k A, η j k A ≤ 2 * h j A := fun j k A => supDist_le (hh0 j A) (hb j k A)
  refine ⟨hgibbs, hpot, η, hη0, fun j k A σ => le_supDist (hb j k A) σ, ?_, ?_, ?_⟩
  · exact pairSumBdd_of_envelope crad_spec (fun _ a b => linkDist_nonneg a b) hlam0 hlam.le hη0 hηh hE
  · exact tailSmall_of_envelope crad_spec hlam0 hlam hη0 hηh hE
  · exact nearUniform_of_stable hconv hstab

end Real

end ProofPhase.H1
