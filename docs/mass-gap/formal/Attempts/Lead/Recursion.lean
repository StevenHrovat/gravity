/-
Lead route attempt, the deterministic part (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/lead/NOTE.md`, section 1 (Theorem D1).
-/

import OneScale.CubeChain

/-!
# A doubling recursion for the box influence implies `UniformGDS`

Notation of `OneScale.CorollaryB`: at level `k` the torus `(ℤ/N_kℤ)^d`, the weight `φ_k`, the lattice spacing `a_k`,
thin cubes `thinCube ℓ x` of side `ℓ`, and `side L a k = ⌈L / a_k⌉₊` (a physical length `L` in lattice units).

* `GDSAt d G n Nk φ k ℓ c`: at level `k`, the thin cubes of side `ℓ` satisfy GDS with constant `c` (with some family of
  influence bounds). The least such `c` is the box influence `κ_k(ℓ)` of the note; we never need the least one.
  `UniformGDS` is exactly `∀ k, GDSAt … k (side L₀ a k) γ` (`uniformGDS_iff`).
* `DoublingRecursion f L₁ a`: **the recursion, uniform in the level**: whenever the side-`ℓ` cubes satisfy GDS with
  constant `c` and `ℓ` is at least the physical scale `L₁` (`L₁ ≤ ℓ a_k`), every side `ℓ'` with `ℓ ≤ ℓ' ≤ 2ℓ` satisfies
  GDS with constant `f c`. (Allowing `ℓ ≤ ℓ' ≤ 2ℓ` instead of `ℓ' = 2ℓ` absorbs the rounding of `⌈L/a_k⌉`.)
* `gdsAt_chain`: from an entrance value `x₀` at side `⌈L₁/a_k⌉`, the side `⌈2^m L₁/a_k⌉` has constant `f^[m] x₀`.
* `uniformGDS_of_recursion` (**Theorem D1**): entrance at the physical scale `L₁` with value `x₀` at every level, the
  recursion, and `f^[N] x₀ ≤ γ` give `UniformGDS` at the physical scale `L₀ = 2^N L₁`.
* `uniformGDS_of_recursion_all`: if moreover `f` maps a set `T ⊆ (-∞, γ]` into itself and `f^[N] x₀ ∈ T`, then
  `UniformGDS` holds at every scale `2^m L₁`, `m ≥ N` ("further doublings keep it there").
* `exists_iterate_le_of_tendsto`: a contracting fixed point `x* < γ` with `x₀` in its basin gives such an `N`.
* `iterate_sq`, `exists_iterate_sq_le`: the quadratic (chessboard-type) map `f x = C x²` has
  `f^[m] x = (C x)^(2^m) / C`; its basin is `0 ≤ C x₀ < 1`, and then every `γ > 0` is reached.
* `corollaryB_of_recursion`: the chain closes: recursion + entrance give Corollary B (physical units) through
  `OneScale.CubeChain.corollaryB_of_uniformGDS`.

**What this does not do.** It proves neither the recursion nor the entrance; both are hypotheses. The note (section 1.4)
explains why the entrance must sit at a physical scale `L₁` (a level-uniform `f` with entrance at a fixed lattice side
would give a lattice-unit gap uniform in `β`, i.e. a physical mass growing like `1/a_k`), so the recursion localises the
one-scale hypothesis at the smaller scale `L₁` with a weaker constant `x₀`, and does not remove it.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete
open OneScale OneScale.Gauge OneScale.CorollaryB

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.Lead

/-! ## GDS is monotone in its constant -/

/-- GDS with constant `γ` implies GDS with any larger constant (the coverage is nonnegative). -/
theorem gds_mono {ι J : Type*} [DecidableEq ι] [Fintype J] {block : J → Finset ι} {k : J → ι → ℝ}
    {γ γ' : ℝ} (h : GDS block k γ) (hle : γ ≤ γ') : GDS block k γ' := fun z =>
  (h z).trans (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg _))

/-! ## Rounding: one halving step of `⌈L/a⌉` -/

/-- `⌈L/a⌉ ≤ ⌈2L/a⌉` for `L ≥ 0`, `a > 0`. -/
theorem side_le_side_two_mul {L : ℝ} (hL : 0 ≤ L) {a : ℕ → ℝ} {k : ℕ} (ha : 0 < a k) :
    side L a k ≤ side (2 * L) a k := by
  unfold side
  refine Nat.ceil_mono ?_
  rw [div_le_div_iff_of_pos_right ha]
  linarith

/-- `⌈2L/a⌉ ≤ 2 ⌈L/a⌉`. -/
theorem side_two_mul_le (L : ℝ) (a : ℕ → ℝ) (k : ℕ) : side (2 * L) a k ≤ 2 * side L a k := by
  unfold side
  rw [Nat.ceil_le]
  push_cast
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by norm_num)

/-- `L ≤ ⌈L/a⌉ a`. -/
theorem le_side_mul (L : ℝ) {a : ℕ → ℝ} {k : ℕ} (ha : 0 < a k) : L ≤ (side L a k : ℝ) * a k := by
  unfold side
  rw [← div_le_iff₀ ha]
  exact Nat.le_ceil _

/-! ## The recursion and Theorem D1 -/

section Levels

variable {d : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] {n : ℕ} [HasGaugeTrace G n]
  {Nk : ℕ → ℕ} [∀ k, NeZero (Nk k)] {φ : ℕ → ℝ → ℝ}

variable (d G n Nk φ) in
/-- At level `k`, the thin cubes of side `ℓ` satisfy GDS with constant `c`, with some family of influence bounds. -/
def GDSAt (k ℓ : ℕ) (c : ℝ) : Prop :=
  ∃ κ : FinLatticeSites d (Nk k) → LatticeLink d (Nk k) → ℝ,
    (∀ x z, z ∉ thinCube ℓ x →
      IsInfluenceBound (thinCube ℓ x) (gaugeSpec (G := G) n (φ k) (thinCube ℓ x)) z (κ x z)) ∧
    GDS (thinCube ℓ) κ c

/-- `UniformGDS` is `GDSAt` at the side `⌈L₀/a_k⌉` with the same `γ` at every level. -/
theorem uniformGDS_iff {L₀ γ : ℝ} {a : ℕ → ℝ} :
    UniformGDS (d := d) (G := G) n Nk φ L₀ γ a ↔ ∀ k, GDSAt d G n Nk φ k (side L₀ a k) γ := Iff.rfl

theorem GDSAt.mono {k ℓ : ℕ} {c c' : ℝ} (h : GDSAt d G n Nk φ k ℓ c) (hle : c ≤ c') :
    GDSAt d G n Nk φ k ℓ c' := by
  obtain ⟨κ, hκ, hg⟩ := h
  exact ⟨κ, hκ, gds_mono hg hle⟩

variable (d G n Nk φ) in
/-- **The doubling recursion** (uniform in the level `k`, valid above the physical scale `L₁`): GDS with constant `c`
for the side-`ℓ` cubes gives GDS with constant `f c` for every side `ℓ'` with `ℓ ≤ ℓ' ≤ 2ℓ`. -/
def DoublingRecursion (f : ℝ → ℝ) (L₁ : ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ (k ℓ ℓ' : ℕ) (c : ℝ), L₁ ≤ (ℓ : ℝ) * a k → ℓ ≤ ℓ' → ℓ' ≤ 2 * ℓ →
    GDSAt d G n Nk φ k ℓ c → GDSAt d G n Nk φ k ℓ' (f c)

/-- **The chain.** From the entrance value `x₀` at side `⌈L₁/a_k⌉`, the recursion gives constant `f^[m] x₀` at side
`⌈2^m L₁/a_k⌉`, for every `m`. -/
theorem gdsAt_chain {f : ℝ → ℝ} {L₁ : ℝ} (hL₁ : 0 ≤ L₁) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k)
    (hrec : DoublingRecursion d G n Nk φ f L₁ a) {x₀ : ℝ} {k : ℕ}
    (hentry : GDSAt d G n Nk φ k (side L₁ a k) x₀) :
    ∀ m : ℕ, GDSAt d G n Nk φ k (side (2 ^ m * L₁) a k) (f^[m] x₀) := by
  intro m
  induction m with
  | zero => simpa using hentry
  | succ m ih =>
    have hLm : 0 ≤ 2 ^ m * L₁ := mul_nonneg (by positivity) hL₁
    have e : (2 : ℝ) ^ (m + 1) * L₁ = 2 * (2 ^ m * L₁) := by rw [pow_succ]; ring
    rw [e, Function.iterate_succ_apply']
    refine hrec k _ _ _ ?_ (side_le_side_two_mul hLm (ha k)) (side_two_mul_le _ a k) ih
    calc L₁ ≤ 2 ^ m * L₁ := le_mul_of_one_le_left hL₁ (one_le_pow₀ (by norm_num))
      _ ≤ _ := le_side_mul _ (ha k)

/-- **Theorem D1.** Entrance at the physical scale `L₁` with value `x₀` at every level, the level-uniform recursion
above `L₁`, and `f^[N] x₀ ≤ γ` give `UniformGDS` at the physical scale `L₀ = 2^N L₁` with constant `γ`. -/
theorem uniformGDS_of_recursion {f : ℝ → ℝ} {L₁ : ℝ} (hL₁ : 0 ≤ L₁) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k)
    (hrec : DoublingRecursion d G n Nk φ f L₁ a) {x₀ : ℝ}
    (hentry : ∀ k, GDSAt d G n Nk φ k (side L₁ a k) x₀) {N : ℕ} {γ : ℝ} (hN : f^[N] x₀ ≤ γ) :
    UniformGDS (d := d) (G := G) n Nk φ (2 ^ N * L₁) γ a :=
  fun k => (gdsAt_chain hL₁ ha hrec (hentry k) N).mono hN

/-- **Theorem D1, all larger scales.** If `f` maps a set `T ⊆ (-∞, γ]` into itself and `f^[N] x₀ ∈ T`, then
`UniformGDS` holds at every physical scale `2^m L₁` with `m ≥ N`. -/
theorem uniformGDS_of_recursion_all {f : ℝ → ℝ} {L₁ : ℝ} (hL₁ : 0 ≤ L₁) {a : ℕ → ℝ} (ha : ∀ k, 0 < a k)
    (hrec : DoublingRecursion d G n Nk φ f L₁ a) {x₀ : ℝ}
    (hentry : ∀ k, GDSAt d G n Nk φ k (side L₁ a k) x₀) {γ : ℝ} {T : Set ℝ} (hT : T ⊆ Set.Iic γ)
    (hinv : Set.MapsTo f T T) {N : ℕ} (hN : f^[N] x₀ ∈ T) :
    ∀ m, N ≤ m → UniformGDS (d := d) (G := G) n Nk φ (2 ^ m * L₁) γ a := by
  intro m hm
  refine uniformGDS_of_recursion hL₁ ha hrec hentry (N := m) ?_
  have e : m = (m - N) + N := (Nat.sub_add_cancel hm).symm
  rw [e, Function.iterate_add_apply]
  exact hT (hinv.iterate (m - N) hN)

end Levels

/-! ## The scalar recursion: basins -/

/-- A contracting fixed point `x* < γ` whose basin contains `x₀`: the iterates eventually stay below `γ`. -/
theorem exists_iterate_le_of_tendsto {f : ℝ → ℝ} {x₀ xs γ : ℝ}
    (h : Tendsto (fun m => f^[m] x₀) atTop (𝓝 xs)) (hx : xs < γ) : ∃ N, ∀ m, N ≤ m → f^[m] x₀ ≤ γ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually (eventually_le_nhds hx))
  exact ⟨N, hN⟩

/-- A global contraction towards `p` with factor `θ` (`|f x - p| ≤ θ |x - p|`): `|f^[m] x - p| ≤ θ^m |x - p|`. -/
theorem iterate_contract {f : ℝ → ℝ} {p θ : ℝ} (hθ : 0 ≤ θ) (hf : ∀ x, |f x - p| ≤ θ * |x - p|) (x : ℝ) :
    ∀ m : ℕ, |f^[m] x - p| ≤ θ ^ m * |x - p| := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    calc |f (f^[m] x) - p| ≤ θ * |f^[m] x - p| := hf _
      _ ≤ θ * (θ ^ m * |x - p|) := mul_le_mul_of_nonneg_left ih hθ
      _ = θ ^ m * θ * |x - p| := by ring

/-- The quadratic map `f x = C x²` (the form a chessboard bound "two independent crossings" would give): its iterates
are `f^[m] x = (C x)^(2^m) / C`. -/
theorem iterate_sq {C : ℝ} (hC : C ≠ 0) (x : ℝ) :
    ∀ m : ℕ, (fun y => C * y ^ 2)^[m] x = (C * x) ^ (2 ^ m) / C := by
  intro m
  induction m with
  | zero => field_simp; simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    show C * ((C * x) ^ 2 ^ m / C) ^ 2 = (C * x) ^ 2 ^ (m + 1) / C
    rw [pow_succ 2 m, pow_mul]
    field_simp

/-- The basin of the quadratic map: if `0 ≤ C x₀ < 1` (and `C > 0`), every `γ > 0` is eventually reached and kept. -/
theorem exists_iterate_sq_le {C x₀ γ : ℝ} (hC : 0 < C) (h0 : 0 ≤ C * x₀) (h1 : C * x₀ < 1) (hγ : 0 < γ) :
    ∃ N, ∀ m, N ≤ m → (fun y => C * y ^ 2)^[m] x₀ ≤ γ := by
  refine exists_iterate_le_of_tendsto (xs := 0) ?_ hγ
  have e : (fun m => (fun y => C * y ^ 2)^[m] x₀) = fun m => (C * x₀) ^ (2 ^ m) / C := by
    funext m; exact iterate_sq hC.ne' x₀ m
  rw [e]
  have h2 : Tendsto (fun m : ℕ => 2 ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp h2).div_const C
  simpa using this

/-! ## The chain closes: recursion + entrance give Corollary B -/

section Chain

variable {d : ℕ} [NeZero d] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] [(haarG G).IsInvInvariant]
  {n : ℕ} [HasGaugeTrace G n]

/-- **Corollary B from the recursion.** In the setting of `OneScale.CubeChain.corollaryB_of_uniformGDS`, replace its
hypothesis `UniformGDS` (at `L₀`) by: the level-uniform recursion above `L₁` and the entrance value `x₀` at `L₁`, on
every torus of the sequences, with `f^[N] x₀ ≤ γ`. Then the physical-units conclusions hold with `L₀ = 2^N L₁`. -/
theorem corollaryB_of_recursion
    (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    {L₁ γ : ℝ} (hL₁ : 0 < L₁) (hγ0 : 0 < γ) (hγ1 : γ < 1) {a : ℕ → ℝ}
    (ha : ∀ k, 0 < a k) (ha0 : Tendsto a atTop (𝓝 0))
    (Ns : ℕ → ℕ → ℕ) [∀ k j, NeZero (Ns k j)] (hEven : ∀ k j, Even (Ns k j))
    (hNs : ∀ k, Tendsto (Ns k) atTop atTop) {φ : ℕ → ℝ → ℝ} (hφ : ∀ k, PosWeight n (φ k))
    {f : ℝ → ℝ} {x₀ : ℝ} {N : ℕ} (hN : f^[N] x₀ ≤ γ)
    (hrec : ∀ j, DoublingRecursion d G n (fun k => Ns k j) φ f L₁ a)
    (hentry : ∀ j k, GDSAt d G n (fun k => Ns k j) φ k (side L₁ a k) x₀)
    (F : ∀ k j, GaugeConnection G d (Ns k j) → ℝ) (hF : ∀ k j, BM (F k j)) (s : ℕ → ℕ)
    (hFs : ∀ k j, DepOn (F k j) (OneScale.LinkDist.timeSlab 0 (s k)))
    (v : ∀ k j, LatticeLink d (Ns k j) → ℝ)
    (hv : ∀ k j, OscBound (F k j) (v k j)) (V L : ℕ → ℝ) (hV : ∀ k j, ∑ l, v k j l ≤ V k)
    (hL : ∀ k j l, v k j l ≤ L k) (h : ℕ → ℕ → ℝ)
    (hlim : ∀ k t, Tendsto (fun j => OneScale.TimeShift.corr n (φ k) (F k j) t) atTop (𝓝 (h k t))) :
    (∀ k t, |h k t| ≤ h k 0 *
        Real.exp (-(Real.log (1 / γ) / (2 ^ N * L₁ + 2 * a k) * (t * a k)))) ∧
    (∀ k, Real.log (1 / γ) / (2 ^ N * L₁ + 2 * a k) ≤ physMass (2 ^ N * L₁) γ a k) ∧
    Tendsto (physMass (2 ^ N * L₁) γ a) atTop (𝓝 (Real.log (1 / γ) / (2 ^ N * L₁))) :=
  OneScale.CubeChain.corollaryB_of_uniformGDS hc hU (by positivity) hγ0 hγ1 ha ha0 Ns hEven hNs hφ
    (fun j => uniformGDS_of_recursion hL₁.le ha (hrec j) (hentry j) hN) F hF s hFs v hv V L hV hL h hlim

end Chain

end Attempts.Lead
