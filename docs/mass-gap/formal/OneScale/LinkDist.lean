/-
The one-scale reduction, a concrete link distance (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/PROOF-NOTE.md`, §1.1 (distance on links), §6.4 (the slab separation used
in Theorem C), §8 (non-vacuity).
-/

import OneScale.SingleLink

/-!
# A link distance on the periodic lattice and the time-slab separation

* `cyc a`: the cyclic distance of `a : ZMod N` from `0`, i.e. `min(a.val, N - a.val)` (via `ZMod.valMinAbs`).
* `linkDist e e'`: the `ℓ^∞` cyclic distance of the **base sites** of the links `e, e'`:
  `max_i cyc(e.site i - e'.site i)`. It is a pseudometric on links (`linkDist_self`, `linkDist_symm`,
  `linkDist_triangle`); two links with the same base site have distance `0`. It differs from the note's midpoint distance
  (§1.1) by at most `1/2` per coordinate. With it:
  - links sharing a plaquette are at distance `≤ 1` (`linkDist_le_one_of_plaq`);
  - **time-slab separation** (`slab_separation`): if `e` has base time in `[0, t₁]` and `e'` base time in `[t₂, t₃]`
    (`t₁ ≤ t₂`, `t₃ < N`), then `linkDist e e' ≥ min(t₂ - t₁, N - t₃)`; the second term is the wrap-around gap.
* `wilson_singleLink_timeDecay`: the strong-coupling decay theorem `OneScale.SingleLink.wilson_singleLink_decay` with
  its distance hypothesis discharged: an **unconditional** exponential decay in the time separation of the supports, for
  the Wilson torus measure in the window `6(d - 1) tanh(n β) e^{λ} < 1`, uniformly in the torus size `N`.

Our own construction; the distance is the standard one up to the choice of base sites instead of midpoints.
-/

open MeasureTheory Finset AreaLaw.Concrete

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace OneScale.LinkDist

variable {d N : ℕ}

/-! ## The cyclic distance on `ZMod N` -/

/-- The cyclic distance of `a` from `0` in `ZMod N`. -/
def cyc (a : ZMod N) : ℕ := a.valMinAbs.natAbs

theorem cyc_zero : cyc (0 : ZMod N) = 0 := by simp [cyc, ZMod.valMinAbs_zero]

theorem cyc_neg (a : ZMod N) : cyc (-a) = cyc a := ZMod.natAbs_valMinAbs_neg a

theorem cyc_add_le (a b : ZMod N) : cyc (a + b) ≤ cyc a + cyc b :=
  (ZMod.natAbs_valMinAbs_add_le a b).trans (Int.natAbs_add_le _ _)

theorem cyc_sub_comm (a b : ZMod N) : cyc (a - b) = cyc (b - a) := by
  rw [← neg_sub, cyc_neg]

variable [NeZero N]

theorem cyc_eq_min (a : ZMod N) : cyc a = min a.val (N - a.val) := ZMod.valMinAbs_natAbs_eq_min a

theorem cyc_le_val (a : ZMod N) : cyc a ≤ a.val := by rw [cyc_eq_min]; exact min_le_left _ _

theorem cyc_one_le : cyc (1 : ZMod N) ≤ 1 :=
  (cyc_le_val 1).trans (by rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le _ _)

/-- A lower bound: if `R ≤ a.val` and `a.val + R ≤ N`, then `R ≤ cyc a`. -/
theorem le_cyc {a : ZMod N} {R : ℕ} (h1 : R ≤ a.val) (h2 : a.val + R ≤ N) : R ≤ cyc a := by
  rw [cyc_eq_min]; exact le_min h1 (by omega)

/-- Two residues with representatives in `[0, ℓ]` are at cyclic distance at most `ℓ`. -/
theorem cyc_sub_le_of_val_le {a b : ZMod N} {ℓ : ℕ} (ha : a.val ≤ ℓ) (hb : b.val ≤ ℓ) : cyc (a - b) ≤ ℓ := by
  rcases le_total b.val a.val with h | h
  · exact (cyc_le_val _).trans (by rw [ZMod.val_sub h]; omega)
  · rw [cyc_sub_comm]; exact (cyc_le_val _).trans (by rw [ZMod.val_sub h]; omega)

/-! ## The `ℓ^∞` distance of base sites -/

/-- The `ℓ^∞` cyclic distance of two sites. -/
def siteDist (x y : FinLatticeSites d N) : ℕ := univ.sup fun i => cyc (x i - y i)

theorem cyc_le_siteDist (x y : FinLatticeSites d N) (i : Fin d) : cyc (x i - y i) ≤ siteDist x y :=
  le_sup (f := fun i => cyc (x i - y i)) (mem_univ i)

theorem siteDist_le {x y : FinLatticeSites d N} {R : ℕ} (h : ∀ i, cyc (x i - y i) ≤ R) : siteDist x y ≤ R :=
  Finset.sup_le fun i _ => h i

theorem siteDist_self (x : FinLatticeSites d N) : siteDist x x = 0 :=
  Nat.le_zero.1 (siteDist_le fun i => by rw [sub_self, cyc_zero])

theorem siteDist_symm (x y : FinLatticeSites d N) : siteDist x y = siteDist y x :=
  le_antisymm (siteDist_le fun i => by rw [cyc_sub_comm]; exact cyc_le_siteDist y x i)
    (siteDist_le fun i => by rw [cyc_sub_comm]; exact cyc_le_siteDist x y i)

theorem siteDist_triangle (x y z : FinLatticeSites d N) : siteDist x z ≤ siteDist x y + siteDist y z :=
  siteDist_le fun i => by
    have e : x i - z i = (x i - y i) + (y i - z i) := by ring
    rw [e]
    exact (cyc_add_le _ _).trans (add_le_add (cyc_le_siteDist x y i) (cyc_le_siteDist y z i))

/-- **The link distance**: the `ℓ^∞` cyclic distance of the base sites. -/
def linkDist (e e' : LatticeLink d N) : ℝ := (siteDist e.site e'.site : ℝ)

theorem linkDist_self (e : LatticeLink d N) : linkDist e e = 0 := by
  simp [linkDist, siteDist_self]

theorem linkDist_symm (e e' : LatticeLink d N) : linkDist e e' = linkDist e' e := by
  simp [linkDist, siteDist_symm]

theorem linkDist_triangle (e e' e'' : LatticeLink d N) : linkDist e e'' ≤ linkDist e e' + linkDist e' e'' := by
  unfold linkDist
  exact_mod_cast siteDist_triangle _ _ _

theorem linkDist_nonneg (e e' : LatticeLink d N) : 0 ≤ linkDist e e' := Nat.cast_nonneg _

/-! ## Neighbours -/

/-- Every coordinate of the base site of a plaquette link is that of the plaquette's site, or one more. -/
theorem boundaryLinks_site (p : LatticePlaquette d N) (k : Fin 4) (i : Fin d) :
    (p.boundaryLinks k).site i = p.site i ∨ (p.boundaryLinks k).site i = p.site i + 1 := by
  fin_cases k <;> simp only [LatticePlaquette.boundaryLinks, siteShift, Function.update_apply] <;>
    (try split_ifs) <;> subst_vars <;> simp

theorem cyc_sub_le_one_of_mem {s a b : ZMod N} (ha : a = s ∨ a = s + 1) (hb : b = s ∨ b = s + 1) :
    cyc (a - b) ≤ 1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
  · simp [cyc_zero]
  · rw [show s - (s + 1) = -1 by ring, cyc_neg]; exact cyc_one_le
  · rw [show s + 1 - s = 1 by ring]; exact cyc_one_le
  · simp [cyc_zero]

/-- **Links sharing a plaquette are at distance at most `1`.** -/
theorem linkDist_le_one_of_plaq {e z : LatticeLink d N} {p : LatticePlaquette d N} (he : e ∈ plaqLinks p)
    (hz : z ∈ plaqLinks p) : linkDist z e ≤ 1 := by
  simp only [plaqLinks, mem_image, mem_univ, true_and] at he hz
  obtain ⟨k, rfl⟩ := he
  obtain ⟨k', rfl⟩ := hz
  unfold linkDist
  exact_mod_cast siteDist_le fun i =>
    cyc_sub_le_one_of_mem (boundaryLinks_site p k' i) (boundaryLinks_site p k i)

/-! ## Time slabs -/

variable [NeZero d]

/-- The links whose base site has time coordinate in `[t₁, t₂]` (as representatives in `[0, N)`). -/
def timeSlab (t₁ t₂ : ℕ) : Finset (LatticeLink d N) :=
  univ.filter fun l => t₁ ≤ (l.site 0).val ∧ (l.site 0).val ≤ t₂

theorem mem_timeSlab {t₁ t₂ : ℕ} {l : LatticeLink d N} :
    l ∈ timeSlab t₁ t₂ ↔ t₁ ≤ (l.site 0).val ∧ (l.site 0).val ≤ t₂ := by
  simp [timeSlab]

/-- The time component bounds the distance from below. -/
theorem cyc_time_le_linkDist (e e' : LatticeLink d N) : (cyc (e.site 0 - e'.site 0) : ℝ) ≤ linkDist e e' := by
  unfold linkDist
  exact_mod_cast cyc_le_siteDist e.site e'.site 0

/-- A lower bound on the distance from the time coordinates: if `v = (t' - t).val` (time difference, as a
representative in `[0, N)`) satisfies `R ≤ v ≤ N - R`, the links are at distance at least `R`. -/
theorem le_linkDist_of_time {e e' : LatticeLink d N} {R : ℕ} (h1 : R ≤ (e'.site 0 - e.site 0).val)
    (h2 : (e'.site 0 - e.site 0).val + R ≤ N) : (R : ℝ) ≤ linkDist e e' := by
  refine le_trans ?_ (cyc_time_le_linkDist e e')
  rw [cyc_sub_comm]
  exact_mod_cast le_cyc h1 h2

/-- **Time-slab separation.** Links with base time in `[0, t₁]` and links with base time in `[t₂, t₃]`
(`t₁ ≤ t₂`, `t₃ < N`) are at distance at least `min(t₂ - t₁, N - t₃)`. -/
theorem slab_separation {t₁ t₂ t₃ : ℕ} (h12 : t₁ ≤ t₂) (h3 : t₃ < N) {e e' : LatticeLink d N}
    (he : e ∈ timeSlab 0 t₁) (he' : e' ∈ timeSlab t₂ t₃) :
    ((min (t₂ - t₁) (N - t₃) : ℕ) : ℝ) ≤ linkDist e e' := by
  rw [mem_timeSlab] at he he'
  have hle : (e.site 0).val ≤ (e'.site 0).val := by omega
  apply le_linkDist_of_time
  · rw [ZMod.val_sub hle]; omega
  · rw [ZMod.val_sub hle]; omega

/-! ## The unconditional strong-coupling decay in time -/

section Measure

open OneScale.Gauge OneScale.SingleLink

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G] {n : ℕ} [HasGaugeTrace G n]

variable (hc : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
  (hU : ∀ g : G, HasGaugeTrace.rep (G := G) (n := n) g ∈ Matrix.unitaryGroup (Fin n) ℂ)

include hc hU in
/-- **Strong-coupling decay in the time separation, unconditional.** For the Wilson torus measure with `β ≥ 0` in the
window `γ e^{λ} < 1`, `γ = 6(d - 1) tanh(n β)`: if `f` depends only on links with base time in `[0, t₁]` and `g` only
on links with base time in `[t₂, t₃]` (`t₁ ≤ t₂`, `t₃ < N`), then
`|μ(f g) - μ(f) μ(g)| ≤ (1 - γ e^{λ})⁻¹ · ∑_a δ_a(f) · L_g · e^{-λ min(t₂ - t₁, N - t₃)}`,
with constants independent of `N`. (This is `wilson_singleLink_decay` with the distance `linkDist`.) -/
theorem wilson_singleLink_timeDecay {β : ℝ} (hβ : 0 ≤ β) {lam : ℝ} (hlam : 0 ≤ lam)
    (hρ : ((6 * (d - 1) : ℕ) : ℝ) * Real.tanh (n * β) * Real.exp lam < 1)
    {f g : GaugeConnection G d N → ℝ} (hf : BM f) (hg : BM g) {t₁ t₂ t₃ : ℕ} (h12 : t₁ ≤ t₂) (h3 : t₃ < N)
    (hfA : DepOn f (timeSlab 0 t₁)) (hgS : DepOn g (timeSlab t₂ t₃)) {vf : LatticeLink d N → ℝ}
    (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg) (hvg : OscBound g (fun _ => Lg)) :
    |∫ U, f U * g U ∂(gaugeMeasure n (fun x => Real.exp (β * x))) -
        (∫ U, f U ∂(gaugeMeasure n (fun x => Real.exp (β * x)))) *
          ∫ U, g U ∂(gaugeMeasure n (fun x => Real.exp (β * x)))| ≤
      (1 - ((6 * (d - 1) : ℕ) : ℝ) * Real.tanh (n * β) * Real.exp lam)⁻¹ * (∑ a ∈ timeSlab 0 t₁, vf a) * Lg *
        Real.exp (-(lam * ((min (t₂ - t₁) (N - t₃) : ℕ) : ℝ))) :=
  wilson_singleLink_decay hc hU hβ linkDist linkDist_self linkDist_triangle
    (fun _ _ _ he hz => linkDist_le_one_of_plaq he hz) hlam hρ hf hg hfA hgS hvf hLg hvg
    (fun _ ha _ hb => slab_separation h12 h3 ha hb)

end Measure

end OneScale.LinkDist
