/-
Proof phase, cycle 6, workstream 5 (c6e-bookkeeping): two-size cells on the periodic torus (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c6e-bookkeeping/NOTE.md`, section 2.
-/

import Mathlib
import AreaLaw.Lattice

/-!
# Cutting a periodic side of length `n` into `m` cells of two sizes, and the Wilson-line blocking onto the cell torus

For every `n ≥ 1` and every number of cells `1 ≤ m ≤ n` the cut points `cutPt n m i = ⌊i n / m⌋` (`i = 0, …, m`) cut the
circle `ℤ/nℤ` into `m` consecutive cells `[cutPt i, cutPt (i+1))` whose lengths are `⌊n/m⌋` or `⌈n/m⌉`
(`cellLen_two_sizes`; exactly `n/m` when `m ∣ n`, `cellLen_of_dvd`). They tile the circle (`sum_cellLen`,
`exists_unique_cell`), also in `d` dimensions (`exists_unique_cell_sites`).

The **blocking onto the cell torus** `blockMap n m : GaugeConnection G d n → GaugeConnection G d m` puts on the link
`(x, μ)` of the torus `(ℤ/mℤ)^d` the ordered product of the fine links along the straight line from the corner of the
cell `x` to the corner of the cell `x + e_μ` (a Wilson line of the cell length). It is continuous, hence measurable
(`measurable_blockMap`), defined for every `n, m` (no divisibility), and gauge covariant for gauge transformations at
the corners (`blockMap_gauge`).
-/

open Finset

noncomputable section

namespace ProofPhase.Book

/-! ## 1. The cut points -/

/-- The cut points of `m` cells on a circle of `n` sites: `⌊i n / m⌋`. -/
def cutPt (n m i : ℕ) : ℕ := i * n / m

/-- The length of cell `i`. -/
def cellLen (n m i : ℕ) : ℕ := cutPt n m (i + 1) - cutPt n m i

theorem cutPt_zero (n m : ℕ) : cutPt n m 0 = 0 := by simp [cutPt]

theorem cutPt_m {n m : ℕ} (hm : 0 < m) : cutPt n m m = n := by
  simp [cutPt, Nat.mul_div_cancel _ hm, Nat.mul_comm]

theorem cutPt_mono (n m : ℕ) : Monotone (cutPt n m) := fun _ _ h =>
  Nat.div_le_div_right (Nat.mul_le_mul_right n h)

theorem cutPt_lt {n m i : ℕ} (hn : 0 < n) (him : i < m) : cutPt n m i < n := by
  unfold cutPt
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  nlinarith

theorem cutPt_add_cellLen (n m i : ℕ) : cutPt n m i + cellLen n m i = cutPt n m (i + 1) := by
  unfold cellLen
  have := cutPt_mono n m (by omega : i ≤ i + 1)
  omega

/-- A cell is at least `⌊n/m⌋` long. -/
theorem div_le_cellLen {n m : ℕ} (hm : 0 < m) (i : ℕ) : n / m ≤ cellLen n m i := by
  unfold cellLen cutPt
  have h1 : i * n / m * m ≤ i * n := Nat.div_mul_le_self _ _
  have h2 : n / m * m ≤ n := Nat.div_mul_le_self _ _
  have h3 : (i * n / m + n / m) ≤ (i + 1) * n / m := by
    rw [Nat.le_div_iff_mul_le hm]
    have : (i * n / m + n / m) * m = i * n / m * m + n / m * m := by ring
    have h4 : (i + 1) * n = i * n + n := by ring
    omega
  omega

/-- A cell is at most `⌊n/m⌋ + 1` long. -/
theorem cellLen_le_div_add_one {n m : ℕ} (hm : 0 < m) (i : ℕ) : cellLen n m i ≤ n / m + 1 := by
  unfold cellLen cutPt
  have h1 : i * n < (i * n / m + 1) * m := by
    have := Nat.lt_mul_div_succ (i * n) hm
    rw [Nat.mul_comm (i * n / m + 1) m]; exact this.trans_eq (by ring_nf)
  have h2 : n < (n / m + 1) * m := by
    have := Nat.lt_mul_div_succ n hm
    rwa [Nat.mul_comm] at this
  have h3 : (i + 1) * n / m < i * n / m + n / m + 2 := by
    rw [Nat.div_lt_iff_lt_mul hm]
    have e1 : (i * n / m + n / m + 2) * m = (i * n / m + 1) * m + (n / m + 1) * m := by ring
    have h4 : (i + 1) * n = i * n + n := by ring
    nlinarith [h1, h2]
  generalize (i + 1) * n / m = X at h3 ⊢
  generalize i * n / m = Y at h3 ⊢
  generalize n / m = Z at h3 ⊢
  omega

/-- When `m ∣ n` all cells have the same length `n/m` (the uniform blocking). -/
theorem cellLen_of_dvd {n m : ℕ} (hd : m ∣ n) (i : ℕ) : cellLen n m i = n / m := by
  obtain ⟨q, rfl⟩ := hd
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [cellLen, cutPt]
  · unfold cellLen cutPt
    have e1 : (i + 1) * (m * q) / m = (i + 1) * q := by
      rw [show (i + 1) * (m * q) = m * ((i + 1) * q) by ring, Nat.mul_div_cancel_left _ hm]
    have e2 : i * (m * q) / m = i * q := by
      rw [show i * (m * q) = m * (i * q) by ring, Nat.mul_div_cancel_left _ hm]
    rw [e1, e2, Nat.mul_div_cancel_left _ hm]
    ring_nf
    omega

/-- **The two cell sizes**: every cell has length `⌊n/m⌋`, or `⌈n/m⌉ = ⌊n/m⌋ + 1` when `m ∤ n`. -/
theorem cellLen_two_sizes {n m : ℕ} (hm : 0 < m) (i : ℕ) :
    cellLen n m i = n / m ∨ (¬ m ∣ n ∧ cellLen n m i = n / m + 1) := by
  by_cases hd : m ∣ n
  · exact Or.inl (cellLen_of_dvd hd i)
  · have h1 := div_le_cellLen (n := n) hm i
    have h2 := cellLen_le_div_add_one (n := n) hm i
    by_cases h : cellLen n m i = n / m
    · exact Or.inl h
    · exact Or.inr ⟨hd, by omega⟩

/-- The cell lengths add up to the circumference. -/
theorem sum_cellLen {n m : ℕ} (hm : 0 < m) : ∑ i ∈ range m, cellLen n m i = n := by
  unfold cellLen
  rw [Finset.sum_range_tsub (cutPt_mono n m), cutPt_m hm, cutPt_zero]
  simp

/-- With `m ≤ n` every cell is nonempty. -/
theorem one_le_cellLen {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) (i : ℕ) : 1 ≤ cellLen n m i :=
  (Nat.div_pos hmn hm).trans_le (div_le_cellLen hm i)

/-- **The cells tile the circle**: every `t < n` lies in exactly one cell `[cutPt a, cutPt (a+1))`, `a < m`. -/
theorem exists_unique_cell {n m : ℕ} (hn : 0 < n) (hm : 0 < m) {t : ℕ} (ht : t < n) :
    ∃! a, a < m ∧ cutPt n m a ≤ t ∧ t < cutPt n m (a + 1) := by
  have hex : ∃ a, a < m ∧ cutPt n m a ≤ t ∧ t < cutPt n m (a + 1) := by
    set a := Nat.findGreatest (fun a => cutPt n m a ≤ t) m with ha
    have h0 : cutPt n m a ≤ t := by
      have := Nat.findGreatest_spec (P := fun a => cutPt n m a ≤ t) (m := 0) (n := m) (Nat.zero_le m)
        (by simp [cutPt_zero])
      exact this
    have hle : a ≤ m := Nat.findGreatest_le m
    have hlt : a < m := by
      rcases hle.lt_or_eq with h | h
      · exact h
      · exfalso
        rw [h, cutPt_m hm] at h0
        omega
    refine ⟨a, hlt, h0, ?_⟩
    by_contra hcon
    have hcon := not_lt.mp hcon
    have := Nat.findGreatest_is_greatest (P := fun a => cutPt n m a ≤ t) (Nat.lt_succ_self a) (by omega : a + 1 ≤ m)
    exact this hcon
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ha, ?_⟩
  rintro b ⟨hb, hb1, hb2⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := cutPt_mono n m (by omega : b + 1 ≤ a)
    omega
  · have := cutPt_mono n m (by omega : a + 1 ≤ b)
    omega

section Sites

variable {d : ℕ}

/-- **The cells tile the torus `(ℤ/nℤ)^d`** (product cells): every site lies in exactly one cell `x ∈ (ℤ/mℤ)^d`. -/
theorem exists_unique_cell_sites {n m : ℕ} [NeZero n] [NeZero m] (y : FinLatticeSites d n) :
    ∃! x : FinLatticeSites d m, ∀ ν, cutPt n m (x ν).val ≤ (y ν).val ∧ (y ν).val < cutPt n m ((x ν).val + 1) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have h1 : ∀ ν, ∃! a, a < m ∧ cutPt n m a ≤ (y ν).val ∧ (y ν).val < cutPt n m (a + 1) :=
    fun ν => exists_unique_cell hn hm (ZMod.val_lt (y ν))
  choose a ha using fun ν => (h1 ν).exists
  refine ⟨fun ν => (a ν : ZMod m), fun ν => ?_, fun x hx => ?_⟩
  · rw [ZMod.val_natCast_of_lt (ha ν).1]
    exact (ha ν).2
  · funext ν
    have hxν := hx ν
    have : (x ν).val = a ν := (h1 ν).unique ⟨ZMod.val_lt (x ν), hxν⟩ (ha ν)
    rw [← this]
    simp

end Sites

/-! ## 2. The blocking onto the cell torus -/

section Block

variable {G : Type*} [Group G] {d : ℕ}

/-- The ordered product `f 0 * f 1 * … * f (k - 1)`. -/
def runProd {A : Type*} (f : ℕ → A → G) : ℕ → A → G
  | 0 => fun _ => 1
  | k + 1 => fun a => runProd f k a * f k a

theorem measurable_runProd {A : Type*} [MeasurableSpace A] [MeasurableSpace G] [MeasurableMul₂ G] {f : ℕ → A → G}
    (hf : ∀ t, Measurable (f t)) (k : ℕ) : Measurable (runProd f k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact ih.mul (hf k)

theorem continuous_runProd {A : Type*} [TopologicalSpace A] [TopologicalSpace G] [IsTopologicalGroup G]
    {f : ℕ → A → G} (hf : ∀ t, Continuous (f t)) (k : ℕ) : Continuous (runProd f k) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih => exact ih.mul (hf k)

theorem runProd_comp {A B : Type*} (f : ℕ → B → G) (φ : A → B) (k : ℕ) (a : A) :
    runProd f k (φ a) = runProd (fun t a => f t (φ a)) k a := by
  induction k with
  | zero => simp [runProd]
  | succ k ih => simp only [runProd]; rw [ih]

/-- Telescoping: a gauge transformation of the factors gives `g₀ · (product) · g_k⁻¹`. -/
theorem runProd_gauge {A : Type*} (f f' : ℕ → A → G) (g : ℕ → A → G)
    (h : ∀ t a, f' t a = g t a * f t a * (g (t + 1) a)⁻¹) (k : ℕ) (a : A) :
    runProd f' k a = g 0 a * runProd f k a * (g k a)⁻¹ := by
  induction k with
  | zero => simp [runProd]
  | succ k ih =>
    simp only [runProd]
    rw [ih, h k a]
    group

variable (n m : ℕ) [NeZero n] [NeZero m]

/-- The corner (lowest site) of the cell `x`. -/
def corner (x : FinLatticeSites d m) : FinLatticeSites d n := fun ν => ((cutPt n m (x ν).val : ℕ) : ZMod n)

/-- The `t`-th site along the line from the corner of the cell `x` in direction `μ`. -/
def runSite (x : FinLatticeSites d m) (μ : Fin d) (t : ℕ) : FinLatticeSites d n :=
  Function.update (corner n m x) μ (((cutPt n m (x μ).val + t : ℕ)) : ZMod n)

/-- **The blocking onto the cell torus**: the link `(x, μ)` of the torus `(ℤ/mℤ)^d` carries the ordered product of the
fine links on the straight line from the corner of the cell `x` to the corner of the cell `x + e_μ`. Defined for all
`n, m`; the cells have the two sizes of `cellLen_two_sizes`. -/
def blockMap (U : GaugeConnection G d n) : GaugeConnection G d m := fun l =>
  runProd (fun t (U : GaugeConnection G d n) => U ⟨runSite n m l.site l.dir t, l.dir⟩)
    (cellLen n m (l.site l.dir).val) U

theorem measurable_blockMap [MeasurableSpace G] [MeasurableMul₂ G] :
    Measurable (blockMap (G := G) (d := d) n m) := by
  refine measurable_pi_iff.2 fun l => ?_
  exact measurable_runProd (f := fun t (U : GaugeConnection G d n) => U ⟨runSite n m l.site l.dir t, l.dir⟩)
    (fun t => measurable_pi_apply _) _

theorem continuous_blockMap [TopologicalSpace G] [IsTopologicalGroup G] :
    Continuous (blockMap (G := G) (d := d) n m) := by
  refine continuous_pi fun l => ?_
  exact continuous_runProd (f := fun t (U : GaugeConnection G d n) => U ⟨runSite n m l.site l.dir t, l.dir⟩)
    (fun t => continuous_apply _) _

/-! ### Gauge covariance -/

theorem runSite_zero (x : FinLatticeSites d m) (μ : Fin d) : runSite n m x μ 0 = corner n m x := by
  unfold runSite
  have : (((cutPt n m (x μ).val + 0 : ℕ)) : ZMod n) = corner n m x μ := by simp [corner]
  rw [this]
  exact Function.update_eq_self μ _

theorem siteShift_runSite (x : FinLatticeSites d m) (μ : Fin d) (t : ℕ) :
    siteShift d n (runSite n m x μ t) μ = runSite n m x μ (t + 1) := by
  unfold siteShift runSite
  simp only [Function.update_self, Function.update_idem]
  congr 2
  push_cast
  ring

theorem runSite_len (x : FinLatticeSites d m) (μ : Fin d) :
    runSite n m x μ (cellLen n m (x μ).val) = corner n m (siteShift d m x μ) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  funext ν
  by_cases hν : ν = μ
  · subst hν
    simp only [runSite, corner, siteShift, Function.update_self]
    rw [cutPt_add_cellLen]
    have hv := ZMod.val_lt (x ν)
    have hval : (x ν + 1).val = ((x ν).val + 1) % m := by
      rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    rw [hval]
    by_cases hlast : (x ν).val + 1 = m
    · rw [hlast, Nat.mod_self, cutPt_m hm, cutPt_zero]
      simp
    · rw [Nat.mod_eq_of_lt (by omega)]
  · simp [runSite, corner, siteShift, Function.update_of_ne hν]

/-- **Gauge covariance of the blocking**: a gauge transformation `g` of the fine field acts on the block field as the
gauge transformation `g ∘ corner` (the sites of the cell torus are the cell corners). -/
theorem blockMap_gauge (g : GaugeTransform G d n) (U : GaugeConnection G d n) :
    blockMap n m (gaugeTransformConnection g U) =
      gaugeTransformConnection (fun x => g (corner n m x)) (blockMap n m U) := by
  funext l
  unfold blockMap
  rw [runProd_comp (fun t (V : GaugeConnection G d n) => V ⟨runSite n m l.site l.dir t, l.dir⟩)
    (gaugeTransformConnection g)]
  rw [runProd_gauge (f := fun t (U : GaugeConnection G d n) => U ⟨runSite n m l.site l.dir t, l.dir⟩)
    (f' := fun t (U : GaugeConnection G d n) =>
      (gaugeTransformConnection g U) ⟨runSite n m l.site l.dir t, l.dir⟩)
    (g := fun t _ => g (runSite n m l.site l.dir t))]
  · simp only [gaugeTransformConnection, LatticeLink.target]
    rw [runSite_zero, runSite_len]
  · intro t U
    simp only [gaugeTransformConnection, LatticeLink.target]
    rw [siteShift_runSite]

end Block

end ProofPhase.Book
