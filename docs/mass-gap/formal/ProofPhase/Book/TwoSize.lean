/-
Proof phase, cycle 6, workstream 5 (c6e-bookkeeping): strategy (a) of version 4 for every volume (2026-11-22).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c6e-bookkeeping/NOTE.md`, section 2.
-/

import ProofPhase.Book.Cells
import ProofPhase.Book.SU2Inst
import ProofPhase.V4.Top
import ProofPhase.Repair.V4Bridge

/-!
# The second blocking `B₂` from `L_*` to `L₁ = 2^r L_*`, for every volume

`V4.Recursion` takes the second blocking `B₂ k j : GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (M j)` as
**any** measurable map onto a torus of side `M j`; nothing in `StageTwoW`, `blockGapBddW_of_stageTwo` or
`yang_mills_assembly_v4_strategyA` assumes equal cells. What was open (c5a NOTE, "Named limitations, Volumes") is a
`B₂` that exists for every `j`. Here:

* `cellCount r j = max 1 ⌊coarseSide j / 2^r⌋`: the number of `L₁` cells per side (`≥ 1`, `≤ coarseSide j`).
* `twoSizeB2 r j = blockMap (coarseSide j) (cellCount r j)`: the Wilson-line blocking of `Book.Cells` onto the cell torus
  of side `cellCount r j`. Measurable (continuous), gauge covariant at the corners, defined for every `j` and `r`.
* Cell sizes (`twoSizeCell_bounds`, `twoSizeCell_uniform`, `twoSizeCell_small`): with `q = 2^r` and `n = coarseSide j`:
  for `q ≤ n` every cell has side `q ≤ side ≤ 2q` and in fact `⌊n/m⌋` or `⌈n/m⌉` with `m = ⌊n/q⌋`; when `q ∣ n` all cells have
  side exactly `q` (the uniform blocking, no new objects); for `n < q` there is one cell, the whole torus.
* `blockGapBddW_twoSize`, `yang_mills_assembly_v4_strategyA_twoSize`, `yang_mills_assembly_v4_strategyA_Ww_twoSize`: the
  recursion lemma and the strategy-(a) theorems with this `B₂`, for **every** volume, with the `L₁` hypotheses
  (`LevelDprimeWOn`/`LevelDprimeWwOn`, `StageTwoW`) stated for this `B₂`.

**Claim level.** Bookkeeping, proved. The scale parameter `s` of `StageTwoW` is a free positive constant: for a nonuniform
cut take `s = 2^(r+1)` (cell sides are at most `2·2^r`); in the uniform case `s = 2^r`. No reflection-positive
structure on `B₂` is required by any existing statement (`hB₂` is `Measurable`), so none is constructed.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  ProofPhase.Torus ProofPhase.V3 ProofPhase.V4

noncomputable section

namespace ProofPhase.Book

open ProofPhase

/-- The number of `L₁` cells per side on the coarse torus of side `coarseSide j`: `⌊coarseSide j / 2^r⌋`, at least `1`. -/
def cellCount (r j : ℕ) : ℕ := max 1 (coarseSide j / 2 ^ r)

theorem cellCount_pos (r j : ℕ) : 0 < cellCount r j := lt_max_of_lt_left Nat.one_pos

instance cellCount_neZero (r j : ℕ) : NeZero (cellCount r j) := ⟨(cellCount_pos r j).ne'⟩

theorem coarseSide_pos (j : ℕ) : 0 < coarseSide j := by unfold coarseSide; omega

theorem cellCount_le (r j : ℕ) : cellCount r j ≤ coarseSide j :=
  max_le (coarseSide_pos j) (Nat.div_le_self _ _)

theorem cellCount_of_le {r j : ℕ} (h : 2 ^ r ≤ coarseSide j) : cellCount r j = coarseSide j / 2 ^ r := by
  unfold cellCount
  exact max_eq_right (Nat.div_pos h ((by positivity)))

/-- **The second blocking `B₂`**: the Wilson-line blocking of the coarse torus onto `cellCount r j` cells per side. -/
def twoSizeB2 (r j : ℕ) : GaugeConnection SU2 4 (coarseSide j) → GaugeConnection SU2 4 (cellCount r j) :=
  blockMap (coarseSide j) (cellCount r j)

theorem twoSizeB2_measurable (r j : ℕ) : Measurable (twoSizeB2 r j) :=
  measurable_blockMap _ _

theorem twoSizeB2_continuous (r j : ℕ) : Continuous (twoSizeB2 r j) :=
  continuous_blockMap _ _

/-- **Gauge covariance of `B₂`** (gauge transformations of the coarse torus act at the cell corners). -/
theorem twoSizeB2_gauge (r j : ℕ) (g : GaugeTransform SU2 4 (coarseSide j)) (U : GaugeConnection SU2 4 (coarseSide j)) :
    twoSizeB2 r j (gaugeTransformConnection g U) =
      gaugeTransformConnection (fun x => g (corner (coarseSide j) (cellCount r j) x)) (twoSizeB2 r j U) :=
  blockMap_gauge _ _ g U

/-! ## Cell sizes -/

/-- **Cells of two sizes, for every volume**: with `q = 2^r`, `n = coarseSide j ≥ q` and `m = cellCount r j = ⌊n/q⌋`, every
cell has side `⌊n/m⌋` or `⌈n/m⌉` (the latter only when `m ∤ n`), and side between `q` and `2q`. -/
theorem twoSizeCell_bounds {r j : ℕ} (h : 2 ^ r ≤ coarseSide j) (i : ℕ) :
    (cellLen (coarseSide j) (cellCount r j) i = coarseSide j / cellCount r j ∨
      (¬ cellCount r j ∣ coarseSide j ∧
        cellLen (coarseSide j) (cellCount r j) i = coarseSide j / cellCount r j + 1)) ∧
    2 ^ r ≤ cellLen (coarseSide j) (cellCount r j) i ∧ cellLen (coarseSide j) (cellCount r j) i ≤ 2 * 2 ^ r := by
  have hq : 0 < 2 ^ r := (by positivity)
  have hm := cellCount_pos r j
  have hmq : cellCount r j = coarseSide j / 2 ^ r := cellCount_of_le h
  refine ⟨cellLen_two_sizes hm i, ?_, ?_⟩
  · refine le_trans ?_ (div_le_cellLen hm i)
    rw [Nat.le_div_iff_mul_le hm]
    have := Nat.div_mul_le_self (coarseSide j) (2 ^ r)
    rw [hmq, Nat.mul_comm]
    exact this
  · refine le_trans (cellLen_le_div_add_one hm i) ?_
    have h1 : coarseSide j < (cellCount r j + 1) * 2 ^ r := by
      rw [hmq]
      have := Nat.lt_mul_div_succ (coarseSide j) hq
      rw [Nat.mul_comm] at this
      exact this
    have h2 : coarseSide j / cellCount r j < 2 * 2 ^ r := by
      rw [Nat.div_lt_iff_lt_mul hm]
      nlinarith
    omega

/-- **The uniform case**: when `2^r ∣ coarseSide j` (and `2^r ≤ coarseSide j`) all cells have side exactly `2^r`. -/
theorem twoSizeCell_uniform {r j : ℕ} (h : 2 ^ r ≤ coarseSide j) (hd : 2 ^ r ∣ coarseSide j) (i : ℕ) :
    cellLen (coarseSide j) (cellCount r j) i = 2 ^ r := by
  have hq : 0 < 2 ^ r := (by positivity)
  have hmq : cellCount r j = coarseSide j / 2 ^ r := cellCount_of_le h
  obtain ⟨c, hc⟩ := hd
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0] at hc; have := coarseSide_pos j; omega
    · exact h0
  have hm : cellCount r j = c := by rw [hmq, hc, Nat.mul_div_cancel_left _ hq]
  have hdvd : cellCount r j ∣ coarseSide j := ⟨2 ^ r, by rw [hm, hc, Nat.mul_comm]⟩
  rw [cellLen_of_dvd hdvd i, hm, hc, Nat.mul_div_cancel _ hcpos]

/-- **A small torus** (`coarseSide j < 2^r`): one cell, the whole torus. -/
theorem twoSizeCell_small {r j : ℕ} (h : coarseSide j < 2 ^ r) :
    cellCount r j = 1 ∧ ∀ i, cellLen (coarseSide j) (cellCount r j) i = coarseSide j := by
  have h1 : cellCount r j = 1 := by
    unfold cellCount
    rw [Nat.div_eq_of_lt h]
    simp
  refine ⟨h1, fun i => ?_⟩
  rw [h1]
  unfold cellLen cutPt
  simp only [Nat.div_one]
  rw [show (i + 1) * coarseSide j = i * coarseSide j + coarseSide j by ring]
  omega

/-- **The cells tile the coarse torus**: the cell lengths add up to the side. -/
theorem twoSize_sum_cellLen (r j : ℕ) :
    ∑ i ∈ range (cellCount r j), cellLen (coarseSide j) (cellCount r j) i = coarseSide j :=
  sum_cellLen (cellCount_pos r j)

/-! ## The recursion lemma and strategy (a) with `B₂` for every volume -/

/-- **The recursion lemma for every volume** (S): `blockGapBddW_of_stageTwo` with `B₂ = twoSizeB2 r`. -/
theorem blockGapBddW_twoSize {T : Tuning} (B₁ : BlockingFamily T) (r : ℕ) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hIR : LawGapBddW (M := cellCount r) (fun k j => (blockedLaw T B₁ k j).map (twoSizeB2 r j)) lam₂)
    (hX : StageTwoW (M := cellCount r) (blockedLaw T B₁) (fun _ j => twoSizeB2 r j) s) :
    ∃ lam : ℝ, 0 < lam ∧ BlockGapBddW T B₁ lam :=
  blockGapBddW_of_stageTwo (M := cellCount r) B₁ (fun _ j => twoSizeB2 r j) (fun _ j => twoSizeB2_measurable r j)
    hs hlam₂ hIR hX

/-- **Strategy (a) of version 4, every volume** (S): `yang_mills_assembly_v4_strategyA` with `B₂ = twoSizeB2 r`. The
`L₁` hypotheses are stated for this `B₂`; no divisibility of the coarse side by `2^r` is needed. -/
theorem yang_mills_assembly_v4_strategyA_twoSize {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T)
    (B₁ : BlockingFamily T) (r : ℕ) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hD : LevelDprimeWOn (M := cellCount r) (fun k j => (blockedLaw T B₁ k j).map (twoSizeB2 r j)) lam₂)
    (hX : StageTwoW (M := cellCount r) (blockedLaw T B₁) (fun _ j => twoSizeB2 r j) s)
    (hUV : ObsTransferPhysTW T B₁) :
    OpenInputsV4 T ∧ TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T :=
  yang_mills_assembly_v4_strategyA (M := cellCount r) hL hN B₁ (fun _ j => twoSizeB2 r j)
    (fun _ j => twoSizeB2_measurable r j) hs hlam₂ hD hX hUV

/-- **Strategy (a) with the weighted hypothesis at `L₁` (c5c), every volume** (S): the same with `LevelDprimeWwOn`
(infinite range, general support) in place of v3's finite-range `LevelDprimeWOn`. -/
theorem yang_mills_assembly_v4_strategyA_Ww_twoSize {T : Tuning} (hL : OnLCP' T) (hN : NonTrivial T)
    (B₁ : BlockingFamily T) (r : ℕ) {s lam₂ : ℝ} (hs : 0 < s) (hlam₂ : 0 < lam₂)
    (hD : ProofPhase.Repair.LevelDprimeWwOn (M := cellCount r)
      (fun k j => (blockedLaw T B₁ k j).map (twoSizeB2 r j)) lam₂)
    (hX : StageTwoW (M := cellCount r) (blockedLaw T B₁) (fun _ j => twoSizeB2 r j) s)
    (hUV : ObsTransferPhysTW T B₁) :
    OpenInputsV4 T ∧ TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T ∧ NonTrivial T := by
  obtain ⟨lam, hlam, hIR⟩ := ProofPhase.Repair.blockGapBddW_of_levelDprimeWwOn (M := cellCount r) B₁
    (fun _ j => twoSizeB2 r j) (fun _ j => twoSizeB2_measurable r j) hs hlam₂ hD hX
  have P : OpenInputsV4 T := ⟨hL, hN, B₁, lam, hlam, hIR, hUV⟩
  exact ⟨P, yang_mills_assembly_v4_inputs P⟩

end ProofPhase.Book
