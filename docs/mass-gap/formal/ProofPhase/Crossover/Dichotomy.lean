/-
Proof phase, crossover workstream (c9a-crossover): the worst-case dichotomy, the parts that are exact (2026-11-23).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c9a-crossover/DICHOTOMY.md`.
-/

import ProofPhase.Saturation.EnergyEntropy

/-!
# The worst-case dichotomy: what is exact

The owner's dichotomy for the one-box condition (PREP, "Yang-Mills: the worst case is collapse into CMOS"): for every outside,
either the box contracts, or the non-contracting part is (a) contained, attached to the boundary that carries it, with weight
bounded by its cost, or (b) uncontained, with zero weight. This file proves the parts that are exact and generic.

**1. Attachment (`cob_restrict_eq_zero_of_interior`, `cob_restrict_eq_zero_of_exterior`, `boundaryCell_of_cob_restrict`).**
A `ℤ/2` cochain `τ` on the cells `P` (plaquettes) with coboundary `δτ(q) = ∑_{p ∈ ∂q} τ p` on the cells `Q` (cubes). If `τ` is
closed (`δτ = 0`, M1's closed centre layer), its restriction to a region `R` (the plaquettes of a box) can have nonzero
coboundary only at **boundary cells** (cells with faces both in and outside `R`). Every sheet piece inside the box either closes
inside or ends on the box boundary: it is attached.

**2. Uncontained has zero weight (`not_uncontained`, `measure_uncontained`).** "Uncontained" (a sheet piece ending at an
interior cell) is impossible for a closed `τ`; under any law carried by closed configurations it has measure zero. This is part
(b) of the dichotomy, and it is structural: M1's decoder makes the layer closed, so an open sheet is not in the state space.

**3. Flux in = flux out (`sum_cob_restrict_eq_zero`).** If every plaquette has an even number of cofaces (true on the
hypercubic lattice in `d ≥ 2`: `2(d − 2)` cubes per plaquette, and for `d = 2, 3` with the appropriate cells), the total
coboundary of the restriction vanishes mod 2: an attached sheet enters and leaves the box an even number of times.

**4. The two mechanisms leave a gap (`window_gap`).** Sheets are suppressed (Peierls) when the minimal cost `E_min` of one
sheet plaquette beats an entropy `K' ≥ 2(d − 1)`: `K' e^{−E_min} < 1`. Sheets saturate (`vortex_saturation`) when the cost
oscillation `E` lies in the window `satQ d E < 1`. Since `E_min ≤ E`, both cannot hold: the regimes are disjoint, and every
`E_min ∈ [log(K/(K−1)), log K']` lies in neither (`K = 2(d − 1)`). For `d = 4`: between `log(6/5) ≈ 0.18` and `log K' ≥ log 6
≈ 1.79` nats per plaquette.

**Claim level.** Lean, generic, standard axioms. No Yang–Mills content beyond the closedness of the layer (an input from M1)
and the two existing windows; the weight bound (a) of the dichotomy is not proved here (DICHOTOMY.md says where it fails).
-/

open MeasureTheory Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Crossover

section Chain

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- The `ℤ/2` coboundary of a cochain `τ` on `P` at a cell `q`, whose faces are `inc q`. -/
def cob (inc : Q → Finset P) (τ : P → ZMod 2) (q : Q) : ZMod 2 := ∑ p ∈ inc q, τ p

/-- `τ` is closed: no cell has a nonzero coboundary (M1's closed centre layer). -/
def Closed (inc : Q → Finset P) (τ : P → ZMod 2) : Prop := ∀ q, cob inc τ q = 0

/-- The restriction of `τ` to the region `R` (the plaquettes of a box). -/
def restrictTo (R : Finset P) (τ : P → ZMod 2) : P → ZMod 2 := fun p => if p ∈ R then τ p else 0

/-- A boundary cell of `R`: some face in `R`, some face outside. -/
def BoundaryCell (inc : Q → Finset P) (R : Finset P) (q : Q) : Prop := ¬ inc q ⊆ R ∧ ¬ Disjoint (inc q) R

theorem cob_restrict_eq_zero_of_interior {inc : Q → Finset P} {τ : P → ZMod 2} (h : Closed inc τ) {R : Finset P} {q : Q}
    (hq : inc q ⊆ R) : cob inc (restrictTo R τ) q = 0 := by
  have : cob inc (restrictTo R τ) q = cob inc τ q := by
    unfold cob restrictTo
    exact sum_congr rfl fun p hp => by simp [hq hp]
  rw [this]; exact h q

theorem cob_restrict_eq_zero_of_exterior {inc : Q → Finset P} {τ : P → ZMod 2} {R : Finset P} {q : Q}
    (hq : Disjoint (inc q) R) : cob inc (restrictTo R τ) q = 0 := by
  unfold cob restrictTo
  exact sum_eq_zero fun p hp => by simp [Finset.disjoint_left.1 hq hp]

/-- **Attachment** (S): a closed cochain restricted to a region has nonzero coboundary only at boundary cells. -/
theorem boundaryCell_of_cob_restrict {inc : Q → Finset P} {τ : P → ZMod 2} (h : Closed inc τ) {R : Finset P} {q : Q}
    (hq : cob inc (restrictTo R τ) q ≠ 0) : BoundaryCell inc R q :=
  ⟨fun hs => hq (cob_restrict_eq_zero_of_interior h hs), fun hd => hq (cob_restrict_eq_zero_of_exterior hd)⟩

/-- **The boundary flux is a function of the outside** (S): for a closed cochain, the coboundary of its restriction to `R`
equals the coboundary of its restriction to the complement. So the flux a box must carry is fixed by the outside
configuration alone (measurable with respect to the outside variables). -/
theorem cob_restrict_eq_cob_restrict_compl {inc : Q → Finset P} {τ : P → ZMod 2} (h : Closed inc τ) (R : Finset P) (q : Q) :
    cob inc (restrictTo R τ) q = cob inc (restrictTo Rᶜ τ) q := by
  have hsum : cob inc (restrictTo R τ) q + cob inc (restrictTo Rᶜ τ) q = cob inc τ q := by
    unfold cob restrictTo
    rw [← sum_add_distrib]
    refine sum_congr rfl fun p _ => ?_
    by_cases hp : p ∈ R <;> simp [hp]
  have h0 := h q
  rw [h0] at hsum
  have : cob inc (restrictTo R τ) q = -cob inc (restrictTo Rᶜ τ) q := eq_neg_of_add_eq_zero_left hsum
  rw [this, ZMod.neg_eq_self_mod_two]

/-- **Uncontained**: the restricted sheet ends at a cell all of whose faces lie in the box. -/
def Uncontained (inc : Q → Finset P) (R : Finset P) (τ : P → ZMod 2) : Prop :=
  ∃ q, inc q ⊆ R ∧ cob inc (restrictTo R τ) q ≠ 0

theorem not_uncontained {inc : Q → Finset P} {τ : P → ZMod 2} (h : Closed inc τ) (R : Finset P) :
    ¬ Uncontained inc R τ := fun ⟨_, hs, hq⟩ => hq (cob_restrict_eq_zero_of_interior h hs)

/-- **Uncontained has zero weight** (S): under any law carried by closed configurations. -/
theorem measure_uncontained {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {inc : Q → Finset P} (τ : Ω → P → ZMod 2)
    (hcl : ∀ᵐ ω ∂μ, Closed inc (τ ω)) (R : Finset P) : μ {ω | Uncontained inc R (τ ω)} = 0 := by
  have h : ∀ᵐ ω ∂μ, ¬ Uncontained inc R (τ ω) := hcl.mono fun ω hω => not_uncontained hω R
  rw [ae_iff] at h
  simpa using h

/-- **Flux in = flux out** (S): if every plaquette has an even number of cofaces, the coboundary of the restriction of any
cochain sums to zero mod 2 (so, for a closed cochain, the boundary cells carrying flux come in even number, counted mod 2). -/
theorem sum_cob_restrict_eq_zero (inc : Q → Finset P) (hev : ∀ p, Even ((univ.filter fun q => p ∈ inc q).card))
    (τ : P → ZMod 2) (R : Finset P) : ∑ q, cob inc (restrictTo R τ) q = 0 := by
  unfold cob
  have hsw : ∑ q, ∑ p ∈ inc q, restrictTo R τ p
      = ∑ p, ((univ.filter fun q => p ∈ inc q).card : ZMod 2) * restrictTo R τ p := by
    have e1 : ∀ q, ∑ p ∈ inc q, restrictTo R τ p = ∑ p, if p ∈ inc q then restrictTo R τ p else 0 := by
      intro q; rw [← sum_filter]; congr 1; ext p; simp
    simp_rw [e1]
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  rw [hsw]
  refine sum_eq_zero fun p _ => ?_
  obtain ⟨k, hk⟩ := hev p
  rw [hk]
  have : ((k + k : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_add, ← two_mul]; exact mul_eq_zero_of_left (by decide) _
  rw [this, zero_mul]

end Chain

/-! ## The two mechanisms leave a gap -/

/-- **The suppression window and the saturation window are disjoint** (S). If sheets are Peierls-suppressed
(`K' e^{−E_min} < 1` with an entropy `K' ≥ 2(d − 1)`) and saturate (`satQ d E < 1`, `vortex_saturation`'s window), with
`E_min ≤ E` (the minimal cost of a sheet plaquette is at most its cost oscillation), we get a contradiction. -/
theorem window_gap {d : ℕ} (hd : 2 ≤ d) {E Emin K' : ℝ} (hK' : 2 * ((d : ℝ) - 1) ≤ K') (hsat : ProofPhase.Saturation.satQ d E < 1)
    (hEm : Emin ≤ E) (hP : K' * Real.exp (-Emin) < 1) : False := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set K := 2 * ((d : ℝ) - 1) with hK
  have hK2 : 2 ≤ K := by rw [hK]; linarith
  have hE : E < Real.log (K / (K - 1)) := (ProofPhase.Saturation.satQ_lt_one_iff hd E).1 hsat
  have hlog : Real.log (K / (K - 1)) ≤ Real.log K := by
    apply Real.log_le_log (div_pos (by linarith) (by linarith))
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hKexp : K' < Real.exp Emin := by
    have h1 : K' * Real.exp (-Emin) * Real.exp Emin < 1 * Real.exp Emin :=
      mul_lt_mul_of_pos_right hP (Real.exp_pos _)
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at h1
  have hlogK : Real.log K < Emin := by
    rw [Real.log_lt_iff_lt_exp (by linarith)]; linarith
  linarith

end ProofPhase.Crossover
