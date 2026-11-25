/-
O1 as a Perelman-typed, Yang-Mills shaped interface (Draft 7, 2026-11-25).
Released under Apache 2.0.

Paper: Draft 7, III.13 and A.2b (`docs/paper/D7`).
-/

import ProofPhase.Closures.OneBoxForm

/-!
# O1 as a Perelman-typed interface

Draft 6 (II.0.4e) records the first author's reading of O1 as constructable through a PP (Perelman-Poincare) typed, Yang-Mills
shaped interface API. This file builds that interface. Its type is the ledger that Appendix A reads off Perelman's proof (A.1):
steps, a monotone quantity bounded above, and a quantum per boundary event, so that only finitely many boundary events happen.

* **The ledger, for any sequence of steps** (`Ledger`): a quantity `W` along the steps, non-decreasing and bounded above, and a
  quantum `q > 0`: at every step where the statement fails (a boundary event, Perelman's surgery), `W` grows by at least `q`.
* **Finitely many surgeries** (`Ledger.eventually`): from some step on, the statement holds at every step. This is the counting
  argument of Perelman's finite surgery theorem (A.1c): the bounded quantity pays for at most finitely many events.
* **It is not vacuous** (`no_ledger`, `gapless_rejected`, `gapped_accepted`): a statement that fails at arbitrarily late steps has
  no ledger; a toy sequence of one-box sums that tends to `1` (gapless) has none for any bound below `1`; a constant sum below the
  bound has one.
* **Typed for the Yang-Mills box** (`BoxAt`, `Interface`): the steps are the lattice levels, and the statement at level `k` is the
  one-box criterion in every volume, with the shared geometry and constants of `FineOneBox`.
* **An instance gives O1** (`o1Form_of_interface`), and with the resolution clause the gap, torus decay and reflection positivity
  (`gap_of_interface`, through `gap_of_o1Form`, III.9.5).
* **And O1 gives an instance** (`interface_of_o1Form`, `interface_iff`): the interface is exactly O1, in Perelman's shape. It adds
  no proof: it types the open step. The open content sits in one field, `ledger.quantum` together with `ledger.W`: a quantity,
  monotone along the levels and bounded, that grows by a fixed quantum at every level where the box fails.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity ProofPhase.Torus ProofPhase.V3 ProofPhase.V4 ProofPhase.RouteA ProofPhase.OneBox
  ProofPhase.Closures.OneBoxForm

open scoped Classical

noncomputable section

namespace ProofPhase.API.Perelman

/-! ## The ledger, for any sequence of steps -/

/-- **Perelman's ledger as an interface**: along the steps, a quantity `W`, non-decreasing and bounded above by `Wmax`, and a
quantum `q > 0` paid at every boundary event, a step where the statement fails. -/
structure Ledger (holds : ℕ → Prop) where
  W : ℕ → ℝ
  mono : Monotone W
  Wmax : ℝ
  le_max : ∀ k, W k ≤ Wmax
  q : ℝ
  q_pos : 0 < q
  quantum : ∀ k, ¬ holds k → W k + q ≤ W (k + 1)

variable {holds : ℕ → Prop}

/-- If boundary events happen arbitrarily late, the quantity grows past every multiple of the quantum. -/
theorem Ledger.grows (L : Ledger holds) (hfreq : ∀ k₀, ∃ k, k₀ ≤ k ∧ ¬ holds k) :
    ∀ n : ℕ, ∃ k, L.W 0 + n * L.q ≤ L.W k := by
  intro n
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨k', hkk', hf⟩ := hfreq k
    refine ⟨k' + 1, ?_⟩
    have h1 := L.quantum k' hf
    have h2 := L.mono hkk'
    push_cast
    linarith

/-- **Finitely many surgeries**: from some step on, the statement holds at every step. -/
theorem Ledger.eventually (L : Ledger holds) : ∃ k₀, ∀ k, k₀ ≤ k → holds k := by
  by_contra hne
  have hfreq : ∀ k₀, ∃ k, k₀ ≤ k ∧ ¬ holds k := by
    intro k₀
    by_contra h
    exact hne ⟨k₀, fun k hk => by
      by_contra hc
      exact h ⟨k, hk, hc⟩⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((L.Wmax - L.W 0) / L.q)
  obtain ⟨k, hk⟩ := L.grows hfreq n
  have hmax := L.le_max k
  rw [div_lt_iff₀ L.q_pos] at hn
  linarith

/-- **No ledger for a statement that fails arbitrarily late.** -/
theorem no_ledger (hfreq : ∀ k₀, ∃ k, k₀ ≤ k ∧ ¬ holds k) : IsEmpty (Ledger holds) :=
  ⟨fun L => by
    obtain ⟨k₀, h⟩ := L.eventually
    obtain ⟨k, hk, hn⟩ := hfreq k₀
    exact hn (h k hk)⟩

/-- **A gapless toy**: one-box sums `1 − 1/(k + 2)`, tending to `1`. -/
def gaplessSum (k : ℕ) : ℝ := 1 - 1 / ((k : ℝ) + 2)

/-- **The gapless toy is rejected**: for any bound `Γ < 1` there is no ledger for "the sum is at most `Γ`". -/
theorem gapless_rejected (Γ : ℝ) (hΓ : Γ < 1) : IsEmpty (Ledger (fun k => gaplessSum k ≤ Γ)) := by
  apply no_ledger
  intro k₀
  have hpos : 0 < 1 - Γ := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 - Γ))
  refine ⟨max k₀ m, le_max_left _ _, ?_⟩
  unfold gaplessSum
  intro h
  have hk : (m : ℝ) ≤ ((max k₀ m : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
  have h2 : (0 : ℝ) < ((max k₀ m : ℕ) : ℝ) + 2 := by positivity
  have h3 : 1 < (((max k₀ m : ℕ) : ℝ) + 2) * (1 - Γ) := by
    rw [div_lt_iff₀ hpos] at hm
    nlinarith
  have h4 : 1 - Γ ≤ 1 / (((max k₀ m : ℕ) : ℝ) + 2) := by linarith
  rw [le_div_iff₀ h2] at h4
  nlinarith

/-- **A gapped toy is accepted**: a constant sum `1/2` below the bound `1/2` has a ledger (no boundary event at all). -/
def gappedLedger : Ledger (fun _ : ℕ => (1 / 2 : ℝ) ≤ 1 / 2) where
  W _ := 0
  mono := monotone_const
  Wmax := 0
  le_max _ := le_rfl
  q := 1
  q_pos := one_pos
  quantum _ h := absurd le_rfl h

theorem gapped_accepted : Nonempty (Ledger (fun _ : ℕ => (1 / 2 : ℝ) ≤ 1 / 2)) := ⟨gappedLedger⟩

/-! ## Typed for the Yang-Mills box -/

/-- **The box at level `k`**: in every volume, the one-box criterion of `FineOneBox` with the shared geometry `cell` and the
constants `lam`, `γ`, `D₀`, `nmax`. -/
def BoxAt (T : Tuning) (cell : ∀ k j, LatticeLink 4 (T.side k j) → LatticeLink 4 (coarseSide j)) (lam γ D₀ : ℝ) (nmax : ℕ)
    (k : ℕ) : Prop :=
  ∀ j, ∃ (Λ₀ : Finset (FinLatticeSites 4 (coarseSide j))) (κ : FinLatticeSites 4 (coarseSide j) → ℝ)
    (P : BlockSpec ((T.ym k j).map (cellLift (cell k j) (1 : SU2))) (FinLatticeSites 4 (coarseSide j))),
    1 ≤ Λ₀.card ∧ Λ₀.card ≤ nmax ∧ (∀ u ∈ Λ₀, ∀ u' ∈ Λ₀, (siteDist u u' : ℝ) ≤ D₀) ∧
    (∀ t, P.block t = boxBlock Λ₀ t) ∧
    (∀ t, SpecCovariant (liftAct (cell k j) (gaugeAct (T.side k j))) (P.spec t)) ∧
    (∀ t z, z ∉ P.block t →
      IsInfluenceBoundOn (ActAdm (liftAct (cell k j) (gaugeAct (T.side k j))) (P.block t)) (P.block t)
        (P.spec t) z (κ (z.site - t))) ∧
    OneBoxSum κ (boxReach Λ₀) Λ₀ lam γ

/-- **The PP-typed, Yang-Mills shaped interface.** The shared geometry and constants of the box, and Perelman's ledger along the
lattice levels for "the box holds at this level". The open content is the ledger: a quantity, monotone along the levels and
bounded, that grows by a fixed quantum at every level where the box fails. -/
structure Interface (T : Tuning) where
  cell : ∀ k j, LatticeLink 4 (T.side k j) → LatticeLink 4 (coarseSide j)
  c₀ : ℝ
  c₁ : ℝ
  geometry : CellGeometry T cell c₀ c₁
  lam : ℝ
  γ : ℝ
  D₀ : ℝ
  nmax : ℕ
  lam_pos : 0 < lam
  γ_nonneg : 0 ≤ γ
  γ_lt_one : γ < 1
  ledger : Ledger (BoxAt T cell lam γ D₀ nmax)

variable {T : Tuning}

/-- **An instance gives O1**: finitely many surgeries, then the box at every level. -/
theorem o1Form_of_interface (I : Interface T) : O1Form T := by
  obtain ⟨k₀, hk⟩ := I.ledger.eventually
  exact ⟨I.cell, I.c₀, I.c₁, I.geometry, I.lam, I.γ, I.D₀, I.nmax, I.lam_pos, I.γ_nonneg, I.γ_lt_one, k₀,
    fun k hk' j => hk k hk' j⟩

/-- **And with the resolution clause, the gap**: torus decay, the gap in both orders of limits and reflection positivity. -/
theorem gap_of_interface (hres : Tendsto T.ℓ atTop atTop) (I : Interface T) :
    TorusDecayLoc T.toV ∧ MassGapLoc T ∧ MassGapMFLoc T.toV ∧ LimitRP T :=
  gap_of_o1Form hres (o1Form_of_interface I)

/-- **O1 gives an instance**: the quantity counts the levels before the box holds, one quantum each. -/
theorem interface_of_o1Form (h : O1Form T) : Nonempty (Interface T) := by
  obtain ⟨cell, c₀, c₁, geo, lam, γ, D₀, nmax, hlam, hγ0, hγ1, k₀, H⟩ := h
  refine ⟨⟨cell, c₀, c₁, geo, lam, γ, D₀, nmax, hlam, hγ0, hγ1, ?_⟩⟩
  refine ⟨fun k => ((min k k₀ : ℕ) : ℝ), ?_, k₀, ?_, 1, one_pos, ?_⟩
  · intro a b hab
    show ((min a k₀ : ℕ) : ℝ) ≤ ((min b k₀ : ℕ) : ℝ)
    exact Nat.cast_le.mpr (min_le_min (le_of_eq_of_le rfl hab) le_rfl)
  · intro k
    exact_mod_cast min_le_right k k₀
  · intro k hk
    have hlt : k < k₀ := by
      by_contra hge
      exact hk (fun j => H k (by omega) j)
    have e1 : min k k₀ = k := min_eq_left hlt.le
    have e2 : min (k + 1) k₀ = k + 1 := min_eq_left hlt
    simp only [e1, e2]
    push_cast
    exact le_rfl

/-- **The interface is exactly O1**, in Perelman's shape. -/
theorem interface_iff : Nonempty (Interface T) ↔ O1Form T :=
  ⟨fun ⟨I⟩ => o1Form_of_interface I, interface_of_o1Form⟩

end ProofPhase.API.Perelman
