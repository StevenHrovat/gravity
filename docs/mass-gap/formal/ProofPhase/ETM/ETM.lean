/-
The Existence Turing Machine round: the summary (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/ETM.md`.
-/

import ProofPhase.ETM.Rooted

/-!
# The ETM round in one statement

* `emptyIsInitial`: the initial running system is the empty one. The initial direction carries no content, which is
  why the universal property is stated in the terminal direction (`RunSys.univIsTerminal`).
* `etm_round`: the universal object is terminal and not a point; the floor is content; the contraction class reaches
  balance by the explicit bound; the ETM runs every partial recursive content, is lossless, and its balance problem is
  undecidable.

No axioms beyond the standard ones.
-/

open CategoryTheory

noncomputable section

namespace ProofPhase.ETM

universe u

namespace RunSys

variable {δ : ℝ}

/-- The empty running system. -/
def empty (δ : ℝ) : RunSys.{u} δ where
  X := PEmpty
  step := id
  fac x := x.elim
  mass x := x.elim
  fac_nonneg x := x.elim
  fac_le_one x := x.elim
  mass_nonneg x := x.elim
  pays x := x.elim

/-- **The initial object is the empty system** (the initial direction is trivial). -/
def emptyIsInitial : Limits.IsInitial (empty.{u} δ) :=
  Limits.IsInitial.ofUniqueHom
    (fun _ => ⟨fun x => x.elim, fun x => x.elim, fun x => x.elim, fun x => x.elim⟩)
    (fun _ _ => Hom.ext (funext fun x => x.elim))

end RunSys

open RunSys

/-- **The ETM round.** (1) The space of ledgers is the terminal running system, and it is not a point; the floor is
content. (2) The contraction class reaches balance within `ε` by the explicit computable bound. (3) The ETM runs every
partial recursive content, is lossless (outside the class), and whether it reaches balance is undecidable. -/
theorem etm_round (δ : ℝ) :
    Nonempty (Limits.IsTerminal (univ.{u} δ)) ∧
    (∃ a b : (univ.{u} δ).X, (univ.{u} δ).fac a ≠ (univ.{u} δ).fac b) ∧
    (∀ δ', δ < δ' → ¬ ∃ L : Ledger δ, L.f = (fun _ => 1) ∧ L.m = fun n : ℕ => Real.exp (n * δ')) ∧
    (∀ (S : RunSys.{u} δ) (θ : ℝ), S.Contracting θ → ∀ (x : S.X) (M ε q : ℚ),
      Real.exp δ * θ ≤ q → q < 1 → S.mass x ≤ M → 0 < ε → ∀ n ≥ balanceBound M ε q, S.Balanced ε x n) ∧
    (∀ f : ℕ →. ℕ, Nat.Partrec f → ∃ c : Nat.Partrec.Code, ∀ n, (etm.Reaches (1 / 2) (start c n) ↔ (f n).Dom)) ∧
    (∀ θ, ¬ etm.Contracting θ) ∧
    (∀ n, ¬ ComputablePred fun c : Nat.Partrec.Code => etm.Reaches (1 / 2) (start c n)) :=
  ⟨⟨univIsTerminal⟩, univ_nontrivial, fun _ h => (floor_strict h).2, (etm_edge.{u}).1 δ, (etm_edge.{u}).2.1,
    (etm_edge.{u}).2.2.1,
    (etm_edge.{u}).2.2.2⟩

end ProofPhase.ETM
