/-
The form layer as one API: a facade over the unified ledger, the encoder, transport and the ETM (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/API.md` (the how-to), `docs/unified/UNIFIED.md`, `ENCODER.md`, `ETM.md`, `TRANSPORT.md`.
-/

import ProofPhase.Unified.Ledger
import ProofPhase.Unified.Encoder
import ProofPhase.Unified.Transport
import ProofPhase.ETM.Machine

/-!
# The form layer as an API: `import ProofPhase.API`, `open ProofPhase.API`

**What this file is.** A facade. It moves, renames and edits nothing: every theorem below is either a re-export
(`export`, `alias`, `abbrev`) of a proved declaration of the form layer, or a thin wrapper whose proof is one call into it.
The form layer says nothing about content. A new problem uses it by supplying **a well-defined input**, **a proved
structure** (the data of a running system, checked), and **one named open step**; the rest is free.

**The concepts, one structure each** (plain words; the how-to is `docs/unified/API.md`).

| concept | structure | what you supply | what you get for free |
|---|---|---|---|
| a running system | `RunSys δ` | step, factor in `[0, 1]`, mass `≥ 0`, the ledger law | `S.carry`, `S.contract`, `S.decay_cost`, the trace into the ledger, `settle`, `edge` |
| a chain with costs | `Chain δ` | a quantity `M`, costs `c`, each step pays its cost up to the floor `δ` | `ledger`, `decay`, `summable`, `size`, `size_log` |
| a margin that survives | `Margin` | a quantity `M`, shares `f ≥ 0` kept per step | `survive`, `nonneg`, `pos` |
| an encoder at a boundary | `Encoder 𝕜 E` | a state and its rotated image of the same norm | the reflection coefficient, the Szego and electric factors in `[0, 1]`, the cost |
| an uncertainty | `Uncertainty δ` | error bound `e`, factor `f`, fresh uncertainty `r`, the transport law | `bounded`, `critical`, `sign` (and a run is one with `r = 0`: `RunSys.uncertainty`) |
| the settle bound, the edge | `settle`, `edge` | `Contracting θ` (cost above the floor) | an explicit step count; the lossless ETM is universal and undecidable |
| the problem card | `Problem` | input type, named open step, conclusion, the proof "open step gives conclusion" | `Problem.holds` |
| the open-step slot | `OpenStep name P` | the statement `P` of the one running-state hypothesis | (a label; `P` itself) |
| the external-input slot | `External source P` | a theorem imported from the literature, with its source | (a label; `P` itself) |
| the computable layer | `szegoQ`, `elecQ`, `PaysQ`, `settle0`, `balanceBound` | rational data | decisions that run (`#eval`, `decide`), each proved right for the real system (section 8) |
| the G0 link | `Phase`, `PhaseLabel`, `ChargeQuantisation` | a continuous character of the circle | integer charge (section 9; discharged in `API/Phase.lean`) |

The core (this file and what it imports: `Unified/Ledger`, `Unified/Encoder`, `Unified/Transport`, `ETM/RunSys`,
`ETM/Machine`) imports only Mathlib; the instances (`API/Template`, `API/YangMills`, `API/GRH`, `API/NP`, `API/Phase`)
import it and are not part of it (`docs/unified/API.md`, section 7).

The three problems are written in this shape in `API/YangMills.lean`, `API/GRH.lean`, `API/NP.lean`; a toy, fully
worked, is `API/Template.lean`. No axioms beyond the standard ones.
-/

open Finset

noncomputable section

namespace ProofPhase.API

universe v

/-! ## 1. The two slots: the open step and the external input -/

/-- **The open-step slot** (the running-state hypothesis of a problem). Write the one statement the problem still needs as
`OpenStep "plain-words name" (statement)`. It *is* that statement (a transparent label, `abbrev`), so theorems take it as
an ordinary hypothesis `(h : OpenStep "..." P)`, and a reader can grep for every `OpenStep` to see all open steps of a
project. Nothing is assumed anywhere: the open step is always a hypothesis of a theorem, never an axiom. -/
abbrev OpenStep (_name : String) (P : Prop) : Prop := P

/-- **The external-input slot** (a theorem taken from the literature, not proved here). Write it as
`External "source" (statement)`. Like `OpenStep` it is transparent and is always a hypothesis, never an axiom; the
`source` string says where the statement comes from, so the dependence on outside results is visible and greppable. -/
abbrev External (_source : String) (P : Prop) : Prop := P

/-! ## 2. A running system and its ledger theorems -/

/-- **A running system** with floor `δ`: states `X`, a transfer `step`, an encoder factor `fac x ∈ [0, 1]`, a mass
`mass x ≥ 0`, and the ledger law `mass (step x) ≤ e^δ · fac x · mass x` (every step pays its factor, up to the floor).
This is `ETM.RunSys`; a one-line check of the four fields is all an instance has to prove. -/
abbrev RunSys (δ : ℝ) := ProofPhase.ETM.RunSys.{v} δ

/- On a running system `S`, the ledger theorems are used with dot notation (they are `ETM.RunSys.*`, found through the
`abbrev`): `S.carry x n` (mass after `n` steps is at most the product of the factors times the start), `S.contract hθ x n`
(factors at most `θ`: decay `(e^δ θ)^n`), `S.decay_cost hf x n` (positive factors: `e^{n δ − Σ cost}`), `S.trace` (the unique
map into the space of ledgers), `S.Contracting θ`, `S.Balanced ε x n`, `S.Reaches ε x`. -/

/-- **The settle bound.** On the contraction class (`Contracting θ`: every factor at most `θ`, `e^δ θ < 1`, a cost above
the floor) a run from mass at most `M` is within `ε` of balance at every step `n ≥ balanceBound M ε q`, an explicit
computable number (any rational `q` with `e^δ θ ≤ q < 1`). Use as `settle S hS x ...`. -/
alias settle := ProofPhase.ETM.RunSys.reaches_of_contracting

/-- **Settling is unconditional on the class**: every run reaches balance within any `ε > 0`. -/
alias settle_everywhere := ProofPhase.ETM.RunSys.reaches_of_contracting'

/-- **The unbounded search is a bounded one** on the contraction class, and it succeeds. -/
alias settle_iff_bounded := ProofPhase.ETM.RunSys.reaches_iff_bounded

/-- **The decidability edge.** Cost above the floor: balance is decided, with an explicit bound. Cost equal to the floor
(lossless, `etm`): Turing-universal, balance undecidable, and `etm` is not in the contraction class. -/
alias edge := ProofPhase.ETM.etm_edge

export ProofPhase.ETM (balanceBound etm etmTruth etm_truth_edge estep_primrec halted_primrec)

/-! ## 3. A chain with costs: decay, gap, size -/

/-- **A chain with costs.** A nonnegative quantity `M n` (an influence, a count, a norm) and a cost `c i` per step: each
step keeps at most the share `e^{−c i}` of it, up to the floor `δ`: `M (i+1) ≤ e^{δ − c i} · M i`. The gap is cost minus
floor. (For a finite horizon use the raw `Pays` and its theorems, exported below.) -/
structure Chain (δ : ℝ) where
  /-- The carried quantity before step `n`. -/
  M : ℕ → ℝ
  /-- The cost of step `n`. -/
  c : ℕ → ℝ
  M_nonneg : ∀ n, 0 ≤ M n
  /-- Each step pays its cost up to the floor. -/
  step : ∀ i, M (i + 1) ≤ Real.exp (δ - c i) * M i

namespace Chain

variable {δ : ℝ} (C : Chain δ)

/-- The chain as the finite-horizon statement of the ledger (`Pays`). -/
theorem pays (n : ℕ) : ProofPhase.Unified.Pays C.M C.c δ n := fun i _ => C.step i

/-- **Decay, general form**: `M n ≤ e^{n δ − Σ c} M 0`. -/
theorem ledger (n : ℕ) : C.M n ≤ Real.exp (n * δ - ∑ i ∈ range n, C.c i) * C.M 0 :=
  ProofPhase.Unified.ledger (C.pays n)

/-- **Decay at a uniform cost**: every cost at least `κ` gives `M n ≤ e^{−n (κ − δ)} M 0`. -/
theorem decay {κ : ℝ} (hκ : ∀ i, κ ≤ C.c i) (n : ℕ) : C.M n ≤ Real.exp (-(n * (κ - δ))) * C.M 0 :=
  ProofPhase.Unified.decay (C.pays n) (fun i _ => hκ i) (C.M_nonneg 0)

/-- **The gap is cost minus floor**: with every cost at least `κ > δ`, the sum of `M` converges. -/
theorem summable {κ : ℝ} (hκ : ∀ i, κ ≤ C.c i) (hgap : δ < κ) : Summable C.M :=
  ProofPhase.Unified.summable_of_gap C.pays hκ hgap C.M_nonneg

/-- **Size**: a quantum `φ` left at step `n` forces `φ e^{Σ c − n δ} ≤ M 0` (the ledger read backwards). -/
theorem size {φ : ℝ} {n : ℕ} (hφ : φ ≤ C.M n) : φ * Real.exp (∑ i ∈ range n, C.c i - n * δ) ≤ C.M 0 :=
  ProofPhase.Unified.size (C.pays n) hφ

/-- **Size in log units**: `Σ c − n δ + log φ ≤ log (M 0)`. -/
theorem size_log {φ : ℝ} {n : ℕ} (hφ0 : 0 < φ) (hφ : φ ≤ C.M n) :
    ∑ i ∈ range n, C.c i - n * δ + Real.log φ ≤ Real.log (C.M 0) :=
  ProofPhase.Unified.size_log (C.pays n) hφ0 hφ

end Chain

export ProofPhase.Unified (Pays Carries carry ledger decay size size_log summable_of_gap accrue CostAboveFloor
  rate_of_costAboveFloor)

/-! ## 4. A margin that survives: lower certificates -/

/-- **A margin.** A quantity `M n` (a lower bound of a margin, a positivity certificate) and a share `f i ≥ 0` kept per
step: `f i · M i ≤ M (i+1)`. A price may shrink a margin, never flip its sign. -/
structure Margin where
  /-- The margin before step `n`. -/
  M : ℕ → ℝ
  /-- The share kept by step `n`. -/
  f : ℕ → ℝ
  f_nonneg : ∀ i, 0 ≤ f i
  keeps : ∀ i, f i * M i ≤ M (i + 1)

namespace Margin

variable (A : Margin)

/-- **Survival**: `M n ≥ (∏_{i<n} f i) · M 0`. -/
theorem survive (n : ℕ) : (∏ i ∈ range n, A.f i) * A.M 0 ≤ A.M n :=
  ProofPhase.Unified.survive (fun i _ => A.f_nonneg i) (fun i _ => A.keeps i)

/-- A nonnegative margin stays nonnegative. -/
theorem nonneg (h0 : 0 ≤ A.M 0) (n : ℕ) : 0 ≤ A.M n :=
  (mul_nonneg (prod_nonneg fun i _ => A.f_nonneg i) h0).trans (A.survive n)

/-- **A positive margin stays positive when every share is positive** (a real, finite cost at every step). -/
theorem pos (hf : ∀ i, 0 < A.f i) (h0 : 0 < A.M 0) (n : ℕ) : 0 < A.M n :=
  (mul_pos (prod_pos fun i _ => hf i) h0).trans_le (A.survive n)

end Margin

export ProofPhase.Unified (survive survive_pos)

/-! ## 5. The encoder at a boundary -/

/-- **An encoder** at a boundary: a state `ψ` passed on by the inside and its rotated image `ψ'` seen from the outside,
of the same norm (the shared root), in a space with a positive form. Its one number is the reflection coefficient
`c = ⟪ψ, ψ'⟫ / ‖ψ‖²` (`Encoder.refl`), with `‖c‖ ≤ 1` (`Encoder.norm_refl_le`). -/
abbrev Encoder (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] :=
  ProofPhase.Unified.Encoder 𝕜 E

namespace Encoder

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **The Szego factor** of an encoder, `1 − ‖c‖²`: the share of the state not carried by its mirror image. -/
def szegoFactor (X : Encoder 𝕜 E) : ℝ := ProofPhase.Unified.szego X.refl

/-- **The electric factor** of an encoder, `(1 − c)/(1 + c)` at `c = re (refl)`: the odd share over the even share. -/
def elecFactor (X : Encoder 𝕜 E) : ℝ := ProofPhase.Unified.elec (RCLike.re X.refl)

/-- **Positivity puts the Szego factor in `[0, 1]`**, so an encoder chain is a ledger with factors in `[0, 1]`. -/
theorem szegoFactor_mem (X : Encoder 𝕜 E) : 0 ≤ X.szegoFactor ∧ X.szegoFactor ≤ 1 :=
  ProofPhase.Unified.szego_mem X

end Encoder

/-- **The cost of a factor**: `−log f`. Cost zero is factor one; cost `≥ 0` is factor `≤ 1`
(`Unified.cost_eq_zero_iff`, `cost_nonneg_iff`); the ledger pays `e^{−cost}` per step. -/
def cost (f : ℝ) : ℝ := -Real.log f

export ProofPhase.Unified (szego elec pays_of_factors costAboveFloor_of_factor_le)

/-! ## 6. An uncertainty transported across the chain -/

/-- **An uncertainty.** An error bound `e n ≥ 0` on the state at step `n`, carried by a step with factor `f n` (floor
`δ`) plus the fresh uncertainty `r n ≥ 0` that the step itself adds: `e (n+1) ≤ e^δ · f n · e n + r n`. With `r = 0` this
is the ledger law. -/
structure Uncertainty (δ : ℝ) where
  /-- The error bound before step `n`. -/
  e : ℕ → ℝ
  /-- The factor of step `n`. -/
  f : ℕ → ℝ
  /-- The fresh uncertainty added by step `n`. -/
  r : ℕ → ℝ
  e0_nonneg : 0 ≤ e 0
  f_nonneg : ∀ i, 0 ≤ f i
  r_nonneg : ∀ i, 0 ≤ r i
  /-- The transport law. -/
  step : ∀ i, e (i + 1) ≤ Real.exp δ * f i * e i + r i

namespace Uncertainty

variable {δ : ℝ} (U : Uncertainty δ)

/-- The uncertainty as the finite-horizon statement of transport (`Transports`). -/
theorem transports (n : ℕ) : ProofPhase.Unified.Transports U.e U.f U.r δ n := fun i _ => U.step i

/-- **Closed form**: `e n` is at most the transported start, `(∏ e^δ f) e₀ + Σ_j (∏_{j<i<n} e^δ f) r j`. -/
theorem closed_form (n : ℕ) : U.e n ≤ ProofPhase.Unified.acc (fun i => Real.exp δ * U.f i) U.r (U.e 0) n :=
  ProofPhase.Unified.transport (U.transports n) fun i _ => U.f_nonneg i

/-- **(a) Bounded transport**: factors at most `θ` with `q = e^δ θ < 1` and fresh uncertainty at most `R` keep the
uncertainty below `e 0 + R / (1 − q)` at every step. -/
theorem bounded {θ R : ℝ} (hθ : ∀ i, U.f i ≤ θ) (hq : Real.exp δ * θ < 1) (hR : ∀ i, U.r i ≤ R) (n : ℕ) :
    U.e n ≤ U.e 0 + R / (1 - Real.exp δ * θ) :=
  (ProofPhase.Unified.bounded_transport (U.transports n) U.f_nonneg hθ hq U.r_nonneg hR U.e0_nonneg).2

/-- **(b) Critical transport** (cost = floor, `e^δ f = 1`): no damping, `e n ≤ e 0 + Σ_{j<n} r j`. Sharp. -/
theorem critical (hcrit : ∀ i, Real.exp δ * U.f i = 1) (n : ℕ) : U.e n ≤ U.e 0 + ∑ j ∈ range n, U.r j :=
  ProofPhase.Unified.critical_transport (U.transports n) fun i _ => hcrit i

/-- **(c) Sign preserved.** `M` has margin `m n ≤ M n`; the quantity `N` across the boundary differs from `M` by at most
the uncertainty, `|N n − M n| ≤ e n`; the uncertainty stays below the margin, `e n < m n`. Then `N n > 0` at every
step. -/
theorem sign {M N m : ℕ → ℝ} (hm : ∀ n, m n ≤ M n) (hN : ∀ n, |N n - M n| ≤ U.e n) (hlt : ∀ n, U.e n < m n)
    (n : ℕ) : 0 < N n := by
  have := ProofPhase.Unified.sign_transport hm hN hlt n
  linarith [this.1, this.2]

/-- **(a) + (c)**: a bounded transport certifies the sign as soon as `e 0 + R / (1 − q)` is below a uniform margin `μ`. -/
theorem sign_of_bounded {M N m : ℕ → ℝ} {θ R μ : ℝ} (hm : ∀ n, m n ≤ M n) (hμ : ∀ n, μ ≤ m n)
    (hN : ∀ n, |N n - M n| ≤ U.e n) (hθ : ∀ i, U.f i ≤ θ) (hq : Real.exp δ * θ < 1) (hR : ∀ i, U.r i ≤ R)
    (hbound : U.e 0 + R / (1 - Real.exp δ * θ) < μ) (n : ℕ) : 0 < N n :=
  ProofPhase.Unified.sign_of_bounded hm hμ hN (fun n => U.transports n) U.f_nonneg hθ hq U.r_nonneg hR U.e0_nonneg
    hbound n

end Uncertainty

/-- **A run is an uncertainty with `r = 0`**: the mass along the run from `x` is transported by the factors. This is the
exact sense in which the ledger is the case "no fresh uncertainty". -/
def RunSys.uncertainty {δ : ℝ} (S : RunSys.{v} δ) (x : S.X) : Uncertainty δ where
  e n := S.mass (S.step^[n] x)
  f n := S.fac (S.step^[n] x)
  r _ := 0
  e0_nonneg := S.mass_nonneg x
  f_nonneg _ := S.fac_nonneg _
  r_nonneg _ := le_rfl
  step n := by
    rw [add_zero, Function.iterate_succ_apply']
    exact S.pays _

export ProofPhase.Unified (Transports acc transport critical_transport bounded_transport sign_transport)

/-! ## 7. The problem card: input + structure + one named open step -/

/-- **A problem in the form layer.** The shape the owner observed: a *well-defined input* (`Input`), a *named open step*
(`Open`, a running-state hypothesis on the input, written with `OpenStep`), a *conclusion* (`Concl`), and the *proved
structure*: from the input and the open step, the conclusion (`proved`). `sources` lists the `External` inputs the
statement leans on. Everything else is free: the ledger theorems act on the `Chain`s, `RunSys` and `Uncertainty`s that
the instance builds. -/
structure Problem where
  /-- A plain-words name. -/
  name : String
  /-- The well-defined input. -/
  Input : Type v
  /-- The one named open step (running-state hypothesis), per input. -/
  Open : Input → Prop
  /-- The conclusion, per input. -/
  Concl : Input → Prop
  /-- The statements imported from the literature, as `source` strings (those used with `External`). -/
  sources : List String := []
  /-- **The proved structure**: input and open step give the conclusion. -/
  proved : ∀ i, Open i → Concl i

/-- **The card read once**: if the open step holds for an input, so does the conclusion. -/
theorem Problem.holds (P : Problem.{v}) (i : P.Input) (h : P.Open i) : P.Concl i := P.proved i h

/-! ## 8. What runs and what is truth only

A running system replaces a *choice* by a *link to G0*: every decision it makes has a computable form (an explicit bound,
a decidable check, a computed factor) whose correctness is a theorem about the real-valued system. The real-valued
structures above (`RunSys`, `Chain`, `Margin`, `Uncertainty`, `Contracting`) are classical statements: they are the
truth side and are not computed. The computable layer works on rational data:

* `balanceBound` (re-exported): the settle bound, a `ℕ` computed from `M ε q`;
* `szegoQ`, `elecQ`: the encoder factor from a rational reflection coefficient (`szegoQ_cast`, `elecQ_cast`: equal to the
  real factors);
* `PaysQ`: the ledger law on a finite horizon of rational data, with a `Decidable` instance (`decide` runs it);
  `PaysQ.pays` turns a passing check into the real ledger `Pays`;
* `settle0`: floor `0`, a rational contraction bound `q < 1` and a rational tolerance: every hypothesis the decision
  needs is a decidable inequality on `ℚ`, and the count is `balanceBound`.

Truth only (`noncomputable`): `etmTruth` (the binary truth of "the ETM reaches balance", re-exported; not computable,
`etm_truth_edge`). -/

/-- **The Szego factor of a rational reflection coefficient**, computed. -/
def szegoQ (c : ℚ) : ℚ := 1 - c ^ 2

/-- **The electric factor of a rational reflection coefficient**, computed. -/
def elecQ (c : ℚ) : ℚ := (1 - c) / (1 + c)

/-- The computed Szego factor is the real one. -/
theorem szegoQ_cast (c : ℚ) : ((szegoQ c : ℚ) : ℝ) = ProofPhase.Unified.szego (c : ℝ) := by
  unfold szegoQ ProofPhase.Unified.szego
  rw [Real.norm_eq_abs, sq_abs]
  push_cast
  ring

/-- The computed electric factor is the real one. -/
theorem elecQ_cast (c : ℚ) : ((elecQ c : ℚ) : ℝ) = ProofPhase.Unified.elec (c : ℝ) := by
  simp [elecQ, ProofPhase.Unified.elec]

/-- **The ledger law on rational data over a finite horizon**: `M (i+1) ≤ f i · M i` for `i < n`. Decidable: a closed
instance is checked by `decide` or `#guard`. -/
def PaysQ (M f : ℕ → ℚ) (n : ℕ) : Prop := ∀ i < n, M (i + 1) ≤ f i * M i

instance (M f : ℕ → ℚ) (n : ℕ) : Decidable (PaysQ M f n) := inferInstanceAs (Decidable (∀ i < n, _))

/-- **A passing check is the real ledger**: with positive factors, rational data satisfying the law pay the costs
`−log f`, floor `0`. -/
theorem PaysQ.pays {M f : ℕ → ℚ} {n : ℕ} (h : PaysQ M f n) (hf : ∀ i < n, 0 < f i) :
    ProofPhase.Unified.Pays (fun i => ((M i : ℚ) : ℝ)) (fun i => -Real.log ((f i : ℚ) : ℝ)) 0 n :=
  ProofPhase.Unified.pays_of_factors (fun i hi => by exact_mod_cast hf i hi) fun i hi => by exact_mod_cast h i hi

/-- **Settle with a computed count** (floor `0`). Every decision is a decidable inequality on rationals (`q < 1`,
`0 < ε`); the only link to the system is `hfac` (every factor is at most `q`) and `hM` (the start mass is at most `M`);
the count is `balanceBound M ε q`, an ordinary computation. -/
theorem settle0 (S : RunSys 0) {q : ℚ} (hq : q < 1) (hfac : ∀ x, S.fac x ≤ q) (x : S.X) {M ε : ℚ}
    (hM : S.mass x ≤ M) (hε : 0 < ε) : ∀ n ≥ balanceBound M ε q, S.Balanced ε x n :=
  ProofPhase.ETM.RunSys.reaches_of_contracting S (θ := (q : ℝ))
    ⟨hfac, by rw [Real.exp_zero, one_mul]; exact_mod_cast hq⟩ x (by rw [Real.exp_zero, one_mul]) hq hM hε

/-! ## 9. The G0 link: the phase field and charge quantisation

G0's phase field is one compact `U(1)`, Mathlib's `Circle`. A label carried on it is a continuous character
`z ↦ χ z` of the circle. The classical fact (Pontryagin duality for the circle) is that every such character is `z ↦ z ^ n`
for an integer `n`: **every label carried on the G0 circle is quantised**. The statement is named here
(`ChargeQuantisation`); a proof (the GU round, `General/GUCharge.lean`, `circle_char`) discharges it in
`API/Phase.lean`. The core takes it as an `External` hypothesis, so no instance depends on where the proof lives. -/

/-- **G0's phase field**: one compact `U(1)`. -/
abbrev Phase := Circle

/-- **A label on the phase field**: a continuous character of the circle. -/
structure PhaseLabel where
  χ : Circle →* Circle
  continuous : Continuous χ

/-- **Charge quantisation** (the named statement): every continuous character of the circle is `z ↦ z ^ n`, `n` an
integer. -/
def ChargeQuantisation : Prop := ∀ χ : Circle →* Circle, Continuous χ → ∃ n : ℤ, ∀ z, χ z = z ^ n

/-- **What the G0 link gives every instance**: every label carried on the phase field has an integer charge. -/
theorem PhaseLabel.charge (hQ : External "classical: characters of the circle; proved in General/GUCharge.lean (circle_char)"
    ChargeQuantisation) (L : PhaseLabel) : ∃ n : ℤ, ∀ z, L.χ z = z ^ n :=
  hQ L.χ L.continuous

end ProofPhase.API
