/-
The form layer as one API: the Navier-Stokes instance, in the API's shape (2026-11-24).
Released under Apache 2.0.

Paper: `docs/unified/NAVIER-STOKES.md` (sections 5 and 6), `docs/unified/API.md`. Ledger skeleton:
`Unified/NavierStokes.lean`.
-/

import ProofPhase.API
import ProofPhase.Unified.NavierStokes

/-!
# Navier-Stokes through the API: input + structure + one named open step

The owner's direction (2026-11-24): fill in the template and let the API answer. Four answers come out, each from an API
theorem; every content step sits in an `OpenStep` or `External` slot.

* **Which window** (`windowQ`, runs): a rational length exponent `α` is sorted into the four windows by a computation, and
  `windowQ_correct` proves the computed answer right against the real statements (`ns_window`, `ns_typeI_iff`).
* **Blowup, route I** (Leray scaling, discretely self-similar): the perturbation over the periods is a running system
  (`system`, `RunSys 0`) in the contraction class (`contracting`), so the API's `settle` answers "it settles onto the
  profile", with a computed period count (`settles_by`); settling in the zoomed frame is blowup in physical time
  (`routeI`, the card). Open step: `PeriodContraction`, the certificate's content.
* **Blowup, route II** (inside the window, Type II): the perturbation is an `Uncertainty` whose fresh uncertainty is the
  viscous residual (`eulerUncertainty`); the API's `bounded` keeps it below an explicit bound (`routeII_bounded`).
* **Regularity** (the reverse ledger over dyadic scales): a `Chain` whose open step is a uniform dissipation cost above the
  transfer floor (`regularity`, the card). The API also says why the energy ledger cannot fill that slot:
  `energy_cannot_fill` (a summable budget pays no uniform cost) and `dyadic_supercritical` (the a priori transfer bound
  outgrows the dissipation by `2^{k/2}` per scale).
* **The external tie** (`ABInterface`, `abProblem`): Alpoge and Buckmaster's claimed theorems as `External` slots, their
  unreleased certificate as the card's one open step; then `¬ (A) ∧ ¬ (B)` of Fefferman's statement follows by the card.

Nothing about the Navier-Stokes equations is proved here. Standard axioms only.
-/

noncomputable section

namespace ProofPhase.API.NavierStokes

open ProofPhase.Unified Filter Topology

/-! ## 1. Which window: a decision that runs -/

/-- The four windows for a profile of length scale `(T* - t)^α`. -/
inductive Window
  /-- `α > 1/2`: the viscous floor grows without bound; no certificate covers all steps. -/
  | aboveViscous
  /-- `α = 1/2`: the Leray scaling, Type I; route I (discretely self-similar, viscosity inside the profile). -/
  | leray
  /-- `2/5 ≤ α < 1/2`: Type II; route II (inviscid profile, viscosity a shrinking residual). -/
  | typeII
  /-- `α < 2/5`: infinite local energy. -/
  | belowEnergy
  deriving DecidableEq, Repr

/-- **The window decision**, computed on a rational exponent. -/
def windowQ (α : ℚ) : Window :=
  if 1 / 2 < α then .aboveViscous else if α = 1 / 2 then .leray else if 2 / 5 ≤ α then .typeII else .belowEnergy

/- The decision runs: Leray's exponent, a Type II exponent, and the two excluded sides (`#eval`, `#guard` evaluate
when the file is checked). -/
#eval windowQ (1 / 2)
#guard windowQ (9 / 20) = .typeII
#guard windowQ (3 / 5) = .aboveViscous
#guard windowQ (1 / 3) = .belowEnergy

/-- The real statement the decision answers: a bounded viscous floor and a bounded local energy (`ns_window`). -/
def Admissible (ν α : ℝ) : Prop :=
  (∃ B, ∀ s, 0 ≤ s → nsViscous ν α s ≤ B) ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 → τ ^ (5 * α - 2) ≤ 1

/-- The Type I bound for the velocity scale (`ns_typeI_iff`). -/
def TypeI (α : ℝ) : Prop := ∀ τ : ℝ, 0 < τ → τ ≤ 1 → τ ^ (α - 1) ≤ τ ^ (-(1 / 2 : ℝ))

theorem windowQ_admissible_iff (α : ℚ) :
    (windowQ α = .leray ∨ windowQ α = .typeII) ↔ 2 / 5 ≤ α ∧ α ≤ 1 / 2 := by
  unfold windowQ
  split_ifs with h1 h2 h3
  · simp only [or_self, false_iff, not_and, not_le]; intro; exact h1
  · simp only [true_or, true_iff]; constructor <;> linarith [h2.le, h2.ge]
  · simp only [or_true, true_iff]; exact ⟨h3, le_of_not_gt h1⟩
  · simp only [or_self, false_iff, not_and, not_le]; intro h; exact absurd h h3

theorem windowQ_leray_iff (α : ℚ) : windowQ α = .leray ↔ α = 1 / 2 := by
  unfold windowQ
  split_ifs with h1 h2 h3
  · simp only [false_iff]; intro h; rw [h] at h1; norm_num at h1
  · simp only [true_iff]; exact h2
  · simp only [false_iff]; exact h2
  · simp only [false_iff]; exact h2

/-- Leray's exponent is the Leray window (kernel-checked through `windowQ_leray_iff`). -/
theorem windowQ_half : windowQ (1 / 2) = .leray := (windowQ_leray_iff _).2 rfl

/-- **The computed window is right** for the real system: the decision says "inside the window" exactly when the viscous
floor and the local energy are bounded, and "Leray" exactly when, in addition, the Type I bound holds. -/
theorem windowQ_correct {ν : ℝ} (hν : 0 < ν) (α : ℚ) :
    ((windowQ α = .leray ∨ windowQ α = .typeII) ↔ Admissible ν α) ∧
      (windowQ α = .leray ↔ Admissible ν α ∧ TypeI α) := by
  have hA : Admissible ν α ↔ 2 / 5 ≤ α ∧ α ≤ 1 / 2 := by
    unfold Admissible
    rw [ns_window hν]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Rat.cast_le (K := ℝ)).1 (by push_cast; exact h1), (Rat.cast_le (K := ℝ)).1 (by push_cast; exact h2)⟩
    · rintro ⟨h1, h2⟩
      have e1 := (Rat.cast_le (K := ℝ)).2 h1
      have e2 := (Rat.cast_le (K := ℝ)).2 h2
      push_cast at e1 e2
      exact ⟨e1, e2⟩
  have hT : TypeI α ↔ 1 / 2 ≤ α := by
    unfold TypeI
    rw [ns_typeI_iff]
    constructor
    · intro h; exact (Rat.cast_le (K := ℝ)).1 (by push_cast; exact h)
    · intro h; have e := (Rat.cast_le (K := ℝ)).2 h; push_cast at e; exact e
  refine ⟨(windowQ_admissible_iff α).trans hA.symm, ?_⟩
  rw [windowQ_leray_iff, hA, hT]
  constructor
  · intro h; subst h; norm_num
  · rintro ⟨⟨_, h2⟩, h3⟩; exact le_antisymm h2 h3

/-! ## 2. Route I: the perturbation over the periods is a running system -/

/-- **The input of route I.** The states of the perturbation from the profile after the finite-dimensional correction of
the datum, the period map `per`, the perturbation size `size` (the rescaled `Ḣ^1` norm), and the constants of the period
estimate: contraction `ρ`, quadratic constant `C`, and a ball radius `δ` with `ρ + C δ < 1`. -/
structure DSSInput where
  Y : Type
  per : Y → Y
  size : Y → ℝ
  size_nonneg : ∀ y, 0 ≤ size y
  ρ : ℝ
  C : ℝ
  δ : ℝ
  ρ_nonneg : 0 ≤ ρ
  C_nonneg : 0 ≤ C
  ball : ρ + C * δ < 1

/-- **The open step of route I**: over one period the perturbation obeys `size (per y) ≤ ρ size y + C (size y)^2`. This
is the content a certificate supplies (Alpoge-Buckmaster: the monodromy operator on the complement of finitely many
directions, with the quadratic term). -/
def PeriodContraction (i : DSSInput) : Prop :=
  OpenStep "route I: one period contracts the perturbation, size (per y) <= rho size y + C (size y)^2"
    (∀ y, i.size (i.per y) ≤ i.ρ * i.size y + i.C * i.size y ^ 2)

/-- The ball of radius `δ` around the profile. -/
def Ball (i : DSSInput) : Type := {y : i.Y // i.size y ≤ i.δ}

theorem fac_le (i : DSSInput) (y : Ball i) : i.ρ + i.C * i.size y.1 ≤ i.ρ + i.C * i.δ := by
  have := mul_le_mul_of_nonneg_left y.2 i.C_nonneg
  linarith

theorem per_le (i : DSSInput) (h : PeriodContraction i) (y : i.Y) :
    i.size (i.per y) ≤ (i.ρ + i.C * i.size y) * i.size y :=
  le_of_le_of_eq (h y) (by ring)

/-- **The proved structure: route I as a running system** (floor 0). States: the ball; step: the period map (the ball is
invariant); factor: `ρ + C · size`, in `[0, 1]`; mass: the perturbation size. The ledger law is the open step. -/
def system (i : DSSInput) (h : PeriodContraction i) : RunSys 0 where
  X := Ball i
  step y := ⟨i.per y.1, ((per_le i h y.1).trans (mul_le_of_le_one_left (i.size_nonneg _)
    ((fac_le i y).trans i.ball.le))).trans y.2⟩
  fac y := i.ρ + i.C * i.size y.1
  mass y := i.size y.1
  fac_nonneg y := add_nonneg i.ρ_nonneg (mul_nonneg i.C_nonneg (i.size_nonneg _))
  fac_le_one y := (fac_le i y).trans i.ball.le
  mass_nonneg y := i.size_nonneg _
  pays y := by rw [Real.exp_zero, one_mul]; exact per_le i h y.1

/-- **Route I is in the contraction class** with `θ = ρ + C δ`: the API's settle theorems apply. -/
theorem contracting (i : DSSInput) (h : PeriodContraction i) : (system i h).Contracting (i.ρ + i.C * i.δ) :=
  ⟨fun y => fac_le i y, by rw [Real.exp_zero, one_mul]; exact i.ball⟩

/-- The point of `Y` that a state of the running system is. -/
def toY (i : DSSInput) (h : PeriodContraction i) (x : (system i h).X) : i.Y := (show Ball i from x).1

/-- The running system's steps are the period map's iterates. -/
theorem system_iter (i : DSSInput) (h : PeriodContraction i) (x : (system i h).X) (n : ℕ) :
    toY i h ((system i h).step^[n] x) = i.per^[n] (toY i h x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    rfl

/-- **Settling onto the profile, with a computed count** (the API's `settle0`): for a rational `q` with `ρ + C δ ≤ q < 1`
and a rational start bound `M`, from period `balanceBound M ε q` on the perturbation is at most `ε`. -/
theorem settles_by (i : DSSInput) (h : PeriodContraction i) {q : ℚ} (hq : q < 1) (hθ : i.ρ + i.C * i.δ ≤ q)
    (y : Ball i) {M ε : ℚ} (hM : i.size y.1 ≤ M) (hε : 0 < ε) :
    ∀ n ≥ balanceBound M ε q, (system i h).Balanced ε y n :=
  settle0 (system i h) hq (fun y => (fac_le i y).trans hθ) y hM hε

/-- **The input of the route I card**: a certificate (`LerayDSSCertificate`, the profile and its constants), the period
map with the same constants, and a start inside the ball. -/
structure RouteIInput where
  X : Type
  cert : LerayDSSCertificate X
  sys : DSSInput
  ρ_eq : sys.ρ = cert.ρ
  C_eq : sys.C = cert.C
  y₀ : sys.Y
  start : sys.size y₀ ≤ sys.δ

/-- **Route I as a problem card.** Open step: the period contraction. Conclusion: the perturbation settles onto the
profile (within every `ε`, by the API's `settle_everywhere`), infinitely many periods fit in the finite time 1, the
`Ḣ^1` amplitude tends to infinity, and the profile is not steady (no exact self-similarity). -/
def routeI : Problem where
  name := "Navier-Stokes, route I: a discretely self-similar profile with a period contraction gives blowup"
  Input := RouteIInput
  Open i := PeriodContraction i.sys
  Concl i := (∀ ε > 0, ∃ n, i.sys.size (i.sys.per^[n] i.y₀) ≤ ε) ∧ HasSum (nsPeriodLength i.cert.S) 1 ∧
    Tendsto (fun n : ℕ => Real.exp (n * i.cert.S / 4) * (i.cert.A - i.sys.size (i.sys.per^[n] i.y₀))) atTop atTop ∧
    ¬ (∀ s, i.cert.W s = i.cert.W 0)
  sources := ["Alpoge-Buckmaster 2026 (claimed): the period contraction on a finite-codimensional complement"]
  proved i h := by
    have hreach : ∀ ε > 0, ∃ n, i.sys.size (i.sys.per^[n] i.y₀) ≤ ε := fun ε hε => by
      let x : (system i.sys h).X := (⟨i.y₀, i.start⟩ : Ball i.sys)
      obtain ⟨n, hn⟩ := settle_everywhere (system i.sys h) (contracting i.sys h) x hε
      refine ⟨n, ?_⟩
      have e := system_iter i.sys h x n
      calc i.sys.size (i.sys.per^[n] i.y₀) = i.sys.size (toY i.sys h ((system i.sys h).step^[n] x)) := by
            rw [e]; rfl
        _ ≤ ε := hn
    have hstep : ∀ n, i.sys.size (i.sys.per^[n + 1] i.y₀) ≤
        i.cert.ρ * i.sys.size (i.sys.per^[n] i.y₀) + i.cert.C * i.sys.size (i.sys.per^[n] i.y₀) ^ 2 := fun n => by
      rw [Function.iterate_succ_apply', ← i.ρ_eq, ← i.C_eq]
      exact h _
    have hδ : i.cert.ρ + i.cert.C * i.sys.δ < 1 := by rw [← i.ρ_eq, ← i.C_eq]; exact i.sys.ball
    obtain ⟨_, h2, h3, h4⟩ := ns_blowup_of_dss i.cert (M := fun n => i.sys.size (i.sys.per^[n] i.y₀))
      (fun n => i.sys.size_nonneg _) hstep i.start hδ
    exact ⟨hreach, h2, h3, h4⟩

/-! ## 3. Route II: viscosity as the fresh uncertainty -/

/-- **Route II as an uncertainty.** The perturbation `M` is transported with the factor `q + C M i` and the fresh
uncertainty `ε + ν e^{-(1 - 2α) σ i}` (the profile's residual plus the viscous term at rescaled time `σ i`). -/
def eulerUncertainty (P : EulerProfileCertificate) {M σ : ℕ → ℝ} (hM : ∀ i, 0 ≤ M i)
    (hstep : ∀ i, M (i + 1) ≤ P.q * M i + P.C * M i ^ 2 + (P.ε + nsViscous P.ν P.α (σ i))) : Uncertainty 0 where
  e := M
  f i := P.q + P.C * M i
  r i := P.ε + nsViscous P.ν P.α (σ i)
  e0_nonneg := hM 0
  f_nonneg i := add_nonneg P.q_nonneg (mul_nonneg P.C_pos.le (hM i))
  r_nonneg i := add_nonneg P.ε_nonneg (nsViscous_nonneg P.ν_nonneg _ _)
  step i := by rw [Real.exp_zero, one_mul]; exact le_of_le_of_eq (hstep i) (by ring)

/-- **The API bounds route II's perturbation.** Once trapped (`trap_of_gap`), the factors are at most
`q + C R = (1 + q)/2 < 1` and the fresh uncertainty at most `ε + ν`, so the API's bounded transport gives
`M n ≤ M 0 + 2 (ε + ν)/(1 - q)` at every step. -/
theorem routeII_bounded (P : EulerProfileCertificate) (hq1 : P.q < 1) {M σ : ℕ → ℝ} (hM : ∀ i, 0 ≤ M i)
    (hσ : ∀ i, 0 ≤ σ i) (hstep : ∀ i, M (i + 1) ≤ P.q * M i + P.C * M i ^ 2 + (P.ε + nsViscous P.ν P.α (σ i)))
    (h0 : M 0 ≤ (1 - P.q) / (2 * P.C)) (n : ℕ) : M n ≤ M 0 + 2 * (P.ε + P.ν) / (1 - P.q) := by
  have hstep' : ∀ i, M (i + 1) ≤ P.q * M i + P.C * M i ^ 2 + (P.ε + P.ν) := fun i => by
    have := nsViscous_le P.ν_nonneg P.below_leray.le (hσ i)
    linarith [hstep i]
  have htrap := trap_of_gap P.q_nonneg P.C_pos hM hstep' P.gap h0
  have hC : P.C ≠ 0 := P.C_pos.ne'
  have hθ : P.q + P.C * ((1 - P.q) / (2 * P.C)) = (1 + P.q) / 2 := by field_simp; ring
  have hfθ : ∀ i, (eulerUncertainty P hM hstep).f i ≤ (1 + P.q) / 2 := fun i => by
    show P.q + P.C * M i ≤ (1 + P.q) / 2
    rw [← hθ]
    linarith [mul_le_mul_of_nonneg_left (htrap i) P.C_pos.le]
  have hq : Real.exp 0 * ((1 + P.q) / 2) < 1 := by rw [Real.exp_zero, one_mul]; linarith
  have hR : ∀ i, (eulerUncertainty P hM hstep).r i ≤ P.ε + P.ν := fun i => by
    show P.ε + nsViscous P.ν P.α (σ i) ≤ P.ε + P.ν
    linarith [nsViscous_le P.ν_nonneg P.below_leray.le (hσ i)]
  have := (eulerUncertainty P hM hstep).bounded hfθ hq hR n
  have he : (1 - Real.exp 0 * ((1 + P.q) / 2)) = (1 - P.q) / 2 := by rw [Real.exp_zero]; ring
  rw [he] at this
  have hpos : 0 < 1 - P.q := by linarith
  calc M n ≤ M 0 + (P.ε + P.ν) / ((1 - P.q) / 2) := this
    _ = M 0 + 2 * (P.ε + P.ν) / (1 - P.q) := by field_simp

/-! ## 4. Regularity: the reverse ledger over dyadic scales -/

/-- **The input of the regularity card**: a chain over dyadic scales `k` (the energy or flux carried to scale `2^{-k}`),
its costs (the share dissipated per scale) and its floor `δ` (the share the transfer adds back per scale). -/
structure DyadicInput where
  δ : ℝ
  ch : Chain δ

/-- **Regularity as a problem card.** Open step: a uniform dissipation cost per dyadic scale strictly above the transfer
floor. Conclusion: the carried quantity decays at a positive rate and is summable over all scales (the cascade dies out
at small scales; the reading "regular" is section 5 of the note). -/
def regularity : Problem where
  name := "Navier-Stokes, regularity: a uniform cost per dyadic scale above the transfer floor stops the cascade"
  Input := DyadicInput
  Open i := OpenStep "regularity: every dyadic scale dissipates a uniform cost above the transfer floor"
    (CostAboveFloor i.ch.c i.δ)
  Concl i := ∃ κ, i.δ < κ ∧ (∀ n, i.ch.M n ≤ Real.exp (-(n * (κ - i.δ))) * i.ch.M 0) ∧ Summable i.ch.M
  proved i h := by
    obtain ⟨κ, hκ, hc⟩ := h
    exact ⟨κ, hκ, fun n => i.ch.decay hc n, i.ch.summable hc hκ⟩

/-- **The energy identity cannot fill the regularity slot** (floor 0): dissipated shares whose partial sums stay below
the start energy never pay a uniform positive cost (`ns_energy_identity_not_costAboveFloor`). Tao's averaged equations
keep exactly this and blow up. -/
theorem energy_cannot_fill {d : ℕ → ℝ} {E₀ : ℝ} (hd : ∀ n, 0 ≤ d n) (hE : ∀ N, ∑ n ∈ Finset.range N, d n ≤ E₀) :
    ¬ CostAboveFloor d 0 :=
  ns_energy_identity_not_costAboveFloor hd hE

/-- **Supercriticality, per dyadic scale.** At scale `2^{-k}` the viscous cost grows like `ν 4^k`, while the transfer
bound that the energy alone gives grows like `K 2^{5k/2} = K (√2)^{5k}` (Bernstein's inequality; `K` carries the energy).
Whatever `ν` and `K > 0`, the transfer bound overtakes the cost at some scale: the energy ledger has no cost above its
floor at small scales. (In two dimensions the same count gives `K 4^k`, the critical case.) -/
theorem dyadic_supercritical (ν : ℝ) {K : ℝ} (hK : 0 < K) : ∃ k : ℕ, ν * 4 ^ k < K * (√2) ^ (5 * k) := by
  have h1 : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually (eventually_gt_atTop (ν / K))).exists
  refine ⟨k, ?_⟩
  have h4 : (√2 : ℝ) ^ 4 = 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsplit : (√2 : ℝ) ^ (5 * k) = 4 ^ k * (√2) ^ k := by
    rw [show 5 * k = 4 * k + k by ring, pow_add, pow_mul, h4]
  rw [hsplit, div_lt_iff₀ hK] at *
  have h4k : (0 : ℝ) < 4 ^ k := by positivity
  nlinarith [mul_lt_mul_of_pos_left hk h4k]

/-! ## 5. The external tie: Alpoge-Buckmaster's claim in the API's slots -/

/-- **The statement-level interface of the Alpoge-Buckmaster claim** (2026-11-20; claimed, not refereed). The four
statements are named, not defined here: this library has no Navier-Stokes object, and audit item 1 replaces them by a
pinned formalisation (Formal Conjectures' statement of Fefferman's (A) and (B), or their own statement files). The three
theorems are `External` fields, never axioms. -/
structure ABInterface where
  /-- A certificate in the sense of their Section 7.3 and Appendix B exists (finitely many fields and numbers). -/
  Certificate : Prop
  /-- A profile with period `S` and isometry `R` in the sense of their (1.2), (1.3) exists. -/
  Profile : Prop
  /-- Fefferman's (A): global smooth solutions of bounded energy on `R^3` for every smooth rapidly decaying datum, no force. -/
  ClayA : Prop
  /-- Fefferman's (B): global smooth periodic solutions on the torus, no force. -/
  ClayB : Prop
  /-- Their Theorem 7.1 (claimed): a certificate gives a profile. -/
  thm71 : External "Alpoge-Buckmaster 2026, Theorem 7.1 (claimed; formal version gives a weak profile)"
    (Certificate → Profile)
  /-- Their Theorem 1.1 (claimed): a profile gives unforced blowup on `R^3` and on `T^3`, disproving (A) and (B). -/
  thm11 : External "Alpoge-Buckmaster 2026, Theorem 1.1 (claimed; formal version without rate)"
    (Profile → ¬ ClayA ∧ ¬ ClayB)
  /-- Their formalisation (claimed): the conditions of Appendix B give the formal Theorem 1.1 directly. -/
  formal : External "Alpoge-Buckmaster 2026, Lean library (comparator files, three standard axioms; patched 2026-11-20,
    not rebuilt)" (Certificate → ¬ ClayA ∧ ¬ ClayB)

/-- **The external tie as a problem card.** Input: the interface. Open step: the certificate, which is the content step
and was unreleased on 2026-11-24 (only its SHA-256 hash is published). Conclusion: Fefferman's (A) and (B) both fail, so
(C) and (D) hold with zero force. The proof is the interface's formal theorem; the paper's route (`thm71`, `thm11`) gives
the same conclusion (`ab_paper_route`). -/
def abProblem : Problem where
  name := "Navier-Stokes, external tie: the Alpoge-Buckmaster certificate disproves Fefferman's (A) and (B)"
  Input := ABInterface
  Open I := OpenStep "the Alpoge-Buckmaster certificate (SHA-256 3f7a335b...4b22c5) satisfies Appendix B; unreleased"
    I.Certificate
  Concl I := ¬ I.ClayA ∧ ¬ I.ClayB
  sources := ["Alpoge-Buckmaster 2026, Theorems 1.1 and 7.1 (claimed)", "Alpoge-Buckmaster 2026, Lean library (claimed)"]
  proved I h := I.formal h

/-- **The paper's route gives the same conclusion**: certificate, then profile (Theorem 7.1), then blowup (Theorem 1.1). -/
theorem ab_paper_route (I : ABInterface) (h : I.Certificate) : ¬ I.ClayA ∧ ¬ I.ClayB := I.thm11 (I.thm71 h)

end ProofPhase.API.NavierStokes
