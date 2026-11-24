/-
The unified lossy-step theorem: the ledger form of a Navier-Stokes blowup (2026-11-24).
Released under Apache 2.0.

Note: `docs/unified/NAVIER-STOKES.md`. Builds on `Blowup.lean` (the rescaled-frame ledger of Chen-Hou) and
`Transport.lean` (transport of an uncertainty). Nothing about the Navier-Stokes equations themselves is proved here.
-/

import ProofPhase.Unified.Blowup
import ProofPhase.Unified.Transport

/-!
# The ledger form of a Navier-Stokes blowup: the window, two routes, and the sufficient conditions

A profile that shrinks like `l(t) = (T* - t)^α` is written in rescaled time `s`, with `T* - t = e^{-s}`. In the rescaled
frame the viscous term carries the coefficient `ν (T* - t)^{1 - 2α} = ν e^{-(1 - 2α) s}` (`nsViscous`).

**1. The window.**
* `nsViscous_half`, `nsViscous_le`, `nsViscous_tendsto_atTop`, `nsViscous_bounded_iff`: the viscous floor is constant at
  the Leray scaling `α = 1/2`, shrinks for `α < 1/2`, and grows without bound for `α > 1/2`; it stays bounded exactly when
  `α ≤ 1/2`.
* `ns_energy_window`: the local energy `(T* - t)^{5α - 2}` stays bounded exactly when `α ≥ 2/5`.
* `ns_typeI_iff`: the velocity scale `(T* - t)^{α - 1}` obeys the Type I bound `(T* - t)^{-1/2}` exactly when `α ≥ 1/2`.
* `ns_window`: bounded viscous floor and bounded local energy together hold exactly for `2/5 ≤ α ≤ 1/2`.
* `ns_no_uniform_certificate`: above the window no one-scale certificate covers every step.

**2. Route II (Type II, `2/5 ≤ α < 1/2`): an inviscid profile, viscosity as a shrinking residual.**
* `EulerProfileCertificate`: the named hypothesis (the certificate of `Blowup.lean` with the residual raised by `ν`).
* `ns_blowup_of_euler_profile`: it forces a trapped perturbation, a finite blowup time and an unbounded amplitude.
* `ns_viscous_transport_bounded`: below the Leray scaling the viscous residual is summable, so even transported without
  damping (cost = floor) its total is bounded. `ns_viscous_transport_unbounded_at_leray`: at `α = 1/2` it is not.

**3. Route I (Type I, `α = 1/2`): a discretely self-similar viscous profile.**
* `LerayDSSCertificate`: the named hypothesis. A profile periodic in rescaled time and **not steady** (an exactly
  self-similar profile is steady, and Necas-Ruzicka-Sverak and Tsai exclude it), a lower bound on its size, and a
  contraction `ρ < 1` per period of the perturbation on the stable complement.
* `ns_free_flow_pays`, `ns_dss_costAboveFloor`: the period map's ledger: the free flow pays `S/4` per period, floor 0.
* `ns_dss_converge`, `ns_period_hasSum`, `ns_dss_amplitude`, `ns_blowup_of_dss`: the perturbation decays geometrically,
  infinitely many periods fit in the finite time 1, and the amplitude `e^{s/4}` (the `Ḣ^1` rate `(T* - t)^{-1/4}`) is
  unbounded.

**4. The energy identity cannot price a step** (`ns_energy_budget_not_costAboveFloor`,
`ns_energy_identity_not_costAboveFloor`): a summable budget never carries a uniform positive cost per step. This is the
ledger content of Tao's averaged Navier-Stokes.

What is **not** here: the PDE. The step inequalities are hypotheses; that a profile exists, and that the linearisation
about it has the stated contraction, are the external inputs. No axioms beyond the standard ones; no unproved steps.
-/

open Finset Filter Topology

noncomputable section

namespace ProofPhase.Unified

/-! ### 1. The window between the energy scaling and the viscous scaling -/

/-- The viscous coefficient in the rescaled frame at rescaled time `s` (`T* - t = e^{-s}`), for a profile of length
scale `(T* - t)^α`: `ν (T* - t)^{1 - 2α} = ν e^{-(1 - 2α) s}`. -/
def nsViscous (ν α s : ℝ) : ℝ := ν * Real.exp (-((1 - 2 * α) * s))

theorem nsViscous_nonneg {ν : ℝ} (hν : 0 ≤ ν) (α s : ℝ) : 0 ≤ nsViscous ν α s :=
  mul_nonneg hν (Real.exp_pos _).le

/-- **At the Leray scaling the viscous floor is constant.** -/
theorem nsViscous_half (ν s : ℝ) : nsViscous ν (1 / 2) s = ν := by
  unfold nsViscous
  norm_num

/-- **Below the Leray scaling the viscous floor only shrinks.** -/
theorem nsViscous_le {ν α s : ℝ} (hν : 0 ≤ ν) (hα : α ≤ 1 / 2) (hs : 0 ≤ s) : nsViscous ν α s ≤ ν := by
  have h : -((1 - 2 * α) * s) ≤ 0 := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * α) hs]
  calc nsViscous ν α s ≤ ν * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 h) hν
    _ = ν := mul_one ν

/-- **Above the Leray scaling the viscous floor grows without bound** in rescaled time. -/
theorem nsViscous_tendsto_atTop {ν α : ℝ} (hν : 0 < ν) (hα : 1 / 2 < α) :
    Tendsto (nsViscous ν α) atTop atTop := by
  have h1 : Tendsto (fun s : ℝ => (2 * α - 1) * s) atTop atTop := tendsto_id.const_mul_atTop (by linarith)
  have h2 := (Real.tendsto_exp_atTop.comp h1).const_mul_atTop hν
  refine h2.congr fun s => ?_
  show ν * Real.exp ((2 * α - 1) * s) = ν * Real.exp (-((1 - 2 * α) * s))
  ring_nf

/-- **The viscous floor stays bounded exactly when `α ≤ 1/2`.** -/
theorem nsViscous_bounded_iff {ν α : ℝ} (hν : 0 < ν) :
    (∃ B, ∀ s, 0 ≤ s → nsViscous ν α s ≤ B) ↔ α ≤ 1 / 2 := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra h0
    have h := lt_of_not_ge h0
    obtain ⟨s, hs1, hs2⟩ :=
      (((nsViscous_tendsto_atTop hν h).eventually (eventually_gt_atTop B)).and (eventually_ge_atTop 0)).exists
    linarith [hB s hs2]
  · intro h
    exact ⟨ν, fun s hs => nsViscous_le hν.le h hs⟩

/-- **Below the Leray scaling the viscous floor is summable** over steps of rescaled length `S > 0`. -/
theorem nsViscous_summable {α S : ℝ} (ν : ℝ) (hα : α < 1 / 2) (hS : 0 < S) :
    Summable (fun n : ℕ => nsViscous ν α (n * S)) := by
  have hpos : 0 < (1 - 2 * α) * S := mul_pos (by linarith) hS
  have hr : Real.exp (-((1 - 2 * α) * S)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hg := (summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left ν
  refine hg.congr fun n => ?_
  simp only [nsViscous]
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- **The energy end of the window.** The local energy near the singular point scales like `(T* - t)^{5α - 2}`; it
stays bounded as `T* - t → 0` exactly when `α ≥ 2/5`. -/
theorem ns_energy_window (α : ℝ) :
    (∀ τ : ℝ, 0 < τ → τ ≤ 1 → τ ^ (5 * α - 2) ≤ 1) ↔ 2 / 5 ≤ α := by
  constructor
  · intro h
    by_contra hα0
    have hα := lt_of_not_ge hα0
    have h1 := h (1 / 2) (by norm_num) (by norm_num)
    have h2 : 1 < (1 / 2 : ℝ) ^ (5 * α - 2) :=
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg (by norm_num) (by norm_num) (by linarith)
    linarith
  · intro hα τ hτ hτ1
    exact Real.rpow_le_one hτ.le hτ1 (by linarith)

/-- **Type I exactly at the Leray end.** The velocity scale `l/(T* - t) = (T* - t)^{α - 1}` obeys the Type I bound
`(T* - t)^{-1/2}` for all small `T* - t` exactly when `α ≥ 1/2`. With `α ≤ 1/2` from the viscous end, Type I means
`α = 1/2`; every `α < 1/2` is a Type II rate. -/
theorem ns_typeI_iff (α : ℝ) :
    (∀ τ : ℝ, 0 < τ → τ ≤ 1 → τ ^ (α - 1) ≤ τ ^ (-(1 / 2 : ℝ))) ↔ 1 / 2 ≤ α := by
  constructor
  · intro h
    by_contra hα0
    have hα := lt_of_not_ge hα0
    have h1 := h (1 / 2) (by norm_num) (by norm_num)
    have h2 : (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) < (1 / 2 : ℝ) ^ (α - 1) :=
      Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) (by linarith)
    linarith
  · intro hα τ hτ hτ1
    exact Real.rpow_le_rpow_of_exponent_ge hτ hτ1 (by linarith)

/-- **The window.** A bounded viscous floor and a bounded local energy hold together exactly for `2/5 ≤ α ≤ 1/2`: the
supercritical gap between the energy scaling and the viscous scaling, where a profile would have to live. -/
theorem ns_window {ν α : ℝ} (hν : 0 < ν) :
    ((∃ B, ∀ s, 0 ≤ s → nsViscous ν α s ≤ B) ∧ (∀ τ : ℝ, 0 < τ → τ ≤ 1 → τ ^ (5 * α - 2) ≤ 1)) ↔
      2 / 5 ≤ α ∧ α ≤ 1 / 2 := by
  rw [nsViscous_bounded_iff hν, ns_energy_window]
  exact And.comm

/-- **Above the window no one-scale certificate exists.** For `α > 1/2` the floor `4 C (ε + ν e^{(2α - 1) n S})`
eventually exceeds any damping `(1 - q)^2`: the trapping condition of `trap_of_gap` fails at some step. -/
theorem ns_no_uniform_certificate {ν α q C ε S : ℝ} (hν : 0 < ν) (hα : 1 / 2 < α) (hC : 0 < C) (hε : 0 ≤ ε)
    (hS : 0 < S) : ¬ ∀ n : ℕ, 4 * C * (ε + nsViscous ν α (n * S)) ≤ (1 - q) ^ 2 := by
  intro h
  have ht : Tendsto (fun n : ℕ => nsViscous ν α (n * S)) atTop atTop :=
    (nsViscous_tendsto_atTop hν hα).comp (tendsto_natCast_atTop_atTop.atTop_mul_const hS)
  obtain ⟨n, hn⟩ := (ht.eventually (eventually_gt_atTop ((1 - q) ^ 2 / (4 * C)))).exists
  have h4 : 0 < 4 * C := by linarith
  rw [div_lt_iff₀ h4] at hn
  nlinarith [h n, mul_nonneg h4.le hε]

/-! ### 2. Route II: an inviscid profile below the Leray scaling, viscosity as a shrinking residual -/

/-- **The sufficient condition, route II (named hypothesis).** An approximate profile of the inviscid rescaled
equation, length exponent `α` with `2/5 ≤ α < 1/2`, damping `q`, nonlinear constant `C`, profile residual `ε`,
viscosity `ν`. The certificate is the one of `Blowup.lean` with the residual raised by `ν`: `(1 - q)^2 ≥ 4 C (ε + ν)`,
and the focusing margin `c̄ + K R ≤ -γ < 0` at the trapping radius `R = (1 - q)/(2C)`. -/
structure EulerProfileCertificate where
  q : ℝ
  C : ℝ
  ε : ℝ
  ν : ℝ
  α : ℝ
  K : ℝ
  cbar : ℝ
  γ : ℝ
  q_nonneg : 0 ≤ q
  C_pos : 0 < C
  ε_nonneg : 0 ≤ ε
  ν_nonneg : 0 ≤ ν
  K_nonneg : 0 ≤ K
  energy : 2 / 5 ≤ α
  below_leray : α < 1 / 2
  gap : 4 * C * (ε + ν) ≤ (1 - q) ^ 2
  focus : cbar + K * ((1 - q) / (2 * C)) ≤ -γ
  γ_pos : 0 < γ

/-- **Route II forces blowup.** The perturbation obeys the step bound of `Blowup.lean` with the residual of step `i`
raised by the viscous term at rescaled time `σ i ≥ 0`. Since below the Leray scaling that term is at most `ν`, the
certificate at step 0 covers every step: the perturbation stays trapped, the physical durations sum to a finite `T*`,
and the amplitude is unbounded. -/
theorem ns_blowup_of_euler_profile (P : EulerProfileCertificate) {M a σ : ℕ → ℝ} (hM : ∀ i, 0 ≤ M i)
    (hσ : ∀ i, 0 ≤ σ i) (hstep : ∀ i, M (i + 1) ≤ P.q * M i + P.C * M i ^ 2 + (P.ε + nsViscous P.ν P.α (σ i)))
    (h0 : M 0 ≤ (1 - P.q) / (2 * P.C)) (ha : ∀ i, a i ≤ P.cbar + P.K * M i) :
    (∀ n, M n ≤ (1 - P.q) / (2 * P.C)) ∧ Summable (durations a) ∧
      ∑' n, durations a n ≤ 1 / (1 - Real.exp (-P.γ)) ∧ Tendsto (fun n => (durations a n)⁻¹) atTop atTop := by
  have hstep' : ∀ i, M (i + 1) ≤ P.q * M i + P.C * M i ^ 2 + (P.ε + P.ν) := fun i => by
    have := nsViscous_le P.ν_nonneg P.below_leray.le (hσ i)
    linarith [hstep i]
  exact blowup_of_certificate P.q_nonneg P.C_pos P.K_nonneg hM hstep' P.gap h0 ha P.focus P.γ_pos

/-- **Route II's certificate in the ledger's language**: cost above floor for the single step type, with the damping
`1 - q` as the cost and `2 √(C (ε + ν))` as the floor, gives the trapping condition. -/
theorem ns_euler_gap_of_costAboveFloor {q C ε ν : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) (hν : 0 ≤ ν)
    (h : CostAboveFloor (fun _ : Unit => 1 - q) (2 * √(C * (ε + ν)))) : 4 * C * (ε + ν) ≤ (1 - q) ^ 2 :=
  gap_of_costAboveFloor hC (add_nonneg hε hν) h

/-- **Below the Leray scaling viscosity is a summable fresh uncertainty**: transported even at cost = floor (no
damping at all, `critAcc`), its accumulated total stays bounded (`critical_bounded_iff`). -/
theorem ns_viscous_transport_bounded {ν α S : ℝ} (hν : 0 ≤ ν) (hα : α < 1 / 2) (hS : 0 < S) (e₀ : ℝ) :
    ∃ B, ∀ n, critAcc e₀ (fun i : ℕ => nsViscous ν α (i * S)) n ≤ B :=
  (critical_bounded_iff fun _ => nsViscous_nonneg hν α _).2 (nsViscous_summable ν hα hS)

/-- **At the Leray scaling it is not**: the viscous term is a constant fresh uncertainty, and at cost = floor it
accumulates without bound (`critical_unbounded`). So at `α = 1/2` viscosity cannot be treated as a perturbation of an
inviscid profile; it has to be part of the profile equation (route I). -/
theorem ns_viscous_transport_unbounded_at_leray {ν S : ℝ} (hν : 0 < ν) (e₀ B : ℝ) :
    ∃ n, B < critAcc e₀ (fun i : ℕ => nsViscous ν (1 / 2) (i * S)) n := by
  have h : (fun i : ℕ => nsViscous ν (1 / 2) (i * S)) = fun _ => ν := funext fun _ => nsViscous_half ν _
  rw [h]
  exact critical_unbounded hν B

/-! ### 3. Route I: a discretely self-similar viscous profile at the Leray scaling -/

/-- **The sufficient condition, route I (named hypothesis).** At the Leray scaling `α = 1/2` the rescaled
Navier-Stokes equation, viscosity included, is autonomous in rescaled time `s = log(T/(T - t))`.
* `W : ℝ → X` is the profile, periodic with period `S > 0` (discrete self-similarity; a rotation can be absorbed into
  `X`), and **not steady**. A steady profile is an exactly self-similar (Leray) solution, which Necas-Ruzicka-Sverak and
  Tsai exclude; a periodic, non-steady profile is the case they leave open.
* `A > 0` is a lower bound on the profile's rescaled `Ḣ^1` size at every time.
* `ρ < 1`, `C ≥ 0`: over one period the perturbation from the profile, after finitely many directions are removed by
  the choice of the datum (finite codimension), contracts by `ρ` up to a quadratic term with constant `C`. -/
structure LerayDSSCertificate (X : Type*) where
  S : ℝ
  S_pos : 0 < S
  W : ℝ → X
  periodic : ∀ s, W (s + S) = W s
  nonsteady : ∃ s, W s ≠ W 0
  A : ℝ
  A_pos : 0 < A
  ρ : ℝ
  C : ℝ
  ρ_nonneg : 0 ≤ ρ
  ρ_lt_one : ρ < 1
  C_nonneg : 0 ≤ C

variable {X : Type*}

/-- **The certificate avoids exact self-similarity**: its profile is not steady. -/
theorem LerayDSSCertificate.not_steady (c : LerayDSSCertificate X) : ¬ ∀ s, c.W s = c.W 0 := fun h =>
  let ⟨s, hs⟩ := c.nonsteady
  hs (h s)

/-- **The free flow pays `S/4` per period, floor 0.** In rescaled variables the heat flow followed by the rescaling
contracts `Ḣ^1` by `e^{-s/4}` (`Ḣ^1` is subcritical by `1/4`); along the periods this is a decay ledger. -/
theorem ns_free_flow_pays (S : ℝ) (n : ℕ) :
    Pays (fun k : ℕ => Real.exp (-(k * (S / 4)))) (fun _ => S / 4) 0 n := fun i _ => by
  rw [← Real.exp_add]
  apply le_of_eq
  push_cast
  ring_nf

/-- **Route I's contraction as cost above floor**: a period factor `0 < ρ < 1` is a positive cost `-log ρ` over the
floor 0, for the single step type of the autonomous rescaled equation. -/
theorem ns_dss_costAboveFloor (c : LerayDSSCertificate X) (hρ : 0 < c.ρ) :
    CostAboveFloor (fun _ : Unit => -Real.log c.ρ) 0 :=
  ⟨-Real.log c.ρ, neg_pos.2 (Real.log_neg hρ c.ρ_lt_one), fun _ => le_rfl⟩

/-- **The perturbation decays geometrically over the periods.** With `M (n+1) ≤ ρ M n + C (M n)^2` (an exact profile:
no residual) and a start `M 0 ≤ δ` with `ρ + C δ < 1`: `M n ≤ (ρ + C δ)^n δ`. The solution converges to the profile. -/
theorem ns_dss_converge (c : LerayDSSCertificate X) {M : ℕ → ℝ} {δ : ℝ} (hM : ∀ n, 0 ≤ M n)
    (hstep : ∀ n, M (n + 1) ≤ c.ρ * M n + c.C * M n ^ 2) (h0 : M 0 ≤ δ) (hδ : c.ρ + c.C * δ < 1) :
    ∀ n, M n ≤ (c.ρ + c.C * δ) ^ n * δ := by
  have hδ0 : 0 ≤ δ := (hM 0).trans h0
  have hθ0 : 0 ≤ c.ρ + c.C * δ := add_nonneg c.ρ_nonneg (mul_nonneg c.C_nonneg hδ0)
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hle : M n ≤ δ := ih.trans (mul_le_of_le_one_left hδ0 (pow_le_one₀ hθ0 hδ.le))
    have hsq : M n ^ 2 ≤ δ * M n := by rw [sq]; exact mul_le_mul_of_nonneg_right hle (hM n)
    have h1 : c.C * M n ^ 2 ≤ c.C * δ * M n := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsq c.C_nonneg
    calc M (n + 1) ≤ c.ρ * M n + c.C * M n ^ 2 := hstep n
      _ ≤ (c.ρ + c.C * δ) * M n := by linarith
      _ ≤ (c.ρ + c.C * δ) * ((c.ρ + c.C * δ) ^ n * δ) := mul_le_mul_of_nonneg_left ih hθ0
      _ = (c.ρ + c.C * δ) ^ (n + 1) * δ := by ring

/-- The physical length of period `n` for blowup time 1: the remaining time drops from `e^{-nS}` to `e^{-(n+1)S}`. -/
def nsPeriodLength (S : ℝ) (n : ℕ) : ℝ := Real.exp (-(n * S)) * (1 - Real.exp (-S))

/-- **Infinitely many periods fit in the finite time 1.** -/
theorem ns_period_hasSum {S : ℝ} (hS : 0 < S) : HasSum (nsPeriodLength S) 1 := by
  have hr0 : 0 ≤ Real.exp (-S) := (Real.exp_pos _).le
  have hr1 : Real.exp (-S) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_right (1 - Real.exp (-S))
  rw [inv_mul_cancel₀ (by linarith : (1 - Real.exp (-S)) ≠ 0)] at h
  have hf : nsPeriodLength S = fun n : ℕ => Real.exp (-S) ^ n * (1 - Real.exp (-S)) := by
    funext n
    simp only [nsPeriodLength]
    rw [← Real.exp_nat_mul]
    congr 2
    ring
  rw [hf]
  exact h

/-- **The amplitude is unbounded.** At the start of period `n` the field's `Ḣ^1` norm is `e^{nS/4}` times its rescaled
norm, which is at least `A - M n` (the profile's size minus the perturbation). This tends to infinity: the rate
`(T - t)^{-1/4}` in `Ḣ^1`, Leray's lower bound for a singular solution. -/
theorem ns_dss_amplitude (c : LerayDSSCertificate X) {M : ℕ → ℝ} {δ : ℝ} (hM : ∀ n, 0 ≤ M n)
    (hstep : ∀ n, M (n + 1) ≤ c.ρ * M n + c.C * M n ^ 2) (h0 : M 0 ≤ δ) (hδ : c.ρ + c.C * δ < 1) :
    Tendsto (fun n : ℕ => Real.exp (n * c.S / 4) * (c.A - M n)) atTop atTop := by
  have hδ0 : 0 ≤ δ := (hM 0).trans h0
  have hθ0 : 0 ≤ c.ρ + c.C * δ := add_nonneg c.ρ_nonneg (mul_nonneg c.C_nonneg hδ0)
  have hconv := ns_dss_converge c hM hstep h0 hδ
  have hz : Tendsto (fun n : ℕ => (c.ρ + c.C * δ) ^ n * δ) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hδ).mul_const δ
  have hA2 : (0 : ℝ) < c.A / 2 := by linarith [c.A_pos]
  have hev : ∀ᶠ n : ℕ in atTop, (c.ρ + c.C * δ) ^ n * δ < c.A / 2 := hz.eventually (gt_mem_nhds hA2)
  have hlin : Tendsto (fun n : ℕ => (n : ℝ) * c.S / 4) atTop atTop := by
    have := tendsto_natCast_atTop_atTop.atTop_mul_const (show (0 : ℝ) < c.S / 4 by linarith [c.S_pos])
    exact this.congr fun n => by ring
  have hexp : Tendsto (fun n : ℕ => Real.exp (n * c.S / 4) * (c.A / 2)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp hlin).atTop_mul_const hA2
  refine tendsto_atTop_mono' atTop ?_ hexp
  filter_upwards [hev] with n hn
  have := hconv n
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

/-- **Route I forces blowup.** The certificate gives: the perturbation decays geometrically over the periods (the
solution converges to the profile), the periods fill the finite time 1 (`T* = 1`), the `Ḣ^1` amplitude tends to
infinity, and the profile is not steady (no exact self-similarity is used). -/
theorem ns_blowup_of_dss (c : LerayDSSCertificate X) {M : ℕ → ℝ} {δ : ℝ} (hM : ∀ n, 0 ≤ M n)
    (hstep : ∀ n, M (n + 1) ≤ c.ρ * M n + c.C * M n ^ 2) (h0 : M 0 ≤ δ) (hδ : c.ρ + c.C * δ < 1) :
    (∀ n, M n ≤ (c.ρ + c.C * δ) ^ n * δ) ∧ HasSum (nsPeriodLength c.S) 1 ∧
      Tendsto (fun n : ℕ => Real.exp (n * c.S / 4) * (c.A - M n)) atTop atTop ∧ ¬ (∀ s, c.W s = c.W 0) :=
  ⟨ns_dss_converge c hM hstep h0 hδ, ns_period_hasSum c.S_pos, ns_dss_amplitude c hM hstep h0 hδ, c.not_steady⟩

/-! ### 4. The energy identity cannot price a single step -/

/-- **A summable budget carries no uniform positive cost.** If the per-step costs are summable, no `κ > 0` bounds
every one of them from below. -/
theorem ns_energy_budget_not_costAboveFloor {c : ℕ → ℝ} (hc : Summable c) : ¬ CostAboveFloor c 0 := by
  rintro ⟨κ, hκ, hle⟩
  obtain ⟨n, hn⟩ := (hc.tendsto_atTop_zero.eventually (gt_mem_nhds hκ)).exists
  linarith [hle n]

/-- **The energy identity in ledger form.** Nonnegative dissipated shares per step whose partial sums stay below the
initial energy `E₀` (the energy identity: a global sum) never pay a uniform positive cost per step. This is the ledger
content of Tao's averaged Navier-Stokes, which keeps this identity and blows up. -/
theorem ns_energy_identity_not_costAboveFloor {d : ℕ → ℝ} {E₀ : ℝ} (hd : ∀ n, 0 ≤ d n)
    (hE : ∀ N, ∑ n ∈ range N, d n ≤ E₀) : ¬ CostAboveFloor d 0 :=
  ns_energy_budget_not_costAboveFloor (summable_of_sum_range_le hd hE)

end ProofPhase.Unified
