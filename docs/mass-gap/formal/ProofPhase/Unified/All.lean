/-
The transport theorem: the three bridges side by side (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/TRANSPORT.md`, section 3; `docs/paper/draft/06-part-VI-common-step.md`, VI.7.
-/

import ProofPhase.Unified.Unified
import ProofPhase.Unified.TransportBridges

/-!
# Three bridges, one transport theorem, three named running-state hypotheses

`three_bridges` plays for the transport theorem the role `three_instances` (`Unified.lean`) plays for the ledger. Each
column is stated as "named running-state hypothesis ⟹ the uncertainty is transported below the margin, and the sign
holds":

| | named hypothesis (running state; open for the specific object) | conclusion (Lean) |
|---|---|---|
| Yang-Mills | `SeamTransport`: the slab chain carries the boundary uncertainty with factor `θ < 1` and seam cost `σ`, with `μ (θ^n u₀ + σ/(1 − θ)) ≤ 1` | the boundary uncertainty after `n` joins is at most `θ^n u₀ + σ/(1 − θ)`, and O1 holds in sector form at `μ` |
| GRH | the summed explicit-formula remainders stay below `log 2` (zero slack: the transport has factor exactly `1`) | `log (1 + relUnc)` is at most the start plus the summed remainders; `relUnc < 1`; zeta's margin is positive, `E n ≥ (1 − relUnc) Ê n` |
| NP vs coNP | `HiddenTransport`: each hidden variable keeps at most `e^{-q}` of the line count; `LiftCPConst` gives it with constant `q = c` | every refutation has at least `e^{W q}` lines |

The general theorem behind all three is `transport` (`Unified/Transport.lean`); with no fresh uncertainty it is `carry`.
For the specific objects (the Wilson measure in the continuum, zeta and the L-functions beyond Dirichlet, strong proof
systems) the hypotheses are the open steps. No axioms beyond the standard ones.
-/

open Finset

noncomputable section

namespace ProofPhase.Unified

open ProofPhase.Proof ProofPhase.Proof.Edge ProofPhase.Proof.Lifting

/-- The Yang-Mills bridge, uncertainty form: under the seam transport the boundary uncertainty after `n` joins is at
most `θ^n u₀ + σ / (1 − θ)`. -/
theorem ym_uncertainty_bound {X : Type*} [Fintype X] {Ω : X → X} {T : ℕ → X → X → ℝ} (hT : ∀ n x y, 0 ≤ T n x y)
    {θ σ u₀ : ℝ} {n : ℕ} (hseam : SeamTransport Ω T (fun _ => θ) (fun _ => σ) n) (h0 : twistCert Ω (T 0) u₀)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hσ : 0 ≤ σ) : twistCert Ω (kchain T n) (θ ^ n * u₀ + σ / (1 - θ)) := by
  have hc := transport_cert hseam (show twistCert Ω (kchain T 0) u₀ from h0)
  have hb : acc (fun _ => θ) (fun _ => σ) u₀ n ≤ θ ^ n * u₀ + σ / (1 - θ) := by
    rw [acc_const]
    have := geom_tail_le hθ0 hθ1 hσ (r := fun _ => σ) (fun _ => le_refl σ) n
    linarith
  exact twistCert_mono (kchain_nonneg hT n) hc hb

/-- **The three bridges side by side**, each as "named running-state hypothesis ⟹ the uncertainty is transported below
the margin and the sign holds". -/
theorem three_bridges :
    -- Yang-Mills: the seam transport carries the boundary uncertainty below the margin `1/μ`; O1 in sector form
    (∀ (X : Type) [Fintype X] (Ω : X → X) (T : ℕ → X → X → ℝ) (θ σ u₀ μ : ℝ) (n : ℕ), (∀ n x y, 0 ≤ T n x y) →
      SeamTransport Ω T (fun _ => θ) (fun _ => σ) n → twistCert Ω (T 0) u₀ → 0 ≤ θ → θ < 1 → 0 ≤ σ → 0 ≤ μ →
      μ * (θ ^ n * u₀ + σ / (1 - θ)) ≤ 1 →
        twistCert Ω (kchain T n) (θ ^ n * u₀ + σ / (1 - θ)) ∧
          ∀ x y, μ * |sec1 Ω (kchain T n) x y| ≤ sec0 Ω (kchain T n) x y) ∧
    -- GRH: at zero slack the summed remainders below `log 2` keep the uncertainty below the margin; the sign holds
    (∀ (E Ê s ŝ : ℕ → ℝ) (n : ℕ), (∀ n, E (n + 1) = s n * E n) → (∀ n, Ê (n + 1) = ŝ n * Ê n) →
      (∀ n, 0 < ŝ n) → 0 < Ê 0 →
      Real.log (1 + relUnc E Ê 0) + ∑ j ∈ range n, Real.log (1 + relRem s ŝ j) < Real.log 2 →
        Real.log (1 + relUnc E Ê n) ≤ Real.log (1 + relUnc E Ê 0) + ∑ j ∈ range n, Real.log (1 + relRem s ŝ j) ∧
          relUnc E Ê n < 1 ∧ 0 < E n ∧ (1 - relUnc E Ê n) * Ê n ≤ E n) ∧
    -- NP vs coNP: the hidden transport is the size bound; the constant quantum gives it with cost `c` per variable
    ((∀ (Line : Type) (Refutes : Finset Line → Prop) (q : ℝ) (W : ℕ), HiddenTransport Refutes q W →
        ∀ P, Refutes P → Real.exp (W * q) ≤ P.card) ∧
      (∀ (G : Gadget) (c : ℝ) (α : Type) [Fintype α] [DecidableEq α] (F : CNF α) (w : ℕ), LiftCPConst G c →
        (∀ D ∈ F, D.Nonempty) → ¬ WD F w ∅ →
          HiddenTransport (CPRefutes (comp G F)) c (w + 1) ∧
            ∀ P, CPRefutes (comp G F) P → Real.exp (((w + 1 : ℕ) : ℝ) * c) ≤ P.card)) := by
  refine ⟨fun X _ Ω T θ σ u₀ μ n hT hseam h0 hθ0 hθ1 hσ hμ0 hm =>
      ⟨ym_uncertainty_bound hT hseam h0 hθ0 hθ1 hσ, ym_bridge hT hseam h0 hθ0 hθ1 hσ hμ0 hm⟩,
    fun E Ê s ŝ n hE hÊ hŝ hÊ0 hsum => ?_, fun Line Refutes q W h P hP => hiddenTransport_iff_size.1 h P hP,
    fun G c α _ _ F w h hF hw => ?_⟩
  · have hL := critical_transport (grh_log_transport hE hÊ hŝ hÊ0 n) fun _ _ => by rw [Real.exp_zero, one_mul]
    obtain ⟨h1, h2, h3⟩ := grh_sign hE hÊ hŝ hÊ0 hsum
    exact ⟨hL, h2, h1, h3⟩
  · have ht := liftCPConst_hiddenTransport h hF hw
    exact ⟨ht, hiddenTransport_iff_size.1 ht⟩

end ProofPhase.Unified
