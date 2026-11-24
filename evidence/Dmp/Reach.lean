/-!
# The mass gap from Axiom 1's reach (finding MG7)

The owner, 2026-11-21, reading Axiom 1 ("A part acts in CMOS only while the two halves of its layer, two independent witnesses, each with
full reach over the act and gated only by the other, trust it for that act. [...] This holds at every layer."): "Since everything inside
CMOS can only perform correct acts, it has to be assumed that it must be able to communicate them at the internal rates."

The chain, in DMP's terms: an IM act inside CMOS needs two witnesses with full reach over it, so its extent is bounded by that reach, the
same at every layer; an act asserts its existence over its extent (the owner's rule: existence times the length it asserts itself over is
one quantum, `h/c`, read with `ħ`); so a bounded extent forces a minimum existence. Payload is not an act inside CMOS, Axiom 1 does not
bound it, and its existence has no floor (light is massless: the photon test).

The model, in whole numbers. A grid of resolution `k` (ticks per unit of length; finer grids have larger `k`). An act's extent is `e`
ticks (`e / k` units of length) and its existence is `x` in units of `1 / k` (`x / k`). The owner's rule, existence times extent is one
quantum `Q`: `(x / k) · (e / k) = Q`, so `x · e = Q · k · k`. Axiom 1's reach, at most `R` units of length: `e ≤ R · k`.

What this file proves, about this model only:

1. **The floor**: existence is at least `Q / R` (`Q · k ≤ x · R`), on every grid. Unlike the potential's gap of `MassGap.lean` (which
   closes as the clock is refined, `mg_refinement_closes_potential_gap`), this floor does not mention the resolution `k`: it survives
   every refinement.
2. **Every layer**: the same floor for every layer, when the reach is the same at every layer ("This holds at every layer").
3. **Never zero**: with a positive quantum, existence is positive.
4. **No reach, no floor**: without Axiom 1's bound, every proposed floor `Q / R` is undercut by some act on some grid. That is the
   payload's case.

What it does not prove: anything about Yang–Mills theory. In physics words the reach bound for IM is confinement (`docs/mass-gap/README.md`
§3.1b); whether Yang–Mills obeys it at every scale is the open problem.
-/

namespace Dmp

/-- **The floor.** An act whose existence times extent is one quantum and whose extent lies within the witnesses' reach has existence at
    least `Q / R`, whatever the resolution of the grid. -/
theorem mg_reach_existence_floor (Q R k x e : Nat) (hk : 0 < k) (hact : x * e = Q * k * k) (hreach : e ≤ R * k) :
    Q * k ≤ x * R := by
  have h1 : x * e ≤ x * (R * k) := Nat.mul_le_mul_left x hreach
  have h2 : Q * k * k ≤ x * R * k := by rw [← hact, Nat.mul_assoc]; exact h1
  exact Nat.le_of_mul_le_mul_right h2 hk

/-- **Every layer.** With the same quantum and the same reach at every layer, every layer's acts keep the same floor, on every layer's
    grid. -/
theorem mg_reach_floor_every_layer (Q R : Nat) (k x e : Nat → Nat) (hk : ∀ n, 0 < k n) (hact : ∀ n, x n * e n = Q * k n * k n)
    (hreach : ∀ n, e n ≤ R * k n) : ∀ n, Q * k n ≤ x n * R :=
  fun n => mg_reach_existence_floor Q R (k n) (x n) (e n) (hk n) (hact n) (hreach n)

/-- **Never zero.** With a positive quantum, an act within reach has positive existence. -/
theorem mg_reach_floor_positive (Q R k x e : Nat) (hQ : 0 < Q) (hk : 0 < k) (hact : x * e = Q * k * k) (hreach : e ≤ R * k) :
    0 < x := by
  have h := mg_reach_existence_floor Q R k x e hk hact hreach
  have hQk : 0 < Q * k := Nat.mul_pos hQ hk
  cases x with
  | zero => simp at h; omega
  | succ n => exact Nat.succ_pos n

/-- **No reach, no floor.** Without Axiom 1's bound on the extent, every proposed floor `Q / R` is undercut: some act on some grid has
    existence below it. The payload's case. -/
theorem mg_no_reach_no_floor (Q R : Nat) (hQ : 0 < Q) :
    ∃ k x e, 0 < k ∧ x * e = Q * k * k ∧ x * R < Q * k := by
  refine ⟨R + 1, 1, Q * (R + 1) * (R + 1), Nat.succ_pos R, Nat.one_mul _, ?_⟩
  have h : R + 1 ≤ Q * (R + 1) := Nat.le_mul_of_pos_left (R + 1) hQ
  omega

/-! ## The existence TTL (the owner, 2026-11-21)

"Using an existence TTL would be a good analog for that. [...] it derives the existence from the confined space (3s), as well as the time
it's existence is certified (1t)." The time side has the same shape: a certificate lives `τ` ticks (`τ / k` units of time), its existence
times its time to live is one quantum (`x · τ = Q · k · k`, existence times time, the quantum of action), and Axiom 1's witnesses renew it
only within their reach in time, at most `Tmax` units (`τ ≤ Tmax · k`). -/

/-- **The TTL floor.** A certificate renewed within a bounded time has existence at least `Q / Tmax`, on every grid: a bounded time to
    live is a mass gap (physics: `Δ = ħ / TTL`, the TTL being the correlation time). -/
theorem mg_ttl_existence_floor (Q Tmax k x τ : Nat) (hk : 0 < k) (hcert : x * τ = Q * k * k) (httl : τ ≤ Tmax * k) :
    Q * k ≤ x * Tmax :=
  mg_reach_existence_floor Q Tmax k x τ hk hcert httl

/-- **3s1t: space and time certify the same existence.** If one existence is certified with one quantum both over its confined space
    (extent `e`) and over its time to live (`τ`), and it is not zero, then extent and time to live coincide in grid units: space reach and
    TTL are one statement (in physics, `reach = c · TTL`, with `c = 1` in these units). -/
theorem mg_space_time_certificate (Q k x e τ : Nat) (hx : 0 < x) (hspace : x * e = Q * k * k) (htime : x * τ = Q * k * k) :
    e = τ :=
  Nat.eq_of_mul_eq_mul_left hx (hspace.trans htime.symm)

end Dmp
