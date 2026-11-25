/-
Attempt r3-dmp (round 3, attempt 5), 2026-11-21. Released under Apache 2.0.

# The triviality test in a one-coupling toy flow

Note: `docs/mass-gap/weak-coupling/attempts/r3-dmp/NOTE.md`, sections 2 and 4.

A one-loop flow of one coupling `x` (g² for Yang–Mills, λ for φ⁴) under one blocking step towards long distances:
`flow b x = x + b·x²`. The sign of `b` is the sign of the one-loop coefficient:
- `b > 0`: asymptotic freedom (Yang–Mills; gluons carry the charge they transmit, antiscreening; Gross–Wilczek, Politzer 1973);
- `b = 0`: no running (pure U(1), the free photon: its carrier carries no charge);
- `b < 0`: infrared freedom (φ⁴ in four dimensions; screening).

A regularised theory with `n` blocking steps between the cutoff and the physical scale is the chain bare coupling → `flow^[n]` →
physical coupling; the continuum limit is `n → ∞` (n ~ log(1/a)). In DMP terms the chain is a recipe whose root (line 0, the
galaxy) is the bare theory at the cutoff; the continuum limit sends the root to infinite depth (the root swap at the existence
boundary of `PREP.md`, read in the ultraviolet).

What is proved (toy model only; the real statements are Balaban, the OpenAI construction, and Aizenman–Duminil-Copin 2021):
1. `irFree_trivial`: for `b = -c < 0`, every bare coupling in the perturbative range `(0, 1/c)` reaches the physical scale with
   coupling at most `1/(n·c)`: the limit `n → ∞` is free, whatever the bare coupling (triviality, the φ⁴₄ shape).
2. `af_shoot`, `af_bare_bound`, `af_bare_coupling_vanishes`: for `b > 0`, every prescribed physical coupling `c > 0` is reached from a
   bare coupling `x_n ∈ (0, c]` (shooting, as the OpenAI construction's `Selected.reaches`), and `x_n ≤ 1/(1/c + n·b/(1+bc)) → 0`:
   the root at infinite depth is the free theory, and the chain out of it is non-trivial (asymptotic freedom).
3. `photon_flat`: for `b = 0` the coupling is the same at every scale (a free field at every coupling, no scale).
4. `af_reaches_one`, `photon_never_reaches`, `irFree_never_reaches`: only `b > 0` brings the coupling to order one at a finite scale
   (dimensional transmutation: the scale L₁ where α_s is of order one, the owner's α pointer). The photon and φ⁴ never get there.
-/

import Mathlib

namespace Attempts.R3.DmpHost

/-- One blocking step of a one-loop flow: `x ↦ x + b·x²`. -/
def flow (b x : ℝ) : ℝ := x + b * x ^ 2

theorem flow_continuous (b : ℝ) : Continuous (flow b) := by
  unfold flow; fun_prop

/-! ## The photon: b = 0 -/

/-- **No running.** With `b = 0` the coupling is the same after any number of steps. -/
theorem photon_flat (x : ℝ) (n : ℕ) : (flow 0)^[n] x = x := by
  have h : flow 0 = id := by funext y; simp [flow]
  rw [h, Function.iterate_id, id]

/-- The photon's coupling never reaches order one from below. -/
theorem photon_never_reaches {x : ℝ} (hx : x < 1) (n : ℕ) : (flow 0)^[n] x < 1 := by
  rw [photon_flat]; exact hx

/-! ## Infrared freedom: b = -c < 0 (φ⁴ in four dimensions) -/

theorem irStep_pos {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hxc : x < 1 / c) : 0 < flow (-c) x ∧ flow (-c) x ≤ x := by
  have hcx : c * x < 1 := by rwa [lt_div_iff₀ hc, mul_comm] at hxc
  unfold flow
  constructor
  · nlinarith
  · nlinarith [sq_nonneg x]

theorem irStep_inv {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hxc : x < 1 / c) : 1 / x + c ≤ 1 / flow (-c) x := by
  have hcx : c * x < 1 := by rwa [lt_div_iff₀ hc, mul_comm] at hxc
  have hf : flow (-c) x = x * (1 - c * x) := by unfold flow; ring
  have h1 : 0 < 1 - c * x := by linarith
  rw [hf, div_add' _ _ _ hx.ne', div_le_div_iff₀ hx (mul_pos hx h1)]
  nlinarith [sq_nonneg (c * x), mul_pos hx (mul_pos hc hc)]

/-- **Triviality (toy).** With `b = -c < 0`, from any bare coupling in `(0, 1/c)`, after `n` steps the coupling stays in `(0, 1/c)`
    and its inverse has grown by at least `n·c`. -/
theorem irFree_iterate {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hxc : x < 1 / c) (n : ℕ) :
    0 < (flow (-c))^[n] x ∧ (flow (-c))^[n] x ≤ x ∧ 1 / x + n * c ≤ 1 / (flow (-c))^[n] x := by
  induction n with
  | zero => simpa using hx
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have hlt : (flow (-c))^[k] x < 1 / c := lt_of_le_of_lt h1 hxc
    obtain ⟨p0, p1⟩ := irStep_pos hc h0 hlt
    have p2 := irStep_inv hc h0 hlt
    rw [Function.iterate_succ_apply']
    refine ⟨p0, le_trans p1 h1, ?_⟩
    push_cast
    linarith

/-- **Triviality (toy), the bound.** After `n ≥ 1` steps the physical coupling is at most `1/(n·c)`, for every bare coupling in the
    perturbative range: as the cutoff is removed (`n → ∞`) the theory becomes free. -/
theorem irFree_trivial {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hxc : x < 1 / c) {n : ℕ} (hn : 1 ≤ n) :
    (flow (-c))^[n] x ≤ 1 / (n * c) := by
  obtain ⟨h0, -, h2⟩ := irFree_iterate hc hx hxc n
  have hnc : 0 < (n : ℝ) * c := mul_pos (by exact_mod_cast hn) hc
  have h3 : (n : ℝ) * c ≤ 1 / (flow (-c))^[n] x := by
    have : 0 < 1 / x := by positivity
    linarith
  rwa [le_one_div h0 hnc]

/-- φ⁴'s coupling never reaches order one from the perturbative range: it only decreases. -/
theorem irFree_never_reaches {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hxc : x < 1 / c) (hx1 : x < 1) (n : ℕ) :
    (flow (-c))^[n] x < 1 :=
  lt_of_le_of_lt (irFree_iterate hc hx hxc n).2.1 hx1

/-! ## Asymptotic freedom: b > 0 (Yang–Mills) -/

theorem afStep_ge {b x : ℝ} (hb : 0 ≤ b) : x ≤ flow b x := by
  unfold flow; nlinarith [sq_nonneg x]

theorem af_iterate_ge {b x : ℝ} (hb : 0 ≤ b) (n : ℕ) : x ≤ (flow b)^[n] x := by
  induction n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply']; exact le_trans ih (afStep_ge hb)

theorem af_iterate_zero (b : ℝ) (n : ℕ) : (flow b)^[n] 0 = 0 :=
  Function.iterate_fixed (by simp [flow]) n

/-- **Shooting.** With `b > 0`, every prescribed physical coupling `c > 0` is reached after `n` steps from some bare coupling in
    `(0, c]` (the OpenAI construction fixes its unit the same way: `Selected.reaches`, β at level 0 equals `bar`). -/
theorem af_shoot {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (n : ℕ) : ∃ x, 0 < x ∧ x ≤ c ∧ (flow b)^[n] x = c := by
  have hcont : ContinuousOn ((flow b)^[n]) (Set.Icc 0 c) := ((flow_continuous b).iterate n).continuousOn
  have hmem : c ∈ Set.Icc ((flow b)^[n] 0) ((flow b)^[n] c) :=
    ⟨by rw [af_iterate_zero]; exact hc.le, af_iterate_ge hb.le n⟩
  obtain ⟨x, ⟨hx0, hxc⟩, hfx⟩ := intermediate_value_Icc hc.le hcont hmem
  refine ⟨x, ?_, hxc, hfx⟩
  rcases hx0.lt_or_eq with h | h
  · exact h
  · subst h; rw [af_iterate_zero] at hfx; exact absurd hfx hc.ne

theorem afStep_inv {b c y : ℝ} (hb : 0 < b) (hy : 0 < y) (hyc : y ≤ c) : 1 / flow b y + b / (1 + b * c) ≤ 1 / y := by
  have hby : 0 < 1 + b * y := by positivity
  have hf : 1 / flow b y = 1 / y - b / (1 + b * y) := by
    unfold flow; field_simp; ring
  have hle : b / (1 + b * c) ≤ b / (1 + b * y) :=
    div_le_div_of_nonneg_left hb.le hby (by nlinarith)
  rw [hf]; linarith

/-- With `b > 0`, if the chain lands at or below `c`, the inverse bare coupling exceeds the inverse physical coupling by at least
    `n·b/(1+bc)`. -/
theorem af_inverse_gain {b c : ℝ} (hb : 0 < b) (n : ℕ) :
    ∀ x : ℝ, 0 < x → (flow b)^[n] x ≤ c → n * (b / (1 + b * c)) ≤ 1 / x - 1 / (flow b)^[n] x := by
  induction n with
  | zero => intro x _ _; simp
  | succ k ih =>
    intro x hx hle
    rw [Function.iterate_succ_apply] at hle ⊢
    have hfx : 0 < flow b x := lt_of_lt_of_le hx (afStep_ge hb.le)
    have hrec := ih (flow b x) hfx hle
    have hxc : x ≤ c := le_trans (le_trans (afStep_ge hb.le) (af_iterate_ge hb.le k)) hle
    have hstep := afStep_inv hb hx hxc
    push_cast
    linarith

/-- **Asymptotic freedom (toy): the bare coupling of a chain of depth `n` landing on `c` is at most `1/(1/c + n·b/(1+bc))`.** -/
theorem af_bare_bound {b c x : ℝ} (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) {n : ℕ} (hland : (flow b)^[n] x = c) :
    x ≤ 1 / (1 / c + n * (b / (1 + b * c))) := by
  have h := af_inverse_gain hb n x hx hland.le
  rw [hland] at h
  have hA : 0 < 1 / c + n * (b / (1 + b * c)) := by positivity
  rw [le_one_div hx hA]
  linarith

/-- **The root at infinite depth is free.** For every `ε > 0` there is a depth beyond which every bare coupling that lands on `c` is
    below `ε`: the continuum limit's root is the free theory, and the chain out of it reaches the non-zero `c`. -/
theorem af_bare_coupling_vanishes {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x, 0 < x → (flow b)^[n] x = c → x < ε := by
  intro ε hε
  set m := b / (1 + b * c) with hm
  have hm0 : 0 < m := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (ε * m))
  refine ⟨N, fun n hn x hx hland => ?_⟩
  have hbound := af_bare_bound hb hc hx hland
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnm : 1 / ε < n * m := by
    have h1 : 1 / (ε * m) * m = 1 / ε := by field_simp
    have h2 : 1 / (ε * m) * m < n * m := mul_lt_mul_of_pos_right (lt_of_lt_of_le hN hnN) hm0
    linarith
  have hc' : 0 < 1 / c := by positivity
  have hA : 1 / ε < 1 / c + n * m := by linarith
  have hpos : 0 < 1 / ε := by positivity
  calc x ≤ 1 / (1 / c + n * m) := hbound
    _ < 1 / (1 / ε) := one_div_lt_one_div_of_lt hpos hA
    _ = ε := by field_simp

/-- With `b > 0` the coupling after `n` steps has grown by at least `n·b·x²`. -/
theorem af_growth {b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) (n : ℕ) : x + n * (b * x ^ 2) ≤ (flow b)^[n] x := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hy : x ≤ (flow b)^[k] x := af_iterate_ge hb k
    have hsq : x ^ 2 ≤ ((flow b)^[k] x) ^ 2 := pow_le_pow_left₀ hx hy 2
    set y := (flow b)^[k] x
    have hfy : flow b y = y + b * y ^ 2 := rfl
    rw [hfy]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hsq hb]

/-- **Scale generation.** With `b > 0`, from any positive coupling the flow reaches order one after finitely many steps: the scale
    L₁ exists (dimensional transmutation). -/
theorem af_reaches_one {b x : ℝ} (hb : 0 < b) (hx : 0 < x) : ∃ n : ℕ, 1 ≤ (flow b)^[n] x := by
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / (b * x ^ 2))
  refine ⟨n, le_trans ?_ (af_growth hb.le hx.le n)⟩
  have hbx : 0 < b * x ^ 2 := by positivity
  have : 1 ≤ n * (b * x ^ 2) := by rwa [div_le_iff₀ hbx] at hn
  linarith

end Attempts.R3.DmpHost
