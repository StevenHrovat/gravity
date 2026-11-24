/-
The join-loss round, part 2: in the boundary-uniform (pointwise) form the join loss is zero (2026-11-23). Released under
Apache 2.0.

Note: `docs/unified/JOIN-LOSS.md`, section 3.
-/

import ProofPhase.Unified.JoinLoss

/-!
# The boundary-uniform electric factor is submultiplicative: zero join loss in the slab geometry

**Setting (finite, abstract).** `X` a finite set of face configurations, `Ω : X → X` an involution (the centre twist of
a face: the `k`-links at `x_k = c` multiplied by `−1`). A slab of length `n` in the series direction is a positive kernel
`K x y` between its two end faces (the outside of the slab is its end-face data). The twisted slab has `K x (Ω y)`: one
centre sheet across the slab. Sectors at the far face:
`sec0 K x y = (K x y + K x (Ω y))/2` (`Z_{e=0}`) and `sec1 K x y = (K x y − K x (Ω y))/2` (`Z_{e=1}`). Joining two slabs
through a shared face is `kcomp Ka Kb x y = Σ_z Ka x z · Kb z y`.

**Theorems.**
* `kcomp_sectors`: if the second slab is centre-symmetric, `Kb (Ω z) (Ω y) = Kb z y`, the sectors of the joined slab are
  the face sums of the sectors: `sec_e (Ka Kb) = Σ_z sec_e Ka · sec_e Kb`. The cross terms (`e = 0` on one side, `e = 1`
  on the other) cancel exactly over the shared face.
* **`elec_submul`**: if `|sec1 Ka| ≤ ρa · sec0 Ka` and `|sec1 Kb| ≤ ρb · sec0 Kb` pointwise, then
  `|sec1 (Ka Kb)| ≤ ρa ρb · sec0 (Ka Kb)` pointwise. The boundary-uniform electric factor is submultiplicative:
  **the join loss is zero**.
* `sector_of_twist`: a pointwise twist ratio `K x (Ω y) ≥ c K x y` for all end faces gives
  `|sec1 K| ≤ elec(c) · sec0 K`.
* **`three_slabs_O1`**: three slabs in series, the last two centre-symmetric, each on the electric side pointwise
  (twist ratio at least `√2 − 1` for every end-face outside): for every `μ ≤ 14` the joined slab satisfies
  `μ |Z_{e=1}| ≤ Z_{e=0}` for every end-face outside (O1 in its sector form, `oneBox_sector`), via `three_steps_clear`.
* `kchain_elec`: `n + 1` centre-symmetric layers, each with pointwise twist ratio at least `c`:
  `|Z_{e=1}| ≤ elec(c)^{n+1} Z_{e=0}` pointwise.
* **`kchain_tanh`** (with `elec_exp_neg_two_mul`, `elec(e^{−2s}) = tanh s`): a single-layer floor `K x (Ω y) ≥ e^{−2s} K x y`
  (SU(2) Wilson: `s = βN`, `N` the plaquettes of the sheet) gives `|Z_{e=1}| ≤ tanh(s)^{n+1} Z_{e=0}` for every
  end-face outside: an unconditional boundary-uniform rate `log coth(βN)` per layer, which degenerates in the continuum.

**When is a slab centre-symmetric?** Multiplying all `k`-links at `x_k = c` (faces and interior) by `−1` leaves every
plaquette of the Wilson action invariant (each plaquette has zero or two such links). So `Kb (Ω z) (Ω y) = Kb z y` holds
when the slab has no outside other than its end faces, i.e. when the two directions transverse to the twist plane are
periodic (the slab geometry). With fixed side outsides the symmetry fails at the side collar (a seam of flipped side
plaquettes), and the join loss returns as the cost of that seam. [classical lattice fact, not formalised here for the
gauge chain]

**Claim discipline.** Not O1. The electric side in this pointwise-uniform form (`c ≥ √2 − 1` for every end-face outside
at the hand-over slab) is open, and is stronger than the torus (annealed) side. The slab geometry is not the box
geometry of the tube chain. Finite face space; for compact `G` the same algebra holds with integrals (Haar measure
invariant under the centre multiplication), not formalised here.
-/

open Finset

noncomputable section

namespace ProofPhase.Unified

section Slab

variable {X : Type*} [Fintype X]

/-- The neutral sector of a slab at its far face, `Z_{e=0}`. -/
def sec0 (Ω : X → X) (K : X → X → ℝ) (x y : X) : ℝ := (K x y + K x (Ω y)) / 2

/-- The charged sector of a slab at its far face, `Z_{e=1}`. -/
def sec1 (Ω : X → X) (K : X → X → ℝ) (x y : X) : ℝ := (K x y - K x (Ω y)) / 2

/-- Two slabs joined through a shared face. -/
def kcomp (Ka Kb : X → X → ℝ) (x y : X) : ℝ := ∑ z, Ka x z * Kb z y

variable {Ω : X → X}

/-- Summing over the shared face is invariant under the twist of that face. -/
theorem sum_twist (hΩ : Function.Involutive Ω) (f : X → ℝ) : ∑ z, f (Ω z) = ∑ z, f z :=
  Equiv.sum_comp (Function.Involutive.toPerm Ω hΩ) f

/-- **The sectors of a joined slab are face sums of the sectors**; the mixed terms cancel over the shared face. -/
theorem kcomp_sectors (hΩ : Function.Involutive Ω) {Ka Kb : X → X → ℝ} (hb : ∀ z y, Kb (Ω z) (Ω y) = Kb z y)
    (x y : X) :
    sec0 Ω (kcomp Ka Kb) x y = ∑ z, sec0 Ω Ka x z * sec0 Ω Kb z y ∧
      sec1 Ω (kcomp Ka Kb) x y = ∑ z, sec1 Ω Ka x z * sec1 Ω Kb z y := by
  have hb' : ∀ z, Kb z (Ω y) = Kb (Ω z) y := fun z => by
    have := hb (Ω z) y; rwa [hΩ z] at this
  have hpl : ∑ z, (sec0 Ω Ka x z * sec0 Ω Kb z y + sec1 Ω Ka x z * sec1 Ω Kb z y) = kcomp Ka Kb x y := by
    have hpt : ∀ z, sec0 Ω Ka x z * sec0 Ω Kb z y + sec1 Ω Ka x z * sec1 Ω Kb z y =
        (Ka x z * Kb z y + Ka x (Ω z) * Kb (Ω z) y) / 2 := by
      intro z; unfold sec0 sec1; rw [hb' z]; ring
    have hr : ∑ z, Ka x (Ω z) * Kb (Ω z) y = ∑ z, Ka x z * Kb z y := sum_twist hΩ (fun z => Ka x z * Kb z y)
    rw [sum_congr rfl (fun z _ => hpt z), ← sum_div, sum_add_distrib, hr]
    unfold kcomp; ring
  have hmi : ∑ z, (sec0 Ω Ka x z * sec0 Ω Kb z y - sec1 Ω Ka x z * sec1 Ω Kb z y) = kcomp Ka Kb x (Ω y) := by
    have hpt : ∀ z, sec0 Ω Ka x z * sec0 Ω Kb z y - sec1 Ω Ka x z * sec1 Ω Kb z y =
        (Ka x z * Kb z (Ω y) + Ka x (Ω z) * Kb (Ω z) (Ω y)) / 2 := by
      intro z; unfold sec0 sec1; rw [hb z y]; ring
    have hr : ∑ z, Ka x (Ω z) * Kb (Ω z) (Ω y) = ∑ z, Ka x z * Kb z (Ω y) :=
      sum_twist hΩ (fun z => Ka x z * Kb z (Ω y))
    rw [sum_congr rfl (fun z _ => hpt z), ← sum_div, sum_add_distrib, hr]
    unfold kcomp; ring
  rw [sum_add_distrib] at hpl
  rw [sum_sub_distrib] at hmi
  constructor
  · rw [show sec0 Ω (kcomp Ka Kb) x y = (kcomp Ka Kb x y + kcomp Ka Kb x (Ω y)) / 2 from rfl, ← hpl, ← hmi]; ring
  · rw [show sec1 Ω (kcomp Ka Kb) x y = (kcomp Ka Kb x y - kcomp Ka Kb x (Ω y)) / 2 from rfl, ← hpl, ← hmi]; ring

/-- **Zero join loss in the boundary-uniform form**: pointwise electric factors multiply under joining. -/
theorem elec_submul (hΩ : Function.Involutive Ω) {Ka Kb : X → X → ℝ} (hb : ∀ z y, Kb (Ω z) (Ω y) = Kb z y)
    {ρa ρb : ℝ} (ha : ∀ x z, |sec1 Ω Ka x z| ≤ ρa * sec0 Ω Ka x z)
    (hbb : ∀ z y, |sec1 Ω Kb z y| ≤ ρb * sec0 Ω Kb z y) (x y : X) :
    |sec1 Ω (kcomp Ka Kb) x y| ≤ (ρa * ρb) * sec0 Ω (kcomp Ka Kb) x y := by
  obtain ⟨h0, h1⟩ := kcomp_sectors hΩ (Ka := Ka) hb x y
  rw [h0, h1]
  calc |∑ z, sec1 Ω Ka x z * sec1 Ω Kb z y| ≤ ∑ z, |sec1 Ω Ka x z * sec1 Ω Kb z y| := abs_sum_le_sum_abs _ _
    _ = ∑ z, |sec1 Ω Ka x z| * |sec1 Ω Kb z y| := by simp only [abs_mul]
    _ ≤ ∑ z, (ρa * sec0 Ω Ka x z) * (ρb * sec0 Ω Kb z y) := by
        refine sum_le_sum fun z _ => mul_le_mul (ha x z) (hbb z y) (abs_nonneg _) ?_
        exact (abs_nonneg _).trans (ha x z)
    _ = (ρa * ρb) * ∑ z, sec0 Ω Ka x z * sec0 Ω Kb z y := by rw [mul_sum]; congr 1; ext z; ring

omit [Fintype X] in
/-- **A pointwise twist ratio gives a pointwise electric factor**: `K x (Ω y) ≥ c K x y` for all end faces implies
`|sec1 K| ≤ elec(c) · sec0 K`. -/
theorem sector_of_twist (hΩ : Function.Involutive Ω) {K : X → X → ℝ} {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ x y, c * K x y ≤ K x (Ω y)) (x y : X) : |sec1 Ω K x y| ≤ elec c * sec0 Ω K x y := by
  have hc' : c * K x (Ω y) ≤ K x y := by have := hc x (Ω y); rwa [hΩ y] at this
  have hcy := hc x y
  have h1c : 0 < 1 + c := by linarith
  have key : (1 + c) * |K x y - K x (Ω y)| ≤ (1 - c) * (K x y + K x (Ω y)) := by
    rcases abs_cases (K x y - K x (Ω y)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> nlinarith
  unfold sec1 sec0 elec
  rw [abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2), div_mul_div_comm,
    div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [key]

omit [Fintype X] in
/-- The neutral sector of a nonnegative kernel is nonnegative. -/
theorem sec0_nonneg {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y) (x y : X) : 0 ≤ sec0 Ω K x y := by
  unfold sec0; have := hK x y; have := hK x (Ω y); positivity

/-- A join of two centre-symmetric slabs is centre-symmetric. -/
theorem kcomp_sym (hΩ : Function.Involutive Ω) {Ka Kb : X → X → ℝ} (ha : ∀ z y, Ka (Ω z) (Ω y) = Ka z y)
    (hb : ∀ z y, Kb (Ω z) (Ω y) = Kb z y) (x y : X) : kcomp Ka Kb (Ω x) (Ω y) = kcomp Ka Kb x y := by
  unfold kcomp
  rw [← sum_twist hΩ (fun z => Ka (Ω x) z * Kb z (Ω y))]
  exact sum_congr rfl fun z _ => by rw [ha, hb]

/-- **Three slabs on the electric side clear O1 with no join loss.** Positive kernels `K₁, K₂, K₃`, the last two
centre-symmetric, each with pointwise twist ratio at least `√2 − 1` for every end-face outside (the electric side of the
hand-over, uniformly). Then for every `0 ≤ μ ≤ 14` the joined slab has `μ |Z_{e=1}| ≤ Z_{e=0}` for every end-face
outside: O1 in its sector form (`oneBox_sector`), here from `three_steps_clear`. -/
theorem three_slabs_O1 (hΩ : Function.Involutive Ω) {K₁ K₂ K₃ : X → X → ℝ} (hK₁ : ∀ x y, 0 < K₁ x y)
    (hK₂ : ∀ x y, 0 < K₂ x y) (hK₃ : ∀ x y, 0 < K₃ x y) (hs₂ : ∀ z y, K₂ (Ω z) (Ω y) = K₂ z y)
    (hs₃ : ∀ z y, K₃ (Ω z) (Ω y) = K₃ z y) (he₁ : ∀ x y, (√2 - 1) * K₁ x y ≤ K₁ x (Ω y))
    (he₂ : ∀ x y, (√2 - 1) * K₂ x y ≤ K₂ x (Ω y)) (he₃ : ∀ x y, (√2 - 1) * K₃ x y ≤ K₃ x (Ω y)) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ 14) (x y : X) :
    μ * |sec1 Ω (kcomp (kcomp K₁ K₂) K₃) x y| ≤ sec0 Ω (kcomp (kcomp K₁ K₂) K₃) x y := by
  have hp : 0 < √2 - 1 := sqrt_two_sub_one_pos
  have b₁ := sector_of_twist hΩ hp he₁
  have b₂ := sector_of_twist hΩ hp he₂
  have b₃ := sector_of_twist hΩ hp he₃
  have b₁₂ := elec_submul hΩ hs₂ b₁ b₂
  have b₁₂₃ := elec_submul hΩ hs₃ b₁₂ b₃ x y
  rw [elec_selfdual] at b₁₂₃
  have hcube : (√2 - 1) * (√2 - 1) * (√2 - 1) = (√2 - 1) ^ 3 := by ring
  rw [hcube] at b₁₂₃
  have hclear := three_steps_clear hμ0 hμ
  have h12 : ∀ x y, 0 ≤ kcomp K₁ K₂ x y := fun x y => sum_nonneg fun z _ => (mul_pos (hK₁ x z) (hK₂ z y)).le
  have n123 : 0 ≤ sec0 Ω (kcomp (kcomp K₁ K₂) K₃) x y :=
    sec0_nonneg (fun x y => sum_nonneg fun z _ => mul_nonneg (h12 x z) (hK₃ z y).le) x y
  calc μ * |sec1 Ω (kcomp (kcomp K₁ K₂) K₃) x y|
      ≤ μ * ((√2 - 1) ^ 3 * sec0 Ω (kcomp (kcomp K₁ K₂) K₃) x y) := mul_le_mul_of_nonneg_left b₁₂₃ hμ0
    _ = ((√2 - 1) ^ 3 * μ) * sec0 Ω (kcomp (kcomp K₁ K₂) K₃) x y := by ring
    _ ≤ 1 * sec0 Ω (kcomp (kcomp K₁ K₂) K₃) x y := mul_le_mul_of_nonneg_right hclear.le n123
    _ = _ := one_mul _

/-- `n + 1` layers (slabs) in series: `kchain T 0 = T 0`, `kchain T (n + 1) = kchain T n ∘ T (n + 1)`. -/
def kchain (T : ℕ → X → X → ℝ) : ℕ → X → X → ℝ
  | 0 => T 0
  | n + 1 => kcomp (kchain T n) (T (n + 1))

/-- **Layers in series, no loss**: centre-symmetric layers, each with pointwise twist ratio at least `c` for every
end-face outside, give `|Z_{e=1}| ≤ elec(c)^{n+1} Z_{e=0}` for `n + 1` layers, pointwise. -/
theorem kchain_elec (hΩ : Function.Involutive Ω) {T : ℕ → X → X → ℝ} (hsym : ∀ n z y, T n (Ω z) (Ω y) = T n z y)
    {c : ℝ} (hc0 : 0 < c) (hc : ∀ n x y, c * T n x y ≤ T n x (Ω y)) (n : ℕ) (x y : X) :
    |sec1 Ω (kchain T n) x y| ≤ elec c ^ (n + 1) * sec0 Ω (kchain T n) x y := by
  induction n generalizing x y with
  | zero =>
    rw [show kchain T 0 = T 0 from rfl, zero_add, pow_one]
    exact sector_of_twist hΩ hc0 (hc 0) x y
  | succ n ih =>
    have h := elec_submul hΩ (hsym (n + 1)) (fun x z => ih x z) (sector_of_twist hΩ hc0 (hc (n + 1))) x y
    rw [show kchain T (n + 1) = kcomp (kchain T n) (T (n + 1)) from rfl, pow_succ]
    exact h

/-- `elec(e^{−2s}) = tanh s`. -/
theorem elec_exp_neg_two_mul (s : ℝ) : elec (Real.exp (-(2 * s))) = Real.tanh s := by
  have h : Real.exp (-(2 * s)) = Real.exp (-s) * Real.exp (-s) := by rw [← Real.exp_add]; ring_nf
  have hs : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
  have hp : 0 < Real.exp s := Real.exp_pos s
  have hq : 0 < Real.exp (-s) := Real.exp_pos (-s)
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, elec, h,
    div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-Real.exp (-s)) * hs

/-- **The single-layer floor gives a rate with no join loss**: if one layer's twist changes the weight by at most a
factor `e^{−2s}` pointwise (SU(2) Wilson action: `s = βN`, `N` the plaquettes of the sheet, the per-configuration floor
of `SATURATION.md` 1), then `n + 1` layers have `|Z_{e=1}| ≤ tanh(s)^{n+1} Z_{e=0}` for every end-face outside. -/
theorem kchain_tanh (hΩ : Function.Involutive Ω) {T : ℕ → X → X → ℝ} (hsym : ∀ n z y, T n (Ω z) (Ω y) = T n z y)
    {s : ℝ} (hc : ∀ n x y, Real.exp (-(2 * s)) * T n x y ≤ T n x (Ω y)) (n : ℕ) (x y : X) :
    |sec1 Ω (kchain T n) x y| ≤ Real.tanh s ^ (n + 1) * sec0 Ω (kchain T n) x y := by
  rw [← elec_exp_neg_two_mul]
  exact kchain_elec hΩ hsym (Real.exp_pos _) hc n x y

end Slab

end ProofPhase.Unified
