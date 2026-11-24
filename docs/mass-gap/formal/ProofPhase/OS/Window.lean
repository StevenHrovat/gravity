/-
Proof phase, windowed OS reconstruction (os-windowed), module 1: reflection-positive data with a finite time window
(2026-11-23). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/os-windowed/NOTE.md`; pack `m1-tools/PACK-OSDATA.md`, route A.
-/

import OneScale.Doubling
import Positivity.Abstract

/-!
# Windowed reflection-positive data

On a periodic torus the time shift carries a positive-time observable around the circle, so the reflection form is
positive only on the translates that still lie in the positive half. `WinRP` records exactly that:

* a real vector space `V` (bounded measurable observables), a symmetric bilinear form `Q u v` (`= E[u · θv]`) and a
  linear step `τ` (time translation by one lattice step) with `Q (τ u) v = Q u (τ v)`, **for all** `u, v`
  (translation invariance and `S_k Θ = Θ S_{-k}`: no positivity needed);
* a subspace `P` (the observables of the closed positive half) on which `Q` is positive semidefinite (site reflection
  positivity).

No boundedness of orbits, no `τ`-invariance of `P`, and no positivity of `τ` (link reflection) is assumed. An observable
`x` is **`K`-admissible** (`Adm K x`) if `τ^i x ∈ P` for `i ≤ K`: it can be transported `K` steps before it reaches
the edge of the positive half.

**Results.**
* `cs`: Cauchy–Schwarz on `P`. `pow_symm`, `hankel`: `Q (τ^a x) (τ^b x) = H x (a + b)` with
  `H x t = Q x (τ^t x)` (the reflected correlation).
* `hankel_cs`: for a `K`-admissible `x`, the hypotheses of `OneScale.doubling` (Lemma 6.2) hold for `H x`. Odd times are
  covered by Cauchy–Schwarz between `τ^j x` and `τ^k x`, so link reflection positivity is not used.
* `win_decay` (**finite-horizon spectral upgrade, one vector**): a decay bound `|H x (2^r n)| ≤ C e^{-λ 2^r n}` gives
  `|H x n| ≤ (H x 0 + 2^{-r} C) e^{-λ n}`. The constant is gone up to an error `2^{-r} C`, which vanishes as the window
  grows (`r → ∞` with the torus).
* `win_contraction` (**approximate contraction**): `Q (τ^i x) (τ^i x) ≤ Q(x,x)^{1 - 2^{-r}} B^{2^{-r}}` when
  `2^r i ≤ K` and `B` bounds `Q (τ^{2^r i} x) (τ^{2^r i} x)`; the factor tends to the OS contraction as `K → ∞`.
* `win_gap_approx` (**the density step in finite volume**): if `f` is `K`-admissible with a decay bound at time `2^r n`
  and `F` is approximated by `f` in the OS seminorm, `Q (F - f) (F - f) ≤ ε`, then
  `|H F n| ≤ (Q F F + 2 √(Q F F · ε) + ε + 2^{-r} C) e^{-λ n} + √(ε B_F) + √(B_f ε)`,
  with `B_F, B_f` bounds for `Q (τ^n F) (τ^n F)` and `Q (τ^n f) (τ^n f)`. This replaces the Hilbert-space spectral
  upgrade of `M1.UVTV.RPData.gap_of_RP` (closure of the block span, `T`-invariance) by an estimate for one approximant
  at a time: the block gap is needed only for the approximants themselves, and no block subspace needs to be
  `τ`-invariant.
-/

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.OS

/-- **Windowed reflection-positive data**: a symmetric bilinear form, a symmetric step, and a subspace on which the form
is positive. -/
structure WinRP (V : Type*) [AddCommGroup V] [Module ℝ V] where
  /-- The OS form `Q u v = E[u · θv]`. -/
  Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  symm : ∀ u v, Q u v = Q v u
  /-- The time translation by one step. -/
  τ : V →ₗ[ℝ] V
  τ_symm : ∀ u v, Q (τ u) v = Q u (τ v)
  /-- The observables of the closed positive half. -/
  P : Submodule ℝ V
  /-- Reflection positivity on the positive half. -/
  pos : ∀ u ∈ P, 0 ≤ Q u u

namespace WinRP

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (R : WinRP V)

/-- The reflected correlation `H x t = Q x (τ^t x)`. -/
def H (x : V) (t : ℕ) : ℝ := R.Q x ((R.τ ^ t) x)

/-- `x` can be transported `K` steps inside the positive half. -/
def Adm (K : ℕ) (x : V) : Prop := ∀ i, i ≤ K → (R.τ ^ i) x ∈ R.P

theorem Adm.sub {K : ℕ} {x y : V} (hx : R.Adm K x) (hy : R.Adm K y) : R.Adm K (x - y) := by
  intro i hi
  rw [map_sub]
  exact R.P.sub_mem (hx i hi) (hy i hi)

theorem Adm.mono {K K' : ℕ} {x : V} (hx : R.Adm K x) (h : K' ≤ K) : R.Adm K' x :=
  fun i hi => hx i (hi.trans h)

theorem Adm.mem {K : ℕ} {x : V} (hx : R.Adm K x) : x ∈ R.P := by
  simpa using hx 0 (Nat.zero_le _)

/-! ### Cauchy–Schwarz and the Hankel structure -/

/-- **Cauchy–Schwarz on the positive half.** -/
theorem cs {u v : V} (hu : u ∈ R.P) (hv : v ∈ R.P) : R.Q u v ^ 2 ≤ R.Q u u * R.Q v v := by
  have key : ∀ t : ℝ, 0 ≤ R.Q u u * (t * t) + 2 * R.Q u v * t + R.Q v v := by
    intro t
    have h := R.pos (t • u + v) (R.P.add_mem (R.P.smul_mem t hu) hv)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [R.symm v u] at h
    nlinarith [h]
  have := Positivity.sq_le_mul_of_quadratic_nonneg key
  linarith [mul_comm (R.Q u u) (R.Q v v)]

theorem abs_le_sqrt {u v : V} (hu : u ∈ R.P) (hv : v ∈ R.P) : |R.Q u v| ≤ Real.sqrt (R.Q u u * R.Q v v) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (R.cs hu hv)

theorem pow_symm (a : ℕ) (u v : V) : R.Q ((R.τ ^ a) u) v = R.Q u ((R.τ ^ a) v) := by
  induction a generalizing u v with
  | zero => rfl
  | succ a ih =>
      have e1 : (R.τ ^ (a + 1)) u = R.τ ((R.τ ^ a) u) := by rw [pow_succ', Module.End.mul_apply]
      have e2 : (R.τ ^ (a + 1)) v = (R.τ ^ a) (R.τ v) := by rw [pow_succ, Module.End.mul_apply]
      rw [e1, e2, R.τ_symm, ih]

theorem pow_add_apply (a b : ℕ) (x : V) : (R.τ ^ a) ((R.τ ^ b) x) = (R.τ ^ (a + b)) x := by
  rw [pow_add, Module.End.mul_apply]

/-- **The Hankel identity**: `Q (τ^a x) (τ^b x) = H x (a + b)`. -/
theorem hankel (x : V) (a b : ℕ) : R.Q ((R.τ ^ a) x) ((R.τ ^ b) x) = R.H x (a + b) := by
  rw [R.pow_symm, R.pow_add_apply]
  rfl

theorem H_two_mul (x : V) (j : ℕ) : R.H x (2 * j) = R.Q ((R.τ ^ j) x) ((R.τ ^ j) x) := by
  rw [R.hankel, two_mul]

/-- **The doubling hypotheses for an admissible observable** (Lemma 6.2's input). -/
theorem hankel_cs {K : ℕ} {x : V} (hx : R.Adm K x) :
    (∀ j k, j ≤ K → k ≤ K → R.H x (j + k) ^ 2 ≤ R.H x (2 * j) * R.H x (2 * k)) ∧
      (∀ j, j ≤ K → 0 ≤ R.H x (2 * j)) := by
  refine ⟨fun j k hj hk => ?_, fun j hj => ?_⟩
  · rw [← R.hankel, R.H_two_mul, R.H_two_mul]
    exact R.cs (hx j hj) (hx k hk)
  · rw [R.H_two_mul]
    exact R.pos _ (hx j hj)

theorem H_zero (x : V) : R.H x 0 = R.Q x x := by simp [H]

/-! ### The finite-horizon upgrade for one vector -/

/-- **Windowed spectral upgrade for one vector.** For a `K`-admissible `x` with `2^{r-1} n ≤ K` and a decay bound at
time `2^r n`, the constant drops out up to `2^{-r} C`: `|H x n| ≤ (Q x x + 2^{-r} C) e^{-λ n}`. -/
theorem win_decay {K : ℕ} {x : V} (hx : R.Adm K x) {n r : ℕ} (hr : 1 ≤ r) (hnK : 2 ^ (r - 1) * n ≤ K) {C lam : ℝ}
    (hC : 0 ≤ C) (hdec : |R.H x (2 ^ r * n)| ≤ C * Real.exp (-(lam * (2 ^ r * n : ℕ)))) :
    |R.H x n| ≤ (R.Q x x + (1 / 2 : ℝ) ^ r * C) * Real.exp (-(lam * n)) := by
  obtain ⟨hcs, hpos⟩ := R.hankel_cs hx
  have h := OneScale.doubling_decay hcs hpos hr hnK hC hdec
  have h0 : 0 ≤ R.H x 0 := by simpa using hpos 0 (Nat.zero_le _)
  set q : ℝ := (1 / 2 : ℝ) ^ r
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hy := Real.geom_mean_le_arith_mean2_weighted (sub_nonneg.2 hq1) hq0 h0 hC (by ring)
  rw [R.H_zero] at h hy h0
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  nlinarith [mul_nonneg hq0 h0]

/-- **Approximate contraction.** If `2^r i ≤ K` and `B` bounds `Q (τ^{2^r i} x) (τ^{2^r i} x)`, then
`Q (τ^i x) (τ^i x) ≤ Q(x,x)^{1 - 2^{-r}} B^{2^{-r}}`. As the window grows (`r → ∞`) the factor tends to the OS
contraction `Q (τ^i x) (τ^i x) ≤ Q x x`. -/
theorem win_contraction {K : ℕ} {x : V} (hx : R.Adm K x) {i r : ℕ} (hr : 1 ≤ r) (hiK : 2 ^ r * i ≤ K) {B : ℝ}
    (hB : R.Q ((R.τ ^ (2 ^ r * i)) x) ((R.τ ^ (2 ^ r * i)) x) ≤ B) :
    R.Q ((R.τ ^ i) x) ((R.τ ^ i) x) ≤ R.Q x x ^ (1 - (1 / 2 : ℝ) ^ r) * B ^ ((1 / 2 : ℝ) ^ r) := by
  obtain ⟨hcs, hpos⟩ := R.hankel_cs hx
  have hm : 2 ^ (r - 1) * (2 * i) ≤ K := by
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    calc 2 ^ r' * (2 * i) = 2 ^ (r' + 1) * i := by ring
      _ ≤ K := hiK
  have hd := OneScale.doubling hcs hpos r hr hm
  have e : 2 ^ r * (2 * i) = 2 * (2 ^ r * i) := by ring
  rw [e, R.H_two_mul, R.H_two_mul, R.H_zero] at hd
  have hnn : 0 ≤ R.Q ((R.τ ^ (2 ^ r * i)) x) ((R.τ ^ (2 ^ r * i)) x) := R.pos _ (hx _ hiK)
  have h0 : 0 ≤ R.Q x x := R.pos _ hx.mem
  calc R.Q ((R.τ ^ i) x) ((R.τ ^ i) x) ≤ |R.Q ((R.τ ^ i) x) ((R.τ ^ i) x)| := le_abs_self _
    _ ≤ _ := hd
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hnn hB (by positivity)) (Real.rpow_nonneg h0 _)

/-! ### The density step -/

/-- The OS seminorm of `f` is at most that of `F` plus the approximation error: with `ε ≥ Q (F - f) (F - f)`,
`Q f f ≤ Q F F + 2 √(Q F F · ε) + ε`. -/
theorem Q_approx_le {F f : V} (hF : F ∈ R.P) (hf : f ∈ R.P) {ε : ℝ} (hε : R.Q (F - f) (F - f) ≤ ε) :
    R.Q f f ≤ R.Q F F + 2 * Real.sqrt (R.Q F F * ε) + ε := by
  have hy : F - f ∈ R.P := R.P.sub_mem hF hf
  have hyy := R.pos _ hy
  have hcs := R.abs_le_sqrt hF hy
  have hle : Real.sqrt (R.Q F F * R.Q (F - f) (F - f)) ≤ Real.sqrt (R.Q F F * ε) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hε (R.pos _ hF))
  have e : R.Q f f = R.Q F F - 2 * R.Q F (F - f) + R.Q (F - f) (F - f) := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [R.symm f F]
    ring
  rw [e]
  have := (abs_le.1 (hcs.trans hle)).1
  linarith

/-- **The density step in finite volume.** `F` and its approximant `f` are `K`-admissible, `2^{r-1} n ≤ K`, the
approximant decays at time `2^r n`, `Q (F - f) (F - f) ≤ ε`, and `B_F`, `B_f` bound the OS norms of the translates
`τ^n F`, `τ^n f`. Then
`|H F n| ≤ (Q F F + 2 √(Q F F · ε) + ε + 2^{-r} C) e^{-λ n} + √(ε B_F) + √(B_f ε)`. -/
theorem win_gap_approx {K : ℕ} {F f : V} (hF : R.Adm K F) (hf : R.Adm K f) {n r : ℕ} (hr : 1 ≤ r)
    (hnK : 2 ^ (r - 1) * n ≤ K) {ε BF Bf C lam : ℝ} (hε : R.Q (F - f) (F - f) ≤ ε)
    (hBF : R.Q ((R.τ ^ n) F) ((R.τ ^ n) F) ≤ BF) (hBf : R.Q ((R.τ ^ n) f) ((R.τ ^ n) f) ≤ Bf) (hC : 0 ≤ C)
    (hdec : |R.H f (2 ^ r * n)| ≤ C * Real.exp (-(lam * (2 ^ r * n : ℕ)))) :
    |R.H F n| ≤ (R.Q F F + 2 * Real.sqrt (R.Q F F * ε) + ε + (1 / 2 : ℝ) ^ r * C) * Real.exp (-(lam * n)) +
      Real.sqrt (ε * BF) + Real.sqrt (Bf * ε) := by
  have hnK' : n ≤ K := le_trans (Nat.le_mul_of_pos_left n (by positivity)) hnK
  set y := F - f with hydef
  have hy : R.Adm K y := hF.sub R hf
  have hyy : 0 ≤ R.Q y y := R.pos _ hy.mem
  -- the decomposition `H F n = H f n + Q f (τ^n y) + Q y (τ^n F)`
  have hdecomp : R.H F n = R.H f n + R.Q ((R.τ ^ n) f) y + R.Q y ((R.τ ^ n) F) := by
    rw [R.pow_symm]
    simp only [H, hydef, map_sub, LinearMap.sub_apply]
    ring
  -- the two cross terms
  have h1 : |R.Q y ((R.τ ^ n) F)| ≤ Real.sqrt (ε * BF) := by
    refine (R.abs_le_sqrt hy.mem (hF n hnK')).trans (Real.sqrt_le_sqrt ?_)
    exact mul_le_mul hε hBF (R.pos _ (hF n hnK')) (hyy.trans hε)
  have h2 : |R.Q ((R.τ ^ n) f) y| ≤ Real.sqrt (Bf * ε) := by
    refine (R.abs_le_sqrt (hf n hnK') hy.mem).trans (Real.sqrt_le_sqrt ?_)
    exact mul_le_mul hBf hε hyy ((R.pos _ (hf n hnK')).trans hBf)
  -- the approximant: windowed upgrade, then its OS norm
  have h3 := R.win_decay hf hr hnK hC hdec
  have h4 := R.Q_approx_le hF.mem hf.mem hε
  have hE := (Real.exp_pos (-(lam * n))).le
  have h3' : |R.H f n| ≤ (R.Q F F + 2 * Real.sqrt (R.Q F F * ε) + ε + (1 / 2 : ℝ) ^ r * C) *
      Real.exp (-(lam * n)) :=
    h3.trans (mul_le_mul_of_nonneg_right (by linarith) hE)
  rw [hdecomp]
  calc |R.H f n + R.Q ((R.τ ^ n) f) y + R.Q y ((R.τ ^ n) F)|
      ≤ |R.H f n| + |R.Q ((R.τ ^ n) f) y| + |R.Q y ((R.τ ^ n) F)| := abs_add_three _ _ _
    _ ≤ _ := by linarith

end WinRP

end ProofPhase.OS
