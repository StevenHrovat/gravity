/-
Birch and Swinnerton-Dyer through the API: the points on an existence line (2026-11-24).
Released under Apache 2.0.

Paper: `docs/unified/BSD.md` (sections 3 to 5), `docs/unified/API.md`. Mathlib-only core: `Unified/BSDCore.lean`.
-/

import ProofPhase.API
import ProofPhase.Unified.BSDCore

/-!
# BSD through the API: input + structure + one named open step

The owner's reading: "the zeros follow existence": the order of the zero of `L(E, s)` at `s = 1` counts the independent
rational points. This file writes that in the API's shape. It proves nothing about BSD that is open; every content step
sits in an `OpenStep` or `External` slot.

* **The steps are the primes** (`EulerData`): at the `n`-th prime `p` the curve has `N_p` points mod `p`, and the step's
  factor is `N_p / p`, the inverse of the local Euler factor of `L(E, s)` at `s = 1`.
* **Hasse's bound is the curve's proved Riemann hypothesis, and it is exactly an encoder** (`frob`): the Frobenius
  eigenvalue `α` with `α + ᾱ = a_p`, `α ᾱ = p` is the rotated image of `√p`, of the same norm exactly when
  `|a_p| ≤ 2 √p`. The reflection coefficient is `a_p / (2 √p) = cos θ_p` (`frob_refl`), the Szego factor is
  `sin² θ_p` (`frob_szego`, the Sato-Tate density), and the point count is `|1 - α|²` (`count_normSq`).
* **The encoder bounds give the ledger** (`EulerData.lower`, `upper`): each step keeps at least `(1 - p^{-1/2})²` and at
  most `(1 + p^{-1/2})²`; so no finite stage of the Euler product vanishes (`no_finite_zero`). The zero at `s = 1` is
  a property of the whole chain, a rate, not of any step.
* **The two counts as the two sides of one balance** (`problem`): the algebraic rank and the order of the zero. The open
  step is BSD itself; the conclusion is the existence line (`E(ℚ)` infinite exactly when `L(E, 1) = 0`) and the parity of
  the rank. External inputs: modularity (continuation and functional equation) and weak Mordell-Weil.
* **The ledger form of the open step** (`ledgerCard`): the 1965 form `∏_{p ≤ x} N_p/p ~ C (log x)^r`, with Goldfeld's
  theorem as the external input, gives BSD.
* **The slot is not empty** (`E32`, `bsd_E32`, `card_E32`): the curve `y² = x³ - x` (conductor 32), with its known
  values as external inputs, satisfies BSD; its point counts and Hasse checks run (`#eval`, `#guard`), proved equal to
  Mathlib's count (`count_E32`).

Standard axioms only.
-/

noncomputable section

namespace ProofPhase.API.BSD

open ProofPhase.BSD Filter Topology

/-! ## 1. Hasse's bound as an encoder -/

/-- **The Frobenius eigenvalue** with trace `a` and norm `q`: `α = a/2 + i √(q - a²/4)`. -/
def frobAlpha (a q : ℝ) : ℂ := ⟨a / 2, Real.sqrt (q - a ^ 2 / 4)⟩

theorem frobAlpha_normSq {a q : ℝ} (hH : a ^ 2 ≤ 4 * q) : Complex.normSq (frobAlpha a q) = q := by
  rw [Complex.normSq_apply]
  simp only [frobAlpha]
  have h : 0 ≤ q - a ^ 2 / 4 := by linarith
  have := Real.mul_self_sqrt h
  nlinarith [this]

theorem norm_frobAlpha {a q : ℝ} (hH : a ^ 2 ≤ 4 * q) : ‖frobAlpha a q‖ = Real.sqrt q := by
  rw [Complex.norm_def, frobAlpha_normSq hH]

/-- **The point count is `|1 - α|²`**: `q + 1 - a = (1 - α)(1 - ᾱ)`. -/
theorem count_normSq {a q : ℝ} (hH : a ^ 2 ≤ 4 * q) : Complex.normSq (1 - frobAlpha a q) = q + 1 - a := by
  rw [Complex.normSq_apply]
  simp only [frobAlpha, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  have h : 0 ≤ q - a ^ 2 / 4 := by linarith
  have := Real.mul_self_sqrt h
  nlinarith [this]

/-- **Hasse's bound as an encoder** (real inner product on `ℂ`): the state `√q` and its rotated image `α`, the Frobenius
eigenvalue. The encoder's one condition, the shared root `‖α‖ = ‖√q‖`, is Hasse's bound `a² ≤ 4 q`. -/
def frob (a q : ℝ) (hq : 0 < q) (hH : a ^ 2 ≤ 4 * q) : Encoder ℝ ℂ where
  ψ := (Real.sqrt q : ℂ)
  ψ' := frobAlpha a q
  root := by rw [norm_frobAlpha hH, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg q)]
  ne := by exact_mod_cast (Real.sqrt_pos.2 hq).ne'

/-- **The reflection coefficient is `a / (2 √q) = cos θ`**, the normalised trace of Frobenius. -/
theorem frob_refl (a q : ℝ) (hq : 0 < q) (hH : a ^ 2 ≤ 4 * q) : (frob a q hq hH).refl = a / (2 * Real.sqrt q) := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  show (((‖(Real.sqrt q : ℂ)‖ ^ 2)⁻¹ : ℝ) : ℝ) * inner ℝ (Real.sqrt q : ℂ) (frobAlpha a q) = _
  rw [Complex.inner, Complex.norm_real, Real.norm_of_nonneg hs.le, hsq]
  simp only [frobAlpha, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  field_simp
  rw [hsq, mul_comm]

/-- **The Szego factor is `1 - a²/(4q) = sin² θ`** (the Sato-Tate density), in `[0, 1]` by the API. -/
theorem frob_szego (a q : ℝ) (hq : 0 < q) (hH : a ^ 2 ≤ 4 * q) :
    (frob a q hq hH).szegoFactor = 1 - a ^ 2 / (4 * q) ∧ 0 ≤ (frob a q hq hH).szegoFactor ∧
      (frob a q hq hH).szegoFactor ≤ 1 := by
  refine ⟨?_, (frob a q hq hH).szegoFactor_mem⟩
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  show ProofPhase.Unified.szego (frob a q hq hH).refl = _
  rw [frob_refl, ProofPhase.Unified.szego, Real.norm_eq_abs, sq_abs, div_pow, mul_pow, hsq]
  norm_num

/-- **The encoder bounds on one step**: Hasse's bound puts the step factor `N/q = (q + 1 - a)/q` between
`(1 - q^{-1/2})²` and `(1 + q^{-1/2})²`. -/
theorem factor_bounds {a q : ℝ} (hq : 0 < q) (hH : a ^ 2 ≤ 4 * q) :
    (1 - 1 / Real.sqrt q) ^ 2 ≤ (q + 1 - a) / q ∧ (q + 1 - a) / q ≤ (1 + 1 / Real.sqrt q) ^ 2 := by
  set s := Real.sqrt q
  have hs : 0 < s := Real.sqrt_pos.2 hq
  have hsq : s ^ 2 = q := Real.sq_sqrt hq.le
  have ha : -(2 * s) ≤ a ∧ a ≤ 2 * s := abs_le.1 (abs_le_of_sq_le_sq' (by rw [mul_pow, hsq]; linarith)
    (by positivity) |> fun h => abs_le.2 h)
  have e1 : (q + 1 - a) / q - (1 - 1 / s) ^ 2 = (2 * s - a) / s ^ 2 := by
    rw [← hsq]; field_simp; ring
  have e2 : (1 + 1 / s) ^ 2 - (q + 1 - a) / q = (2 * s + a) / s ^ 2 := by
    rw [← hsq]; field_simp; ring
  constructor
  · have : 0 ≤ (2 * s - a) / s ^ 2 := div_nonneg (by linarith) (by positivity)
    linarith
  · have : 0 ≤ (2 * s + a) / s ^ 2 := div_nonneg (by linarith) (by positivity)
    linarith

/-! ## 2. The steps are the primes: the Euler ledger -/

/-- **The prime data of a curve** (the input of the ledger): at the `n`-th prime `p n`, the number `N n` of points mod
`p n` (at a bad prime: the nonsingular points with the point at infinity, so that `N/p` is the inverse local factor at
`s = 1` at every prime). Hasse's bound is an external input (Hasse 1933-36; not in Mathlib). -/
structure EulerData where
  N : ℕ → ℤ
  hasse : External "Hasse 1933-36: |p + 1 - N_p| <= 2 sqrt p for every elliptic curve over F_p (nonsingular points at bad p)"
    (∀ n, ((Nat.nth Nat.Prime n : ℝ) + 1 - N n) ^ 2 ≤ 4 * (Nat.nth Nat.Prime n : ℝ))

namespace EulerData

variable (D : EulerData)

/-- The `n`-th prime, as a real number. -/
def p (n : ℕ) : ℝ := Nat.nth Nat.Prime n

theorem p_gt_one (n : ℕ) : 1 < p n := by
  unfold p; exact_mod_cast (Nat.prime_nth_prime n).one_lt

/-- The trace of Frobenius at the `n`-th prime, `a = p + 1 - N`. -/
def a (n : ℕ) : ℝ := p n + 1 - D.N n

theorem hasse' (n : ℕ) : D.a n ^ 2 ≤ 4 * p n := D.hasse n

/-- **The step factor** `N_p / p`, the inverse of the local Euler factor of `L(E, s)` at `s = 1`. -/
def fac (n : ℕ) : ℝ := (p n + 1 - D.a n) / p n

/-- **The partial Euler product** `∏_{i < n} N_{p_i} / p_i`, the inverse of the partial L-value at `s = 1`. -/
def P (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, D.fac i

/-- The lower share per step, `(1 - p^{-1/2})²`. -/
def share (n : ℕ) : ℝ := (1 - 1 / Real.sqrt (p n)) ^ 2

/-- The upper factor per step, `(1 + p^{-1/2})²`. -/
def top (n : ℕ) : ℝ := (1 + 1 / Real.sqrt (p n)) ^ 2

theorem fac_bounds (n : ℕ) : share n ≤ D.fac n ∧ D.fac n ≤ top n :=
  factor_bounds (lt_trans one_pos (p_gt_one n)) (D.hasse' n)

theorem share_pos (n : ℕ) : 0 < share n := by
  have h1 : 1 < Real.sqrt (p n) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt (by norm_num) (p_gt_one n)
  have : 1 / Real.sqrt (p n) < 1 := by rw [div_lt_one (by linarith)]; exact h1
  unfold share
  have : 0 < 1 - 1 / Real.sqrt (p n) := by linarith
  positivity

theorem top_pos (n : ℕ) : 0 < top n := by unfold top; positivity

theorem fac_nonneg (n : ℕ) : 0 ≤ D.fac n := (share_pos n).le.trans (D.fac_bounds n).1

theorem P_nonneg (n : ℕ) : 0 ≤ D.P n := Finset.prod_nonneg fun i _ => D.fac_nonneg i

theorem P_succ (n : ℕ) : D.P (n + 1) = D.fac n * D.P n := by
  unfold P; rw [Finset.prod_range_succ, mul_comm]

/-- **The lower ledger**: a margin keeping at least the share `(1 - p^{-1/2})²` per prime. -/
def lower : Margin where
  M := D.P
  f := share
  f_nonneg n := (share_pos n).le
  keeps n := by rw [D.P_succ]; exact mul_le_mul_of_nonneg_right (D.fac_bounds n).1 (D.P_nonneg n)

/-- **The upper ledger**: a chain with floor `0` and cost `-log (1 + p^{-1/2})²` per prime. -/
def upper : Chain 0 where
  M := D.P
  c n := -Real.log (top n)
  M_nonneg := D.P_nonneg
  step n := by
    rw [zero_sub, neg_neg, Real.exp_log (top_pos n), D.P_succ]
    exact mul_le_mul_of_nonneg_right (D.fac_bounds n).2 (D.P_nonneg n)

/-- **No finite stage sees the zero**: every partial Euler product is positive (the API's `Margin.pos`). A zero of
`L(E, s)` at `s = 1` is a property of the whole chain, a rate, not of any step. -/
theorem no_finite_zero (n : ℕ) : 0 < D.P n :=
  D.lower.pos share_pos (by simp [lower, P]) n

/-- **The upper ledger, for free**: `P n ≤ ∏ (1 + p^{-1/2})²` (the API's `Chain.ledger`). -/
theorem P_le (n : ℕ) : D.P n ≤ Real.exp (n * 0 - ∑ i ∈ Finset.range n, -Real.log (top i)) * 1 := by
  have := D.upper.ledger n
  simpa [upper, P] using this

/-- **The balance** of the 1965 form of the conjecture: `∏_{p ≤ p_n} N_p / p ~ C (log p_n)^r` with `C > 0`. -/
def Balance (r : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ Tendsto (fun n => D.P (n + 1) / Real.log (p n) ^ r) atTop (𝓝 C)

end EulerData

/-! ## 3. The problem card: the two counts as the two sides of one balance -/

/-- **The well-defined input**: an elliptic curve over `ℚ`, its conductor `N`, an entire function `Λ` and a root number
`w`, with the classical theorems that make them the curve's L-function as external inputs. -/
structure Input where
  W : WeierstrassCurve ℚ
  [ell : W.IsElliptic]
  N : ℕ
  N_pos : 0 < N
  Λ : ℂ → ℂ
  w : ℂ
  cont : External "modularity (Wiles 1995, Taylor-Wiles 1995, Breuil-Conrad-Diamond-Taylor 2001) with Hecke's theory:
    L(E, s) continues to an entire function" (IsContinuation W Λ)
  fe : External "modularity with Hecke's theory: the completed L-function satisfies xi(2 - s) = w xi(s)"
    (FunctionalEquation N Λ w)
  weak : External "weak Mordell-Weil (Mordell 1922, Weil 1929): E(Q)/2E(Q) is finite; not in Mathlib" (WeakMordellWeil W)

attribute [instance] Input.ell

/-- **What holds without BSD** (Lean from the external inputs): `E(ℚ)` is finitely generated, its torsion is finite, the
order of the zero at `s = 1` does not depend on the continuation, and its parity is the root number. -/
theorem unconditional (i : Input) :
    AddGroup.FG (Pts i.W) ∧ Finite (AddCommGroup.torsion (Pts i.W)) ∧
      (∀ Λ', IsContinuation i.W Λ' → analyticOrderAt Λ' 1 = analyticOrderAt i.Λ 1) ∧
      (∀ n : ℕ, analyticOrderAt i.Λ 1 = n → i.w = (-1) ^ n) :=
  ⟨mordellWeil_of_weak i.W i.weak, torsion_finite i.W, fun _ h => order_welldefined h i.cont,
    fun _ hn => analytic_parity i.N_pos (i.cont.1.analyticAt 1) i.fe hn⟩

/-- **BSD as a problem card.** Open step: the rank of `E(ℚ)` equals the order of the zero of `L(E, s)` at `s = 1`.
Conclusion: the existence line (`E(ℚ)` is infinite exactly when `L(E, 1) = 0`) and the parity of the rank
(`w = (-1)^rank`). -/
def problem : Problem where
  name := "Birch and Swinnerton-Dyer: the zeros follow existence"
  Input := Input
  Open i := OpenStep "BSD: the rank of E(Q) equals the order of the zero of L(E, s) at s = 1" (BSDStatement i.W i.Λ)
  Concl i := (Infinite (Pts i.W) ↔ i.Λ 1 = 0) ∧ i.w = (-1) ^ algRank i.W
  sources := ["modularity (Wiles; Taylor-Wiles; Breuil-Conrad-Diamond-Taylor)", "weak Mordell-Weil (Mordell; Weil)"]
  proved i h := ⟨existence_line i.W (mordellWeil_of_weak i.W i.weak) i.cont.1 h,
    rank_parity i.W i.N_pos i.cont.1 i.fe h⟩

/-- **The low-rank theorem** (Gross-Zagier 1986, Kolyvagin 1988-90, with modularity) in its slot: analytic rank at most
one gives BSD. With it the card's open step is filled for every such curve. -/
def LowRank (i : Input) : Prop :=
  External "Gross-Zagier 1986, Kolyvagin 1988-90, with modularity: analytic rank 0 or 1 implies rank = analytic rank"
    (analyticOrderAt i.Λ 1 ≤ 1 → BSDStatement i.W i.Λ)

theorem open_of_lowRank (i : Input) (hGZK : LowRank i) (h : analyticOrderAt i.Λ 1 ≤ 1) : problem.Open i := hGZK h

/-! ## 4. The ledger form of the open step -/

/-- **The input of the ledger card**: a curve, its continuation, its prime data, and Goldfeld's theorem as the external
input (true when the prime data are the curve's). -/
structure LedgerInput where
  W : WeierstrassCurve ℚ
  Λ : ℂ → ℂ
  D : EulerData
  goldfeld : External "Goldfeld 1982: if the partial Euler products at s = 1 of the curve grow like C (log x)^r, then
    L(E, s) has a zero of order r at s = 1 (and satisfies RH)" (∀ r : ℕ, D.Balance r → analyticOrderAt Λ 1 = r)

/-- **The 1965 form as the open step.** Open step: the partial Euler products grow like `C (log x)^rank`; conclusion:
BSD. The ledger form is the stronger statement (it also gives RH for `L(E, s)`, by Goldfeld). -/
def ledgerCard : Problem where
  name := "Birch and Swinnerton-Dyer, 1965 form: the Euler ledger grows like (log x)^rank"
  Input := LedgerInput
  Open i := OpenStep "the partial products of N_p/p grow like C (log p)^rank" (i.D.Balance (algRank i.W))
  Concl i := BSDStatement i.W i.Λ
  sources := ["Goldfeld 1982"]
  proved i h := (i.goldfeld _ h).symm

/-! ## 5. The slot is not empty: `y² = x³ - x` (conductor 32, rank 0) -/

/-- **The curve `y² = x³ - x`** over `ℚ` (Cremona 32a2; complex multiplication by `i`; Fermat's congruent-number
curve for `n = 1`). -/
def E32 : WeierstrassCurve ℚ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 0 }

theorem E32_Δ : E32.Δ = 64 := by
  simp [E32, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

instance : E32.IsElliptic := ⟨isUnit_iff_ne_zero.2 (by rw [E32_Δ]; norm_num)⟩

/-- The three points of order two, `(0, 0)`, `(1, 0)`, `(-1, 0)`, are on the curve. -/
theorem E32_points : E32.toAffine.Equation 0 0 ∧ E32.toAffine.Equation 1 0 ∧ E32.toAffine.Equation (-1) 0 := by
  simp only [WeierstrassCurve.Affine.equation_iff, E32]
  norm_num

/-- The integral model of the same curve. -/
def E32Z : WeierstrassCurve ℤ := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 0 }

theorem E32Z_Δ : E32Z.Δ = 64 := by
  simp [E32Z, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- **The computed count is Mathlib's** at every odd prime (good reduction away from 2). -/
theorem count_E32 (p : ℕ) [hp : Fact p.Prime] (h2 : p ≠ 2) :
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    Nat.card (Pts (E32Z.map (Int.castRingHom (ZMod p)))) = countZ 0 0 0 (-1) 0 p := by
  have hΔ : ((E32Z.Δ : ℤ) : ZMod p) ≠ 0 := by
    rw [E32Z_Δ, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    have hd' : p ∣ 2 ^ 6 := by exact_mod_cast hd
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow hd'))
  exact count_correct E32Z p hΔ

/- The counts run: `a_p` at the odd primes below 40 (zero at `p ≡ 3 mod 4`, complex multiplication), and the Hasse
check `a_p² ≤ 4p` at every odd prime below 100. -/
#eval [apZ 0 0 0 (-1) 0 3, apZ 0 0 0 (-1) 0 5, apZ 0 0 0 (-1) 0 7, apZ 0 0 0 (-1) 0 11, apZ 0 0 0 (-1) 0 13,
  apZ 0 0 0 (-1) 0 17, apZ 0 0 0 (-1) 0 19, apZ 0 0 0 (-1) 0 23, apZ 0 0 0 (-1) 0 29, apZ 0 0 0 (-1) 0 31,
  apZ 0 0 0 (-1) 0 37]
#guard apZ 0 0 0 (-1) 0 5 = -2
#guard apZ 0 0 0 (-1) 0 7 = 0
#guard [hasseZ 0 0 0 (-1) 0 3, hasseZ 0 0 0 (-1) 0 5, hasseZ 0 0 0 (-1) 0 7, hasseZ 0 0 0 (-1) 0 11,
  hasseZ 0 0 0 (-1) 0 13, hasseZ 0 0 0 (-1) 0 17, hasseZ 0 0 0 (-1) 0 19, hasseZ 0 0 0 (-1) 0 23,
  hasseZ 0 0 0 (-1) 0 29, hasseZ 0 0 0 (-1) 0 31, hasseZ 0 0 0 (-1) 0 37, hasseZ 0 0 0 (-1) 0 41,
  hasseZ 0 0 0 (-1) 0 43, hasseZ 0 0 0 (-1) 0 47, hasseZ 0 0 0 (-1) 0 53, hasseZ 0 0 0 (-1) 0 59,
  hasseZ 0 0 0 (-1) 0 61, hasseZ 0 0 0 (-1) 0 67, hasseZ 0 0 0 (-1) 0 71, hasseZ 0 0 0 (-1) 0 73,
  hasseZ 0 0 0 (-1) 0 79, hasseZ 0 0 0 (-1) 0 83, hasseZ 0 0 0 (-1) 0 89, hasseZ 0 0 0 (-1) 0 97].all id

/-- **Hasse at `p = 5`, proved by the kernel**: `a_5 = -2` and `|a_5| ≤ 2 √5`. -/
theorem hasse_E32_five : |(apZ 0 0 0 (-1) 0 5 : ℝ)| ≤ 2 * Real.sqrt 5 := by
  have := (hasseZ_iff 0 0 0 (-1) 0 5).1 (by decide)
  exact_mod_cast this

/-- **The known values of `y² = x³ - x`, as external inputs.** -/
structure Data32 where
  Λ : ℂ → ℂ
  w : ℂ
  cont : External "Deuring 1953-56 (complex multiplication: a Hecke L-function), or modularity: continuation"
    (IsContinuation E32 Λ)
  fe : External "Deuring / Hecke: functional equation of the completed L-function, conductor 32" (FunctionalEquation 32 Λ w)
  nonvanish : External "L(E, 1) = 0.6555... is not 0 (modular symbols: L(E, 1)/Omega is the rational 1/4)" (Λ 1 ≠ 0)
  finite : External "Fermat: 1 is not a congruent number (descent); E(Q) = {O, (0, 0), (1, 0), (-1, 0)}"
    (Finite (Pts E32))

/-- The card's input for `y² = x³ - x`: weak Mordell-Weil follows from the finiteness of `E(ℚ)`. -/
def input32 (d : Data32) : Input where
  W := E32
  N := 32
  N_pos := by norm_num
  Λ := d.Λ
  w := d.w
  cont := d.cont
  fe := d.fe
  weak := by have := d.finite; exact AddSubgroup.finiteIndex_of_finite

/-- **BSD for `y² = x³ - x`** from its known values: rank 0 and order 0. -/
theorem bsd_E32 (d : Data32) : BSDStatement E32 d.Λ := by
  have := d.finite
  have hfg : AddGroup.FG (Pts E32) := AddGroup.fg_of_finite
  have hr : algRank E32 = 0 := (algRank_eq_zero_iff E32 hfg).2 d.finite
  have ho : analyticOrderAt d.Λ 1 = 0 := analyticOrderAt_eq_zero.2 (Or.inr d.nonvanish)
  unfold BSDStatement
  rw [hr, ho]
  rfl

/-- **The card, read for `y² = x³ - x`**: its open step is filled, so its conclusion holds; in particular the root
number is `+1`. -/
theorem card_E32 (d : Data32) : problem.Open (input32 d) ∧ (Infinite (Pts E32) ↔ d.Λ 1 = 0) ∧ d.w = 1 := by
  have h := bsd_E32 d
  have hc := problem.holds (input32 d) h
  have := d.finite
  have hr : algRank E32 = 0 := (algRank_eq_zero_iff E32 AddGroup.fg_of_finite).2 d.finite
  refine ⟨h, hc.1, ?_⟩
  have := hc.2
  simp only [input32] at this
  rw [this, hr, pow_zero]

end ProofPhase.API.BSD
