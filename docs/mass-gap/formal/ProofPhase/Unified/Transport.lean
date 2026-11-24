/-
The transport theorem: an uncertainty, defined exactly, carried across a chain of DBs (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/TRANSPORT.md`, sections 1 and 2.
-/

import ProofPhase.ETM.RunSys

/-!
# Transport of an uncertainty across a chain of boundaries

**The approach** (the owner, 2026-11-23): "Exactly define the uncertainty, then transport it in a meaningful way across a
DB." Here an uncertainty is a carried quantity: an error bound `e n ≥ 0` on the state at step `n`. A step with factor
`f n` and floor `δ` transports it by

  `e (n + 1) ≤ e^δ · f n · e n + r n`,

where `r n ≥ 0` is the **fresh** uncertainty that the step itself adds. With `r = 0` this is the ledger law (`Pays`,
`Carries`, `ETM.Ledger`).

**Theorems.**
* `transport_cert`, `acc_eq`, `acc_const`: the closed form (variation of constants). The transported bound is
  `(∏ a) e₀ + Σ_j (∏_{j < i < n} a i) r j`, with `a i = e^δ f i`.
* `transportsCert_zero_iff`, `carry_of_transport`, `pays_iff_transports`, `ETM.Ledger.transports`,
  `contract_of_transport`: **the ledger is the case `r = 0`** (`Carries`, `carry`, `Pays`, `Ledger.contract`).
* **(a) bounded transport** (`transport_geom`, `bounded_transport`): with `f n ≤ θ` and `q = e^δ θ < 1`, and fresh
  uncertainty at most `R`, `e n ≤ q^n e 0 + R / (1 − q) ≤ e 0 + R / (1 − q)` for every `n`.
* **(b) the critical case** (`critical_transport`): at cost = floor (`e^δ f n = 1`) the uncertainty is carried without
  damping, `e n ≤ e 0 + Σ_{j<n} r j`. **Sharp** (`critical_sharp`: the chain `e₀ + Σ r` is a critical transport and
  attains the bound); a uniform bound exists exactly when `Σ r` converges (`critical_bounded_iff`); a constant fresh
  uncertainty is unbounded (`critical_unbounded`), while the same fresh uncertainty under contraction stays bounded (a).
* **(c) sign preservation** (`sign_transport`, `sign_of_bounded`, `sign_of_critical`): a quantity `M` with sign margin
  `m n ≤ M n`, and a quantity `N` across the DB with `|N n − M n| ≤ e n < m n`: then `N n ≥ m n − e n > 0` at every
  step.
* **Relative to a margin, transport is critical** (`relative_transport`, `relative_critical`): if the uncertainty and
  the margin `E` are carried with the same factor `s n`, the ratio `e / E` is transported at exactly cost = floor, with
  fresh uncertainty `r n / E (n + 1)`. This is the exact sense of "zero slack".

No problem-specific object occurs here. Standard axioms only; nothing is assumed.
-/

open Finset

noncomputable section

namespace ProofPhase.Unified

/-! ### 1. Transport of a certificate with fresh uncertainty -/

/-- **Transport with fresh uncertainty.** Each step `i < n` carries every certified value `e` to the certified value
`a i * e + r i`: the step's factor times the old value, plus the fresh uncertainty the step adds. -/
def TransportsCert (Cert : ℕ → ℝ → Prop) (a r : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i < n, ∀ e, Cert i e → Cert (i + 1) (a i * e + r i)

/-- The transported value: `acc 0 = e₀`, `acc (n + 1) = a n · acc n + r n`. -/
def acc (a r : ℕ → ℝ) (e₀ : ℝ) : ℕ → ℝ
  | 0 => e₀
  | n + 1 => a n * acc a r e₀ n + r n

/-- **The transport theorem, certificate form.** A certificate at the start is carried to the transported value. -/
theorem transport_cert {Cert : ℕ → ℝ → Prop} {a r : ℕ → ℝ} {n : ℕ} (h : TransportsCert Cert a r n) {e₀ : ℝ}
    (h0 : Cert 0 e₀) : Cert n (acc a r e₀ n) := by
  induction n with
  | zero => exact h0
  | succ n ih => exact h n (Nat.lt_succ_self n) _ (ih fun i hi => h i (Nat.lt_succ_of_lt hi))

/-- **The closed form** (variation of constants): `acc n = (∏_{i<n} a i) e₀ + Σ_{j<n} (∏_{j<i<n} a i) r j`. -/
theorem acc_eq (a r : ℕ → ℝ) (e₀ : ℝ) (n : ℕ) :
    acc a r e₀ n = (∏ i ∈ range n, a i) * e₀ + ∑ j ∈ range n, (∏ i ∈ Ico (j + 1) n, a i) * r j := by
  induction n with
  | zero => simp [acc]
  | succ n ih =>
    have hs : ∀ j ∈ range n, a n * ((∏ i ∈ Ico (j + 1) n, a i) * r j) = (∏ i ∈ Ico (j + 1) (n + 1), a i) * r j := by
      intro j hj
      rw [prod_Ico_succ_top (Nat.succ_le_of_lt (mem_range.1 hj))]
      ring
    rw [acc, ih, prod_range_succ, sum_range_succ, Ico_self, prod_empty, one_mul, mul_add, mul_sum,
      sum_congr rfl hs]
    ring

/-- **Constant factor**: `acc n = q^n e₀ + Σ_{j<n} q^{n-1-j} r j`. -/
theorem acc_const (q : ℝ) (r : ℕ → ℝ) (e₀ : ℝ) (n : ℕ) :
    acc (fun _ => q) r e₀ n = q ^ n * e₀ + ∑ j ∈ range n, q ^ (n - 1 - j) * r j := by
  induction n with
  | zero => simp [acc]
  | succ n ih =>
    have hs : ∀ j ∈ range n, q * (q ^ (n - 1 - j) * r j) = q ^ (n + 1 - 1 - j) * r j := by
      intro j hj
      have hj := mem_range.1 hj
      rw [show n + 1 - 1 - j = (n - 1 - j) + 1 by omega, pow_succ]
      ring
    show q * acc (fun _ => q) r e₀ n + r n = _
    rw [ih, sum_range_succ, mul_add, mul_sum, sum_congr rfl hs, show n + 1 - 1 - n = 0 by omega, pow_zero,
      one_mul, pow_succ]
    ring

/-- With nonnegative factors, fresh uncertainties and start, the transported value is nonnegative. -/
theorem acc_nonneg {a r : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hr : ∀ i, 0 ≤ r i) {e₀ : ℝ} (he : 0 ≤ e₀) (n : ℕ) :
    0 ≤ acc a r e₀ n := by
  induction n with
  | zero => exact he
  | succ n ih => exact add_nonneg (mul_nonneg (ha n) ih) (hr n)

/-- Larger factors transport to a larger value. -/
theorem acc_mono {a b r : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hab : ∀ i, a i ≤ b i) (hr : ∀ i, 0 ≤ r i) {e₀ : ℝ}
    (he : 0 ≤ e₀) (n : ℕ) : acc a r e₀ n ≤ acc b r e₀ n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    show a n * acc a r e₀ n + r n ≤ b n * acc b r e₀ n + r n
    have := mul_le_mul (hab n) ih (acc_nonneg ha hr he n) ((ha n).trans (hab n))
    linarith

/-! ### 2. The ledger is the case `r = 0` -/

/-- **`Carries` is transport without fresh uncertainty.** -/
theorem transportsCert_zero_iff {Cert : ℕ → ℝ → Prop} {a : ℕ → ℝ} {n : ℕ} :
    TransportsCert Cert a (fun _ => 0) n ↔ Carries Cert a n := by
  simp only [TransportsCert, Carries, add_zero]

/-- Without fresh uncertainty the transported value is the product of the factors times the start. -/
theorem acc_zero_r (a : ℕ → ℝ) (e₀ : ℝ) (n : ℕ) : acc a (fun _ => 0) e₀ n = (∏ i ∈ range n, a i) * e₀ := by
  rw [acc_eq]; simp

/-- **`carry` is the transport theorem at `r = 0`.** -/
theorem carry_of_transport {Cert : ℕ → ℝ → Prop} {a : ℕ → ℝ} {n : ℕ} (h : Carries Cert a n) {e₀ : ℝ}
    (h0 : Cert 0 e₀) : Cert n ((∏ i ∈ range n, a i) * e₀) := by
  rw [← acc_zero_r]
  exact transport_cert (transportsCert_zero_iff.2 h) h0

/-- **An uncertainty `e` transported along a chain**: `e (i + 1) ≤ e^δ · f i · e i + r i` for `i < n`. -/
def Transports (e f r : ℕ → ℝ) (δ : ℝ) (n : ℕ) : Prop :=
  ∀ i < n, e (i + 1) ≤ Real.exp δ * f i * e i + r i

/-- **`Pays` is transport without fresh uncertainty**, with the factor `e^{-c}`. -/
theorem pays_iff_transports {M c : ℕ → ℝ} {δ : ℝ} {n : ℕ} :
    Pays M c δ n ↔ Transports M (fun i => Real.exp (-c i)) (fun _ => 0) δ n := by
  have h : ∀ i, Real.exp δ * Real.exp (-c i) * M i + 0 = Real.exp (δ - c i) * M i := fun i => by
    rw [add_zero, ← Real.exp_add, ← sub_eq_add_neg]
  simp only [Pays, Transports, h]

/-- A transported uncertainty with nonnegative factors is a transported certificate (`Cert i x := e i ≤ x`). -/
theorem transportsCert_of_transports {e f r : ℕ → ℝ} {δ : ℝ} {n : ℕ} (h : Transports e f r δ n)
    (hf : ∀ i < n, 0 ≤ f i) : TransportsCert (fun i x => e i ≤ x) (fun i => Real.exp δ * f i) r n :=
  fun i hi x hx => (h i hi).trans (by
    have := mul_le_mul_of_nonneg_left hx (mul_nonneg (Real.exp_pos δ).le (hf i hi))
    linarith)

/-- **The transport theorem.** `e n` is at most the transported value of `e 0`. -/
theorem transport {e f r : ℕ → ℝ} {δ : ℝ} {n : ℕ} (h : Transports e f r δ n) (hf : ∀ i < n, 0 ≤ f i) :
    e n ≤ acc (fun i => Real.exp δ * f i) r (e 0) n :=
  transport_cert (transportsCert_of_transports h hf) (le_refl _)

/-- **A DMP ledger is a transport with `r = 0`** (`ETM/RunSys.lean`). -/
theorem _root_.ProofPhase.ETM.Ledger.transports {δ : ℝ} (L : ProofPhase.ETM.Ledger δ) (n : ℕ) :
    Transports L.m L.f (fun _ => 0) δ n := fun i _ => by
  rw [add_zero]; exact L.pays i

/-! ### 3. (a) Bounded transport -/

/-- **Geometric transport**: with factors in `[0, θ]`, `e n ≤ q^n e 0 + Σ_{j<n} q^{n-1-j} r j`, `q = e^δ θ`. -/
theorem transport_geom {e f r : ℕ → ℝ} {δ θ : ℝ} {n : ℕ} (h : Transports e f r δ n) (hf0 : ∀ i, 0 ≤ f i)
    (hfθ : ∀ i, f i ≤ θ) (hr : ∀ i, 0 ≤ r i) (he0 : 0 ≤ e 0) :
    e n ≤ (Real.exp δ * θ) ^ n * e 0 + ∑ j ∈ range n, (Real.exp δ * θ) ^ (n - 1 - j) * r j := by
  rw [← acc_const]
  exact (transport h fun i _ => hf0 i).trans (acc_mono (fun i => mul_nonneg (Real.exp_pos δ).le (hf0 i))
    (fun i => mul_le_mul_of_nonneg_left (hfθ i) (Real.exp_pos δ).le) hr he0 n)

/-- **`Ledger.contract` is (a) at `r = 0`**: a ledger with factors at most `θ` has `m n ≤ (e^δ θ)^n m 0`. -/
theorem contract_of_transport {δ θ : ℝ} (L : ProofPhase.ETM.Ledger δ) (hθ : ∀ n, L.f n ≤ θ) (n : ℕ) :
    L.m n ≤ (Real.exp δ * θ) ^ n * L.m 0 := by
  have := transport_geom (L.transports n) L.f_nonneg hθ (fun _ => le_refl 0) (L.m_nonneg 0)
  simpa using this

/-- The geometric tail with fresh uncertainty at most `R` is at most `R / (1 − q)`, for every `n`. -/
theorem geom_tail_le {q R : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hR0 : 0 ≤ R) {r : ℕ → ℝ} (hrR : ∀ j, r j ≤ R) (n : ℕ) :
    ∑ j ∈ range n, q ^ (n - 1 - j) * r j ≤ R / (1 - q) := by
  have h1 : ∑ j ∈ range n, q ^ (n - 1 - j) * r j ≤ ∑ j ∈ range n, q ^ (n - 1 - j) * R :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hrR j) (pow_nonneg hq0 _)
  have h2 : ∑ j ∈ range n, q ^ (n - 1 - j) * R = (∑ j ∈ range n, q ^ j) * R := by
    rw [sum_mul]; exact sum_range_reflect (fun j => q ^ j * R) n
  have h3 : (∑ j ∈ range n, q ^ j) * (1 - q) = 1 - q ^ n := geom_sum_mul_neg q n
  have hpos : 0 < 1 - q := by linarith
  have h4 : (∑ j ∈ range n, q ^ j) * R ≤ R / (1 - q) := by
    rw [le_div_iff₀ hpos]
    have h5 : (∑ j ∈ range n, q ^ j) * R * (1 - q) = (1 - q ^ n) * R := by rw [← h3]; ring
    rw [h5]
    nlinarith [pow_nonneg hq0 n]
  linarith

/-- **(a) Bounded transport.** Factors in `[0, θ]` with `q = e^δ θ < 1`, fresh uncertainty in `[0, R]`, start
`e 0 ≥ 0`: for every `n`, `e n ≤ q^n e 0 + R / (1 − q)`, and so `e n ≤ e 0 + R / (1 − q)`, uniformly in `n`. -/
theorem bounded_transport {e f r : ℕ → ℝ} {δ θ R : ℝ} {n : ℕ} (h : Transports e f r δ n) (hf0 : ∀ i, 0 ≤ f i)
    (hfθ : ∀ i, f i ≤ θ) (hq : Real.exp δ * θ < 1) (hr : ∀ i, 0 ≤ r i) (hR : ∀ i, r i ≤ R) (he0 : 0 ≤ e 0) :
    e n ≤ (Real.exp δ * θ) ^ n * e 0 + R / (1 - Real.exp δ * θ) ∧
      e n ≤ e 0 + R / (1 - Real.exp δ * θ) := by
  have hθ : 0 ≤ θ := (hf0 0).trans (hfθ 0)
  have hq0 : 0 ≤ Real.exp δ * θ := mul_nonneg (Real.exp_pos δ).le hθ
  have hR0 : 0 ≤ R := (hr 0).trans (hR 0)
  have h1 := transport_geom h hf0 hfθ hr he0
  have h2 := geom_tail_le hq0 hq hR0 hR n
  have h3 : (Real.exp δ * θ) ^ n * e 0 ≤ e 0 := mul_le_of_le_one_left he0 (pow_le_one₀ hq0 hq.le)
  exact ⟨by linarith, by linarith⟩

/-- **Accumulated form**: with `q ≤ 1` the tail is at most the plain sum of the fresh uncertainties. -/
theorem geom_tail_le_sum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {r : ℕ → ℝ} (hr : ∀ i, 0 ≤ r i) (n : ℕ) :
    ∑ j ∈ range n, q ^ (n - 1 - j) * r j ≤ ∑ j ∈ range n, r j :=
  sum_le_sum fun j _ => mul_le_of_le_one_left (hr j) (pow_le_one₀ hq0 hq1)

/-! ### 4. (b) The critical case: cost = floor -/

/-- **(b) Critical transport.** At cost = floor, `e^δ f i = 1`, the uncertainty is carried without damping:
`e n ≤ e 0 + Σ_{j<n} r j`. No sign condition is needed. -/
theorem critical_transport {e f r : ℕ → ℝ} {δ : ℝ} {n : ℕ} (h : Transports e f r δ n)
    (hcrit : ∀ i < n, Real.exp δ * f i = 1) : e n ≤ e 0 + ∑ j ∈ range n, r j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := h n (Nat.lt_succ_self n)
    rw [hcrit n (Nat.lt_succ_self n), one_mul] at h1
    have h2 := ih (fun i hi => h i (Nat.lt_succ_of_lt hi)) (fun i hi => hcrit i (Nat.lt_succ_of_lt hi))
    rw [sum_range_succ]
    linarith

/-- The critical chain: the start plus the accumulated fresh uncertainty. -/
def critAcc (e₀ : ℝ) (r : ℕ → ℝ) (n : ℕ) : ℝ := e₀ + ∑ j ∈ range n, r j

/-- **(b) is sharp.** The critical chain is a transport at cost = floor (factor `e^{-δ}`, so `e^δ f = 1`) and it
attains the bound of `critical_transport` with equality at every step. -/
theorem critical_sharp (e₀ δ : ℝ) (r : ℕ → ℝ) (n : ℕ) :
    Transports (critAcc e₀ r) (fun _ => Real.exp (-δ)) r δ n ∧ Real.exp δ * Real.exp (-δ) = 1 ∧
      critAcc e₀ r n = critAcc e₀ r 0 + ∑ j ∈ range n, r j := by
  have hc : Real.exp δ * Real.exp (-δ) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  refine ⟨fun i _ => ?_, hc, by simp [critAcc]⟩
  rw [hc, one_mul]
  simp only [critAcc, sum_range_succ]
  linarith

/-- **At cost = floor a uniform bound exists exactly when the fresh uncertainty is summable.** -/
theorem critical_bounded_iff {e₀ : ℝ} {r : ℕ → ℝ} (hr : ∀ i, 0 ≤ r i) :
    (∃ C, ∀ n, critAcc e₀ r n ≤ C) ↔ Summable r := by
  constructor
  · rintro ⟨C, hC⟩
    exact summable_of_sum_range_le (c := C - e₀) hr (fun n => by have := hC n; simp only [critAcc] at this; linarith)
  · intro hs
    exact ⟨e₀ + ∑' i, r i, fun n => by
      simp only [critAcc]; linarith [hs.sum_le_tsum (range n) (fun i _ => hr i)]⟩

/-- **A constant fresh uncertainty is not bounded at cost = floor.** (Under contraction the same fresh uncertainty
stays below `ρ / (1 − q)`, `bounded_transport`.) -/
theorem critical_unbounded {e₀ ρ : ℝ} (hρ : 0 < ρ) (C : ℝ) : ∃ n, C < critAcc e₀ (fun _ => ρ) n := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - e₀) / ρ)
  refine ⟨n, ?_⟩
  simp only [critAcc, sum_const, card_range, nsmul_eq_mul]
  rw [div_lt_iff₀ hρ] at hn
  linarith

/-! ### 5. (c) Sign preservation across the DB -/

/-- **(c) Sign preservation.** `M` has a sign margin `m n ≤ M n`; the quantity `N` across the DB differs from it by at
most the uncertainty, `|N n − M n| ≤ e n`; the uncertainty stays below the margin, `e n < m n`. Then the sign is
certified at every step: `N n ≥ m n − e n > 0`. -/
theorem sign_transport {M N m e : ℕ → ℝ} (hm : ∀ n, m n ≤ M n) (he : ∀ n, |N n - M n| ≤ e n)
    (hlt : ∀ n, e n < m n) (n : ℕ) : 0 < m n - e n ∧ m n - e n ≤ N n := by
  have := (abs_le.1 (he n)).1
  constructor <;> linarith [hm n, hlt n]

/-- **(a) + (c)**: a contracting transport of the uncertainty certifies the sign at every step as soon as the uniform
bound `e 0 + R / (1 − q)` is below a uniform margin `μ`. -/
theorem sign_of_bounded {M N m e f r : ℕ → ℝ} {δ θ R μ : ℝ} (hm : ∀ n, m n ≤ M n) (hμ : ∀ n, μ ≤ m n)
    (he : ∀ n, |N n - M n| ≤ e n) (h : ∀ n, Transports e f r δ n) (hf0 : ∀ i, 0 ≤ f i) (hfθ : ∀ i, f i ≤ θ)
    (hq : Real.exp δ * θ < 1) (hr : ∀ i, 0 ≤ r i) (hR : ∀ i, r i ≤ R) (he0 : 0 ≤ e 0)
    (hbound : e 0 + R / (1 - Real.exp δ * θ) < μ) (n : ℕ) : 0 < N n := by
  have hlt : ∀ n, e n < m n := fun n =>
    ((bounded_transport (h n) hf0 hfθ hq hr hR he0).2.trans_lt hbound).trans_le (hμ n)
  have := sign_transport hm he hlt n
  linarith [this.1, this.2]

/-- **(b) + (c)**: at cost = floor the sign is certified at every step when the start plus the total fresh
uncertainty stays below the margin. -/
theorem sign_of_critical {M N m e f r : ℕ → ℝ} {δ : ℝ} (hm : ∀ n, m n ≤ M n) (he : ∀ n, |N n - M n| ≤ e n)
    (h : ∀ n, Transports e f r δ n) (hcrit : ∀ i, Real.exp δ * f i = 1)
    (hbound : ∀ n, e 0 + ∑ j ∈ range n, r j < m n) (n : ℕ) : 0 < N n := by
  have hlt : ∀ n, e n < m n := fun n => (critical_transport (h n) fun i _ => hcrit i).trans_lt (hbound n)
  have := sign_transport hm he hlt n
  linarith [this.1, this.2]

/-! ### 6. Relative to a margin, transport is critical (zero slack) -/

/-- **Relative transport.** If the uncertainty is carried with the factor `s i` and the margin `E > 0` is carried with
the same factor, `E (i + 1) = s i · E i`, then the relative uncertainty `e / E` is transported at **exactly cost =
floor** (floor `0`, factor `1`), with fresh uncertainty `r i / E (i + 1)`. -/
theorem relative_transport {e s r E : ℕ → ℝ} (h : ∀ i, e (i + 1) ≤ s i * e i + r i)
    (hE : ∀ i, E (i + 1) = s i * E i) (hpos : ∀ i, 0 < E i) (n : ℕ) :
    Transports (fun i => e i / E i) (fun _ => 1) (fun i => r i / E (i + 1)) 0 n := fun i _ => by
  have hs : 0 < s i := by
    have h1 := hpos (i + 1); rw [hE i] at h1; exact pos_of_mul_pos_left h1 (hpos i).le
  show e (i + 1) / E (i + 1) ≤ Real.exp 0 * 1 * (e i / E i) + r i / E (i + 1)
  rw [Real.exp_zero, one_mul, one_mul, ← mul_div_mul_left (e i) (E i) hs.ne', ← hE i, ← add_div]
  exact div_le_div_of_nonneg_right (h i) (hpos _).le

/-- **Zero slack, accumulated**: the relative uncertainty is at most its start plus the sum of the fresh relative
uncertainties, `e n / E n ≤ e 0 / E 0 + Σ_{j<n} r j / E (j + 1)`. -/
theorem relative_critical {e s r E : ℕ → ℝ} (h : ∀ i, e (i + 1) ≤ s i * e i + r i)
    (hE : ∀ i, E (i + 1) = s i * E i) (hpos : ∀ i, 0 < E i) (n : ℕ) :
    e n / E n ≤ e 0 / E 0 + ∑ j ∈ range n, r j / E (j + 1) :=
  critical_transport (relative_transport h hE hpos n) fun _ _ => by rw [Real.exp_zero, one_mul]

end ProofPhase.Unified
