/-
The transport theorem, part 2: the three bridges in transport form (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/TRANSPORT.md`, section 3.
-/

import ProofPhase.Unified.Transport
import ProofPhase.Unified.JoinLossSlab
import ProofPhase.Proof.LiftingNP

/-!
# The three bridges, each as an uncertainty transported across its DB

Each column's one named bridge is stated as: *this uncertainty, defined exactly, is transported across this DB with these
factors, and stays below this margin.* What is proved here is the transport and the certification; the open step of each
column is a named hypothesis or a hypothesis of a theorem, never a conclusion.

**Yang-Mills** (the slab chain, `JoinLossSlab.lean`).
* The uncertainty: `twistCert Ω K u`, the **boundary uncertainty** of a slab: at every end-face outside, the charged
  sector is at most `u` times the neutral one. O1 in sector form at `μ` is the margin `u ≤ 1/μ` (`ym_O1_of_cert`).
* `ym_slab_transport` (Lean): in the slab geometry the chain transports it with the factors of the layers and **no fresh
  uncertainty** (`r = 0`, zero join loss, from `elec_submul`).
* `SeamTransport` (named, **open** in the box geometry): the same with a fresh uncertainty `σ i` per join, the cost of the
  side seam. `ym_bridge` (Lean): under it, with factor `θ < 1`, O1 at `μ` holds once `μ (θ^n u₀ + σ / (1 − θ)) ≤ 1`.
* `elecDeficit c = (√2 − 1) − c`, the electric-side deficit of a slab with pointwise twist ratio `c`. Deficit `≤ 0` gives
  factor `≤ √2 − 1` (`elec_le_of_deficit`, the input of `three_slabs_O1`). A positive deficit with `c > 0` only costs
  layers (`ym_layers_needed`, Lean). **Open:** a ratio `c > 0` uniform in the lattice spacing at fixed physical layer
  length.

**GRH** (the scale chain, Szego factors `1 − |k|^2`).
* The margins: zeta's `E` and the finite model's `Ê` are carried by their Szego factors, `E (n + 1) = s n · E n`,
  `Ê (n + 1) = ŝ n · Ê n`. The explicit formula's remainder enters at scale `n` as the relative difference of the two
  factors, `relRem s ŝ n = |s n − ŝ n| / ŝ n`. The uncertainty is `relUnc E Ê n = |E n − Ê n| / Ê n`.
* `grh_abs_step` (Lean): `|E − Ê|` is transported with the model's factor `ŝ n` and fresh uncertainty
  `|s n − ŝ n| |E n|`. `grh_log_transport` (Lean): `log (1 + relUnc)` is transported at **exactly cost = floor**
  (zero slack), with fresh uncertainty `log (1 + relRem)`.
* `grh_sign`, `grh_sign_of_sum`, `grh_sign_szego` (Lean): zeta's margin is positive, with `E n ≥ (1 − relUnc) Ê n`, as
  long as the accumulated remainder stays below `log 2`. `grh_sign_step` (Lean): the sign alone is decided step by step,
  `relRem n < 1`. **Open:** the size of `relRem` from the primes alone (beyond Dirichlet); see the paper.

**NP** (the two-party split, lifting).
* `hiddenQuantum G`: the hidden information per variable, Alice's pointer bits in nats (`log m` for Index,
  `indGadget_quantum`).
* `HiddenTransport R q W`: every refutation's line count is carried across `W` hidden variables, each crossing keeping at
  most `e^{-q}` of it, with one line left (transport with `r = 0`). `hiddenTransport_iff_size` (Lean): this is exactly the
  size bound `e^{W q} ≤ |P|`.
* `liftCP_hiddenTransport` (Lean, from the named external `LiftCP`): `q = c log n` per hidden variable.
  `liftCPConst_hiddenTransport` (Lean, from the named **open** `LiftCPConst`): `q = c`, a constant cost above the floor
  (`costAboveFloor_const_iff`).
* `hiding_accumulates` (Lean): per-block hiding errors `ε` across `n` blocks add up at cost = floor, `n ε`, unbounded.

Standard axioms only. Nothing here proves O1, GRH beyond Dirichlet, or a crossing cost for strong systems.
-/

open Finset

noncomputable section

namespace ProofPhase.Unified

/-! ### 1. Yang-Mills: the boundary uncertainty through the slab chain -/

section YM

variable {X : Type*} [Fintype X] {Ω : X → X}

/-- **The boundary uncertainty of a slab** (exact): at every end-face outside the charged sector is at most `u` times
the neutral sector. The least such `u` is the boundary-uniform electric factor. -/
def twistCert (Ω : X → X) (K : X → X → ℝ) (u : ℝ) : Prop := ∀ x y, |sec1 Ω K x y| ≤ u * sec0 Ω K x y

/-- **The electric-side deficit** of a slab with pointwise twist ratio `c`: how far `c` is below `√2 − 1`. -/
def elecDeficit (c : ℝ) : ℝ := (√2 - 1) - c

omit [Fintype X] in
/-- A boundary uncertainty may be raised (nonnegative kernel). -/
theorem twistCert_mono {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y) {u v : ℝ} (h : twistCert Ω K u) (huv : u ≤ v) :
    twistCert Ω K v :=
  fun x y => (h x y).trans (mul_le_mul_of_nonneg_right huv (sec0_nonneg hK x y))

/-- A chain of nonnegative layers is nonnegative. -/
theorem kchain_nonneg {T : ℕ → X → X → ℝ} (hT : ∀ n x y, 0 ≤ T n x y) (n : ℕ) (x y : X) : 0 ≤ kchain T n x y := by
  induction n generalizing x y with
  | zero => exact hT 0 x y
  | succ n ih =>
    show 0 ≤ ∑ z, kchain T n x z * T (n + 1) z y
    exact sum_nonneg fun z _ => mul_nonneg (ih x z) (hT (n + 1) z y)

omit [Fintype X] in
/-- **(c) for Yang-Mills: the margin is `1/μ`.** A boundary uncertainty `u` with `μ u ≤ 1` is O1 in sector form,
`μ |Z_{e=1}| ≤ Z_{e=0}` at every end-face outside. -/
theorem ym_O1_of_cert {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y) {u μ : ℝ} (h : twistCert Ω K u) (hμ0 : 0 ≤ μ)
    (hu : μ * u ≤ 1) (x y : X) : μ * |sec1 Ω K x y| ≤ sec0 Ω K x y := by
  have h0 := sec0_nonneg (Ω := Ω) hK x y
  calc μ * |sec1 Ω K x y| ≤ μ * (u * sec0 Ω K x y) := mul_le_mul_of_nonneg_left (h x y) hμ0
    _ = (μ * u) * sec0 Ω K x y := by ring
    _ ≤ 1 * sec0 Ω K x y := mul_le_mul_of_nonneg_right hu h0
    _ = _ := one_mul _

/-- **The slab geometry transports the boundary uncertainty with no fresh uncertainty** (`r = 0`): joining layer
`i + 1` multiplies it by the layer's own factor `ρ i` (`elec_submul`, zero join loss). -/
theorem ym_slab_transport (hΩ : Function.Involutive Ω) {T : ℕ → X → X → ℝ}
    (hsym : ∀ n z y, T n (Ω z) (Ω y) = T n z y) {ρ : ℕ → ℝ} (hρ : ∀ i, twistCert Ω (T (i + 1)) (ρ i)) (n : ℕ) :
    TransportsCert (fun i u => twistCert Ω (kchain T i) u) ρ (fun _ => 0) n := fun i _ u hu x y => by
  have h := elec_submul hΩ (hsym (i + 1)) hu (hρ i) x y
  rw [show ρ i * u + 0 = u * ρ i by ring]
  exact h

/-- **The side seam in transport form** (named; **open** in the box geometry). Joining layer `i + 1` to the chain
multiplies the boundary uncertainty by `ρ i` and adds at most `σ i`, the cost of the seam of the twist sheet along the
side outside. In the slab geometry it holds with `σ = 0` (`seamTransport_slab`). -/
def SeamTransport (Ω : X → X) (T : ℕ → X → X → ℝ) (ρ σ : ℕ → ℝ) (n : ℕ) : Prop :=
  TransportsCert (fun i u => twistCert Ω (kchain T i) u) ρ σ n

/-- In the slab geometry the seam costs nothing. -/
theorem seamTransport_slab (hΩ : Function.Involutive Ω) {T : ℕ → X → X → ℝ}
    (hsym : ∀ n z y, T n (Ω z) (Ω y) = T n z y) {ρ : ℕ → ℝ} (hρ : ∀ i, twistCert Ω (T (i + 1)) (ρ i)) (n : ℕ) :
    SeamTransport Ω T ρ (fun _ => 0) n :=
  ym_slab_transport hΩ hsym hρ n

/-- **The Yang-Mills bridge in transport form.** Nonnegative layers; the first has boundary uncertainty `u₀`; the seam
transport holds with factor `θ < 1` and seam cost `σ` per join. Then O1 in sector form at `μ` holds after `n` joins as
soon as `μ (θ^n u₀ + σ / (1 − θ)) ≤ 1`: the transported uncertainty, (a), stays below the margin `1/μ`, (c). -/
theorem ym_bridge {T : ℕ → X → X → ℝ} (hT : ∀ n x y, 0 ≤ T n x y) {θ σ u₀ μ : ℝ} {n : ℕ}
    (hseam : SeamTransport Ω T (fun _ => θ) (fun _ => σ) n) (h0 : twistCert Ω (T 0) u₀) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hσ : 0 ≤ σ) (hμ0 : 0 ≤ μ) (hmargin : μ * (θ ^ n * u₀ + σ / (1 - θ)) ≤ 1) (x y : X) :
    μ * |sec1 Ω (kchain T n) x y| ≤ sec0 Ω (kchain T n) x y := by
  have hc := transport_cert hseam (show twistCert Ω (kchain T 0) u₀ from h0)
  have hb : acc (fun _ => θ) (fun _ => σ) u₀ n ≤ θ ^ n * u₀ + σ / (1 - θ) := by
    rw [acc_const]
    have := geom_tail_le hθ0 hθ1 hσ (r := fun _ => σ) (fun _ => le_refl σ) n
    linarith
  exact ym_O1_of_cert (kchain_nonneg hT n) (twistCert_mono (kchain_nonneg hT n) hc hb) hμ0 hmargin x y

/-- **Deficit at most zero puts the slab at or below the self-dual factor** `√2 − 1`, the input of `three_slabs_O1`. -/
theorem elec_le_of_deficit {c : ℝ} (hd : elecDeficit c ≤ 0) : elec c ≤ √2 - 1 := by
  have hc : √2 - 1 ≤ c := by unfold elecDeficit at hd; linarith
  have hp := sqrt_two_sub_one_pos
  calc elec c ≤ elec (√2 - 1) := (elec_le_elec_iff (by linarith) (by linarith)).2 hc
    _ = √2 - 1 := elec_selfdual

/-- **A positive deficit only costs layers.** In the slab geometry, if every layer has pointwise twist ratio at least
`c ∈ (0, 1]` (any deficit `< √2 − 1`), then for every `μ ≥ 0` there is `N` such that every chain of more than `N` layers
satisfies O1 in sector form at `μ`. The open step is not here: it is that `c` stays bounded below **uniformly in the
lattice spacing at a fixed physical layer length**, so that `N` layers have a fixed physical length. -/
theorem ym_layers_needed (hΩ : Function.Involutive Ω) {T : ℕ → X → X → ℝ} (hT : ∀ n x y, 0 ≤ T n x y)
    (hsym : ∀ n z y, T n (Ω z) (Ω y) = T n z y) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hc : ∀ n x y, c * T n x y ≤ T n x (Ω y)) {μ : ℝ} (hμ : 0 ≤ μ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ x y, μ * |sec1 Ω (kchain T n) x y| ≤ sec0 Ω (kchain T n) x y := by
  have hq0 : 0 ≤ elec c := div_nonneg (by linarith) (by linarith)
  have hq1 : elec c < 1 := by rw [elec, div_lt_one (by linarith)]; linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (μ + 1) by positivity) hq1
  refine ⟨N, fun n hn x y => ym_O1_of_cert (kchain_nonneg hT n) (fun x y => kchain_elec hΩ hsym hc0 hc n x y) hμ ?_ x y⟩
  have h1 : elec c ^ (n + 1) ≤ elec c ^ N := pow_le_pow_of_le_one hq0 hq1.le (by omega)
  have h2 : μ * elec c ^ (n + 1) ≤ μ * (1 / (μ + 1)) := mul_le_mul_of_nonneg_left (h1.trans hN.le) hμ
  have h3 : μ * (1 / (μ + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by linarith)]; linarith
  linarith

end YM

/-! ### 2. GRH: the explicit formula's remainder along the scale steps -/

section GRH

/-- **The uncertainty of the margin**, relative to the finite model's margin: `|E n − Ê n| / Ê n`. -/
def relUnc (E Ê : ℕ → ℝ) (n : ℕ) : ℝ := |E n - Ê n| / Ê n

/-- **The explicit formula's remainder at scale `n`**, as it enters the step: the relative difference of zeta's Szego
factor `s n = 1 − |k n|^2` and the model's `ŝ n = 1 − |k̂ n|^2`. -/
def relRem (s ŝ : ℕ → ℝ) (n : ℕ) : ℝ := |s n - ŝ n| / ŝ n

variable {E Ê s ŝ : ℕ → ℝ}

/-- The model's margin stays positive while its factors are positive. -/
theorem margin_pos (hÊ : ∀ n, Ê (n + 1) = ŝ n * Ê n) (hŝ : ∀ n, 0 < ŝ n) (h0 : 0 < Ê 0) (n : ℕ) : 0 < Ê n := by
  induction n with
  | zero => exact h0
  | succ n ih => rw [hÊ]; exact mul_pos (hŝ n) ih

/-- **The absolute transport.** `|E − Ê|` is carried with the model's Szego factor `ŝ n` (floor `0`) and gets the fresh
uncertainty `|s n − ŝ n| |E n|` from the remainder at scale `n`. -/
theorem grh_abs_step (hE : ∀ n, E (n + 1) = s n * E n) (hÊ : ∀ n, Ê (n + 1) = ŝ n * Ê n) {n : ℕ}
    (hŝ : 0 ≤ ŝ n) : |E (n + 1) - Ê (n + 1)| ≤ ŝ n * |E n - Ê n| + |s n - ŝ n| * |E n| := by
  rw [hE, hÊ, show s n * E n - ŝ n * Ê n = ŝ n * (E n - Ê n) + (s n - ŝ n) * E n by ring]
  calc _ ≤ |ŝ n * (E n - Ê n)| + |(s n - ŝ n) * E n| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hŝ]

/-- **The relative step**: `1 + relUnc (n + 1) ≤ (1 + relRem n) (1 + relUnc n)`. -/
theorem grh_rel_step (hE : ∀ n, E (n + 1) = s n * E n) (hÊ : ∀ n, Ê (n + 1) = ŝ n * Ê n) {n : ℕ}
    (hŝ : 0 < ŝ n) (hÊn : 0 < Ê n) :
    1 + relUnc E Ê (n + 1) ≤ (1 + relRem s ŝ n) * (1 + relUnc E Ê n) := by
  have hstep := grh_abs_step hE hÊ hŝ.le
  have hEabs : |E n| ≤ Ê n + |E n - Ê n| := by
    calc |E n| = |Ê n + (E n - Ê n)| := by ring_nf
      _ ≤ |Ê n| + |E n - Ê n| := abs_add_le _ _
      _ = _ := by rw [abs_of_pos hÊn]
  have hd : 0 ≤ |s n - ŝ n| := abs_nonneg _
  have key : |E (n + 1) - Ê (n + 1)| ≤ ŝ n * |E n - Ê n| + |s n - ŝ n| * (Ê n + |E n - Ê n|) :=
    hstep.trans (by have := mul_le_mul_of_nonneg_left hEabs hd; linarith)
  have hden : Ê (n + 1) = ŝ n * Ê n := hÊ n
  have hpos : 0 < Ê (n + 1) := by rw [hden]; exact mul_pos hŝ hÊn
  have hŝne := hŝ.ne'
  have hÊne := hÊn.ne'
  have h1 : |E (n + 1) - Ê (n + 1)| / Ê (n + 1) ≤
      (ŝ n * |E n - Ê n| + |s n - ŝ n| * (Ê n + |E n - Ê n|)) / Ê (n + 1) :=
    div_le_div_of_nonneg_right key hpos.le
  have h2 : (ŝ n * |E n - Ê n| + |s n - ŝ n| * (Ê n + |E n - Ê n|)) / Ê (n + 1) =
      |E n - Ê n| / Ê n + |s n - ŝ n| / ŝ n + (|s n - ŝ n| / ŝ n) * (|E n - Ê n| / Ê n) := by
    rw [hden]; field_simp; ring
  unfold relUnc relRem
  nlinarith [h1, h2]

/-- **GRH is the critical case.** `log (1 + relUnc)` is transported at exactly cost = floor (floor `0`, factor `1`),
with fresh uncertainty `log (1 + relRem n)`: no damping across scales (zero slack). -/
theorem grh_log_transport (hE : ∀ n, E (n + 1) = s n * E n) (hÊ : ∀ n, Ê (n + 1) = ŝ n * Ê n)
    (hŝ : ∀ n, 0 < ŝ n) (hÊ0 : 0 < Ê 0) (n : ℕ) :
    Transports (fun i => Real.log (1 + relUnc E Ê i)) (fun _ => 1) (fun i => Real.log (1 + relRem s ŝ i)) 0 n :=
  fun i _ => by
    have hu : 0 ≤ relUnc E Ê i := div_nonneg (abs_nonneg _) (margin_pos hÊ hŝ hÊ0 i).le
    have hu' : 0 ≤ relUnc E Ê (i + 1) := div_nonneg (abs_nonneg _) (margin_pos hÊ hŝ hÊ0 (i + 1)).le
    have hr : 0 ≤ relRem s ŝ i := div_nonneg (abs_nonneg _) (hŝ i).le
    have hstep := grh_rel_step hE hÊ (hŝ i) (margin_pos hÊ hŝ hÊ0 i)
    show Real.log (1 + relUnc E Ê (i + 1)) ≤
      Real.exp 0 * 1 * Real.log (1 + relUnc E Ê i) + Real.log (1 + relRem s ŝ i)
    rw [Real.exp_zero, one_mul, one_mul, add_comm (Real.log (1 + relUnc E Ê i)),
      ← Real.log_mul (show (0 : ℝ) < 1 + relRem s ŝ i by linarith).ne'
        (show (0 : ℝ) < 1 + relUnc E Ê i by linarith).ne']
    exact Real.log_le_log (by linarith) hstep

/-- **The GRH bridge, sign form.** If the start plus the accumulated remainder stays below `log 2`, zeta's margin is
positive at scale `n`, and quantitatively `E n ≥ (1 − relUnc n) Ê n` with `relUnc n < 1`. -/
theorem grh_sign (hE : ∀ n, E (n + 1) = s n * E n) (hÊ : ∀ n, Ê (n + 1) = ŝ n * Ê n) (hŝ : ∀ n, 0 < ŝ n)
    (hÊ0 : 0 < Ê 0) {n : ℕ}
    (hsum : Real.log (1 + relUnc E Ê 0) + ∑ j ∈ range n, Real.log (1 + relRem s ŝ j) < Real.log 2) :
    0 < E n ∧ relUnc E Ê n < 1 ∧ (1 - relUnc E Ê n) * Ê n ≤ E n := by
  have hpos := margin_pos hÊ hŝ hÊ0 n
  have hu : 0 ≤ relUnc E Ê n := div_nonneg (abs_nonneg _) hpos.le
  have hL := critical_transport (grh_log_transport hE hÊ hŝ hÊ0 n) fun _ _ => by rw [Real.exp_zero, one_mul]
  have h2 : 1 + relUnc E Ê n < 2 := (Real.log_lt_log_iff (by linarith) (by norm_num)).1 (hL.trans_lt hsum)
  have hlt : relUnc E Ê n < 1 := by linarith
  have habs : |E n - Ê n| = relUnc E Ê n * Ê n := by unfold relUnc; field_simp
  have hge : Ê n - |E n - Ê n| ≤ E n := by linarith [neg_abs_le (E n - Ê n)]
  refine ⟨?_, hlt, ?_⟩
  · have : |E n - Ê n| < Ê n := by rw [habs]; nlinarith
    linarith
  · rw [habs] at hge; linarith

/-- **The GRH bridge, summed form.** Starting from equal margins, a total relative remainder below `log 2` certifies
zeta's margin at every scale up to `n`. -/
theorem grh_sign_of_sum (hE : ∀ n, E (n + 1) = s n * E n) (hÊ : ∀ n, Ê (n + 1) = ŝ n * Ê n) (hŝ : ∀ n, 0 < ŝ n)
    (hÊ0 : 0 < Ê 0) (h0 : E 0 = Ê 0) {n : ℕ} (hsum : ∑ j ∈ range n, relRem s ŝ j < Real.log 2) : 0 < E n := by
  refine (grh_sign hE hÊ hŝ hÊ0 ?_).1
  have hu0 : relUnc E Ê 0 = 0 := by simp [relUnc, h0]
  rw [hu0, add_zero, Real.log_one, zero_add]
  refine lt_of_le_of_lt (sum_le_sum fun j _ => ?_) hsum
  have hr : 0 ≤ relRem s ŝ j := div_nonneg (abs_nonneg _) (hŝ j).le
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + relRem s ŝ j by linarith)
  linarith

/-- **The sign alone is decided step by step**: a remainder below the model's factor, `relRem n < 1`, keeps zeta's
factor positive. What the transport adds is the size of the margin (`grh_sign`). -/
theorem grh_sign_step (hE : ∀ n, E (n + 1) = s n * E n) {n : ℕ} (hŝ : 0 < ŝ n) (hη : relRem s ŝ n < 1)
    (hEn : 0 < E n) : 0 < E (n + 1) := by
  have h1 : |s n - ŝ n| < ŝ n := by rwa [relRem, div_lt_one hŝ] at hη
  have h2 : 0 < s n := by linarith [neg_abs_le (s n - ŝ n)]
  rw [hE]; exact mul_pos h2 hEn

/-- **With the model's factors as Szego factors** `1 − |k̂ n|^2` of reflection coefficients in the open unit disk
(`Encoder.lean`, `szego_pos_iff`). -/
theorem grh_sign_szego {k : ℕ → ℂ} (hE : ∀ n, E (n + 1) = s n * E n)
    (hÊ : ∀ n, Ê (n + 1) = szego (k n) * Ê n) (hk : ∀ n, ‖k n‖ < 1) (hÊ0 : 0 < Ê 0) (h0 : E 0 = Ê 0) {n : ℕ}
    (hsum : ∑ j ∈ range n, relRem s (fun j => szego (k j)) j < Real.log 2) : 0 < E n :=
  grh_sign_of_sum (ŝ := fun j => szego (k j)) hE hÊ (fun j => (szego_pos_iff (k j)).2 (hk j)) hÊ0 h0 hsum

end GRH

/-! ### 3. NP: the hidden information across the two-party split -/

section NP

open ProofPhase.Proof ProofPhase.Proof.Edge ProofPhase.Proof.Lifting

/-- **The hidden information per variable**: Alice's pointer bits, in nats. -/
def hiddenQuantum (G : Gadget) : ℝ := G.a * Real.log 2

/-- For the Index gadget the quantum is `log m`, `m = 2^t` the size of Bob's table. -/
theorem indGadget_quantum (t : ℕ) : hiddenQuantum (indGadget t) = Real.log ((indGadget t).b) := by
  show (t : ℝ) * Real.log 2 = Real.log (((2 ^ t : ℕ) : ℝ))
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]

/-- **Hidden transport**: every refutation's line count is carried across `W` hidden variables, each crossing keeping at
most the share `e^{-q}` (the ledger law `Pays` with cost `q`, floor `0`, no fresh uncertainty), and one line is left. -/
def HiddenTransport {Line : Type*} (Refutes : Finset Line → Prop) (q : ℝ) (W : ℕ) : Prop :=
  ∀ P, Refutes P → ∃ M : ℕ → ℝ, M 0 = P.card ∧ Pays M (fun _ => q) 0 W ∧ 1 ≤ M W

/-- **Hidden transport is exactly a size bound** `e^{W q} ≤ |P|`. -/
theorem hiddenTransport_iff_size {Line : Type*} {Refutes : Finset Line → Prop} {q : ℝ} {W : ℕ} :
    HiddenTransport Refutes q W ↔ ∀ P, Refutes P → Real.exp (W * q) ≤ P.card := by
  constructor
  · intro h P hP
    obtain ⟨M, h0, hp, h1⟩ := h P hP
    have := size hp h1
    simp only [sum_const, card_range, nsmul_eq_mul, mul_zero, sub_zero, one_mul] at this
    rwa [h0] at this
  · intro h P hP
    refine ⟨fun k => P.card * Real.exp (-(k * q)), by simp, fun i _ => le_of_eq ?_, ?_⟩
    · show (P.card : ℝ) * Real.exp (-(((i + 1 : ℕ) : ℝ) * q)) = Real.exp (0 - q) * (P.card * Real.exp (-(i * q)))
      rw [show -(((i + 1 : ℕ) : ℝ) * q) = (0 - q) + -((i : ℝ) * q) by push_cast; ring, Real.exp_add]
      ring
    · show 1 ≤ (P.card : ℝ) * Real.exp (-(W * q))
      calc (1 : ℝ) = Real.exp (W * q) * Real.exp (-(W * q)) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        _ ≤ P.card * Real.exp (-(W * q)) := mul_le_mul_of_nonneg_right (h P hP) (Real.exp_pos _).le

variable {α : Type} [Fintype α] [DecidableEq α]

/-- **Lifting in transport form** (from the named external `LiftCP`): a width-hard formula's lifted refutations carry
the line count across `w + 1` hidden variables at cost `c log n` each. -/
theorem liftCP_hiddenTransport {gad : ℕ → Gadget} {c : ℝ} {n₀ : ℕ} (h : LiftCP gad c n₀)
    (hn : n₀ ≤ Fintype.card α) {F : CNF α} (hF : ∀ D ∈ F, D.Nonempty) {w : ℕ} (hw : ¬ WD F w ∅) :
    HiddenTransport (CPRefutes (comp (gad (Fintype.card α)) F)) (c * Real.log (Fintype.card α)) (w + 1) :=
  hiddenTransport_iff_size.2 fun P hP => by
    have := lifted_size h hn hF hw hP
    rwa [show ((w + 1 : ℕ) : ℝ) * (c * Real.log (Fintype.card α)) = c * (w + 1) * Real.log (Fintype.card α) by
      push_cast; ring]

/-- **The constant quantum in transport form** (from the named **open** `LiftCPConst`): cost `c` per hidden variable,
free of `n`. -/
theorem liftCPConst_hiddenTransport {G : Gadget} {c : ℝ} (h : LiftCPConst G c) {F : CNF α}
    (hF : ∀ D ∈ F, D.Nonempty) {w : ℕ} (hw : ¬ WD F w ∅) :
    HiddenTransport (CPRefutes (comp G F)) c (w + 1) :=
  hiddenTransport_iff_size.2 fun P hP => by
    have := h α F w hF hw P hP
    rwa [show ((w + 1 : ℕ) : ℝ) * c = c * (w + 1) by push_cast; ring]

/-- A constant cost per hidden variable is a cost above the floor `0` exactly when it is positive. -/
theorem costAboveFloor_const_iff {c : ℝ} : CostAboveFloor (fun _ : ℕ => c) 0 ↔ 0 < c :=
  ⟨fun ⟨_, hκ, h⟩ => hκ.trans_le (h 0), fun hc => ⟨c, hc, fun _ => le_rfl⟩⟩

/-- **Hiding errors add up at cost = floor.** Per-block hiding errors `ε` across `n` blocks, transported with factor
`1` (blocks do not damp each other's errors), total exactly `n ε`; with `ε > 0` the total exceeds every margin. -/
theorem hiding_accumulates {ε : ℝ} (n : ℕ) :
    critAcc 0 (fun _ => ε) n = n * ε ∧ (0 < ε → ∀ μ, ∃ N, μ < critAcc 0 (fun _ => ε) N) :=
  ⟨by simp [critAcc], fun hε μ => critical_unbounded hε μ⟩

end NP

end ProofPhase.Unified
