/-
The electric-SU(N) round, part 2: pressing (fine to coarse), the side seam, and O1 as one named statement plus the seam
(2026-11-23). Released under Apache 2.0.

Note: `docs/unified/ELECTRIC-SUN.md`, sections 3 to 5.
-/

import ProofPhase.Unified.ElectricSUN

/-!
# Pressing the electric factor from fine to coarse; the side seam as the transport's fresh uncertainty

**1. Pressing.** The slab of thickness `(n + 1) L` is the `(n + 1)`-fold join of the slab of thickness `L` (the transfer
kernel composes, `kpow`). Coarse-graining an end face is a further join with a nonnegative block kernel: on the near
face any `P ≥ 0`, on the far face a centre-symmetric `Q ≥ 0` (`coarse P K Q`).
* `twistCertN_left`, `twistCertN_right`: coarse-graining never raises the boundary-uniform electric factor.
* `twistCertN_kpow`: thickness `(n + 1) L` has factor at most `u^{n+1}` (zero join loss, `elecN_submul`).
* **`press`**: the coarse-grained slab of thickness `(n + 1) L` has factor at most `u^{n+1}`; in cost form
  (`elecCost u = −log u`) the cost is at least `(n + 1)` times the cost of one fine slab (`press_cost`).
* `centreSym_kjoin`, `centreSym_coarse`: joins and centre-symmetric coarse-grainings stay centre-symmetric, so pressed
  slabs can be pressed again.

**2. The named hypothesis.** A family of hand-over slabs `Kh i`, one per cutoff `i` (lattice spacing; any side outside
may be folded into the index), each of the same fixed physical thickness `L_h`.
* **`HandoverSide N Kh`**: for every cutoff, every nontrivial sector `e` and every end-face outside,
  `‖Z_e‖ ≤ (√2 − 1) Z_0`. **open**
* `handoverSide_iff`: this is exactly O1 in sector form at `μ = 1 + √2` at the single length `L_h`.
* **`O1_slab_of_handover`**: in the slab geometry it gives O1 at `3 L_h` for every `μ ≤ 14`, every cutoff, every
  sector, every end-face outside; `O1_slab_coarse` the same after coarse-graining the end faces.

**3. The side seam.** In a box the side outside is fixed, and the centre action of the slab geometry is no symmetry.
* `SeamDefect N K δ`: `|K (k +ᵥ z) (k +ᵥ y) − K z y| ≤ δ K z y` for every twist and every pair of end faces: the
  **exact seam cost** of a layer, the relative change of its weight when the centre action moves past the side collar.
  `seamDefect_zero_iff`: `δ = 0` is `CentreSym`.
* `ksym`: the centre average of a layer, centre-symmetric (`centreSym_ksym`), with the same sector factor
  (`twistCertN_ksym`) and within `δ` of the layer (`ksym_sub_le`, `ksym_le`).
* **`elecN_seam`**: joining a layer with seam cost `δ` carries the factor `u` to `(1 + δ) ρ u + δ`. So the seam is
  exactly the transport's fresh uncertainty `r = δ` per join, with factor `(1 + δ) ρ` (`seamTransportN`, a
  `TransportsCert` of `Transport.lean`).
* **`ym_box_bridge`**: O1 at `μ` after `n` joins once `μ (θ'^n u₀ + δ/(1 − θ')) ≤ 1`, `θ' = (1 + δ) θ < 1`.
* **`three_boxes_seam`**, `three_boxes_seam_num`: three box layers at the self-dual factor with seam cost `δ ≤ 1/25`
  clear O1 for every `μ ≤ 7`.
* `seamDefect_of_floor`, `seamDefect_small`: a per-configuration floor `e^{−s} ≤ K(k +ᵥ z, k +ᵥ y)/K(z, y) ≤ e^{s}`
  gives seam cost `e^s − 1`, at most `1/25` for `s ≤ 1/50` (strong coupling or a short seam: SU(2) Wilson `s = 2 β M`,
  `M` the seam plaquettes of one layer).
* **`O1_box_of_handover_seam`**: `HandoverSide` for the box layers plus seam cost `≤ 1/25` per join give O1 at `3 L_h`
  for `μ ≤ 7`, every cutoff. **So O1 is the one named statement `HandoverSide` plus the seam bound.**

**Claim discipline.** Not O1. `HandoverSide` is open (uniform in the cutoff it is confinement's onset at a fixed
physical size); the seam bound is proved here only under a per-configuration floor, i.e. at strong coupling or for a
short seam. The lattice facts (the transfer kernel composes; the slab is centre-symmetric with periodic transverse
directions; the seam is the side collar) are classical and not formalised for the gauge chain.
-/

open Finset ZMod

noncomputable section

namespace ProofPhase.Unified

/-! ## 1. Pressing: joins and coarse-graining of end faces -/

section Press

variable {N : ℕ} [NeZero N] {W X Y V : Type*} [Fintype X] [Fintype Y] [AddAction (ZMod N) X] [AddAction (ZMod N) Y]
  [AddAction (ZMod N) V]

/-- Coarse-graining both end faces: `P` on the near face, `Q` on the far face. -/
def coarse (P : W → X → ℝ) (K : X → Y → ℝ) (Q : Y → V → ℝ) : W → V → ℝ := kjoin (kjoin P K) Q

/-- `n + 1` copies of one slab in series: the slab of thickness `(n + 1) L`. -/
def kpow {Z : Type*} [Fintype Z] (K : Z → Z → ℝ) (n : ℕ) : Z → Z → ℝ := kchain (fun _ => K) n

/-- The electric cost of a factor, `−log u`. -/
def elecCost (u : ℝ) : ℝ := -Real.log u

omit [Fintype Y] [AddAction (ZMod N) X] [AddAction (ZMod N) V] in
/-- Joining on the near face is linear in the sectors (no symmetry needed). -/
theorem secN_kjoin_left (P : W → X → ℝ) (K : X → Y → ℝ) (e : ZMod N) (w : W) (y : Y) :
    secN (kjoin P K) e w y = ∑ x, (P w x : ℂ) * secN K e x y := by
  unfold secN kjoin
  push_cast
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_congr rfl fun k _ => by ring

omit [Fintype Y] [AddAction (ZMod N) X] [AddAction (ZMod N) V] in
theorem sec0N_kjoin_left (P : W → X → ℝ) (K : X → Y → ℝ) (w : W) (y : Y) :
    sec0N N (kjoin P K) w y = ∑ x, P w x * sec0N N K x y := by
  have h := secN_kjoin_left P K (0 : ZMod N) w y
  simp only [secN_zero] at h
  exact_mod_cast h

omit [Fintype Y] [AddAction (ZMod N) X] [AddAction (ZMod N) V] in
/-- **Coarse-graining the near face never raises the factor.** -/
theorem twistCertN_left {P : W → X → ℝ} (hP : ∀ w x, 0 ≤ P w x) {K : X → Y → ℝ} {e : ZMod N} {u : ℝ}
    (h : twistCertN N K e u) : twistCertN N (kjoin P K) e u := by
  intro w y
  rw [secN_kjoin_left, sec0N_kjoin_left, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun x _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hP w x)]
  calc P w x * ‖secN K e x y‖ ≤ P w x * (u * sec0N N K x y) := mul_le_mul_of_nonneg_left (h x y) (hP w x)
    _ = u * (P w x * sec0N N K x y) := by ring

omit [Fintype X] [AddAction (ZMod N) X] in
/-- **Coarse-graining the far face (centre-symmetric block kernel) never raises the factor.** -/
theorem twistCertN_right {K : W → Y → ℝ} {Q : Y → V → ℝ} (hQ : ∀ y v, 0 ≤ Q y v) (hs : CentreSym N Q) {e : ZMod N}
    {u : ℝ} (h : twistCertN N K e u) : twistCertN N (kjoin K Q) e u := by
  have := elecN_submul hs h (twistCertN_one hQ e)
  rwa [mul_one] at this

omit [AddAction (ZMod N) X] in
theorem twistCertN_coarse {P : W → X → ℝ} (hP : ∀ w x, 0 ≤ P w x) {K : X → Y → ℝ} {Q : Y → V → ℝ}
    (hQ : ∀ y v, 0 ≤ Q y v) (hs : CentreSym N Q) {e : ZMod N} {u : ℝ} (h : twistCertN N K e u) :
    twistCertN N (coarse P K Q) e u :=
  twistCertN_right hQ hs (twistCertN_left hP h)

omit [NeZero N] [Fintype Y] [AddAction (ZMod N) Y] in
/-- A join of centre-symmetric kernels is centre-symmetric. -/
theorem centreSym_kjoin {Ka : W → X → ℝ} {Kb : X → V → ℝ} [AddAction (ZMod N) W] (ha : CentreSym N Ka)
    (hb : CentreSym N Kb) : CentreSym N (kjoin Ka Kb) := by
  intro k w v
  unfold kjoin
  refine Fintype.sum_equiv (vaddPerm (Z := X) k).symm _ _ fun x => ?_
  show Ka (k +ᵥ w) x * Kb x (k +ᵥ v) = Ka w ((-k) +ᵥ x) * Kb ((-k) +ᵥ x) v
  conv_lhs => rw [← vadd_neg_vadd k x]
  rw [ha, hb]

omit [NeZero N] in
theorem centreSym_coarse [AddAction (ZMod N) W] {P : W → X → ℝ} {K : X → Y → ℝ} {Q : Y → V → ℝ}
    (hP : CentreSym N P) (hK : CentreSym N K) (hQ : CentreSym N Q) : CentreSym N (coarse P K Q) :=
  centreSym_kjoin (centreSym_kjoin hP hK) hQ

omit [Fintype Y] [AddAction (ZMod N) Y] [AddAction (ZMod N) V] in
theorem kpow_nonneg {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y) (n : ℕ) (x y : X) : 0 ≤ kpow K n x y :=
  kchain_nonneg (fun _ => hK) n x y

omit [NeZero N] [Fintype Y] [AddAction (ZMod N) Y] [AddAction (ZMod N) V] in
theorem centreSym_kpow {K : X → X → ℝ} (hK : CentreSym N K) (n : ℕ) : CentreSym N (kpow K n) := by
  induction n with
  | zero => exact hK
  | succ n ih => exact centreSym_kjoin ih hK

omit [Fintype Y] [AddAction (ZMod N) Y] [AddAction (ZMod N) V] in
/-- **Thickness `(n + 1) L` from thickness `L`, no loss**: factor at most `u^{n+1}`. -/
theorem twistCertN_kpow {K : X → X → ℝ} (hK : CentreSym N K) {e : ZMod N} {u : ℝ} (h : twistCertN N K e u)
    (n : ℕ) : twistCertN N (kpow K n) e (u ^ (n + 1)) :=
  kchainN_elec (fun _ => hK) (fun _ => h) n

omit [Fintype Y] in
/-- **Pressing, fine to coarse**: the slab of thickness `(n + 1) L`, both end faces coarse-grained, has factor at most
`u^{n+1}` when the fine slab of thickness `L` has factor `u` at every end face. -/
theorem press {P : W → X → ℝ} (hP : ∀ w x, 0 ≤ P w x) {K : X → X → ℝ} (hsK : CentreSym N K) {Q : X → V → ℝ}
    (hQ : ∀ x v, 0 ≤ Q x v) (hsQ : CentreSym N Q) {e : ZMod N} {u : ℝ} (h : twistCertN N K e u) (n : ℕ) :
    twistCertN N (coarse P (kpow K n) Q) e (u ^ (n + 1)) :=
  twistCertN_coarse hP hQ hsQ (twistCertN_kpow hsK h n)

/-- **The pressing law in cost form**: the cost is additive along the series, `elecCost (u^{n+1}) = (n + 1) elecCost u`. -/
theorem press_cost (u : ℝ) (n : ℕ) : elecCost (u ^ (n + 1)) = (n + 1) * elecCost u := by
  unfold elecCost; rw [Real.log_pow]; push_cast; ring

/-- Costs add under a join: `elecCost (ρa ρb) = elecCost ρa + elecCost ρb` (positive factors). -/
theorem elecCost_mul {ρa ρb : ℝ} (ha : 0 < ρa) (hb : 0 < ρb) : elecCost (ρa * ρb) = elecCost ρa + elecCost ρb := by
  unfold elecCost; rw [Real.log_mul ha.ne' hb.ne']; ring

end Press

/-! ## 2. The named hypothesis: the pointwise electric side at the hand-over slab, uniform in the cutoff -/

section Handover

variable {N : ℕ} [NeZero N] {ι : Type*} {Xf : ι → Type*} [∀ i, Fintype (Xf i)] [∀ i, AddAction (ZMod N) (Xf i)]

/-- **The pointwise electric side at the hand-over slab, uniform in the cutoff** (named; **open**). For every cutoff
`i`, every nontrivial sector `e` and every end-face outside, the hand-over slab `Kh i` (fixed physical thickness `L_h`)
has `‖Z_e‖ ≤ (√2 − 1) Z_0`. -/
def HandoverSide (N : ℕ) [NeZero N] {ι : Type*} {Xf : ι → Type*} [∀ i, AddAction (ZMod N) (Xf i)]
    (Kh : ∀ i, Xf i → Xf i → ℝ) : Prop :=
  ∀ i (e : ZMod N), e ≠ 0 → twistCertN N (Kh i) e (√2 - 1)

omit [∀ i, Fintype (Xf i)] in
/-- **The named hypothesis is O1 at `μ = 1 + √2` at the single length `L_h`.** -/
theorem handoverSide_iff {Kh : ∀ i, Xf i → Xf i → ℝ} (hK : ∀ i x y, 0 ≤ Kh i x y) :
    HandoverSide N Kh ↔ ∀ i (e : ZMod N), e ≠ 0 → ∀ x y, (1 + √2) * ‖secN (Kh i) e x y‖ ≤ sec0N N (Kh i) x y := by
  have hm := sqrt_two_mul
  have hp : 0 < 1 + √2 := by positivity
  constructor
  · intro h i e he x y
    have := mul_le_mul_of_nonneg_left (h i e he x y) hp.le
    calc (1 + √2) * ‖secN (Kh i) e x y‖ ≤ (1 + √2) * ((√2 - 1) * sec0N N (Kh i) x y) := this
      _ = sec0N N (Kh i) x y := by rw [← mul_assoc, mul_comm (1 + √2), hm, one_mul]
  · intro h i e he x y
    have h1 := h i e he x y
    have h0 := sec0N_nonneg (N := N) (hK i) x y
    have hq : √2 - 1 = (1 + √2)⁻¹ := (eq_inv_of_mul_eq_one_left hm)
    rw [hq, ← div_eq_inv_mul, le_div_iff₀ hp, mul_comm]
    exact h1

omit [∀ i, Fintype (Xf i)] in
/-- The hand-over side follows from a pointwise twist ratio at least `cstarN N` at the hand-over slab, every cutoff. -/
theorem handoverSide_of_twist (hN : 2 ≤ N) {Kh : ∀ i, Xf i → Xf i → ℝ} (hK : ∀ i x y, 0 ≤ Kh i x y) {c : ℝ}
    (hc0 : 0 < c) (hc : cstarN N ≤ c) (ht : ∀ i (k : ZMod N) x y, c * Kh i x y ≤ Kh i x (k +ᵥ y)) :
    HandoverSide N Kh := fun i _ he =>
  twistCertN_mono (hK i) (sector_of_twistN (hK i) hc0 (ht i) he) (rhoN_le_of_cstar hN hc0 hc)

/-- **O1 in the slab geometry from the named hypothesis**: three hand-over slabs (`kpow (Kh i) 2`, thickness `3 L_h`)
satisfy `μ ‖Z_e‖ ≤ Z_0` for every `μ ≤ 14`, every cutoff, every nontrivial sector, every end-face outside. -/
theorem O1_slab_of_handover {Kh : ∀ i, Xf i → Xf i → ℝ} (hK : ∀ i x y, 0 ≤ Kh i x y) (hs : ∀ i, CentreSym N (Kh i))
    (h : HandoverSide N Kh) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ 14) (i : ι) {e : ZMod N} (he : e ≠ 0) (x y : Xf i) :
    μ * ‖secN (kpow (Kh i) 2) e x y‖ ≤ sec0N N (kpow (Kh i) 2) x y :=
  three_slabsN_O1 (hK i) (hK i) (hK i) (hs i) (hs i) (h i e he) (h i e he) (h i e he) hμ0 hμ x y

/-- The same for the coarse-grained slab (any nonnegative block kernel on the near face, a centre-symmetric one on the
far face): the hand-over side survives blocking of the end faces. -/
theorem O1_slab_coarse {Kh : ∀ i, Xf i → Xf i → ℝ} (hK : ∀ i x y, 0 ≤ Kh i x y) (hs : ∀ i, CentreSym N (Kh i))
    (h : HandoverSide N Kh) {W V : Type*} [AddAction (ZMod N) V] {i : ι} {P : W → Xf i → ℝ} (hP : ∀ w x, 0 ≤ P w x)
    {Q : Xf i → V → ℝ} (hQ : ∀ x v, 0 ≤ Q x v) (hsQ : CentreSym N Q) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ 14)
    {e : ZMod N} (he : e ≠ 0) (w : W) (v : V) :
    μ * ‖secN (coarse P (kpow (Kh i) 2) Q) e w v‖ ≤ sec0N N (coarse P (kpow (Kh i) 2) Q) w v := by
  have hc := press hP (hs i) hQ hsQ (h i e he) 2
  have h0 : 0 ≤ sec0N N (coarse P (kpow (Kh i) 2) Q) w v :=
    sec0N_nonneg (kjoin_nonneg (kjoin_nonneg hP (kpow_nonneg (hK i) 2)) hQ) w v
  have hclear := three_steps_clear hμ0 hμ
  calc μ * ‖secN (coarse P (kpow (Kh i) 2) Q) e w v‖ ≤ μ * ((√2 - 1) ^ (2 + 1) * sec0N N (coarse P (kpow (Kh i) 2) Q) w v) :=
        mul_le_mul_of_nonneg_left (hc w v) hμ0
    _ = ((√2 - 1) ^ 3 * μ) * sec0N N (coarse P (kpow (Kh i) 2) Q) w v := by ring
    _ ≤ 1 * sec0N N (coarse P (kpow (Kh i) 2) Q) w v := mul_le_mul_of_nonneg_right hclear.le h0
    _ = _ := one_mul _

end Handover

/-! ## 3. The side seam: the exact seam cost and the transport -/

section Seam

variable {N : ℕ} [NeZero N] {X Y : Type*} [Fintype X] [AddAction (ZMod N) X] [AddAction (ZMod N) Y]

/-- **The exact seam cost of a layer**: the centre action moves the layer's weight by at most the fraction `δ`, for
every twist and every pair of end faces. In a box it is the relative weight change of the side collar. -/
def SeamDefect (N : ℕ) {Z Y : Type*} [AddAction (ZMod N) Z] [AddAction (ZMod N) Y] (K : Z → Y → ℝ) (δ : ℝ) : Prop :=
  ∀ (k : ZMod N) z y, |K (k +ᵥ z) (k +ᵥ y) - K z y| ≤ δ * K z y

/-- The centre average of a layer. -/
def ksym (N : ℕ) [NeZero N] {Z Y : Type*} [AddAction (ZMod N) Z] [AddAction (ZMod N) Y] (K : Z → Y → ℝ) (z : Z)
    (y : Y) : ℝ :=
  (N : ℝ)⁻¹ * ∑ j : ZMod N, K (j +ᵥ z) (j +ᵥ y)

omit [Fintype X] [NeZero N] in
/-- Seam cost zero is the slab symmetry. -/
theorem seamDefect_zero_iff {K : X → Y → ℝ} : SeamDefect N K 0 ↔ CentreSym N K := by
  constructor
  · intro h k z y; have := h k z y; rw [zero_mul, abs_nonpos_iff, sub_eq_zero] at this; exact this
  · intro h k z y; rw [h, sub_self, abs_zero, zero_mul]

omit [Fintype X] in
theorem centreSym_ksym (K : X → Y → ℝ) : CentreSym N (ksym N K) := by
  intro k z y
  unfold ksym
  congr 1
  refine Fintype.sum_equiv (Equiv.addRight k) _ _ fun j => ?_
  simp only [Equiv.coe_addRight, vadd_vadd]

omit [Fintype X] in
theorem ksym_nonneg {K : X → Y → ℝ} (hK : ∀ z y, 0 ≤ K z y) (z : X) (y : Y) : 0 ≤ ksym N K z y :=
  mul_nonneg (by positivity) (sum_nonneg fun j _ => hK _ _)

omit [Fintype X] in
/-- The sectors of the centre average are the averages of the shifted sectors. -/
theorem secN_ksym (K : X → Y → ℝ) (e : ZMod N) (z : X) (y : Y) :
    secN (ksym N K) e z y = (N : ℂ)⁻¹ * ∑ j : ZMod N, secN K e (j +ᵥ z) (j +ᵥ y) := by
  unfold secN ksym
  push_cast
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [vadd_vadd, vadd_vadd, add_comm j k]
  ring

omit [Fintype X] in
theorem sec0N_ksym (K : X → Y → ℝ) (z : X) (y : Y) :
    sec0N N (ksym N K) z y = (N : ℝ)⁻¹ * ∑ j : ZMod N, sec0N N K (j +ᵥ z) (j +ᵥ y) := by
  unfold sec0N ksym
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [vadd_vadd, vadd_vadd, add_comm j k]

omit [Fintype X] in
/-- **The centre average keeps the sector factor.** -/
theorem twistCertN_ksym {K : X → Y → ℝ} {e : ZMod N} {u : ℝ} (h : twistCertN N K e u) : twistCertN N (ksym N K) e u := by
  intro z y
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [secN_ksym, sec0N_ksym, norm_mul, norm_inv, Complex.norm_natCast, mul_left_comm, mul_sum]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun j _ => h _ _)) (inv_nonneg.2 hN.le)

omit [Fintype X] in
/-- The centre average is within `δ` of the layer. -/
theorem ksym_sub_le {K : X → Y → ℝ} {δ : ℝ} (hd : SeamDefect N K δ) (z : X) (y : Y) :
    |K z y - ksym N K z y| ≤ δ * K z y := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hK : (N : ℝ)⁻¹ * ∑ _j : ZMod N, K z y = K z y := by
    rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]; field_simp
  have hδK : (N : ℝ)⁻¹ * ∑ _j : ZMod N, δ * K z y = δ * K z y := by
    rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]; field_simp
  have e1 : K z y - (N : ℝ)⁻¹ * ∑ j : ZMod N, K (j +ᵥ z) (j +ᵥ y) =
      (N : ℝ)⁻¹ * ∑ j : ZMod N, (K z y - K (j +ᵥ z) (j +ᵥ y)) := by
    rw [sum_sub_distrib, mul_sub, hK]
  unfold ksym
  rw [e1, abs_mul, abs_of_pos (inv_pos.2 hN), ← hδK]
  refine mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)) (inv_nonneg.2 hN.le)
  rw [abs_sub_comm]; exact hd j z y

omit [Fintype X] in
theorem ksym_le {K : X → Y → ℝ} {δ : ℝ} (hd : SeamDefect N K δ) (z : X) (y : Y) : ksym N K z y ≤ (1 + δ) * K z y := by
  have := ksym_sub_le hd z y
  have := neg_abs_le (K z y - ksym N K z y)
  linarith

omit [Fintype X] [AddAction (ZMod N) X] in
/-- Two kernels within `δ K` of each other have sectors within `δ Z_0(K)` of each other. -/
theorem norm_secN_sub_le {Z : Type*} {K K' : Z → Y → ℝ} {δ : ℝ} (h : ∀ z y, |K z y - K' z y| ≤ δ * K z y)
    (e : ZMod N) (z : Z) (y : Y) : ‖secN K e z y - secN K' e z y‖ ≤ δ * sec0N N K z y := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  unfold secN sec0N
  rw [← mul_sub, ← sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast, mul_left_comm, mul_sum]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)) (inv_nonneg.2 hN.le)
  rw [← mul_sub, norm_mul, AddChar.norm_apply, one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact h z _

omit [AddAction (ZMod N) X] in
theorem kjoin_sub_le {Z : Type*} {Ka : Z → X → ℝ} (ha : ∀ z x, 0 ≤ Ka z x) {Kb Kb' : X → Y → ℝ} {δ : ℝ}
    (h : ∀ x y, |Kb x y - Kb' x y| ≤ δ * Kb x y) (z : Z) (y : Y) :
    |kjoin Ka Kb z y - kjoin Ka Kb' z y| ≤ δ * kjoin Ka Kb z y := by
  unfold kjoin
  rw [← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (ha z x)]
  calc Ka z x * |Kb x y - Kb' x y| ≤ Ka z x * (δ * Kb x y) := mul_le_mul_of_nonneg_left (h x y) (ha z x)
    _ = δ * (Ka z x * Kb x y) := by ring

omit [AddAction (ZMod N) X] in
theorem sec0N_kjoin_le {Z : Type*} {Ka : Z → X → ℝ} (ha : ∀ z x, 0 ≤ Ka z x) {Kb Kb' : X → Y → ℝ} {t : ℝ}
    (h : ∀ x y, Kb' x y ≤ t * Kb x y) (z : Z) (y : Y) : sec0N N (kjoin Ka Kb') z y ≤ t * sec0N N (kjoin Ka Kb) z y := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  unfold sec0N kjoin
  calc (N : ℝ)⁻¹ * ∑ k : ZMod N, ∑ x, Ka z x * Kb' x (k +ᵥ y)
      ≤ (N : ℝ)⁻¹ * ∑ k : ZMod N, ∑ x, t * (Ka z x * Kb x (k +ᵥ y)) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => sum_le_sum fun x _ => ?_) (inv_nonneg.2 hN.le)
        calc Ka z x * Kb' x (k +ᵥ y) ≤ Ka z x * (t * Kb x (k +ᵥ y)) := mul_le_mul_of_nonneg_left (h x _) (ha z x)
          _ = t * (Ka z x * Kb x (k +ᵥ y)) := by ring
    _ = t * ((N : ℝ)⁻¹ * ∑ k : ZMod N, ∑ x, Ka z x * Kb x (k +ᵥ y)) := by
        simp only [← mul_sum]; ring

/-- **The seam is the transport's fresh uncertainty.** Joining a layer with seam cost `δ` and sector factor `ρb` to a
slab with factor `ρa` gives factor `(1 + δ) ρa ρb + δ`: the centre-symmetric part composes with no loss, the seam adds
`δ` and inflates the neutral weight by at most `1 + δ`. -/
theorem elecN_seam {Z : Type*} {Ka : Z → X → ℝ} {Kb : X → Y → ℝ} (ha0 : ∀ z x, 0 ≤ Ka z x)
    (hb0 : ∀ x y, 0 ≤ Kb x y) {δ : ℝ} (hd : SeamDefect N Kb δ) {e : ZMod N} {ρa ρb : ℝ} (hρa : 0 ≤ ρa) (hρb : 0 ≤ ρb)
    (ha : twistCertN N Ka e ρa) (hb : twistCertN N Kb e ρb) : twistCertN N (kjoin Ka Kb) e ((1 + δ) * (ρa * ρb) + δ) := by
  intro z y
  have hsym := elecN_submul (centreSym_ksym Kb) ha (twistCertN_ksym hb) z y
  have hdiff := norm_secN_sub_le (kjoin_sub_le ha0 (ksym_sub_le hd)) e z y
  have hmono := sec0N_kjoin_le (N := N) ha0 (ksym_le hd) z y
  have h0 := sec0N_nonneg (N := N) (kjoin_nonneg ha0 hb0) z y
  have hρ : 0 ≤ ρa * ρb := mul_nonneg hρa hρb
  calc ‖secN (kjoin Ka Kb) e z y‖
      ≤ ‖secN (kjoin Ka (ksym N Kb)) e z y‖ + ‖secN (kjoin Ka Kb) e z y - secN (kjoin Ka (ksym N Kb)) e z y‖ := by
        have := norm_add_le (secN (kjoin Ka (ksym N Kb)) e z y)
          (secN (kjoin Ka Kb) e z y - secN (kjoin Ka (ksym N Kb)) e z y)
        rwa [add_sub_cancel] at this
    _ ≤ ρa * ρb * sec0N N (kjoin Ka (ksym N Kb)) z y + δ * sec0N N (kjoin Ka Kb) z y := add_le_add hsym hdiff
    _ ≤ ρa * ρb * ((1 + δ) * sec0N N (kjoin Ka Kb) z y) + δ * sec0N N (kjoin Ka Kb) z y := by
        gcongr
    _ = ((1 + δ) * (ρa * ρb) + δ) * sec0N N (kjoin Ka Kb) z y := by ring

omit [Fintype X] [NeZero N] in
/-- **A per-configuration floor bounds the seam cost**: `e^{−s} K ≤ K(k +ᵥ ·, k +ᵥ ·) ≤ e^{s} K` gives seam cost
`e^s − 1`. -/
theorem seamDefect_of_floor {K : X → Y → ℝ} (hK : ∀ z y, 0 ≤ K z y) {s : ℝ}
    (hlo : ∀ (k : ZMod N) z y, Real.exp (-s) * K z y ≤ K (k +ᵥ z) (k +ᵥ y))
    (hhi : ∀ (k : ZMod N) z y, K (k +ᵥ z) (k +ᵥ y) ≤ Real.exp s * K z y) : SeamDefect N K (Real.exp s - 1) := by
  intro k z y
  have h1 := hlo k z y
  have h2 := hhi k z y
  have h0 := hK z y
  have hsum : 2 ≤ Real.exp s + Real.exp (-s) := by
    have := Real.add_one_le_exp s; have := Real.add_one_le_exp (-s); linarith
  rw [abs_le]
  constructor <;> nlinarith

/-- A short or weakly coupled seam: `0 ≤ s ≤ 1/50` gives seam cost at most `1/25`. -/
theorem seamDefect_small {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 50) : Real.exp s - 1 ≤ 1 / 25 := by
  have h := Real.abs_exp_sub_one_le (x := s) (by rw [abs_of_nonneg hs0]; linarith)
  rw [abs_of_nonneg hs0] at h
  linarith [le_abs_self (Real.exp s - 1)]

end Seam

/-! ## 4. The seam in transport form; three boxes -/

section Box

variable {N : ℕ} [NeZero N] {X : Type*} [Fintype X] [AddAction (ZMod N) X]

/-- **The box chain transports the factor with fresh uncertainty `δ` per join** (a `TransportsCert` of `Transport.lean`):
each layer `i + 1` with sector factor `ρ` and seam cost `δ` carries a factor `u` of the chain to `(1 + δ) ρ u + δ`. -/
theorem seamTransportN {T : ℕ → X → X → ℝ} (hT : ∀ n x y, 0 ≤ T n x y) {δ ρ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ n, SeamDefect N (T (n + 1)) δ) {e : ZMod N} (hρ0 : 0 ≤ ρ) (hρ : ∀ n, twistCertN N (T (n + 1)) e ρ)
    (n : ℕ) :
    TransportsCert (fun i u => 0 ≤ u ∧ twistCertN N (kchain T i) e u) (fun _ => (1 + δ) * ρ) (fun _ => δ) n := by
  intro i _ u ⟨hu0, hu⟩
  refine ⟨by positivity, ?_⟩
  have h := elecN_seam (kchain_nonneg hT i) (hT (i + 1)) (hδ i) hu0 hρ0 hu (hρ i)
  rw [show (1 + δ) * (u * ρ) + δ = (1 + δ) * ρ * u + δ by ring] at h
  exact h

/-- **The Yang-Mills bridge in a box**: first layer factor `u₀`, each further layer factor `ρ` and seam cost `δ`, with
`θ' = (1 + δ) ρ < 1`. O1 in sector form at `μ` after `n` joins once `μ (θ'^n u₀ + δ/(1 − θ')) ≤ 1`. -/
theorem ym_box_bridge {T : ℕ → X → X → ℝ} (hT : ∀ n x y, 0 ≤ T n x y) {δ ρ u₀ μ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ n, SeamDefect N (T (n + 1)) δ) {e : ZMod N} (hρ0 : 0 ≤ ρ) (hρ : ∀ n, twistCertN N (T (n + 1)) e ρ)
    (hθ : (1 + δ) * ρ < 1) (hu0 : 0 ≤ u₀) (h0 : twistCertN N (T 0) e u₀) (hμ0 : 0 ≤ μ) {n : ℕ}
    (hmargin : μ * (((1 + δ) * ρ) ^ n * u₀ + δ / (1 - (1 + δ) * ρ)) ≤ 1) (x y : X) :
    μ * ‖secN (kchain T n) e x y‖ ≤ sec0N N (kchain T n) x y := by
  have hc := transport_cert (seamTransportN hT hδ0 hδ hρ0 hρ n)
    (show 0 ≤ u₀ ∧ twistCertN N (kchain T 0) e u₀ from ⟨hu0, h0⟩)
  have hb : acc (fun _ => (1 + δ) * ρ) (fun _ => δ) u₀ n ≤ ((1 + δ) * ρ) ^ n * u₀ + δ / (1 - (1 + δ) * ρ) := by
    rw [acc_const]
    have := geom_tail_le (by positivity) hθ hδ0 (r := fun _ => δ) (fun _ => le_refl δ) n
    linarith
  have hcert := twistCertN_mono (kchain_nonneg hT n) hc.2 hb
  have h0' := sec0N_nonneg (N := N) (kchain_nonneg hT n) x y
  calc μ * ‖secN (kchain T n) e x y‖
      ≤ μ * ((((1 + δ) * ρ) ^ n * u₀ + δ / (1 - (1 + δ) * ρ)) * sec0N N (kchain T n) x y) :=
        mul_le_mul_of_nonneg_left (hcert x y) hμ0
    _ = (μ * (((1 + δ) * ρ) ^ n * u₀ + δ / (1 - (1 + δ) * ρ))) * sec0N N (kchain T n) x y := by ring
    _ ≤ 1 * sec0N N (kchain T n) x y := mul_le_mul_of_nonneg_right hmargin h0'
    _ = _ := one_mul _

/-- The transported value of three box layers at factor `θ` with seam cost `δ` per join. -/
def threeBox (θ δ : ℝ) : ℝ := (1 + δ) * (((1 + δ) * (θ * θ) + δ) * θ) + δ

/-- **Three box layers with a seam.** Each layer with sector factor `θ ≥ 0`, the last two with seam cost `δ ≥ 0`:
O1 at `μ` once `μ · threeBox θ δ ≤ 1`. With `δ = 0` this is `three_slabsN_O1`. -/
theorem three_boxes_seam {K₁ K₂ K₃ : X → X → ℝ} (hK₁ : ∀ x y, 0 ≤ K₁ x y) (hK₂ : ∀ x y, 0 ≤ K₂ x y)
    (hK₃ : ∀ x y, 0 ≤ K₃ x y) {δ θ : ℝ} (hδ0 : 0 ≤ δ) (hθ0 : 0 ≤ θ) (hd₂ : SeamDefect N K₂ δ)
    (hd₃ : SeamDefect N K₃ δ) {e : ZMod N} (h₁ : twistCertN N K₁ e θ) (h₂ : twistCertN N K₂ e θ)
    (h₃ : twistCertN N K₃ e θ) {μ : ℝ} (hμ0 : 0 ≤ μ) (hmargin : μ * threeBox θ δ ≤ 1) (x y : X) :
    μ * ‖secN (kjoin (kjoin K₁ K₂) K₃) e x y‖ ≤ sec0N N (kjoin (kjoin K₁ K₂) K₃) x y := by
  have c₁₂ := elecN_seam hK₁ hK₂ hd₂ hθ0 hθ0 h₁ h₂
  have hu : 0 ≤ (1 + δ) * (θ * θ) + δ := by positivity
  have c := elecN_seam (kjoin_nonneg hK₁ hK₂) hK₃ hd₃ hu hθ0 c₁₂ h₃ x y
  have n0 := sec0N_nonneg (N := N) (kjoin_nonneg (kjoin_nonneg hK₁ hK₂) hK₃) x y
  calc μ * ‖secN (kjoin (kjoin K₁ K₂) K₃) e x y‖ ≤ μ * (threeBox θ δ * sec0N N (kjoin (kjoin K₁ K₂) K₃) x y) :=
        mul_le_mul_of_nonneg_left c hμ0
    _ = (μ * threeBox θ δ) * sec0N N (kjoin (kjoin K₁ K₂) K₃) x y := by ring
    _ ≤ 1 * sec0N N (kjoin (kjoin K₁ K₂) K₃) x y := mul_le_mul_of_nonneg_right hmargin n0
    _ = _ := one_mul _

/-- **The seam budget**: at the self-dual factor, a seam cost `δ ≤ 1/25` per join leaves O1 for every `μ ≤ 7`
(`threeBox (√2 − 1) (1/25) ≈ 0.134`; `μ₄ = 6.77`). -/
theorem three_boxes_seam_num {δ μ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 25) (hμ : μ ≤ 7) :
    μ * threeBox (√2 - 1) δ ≤ 1 := by
  have hs : √2 ≤ 1.4143 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have ht0 : 0 ≤ √2 - 1 := sqrt_two_sub_one_pos.le
  set t := √2 - 1 with htdef
  have ht : t ≤ 0.4143 := by rw [htdef]; linarith
  have h1 : 1 + δ ≤ 1.04 := by linarith
  have htt : t * t ≤ 0.4143 * 0.4143 := mul_le_mul ht ht ht0 (by norm_num)
  have hin : (1 + δ) * (t * t) + δ ≤ 1.04 * (0.4143 * 0.4143) + 0.04 := by
    have := mul_le_mul h1 htt (mul_nonneg ht0 ht0) (by norm_num); linarith
  have hin0 : 0 ≤ (1 + δ) * (t * t) + δ := by positivity
  have h2 : ((1 + δ) * (t * t) + δ) * t ≤ (1.04 * (0.4143 * 0.4143) + 0.04) * 0.4143 :=
    mul_le_mul hin ht ht0 (by norm_num)
  have h3 : (1 + δ) * (((1 + δ) * (t * t) + δ) * t) ≤ 1.04 * ((1.04 * (0.4143 * 0.4143) + 0.04) * 0.4143) :=
    mul_le_mul h1 h2 (mul_nonneg hin0 ht0) (by norm_num)
  have hE : threeBox t δ ≤ 0.1342 := by unfold threeBox; norm_num at h3 ⊢; linarith
  have hE0 : 0 ≤ threeBox t δ := by unfold threeBox; positivity
  calc μ * threeBox t δ ≤ 7 * 0.1342 := mul_le_mul hμ hE hE0 (by norm_num)
    _ ≤ 1 := by norm_num

end Box

/-! ## 5. O1 = the named hypothesis plus the seam -/

section O1

variable {N : ℕ} [NeZero N] {ι : Type*} {Xf : ι → Type*} [∀ i, Fintype (Xf i)] [∀ i, AddAction (ZMod N) (Xf i)]

/-- **O1 from the named hypothesis plus the seam.** Three box layers `K₁ i, K₂ i, K₃ i` per cutoff `i` (side outsides
folded into `i`), each on the pointwise electric side (`HandoverSide`), the last two with seam cost `0 ≤ δ ≤ 1/25`:
O1 in sector form at `3 L_h` for every `μ ≤ 7`, every cutoff, every nontrivial sector, every end-face outside. -/
theorem O1_box_of_handover_seam {K₁ K₂ K₃ : ∀ i, Xf i → Xf i → ℝ} (hK₁ : ∀ i x y, 0 ≤ K₁ i x y)
    (hK₂ : ∀ i x y, 0 ≤ K₂ i x y) (hK₃ : ∀ i x y, 0 ≤ K₃ i x y) (h₁ : HandoverSide N K₁) (h₂ : HandoverSide N K₂)
    (h₃ : HandoverSide N K₃) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 25) (hd₂ : ∀ i, SeamDefect N (K₂ i) δ)
    (hd₃ : ∀ i, SeamDefect N (K₃ i) δ) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ 7) (i : ι) {e : ZMod N} (he : e ≠ 0)
    (x y : Xf i) :
    μ * ‖secN (kjoin (kjoin (K₁ i) (K₂ i)) (K₃ i)) e x y‖ ≤ sec0N N (kjoin (kjoin (K₁ i) (K₂ i)) (K₃ i)) x y :=
  three_boxes_seam (hK₁ i) (hK₂ i) (hK₃ i) hδ0 sqrt_two_sub_one_pos.le (hd₂ i) (hd₃ i) (h₁ i e he) (h₂ i e he)
    (h₃ i e he) hμ0 (three_boxes_seam_num hδ0 hδ hμ) x y

/-- **A regime where everything is proved: per-configuration floors.** If every layer has pointwise twist ratio at
least `cstarN N` for every twist (the side; SU(2): `e^{−2βN_sheet} ≥ √2 − 1`), and the last two have a seam floor
`e^{−s} ≤ K(k +ᵥ ·, k +ᵥ ·)/K ≤ e^{s}` with `0 ≤ s ≤ 1/50` (SU(2): `2 β M ≤ 1/50`, `M` the seam plaquettes per layer),
then O1 holds at `3 L_h` for every `μ ≤ 7`. This is strong coupling in tick units. -/
theorem O1_box_of_floors (hN : 2 ≤ N) {K₁ K₂ K₃ : ∀ i, Xf i → Xf i → ℝ} (hK₁ : ∀ i x y, 0 ≤ K₁ i x y)
    (hK₂ : ∀ i x y, 0 ≤ K₂ i x y) (hK₃ : ∀ i x y, 0 ≤ K₃ i x y) {c : ℝ} (hc0 : 0 < c) (hc : cstarN N ≤ c)
    (t₁ : ∀ i (k : ZMod N) x y, c * K₁ i x y ≤ K₁ i x (k +ᵥ y)) (t₂ : ∀ i (k : ZMod N) x y, c * K₂ i x y ≤ K₂ i x (k +ᵥ y))
    (t₃ : ∀ i (k : ZMod N) x y, c * K₃ i x y ≤ K₃ i x (k +ᵥ y)) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 50)
    (lo₂ : ∀ i (k : ZMod N) z y, Real.exp (-s) * K₂ i z y ≤ K₂ i (k +ᵥ z) (k +ᵥ y))
    (hi₂ : ∀ i (k : ZMod N) z y, K₂ i (k +ᵥ z) (k +ᵥ y) ≤ Real.exp s * K₂ i z y)
    (lo₃ : ∀ i (k : ZMod N) z y, Real.exp (-s) * K₃ i z y ≤ K₃ i (k +ᵥ z) (k +ᵥ y))
    (hi₃ : ∀ i (k : ZMod N) z y, K₃ i (k +ᵥ z) (k +ᵥ y) ≤ Real.exp s * K₃ i z y) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ 7)
    (i : ι) {e : ZMod N} (he : e ≠ 0) (x y : Xf i) :
    μ * ‖secN (kjoin (kjoin (K₁ i) (K₂ i)) (K₃ i)) e x y‖ ≤ sec0N N (kjoin (kjoin (K₁ i) (K₂ i)) (K₃ i)) x y := by
  have hδ0 : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
  exact O1_box_of_handover_seam hK₁ hK₂ hK₃ (handoverSide_of_twist hN hK₁ hc0 hc t₁)
    (handoverSide_of_twist hN hK₂ hc0 hc t₂) (handoverSide_of_twist hN hK₃ hc0 hc t₃) hδ0 (seamDefect_small hs0 hs)
    (fun i => seamDefect_of_floor (hK₂ i) (lo₂ i) (hi₂ i)) (fun i => seamDefect_of_floor (hK₃ i) (lo₃ i) (hi₃ i))
    hμ0 hμ i he x y

end O1

end ProofPhase.Unified
