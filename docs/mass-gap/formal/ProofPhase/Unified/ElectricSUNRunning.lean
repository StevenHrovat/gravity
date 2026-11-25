/-
The electric-SU(N) round, part 3: running outsides and remnants (2026-11-24). Released under Apache 2.0.

Note: `docs/unified/ELECTRIC-SUN.md`, section 10. The owner's reading behind it (`mass-gap/weak-coupling/PREP.md`, last
entry): "Frozen faces aren't running outsides, so they don't count, but their ticks of not counting do count as remnants."
-/

import ProofPhase.Unified.ElectricSUNPress

/-!
# The electric side over running outsides only; the frozen ones enter as a remnant, a fresh uncertainty per join

**Why.** The pointwise side over all end faces (`HandoverSide`) is dominated by frozen (ordered) faces, where a twist
costs about `(1/g²) L/T`; in the continuum that is most likely false. The reformulation quantifies over **running**
outsides only and charges the others as a remnant.

**Definitions.**
* `twistCertOn N K R e u`: `‖Z_e‖ ≤ u Z_0` for the end-face pairs in the running set `R` only.
* `DiagInvariant N R`: the running set is invariant under the centre action on both faces (true for any set defined by
  the faces' own action density, `windowFaces`, since the face plaquettes are centre-invariant in the slab geometry).
* **`RemnantMass N Ka Kb Ra Rb Rab ε`**: for every running outer pair `(x, y) ∈ Rab` of the joined slab, the shared
  faces `z` that are not running (`(x, z) ∉ Ra` or `(z, y) ∉ Rb`) carry at most the fraction `ε` of the joined neutral
  weight: `Σ_{z bad} Z_0^a(x, z) Z_0^b(z, y) ≤ ε Z_0^{ab}(x, y)`. In the slab geometry `Z_0^a Z_0^b / Z_0^{ab}` is exactly
  the neutral-sector conditional law of the shared face given the outer faces (`kjoin_sec0N`), so `ε` is a **conditional
  probability that the shared face is not running**. Instantiable through `runPairs`, `windowFaces` and
  `remnant_of_faces` (faces whose boundary action density lies in a typical window).

**Theorems.**
* **`elecN_running`** (box, seam cost `δ`): running factors `ρa`, `ρb`, remnant `ε`, seam `δ`: the join has running
  factor `(1 + δ)(ρa ρb + ε) + δ` on `Rab`. The non-running shared faces are bounded by the trivial factor 1
  (`twistCertN_one`; every factor is at most 1), so they contribute at most `ε`.
* `elecN_running_slab`: the slab geometry (`δ = 0`): factor `ρa ρb + ε`.
* **`runningTransport_slab`**, **`runningTransport`**: the chain over running sets is a `TransportsCert` of
  `Transport.lean` with factor `ρ` and **fresh uncertainty `r = ε`** (slab), resp. factor `(1 + δ) ρ` and
  `r = (1 + δ) ε + δ` (box).
* `ym_running_bridge`: O1 at `μ` after `n` joins once `μ (θ'^n u₀ + r/(1 − θ')) ≤ 1`.
* **`three_slabs_running`**, `three_slabs_running_num`: three slabs on the running electric side with remnant
  `ε ≤ 1/20` per join: O1 for every `μ ≤ 7` (transported value `θ³ + (1 + θ) ε`).
* **`three_boxes_running`**, `three_boxes_running_num`: in a box, remnant and seam cost each `≤ 1/50` per join: O1 for
  every `μ ≤ 7`.
* **`HandoverSideRunning`** (named, **open**) and the assemblies **`O1_slab_running`**, **`O1_box_running`**:
  O1 = `HandoverSideRunning` + remnant + seam, with explicit thresholds.

**Claim discipline.** Not O1. `HandoverSideRunning` is open; the remnant bound `ε` (a large-deviation statement for the
face action density under the conditional measure) is open uniformly in the cutoff; the seam bound is as in
`ElectricSUNPress`. The conclusions hold for running outer pairs only: O1 here is O1 over running outsides.
-/

open Finset ZMod

open scoped Classical

noncomputable section

namespace ProofPhase.Unified

/-! ## 1. Running sets, the remnant, and a concrete instance -/

/-- **The electric factor over running outsides only.** -/
def twistCertOn (N : ℕ) [NeZero N] {X Y : Type*} [AddAction (ZMod N) Y] (K : X → Y → ℝ) (R : Set (X × Y))
    (e : ZMod N) (u : ℝ) : Prop :=
  ∀ x y, (x, y) ∈ R → ‖secN K e x y‖ ≤ u * sec0N N K x y

/-- A running set invariant under the centre action on both faces. -/
def DiagInvariant (N : ℕ) {Z Y : Type*} [AddAction (ZMod N) Z] [AddAction (ZMod N) Y] (R : Set (Z × Y)) : Prop :=
  ∀ (k : ZMod N) z y, (z, y) ∈ R → (k +ᵥ z, k +ᵥ y) ∈ R

/-- **The remnant**: for every running outer pair, the non-running shared faces carry at most the fraction `ε` of the
joined neutral weight (a conditional probability that the shared face is not running). -/
def RemnantMass (N : ℕ) [NeZero N] {X Z Y : Type*} [Fintype Z] [AddAction (ZMod N) Z] [AddAction (ZMod N) Y]
    (Ka : X → Z → ℝ) (Kb : Z → Y → ℝ) (Ra : Set (X × Z)) (Rb : Set (Z × Y)) (Rab : Set (X × Y)) (ε : ℝ) : Prop :=
  ∀ x y, (x, y) ∈ Rab →
    ∑ z ∈ univ.filter (fun z => ¬((x, z) ∈ Ra ∧ (z, y) ∈ Rb)), sec0N N Ka x z * sec0N N Kb z y ≤
      ε * sec0N N (kjoin Ka Kb) x y

/-- Running pairs from running faces: both end faces running. -/
def runPairs {X Y : Type*} (Tx : Set X) (Ty : Set Y) : Set (X × Y) := {p | p.1 ∈ Tx ∧ p.2 ∈ Ty}

/-- A concrete running set of faces: boundary action density in a typical window `[lo, hi]`. -/
def windowFaces {Y : Type*} (dens : Y → ℝ) (lo hi : ℝ) : Set Y := {y | lo ≤ dens y ∧ dens y ≤ hi}

section Basic

variable {N : ℕ} [NeZero N] {X Y Z : Type*} [Fintype Z] [AddAction (ZMod N) Y] [AddAction (ZMod N) Z]

omit [NeZero N] [Fintype Z] in
/-- Running pairs of centre-invariant face sets are centre-invariant. -/
theorem diagInvariant_runPairs {Tz : Set Z} {Ty : Set Y} (hz : ∀ (k : ZMod N) z, z ∈ Tz → k +ᵥ z ∈ Tz)
    (hy : ∀ (k : ZMod N) y, y ∈ Ty → k +ᵥ y ∈ Ty) : DiagInvariant N (runPairs Tz Ty) :=
  fun k z y h => ⟨hz k z h.1, hy k y h.2⟩

omit [NeZero N] [Fintype Z] [AddAction (ZMod N) Z] in
/-- A window of a centre-invariant density (the face's own plaquettes) is centre-invariant. -/
theorem windowFaces_invariant {dens : Y → ℝ} (hd : ∀ (k : ZMod N) y, dens (k +ᵥ y) = dens y) {lo hi : ℝ}
    (k : ZMod N) (y : Y) (h : y ∈ windowFaces dens lo hi) : k +ᵥ y ∈ windowFaces dens lo hi := by
  unfold windowFaces at *; rw [Set.mem_ofPred_eq, hd]; exact h

/-- **Instantiating the remnant from running faces**: if, for running outer faces, the non-running shared faces carry
at most `ε` of the joined neutral weight, the remnant bound holds for the running pairs. -/
theorem remnant_of_faces {Ka : X → Z → ℝ} {Kb : Z → Y → ℝ} {Tx : Set X} {Tz : Set Z} {Ty : Set Y} {ε : ℝ}
    (h : ∀ x y, x ∈ Tx → y ∈ Ty →
      ∑ z ∈ univ.filter (fun z => z ∉ Tz), sec0N N Ka x z * sec0N N Kb z y ≤ ε * sec0N N (kjoin Ka Kb) x y) :
    RemnantMass N Ka Kb (runPairs Tx Tz) (runPairs Tz Ty) (runPairs Tx Ty) ε := by
  intro x y hxy
  have hx : x ∈ Tx := hxy.1
  have hy : y ∈ Ty := hxy.2
  have hf : univ.filter (fun z => ¬((x, z) ∈ runPairs Tx Tz ∧ (z, y) ∈ runPairs Tz Ty)) =
      univ.filter (fun z => z ∉ Tz) := by
    ext z
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro h hz; exact h ⟨⟨hx, hz⟩, hz, hy⟩
    · intro h hg; exact h hg.1.2
  rw [hf]
  exact h x y hx hy

omit [Fintype Z] [AddAction (ZMod N) Z] in
/-- A running certificate may be raised (nonnegative kernel). -/
theorem twistCertOn_mono {K : X → Y → ℝ} (hK : ∀ x y, 0 ≤ K x y) {R : Set (X × Y)} {e : ZMod N} {u v : ℝ}
    (h : twistCertOn N K R e u) (huv : u ≤ v) : twistCertOn N K R e v :=
  fun x y hxy => (h x y hxy).trans (mul_le_mul_of_nonneg_right huv (sec0N_nonneg hK x y))

omit [Fintype Z] [AddAction (ZMod N) Z] in
/-- An all-outsides certificate is a running one for every running set. -/
theorem twistCertOn_of_twistCertN {K : X → Y → ℝ} {e : ZMod N} {u : ℝ} (h : twistCertN N K e u) (R : Set (X × Y)) :
    twistCertOn N K R e u :=
  fun x y _ => h x y

end Basic

/-! ## 2. The join over running outsides -/

section Join

variable {N : ℕ} [NeZero N] {X Y Z : Type*} [Fintype X] [AddAction (ZMod N) X] [AddAction (ZMod N) Y]

omit [Fintype X] in
/-- The centre average keeps a running factor on a centre-invariant running set. -/
theorem twistCertOn_ksym {K : X → Y → ℝ} {R : Set (X × Y)} (hR : DiagInvariant N R) {e : ZMod N} {u : ℝ}
    (h : twistCertOn N K R e u) : twistCertOn N (ksym N K) R e u := by
  intro z y hzy
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [secN_ksym, sec0N_ksym, norm_mul, norm_inv, Complex.norm_natCast, mul_left_comm, mul_sum]
  exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun j _ => h _ _ (hR j z y hzy)))
    (inv_nonneg.2 hN.le)

omit [Fintype X] in
/-- The neutral sector of the centre average is within the factor `1 + δ`. -/
theorem sec0N_ksym_le {K : X → Y → ℝ} {δ : ℝ} (hd : SeamDefect N K δ) (z : X) (y : Y) :
    sec0N N (ksym N K) z y ≤ (1 + δ) * sec0N N K z y := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  unfold sec0N
  calc (N : ℝ)⁻¹ * ∑ k : ZMod N, ksym N K z (k +ᵥ y) ≤ (N : ℝ)⁻¹ * ∑ k : ZMod N, (1 + δ) * K z (k +ᵥ y) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => ksym_le hd z _) (inv_nonneg.2 hN.le)
    _ = (1 + δ) * ((N : ℝ)⁻¹ * ∑ k : ZMod N, K z (k +ᵥ y)) := by rw [← mul_sum]; ring

/-- **The join over running outsides (box, seam cost `δ`).** Running factors `ρa ≥ 0` on `Ra`, `ρb ≥ 0` on a
centre-invariant `Rb`, remnant `ε` and seam cost `δ ≥ 0` of the added layer: the join has running factor
`(1 + δ)(ρa ρb + ε) + δ` on `Rab`. The frozen shared faces are bounded by the trivial factor 1. -/
theorem elecN_running {Z : Type*} [Fintype Z] {Ka : Z → X → ℝ} {Kb : X → Y → ℝ} (ha0 : ∀ z x, 0 ≤ Ka z x)
    (hb0 : ∀ x y, 0 ≤ Kb x y) {Ra : Set (Z × X)} {Rb : Set (X × Y)} {Rab : Set (Z × Y)} (hRb : DiagInvariant N Rb)
    {δ ε : ℝ} (hδ0 : 0 ≤ δ) (hd : SeamDefect N Kb δ) (hε : RemnantMass N Ka Kb Ra Rb Rab ε) {e : ZMod N}
    {ρa ρb : ℝ} (hρa : 0 ≤ ρa) (hρb : 0 ≤ ρb) (ha : twistCertOn N Ka Ra e ρa) (hb : twistCertOn N Kb Rb e ρb) :
    twistCertOn N (kjoin Ka Kb) Rab e ((1 + δ) * (ρa * ρb + ε) + δ) := by
  intro z y hzy
  set Kbs := ksym N Kb with hKbs
  have hbs0 : ∀ x y, 0 ≤ Kbs x y := ksym_nonneg hb0
  have hbsC := centreSym_ksym (N := N) Kb
  have hbs := twistCertOn_ksym hRb hb
  have ha1 := twistCertN_one (N := N) ha0 e
  have hbs1 := twistCertN_one (N := N) hbs0 e
  have hρ : 0 ≤ ρa * ρb := mul_nonneg hρa hρb
  set S := sec0N N (kjoin Ka Kb) z y with hS
  have hS0 : 0 ≤ S := sec0N_nonneg (kjoin_nonneg ha0 hb0) z y
  set bad : Finset X := univ.filter (fun x => ¬((z, x) ∈ Ra ∧ (x, y) ∈ Rb)) with hbad
  -- (A) the centre-symmetric part
  have hA : ‖secN (kjoin Ka Kbs) e z y‖ ≤
      ρa * ρb * ∑ x, sec0N N Ka z x * sec0N N Kbs x y + ∑ x ∈ bad, sec0N N Ka z x * sec0N N Kbs x y := by
    rw [kjoin_secN hbsC Ka e z y]
    refine (norm_sum_le _ _).trans ?_
    rw [sum_filter, mul_sum, ← sum_add_distrib]
    refine sum_le_sum fun x _ => ?_
    rw [norm_mul]
    have p0 : 0 ≤ sec0N N Ka z x * sec0N N Kbs x y := mul_nonneg (sec0N_nonneg ha0 z x) (sec0N_nonneg hbs0 x y)
    by_cases hg : (z, x) ∈ Ra ∧ (x, y) ∈ Rb
    · rw [ite_eq_right (not_not.2 hg), add_zero]
      calc ‖secN Ka e z x‖ * ‖secN Kbs e x y‖ ≤ (ρa * sec0N N Ka z x) * (ρb * sec0N N Kbs x y) :=
            mul_le_mul (ha z x hg.1) (hbs x y hg.2) (norm_nonneg _) ((norm_nonneg _).trans (ha z x hg.1))
        _ = ρa * ρb * (sec0N N Ka z x * sec0N N Kbs x y) := by ring
    · rw [ite_eq_left hg]
      have := mul_le_mul (ha1 z x) (hbs1 x y) (norm_nonneg _) ((norm_nonneg _).trans (ha1 z x))
      rw [one_mul, one_mul] at this
      nlinarith [mul_nonneg hρ p0]
  -- the neutral totals with the centre average
  have hT : ∑ x, sec0N N Ka z x * sec0N N Kbs x y ≤ (1 + δ) * S := by
    rw [← kjoin_sec0N hbsC Ka z y]
    exact sec0N_kjoin_le ha0 (ksym_le hd) z y
  have hB : ∑ x ∈ bad, sec0N N Ka z x * sec0N N Kbs x y ≤ (1 + δ) * (ε * S) := by
    calc ∑ x ∈ bad, sec0N N Ka z x * sec0N N Kbs x y ≤ ∑ x ∈ bad, (1 + δ) * (sec0N N Ka z x * sec0N N Kb x y) :=
          sum_le_sum fun x _ => by
            have := mul_le_mul_of_nonneg_left (sec0N_ksym_le hd x y) (sec0N_nonneg (N := N) ha0 z x)
            linarith
      _ = (1 + δ) * ∑ x ∈ bad, sec0N N Ka z x * sec0N N Kb x y := by rw [mul_sum]
      _ ≤ (1 + δ) * (ε * S) := mul_le_mul_of_nonneg_left (hε z y hzy) (by linarith)
  -- (B) the seam part
  have hdiff := norm_secN_sub_le (kjoin_sub_le ha0 (ksym_sub_le hd)) e z y
  calc ‖secN (kjoin Ka Kb) e z y‖
      ≤ ‖secN (kjoin Ka Kbs) e z y‖ + ‖secN (kjoin Ka Kb) e z y - secN (kjoin Ka Kbs) e z y‖ := by
        have := norm_add_le (secN (kjoin Ka Kbs) e z y) (secN (kjoin Ka Kb) e z y - secN (kjoin Ka Kbs) e z y)
        rwa [add_sub_cancel] at this
    _ ≤ (ρa * ρb * ((1 + δ) * S) + (1 + δ) * (ε * S)) + δ * S := by
        refine add_le_add (hA.trans (add_le_add (mul_le_mul_of_nonneg_left hT hρ) hB)) hdiff
    _ = ((1 + δ) * (ρa * ρb + ε) + δ) * S := by ring

/-- **The join over running outsides, slab geometry**: factor `ρa ρb + ε`. -/
theorem elecN_running_slab {Z : Type*} [Fintype Z] {Ka : Z → X → ℝ} {Kb : X → Y → ℝ} (ha0 : ∀ z x, 0 ≤ Ka z x)
    (hb0 : ∀ x y, 0 ≤ Kb x y) (hsym : CentreSym N Kb) {Ra : Set (Z × X)} {Rb : Set (X × Y)} {Rab : Set (Z × Y)}
    (hRb : DiagInvariant N Rb) {ε : ℝ} (hε : RemnantMass N Ka Kb Ra Rb Rab ε) {e : ZMod N} {ρa ρb : ℝ}
    (hρa : 0 ≤ ρa) (hρb : 0 ≤ ρb) (ha : twistCertOn N Ka Ra e ρa) (hb : twistCertOn N Kb Rb e ρb) :
    twistCertOn N (kjoin Ka Kb) Rab e (ρa * ρb + ε) := by
  have h := elecN_running ha0 hb0 hRb le_rfl (seamDefect_zero_iff.2 hsym) hε hρa hρb ha hb
  simpa using h

end Join

/-! ## 3. The remnant is a fresh uncertainty of the transport theorem -/

section Transport

variable {N : ℕ} [NeZero N] {X : Type*} [Fintype X] [AddAction (ZMod N) X]

/-- **Box chain over running outsides**: factor `(1 + δ) ρ`, fresh uncertainty `r = (1 + δ) ε + δ` per join. -/
theorem runningTransport {T : ℕ → X → X → ℝ} (hT : ∀ n x y, 0 ≤ T n x y) {Rc Rl : ℕ → Set (X × X)}
    (hRl : ∀ n, DiagInvariant N (Rl (n + 1))) {δ ε ρ : ℝ} (hδ0 : 0 ≤ δ) (hε0 : 0 ≤ ε)
    (hd : ∀ n, SeamDefect N (T (n + 1)) δ)
    (hε : ∀ n, RemnantMass N (kchain T n) (T (n + 1)) (Rc n) (Rl (n + 1)) (Rc (n + 1)) ε) {e : ZMod N}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ n, twistCertOn N (T (n + 1)) (Rl (n + 1)) e ρ) (n : ℕ) :
    TransportsCert (fun i u => 0 ≤ u ∧ twistCertOn N (kchain T i) (Rc i) e u) (fun _ => (1 + δ) * ρ)
      (fun _ => (1 + δ) * ε + δ) n := by
  intro i _ u ⟨hu0, hu⟩
  refine ⟨by positivity, ?_⟩
  have h := elecN_running (kchain_nonneg hT i) (hT (i + 1)) (hRl i) hδ0 (hd i) (hε i) hu0 hρ0 hu (hρ i)
  rw [show (1 + δ) * (u * ρ + ε) + δ = (1 + δ) * ρ * u + ((1 + δ) * ε + δ) by ring] at h
  exact h

/-- **Slab chain over running outsides: the remnant is exactly the fresh uncertainty `r = ε`**, with factor `ρ`. -/
theorem runningTransport_slab {T : ℕ → X → X → ℝ} (hT : ∀ n x y, 0 ≤ T n x y) (hsym : ∀ n, CentreSym N (T n))
    {Rc Rl : ℕ → Set (X × X)} (hRl : ∀ n, DiagInvariant N (Rl (n + 1))) {ε ρ : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ n, RemnantMass N (kchain T n) (T (n + 1)) (Rc n) (Rl (n + 1)) (Rc (n + 1)) ε) {e : ZMod N}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ n, twistCertOn N (T (n + 1)) (Rl (n + 1)) e ρ) (n : ℕ) :
    TransportsCert (fun i u => 0 ≤ u ∧ twistCertOn N (kchain T i) (Rc i) e u) (fun _ => ρ) (fun _ => ε) n := by
  intro i _ u ⟨hu0, hu⟩
  refine ⟨by positivity, ?_⟩
  have h := elecN_running_slab (kchain_nonneg hT i) (hT (i + 1)) (hsym (i + 1)) (hRl i) (hε i) hu0 hρ0 hu (hρ i)
  rw [show u * ρ + ε = ρ * u + ε by ring] at h
  exact h

/-- **The bridge over running outsides**: first factor `u₀` on `Rc 0`, factor `θ' < 1` and fresh uncertainty `r` per
join (`r = ε` in a slab, `(1 + δ) ε + δ` in a box): O1 on the running pairs `Rc n` once
`μ (θ'^n u₀ + r/(1 − θ')) ≤ 1`. -/
theorem ym_running_bridge {T : ℕ → X → X → ℝ} (hT : ∀ n x y, 0 ≤ T n x y) {Rc : ℕ → Set (X × X)} {e : ZMod N}
    {θ r u₀ μ : ℝ} {n : ℕ}
    (htr : TransportsCert (fun i u => 0 ≤ u ∧ twistCertOn N (kchain T i) (Rc i) e u) (fun _ => θ) (fun _ => r) n)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hr : 0 ≤ r) (hu0 : 0 ≤ u₀) (h0 : twistCertOn N (T 0) (Rc 0) e u₀) (hμ0 : 0 ≤ μ)
    (hmargin : μ * (θ ^ n * u₀ + r / (1 - θ)) ≤ 1) (x y : X) (hxy : (x, y) ∈ Rc n) :
    μ * ‖secN (kchain T n) e x y‖ ≤ sec0N N (kchain T n) x y := by
  have hc := transport_cert htr (show 0 ≤ u₀ ∧ twistCertOn N (kchain T 0) (Rc 0) e u₀ from ⟨hu0, h0⟩)
  have hb : acc (fun _ => θ) (fun _ => r) u₀ n ≤ θ ^ n * u₀ + r / (1 - θ) := by
    rw [acc_const]
    have := geom_tail_le hθ0 hθ1 hr (r := fun _ => r) (fun _ => le_refl r) n
    linarith
  have hcert := twistCertOn_mono (kchain_nonneg hT n) hc.2 hb
  have h0' := sec0N_nonneg (N := N) (kchain_nonneg hT n) x y
  calc μ * ‖secN (kchain T n) e x y‖ ≤ μ * ((θ ^ n * u₀ + r / (1 - θ)) * sec0N N (kchain T n) x y) :=
        mul_le_mul_of_nonneg_left (hcert x y hxy) hμ0
    _ = (μ * (θ ^ n * u₀ + r / (1 - θ))) * sec0N N (kchain T n) x y := by ring
    _ ≤ 1 * sec0N N (kchain T n) x y := mul_le_mul_of_nonneg_right hmargin h0'
    _ = _ := one_mul _

end Transport

/-! ## 4. Three slabs and three boxes over running outsides, with explicit thresholds -/

section Three

variable {N : ℕ} [NeZero N] {X : Type*} [Fintype X] [AddAction (ZMod N) X]

/-- Three slabs, running factor `θ` each, remnant `ε` per join: `θ³ + θ ε + ε`. -/
def threeSlabRun (θ ε : ℝ) : ℝ := (θ * θ + ε) * θ + ε

/-- Three boxes, running factor `θ`, remnant `ε`, seam cost `δ` per join. -/
def threeBoxRun (θ ε δ : ℝ) : ℝ := (1 + δ) * (((1 + δ) * (θ * θ + ε) + δ) * θ + ε) + δ

omit [Fintype X] in
theorem O1_of_runCert {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y) {R : Set (X × X)} {e : ZMod N} {u μ : ℝ}
    (h : twistCertOn N K R e u) (hμ0 : 0 ≤ μ) (hm : μ * u ≤ 1) (x y : X) (hxy : (x, y) ∈ R) :
    μ * ‖secN K e x y‖ ≤ sec0N N K x y := by
  have h0 := sec0N_nonneg (N := N) hK x y
  calc μ * ‖secN K e x y‖ ≤ μ * (u * sec0N N K x y) := mul_le_mul_of_nonneg_left (h x y hxy) hμ0
    _ = (μ * u) * sec0N N K x y := by ring
    _ ≤ 1 * sec0N N K x y := mul_le_mul_of_nonneg_right hm h0
    _ = _ := one_mul _

/-- **Three slabs over running outsides.** Running factor `θ ≥ 0` for each slab, the last two centre-symmetric with
centre-invariant running sets, remnant `ε ≥ 0` at each of the two joins: O1 on the running pairs `R₁₂₃` once
`μ · threeSlabRun θ ε ≤ 1`. -/
theorem three_slabs_running {K₁ K₂ K₃ : X → X → ℝ} (hK₁ : ∀ x y, 0 ≤ K₁ x y) (hK₂ : ∀ x y, 0 ≤ K₂ x y)
    (hK₃ : ∀ x y, 0 ≤ K₃ x y) (hs₂ : CentreSym N K₂) (hs₃ : CentreSym N K₃) {R₁ R₂ R₃ R₁₂ R₁₂₃ : Set (X × X)}
    (hR₂ : DiagInvariant N R₂) (hR₃ : DiagInvariant N R₃) {θ ε : ℝ} (hθ0 : 0 ≤ θ) (hε0 : 0 ≤ ε)
    (hε₁₂ : RemnantMass N K₁ K₂ R₁ R₂ R₁₂ ε) (hε₁₂₃ : RemnantMass N (kjoin K₁ K₂) K₃ R₁₂ R₃ R₁₂₃ ε) {e : ZMod N}
    (h₁ : twistCertOn N K₁ R₁ e θ) (h₂ : twistCertOn N K₂ R₂ e θ) (h₃ : twistCertOn N K₃ R₃ e θ) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hm : μ * threeSlabRun θ ε ≤ 1) (x y : X) (hxy : (x, y) ∈ R₁₂₃) :
    μ * ‖secN (kjoin (kjoin K₁ K₂) K₃) e x y‖ ≤ sec0N N (kjoin (kjoin K₁ K₂) K₃) x y := by
  have c₁₂ := elecN_running_slab hK₁ hK₂ hs₂ hR₂ hε₁₂ hθ0 hθ0 h₁ h₂
  have c := elecN_running_slab (kjoin_nonneg hK₁ hK₂) hK₃ hs₃ hR₃ hε₁₂₃ (by positivity) hθ0 c₁₂ h₃
  exact O1_of_runCert (kjoin_nonneg (kjoin_nonneg hK₁ hK₂) hK₃) c hμ0 hm x y hxy

/-- **Three boxes over running outsides**, seam cost `δ` and remnant `ε` at each join. -/
theorem three_boxes_running {K₁ K₂ K₃ : X → X → ℝ} (hK₁ : ∀ x y, 0 ≤ K₁ x y) (hK₂ : ∀ x y, 0 ≤ K₂ x y)
    (hK₃ : ∀ x y, 0 ≤ K₃ x y) {R₁ R₂ R₃ R₁₂ R₁₂₃ : Set (X × X)} (hR₂ : DiagInvariant N R₂)
    (hR₃ : DiagInvariant N R₃) {θ ε δ : ℝ} (hθ0 : 0 ≤ θ) (hε0 : 0 ≤ ε) (hδ0 : 0 ≤ δ) (hd₂ : SeamDefect N K₂ δ)
    (hd₃ : SeamDefect N K₃ δ) (hε₁₂ : RemnantMass N K₁ K₂ R₁ R₂ R₁₂ ε)
    (hε₁₂₃ : RemnantMass N (kjoin K₁ K₂) K₃ R₁₂ R₃ R₁₂₃ ε) {e : ZMod N} (h₁ : twistCertOn N K₁ R₁ e θ)
    (h₂ : twistCertOn N K₂ R₂ e θ) (h₃ : twistCertOn N K₃ R₃ e θ) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hm : μ * threeBoxRun θ ε δ ≤ 1) (x y : X) (hxy : (x, y) ∈ R₁₂₃) :
    μ * ‖secN (kjoin (kjoin K₁ K₂) K₃) e x y‖ ≤ sec0N N (kjoin (kjoin K₁ K₂) K₃) x y := by
  have c₁₂ := elecN_running hK₁ hK₂ hR₂ hδ0 hd₂ hε₁₂ hθ0 hθ0 h₁ h₂
  have c := elecN_running (kjoin_nonneg hK₁ hK₂) hK₃ hR₃ hδ0 hd₃ hε₁₂₃ (by positivity) hθ0 c₁₂ h₃
  exact O1_of_runCert (kjoin_nonneg (kjoin_nonneg hK₁ hK₂) hK₃) c hμ0 hm x y hxy

theorem sqrt_two_le_num : √2 ≤ 1.4143 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num

/-- **Remnant threshold, slab**: at the self-dual factor, `ε ≤ 1/20` per join leaves O1 for every `μ ≤ 7`
(`threeSlabRun (√2 − 1) (1/20) ≈ 0.1418`, margin to `1/7 = 0.1429`). -/
theorem three_slabs_running_num {ε μ : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 20) (hμ : μ ≤ 7) :
    μ * threeSlabRun (√2 - 1) ε ≤ 1 := by
  have hs := sqrt_two_le_num
  have ht0 : 0 ≤ √2 - 1 := sqrt_two_sub_one_pos.le
  set t := √2 - 1 with htdef
  have ht : t ≤ 0.4143 := by rw [htdef]; linarith
  have htt : t * t ≤ 0.4143 * 0.4143 := mul_le_mul ht ht ht0 (by norm_num)
  have h2 : (t * t + ε) * t ≤ (0.4143 * 0.4143 + 0.05) * 0.4143 :=
    mul_le_mul (by linarith) ht ht0 (by norm_num)
  have hE : threeSlabRun t ε ≤ 0.1419 := by unfold threeSlabRun; norm_num at h2 ⊢; linarith
  have hE0 : 0 ≤ threeSlabRun t ε := by unfold threeSlabRun; positivity
  rcases le_or_gt 0 μ with hμ0 | hμ0
  · calc μ * threeSlabRun t ε ≤ 7 * 0.1419 := mul_le_mul hμ hE hE0 (by norm_num)
      _ ≤ 1 := by norm_num
  · nlinarith

/-- **Remnant and seam thresholds, box**: `ε ≤ 1/50` and `δ ≤ 1/50` per join leave O1 for every `μ ≤ 7`
(`threeBoxRun (√2 − 1) (1/50) (1/50) ≈ 0.1314`). -/
theorem three_boxes_running_num {ε δ μ : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 50) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 50)
    (hμ : μ ≤ 7) : μ * threeBoxRun (√2 - 1) ε δ ≤ 1 := by
  have hs := sqrt_two_le_num
  have ht0 : 0 ≤ √2 - 1 := sqrt_two_sub_one_pos.le
  set t := √2 - 1 with htdef
  have ht : t ≤ 0.4143 := by rw [htdef]; linarith
  have h1 : 1 + δ ≤ 1.02 := by linarith
  have htt : t * t ≤ 0.4143 * 0.4143 := mul_le_mul ht ht ht0 (by norm_num)
  have hu2 : (1 + δ) * (t * t + ε) + δ ≤ 1.02 * (0.4143 * 0.4143 + 0.02) + 0.02 := by
    have := mul_le_mul h1 (show t * t + ε ≤ 0.4143 * 0.4143 + 0.02 by linarith) (by positivity) (by norm_num)
    linarith
  have hu20 : 0 ≤ (1 + δ) * (t * t + ε) + δ := by positivity
  have h3 : ((1 + δ) * (t * t + ε) + δ) * t + ε ≤ (1.02 * (0.4143 * 0.4143 + 0.02) + 0.02) * 0.4143 + 0.02 := by
    have := mul_le_mul hu2 ht ht0 (by norm_num); linarith
  have h30 : 0 ≤ ((1 + δ) * (t * t + ε) + δ) * t + ε := by positivity
  have h4 : (1 + δ) * (((1 + δ) * (t * t + ε) + δ) * t + ε) ≤
      1.02 * ((1.02 * (0.4143 * 0.4143 + 0.02) + 0.02) * 0.4143 + 0.02) := mul_le_mul h1 h3 h30 (by norm_num)
  have hE : threeBoxRun t ε δ ≤ 0.1315 := by unfold threeBoxRun; norm_num at h4 ⊢; linarith
  have hE0 : 0 ≤ threeBoxRun t ε δ := by unfold threeBoxRun; positivity
  rcases le_or_gt 0 μ with hμ0 | hμ0
  · calc μ * threeBoxRun t ε δ ≤ 7 * 0.1315 := mul_le_mul hμ hE hE0 (by norm_num)
      _ ≤ 1 := by norm_num
  · nlinarith

end Three

/-! ## 5. The named hypothesis over running outsides; O1 = it + remnant + seam -/

section Assembly

variable {N : ℕ} [NeZero N] {ι : Type*} {Xf : ι → Type*} [∀ i, Fintype (Xf i)] [∀ i, AddAction (ZMod N) (Xf i)]

/-- **The pointwise electric side over running outsides, uniform in the cutoff** (named; **open**). For every cutoff
`i`, every nontrivial sector and every running end-face pair `(x, y) ∈ R i`, the hand-over slab has
`‖Z_e‖ ≤ (√2 − 1) Z_0`. Frozen outsides are not quantified over. -/
def HandoverSideRunning (N : ℕ) [NeZero N] {ι : Type*} {Xf : ι → Type*} [∀ i, AddAction (ZMod N) (Xf i)]
    (Kh : ∀ i, Xf i → Xf i → ℝ) (R : ∀ i, Set (Xf i × Xf i)) : Prop :=
  ∀ i (e : ZMod N), e ≠ 0 → twistCertOn N (Kh i) (R i) e (√2 - 1)

omit [∀ i, Fintype (Xf i)] in
/-- The all-outsides side implies the running side for every running set. -/
theorem handoverSideRunning_of_handoverSide {Kh : ∀ i, Xf i → Xf i → ℝ} (h : HandoverSide N Kh)
    (R : ∀ i, Set (Xf i × Xf i)) : HandoverSideRunning N Kh R :=
  fun i e he => twistCertOn_of_twistCertN (h i e he) (R i)

/-- **O1, slab geometry, over running outsides**: the hand-over slab `Kh i` (centre-symmetric) on the running electric
side over a centre-invariant running set `R i`, remnants at most `ε ≤ 1/20` at the two joins (outer running sets
`R₂ i`, `R₃ i` of the joined slabs): O1 at `3 L_h` on `R₃ i` for every `μ ≤ 7`, every cutoff, every nontrivial sector. -/
theorem O1_slab_running {Kh : ∀ i, Xf i → Xf i → ℝ} (hK : ∀ i x y, 0 ≤ Kh i x y) (hs : ∀ i, CentreSym N (Kh i))
    {R R₂ R₃ : ∀ i, Set (Xf i × Xf i)} (hR : ∀ i, DiagInvariant N (R i)) (h : HandoverSideRunning N Kh R) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 20) (hε₂ : ∀ i, RemnantMass N (Kh i) (Kh i) (R i) (R i) (R₂ i) ε)
    (hε₃ : ∀ i, RemnantMass N (kjoin (Kh i) (Kh i)) (Kh i) (R₂ i) (R i) (R₃ i) ε) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : μ ≤ 7) (i : ι) {e : ZMod N} (he : e ≠ 0) (x y : Xf i) (hxy : (x, y) ∈ R₃ i) :
    μ * ‖secN (kpow (Kh i) 2) e x y‖ ≤ sec0N N (kpow (Kh i) 2) x y :=
  three_slabs_running (hK i) (hK i) (hK i) (hs i) (hs i) (hR i) (hR i) sqrt_two_sub_one_pos.le hε0 (hε₂ i) (hε₃ i)
    (h i e he) (h i e he) (h i e he) hμ0 (three_slabs_running_num hε0 hε hμ) x y hxy

/-- **O1, box geometry, over running outsides = `HandoverSideRunning` + remnant + seam.** Three box layers per cutoff
on the running electric side over centre-invariant running sets, remnant `ε ≤ 1/50` and seam cost `δ ≤ 1/50` at each
join: O1 at `3 L_h` on the running pairs for every `μ ≤ 7`, every cutoff, every nontrivial sector. -/
theorem O1_box_running {K₁ K₂ K₃ : ∀ i, Xf i → Xf i → ℝ} (hK₁ : ∀ i x y, 0 ≤ K₁ i x y)
    (hK₂ : ∀ i x y, 0 ≤ K₂ i x y) (hK₃ : ∀ i x y, 0 ≤ K₃ i x y) {R₁ R₂ R₃ R₁₂ R₁₂₃ : ∀ i, Set (Xf i × Xf i)}
    (hR₂ : ∀ i, DiagInvariant N (R₂ i)) (hR₃ : ∀ i, DiagInvariant N (R₃ i)) (h₁ : HandoverSideRunning N K₁ R₁)
    (h₂ : HandoverSideRunning N K₂ R₂) (h₃ : HandoverSideRunning N K₃ R₃) {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 50)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 50) (hd₂ : ∀ i, SeamDefect N (K₂ i) δ) (hd₃ : ∀ i, SeamDefect N (K₃ i) δ)
    (hε₁₂ : ∀ i, RemnantMass N (K₁ i) (K₂ i) (R₁ i) (R₂ i) (R₁₂ i) ε)
    (hε₁₂₃ : ∀ i, RemnantMass N (kjoin (K₁ i) (K₂ i)) (K₃ i) (R₁₂ i) (R₃ i) (R₁₂₃ i) ε) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : μ ≤ 7) (i : ι) {e : ZMod N} (he : e ≠ 0) (x y : Xf i) (hxy : (x, y) ∈ R₁₂₃ i) :
    μ * ‖secN (kjoin (kjoin (K₁ i) (K₂ i)) (K₃ i)) e x y‖ ≤ sec0N N (kjoin (kjoin (K₁ i) (K₂ i)) (K₃ i)) x y :=
  three_boxes_running (hK₁ i) (hK₂ i) (hK₃ i) (hR₂ i) (hR₃ i) sqrt_two_sub_one_pos.le hε0 hδ0 (hd₂ i) (hd₃ i)
    (hε₁₂ i) (hε₁₂₃ i) (h₁ i e he) (h₂ i e he) (h₃ i e he) hμ0 (three_boxes_running_num hε0 hε hδ0 hδ hμ) x y hxy

end Assembly

end ProofPhase.Unified
