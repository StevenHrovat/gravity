/-
The electric-SU(N) round, part 1: the boundary-uniform slab join for the `Z_N` twist of SU(N) (2026-11-23). Released
under Apache 2.0.

Note: `docs/unified/ELECTRIC-SUN.md`, section 2.
-/

import ProofPhase.Unified.TransportBridges
import ProofPhase.General.SUNTwistSectors
import Mathlib.Analysis.Normed.Ring.Finite

/-!
# Zero join loss for every SU(N): the `Z_N` sectors of a slab multiply under joining

**Setting (finite, abstract).** The centre of SU(N) is `Z_N`; it acts on a finite set of face configurations (`AddAction
(ZMod N) Y`: `k +ᵥ y` multiplies the `k`-links of the face at `x_k = c` by `ω^k`, `ω = e^{2πi/N}`). A slab is a
kernel `K x y` between its two end faces. The twisted slab `K x (k +ᵥ y)` carries the twist `ω^k` across the slab.
The **electric sector `e`** of the slab, at its far face, is the `Z_N` Fourier transform of the twisted slabs:
`secN K e x y = (1/N) Σ_k ω^{−ek} K x (k +ᵥ y)` (`= General.elecZ`, the transform of `SUNTwistSectors`). The neutral
sector is real: `sec0N N K x y = (1/N) Σ_k K x (k +ᵥ y)` (`secN_zero`). Joining two slabs through a shared face is
`kjoin Ka Kb x y = Σ_z Ka x z · Kb z y` (the face spaces may differ, for coarse-graining; `kjoin = kcomp` when they agree).

**Theorems.**
* **`kjoin_secN`**: if the second slab commutes with the centre action, `Kb (k +ᵥ z) (k +ᵥ y) = Kb z y` (`CentreSym`),
  then **each sector of the joined slab is the face sum of the products of that same sector**:
  `secN (Ka Kb) e = Σ_z secN Ka e · secN Kb e`. Sectors never mix across the shared face, for every `N` and every `e`.
* **`elecN_submul`**: pointwise electric factors per sector multiply: `‖secN Ka e‖ ≤ ρa · sec0N Ka` and
  `‖secN Kb e‖ ≤ ρb · sec0N Kb` at every end face give `‖secN (Ka Kb) e‖ ≤ ρa ρb · sec0N (Ka Kb)`. **Zero join loss in every
  sector of every SU(N).**
* `twistCertN_one`: every nonnegative kernel has factor 1 in every sector (the trivial certificate).
* **`sector_of_twistN`**: a pointwise twist ratio `K x (k +ᵥ y) ≥ c K x y` for every twist `k` and every end face gives
  `‖secN K e‖ ≤ rhoN N c · sec0N K` for every `e ≠ 0`, `rhoN N c = (N − 1)(1 − c)/(N − 1 + c)`. For `N = 2` this is
  `elec c` (`rhoN_two`), the sharp `Z_2` factor; for `N ≥ 3` it is a valid, not sharp, bound.
* `rhoN_le_of_cstar`: `rhoN N c ≤ √2 − 1` once `c ≥ cstarN N = (N − 1)(2 − √2)/(N − 2 + √2)` (`cstarN_two`:
  `cstarN 2 = √2 − 1`).
* **`three_slabsN_O1`**: three slabs, the last two centre-symmetric, each with sector-`e` factor at most `√2 − 1` at every
  end face: `μ ‖Z_e‖ ≤ Z_0` for every `μ ≤ 14`, every end face (O1 in sector form, sector by sector).
* `kchainN_elec`: `n + 1` centre-symmetric layers with factor `ρ`: `‖Z_e‖ ≤ ρ^{n+1} Z_0`.
* `secN_two_one`, `secN_two_zero`: for `N = 2` the sectors are `sec1`, `sec0` of `JoinLossSlab` with `Ω = (1 +ᵥ ·)`,
  so `elecN_submul` contains `elec_submul`.
* Instances `N = 2, 3, 5, 11` (`su2_slab_O1`, `su3_slab_O1`, `su5_slab_O1`, `su11_slab_O1`), each from the general
  theorem.

**When is a slab centre-symmetric?** Multiplying all `k`-links at `x_k = c` (end faces and interior) by the central
element `ω^j` leaves every Wilson plaquette invariant: a plaquette contains either none of these links or two, one as
`U` and one as `U†`, and `ω^j` is central. So `CentreSym` holds in the slab geometry (directions transverse to the
twist plane periodic) [classical lattice fact, not formalised for the gauge chain]. With fixed side outsides it fails at
the side collar; that is the seam of `ElectricSUNPress`.

**Claim discipline.** Not O1. The pointwise electric side (factor `≤ √2 − 1` at the hand-over slab for every end-face
outside, uniformly in the cutoff) is open. Finite face space; for compact `G` the same algebra holds with integrals.
-/

open Finset ZMod

noncomputable section

namespace ProofPhase.Unified

/-! ## 1. Definitions -/

/-- **The electric sector `e` of a slab** at its far face: `(1/N) Σ_k ω^{−ek} K x (k +ᵥ y)`. -/
def secN {N : ℕ} [NeZero N] {X Y : Type*} [AddAction (ZMod N) Y] (K : X → Y → ℝ) (e : ZMod N) (x : X) (y : Y) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k : ZMod N, (stdAddChar (-(k * e)) : ℂ) * (K x (k +ᵥ y) : ℂ)

/-- **The neutral sector** (real): `(1/N) Σ_k K x (k +ᵥ y)`. -/
def sec0N (N : ℕ) [NeZero N] {X Y : Type*} [AddAction (ZMod N) Y] (K : X → Y → ℝ) (x : X) (y : Y) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k : ZMod N, K x (k +ᵥ y)

/-- **A slab commutes with the centre action** (the slab geometry). -/
def CentreSym (N : ℕ) {Z Y : Type*} [AddAction (ZMod N) Z] [AddAction (ZMod N) Y] (K : Z → Y → ℝ) : Prop :=
  ∀ (k : ZMod N) z y, K (k +ᵥ z) (k +ᵥ y) = K z y

/-- Two slabs joined through a shared face (face spaces may differ). -/
def kjoin {X Z Y : Type*} [Fintype Z] (Ka : X → Z → ℝ) (Kb : Z → Y → ℝ) (x : X) (y : Y) : ℝ := ∑ z, Ka x z * Kb z y

/-- **The boundary-uniform electric factor in sector `e`** (certificate form): `‖Z_e‖ ≤ u Z_0` at every end face. -/
def twistCertN (N : ℕ) [NeZero N] {X Y : Type*} [AddAction (ZMod N) Y] (K : X → Y → ℝ) (e : ZMod N) (u : ℝ) : Prop :=
  ∀ x y, ‖secN K e x y‖ ≤ u * sec0N N K x y

/-- The `Z_N` factor from a pointwise twist ratio `c`. -/
def rhoN (N : ℕ) (c : ℝ) : ℝ := ((N : ℝ) - 1) * (1 - c) / ((N : ℝ) - 1 + c)

/-- The pointwise twist ratio that puts `rhoN` at the self-dual point `√2 − 1`. -/
def cstarN (N : ℕ) : ℝ := ((N : ℝ) - 1) * (2 - √2) / ((N : ℝ) - 2 + √2)

theorem kjoin_eq_kcomp {X : Type*} [Fintype X] (Ka Kb : X → X → ℝ) : kjoin Ka Kb = kcomp Ka Kb := rfl

/-! ## 2. The sector join -/

section Join

variable {N : ℕ} [NeZero N] {X Y Z : Type*} [Fintype Z] [AddAction (ZMod N) Y] [AddAction (ZMod N) Z]

/-- The centre action of `j` on a face, as a permutation. -/
def vaddPerm (j : ZMod N) : Equiv.Perm Z := ⟨(j +ᵥ ·), ((-j) +ᵥ ·), neg_vadd_vadd j, vadd_neg_vadd j⟩

omit [Fintype Z] [AddAction (ZMod N) Z] in
theorem secN_eq_elecZ (K : X → Y → ℝ) (e : ZMod N) (x : X) (y : Y) :
    secN K e x y = General.elecZ (fun k => K x (k +ᵥ y)) e := by
  rw [General.elecZ_eq]; rfl

omit [Fintype Z] [AddAction (ZMod N) Z] in
theorem secN_zero (K : X → Y → ℝ) (x : X) (y : Y) : secN K (0 : ZMod N) x y = (sec0N N K x y : ℂ) := by
  simp [secN, sec0N]

omit [Fintype Z] [AddAction (ZMod N) Z] in
theorem sec0N_nonneg {K : X → Y → ℝ} (hK : ∀ x y, 0 ≤ K x y) (x : X) (y : Y) : 0 ≤ sec0N N K x y :=
  mul_nonneg (by positivity) (sum_nonneg fun k _ => hK x _)

omit [AddAction (ZMod N) Z] in
theorem kjoin_nonneg {Ka : X → Z → ℝ} {Kb : Z → Y → ℝ} (ha : ∀ x z, 0 ≤ Ka x z) (hb : ∀ z y, 0 ≤ Kb z y) (x : X)
    (y : Y) : 0 ≤ kjoin Ka Kb x y :=
  sum_nonneg fun z _ => mul_nonneg (ha x z) (hb z y)

omit [NeZero N] in
/-- The shared-face sum after a twist of the first slab's far face equals the joined slab with the twist moved to its
far face, when the second slab is centre-symmetric. -/
theorem inner_shift {Kb : Z → Y → ℝ} (hb : CentreSym N Kb) (Ka : X → Z → ℝ) (j l : ZMod N) (x : X) (y : Y) :
    ∑ z, (Ka x (j +ᵥ z) : ℂ) * (Kb z (l +ᵥ y) : ℂ) = (kjoin Ka Kb x ((j + l) +ᵥ y) : ℂ) := by
  calc ∑ z, (Ka x (j +ᵥ z) : ℂ) * (Kb z (l +ᵥ y) : ℂ)
      = ∑ w, (Ka x w : ℂ) * (Kb w ((j + l) +ᵥ y) : ℂ) := by
        refine Fintype.sum_equiv (vaddPerm j) _ _ fun z => ?_
        show (Ka x (j +ᵥ z) : ℂ) * (Kb z (l +ᵥ y) : ℂ) = (Ka x (j +ᵥ z) : ℂ) * (Kb (j +ᵥ z) ((j + l) +ᵥ y) : ℂ)
        have hs := hb j z (l +ᵥ y)
        rw [vadd_vadd] at hs
        rw [hs]
    _ = _ := by unfold kjoin; push_cast; rfl

/-- **The sectors of a joined slab are face sums of products of the same sector** (second slab centre-symmetric). -/
theorem kjoin_secN {Kb : Z → Y → ℝ} (hb : CentreSym N Kb) (Ka : X → Z → ℝ) (e : ZMod N) (x : X) (y : Y) :
    secN (kjoin Ka Kb) e x y = ∑ z, secN Ka e x z * secN Kb e z y := by
  set ψ : ZMod N → ℂ := fun k => (stdAddChar (-(k * e)) : ℂ) with hψdef
  set G : ZMod N → ℂ := fun m => (kjoin Ka Kb x (m +ᵥ y) : ℂ) with hGdef
  have hψ : ∀ j l : ZMod N, ψ j * ψ l = ψ (j + l) := by
    intro j l; simp only [hψdef]; rw [← AddChar.map_add_eq_mul]; congr 1; ring
  have hpt : ∀ z, secN Ka e x z * secN Kb e z y =
      (N : ℂ)⁻¹ * (N : ℂ)⁻¹ * ∑ j, ∑ l, ψ j * ψ l * ((Ka x (j +ᵥ z) : ℂ) * (Kb z (l +ᵥ y) : ℂ)) := by
    intro z
    simp only [secN, hψdef]
    rw [mul_mul_mul_comm, sum_mul_sum]
    congr 1
    refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => by ring
  have hR : ∑ z, secN Ka e x z * secN Kb e z y = (N : ℂ)⁻¹ * (N : ℂ)⁻¹ * ∑ j, ∑ l, ψ (j + l) * G (j + l) := by
    rw [sum_congr rfl fun z _ => hpt z, ← mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    rw [← mul_sum, inner_shift hb Ka j l x y, hψ]
  have hshift : ∀ j : ZMod N, ∑ l, ψ (j + l) * G (j + l) = ∑ m, ψ m * G m := fun j =>
    Fintype.sum_equiv (Equiv.addLeft j) _ _ fun l => rfl
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  rw [hR, sum_congr rfl fun j _ => hshift j, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  simp only [secN, hGdef, hψdef]
  field_simp

/-- The neutral sector of a join (second slab centre-symmetric) is the face sum of the neutral sectors. -/
theorem kjoin_sec0N {Kb : Z → Y → ℝ} (hb : CentreSym N Kb) (Ka : X → Z → ℝ) (x : X) (y : Y) :
    sec0N N (kjoin Ka Kb) x y = ∑ z, sec0N N Ka x z * sec0N N Kb z y := by
  have h := kjoin_secN hb Ka 0 x y
  simp only [secN_zero] at h
  exact_mod_cast h

/-- **Zero join loss in every sector of every SU(N)**: pointwise electric factors per sector multiply under joining. -/
theorem elecN_submul {Ka : X → Z → ℝ} {Kb : Z → Y → ℝ} (hb : CentreSym N Kb) {e : ZMod N} {ρa ρb : ℝ}
    (ha : twistCertN N Ka e ρa) (hbb : twistCertN N Kb e ρb) : twistCertN N (kjoin Ka Kb) e (ρa * ρb) := by
  intro x y
  rw [kjoin_secN hb Ka e x y, kjoin_sec0N hb Ka x y]
  calc ‖∑ z, secN Ka e x z * secN Kb e z y‖ ≤ ∑ z, ‖secN Ka e x z * secN Kb e z y‖ := norm_sum_le _ _
    _ = ∑ z, ‖secN Ka e x z‖ * ‖secN Kb e z y‖ := by simp only [norm_mul]
    _ ≤ ∑ z, (ρa * sec0N N Ka x z) * (ρb * sec0N N Kb z y) := by
        refine sum_le_sum fun z _ => mul_le_mul (ha x z) (hbb z y) (norm_nonneg _) ?_
        exact (norm_nonneg _).trans (ha x z)
    _ = (ρa * ρb) * ∑ z, sec0N N Ka x z * sec0N N Kb z y := by rw [mul_sum]; congr 1; ext z; ring

omit [Fintype Z] [AddAction (ZMod N) Z] in
/-- **The trivial certificate**: a nonnegative kernel has factor 1 in every sector. -/
theorem twistCertN_one {K : X → Y → ℝ} (hK : ∀ x y, 0 ≤ K x y) (e : ZMod N) : twistCertN N K e 1 := by
  intro x y
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  unfold secN sec0N
  rw [norm_mul, one_mul, norm_inv, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hN.le)
  refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => ?_))
  rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_of_nonneg (hK x _)]

omit [Fintype Z] [AddAction (ZMod N) Z] in
/-- A certificate may be raised (nonnegative kernel). -/
theorem twistCertN_mono {K : X → Y → ℝ} (hK : ∀ x y, 0 ≤ K x y) {e : ZMod N} {u v : ℝ} (h : twistCertN N K e u)
    (huv : u ≤ v) : twistCertN N K e v :=
  fun x y => (h x y).trans (mul_le_mul_of_nonneg_right huv (sec0N_nonneg hK x y))

end Join

/-! ## 3. From a pointwise twist ratio to a sector factor -/

section Twist

variable {N : ℕ} [NeZero N] {X Y : Type*} [AddAction (ZMod N) Y]

theorem sum_stdAddChar_neg_mul {e : ZMod N} (he : e ≠ 0) : ∑ k : ZMod N, (stdAddChar (-(k * e)) : ℂ) = 0 := by
  have h := General.sum_char_mul (N := N) (-e)
  rw [ite_eq_right (neg_ne_zero.2 he)] at h
  rw [← h]
  exact sum_congr rfl fun k _ => by rw [mul_neg]

/-- **A pointwise twist ratio gives a sector factor**: `K x (k +ᵥ y) ≥ c K x y` for every twist `k` and every end face
gives `‖Z_e‖ ≤ rhoN N c · Z_0` for every `e ≠ 0`, `rhoN N c = (N − 1)(1 − c)/(N − 1 + c)`. -/
theorem sector_of_twistN {K : X → Y → ℝ} (hK : ∀ x y, 0 ≤ K x y) {c : ℝ} (hc0 : 0 < c)
    (hc : ∀ (k : ZMod N) x y, c * K x y ≤ K x (k +ᵥ y)) {e : ZMod N} (he : e ≠ 0) : twistCertN N K e (rhoN N c) := by
  intro x y
  set a : ZMod N → ℝ := fun k => K x (k +ᵥ y) with ha
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_min_image (univ : Finset (ZMod N)) a univ_nonempty
  set m := a k₀ with hm
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (Nat.one_le_iff_ne_zero.2 (NeZero.ne N))
  have ha0 : ∀ k, 0 ≤ a k := fun k => hK x _
  have ham : ∀ k, m ≤ a k := fun k => hk₀ k (mem_univ k)
  -- every value is at most m / c
  have hcm : ∀ j, c * a j ≤ m := by
    intro j
    have h := hc (k₀ - j) x (j +ᵥ y)
    rwa [vadd_vadd, sub_add_cancel] at h
  set S := ∑ k, a k with hS
  -- (1) the norm of the sector is at most `S/N - m`
  have h1 : ‖∑ k : ZMod N, (stdAddChar (-(k * e)) : ℂ) * (a k : ℂ)‖ ≤ S - N * m := by
    have hsplit : ∑ k : ZMod N, (stdAddChar (-(k * e)) : ℂ) * (a k : ℂ) =
        ∑ k : ZMod N, (stdAddChar (-(k * e)) : ℂ) * ((a k - m : ℝ) : ℂ) := by
      have hz : ∑ k : ZMod N, (stdAddChar (-(k * e)) : ℂ) * (m : ℂ) = 0 := by
        rw [← sum_mul, sum_stdAddChar_neg_mul he, zero_mul]
      rw [← sub_zero (∑ k : ZMod N, (stdAddChar (-(k * e)) : ℂ) * (a k : ℂ)), ← hz, ← sum_sub_distrib]
      exact sum_congr rfl fun k _ => by push_cast; ring
    rw [hsplit]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    rw [show S - N * m = ∑ k : ZMod N, (a k - m) by
      rw [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul]]
    refine sum_congr rfl fun k _ => ?_
    rw [norm_mul, AddChar.norm_apply, one_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.2 (ham k))]
  -- (2) `c S ≤ (N − 1 + c) m`
  have h2 : c * S ≤ ((N : ℝ) - 1 + c) * m := by
    have hsum := Finset.add_sum_erase (univ : Finset (ZMod N)) a (mem_univ k₀)
    have hcard : ((univ.erase k₀).card : ℝ) = (N : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (mem_univ k₀), card_univ, ZMod.card, Nat.cast_sub (Nat.one_le_iff_ne_zero.2
        (NeZero.ne N)), Nat.cast_one]
    have hrest : c * ∑ k ∈ univ.erase k₀, a k ≤ ((N : ℝ) - 1) * m := by
      rw [mul_sum, ← hcard, ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun k _ => hcm k
    rw [hS, ← hsum, mul_add, ← hm]
    nlinarith
  have hm0 : 0 ≤ m := ha0 k₀
  have hS0 : 0 ≤ S := sum_nonneg fun k _ => ha0 k
  unfold secN sec0N rhoN
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  change (N : ℝ)⁻¹ * ‖∑ k : ZMod N, (stdAddChar (-(k * e)) : ℂ) * (a k : ℂ)‖ ≤ _ * ((N : ℝ)⁻¹ * S)
  have hden : 0 < (N : ℝ) - 1 + c := by linarith
  calc (N : ℝ)⁻¹ * ‖∑ k : ZMod N, (stdAddChar (-(k * e)) : ℂ) * (a k : ℂ)‖ ≤ (N : ℝ)⁻¹ * (S - N * m) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hNpos.le)
    _ ≤ ((N : ℝ) - 1) * (1 - c) / ((N : ℝ) - 1 + c) * ((N : ℝ)⁻¹ * S) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hden]
        have : (N : ℝ)⁻¹ * (S - N * m) * ((N : ℝ) - 1 + c) = (N : ℝ)⁻¹ * (S * ((N : ℝ) - 1 + c)) - m * ((N : ℝ) - 1 + c) := by
          field_simp
        rw [this]
        have h3 : (N : ℝ)⁻¹ * (S * ((N : ℝ) - 1 + c)) - (N : ℝ)⁻¹ * (((N : ℝ) - 1) * (1 - c) * S) = c * S := by
          field_simp; ring
        nlinarith

theorem rhoN_two (c : ℝ) : rhoN 2 c = elec c := by
  unfold rhoN elec; norm_num

theorem cstarN_two : cstarN 2 = √2 - 1 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < √2 := by positivity
  unfold cstarN
  rw [div_eq_iff (by norm_num)]
  push_cast; nlinarith

/-- **The self-dual threshold for `Z_N`**: a pointwise twist ratio at least `cstarN N` gives sector factor at most
`√2 − 1`. -/
theorem rhoN_le_of_cstar {N : ℕ} (hN : 2 ≤ N) {c : ℝ} (hc0 : 0 < c) (hc : cstarN N ≤ c) : rhoN N c ≤ √2 - 1 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs1 : 1 < √2 := by rw [Real.lt_sqrt zero_le_one]; norm_num
  have hs2 : √2 < 2 := by rw [Real.sqrt_lt' two_pos]; norm_num
  have hden : 0 < (N : ℝ) - 2 + √2 := by linarith
  have hden' : 0 < (N : ℝ) - 1 + c := by linarith
  unfold cstarN at hc
  rw [div_le_iff₀ hden] at hc
  unfold rhoN
  rw [div_le_iff₀ hden']
  nlinarith

end Twist

/-! ## 4. Three slabs and chains, sector by sector -/

section Chains

variable {N : ℕ} [NeZero N] {X : Type*} [Fintype X] [AddAction (ZMod N) X]

/-- **Three slabs on the electric side clear O1 in every sector, with no join loss.** Nonnegative kernels, the last two
centre-symmetric, each with sector-`e` factor at most `√2 − 1` at every end face: for every `0 ≤ μ ≤ 14`,
`μ ‖Z_e‖ ≤ Z_0` at every end face of the joined slab. -/
theorem three_slabsN_O1 {K₁ K₂ K₃ : X → X → ℝ} (hK₁ : ∀ x y, 0 ≤ K₁ x y) (hK₂ : ∀ x y, 0 ≤ K₂ x y)
    (hK₃ : ∀ x y, 0 ≤ K₃ x y) (hs₂ : CentreSym N K₂) (hs₃ : CentreSym N K₃) {e : ZMod N}
    (he₁ : twistCertN N K₁ e (√2 - 1)) (he₂ : twistCertN N K₂ e (√2 - 1)) (he₃ : twistCertN N K₃ e (√2 - 1)) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ 14) (x y : X) :
    μ * ‖secN (kjoin (kjoin K₁ K₂) K₃) e x y‖ ≤ sec0N N (kjoin (kjoin K₁ K₂) K₃) x y := by
  have b := elecN_submul hs₃ (elecN_submul hs₂ he₁ he₂) he₃ x y
  have hcube : (√2 - 1) * (√2 - 1) * (√2 - 1) = (√2 - 1) ^ 3 := by ring
  rw [hcube] at b
  have hclear := three_steps_clear hμ0 hμ
  have n0 : 0 ≤ sec0N N (kjoin (kjoin K₁ K₂) K₃) x y :=
    sec0N_nonneg (kjoin_nonneg (kjoin_nonneg hK₁ hK₂) hK₃) x y
  calc μ * ‖secN (kjoin (kjoin K₁ K₂) K₃) e x y‖ ≤ μ * ((√2 - 1) ^ 3 * sec0N N (kjoin (kjoin K₁ K₂) K₃) x y) :=
        mul_le_mul_of_nonneg_left b hμ0
    _ = ((√2 - 1) ^ 3 * μ) * sec0N N (kjoin (kjoin K₁ K₂) K₃) x y := by ring
    _ ≤ 1 * sec0N N (kjoin (kjoin K₁ K₂) K₃) x y := mul_le_mul_of_nonneg_right hclear.le n0
    _ = _ := one_mul _

/-- **The same from pointwise twist ratios**: each slab with twist ratio at least `cstarN N` for every twist. -/
theorem three_slabsN_O1_twist (hN : 2 ≤ N) {K₁ K₂ K₃ : X → X → ℝ} (hK₁ : ∀ x y, 0 ≤ K₁ x y)
    (hK₂ : ∀ x y, 0 ≤ K₂ x y) (hK₃ : ∀ x y, 0 ≤ K₃ x y) (hs₂ : CentreSym N K₂) (hs₃ : CentreSym N K₃) {c : ℝ}
    (hc0 : 0 < c) (hc : cstarN N ≤ c) (h₁ : ∀ (k : ZMod N) x y, c * K₁ x y ≤ K₁ x (k +ᵥ y))
    (h₂ : ∀ (k : ZMod N) x y, c * K₂ x y ≤ K₂ x (k +ᵥ y)) (h₃ : ∀ (k : ZMod N) x y, c * K₃ x y ≤ K₃ x (k +ᵥ y))
    {e : ZMod N} (he : e ≠ 0) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ 14) (x y : X) :
    μ * ‖secN (kjoin (kjoin K₁ K₂) K₃) e x y‖ ≤ sec0N N (kjoin (kjoin K₁ K₂) K₃) x y := by
  have hr := rhoN_le_of_cstar hN hc0 hc
  exact three_slabsN_O1 hK₁ hK₂ hK₃ hs₂ hs₃ (twistCertN_mono hK₁ (sector_of_twistN hK₁ hc0 h₁ he) hr)
    (twistCertN_mono hK₂ (sector_of_twistN hK₂ hc0 h₂ he) hr) (twistCertN_mono hK₃ (sector_of_twistN hK₃ hc0 h₃ he) hr)
    hμ0 hμ x y

/-- **Layers in series, no loss, every sector**: `n + 1` centre-symmetric layers with sector-`e` factor `ρ` give
factor `ρ^{n+1}`. -/
theorem kchainN_elec {T : ℕ → X → X → ℝ} (hsym : ∀ n, CentreSym N (T n)) {e : ZMod N} {ρ : ℝ}
    (hρ : ∀ n, twistCertN N (T n) e ρ) (n : ℕ) : twistCertN N (kchain T n) e (ρ ^ (n + 1)) := by
  induction n with
  | zero => rw [zero_add, pow_one]; exact hρ 0
  | succ n ih =>
    rw [pow_succ]
    exact elecN_submul (hsym (n + 1)) ih (hρ (n + 1))

end Chains

/-! ## 5. `N = 2` is the `Z_2` slab of `JoinLossSlab` -/

section Two

variable {X Y : Type*} [AddAction (ZMod 2) Y]

theorem stdAddChar_two_one : (stdAddChar (1 : ZMod 2) : ℂ) = -1 := by
  have h := General.sum_char_mul (N := 2) 1
  rw [ite_eq_right (by decide)] at h
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl, sum_pair (by decide)] at h
  have h' := h
  simp only [zero_mul, AddChar.map_zero_eq_one, one_mul] at h'
  linear_combination h'

/-- The twist of `Z_2` as an involution. -/
def omega2 (y : Y) : Y := (1 : ZMod 2) +ᵥ y

theorem omega2_involutive : Function.Involutive (omega2 (Y := Y)) := fun y => by
  unfold omega2; rw [vadd_vadd]; rw [show (1 : ZMod 2) + 1 = 0 from rfl, zero_vadd]

theorem secN_two_one (K : Y → Y → ℝ) (x y : Y) : secN K (1 : ZMod 2) x y = (sec1 omega2 K x y : ℂ) := by
  unfold secN sec1 omega2
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl, sum_pair (by decide)]
  simp only [neg_zero, AddChar.map_zero_eq_one, one_mul, zero_vadd, mul_one]
  rw [show (-(1 : ZMod 2)) = 1 from rfl, stdAddChar_two_one]
  push_cast; ring

theorem secN_two_zero (K : Y → Y → ℝ) (x y : Y) : secN K (0 : ZMod 2) x y = (sec0 omega2 K x y : ℂ) := by
  rw [secN_zero]
  unfold sec0N sec0 omega2
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} from rfl, sum_pair (by decide), zero_vadd]
  push_cast; ring

end Two

/-! ## 6. The owner's candidates `N = 2, 3, 5, 11`, through the general theorem -/

section Instances

variable {X : Type*} [Fintype X]

/-- SU(2): three slabs with pointwise twist ratio at least `√2 − 1` clear O1 (sector `e = 1`). -/
theorem su2_slab_O1 [AddAction (ZMod 2) X] {K₁ K₂ K₃ : X → X → ℝ} (hK₁ : ∀ x y, 0 ≤ K₁ x y)
    (hK₂ : ∀ x y, 0 ≤ K₂ x y) (hK₃ : ∀ x y, 0 ≤ K₃ x y) (hs₂ : CentreSym 2 K₂) (hs₃ : CentreSym 2 K₃) {c : ℝ}
    (hc : √2 - 1 ≤ c) (h₁ : ∀ (k : ZMod 2) x y, c * K₁ x y ≤ K₁ x (k +ᵥ y))
    (h₂ : ∀ (k : ZMod 2) x y, c * K₂ x y ≤ K₂ x (k +ᵥ y)) (h₃ : ∀ (k : ZMod 2) x y, c * K₃ x y ≤ K₃ x (k +ᵥ y))
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ 14) (x y : X) :
    μ * ‖secN (kjoin (kjoin K₁ K₂) K₃) (1 : ZMod 2) x y‖ ≤ sec0N 2 (kjoin (kjoin K₁ K₂) K₃) x y :=
  three_slabsN_O1_twist le_rfl hK₁ hK₂ hK₃ hs₂ hs₃ (lt_of_lt_of_le sqrt_two_sub_one_pos hc)
    (by rw [cstarN_two]; exact hc) h₁ h₂ h₃ (by decide) hμ0 hμ x y

/-- SU(3): every nontrivial sector, from twist ratio at least `cstarN 3`. -/
theorem su3_slab_O1 [AddAction (ZMod 3) X] {K₁ K₂ K₃ : X → X → ℝ} (hK₁ : ∀ x y, 0 ≤ K₁ x y)
    (hK₂ : ∀ x y, 0 ≤ K₂ x y) (hK₃ : ∀ x y, 0 ≤ K₃ x y) (hs₂ : CentreSym 3 K₂) (hs₃ : CentreSym 3 K₃) {c : ℝ}
    (hc0 : 0 < c) (hc : cstarN 3 ≤ c) (h₁ : ∀ (k : ZMod 3) x y, c * K₁ x y ≤ K₁ x (k +ᵥ y))
    (h₂ : ∀ (k : ZMod 3) x y, c * K₂ x y ≤ K₂ x (k +ᵥ y)) (h₃ : ∀ (k : ZMod 3) x y, c * K₃ x y ≤ K₃ x (k +ᵥ y))
    {e : ZMod 3} (he : e ≠ 0) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ 14) (x y : X) :
    μ * ‖secN (kjoin (kjoin K₁ K₂) K₃) e x y‖ ≤ sec0N 3 (kjoin (kjoin K₁ K₂) K₃) x y :=
  three_slabsN_O1_twist (by norm_num) hK₁ hK₂ hK₃ hs₂ hs₃ hc0 hc h₁ h₂ h₃ he hμ0 hμ x y

/-- SU(5): every nontrivial sector, from twist ratio at least `cstarN 5`. -/
theorem su5_slab_O1 [AddAction (ZMod 5) X] {K₁ K₂ K₃ : X → X → ℝ} (hK₁ : ∀ x y, 0 ≤ K₁ x y)
    (hK₂ : ∀ x y, 0 ≤ K₂ x y) (hK₃ : ∀ x y, 0 ≤ K₃ x y) (hs₂ : CentreSym 5 K₂) (hs₃ : CentreSym 5 K₃) {c : ℝ}
    (hc0 : 0 < c) (hc : cstarN 5 ≤ c) (h₁ : ∀ (k : ZMod 5) x y, c * K₁ x y ≤ K₁ x (k +ᵥ y))
    (h₂ : ∀ (k : ZMod 5) x y, c * K₂ x y ≤ K₂ x (k +ᵥ y)) (h₃ : ∀ (k : ZMod 5) x y, c * K₃ x y ≤ K₃ x (k +ᵥ y))
    {e : ZMod 5} (he : e ≠ 0) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ 14) (x y : X) :
    μ * ‖secN (kjoin (kjoin K₁ K₂) K₃) e x y‖ ≤ sec0N 5 (kjoin (kjoin K₁ K₂) K₃) x y :=
  three_slabsN_O1_twist (by norm_num) hK₁ hK₂ hK₃ hs₂ hs₃ hc0 hc h₁ h₂ h₃ he hμ0 hμ x y

/-- SU(11): every nontrivial sector, from twist ratio at least `cstarN 11`. -/
theorem su11_slab_O1 [AddAction (ZMod 11) X] {K₁ K₂ K₃ : X → X → ℝ} (hK₁ : ∀ x y, 0 ≤ K₁ x y)
    (hK₂ : ∀ x y, 0 ≤ K₂ x y) (hK₃ : ∀ x y, 0 ≤ K₃ x y) (hs₂ : CentreSym 11 K₂) (hs₃ : CentreSym 11 K₃) {c : ℝ}
    (hc0 : 0 < c) (hc : cstarN 11 ≤ c) (h₁ : ∀ (k : ZMod 11) x y, c * K₁ x y ≤ K₁ x (k +ᵥ y))
    (h₂ : ∀ (k : ZMod 11) x y, c * K₂ x y ≤ K₂ x (k +ᵥ y)) (h₃ : ∀ (k : ZMod 11) x y, c * K₃ x y ≤ K₃ x (k +ᵥ y))
    {e : ZMod 11} (he : e ≠ 0) {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : μ ≤ 14) (x y : X) :
    μ * ‖secN (kjoin (kjoin K₁ K₂) K₃) e x y‖ ≤ sec0N 11 (kjoin (kjoin K₁ K₂) K₃) x y :=
  three_slabsN_O1_twist (by norm_num) hK₁ hK₂ hK₃ hs₂ hs₃ hc0 hc h₁ h₂ h₃ he hμ0 hμ x y

/-- The thresholds increase with `N` and stay below `2 − √2`: `cstarN 2 < cstarN 3 < cstarN 5 < cstarN 11 < 2 − √2`. -/
theorem cstarN_chain : cstarN 2 < cstarN 3 ∧ cstarN 3 < cstarN 5 ∧ cstarN 5 < cstarN 11 ∧ cstarN 11 < 2 - √2 := by
  have hs1 : 1 < √2 := by rw [Real.lt_sqrt zero_le_one]; norm_num
  have hs2 : √2 < 2 := by rw [Real.sqrt_lt' two_pos]; norm_num
  have hq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  unfold cstarN
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · rw [div_lt_iff₀ (by linarith)]; nlinarith

end Instances

end ProofPhase.Unified
