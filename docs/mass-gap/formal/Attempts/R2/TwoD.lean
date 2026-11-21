/-
Round 2, attempt A: the reduction closes in 2D compact U(1) (2026-11-21). Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/attempts/r2-2d/NOTE.md` (certificate, validity lemma, status) and
`PREREG.md`; computational input: `attempts/r2-2d/tree_cert.py`, output `attempts/r2-2d/cert_2_11.json`.
-/

import OneScale.CorollaryBW
import Positivity.Concrete

/-!
# 2D compact U(1) at β = 2: from certified one-box numbers to exponential decay

The W-form chain (`OneScale.CubeChain.gauge_decay_finiteVolume_W`, Theorem A (W) + Theorem C on the torus) instantiated
for `d = 2`, `G = U(1)` (`Un 1`), Wilson weight `φ(x) = exp(2x)` (β = 2), cost = arc length on U(1), thin squares of
side `ℓ = 11`.

* `arc`: the arc-length (geodesic) distance on U(1), `|arg(a b̄)|`; `0 ≤ arc ≤ π`, inversion invariant, not identically 0.
* `kappa ℓ kP kD x z`: the influence coefficient of the shell link `z` on the square at `x`, by class: parallel links at
  face position `i` (`kP i`), dangling links at face-interior sites (`kD`), the four corner links per direction (`kP 0`).
  It is written as a sum over relative offsets `z.site - x` (one offset per shell position), so the GDS sum over `x`
  is the plain sum of the class values (`sum_kappa`), with no geometry.
* `coverage_ge`: every link lies in at least `ℓ(ℓ+1)` thin squares (`d = 2`, `ℓ + 1 ≤ N`).
* `gds_kappaT`: **GDS for the 2D thin squares** with `γ = [2 Σ_i kP i + 2(ℓ-1) kD + 4 kP 0]/(ℓ(ℓ+1))` (proved).
* `CertifiedInfluence N`: **the computational input** (W-form influence bounds of the shell links with the certified
  numbers `kPcert`, `kDcert`); it is a hypothesis here, established outside Lean by the interval-arithmetic
  certificate `tree_cert.py` (computer-assisted, see the NOTE). Only shell links are assumed; off the shell the zero
  coefficient is proved (`influence_of_shell`).
* `gammaCert_lt_one`: `γ < 1` for the certified numbers, by `norm_num`.
* **`twoD_U1_decay`**: under `CertifiedInfluence N`, on every even torus `N ≥ 14`, slab observables Lipschitz in each
  link for `arc` have `|Cov(F ∘ S_m, F ∘ Θ)| ≤ (Cov(0) + 2^{-r} C) e^{-λ m}` for every `λ < log(1/γ)/12`, with `C`
  independent of `N`.
* **`twoD_U1_decay_limit`**: the same bound with prefactor `h(0)` for any limit `h` of the torus correlations along even
  `N_j → ∞`.
* `twoD_U1_decay_10`: the same from the smallest certified box, side 10 (`γ ≤ 0.9924`, `cert_2_10.json`).

The classification of the shell links (that `kappa` lists exactly the shell offsets) is checked by enumeration in
`attempts/r2-2d/shell_check.py`; it is not needed for the truth of the theorems (an unlisted shell link would make the
hypothesis false, not the conclusion).
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete
open OneScale OneScale.Gauge OneScale.CorollaryB OneScale.CubeChain OneScale.LinkDist OneScale.TimeShift Positivity

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace Attempts.R2.TwoD

/-! ## U(1) with the arc-length cost -/

/-- The single matrix entry of a U(1) element. -/
def ent (a : Un 1) : ℂ := (a : Matrix (Fin 1) (Fin 1) ℂ) 0 0

theorem ent_inv (a : Un 1) : ent a⁻¹ = star (ent a) := by
  simp [ent, Matrix.star_apply]

/-- The arc-length (geodesic) distance on U(1): `|arg(a b̄)|`. -/
def arc (a b : Un 1) : ℝ := |Complex.arg (ent a * star (ent b))|

theorem arc_nonneg (a b : Un 1) : 0 ≤ arc a b := abs_nonneg _

theorem arc_le_pi (a b : Un 1) : arc a b ≤ Real.pi := Complex.abs_arg_le_pi _

theorem arc_inv (a b : Un 1) : arc a⁻¹ b⁻¹ = arc a b := by
  unfold arc
  rw [ent_inv, ent_inv, star_star]
  have h : star (ent a) * ent b = (starRingEnd ℂ) (ent a * star (ent b)) := by
    simp only [Complex.star_def, map_mul, Complex.conj_conj]
  rw [h, Complex.arg_conj]
  split_ifs with h'
  · rw [h']
  · rw [abs_neg]

theorem arc_pos : ∃ a b : Un 1, 0 < arc a b := by
  refine ⟨1, negOneUn 1, ?_⟩
  have h1 : ent 1 = 1 := by simp [ent]
  have h2 : ent (negOneUn 1) = -1 := by simp [ent, negOneUn]
  rw [arc, h1, h2]
  simp [Complex.arg_neg_one, Real.pi_pos]

theorem rep_continuous : Continuous (HasGaugeTrace.rep (G := Un 1) (n := 1)) := continuous_subtype_val

theorem rep_unitary : ∀ g : Un 1, HasGaugeTrace.rep (G := Un 1) (n := 1) g ∈ Matrix.unitaryGroup (Fin 1) ℂ :=
  fun g => g.2

/-! ## The influence classes and GDS for 2D thin squares -/

variable {N : ℕ} [NeZero N]

/-- The relative offset with coordinate `a` along the direction `μ` and `b` across it. -/
def off (μ : Fin 2) (a b : ZMod N) : Fin 2 → ZMod N := fun i => if i = μ then a else b

/-- Indicator that `z` sits at offset `o` from the corner `x` of a square. -/
def ind (x : FinLatticeSites 2 N) (z : LatticeLink 2 N) (o : Fin 2 → ZMod N) : ℝ := if z.site - x = o then 1 else 0

theorem ind_nonneg (x : FinLatticeSites 2 N) (z : LatticeLink 2 N) (o : Fin 2 → ZMod N) : 0 ≤ ind x z o := by
  unfold ind; split_ifs <;> norm_num

theorem sum_ind (z : LatticeLink 2 N) (o : Fin 2 → ZMod N) : ∑ x, ind x z o = 1 := by
  have h : ∀ x : FinLatticeSites 2 N, (z.site - x = o) ↔ (x = z.site - o) := fun x => by
    rw [eq_sub_iff_add_eq, sub_eq_iff_eq_add']; exact eq_comm
  simp only [ind, h]
  simp

/-- **The influence coefficients by class** (side `ℓ`; `kP i` for the parallel links at face position `i`, bottom and
top; `kD` for the dangling links at the face-interior sites `1..ℓ-1`, left and right; `kP 0` for the four corner links;
all relative to the direction of `z`). -/
def kappa (ℓ : ℕ) (kP : ℕ → ℝ) (kD : ℝ) (x : FinLatticeSites 2 N) (z : LatticeLink 2 N) : ℝ :=
  (∑ i ∈ range ℓ, kP i * (ind x z (off z.dir (i : ZMod N) (-1)) + ind x z (off z.dir (i : ZMod N) ((ℓ : ZMod N) + 1)))) +
  (∑ s ∈ Ico 1 ℓ, kD * (ind x z (off z.dir (-1) (s : ZMod N)) + ind x z (off z.dir (ℓ : ZMod N) (s : ZMod N)))) +
  kP 0 * (ind x z (off z.dir (-1) 0) + ind x z (off z.dir (-1) (ℓ : ZMod N)) + ind x z (off z.dir (ℓ : ZMod N) 0) +
    ind x z (off z.dir (ℓ : ZMod N) (ℓ : ZMod N)))

theorem kappa_nonneg {ℓ : ℕ} {kP : ℕ → ℝ} {kD : ℝ} (hkP : ∀ i, 0 ≤ kP i) (hkD : 0 ≤ kD)
    (x : FinLatticeSites 2 N) (z : LatticeLink 2 N) : 0 ≤ kappa ℓ kP kD x z := by
  unfold kappa
  have hi := ind_nonneg (N := N) x z
  refine add_nonneg (add_nonneg (sum_nonneg fun i _ => mul_nonneg (hkP i) (add_nonneg (hi _) (hi _)))
    (sum_nonneg fun s _ => mul_nonneg hkD (add_nonneg (hi _) (hi _)))) ?_
  exact mul_nonneg (hkP 0) (add_nonneg (add_nonneg (add_nonneg (hi _) (hi _)) (hi _)) (hi _))

/-- The GDS sum of `kappa` over the squares is the plain sum of the class values (every offset is hit by exactly one
corner `x`). -/
theorem sum_kappa (ℓ : ℕ) (kP : ℕ → ℝ) (kD : ℝ) (z : LatticeLink 2 N) :
    ∑ x, kappa ℓ kP kD x z = 2 * ∑ i ∈ range ℓ, kP i + 2 * ((ℓ - 1 : ℕ) : ℝ) * kD + 4 * kP 0 := by
  unfold kappa
  rw [sum_add_distrib, sum_add_distrib, sum_comm, sum_comm (s := univ) (t := Ico 1 ℓ), ← mul_sum]
  simp only [← mul_sum, sum_add_distrib, sum_ind]
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_sum]
  ring_nf

/-- Every link lies in at least `ℓ(ℓ+1)` thin squares (`d = 2`, `ℓ + 1 ≤ N`). -/
theorem coverage_ge (ℓ : ℕ) (hN : ℓ + 1 ≤ N) (z : LatticeLink 2 N) :
    ℓ * (ℓ + 1) ≤ coverage (thinCube (d := 2) (N := N) ℓ) z := by
  unfold coverage
  obtain ⟨ν, hν⟩ : ∃ ν : Fin 2, ν ≠ z.dir := by
    by_cases h : z.dir = 0
    · exact ⟨1, by rw [h]; decide⟩
    · exact ⟨0, fun h' => h h'.symm⟩
  set f : Fin ℓ × Fin (ℓ + 1) → FinLatticeSites 2 N :=
    fun p => z.site - off z.dir ((p.1 : ℕ) : ZMod N) ((p.2 : ℕ) : ZMod N) with hf
  have hval : ∀ a : ℕ, a < N → ((a : ZMod N)).val = a := fun a ha => ZMod.val_natCast_of_lt ha
  have hmem : ∀ p, z ∈ thinCube (d := 2) (N := N) ℓ (f p) := by
    intro p
    rw [mem_thinCube]
    intro i
    have e1 : z.site i - f p i = off z.dir ((p.1 : ℕ) : ZMod N) ((p.2 : ℕ) : ZMod N) i := by
      simp only [hf, Pi.sub_apply]; ring
    have e2 : z.target i - f p i = z.target i - z.site i + off z.dir ((p.1 : ℕ) : ZMod N) ((p.2 : ℕ) : ZMod N) i := by
      simp only [hf, Pi.sub_apply]; ring
    rw [e1, e2]
    by_cases hi : i = z.dir
    · subst hi
      have ht : z.target z.dir - z.site z.dir = 1 := by
        simp [LatticeLink.target, siteShift]
      rw [ht]
      simp only [off, ↓reduceIte]
      have h1 : (1 : ZMod N) + ((p.1 : ℕ) : ZMod N) = (((p.1 : ℕ) + 1 : ℕ) : ZMod N) := by push_cast; ring
      rw [h1, hval _ (by omega), hval _ (by omega)]
      omega
    · have ht : z.target i - z.site i = 0 := by
        simp [LatticeLink.target, siteShift, Function.update_of_ne hi]
      rw [ht, zero_add]
      simp only [off, hi, ↓reduceIte]
      rw [hval _ (by omega)]
      omega
  have hinj : Set.InjOn f (univ : Finset (Fin ℓ × Fin (ℓ + 1))) := by
    intro p _ q _ hpq
    have h : off z.dir ((p.1 : ℕ) : ZMod N) ((p.2 : ℕ) : ZMod N) =
        off z.dir ((q.1 : ℕ) : ZMod N) ((q.2 : ℕ) : ZMod N) := sub_right_injective hpq
    have h1 := congrFun h z.dir
    have h2 := congrFun h ν
    simp only [off, hν, ↓reduceIte] at h1 h2
    have e1 := congrArg ZMod.val h1
    have e2 := congrArg ZMod.val h2
    rw [hval _ (by omega), hval _ (by omega)] at e1 e2
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  have := card_le_card_of_injOn f (t := univ.filter fun x => z ∈ thinCube (d := 2) (N := N) ℓ x)
    (fun p _ => Finset.mem_coe.2 (Finset.mem_filter.2 ⟨mem_univ _, hmem p⟩)) hinj
  rw [card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
  exact this

/-- The coefficients restricted to the shell (`0` off the shell). -/
def kappaT (ℓ : ℕ) (kP : ℕ → ℝ) (kD : ℝ) (x : FinLatticeSites 2 N) (z : LatticeLink 2 N) : ℝ :=
  if InShell (thinCube (d := 2) (N := N) ℓ x) z then kappa ℓ kP kD x z else 0

/-- The GDS constant of the class values. -/
def gammaOf (ℓ : ℕ) (kP : ℕ → ℝ) (kD : ℝ) : ℝ :=
  (2 * ∑ i ∈ range ℓ, kP i + 2 * ((ℓ - 1 : ℕ) : ℝ) * kD + 4 * kP 0) / ((ℓ : ℝ) * ((ℓ : ℝ) + 1))

/-- **GDS for the 2D thin squares from the class values** (proved). -/
theorem gds_kappaT {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hN : ℓ + 1 ≤ N) {kP : ℕ → ℝ} {kD : ℝ} (hkP : ∀ i, 0 ≤ kP i)
    (hkD : 0 ≤ kD) : GDS (thinCube (d := 2) (N := N) ℓ) (kappaT ℓ kP kD) (gammaOf ℓ kP kD) := by
  intro z
  have hpos : (0 : ℝ) < (ℓ : ℝ) * ((ℓ : ℝ) + 1) := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    positivity
  have hK : 0 ≤ 2 * ∑ i ∈ range ℓ, kP i + 2 * ((ℓ - 1 : ℕ) : ℝ) * kD + 4 * kP 0 := by
    have := sum_nonneg fun i (_ : i ∈ range ℓ) => hkP i
    have := hkP 0
    positivity
  have hγ0 : 0 ≤ gammaOf ℓ kP kD := div_nonneg hK hpos.le
  have hcov : ((ℓ : ℝ) * ((ℓ : ℝ) + 1)) ≤ (coverage (thinCube (d := 2) (N := N) ℓ) z : ℝ) := by
    exact_mod_cast coverage_ge ℓ hN z
  calc ∑ x ∈ univ.filter (fun x => z ∉ thinCube ℓ x), kappaT ℓ kP kD x z
      ≤ ∑ x ∈ univ.filter (fun x => z ∉ thinCube ℓ x), kappa ℓ kP kD x z := by
        refine sum_le_sum fun x _ => ?_
        unfold kappaT; split_ifs
        · exact le_rfl
        · exact kappa_nonneg hkP hkD x z
    _ ≤ ∑ x, kappa ℓ kP kD x z :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) fun x _ _ => kappa_nonneg hkP hkD x z
    _ = gammaOf ℓ kP kD * ((ℓ : ℝ) * ((ℓ : ℝ) + 1)) := by
        rw [sum_kappa, gammaOf, div_mul_cancel₀ _ hpos.ne']
    _ ≤ gammaOf ℓ kP kD * coverage (thinCube ℓ) z := mul_le_mul_of_nonneg_left hcov hγ0

/-- Shell bounds suffice: off the shell the zero coefficient is an influence bound (the link does not enter the block
specification). -/
theorem influence_of_shell {ℓ : ℕ} {kP : ℕ → ℝ} {kD : ℝ} {φ : ℝ → ℝ}
    (h : ∀ x z, z ∉ thinCube (d := 2) (N := N) ℓ x → InShell (thinCube ℓ x) z →
      IsInfluenceBoundW arc (thinCube ℓ x) (gaugeSpec (G := Un 1) 1 φ (thinCube ℓ x)) z (kappa ℓ kP kD x z)) :
    ∀ x z, z ∉ thinCube (d := 2) (N := N) ℓ x →
      IsInfluenceBoundW arc (thinCube ℓ x) (gaugeSpec (G := Un 1) 1 φ (thinCube ℓ x)) z (kappaT ℓ kP kD x z) := by
  intro x z hz
  unfold kappaT
  split_ifs with hs
  · exact h x z hz hs
  · intro U s F L _ _ _
    rw [gaugeSpec_update_of_not_shell hz hs U s, sub_self, abs_zero, zero_mul, zero_mul]

/-! ## The certified numbers (β = 2, ℓ = 11) and the decay statement -/

/-- Certified upper bounds of the parallel-link coefficients, by distance to the nearer corner `j = min(i, 10 - i)`
(from `cert_2_11.json`, rounded up). -/
def kq (j : ℕ) : ℝ :=
  if j = 0 then 2.4825 else if j = 1 then 2.4215 else if j = 2 then 2.4194 else if j = 3 then 2.4194
  else if j = 4 then 2.4194 else 2.4194

/-- Parallel links at face position `i` of the side-11 square. -/
def kPcert (i : ℕ) : ℝ := kq (min i (10 - i))

/-- Certified upper bound of the dangling-link coefficient (`cert_2_11.json`, rounded up). -/
def kDcert : ℝ := 2.8099

/-- The certified GDS constant. -/
def gammaCert : ℝ := gammaOf 11 kPcert kDcert

theorem gammaCert_lt_one : gammaCert < 1 := by
  norm_num [gammaCert, gammaOf, kPcert, kq, kDcert, Finset.sum_range_succ]

theorem gammaCert_pos : 0 < gammaCert := by
  norm_num [gammaCert, gammaOf, kPcert, kq, kDcert, Finset.sum_range_succ]

theorem kPcert_nonneg (i : ℕ) : 0 ≤ kPcert i := by
  unfold kPcert kq; split_ifs <;> norm_num

/-- The Wilson weight at β = 2 (U(1): `Re tr U_p = cos θ_p`). -/
abbrev phi2 : ℝ → ℝ := fun x => Real.exp (2 * x)

/-- **The computational input** (computer-assisted, `attempts/r2-2d/tree_cert.py`, `cert_2_11.json`): every shell link
`z` of every thin square of side 11 has W-form influence (cost `arc`) at most its class value `kappa 11 kPcert kDcert`,
for 2D compact U(1) at β = 2 on the torus `(ℤ/Nℤ)²`. -/
def CertifiedInfluence (N : ℕ) [NeZero N] : Prop :=
  ∀ x z, z ∉ thinCube (d := 2) (N := N) 11 x → InShell (thinCube 11 x) z →
    IsInfluenceBoundW arc (thinCube 11 x) (gaugeSpec (G := Un 1) 1 phi2 (thinCube 11 x)) z
      (kappa 11 kPcert kDcert x z)

/-- **2D compact U(1) at β = 2, exponential decay on the torus, uniform in `N`** (under the certified influence bounds).
For every even `N ≥ 14`, every slab observable `F` (depending on the time slab `[0, s]`) Lipschitz in each link for the
arc length (`w ≥ 0`, `∑ w ≤ V`, `w ≤ L`), every `0 ≤ λ < log(1/γ)/12` and `r ≥ 1` with `2^{r+1} m + 2s + 2 ≤ N`:
`|Cov(F ∘ S_m, F ∘ Θ)| ≤ (Cov(F ∘ S_0, F ∘ Θ) + 2^{-r} C) e^{-λ m}`, `C = cubeConstW 2 11 γ λ V L π` independent of `N`. -/
theorem twoD_U1_decay {N : ℕ} [NeZero N] (hEven : Even N) (hN : 14 ≤ N) (hcert : CertifiedInfluence N)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < Real.log (1 / gammaCert) / 12)
    {F : GaugeConnection (Un 1) 2 N → ℝ} (hF : BM F) {s : ℕ} (hFs : DepOn F (timeSlab 0 s))
    {w : LatticeLink 2 N → ℝ} (hw0 : ∀ l, 0 ≤ w l) (hw : LipBound arc F w) {V L : ℝ} (hV : ∑ l, w l ≤ V)
    (hL : ∀ l, w l ≤ L) {m r : ℕ} (hr : 1 ≤ r) (hNr : 2 ^ (r + 1) * m + 2 * s + 2 ≤ N) :
    |corr 1 phi2 F m| ≤
      (corr 1 phi2 F 0 + (1 / 2 : ℝ) ^ r * cubeConstW 2 11 gammaCert lam V L Real.pi) * Real.exp (-(lam * m)) := by
  have hρ : gammaCert * Real.exp (lam * (((11 : ℕ) : ℝ) + 1)) < 1 :=
    rate_lt_of_lt gammaCert_pos (by norm_num) (by rw [show (((11 : ℕ) : ℝ) + 1) = 12 by norm_num]; exact hlam)
  have hgds : GDS (thinCube (d := 2) (N := N) 11) (kappaT 11 kPcert kDcert) gammaCert :=
    gds_kappaT (by norm_num) (by omega) kPcert_nonneg (by norm_num [kDcert])
  exact gauge_decay_finiteVolume_W rep_continuous rep_unitary hEven arc_nonneg arc_le_pi arc_pos arc_inv
    (posWeight_exp 1 2) (by norm_num) (influence_of_shell hcert) gammaCert_pos.le hgds hlam0 hρ hF hFs hw0 hw hV hL
    hr hNr

/-- **The infinite-volume form.** If along even tori `N_j → ∞` (each `≥ 14`, each with the certified bounds) the
correlations `t ↦ Cov_{N_j}(F_j ∘ S_t, F_j ∘ Θ)` of slab observables with uniform constants converge to `h t`, then
`|h t| ≤ h 0 · e^{-λ t}` for every `0 ≤ λ < log(1/γ)/12`. -/
theorem twoD_U1_decay_limit (Ns : ℕ → ℕ) [∀ j, NeZero (Ns j)] (hEven : ∀ j, Even (Ns j)) (hN : ∀ j, 14 ≤ Ns j)
    (hNs : Tendsto Ns atTop atTop) (hcert : ∀ j, CertifiedInfluence (Ns j))
    (F : ∀ j, GaugeConnection (Un 1) 2 (Ns j) → ℝ) (hF : ∀ j, BM (F j)) (s : ℕ)
    (hFs : ∀ j, DepOn (F j) (timeSlab 0 s)) (w : ∀ j, LatticeLink 2 (Ns j) → ℝ) (hw0 : ∀ j l, 0 ≤ w j l)
    (hw : ∀ j, LipBound arc (F j) (w j)) (V L : ℝ) (hV : ∀ j, ∑ l, w j l ≤ V) (hL : ∀ j l, w j l ≤ L)
    (h : ℕ → ℝ) (hlim : ∀ t, Tendsto (fun j => corr 1 phi2 (F j) t) atTop (𝓝 (h t)))
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < Real.log (1 / gammaCert) / 12) (t : ℕ) :
    |h t| ≤ h 0 * Real.exp (-(lam * t)) := by
  set C := cubeConstW 2 11 gammaCert lam V L Real.pi
  set E := Real.exp (-(lam * t))
  have hfin : ∀ r : ℕ, 1 ≤ r → ∀ᶠ j in atTop,
      |corr 1 phi2 (F j) t| ≤ (corr 1 phi2 (F j) 0 + (1 / 2 : ℝ) ^ r * C) * E := by
    intro r hr
    filter_upwards [tendsto_atTop.1 hNs (2 ^ (r + 1) * t + 2 * s + 2)] with j hj
    exact twoD_U1_decay (hEven j) (hN j) (hcert j) hlam0 hlam (hF j) (hFs j) (hw0 j) (hw j) (hV j) (hL j) hr hj
  have hr_bound : ∀ r : ℕ, 1 ≤ r → |h t| ≤ (h 0 + (1 / 2 : ℝ) ^ r * C) * E := fun r hr =>
    le_of_tendsto_of_tendsto (hlim t).abs (((hlim 0).add_const _).mul_const E) (hfin r hr)
  have hq : Tendsto (fun r : ℕ => (h 0 + (1 / 2 : ℝ) ^ r * C) * E) atTop (𝓝 ((h 0 + 0 * C) * E)) :=
    (tendsto_const_nhds.add
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul_const C)).mul_const E
  rw [zero_mul, add_zero] at hq
  exact ge_of_tendsto hq (eventually_atTop.2 ⟨1, fun r hr => hr_bound r hr⟩)

/-! ## The smallest certified box: ℓ = 10 (`cert_2_10.json`) -/

/-- Certified upper bounds for the side-10 square, by distance to the nearer corner `j = min(i, 9 - i)`
(`cert_2_10.json`, rounded up; the dangling-link bound is `kDcert`). -/
def kq10 (j : ℕ) : ℝ :=
  if j = 0 then 2.4824 else if j = 1 then 2.4214 else 2.4193

def kPcert10 (i : ℕ) : ℝ := kq10 (min i (9 - i))

def gammaCert10 : ℝ := gammaOf 10 kPcert10 kDcert

theorem gammaCert10_lt_one : gammaCert10 < 1 := by
  norm_num [gammaCert10, gammaOf, kPcert10, kq10, kDcert, Finset.sum_range_succ]

theorem gammaCert10_pos : 0 < gammaCert10 := by
  norm_num [gammaCert10, gammaOf, kPcert10, kq10, kDcert, Finset.sum_range_succ]

theorem kPcert10_nonneg (i : ℕ) : 0 ≤ kPcert10 i := by
  unfold kPcert10 kq10; split_ifs <;> norm_num

/-- The computational input for side 10 (`cert_2_10.json`). -/
def CertifiedInfluence10 (N : ℕ) [NeZero N] : Prop :=
  ∀ x z, z ∉ thinCube (d := 2) (N := N) 10 x → InShell (thinCube 10 x) z →
    IsInfluenceBoundW arc (thinCube 10 x) (gaugeSpec (G := Un 1) 1 phi2 (thinCube 10 x)) z
      (kappa 10 kPcert10 kDcert x z)

/-- **Decay from the smallest certified box** (side 10, `γ ≤ 0.9924`): as `twoD_U1_decay`, for even `N ≥ 13`, at every rate
`λ < log(1/γ)/11` (about `7·10⁻⁴`; side 11 gives the better rate). -/
theorem twoD_U1_decay_10 {N : ℕ} [NeZero N] (hEven : Even N) (hN : 13 ≤ N) (hcert : CertifiedInfluence10 N)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < Real.log (1 / gammaCert10) / 11)
    {F : GaugeConnection (Un 1) 2 N → ℝ} (hF : BM F) {s : ℕ} (hFs : DepOn F (timeSlab 0 s))
    {w : LatticeLink 2 N → ℝ} (hw0 : ∀ l, 0 ≤ w l) (hw : LipBound arc F w) {V L : ℝ} (hV : ∑ l, w l ≤ V)
    (hL : ∀ l, w l ≤ L) {m r : ℕ} (hr : 1 ≤ r) (hNr : 2 ^ (r + 1) * m + 2 * s + 2 ≤ N) :
    |corr 1 phi2 F m| ≤
      (corr 1 phi2 F 0 + (1 / 2 : ℝ) ^ r * cubeConstW 2 10 gammaCert10 lam V L Real.pi) * Real.exp (-(lam * m)) := by
  have hρ : gammaCert10 * Real.exp (lam * (((10 : ℕ) : ℝ) + 1)) < 1 :=
    rate_lt_of_lt gammaCert10_pos (by norm_num) (by rw [show (((10 : ℕ) : ℝ) + 1) = 11 by norm_num]; exact hlam)
  have hgds : GDS (thinCube (d := 2) (N := N) 10) (kappaT 10 kPcert10 kDcert) gammaCert10 :=
    gds_kappaT (by norm_num) (by omega) kPcert10_nonneg (by norm_num [kDcert])
  exact gauge_decay_finiteVolume_W rep_continuous rep_unitary hEven arc_nonneg arc_le_pi arc_pos arc_inv
    (posWeight_exp 1 2) (by norm_num) (influence_of_shell hcert) gammaCert10_pos.le hgds hlam0 hρ hF hFs hw0 hw hV hL
    hr hNr

end Attempts.R2.TwoD
