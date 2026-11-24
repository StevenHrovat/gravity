/-
Cycle 4, workstream 4 (c4d): the W₁ column of the measured blocked action, certified (2026-11-22).
Released under Apache 2.0.

Reference text: `docs/mass-gap/weak-coupling/proof-phase/c4d-certified/NOTE.md` (PREREG.md there).
-/

import ProofPhase.Certified.AdjointW

/-!
# The measured action at `L√σ = 2.80`: anisotropic plaquette action, W₁ column below `1`

**Setting.** The good blocking at `β = 2.3`, `b = 8` (cycle 3, `c3b-refit`) leaves the coarse SU(2) lattice `(ℤ/Nℤ)⁴` with an effective
action fitted by two plane-class–resolved plaquette families: time-like plaquettes (plane contains direction `0`, i.e. `dir1 = 0`) and
space-like ones, each with the factor `φ(t) = β_F t + (β_A/3)(4t² − 1) + β_T(2t³ − t)`, `t = ½ Re tr U_p` (`planeFactor`). The
fit values (and the box of ±3σ of all four fits, rounded up) are in `PREREG.md`; the base fit has `β_T = 0`; the extension `ext_T` has
`β_T ≠ 0`. The 1×2 rectangle extension is **not** in this file (the lattice here has plaquette supports only); its certified column
is in the note.

* `measuredAction`: the anisotropic action as a local potential (`potential_measuredAction`).
* **`CertifiedMeasured`: the computational input, one named hypothesis** (computer-assisted: NOTE.md, `cert_measured.py`): for every
  coupling vector in the box and every torus `N ≥ 2`, a link `z` influences the single-link conditional law of `i` by at most
  `Kmeas` per plaquette containing both (W₁, geodesic cost). `Kmeas = 0.05442` bounds the per-plaquette coefficient of **both** plane
  classes (`k_ts ≤ 0.0181`, `k_ss ≤ 0.05442`, certified over the box); the class-resolved column (0.761) is in the note, the Lean
  column below uses the uniform constant (`18·Kmeas = 0.9796`).
* `kMeas_column_lt_one`: `18 · Kmeas < 1`, **by `norm_num`**.
* **`limitDprimeW_measured`**: under `CertifiedMeasured`, every action in the box satisfies `LimitDprimeW` (W₁ form of D′, column sum
  `≤ 18 · Kmeas < 1`, range 1, every volume); **`measured_decay`**: uniform exponential decay.

**Claim level.** Proved in Lean except `CertifiedMeasured` (paper reduction + interval arithmetic). It is a statement about the
**fitted, truncated, anisotropic effective action** on the coarse torus, not about the lattice Yang–Mills theory: the distance to the
true blocked action (`H1LocalLip`, truncation, and the fit's closure residuals) and `ObsTransferPhys` are untouched.
-/

open MeasureTheory Finset OneScale Attempts.R3 AreaLaw.Concrete

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Certified

section Measured

variable {N : ℕ} [NeZero N]

/-- One plane class' plaquette factor `β_F t + (β_A/3)(4t² − 1) + β_T(2t³ − t)`. -/
def planeFactor (βF βA βT : ℝ) (p : LatticePlaquette 4 N) (U : GaugeConnection SU2 4 N) : ℝ :=
  βF * tp p U + βA / 3 * (4 * tp p U ^ 2 - 1) + βT * (2 * tp p U ^ 3 - tp p U)

/-- **The measured anisotropic action**: time-like plaquettes (`dir1 = 0`, the plane contains the time direction) carry
`(Fts, Ats, Tts)`, space-like ones `(Fss, Ass, Tss)`. -/
def measuredAction (Fts Fss Ats Ass Tts Tss : ℝ) (p : LatticePlaquette 4 N) (U : GaugeConnection SU2 4 N) : ℝ :=
  if p.dir1 = 0 then planeFactor Fts Ats Tts p U else planeFactor Fss Ass Tss p U

theorem abs_planeFactor_le (βF βA βT : ℝ) (p : LatticePlaquette 4 N) (U : GaugeConnection SU2 4 N) :
    |planeFactor βF βA βT p U| ≤ |βF| + |βA| + |βT| := by
  have ht := abs_tp_le p U
  set t := tp p U with htdef
  have ht1 := abs_le.1 ht
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht1.1, ht1.2]
  have h4 : |4 * t ^ 2 - 1| ≤ 3 := abs_le.2 ⟨by nlinarith [sq_nonneg t], by linarith⟩
  have h3 : |2 * t ^ 3 - t| ≤ 1 := by
    refine abs_le.2 ⟨?_, ?_⟩
    · nlinarith [mul_nonneg (by linarith [ht1.1] : (0 : ℝ) ≤ t + 1) (add_nonneg (sq_nonneg t) (sq_nonneg (t - 1)))]
    · nlinarith [mul_nonneg (by linarith [ht1.2] : (0 : ℝ) ≤ 1 - t) (add_nonneg (sq_nonneg t) (sq_nonneg (t + 1)))]
  unfold planeFactor
  calc |βF * t + βA / 3 * (4 * t ^ 2 - 1) + βT * (2 * t ^ 3 - t)|
      ≤ |βF * t + βA / 3 * (4 * t ^ 2 - 1)| + |βT * (2 * t ^ 3 - t)| := abs_add_le _ _
    _ ≤ (|βF * t| + |βA / 3 * (4 * t ^ 2 - 1)|) + |βT * (2 * t ^ 3 - t)| := by
        gcongr; exact abs_add_le _ _
    _ = (|βF| * |t| + |βA| / 3 * |4 * t ^ 2 - 1|) + |βT| * |2 * t ^ 3 - t| := by
        rw [abs_mul, abs_mul, abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    _ ≤ (|βF| * 1 + |βA| / 3 * 3) + |βT| * 1 := by gcongr
    _ = |βF| + |βA| + |βT| := by ring

theorem measurable_planeFactor (βF βA βT : ℝ) (p : LatticePlaquette 4 N) :
    Measurable (planeFactor (N := N) βF βA βT p) := by
  have h : Measurable (tp (N := N) p) := (measurable_xp su2_rep_continuous p).div_const 2
  unfold planeFactor
  exact ((h.const_mul βF).add ((((h.pow_const 2).const_mul 4).sub_const 1).const_mul (βA / 3))).add
    ((((h.pow_const 3).const_mul 2).sub h).const_mul βT)

theorem planeFactor_dep (βF βA βT : ℝ) (p : LatticePlaquette 4 N) (U U' : GaugeConnection SU2 4 N)
    (h : ∀ l ∈ plaqSupp p, U l = U' l) : planeFactor βF βA βT p U = planeFactor βF βA βT p U' := by
  have e : tp p U = tp p U' := by
    have hh : plaquetteHolonomy U p = plaquetteHolonomy U' p := plaquetteHolonomy_dependsOn p U U' h
    unfold tp xp
    rw [hh]
  unfold planeFactor
  rw [e]

/-- **The measured action is a local potential** (measurable, bounded, each factor reads only its plaquette). -/
theorem potential_measuredAction (Fts Fss Ats Ass Tts Tss : ℝ) :
    Potential (plaqSupp (N := N)) (measuredAction Fts Fss Ats Ass Tts Tss) where
  meas p := by
    unfold measuredAction
    by_cases h : p.dir1 = 0
    · simp only [h, ite_true]; exact measurable_planeFactor _ _ _ p
    · simp only [h, ite_false]; exact measurable_planeFactor _ _ _ p
  bdd := ⟨|Fts| + |Ats| + |Tts| + (|Fss| + |Ass| + |Tss|), fun p U => by
    unfold measuredAction
    have a1 := abs_planeFactor_le Fts Ats Tts p U
    have a2 := abs_planeFactor_le Fss Ass Tss p U
    have b1 := abs_nonneg Fts; have b2 := abs_nonneg Ats; have b3 := abs_nonneg Tts
    have c1 := abs_nonneg Fss; have c2 := abs_nonneg Ass; have c3 := abs_nonneg Tss
    split_ifs
    · linarith
    · linarith⟩
  dep p U U' h := by
    unfold measuredAction
    by_cases hp : p.dir1 = 0
    · simp only [hp, ite_true]; exact planeFactor_dep _ _ _ p U U' h
    · simp only [hp, ite_false]; exact planeFactor_dep _ _ _ p U U' h

end Measured

/-! ## The box and the certified constant -/

/-- The box of couplings (`PREREG.md`): contains the ±3σ box of the base fit and of `ext_T`; bounds rounded up. -/
def boxFts : ℝ := 545 / 10000
def boxFss : ℝ := 1725 / 10000
def boxAts : ℝ := 11 / 10000
def boxAss : ℝ := 20 / 10000
def boxTts : ℝ := 9 / 10000
def boxTss : ℝ := 9 / 10000

/-- Certified per-plaquette W₁ influence bound of the measured action over the box, rounded up from `0.0544198`
(`cert_measured.json`, `ext_T`, box ×1.0: `k_ss`; the time-like class has `k_ts ≤ 0.0181`, below it). -/
def Kmeas : ℝ := 5442 / 100000

theorem Kmeas_nonneg : 0 ≤ Kmeas := by norm_num [Kmeas]

/-- **The certified column sum is below `1`** (`norm_num`). -/
theorem kMeas_column_lt_one : 18 * Kmeas < 1 := by norm_num [Kmeas]

/-- **The computational input (computer-assisted; NOTE.md, `cert_measured.py`, `cert_measured.json`).** For every torus `(ℤ/Nℤ)⁴`,
`N ≥ 2`, and every coupling vector in the box: a link `z` influences the single-link conditional law of a link `i` by at most
`Kmeas` per plaquette containing both (W₁ for the geodesic cost of `S³`). -/
def CertifiedMeasured : Prop :=
  ∀ (N : ℕ) [NeZero N], 2 ≤ N → ∀ Fts Fss Ats Ass Tts Tss : ℝ, |Fts| ≤ boxFts → |Fss| ≤ boxFss → |Ats| ≤ boxAts →
    |Ass| ≤ boxAss → |Tts| ≤ boxTts → |Tss| ≤ boxTss →
    SiteInfluenceW (haarG SU2) (plaqSupp (N := N)) (measuredAction Fts Fss Ats Ass Tts Tss) geodSU2
      (fun i z => Kmeas * OneScale.SingleLink.common i z)

/-- The column sum of the certified coefficients: at most `18 · Kmeas`. -/
theorem measured_column_le {N : ℕ} [NeZero N] (z : LatticeLink 4 N) :
    ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (LatticeLink 4 N))),
      Kmeas * (OneScale.SingleLink.common i z : ℝ) ≤ 18 * Kmeas := by
  rw [← mul_sum, mul_comm (18 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ Kmeas_nonneg
  have h := OneScale.SingleLink.sum_common_le (d := 4) (N := N) z
  have h' : ((∑ e ∈ univ.filter (fun e => z ∉ ({e} : Finset (LatticeLink 4 N))),
      OneScale.SingleLink.common e z : ℕ) : ℝ) ≤ 18 := by exact_mod_cast h
  simpa [Nat.cast_sum] using h'

/-- Links with a positive certified coefficient share a plaquette, so they are at distance at most `1`. -/
theorem measured_dist_le {N : ℕ} [NeZero N] {i z : LatticeLink 4 N}
    (h : Kmeas * (OneScale.SingleLink.common i z : ℝ) ≠ 0) : OneScale.LinkDist.linkDist z i ≤ 1 := by
  have hc : OneScale.SingleLink.common i z ≠ 0 := by
    intro h0; apply h; rw [h0, Nat.cast_zero, mul_zero]
  obtain ⟨p, hp⟩ := Finset.card_ne_zero.1 hc
  simp only [mem_filter, mem_univ, true_and] at hp
  exact OneScale.LinkDist.linkDist_le_one_of_plaq hp.1 hp.2

/-- **The measured action in the box satisfies the W₁ form of D′**, in every coarse volume, with `γ = 18 · Kmeas < 1`. -/
theorem limitDprimeW_measured (hcert : CertifiedMeasured) {Fts Fss Ats Ass Tts Tss : ℝ} (h1 : |Fts| ≤ boxFts)
    (h2 : |Fss| ≤ boxFss) (h3 : |Ats| ≤ boxAts) (h4 : |Ass| ≤ boxAss) (h5 : |Tts| ≤ boxTts) (h6 : |Tss| ≤ boxTss) :
    LimitDprimeW (fun _ => measuredAction Fts Fss Ats Ass Tts Tss) :=
  ⟨18 * Kmeas, mul_nonneg (by norm_num) Kmeas_nonneg, kMeas_column_lt_one, fun j =>
    ⟨fun i z => Kmeas * OneScale.SingleLink.common i z,
      hcert (coarseSide j) (two_le_coarseSide j) Fts Fss Ats Ass Tts Tss h1 h2 h3 h4 h5 h6,
      fun z => measured_column_le z, fun i z h => measured_dist_le h⟩⟩

/-- **Exponential decay for every measured action in the box**, uniformly in `N ≥ 2`, at every `λ ≥ 0` with
`18 · Kmeas · e^λ < 1`. -/
theorem measured_decay (hcert : CertifiedMeasured) {N : ℕ} [NeZero N] (hN : 2 ≤ N) {Fts Fss Ats Ass Tts Tss : ℝ}
    (h1 : |Fts| ≤ boxFts) (h2 : |Fss| ≤ boxFss) (h3 : |Ats| ≤ boxAts) (h4 : |Ass| ≤ boxAss) (h5 : |Tts| ≤ boxTts)
    (h6 : |Tss| ≤ boxTss) {lam : ℝ} (hlam : 0 ≤ lam) (hρ : 18 * Kmeas * Real.exp lam < 1)
    {f g : GaugeConnection SU2 4 N → ℝ} (hf : BM f) (hg : BM g) {A Sg : Finset (LatticeLink 4 N)} (hfA : DepOn f A)
    (hgS : DepOn g Sg) {vf : LatticeLink 4 N → ℝ} (hvf : OscBound f vf) {Lg : ℝ} (hLg : 0 ≤ Lg)
    (hvg : LipBound geodSU2 g (fun _ => Lg)) {R : ℝ} (hR : ∀ a ∈ A, ∀ s ∈ Sg, R ≤ OneScale.LinkDist.linkDist a s) :
    |∫ σ, f σ * g σ ∂(gibbsMeasure (haarG SU2) (measuredAction Fts Fss Ats Ass Tts Tss)) -
        (∫ σ, f σ ∂(gibbsMeasure (haarG SU2) (measuredAction Fts Fss Ats Ass Tts Tss))) *
          ∫ σ, g σ ∂(gibbsMeasure (haarG SU2) (measuredAction Fts Fss Ats Ass Tts Tss))| ≤
      Real.pi / (1 - 18 * Kmeas * Real.exp lam) * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R)) := by
  have : Nonempty (LatticeLink 4 N) := ⟨⟨0, 0⟩⟩
  have h := decay_of_siteW (haarG SU2) (potential_measuredAction (N := N) Fts Fss Ats Ass Tts Tss) geodSU2_nonneg
    geodSU2_le_pi (hcert N hN Fts Fss Ats Ass Tts Tss h1 h2 h3 h4 h5 h6) (mul_nonneg (by norm_num) Kmeas_nonneg)
    (fun z => measured_column_le z)
    OneScale.LinkDist.linkDist OneScale.LinkDist.linkDist_self OneScale.LinkDist.linkDist_triangle (D₁ := 1)
    (fun i z _ h => measured_dist_le h) hlam (by rw [mul_one]; exact hρ) hf hg hfA hgS hvf hLg hvg hR
  simpa only [mul_one] using h

/-- A positive rate exists. -/
theorem exists_rate_measured : ∃ lam : ℝ, 0 < lam ∧ 18 * Kmeas * Real.exp lam < 1 :=
  OneScale.SingleLink.exists_rate (mul_nonneg (by norm_num) Kmeas_nonneg) kMeas_column_lt_one

end ProofPhase.Certified
