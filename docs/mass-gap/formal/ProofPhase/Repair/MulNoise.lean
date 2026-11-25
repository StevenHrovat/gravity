/-
Proof phase, cycle 5, workstream 3 (c5c-repair): the multiplicative noisy blocking (smeared value times independent
noise per coarse link) as a `NoisyRPBlocking` (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5c-repair/NOTE.md`, section 3.2.
-/

import ProofPhase.Repair.Noisy

/-!
# The multiplicative noisy blocking is reflection-respecting

Given a deterministic reflection-respecting blocking `P` (for example the good blocking of `RouteA/Blocking.lean`), the
**noisy blocking** multiplies every coarse link by an independent noise element:

* a link fixed by the reflection (spatial, in the slices `t = 0, M/2`): `φ_l = b_l · c_l`;
* a positive link: `φ_l = b_l · a_l`;
* the mirror `l = m(p)` of a positive link `p`: `φ_l = b_l · a'_p` if `l` is spatial, `φ_l = (a'_p)⁻¹ · b_l` if `l` is
  temporal (the reflection reverses temporal links, so the noise is put on the other side),

where `b = P.B U`. With the noise laws `c_l, a_p, a'_p` i.i.d. with a density `h` w.r.t. Haar that is a **class function**
and **inversion symmetric** (the heat kernel is both), the conditional law of every coarse link given `U` is
`h(b_l⁻¹ φ_l) dφ_l`, the same on all links (NOTE §3.2); the side on which the noise sits is invisible in law.

* `mulNoise`, `mulNoise_fixed`, `mulNoise_pos`, `mulNoise_mirror` (definitions and the three cases).
* **`mulNoise_theta`** (S): `Θ(mulNoise b (c, a, a')) = mulNoise (Θ b) (c, a', a)`.
* **`mulNoiseBlocking`** (S): the multiplicative noisy blocking of any `RPBlocking` is a `NoisyRPBlocking`
  (measurable, reflection-covariant with `a ↔ a'`, positive-half property). Hence `noisy_blocked_wilson_rp` applies:
  **every layer of the noisy good blocking is reflection positive** (`goodNoisy_rp`).
* `goodNoisyFamily` (S): the noisy good blocking family, for any single-link noise law `τ` (a probability measure).

**Claim level.** All proved. Not proved here: `KernelDensity` for this family when `τ = h · Haar` with `0 < m ≤ h ≤ M`
(on paper, NOTE §3.2: left invariance of Haar measure and the class-function property; the Lean proof needs a reindexing
of `Measure.pi` along `linkSplit`, about a hundred lines, listed as next step), and gauge covariance (in law; NOTE §3.2).
-/

open MeasureTheory Finset AreaLaw.Concrete Positivity OneScale

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Repair

section MulNoise

variable {d M : ℕ} [NeZero d] [NeZero M] {G : Type*} [Group G]

/-- **The multiplicative noise.** -/
def mulNoise (hM : Even M) (b : GaugeConnection G d M) (η : (FixLink d M → G) × (PosLink d M → G) × (PosLink d M → G)) :
    GaugeConnection G d M := fun l =>
  if h1 : IsFixedLink l then b l * η.1 ⟨l, h1⟩
  else if h2 : IsPosLink l then b l * η.2.1 ⟨l, h2⟩
  else if l.dir = 0 then (η.2.2 ⟨mirrorLink l, link_neg_mirror hM h1 h2⟩)⁻¹ * b l
  else b l * η.2.2 ⟨mirrorLink l, link_neg_mirror hM h1 h2⟩

variable (hM : Even M) (b : GaugeConnection G d M) (η : (FixLink d M → G) × (PosLink d M → G) × (PosLink d M → G))

theorem mulNoise_fixed {l : LatticeLink d M} (h1 : IsFixedLink l) : mulNoise hM b η l = b l * η.1 ⟨l, h1⟩ :=
  dite_eq_left h1

theorem mulNoise_pos {l : LatticeLink d M} (h2 : IsPosLink l) : mulNoise hM b η l = b l * η.2.1 ⟨l, h2⟩ := by
  unfold mulNoise
  rw [dite_eq_right (not_fixed_of_pos h2), dite_eq_left h2]

theorem mulNoise_neg {l : LatticeLink d M} (h1 : ¬IsFixedLink l) (h2 : ¬IsPosLink l) :
    mulNoise hM b η l = if l.dir = 0 then (η.2.2 ⟨mirrorLink l, link_neg_mirror hM h1 h2⟩)⁻¹ * b l
      else b l * η.2.2 ⟨mirrorLink l, link_neg_mirror hM h1 h2⟩ := by
  unfold mulNoise
  rw [dite_eq_right h1, dite_eq_right h2]

theorem mulNoise_mirror (p : PosLink d M) :
    mulNoise hM b η (mirrorLink p.1) =
      if p.1.dir = 0 then (η.2.2 p)⁻¹ * b (mirrorLink p.1) else b (mirrorLink p.1) * η.2.2 p := by
  obtain ⟨h1, h2⟩ := link_pos_mirror hM p.2
  rw [mulNoise_neg hM b η h1 h2, mirrorLink_dir]
  have e : (⟨mirrorLink (mirrorLink p.1), link_neg_mirror hM h1 h2⟩ : PosLink d M) = p :=
    Subtype.ext (mirrorLink_involutive p.1)
  rw [e]

/-- **The noise commutes with the reflection when the positive and negative noises are swapped.** -/
theorem mulNoise_theta (c : FixLink d M → G) (a a' : PosLink d M → G) :
    thetaConn (mulNoise hM b (c, a, a')) = mulNoise hM (thetaConn b) (c, a', a) := by
  funext l
  rw [thetaConn_eq]
  by_cases h1 : IsFixedLink l
  · have hm := link_fixed_mirror hM h1
    have hd : l.dir ≠ 0 := h1.1
    rw [hm, mulNoise_fixed hM b _ h1, mulNoise_fixed hM _ _ h1, thetaConn_eq, hm]
    simp [linkTwist, hd]
  by_cases h2 : IsPosLink l
  · rw [show mirrorLink l = mirrorLink (⟨l, h2⟩ : PosLink d M).1 from rfl, mulNoise_mirror hM b _ ⟨l, h2⟩,
      mulNoise_pos hM _ _ h2, thetaConn_eq]
    by_cases hd : l.dir = 0
    · simp [linkTwist, hd, mul_inv_rev]
    · simp [linkTwist, hd]
  · have hq := link_neg_mirror hM h1 h2
    rw [mulNoise_pos hM b _ hq, mulNoise_neg hM _ _ h1 h2, thetaConn_eq]
    by_cases hd : l.dir = 0
    · simp [linkTwist, hd, mul_inv_rev]
    · simp [linkTwist, hd]

/-- On the closed positive half the noisy field does not read the negative noise `a'`. -/
theorem mulNoise_posHalf [Fintype (LatticeLink d M)] {l : LatticeLink d M} (hl : l ∈ posHalfLinks d M)
    (c : FixLink d M → G) (a a₁ a₂ : PosLink d M → G) (b' : GaugeConnection G d M) (hb : b l = b' l) :
    mulNoise hM b (c, a, a₁) l = mulNoise hM b' (c, a, a₂) l := by
  simp only [posHalfLinks, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  rcases hl with h2 | h1
  · rw [mulNoise_pos hM _ _ h2, mulNoise_pos hM _ _ h2, hb]
  · rw [mulNoise_fixed hM _ _ h1, mulNoise_fixed hM _ _ h1, hb]

end MulNoise

section Blocking

variable {d N M : ℕ} [NeZero d] [NeZero N] [NeZero M]
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

/-- **The multiplicative noisy blocking of a reflection-respecting blocking** is a noisy reflection-respecting
blocking. -/
def mulNoiseBlocking (hM : Even M) (P : RPBlocking G d N M) :
    NoisyRPBlocking G d N M (FixLink d M → G) (PosLink d M → G) where
  B U η := mulNoise hM (P.B U) η
  meas := by
    refine measurable_pi_iff.2 fun l => ?_
    have hb : Measurable (fun q : GaugeConnection G d N × ((FixLink d M → G) × (PosLink d M → G) ×
        (PosLink d M → G)) => P.B q.1 l) := (measurable_pi_apply l).comp (P.meas.comp measurable_fst)
    by_cases h1 : IsFixedLink l
    · simp only [mulNoise, dite_eq_left h1]
      exact hb.mul ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd))
    by_cases h2 : IsPosLink l
    · simp only [mulNoise, dite_eq_right h1, dite_eq_left h2]
      exact hb.mul ((measurable_pi_apply _).comp ((measurable_fst.comp measurable_snd).comp measurable_snd))
    · have ha : Measurable (fun q : GaugeConnection G d N × ((FixLink d M → G) × (PosLink d M → G) ×
          (PosLink d M → G)) => q.2.2.2 ⟨mirrorLink l, link_neg_mirror hM h1 h2⟩) :=
        (measurable_pi_apply _).comp ((measurable_snd.comp measurable_snd).comp measurable_snd)
      by_cases hd : l.dir = 0
      · simp only [mulNoise, dite_eq_right h1, dite_eq_right h2, hd, ite_true]
        exact ha.inv.mul hb
      · simp only [mulNoise, dite_eq_right h1, dite_eq_right h2, hd, ite_false]
        exact hb.mul ha
  theta U c a a' := by
    simp only [P.theta, mulNoise_theta]
  half F hF U U' c a a₁ a₂ h := by
    have hF' : LinkDep (fun b => F (mulNoise hM b (c, a, a))) (posHalfLinks d M) := by
      intro b b' hbb
      exact hF _ _ fun l hl => mulNoise_posHalf hM b hl c a a a b' (hbb l hl)
    have e : ∀ (b : GaugeConnection G d M) (a₀ : PosLink d M → G),
        F (mulNoise hM b (c, a, a₀)) = F (mulNoise hM b (c, a, a)) := fun b a₀ =>
      hF _ _ fun l hl => mulNoise_posHalf hM b hl c a a₀ a b rfl
    show F (mulNoise hM (P.B U) (c, a, a₁)) = F (mulNoise hM (P.B U') (c, a, a₂))
    rw [e (P.B U) a₁, e (P.B U') a₂]
    exact P.half _ hF' U U' h

end Blocking

/-! ## The noisy good blocking family -/

/-- **The noisy good blocking family**: the good blocking (`RouteA.goodBlocking`) followed by independent multiplicative
noise with single-link law `τ` on every coarse link. -/
def goodNoisyFamily (T : Tuning) (w : ℝ) (n : ℕ → ℕ) (hn : ∀ k, T.ℓ k = 2 ^ n k) (τ : Measure SU2)
    [IsProbabilityMeasure τ] :
    NoisyBlockingFamily T (fun j => FixLink 4 (coarseSide j) → SU2) (fun j => PosLink 4 (coarseSide j) → SU2) where
  blk k j := mulNoiseBlocking (RouteA.even_coarseSide j) (RouteA.goodBlocking T w n hn k j)
  ν0 _ _ := Measure.pi fun _ => τ
  νp _ _ := Measure.pi fun _ => τ
  prob0 _ _ := inferInstance
  probp _ _ := inferInstance

/-- **Every layer of the noisy good blocking is reflection positive** (S). -/
theorem goodNoisy_rp (T : Tuning) (w : ℝ) (n : ℕ → ℕ) (hn : ∀ k, T.ℓ k = 2 ^ n k) (τ : Measure SU2)
    [IsProbabilityMeasure τ] (k j : ℕ) {F : GaugeConnection SU2 4 (coarseSide j) → ℝ}
    (hF : LinkDep F (posHalfLinks 4 (coarseSide j))) (mF : Measurable F) (bF : ∃ C, ∀ V, |F V| ≤ C) :
    0 ≤ ∫ c, ∫ q : (PosLink 4 (coarseSide j) → SU2) × (PosLink 4 (coarseSide j) → SU2), ∫ U,
        F (((goodNoisyFamily T w n hn τ).blk k j).B U (c, q.1, q.2)) *
        F (thetaConn (((goodNoisyFamily T w n hn τ).blk k j).B U (c, q.1, q.2))) *
        ∏ p ∈ (univ : Finset (LatticePlaquette 4 (T.side k j))), Real.exp (T.β k * xp 2 p U)
          ∂(productHaar SU2 4 (T.side k j)) ∂((Measure.pi fun _ => τ).prod (Measure.pi fun _ => τ))
          ∂(Measure.pi fun _ => τ) :=
  noisyFamily_rp (goodNoisyFamily T w n hn τ) k j hF mF bF

end ProofPhase.Repair
