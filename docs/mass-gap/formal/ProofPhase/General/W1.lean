/-
Proof phase, generalisation phase 1c: the W₁ route over any gauge group and dimension (2026-11-24).
Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/general/NOTE.md`, phase 1c.
-/

import ProofPhase.General.Level
import ProofPhase.General.Recursion
import ProofPhase.V3.W1Route
import ProofPhase.V4.Gap

/-!
# The W₁ route, over any gauge group and dimension

`V3/W1Route` and the second half of `V4/Gap` for the Wilson measure of any `Gr` of the package in dimension `d`, with the
cost distance a parameter `cost` (`geodSU2` for SU(2), `geodSUN` for SU(N)). The two facts used about it are
`0 ≤ cost ≤ P` (`P = π` for the geodesic distances). Ported: `LevelDprimeW`, `BlockGapUnifW`,
`blockGapUnifW_of_levelDprimeW`, `ObsTransferPhysTW`, `ObsQuasiLocTW`, `obsTransferPhysTW_of_condMassDecay`,
`obsTransferPhysTW_of_condMass`, `wcorr_le_blockedW`, `torusDecayLoc_of_blockGapUnifW`, `LevelTorusRouteW`,
`bothOrdersLoc_of_levelRouteW`; `levelDprimeW_iff_on`, `blockGapUnifW_iff_lawGapW`, `blockGapBddW_iff_lawGapBddW`,
`blockGapBddW_of_unifW`, `torusDecayLoc_of_blockGapBddW`. Not ported (they name the certified SU(2) window):
`H1LocalLipW`, `levelDprimeW_of_h1LocalLip`, `levelDprimeW_of_certified`.
-/

open MeasureTheory Finset Filter Topology AreaLaw.Concrete OneScale OneScale.Gauge OneScale.LinkDist
  OneScale.TimeShift Positivity

open ProofPhase (IsLimitPoint)
open ProofPhase.Certified (SiteInfluenceW decay_of_siteW)
open ProofPhase.RouteA (cov_transfer gaugeInvariant_tShift gaugeInvariant_thetaConn)
open ProofPhase.V3 (timeDist timeDist_le_linkDist abs_condDefect_le_of_ae)
open ProofPhase.UV

open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.General

section W1

variable {Gr : Type*} [Group Gr] [TopologicalSpace Gr] [MeasurableSpace Gr] [HasHaarProbability Gr]
  (nr : ℕ) [HasGaugeTrace Gr nr] [GaugeGroupBase Gr] {d : ℕ} [NeZero d] (cost : Gr → Gr → ℝ)

def LevelDprimeW (T : Tuning) (B : BlockingFamily Gr d T) (lam : ℝ) : Prop :=
  ∃ γ D₁ : ℝ, 0 ≤ γ ∧ γ * Real.exp (lam * D₁) < 1 ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ j, ∃ V : CoarsePot Gr d j,
    blockedLaw nr T B k j = Attempts.R3.gibbsMeasure (haarG Gr) V ∧ Attempts.R3.Potential (fun A => A) V ∧
    ∃ kk : LatticeLink d (coarseSide j) → LatticeLink d (coarseSide j) → ℝ,
      SiteInfluenceW (haarG Gr) (fun A => A) V cost kk ∧
      (∀ z, ∑ i ∈ univ.filter (fun i => z ∉ ({i} : Finset (LatticeLink d (coarseSide j)))), kk i z ≤ γ) ∧
      (∀ i z, z ∉ ({i} : Finset (LatticeLink d (coarseSide j))) → kk i z ≠ 0 → linkDist z i ≤ D₁)

def BlockGapUnifW (T : Tuning) (B : BlockingFamily Gr d T) (lam : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink d (coarseSide j)))
    (vf : LatticeLink d (coarseSide j) → ℝ) (Lg R : ℝ),
    BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg → LipBound cost g (fun _ => Lg) →
    (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
    |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j) -
        (∫ U, f ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)) * ∫ U, g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)| ≤
      C * (∑ a ∈ A, vf a) * Lg * Real.exp (-(lam * R))

def ObsTransferPhysTW (T : Tuning) (B : BlockingFamily Gr d T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection Gr d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ), 0 ≤ D →
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e') →
    ∃ (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink d (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink d (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ d) ∧
      LipBound cost g (fun _ => K) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U - f ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U - g ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      |∫ U, F U * G U ∂(ymLaw (G := Gr) nr d T k j) -
          ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U *
            condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U ∂(ymLaw (G := Gr) nr d T k j)|
        ≤ c * Real.exp (-(m * D))

def ObsQuasiLocTW (T : Tuning) (B : BlockingFamily Gr d T) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ R : ℝ, ∃ c K : ℝ, 0 ≤ c ∧ 0 ≤ K ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (j : ℕ)
    (F G : GaugeConnection Gr d (T.side k j) → ℝ) (A₀ B₀ : Finset (LatticeLink d (T.side k j))) (D : ℝ), 0 ≤ D →
    Measurable F → Measurable G → (∀ U, |F U| ≤ 1) → (∀ U, |G U| ≤ 1) → GaugeInvariant F → GaugeInvariant G →
    DepOn F A₀ → DepOn G B₀ → PhysExtent T k A₀ R → PhysExtent T k B₀ R →
    (∀ e ∈ A₀, ∀ e' ∈ B₀, D ≤ T.a k * timeDist e e') →
    ∃ (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink d (coarseSide j))),
      Measurable f ∧ Measurable g ∧ (∀ V, |f V| ≤ 1) ∧ (∀ V, |g V| ≤ 1) ∧ DepOn f A' ∧ DepOn g B' ∧
      (∃ vf : LatticeLink d (coarseSide j) → ℝ, OscBound f vf ∧ ∑ a ∈ A', vf a ≤ 2 * K * (1 + D / T.L₁) ^ d) ∧
      LipBound cost g (fun _ => K) ∧
      (∀ x ∈ A', ∀ y ∈ B', D / 2 ≤ T.L₁ * linkDist x y) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) F U - f ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D)) ∧
      ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) G U - g ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j)
        ≤ c * Real.exp (-(m * D))

variable [GaugeRep Gr nr]

theorem blockGapUnifW_of_levelDprimeW {P : ℝ} (hc0 : ∀ a b, 0 ≤ cost a b) (hP : ∀ a b, cost a b ≤ P) {T : Tuning}
    (B : BlockingFamily Gr d T) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : LevelDprimeW nr cost T B lam) : BlockGapUnifW nr cost T B lam := by
  obtain ⟨γ, D₁, hγ0, hρ, k₀, H⟩ := h
  have hP0 : 0 ≤ P := (hc0 1 1).trans (hP 1 1)
  refine ⟨P / (1 - γ * Real.exp (lam * D₁)), div_nonneg hP0 (by linarith), k₀,
    fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hvg hR => ?_⟩
  obtain ⟨V, hgibbs, hpot, kk, hk', hcol, hD₁⟩ := H k hk j
  have : Nonempty (LatticeLink d (coarseSide j)) := ⟨⟨fun _ => 1, ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩⟩
  rw [Effective.cov_map (ymLaw (G := Gr) nr d T k j) (B k j).meas hf hg]
  have e : (ymLaw (G := Gr) nr d T k j).map (B k j).B = Attempts.R3.gibbsMeasure (haarG Gr) V := hgibbs
  rw [e]
  exact decay_of_siteW (haarG Gr) hpot hc0 hP hk' hγ0 hcol linkDist linkDist_self
    linkDist_triangle hD₁ hlam hρ hf hg hfA hgS hvf hLg hvg hR

theorem obsTransferPhysTW_of_condMassDecay {T : Tuning} {B : BlockingFamily Gr d T} (h1 : CondMassDecay nr T B)
    (h2 : ObsQuasiLocTW nr cost T B) : ObsTransferPhysTW nr cost T B := by
  obtain ⟨m₁, hm₁, H1⟩ := h1
  obtain ⟨m₂, hm₂, H2⟩ := h2
  refine ⟨min m₁ m₂, lt_min hm₁ hm₂, fun R => ?_⟩
  obtain ⟨c₁, hc₁, k₁, Hk1⟩ := H1 R
  obtain ⟨c₂, K, hc₂, hK, k₂, Hk2⟩ := H2 R
  refine ⟨c₁ + c₂, K, by positivity, hK, max k₁ k₂,
    fun k hk j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep => ?_⟩
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hlip, hsep', hEF, hEG⟩ :=
    Hk2 k ((le_max_right _ _).trans hk) j F G A₀ B₀ D hD mF mG bF bG gF gG dF dG eA eB hsep
  have hae := Hk1 k ((le_max_left _ _).trans hk) j F G A₀ B₀ D mF mG bF bG dF dG eA
    (fun e he e' he' => (hsep e he e' he').trans
      (mul_le_mul_of_nonneg_left (timeDist_le_linkDist e e') (T.a_pos k).le))
  have := isProbabilityMeasure_wilsonMeasure (G := Gr) (n := nr) d (T.side k j) (T.β k)
  have hdec := abs_condDefect_le_of_ae (B k j).meas.comap_le (UV.Bdd1.of_measurable mF bF)
    (UV.Bdd1.of_measurable mG bG) hae
  have hE1 : Real.exp (-(m₁ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left m₁ m₂])
  have hE2 : Real.exp (-(m₂ * D)) ≤ Real.exp (-(min m₁ m₂ * D)) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_right m₁ m₂])
  have hx := Real.exp_pos (-(min m₁ m₂ * D))
  refine ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, hv, hlip, hsep', ?_, ?_, ?_⟩
  · refine hEF.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hEG.trans ?_
    calc c₂ * Real.exp (-(m₂ * D)) ≤ c₂ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE2 hc₂
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le
  · refine hdec.trans ?_
    calc c₁ * Real.exp (-(m₁ * D)) ≤ c₁ * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_left hE1 hc₁
      _ ≤ (c₁ + c₂) * Real.exp (-(min m₁ m₂ * D)) := mul_le_mul_of_nonneg_right (by linarith) hx.le

theorem obsTransferPhysTW_of_condMass {T : Tuning} {B : BlockingFamily Gr d T} (h1 : CondMass nr T B)
    (h2 : ObsQuasiLocTW nr cost T B) : ObsTransferPhysTW nr cost T B :=
  obsTransferPhysTW_of_condMassDecay nr cost (condMassDecay_of_condMass nr h1) h2

theorem wcorr_le_blockedW (T : Tuning) (B : BlockingFamily Gr d T) {k j : ℕ} {s : ℝ} {V : ℕ → ℕ} (O : SlabObs Gr d T s V)
    (n : ℕ) {C lam ε Kv Lg : ℝ}
    (hgap : ∀ (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink d (coarseSide j)))
      (vf : LatticeLink d (coarseSide j) → ℝ) (Lg' R : ℝ),
      BM f → BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg' → LipBound cost g (fun _ => Lg') →
      (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
      |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j) -
          (∫ U, f ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)) * ∫ U, g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)| ≤
        C * (∑ a ∈ A, vf a) * Lg' * Real.exp (-(lam * R)))
    (hC : 0 ≤ C)
    (f g : GaugeConnection Gr d (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink d (coarseSide j)))
    (mf : Measurable f) (mg : Measurable g) (bf : ∀ V, |f V| ≤ 1) (bg : ∀ V, |g V| ≤ 1)
    (dfA : DepOn f A') (dgB : DepOn g B') (vf : LatticeLink d (coarseSide j) → ℝ) (hvf : OscBound f vf)
    (hsumv : ∑ a ∈ A', vf a ≤ Kv) (hLg : 0 ≤ Lg) (hlip : LipBound cost g (fun _ => Lg))
    (hsep : ∀ x ∈ A', ∀ y ∈ B', (n * T.a k) / 2 ≤ T.L₁ * linkDist x y)
    (hEF : ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j)
        (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) U - f ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j) ≤ ε)
    (hEG : ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j)
        (fun U => O.F k j (thetaConn U)) U - g ((B k j).B U)| ∂(ymLaw (G := Gr) nr d T k j) ≤ ε)
    (hdec : |∫ U, O.F k j (tShift (n : ZMod (T.side k j)) U) * O.F k j (thetaConn U) ∂(ymLaw (G := Gr) nr d T k j) -
        ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j)
            (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) U *
          condExp (MeasurableSpace.comap (B k j).B inferInstance) (ymLaw (G := Gr) nr d T k j) (fun U => O.F k j (thetaConn U)) U
            ∂(ymLaw (G := Gr) nr d T k j)| ≤ ε) :
    |wcorr nr T k j (O.F k j) n| ≤ C * Kv * Lg * Real.exp (-(lam * ((n * T.a k) / (2 * T.L₁)))) + 5 * ε := by
  have := isProbabilityMeasure_wilsonMeasure (G := Gr) (n := nr) d (T.side k j) (T.β k)
  have hFm := O.meas k j
  have hF1 := O.bdd k j
  have htr := cov_transfer (ymLaw (G := Gr) nr d T k j) (B k j).meas (hFm.comp (measurable_tShift _))
    (hFm.comp measurePreserving_thetaConn.measurable) (fun U => hF1 _) (fun U => hF1 _) mf mg bf bg hEF hEG hdec
  have hL1 := T.L₁_pos
  have hR : ∀ x ∈ A', ∀ y ∈ B', (n * T.a k) / (2 * T.L₁) ≤ linkDist x y := by
    intro x hx y hy
    rw [div_le_iff₀ (by positivity)]
    have := hsep x hx y hy
    nlinarith
  have hblk := hgap f g A' B' vf Lg _ ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩ dfA dgB hvf hLg hlip hR
  have hblk' : |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j) -
      (∫ U, f ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)) * ∫ U, g ((B k j).B U) ∂(ymLaw (G := Gr) nr d T k j)| ≤
      C * Kv * Lg * Real.exp (-(lam * ((n * T.a k) / (2 * T.L₁)))) :=
    hblk.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsumv hC) hLg)
      (Real.exp_pos _).le)
  unfold wcorr corr
  exact htr.trans (by linarith)

theorem torusDecayLoc_of_blockGapUnifW {T : Tuning} (B : BlockingFamily Gr d T) {lam : ℝ} (hlam : 0 < lam)
    (hB : BlockGapUnifW nr cost T B lam) (h3 : ObsTransferPhysTW nr cost T B) : TorusDecayLoc Gr nr d T.toV := by
  obtain ⟨C, hC, k₀, hgap⟩ := hB
  obtain ⟨m, hm, htrP⟩ := h3
  have hL1 := T.L₁_pos
  set a := lam / 4
  have ha : 0 < a := by positivity
  set m' := min (lam / (4 * T.L₁)) m
  have hm' : 0 < m' := lt_min (by positivity) hm
  refine ⟨m', hm', fun s R => ?_⟩
  obtain ⟨c, K, hc, hK, k₁, htr⟩ := htrP (R + T.L₁)
  refine ⟨max k₀ k₁, C * (2 * K) * K * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) + 5 * c, by positivity,
    fun k hk Vb j O hO n hn => ?_⟩
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hk₁ : k₁ ≤ k := (le_max_right _ _).trans hk
  obtain ⟨hdA, hdB, -, -, -⟩ := slab_transfer_data T O hn
  have hsepT := slab_time_sep T O hn
  have hak := T.a_pos k
  have haL : T.a k ≤ T.L₁ := div_le_self hL1.le (by exact_mod_cast T.ℓ_pos k)
  have eA : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j))))
      (R + T.L₁) := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    rw [linkDist_shiftLink]
    have : T.a k * linkDist l l' ≤ R := hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
    linarith
  have eB : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image mirrorLink) (R + T.L₁) := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    have h1 : T.a k * linkDist l l' ≤ R := hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
    have h2 := mul_le_mul_of_nonneg_left (linkDist_mirrorLink_le l l') hak.le
    nlinarith
  set D := (n : ℝ) * T.a k
  have hD : 0 ≤ D := by positivity
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, ⟨vf, hvf, hsv⟩, hlip, hsep', hEF, hEG, hdec⟩ :=
    htr k hk₁ j _ _ _ _ D hD ((O.meas k j).comp (measurable_tShift _))
      ((O.meas k j).comp measurePreserving_thetaConn.measurable) (fun U => O.bdd k j _) (fun U => O.bdd k j _)
      (gaugeInvariant_tShift (O.gauge k j) _) (gaugeInvariant_thetaConn (O.gauge k j)) hdA hdB eA eB hsepT
  have hx : 0 ≤ D / T.L₁ := by positivity
  have hsv' : ∑ a ∈ A', vf a ≤ 2 * (K * (1 + D / T.L₁) ^ d) := by linarith
  have hmain := wcorr_le_blockedW nr cost T B O n (hgap k hk₀ j) hC f g A' B' mf mg bf bg dfA dgB vf hvf hsv' hK hlip
    hsep' hEF hEG hdec
  have hpoly := poly_exp_le d ha hx
  have e1 : lam * (D / (2 * T.L₁)) = 2 * a * (D / T.L₁) := by simp only [a]; field_simp; ring
  have e2 : a * (D / T.L₁) = lam / (4 * T.L₁) * D := by simp only [a]; field_simp
  have hE1 : Real.exp (-(lam / (4 * T.L₁) * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (lam / (4 * T.L₁)) m])
  have hE2 : Real.exp (-(m * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (lam / (4 * T.L₁)) m])
  have hCK : 0 ≤ C * (2 * K) * K := by positivity
  show |wcorr nr T k j (O.F k j) n| ≤ _
  calc |wcorr nr T k j (O.F k j) n|
      ≤ C * (2 * (K * (1 + D / T.L₁) ^ d)) * K * Real.exp (-(lam * (D / (2 * T.L₁)))) +
          5 * (c * Real.exp (-(m * D))) := hmain
    _ = C * (2 * K) * K * ((1 + D / T.L₁) ^ d * Real.exp (-(2 * a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m * D)) := by rw [e1]; ring
    _ ≤ C * (2 * K) * K * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a * Real.exp (-(a * (D / T.L₁)))) +
          5 * c * Real.exp (-(m' * D)) := by
        gcongr
    _ = C * (2 * K) * K * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) * Real.exp (-(lam / (4 * T.L₁) * D)) +
          5 * c * Real.exp (-(m' * D)) := by rw [e2]; ring
    _ ≤ C * (2 * K) * K * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) * Real.exp (-(m' * D)) +
          5 * c * Real.exp (-(m' * D)) := by gcongr
    _ = (C * (2 * K) * K * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) + 5 * c) * Real.exp (-(m' * (n * T.a k))) := by
        ring

theorem levelDprimeW_iff_on {T : Tuning} (B : BlockingFamily Gr d T) (lam : ℝ) :
    LevelDprimeW nr cost T B lam ↔ LevelDprimeWOn cost (M := coarseSide) (blockedLaw nr T B) lam := Iff.rfl

theorem blockGapUnifW_iff_lawGapW {T : Tuning} (B : BlockingFamily Gr d T) (lam : ℝ) :
    BlockGapUnifW nr cost T B lam ↔ LawGapW cost (M := coarseSide) (blockedLaw nr T B) lam := by
  constructor
  · rintro ⟨C, hC, k₀, H⟩
    refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hlip hR => ?_⟩
    have := H k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hlip hR
    rw [Effective.cov_map (ymLaw (G := Gr) nr d T k j) (B k j).meas hf hg] at this
    exact this
  · rintro ⟨C, hC, k₀, H⟩
    refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hlip hR => ?_⟩
    rw [Effective.cov_map (ymLaw (G := Gr) nr d T k j) (B k j).meas hf hg]
    exact H k hk j f g A Sg vf Lg R hf hg hfA hgS hvf hLg hlip hR

theorem blockGapBddW_iff_lawGapBddW {T : Tuning} (B : BlockingFamily Gr d T) (lam : ℝ) :
    BlockGapBddW nr cost T B lam ↔ LawGapBddW cost (M := coarseSide) (blockedLaw nr T B) lam := by
  constructor
  · rintro ⟨C, hC, k₀, H⟩
    refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR => ?_⟩
    have := H k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR
    rw [Effective.cov_map (ymLaw (G := Gr) nr d T k j) (B k j).meas ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩] at this
    exact this
  · rintro ⟨C, hC, k₀, H⟩
    refine ⟨C, hC, k₀, fun k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR => ?_⟩
    rw [Effective.cov_map (ymLaw (G := Gr) nr d T k j) (B k j).meas ⟨mf, 1, bf⟩ ⟨mg, 1, bg⟩]
    exact H k hk j f g A Sg vf Lg R mf mg bf bg hfA hgS hvf hLg hlip hR0 hR

theorem blockGapBddW_of_unifW {T : Tuning} {B : BlockingFamily Gr d T} {lam : ℝ} (h : BlockGapUnifW nr cost T B lam) :
    BlockGapBddW nr cost T B lam :=
  (blockGapBddW_iff_lawGapBddW nr cost B lam).2 (lawGapBddW_of_lawGapW cost ((blockGapUnifW_iff_lawGapW nr cost B lam).1 h))

theorem torusDecayLoc_of_blockGapBddW {T : Tuning} (B : BlockingFamily Gr d T) {lam : ℝ} (hlam : 0 < lam)
    (hB : BlockGapBddW nr cost T B lam) (h3 : ObsTransferPhysTW nr cost T B) : TorusDecayLoc Gr nr d T.toV := by
  obtain ⟨C, hC, k₀, hgap⟩ := hB
  obtain ⟨m, hm, htrP⟩ := h3
  have hL1 := T.L₁_pos
  set a := lam / 4
  have ha : 0 < a := by positivity
  set m' := min (lam / (4 * T.L₁)) m
  have hm' : 0 < m' := lt_min (by positivity) hm
  refine ⟨m', hm', fun s R => ?_⟩
  obtain ⟨c, K, hc, hK, k₁, htr⟩ := htrP (R + T.L₁)
  refine ⟨max k₀ k₁, C * (1 + 2 * K) * (1 + K) * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) + 5 * c, by positivity,
    fun k hk Vb j O hO n hn => ?_⟩
  have hk₀ : k₀ ≤ k := (le_max_left _ _).trans hk
  have hk₁ : k₁ ≤ k := (le_max_right _ _).trans hk
  obtain ⟨hdA, hdB, -, -, -⟩ := slab_transfer_data T O hn
  have hsepT := slab_time_sep T O hn
  have hak := T.a_pos k
  have haL : T.a k ≤ T.L₁ := div_le_self hL1.le (by exact_mod_cast T.ℓ_pos k)
  have eA : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image (shiftLink (n : ZMod (T.side k j))))
      (R + T.L₁) := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    rw [linkDist_shiftLink]
    have : T.a k * linkDist l l' ≤ R := hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
    linarith
  have eB : PhysExtent T k (((O.supp k j) ∩ timeSlab 0 (T.thick k s)).image mirrorLink) (R + T.L₁) := by
    intro e he e' he'
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 he'
    have h1 : T.a k * linkDist l l' ≤ R := hO k j l (Finset.mem_inter.1 hl).1 l' (Finset.mem_inter.1 hl').1
    have h2 := mul_le_mul_of_nonneg_left (linkDist_mirrorLink_le l l') hak.le
    nlinarith
  set D := (n : ℝ) * T.a k
  have hD : 0 ≤ D := by positivity
  obtain ⟨f, g, A', B', mf, mg, bf, bg, dfA, dgB, ⟨vf, hvf, hsv⟩, hlip, hsep', hEF, hEG, hdec⟩ :=
    htr k hk₁ j _ _ _ _ D hD ((O.meas k j).comp (measurable_tShift _))
      ((O.meas k j).comp measurePreserving_thetaConn.measurable) (fun U => O.bdd k j _) (fun U => O.bdd k j _)
      (gaugeInvariant_tShift (O.gauge k j) _) (gaugeInvariant_thetaConn (O.gauge k j)) hdA hdB eA eB hsepT
  have hx : 0 ≤ D / T.L₁ := by positivity
  -- the block covariance, by the bounded infrared input
  have hR' : ∀ x ∈ A', ∀ y ∈ B', D / (2 * T.L₁) ≤ linkDist x y := by
    intro x hx' y hy
    rw [div_le_iff₀ (by positivity)]
    have := hsep' x hx' y hy
    nlinarith
  have hblk := hgap k hk₀ j f g A' B' vf K (D / (2 * T.L₁)) mf mg bf bg dfA dgB hvf hK hlip (by positivity) hR'
  -- the transfer
  have := isProbabilityMeasure_wilsonMeasure (G := Gr) (n := nr) d (T.side k j) (T.β k)
  have htr' := cov_transfer (ymLaw (G := Gr) nr d T k j) (B k j).meas ((O.meas k j).comp (measurable_tShift _))
    ((O.meas k j).comp measurePreserving_thetaConn.measurable) (fun U => O.bdd k j _) (fun U => O.bdd k j _)
    mf mg bf bg hEF hEG hdec
  have hw : |wcorr nr T k j (O.F k j) n| ≤
      C * (1 + ∑ a ∈ A', vf a) * (1 + K) * Real.exp (-(lam * (D / (2 * T.L₁)))) +
        5 * (c * Real.exp (-(m * D))) := by
    unfold wcorr corr
    exact htr'.trans (by linarith)
  -- constants
  have hY1 : 1 ≤ (1 + D / T.L₁) ^ d := one_le_pow₀ (by linarith)
  have h1S : 1 + ∑ a ∈ A', vf a ≤ (1 + 2 * K) * (1 + D / T.L₁) ^ d := by nlinarith
  set Kc := C * (1 + 2 * K) * (1 + K) with hKcdef
  have hKc : 0 ≤ Kc := by positivity
  have hstep : C * (1 + ∑ a ∈ A', vf a) * (1 + K) ≤ Kc * (1 + D / T.L₁) ^ d := by
    have h1 := mul_le_mul_of_nonneg_left h1S hC
    have h2 := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 1 + K)
    calc C * (1 + ∑ a ∈ A', vf a) * (1 + K) ≤ C * ((1 + 2 * K) * (1 + D / T.L₁) ^ d) * (1 + K) := h2
      _ = Kc * (1 + D / T.L₁) ^ d := by rw [hKcdef]; ring
  have hpoly := poly_exp_le d ha hx
  have e1 : lam * (D / (2 * T.L₁)) = 2 * a * (D / T.L₁) := by simp only [a]; field_simp; ring
  have e2 : a * (D / T.L₁) = lam / (4 * T.L₁) * D := by simp only [a]; field_simp
  have hE1 : Real.exp (-(lam / (4 * T.L₁) * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (lam / (4 * T.L₁)) m])
  have hE2 : Real.exp (-(m * D)) ≤ Real.exp (-(m' * D)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (lam / (4 * T.L₁)) m])
  show |wcorr nr T k j (O.F k j) n| ≤ _
  calc |wcorr nr T k j (O.F k j) n|
      ≤ C * (1 + ∑ a ∈ A', vf a) * (1 + K) * Real.exp (-(lam * (D / (2 * T.L₁)))) +
          5 * (c * Real.exp (-(m * D))) := hw
    _ ≤ Kc * (1 + D / T.L₁) ^ d * Real.exp (-(2 * a * (D / T.L₁))) + 5 * c * Real.exp (-(m' * D)) := by
        rw [e1]
        have h5 : c * Real.exp (-(m * D)) ≤ c * Real.exp (-(m' * D)) := mul_le_mul_of_nonneg_left hE2 hc
        have h6 := mul_le_mul_of_nonneg_right hstep (Real.exp_pos (-(2 * a * (D / T.L₁)))).le
        linarith
    _ = Kc * ((1 + D / T.L₁) ^ d * Real.exp (-(2 * a * (D / T.L₁)))) + 5 * c * Real.exp (-(m' * D)) := by ring
    _ ≤ Kc * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a * Real.exp (-(a * (D / T.L₁)))) + 5 * c * Real.exp (-(m' * D)) := by
        gcongr
    _ = Kc * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) * Real.exp (-(lam / (4 * T.L₁) * D)) + 5 * c * Real.exp (-(m' * D)) := by
        rw [e2]; ring
    _ ≤ Kc * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) * Real.exp (-(m' * D)) + 5 * c * Real.exp (-(m' * D)) := by gcongr
    _ = (Kc * ((Nat.factorial d : ℝ) / a ^ d * Real.exp a) + 5 * c) * Real.exp (-(m' * (n * T.a k))) := by ring

section Explicit

variable (Gr) (d)

def LevelTorusRouteW (T : Tuning) : Prop :=
  ∃ (B : BlockingFamily Gr d T) (lam : ℝ), 0 < lam ∧ LevelDprimeW nr cost T B lam ∧ ObsTransferPhysTW nr cost T B

theorem bothOrdersLoc_of_levelRouteW {P : ℝ} (hc0 : ∀ a b, 0 ≤ cost a b) (hP : ∀ a b, cost a b ≤ P) {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0)) (h : LevelTorusRouteW Gr nr d cost T) :
    TorusDecayLoc Gr nr d T.toV ∧ MassGapLoc Gr nr d T ∧ MassGapMFLoc Gr nr d T.toV := by
  obtain ⟨B, lam, hlam, hD, h3⟩ := h
  have hT := torusDecayLoc_of_blockGapUnifW nr cost B hlam (blockGapUnifW_of_levelDprimeW nr cost hc0 hP B hlam.le hD) h3
  exact ⟨hT, bothOrdersLoc_of_torusDecayLoc Gr nr d ha hT⟩

end Explicit

end W1


/-! ## The SU(2), `d = 4` instances -/

section Instance

open ProofPhase.Certified (geodSU2 geodSU2_nonneg geodSU2_le_pi)

theorem levelDprimeW_iff (T : Tuning) (B : ProofPhase.BlockingFamily T) (lam : ℝ) :
    ProofPhase.V3.LevelDprimeW T B lam ↔ LevelDprimeW 2 geodSU2 T B lam := Iff.rfl

theorem blockGapUnifW_iff (T : Tuning) (B : ProofPhase.BlockingFamily T) (lam : ℝ) :
    ProofPhase.V3.BlockGapUnifW T B lam ↔ BlockGapUnifW 2 geodSU2 T B lam := Iff.rfl

theorem obsTransferPhysTW_iff (T : Tuning) (B : ProofPhase.BlockingFamily T) :
    ProofPhase.V3.ObsTransferPhysTW T B ↔ ObsTransferPhysTW 2 geodSU2 T B := Iff.rfl

theorem obsQuasiLocTW_iff (T : Tuning) (B : ProofPhase.BlockingFamily T) :
    ProofPhase.V3.ObsQuasiLocTW T B ↔ ObsQuasiLocTW 2 geodSU2 T B := Iff.rfl

theorem levelTorusRouteW_iff (T : Tuning) : ProofPhase.V3.LevelTorusRouteW T ↔ LevelTorusRouteW SU2 2 4 geodSU2 T :=
  Iff.rfl

/-- `ProofPhase.V3.blockGapUnifW_of_levelDprimeW` from the generic theorem (`P = π`). -/
theorem blockGapUnifW_of_levelDprimeW_su2 {T : Tuning} (B : ProofPhase.BlockingFamily T) {lam : ℝ} (hlam : 0 ≤ lam)
    (h : ProofPhase.V3.LevelDprimeW T B lam) : ProofPhase.V3.BlockGapUnifW T B lam :=
  blockGapUnifW_of_levelDprimeW (Gr := SU2) 2 (d := 4) geodSU2 geodSU2_nonneg geodSU2_le_pi B hlam h

/-- `ProofPhase.V3.obsTransferPhysTW_of_condMassDecay` from the generic theorem. -/
theorem obsTransferPhysTW_of_condMassDecay_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T}
    (h1 : ProofPhase.V3.CondMassDecay T B) (h2 : ProofPhase.V3.ObsQuasiLocTW T B) :
    ProofPhase.V3.ObsTransferPhysTW T B :=
  obsTransferPhysTW_of_condMassDecay (Gr := SU2) 2 (d := 4) geodSU2 h1 h2

/-- `ProofPhase.V3.obsTransferPhysTW_of_condMass` from the generic theorem. -/
theorem obsTransferPhysTW_of_condMass_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T}
    (h1 : ProofPhase.V3.CondMass T B) (h2 : ProofPhase.V3.ObsQuasiLocTW T B) :
    ProofPhase.V3.ObsTransferPhysTW T B :=
  obsTransferPhysTW_of_condMass (Gr := SU2) 2 (d := 4) geodSU2 h1 h2

/-- `ProofPhase.V3.torusDecayLoc_of_blockGapUnifW` from the generic theorem. -/
theorem torusDecayLoc_of_blockGapUnifW_su2 {T : Tuning} (B : ProofPhase.BlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    (hB : ProofPhase.V3.BlockGapUnifW T B lam) (h3 : ProofPhase.V3.ObsTransferPhysTW T B) :
    ProofPhase.Torus.TorusDecayLoc T.toV :=
  (torusDecayLoc_iff _).2 (torusDecayLoc_of_blockGapUnifW (Gr := SU2) 2 (d := 4) geodSU2 B hlam hB h3)

/-- `ProofPhase.V4.blockGapBddW_of_unifW` from the generic theorem. -/
theorem blockGapBddW_of_unifW_su2 {T : Tuning} {B : ProofPhase.BlockingFamily T} {lam : ℝ}
    (h : ProofPhase.V3.BlockGapUnifW T B lam) : ProofPhase.V4.BlockGapBddW T B lam :=
  blockGapBddW_of_unifW (Gr := SU2) 2 (d := 4) geodSU2 h

/-- `ProofPhase.V4.torusDecayLoc_of_blockGapBddW` from the generic theorem. -/
theorem torusDecayLoc_of_blockGapBddW_su2 {T : Tuning} (B : ProofPhase.BlockingFamily T) {lam : ℝ} (hlam : 0 < lam)
    (hB : ProofPhase.V4.BlockGapBddW T B lam) (h3 : ProofPhase.V3.ObsTransferPhysTW T B) :
    ProofPhase.Torus.TorusDecayLoc T.toV :=
  (torusDecayLoc_iff _).2 (torusDecayLoc_of_blockGapBddW (Gr := SU2) 2 (d := 4) geodSU2 B hlam hB h3)

/-- `ProofPhase.V3.bothOrdersLoc_of_levelRouteW` from the generic theorem. -/
theorem bothOrdersLoc_of_levelRouteW_su2 {T : Tuning} (ha : Tendsto T.a atTop (𝓝 0))
    (h : ProofPhase.V3.LevelTorusRouteW T) :
    ProofPhase.Torus.TorusDecayLoc T.toV ∧ ProofPhase.MassGapLoc T ∧ ProofPhase.Torus.MassGapMFLoc T.toV := by
  have := bothOrdersLoc_of_levelRouteW SU2 2 4 geodSU2 geodSU2_nonneg geodSU2_le_pi ha h
  exact ⟨(torusDecayLoc_iff _).2 this.1, (massGapLoc_iff T).2 this.2.1, (massGapMFLoc_iff _).2 this.2.2⟩

theorem wcorr_le_blockedW_su2 (T : Tuning) (B : ProofPhase.BlockingFamily T) {k j : ℕ} {s : ℝ} {V : ℕ → ℕ} (O : ProofPhase.SlabObs T s V)
    (n : ℕ) {C lam ε Kv Lg : ℝ}
    (hgap : ∀ (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A Sg : Finset (LatticeLink 4 (coarseSide j)))
      (vf : LatticeLink 4 (coarseSide j) → ℝ) (Lg' R : ℝ),
      OneScale.BM f → OneScale.BM g → DepOn f A → DepOn g Sg → OscBound f vf → 0 ≤ Lg' → LipBound ProofPhase.Certified.geodSU2 g (fun _ => Lg') →
      (∀ x ∈ A, ∀ y ∈ Sg, R ≤ linkDist x y) →
      |∫ U, f ((B k j).B U) * g ((B k j).B U) ∂(T.ym k j) -
          (∫ U, f ((B k j).B U) ∂(T.ym k j)) * ∫ U, g ((B k j).B U) ∂(T.ym k j)| ≤
        C * (∑ a ∈ A, vf a) * Lg' * Real.exp (-(lam * R)))
    (hC : 0 ≤ C)
    (f g : GaugeConnection SU2 4 (coarseSide j) → ℝ) (A' B' : Finset (LatticeLink 4 (coarseSide j)))
    (mf : Measurable f) (mg : Measurable g) (bf : ∀ V, |f V| ≤ 1) (bg : ∀ V, |g V| ≤ 1)
    (dfA : DepOn f A') (dgB : DepOn g B') (vf : LatticeLink 4 (coarseSide j) → ℝ) (hvf : OscBound f vf)
    (hsumv : ∑ a ∈ A', vf a ≤ Kv) (hLg : 0 ≤ Lg) (hlip : LipBound ProofPhase.Certified.geodSU2 g (fun _ => Lg))
    (hsep : ∀ x ∈ A', ∀ y ∈ B', (n * T.a k) / 2 ≤ T.L₁ * linkDist x y)
    (hEF : ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j)
        (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) U - f ((B k j).B U)| ∂(T.ym k j) ≤ ε)
    (hEG : ∫ U, |condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j)
        (fun U => O.F k j (thetaConn U)) U - g ((B k j).B U)| ∂(T.ym k j) ≤ ε)
    (hdec : |∫ U, O.F k j (tShift (n : ZMod (T.side k j)) U) * O.F k j (thetaConn U) ∂(T.ym k j) -
        ∫ U, condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j)
            (fun U => O.F k j (tShift (n : ZMod (T.side k j)) U)) U *
          condExp (MeasurableSpace.comap (B k j).B inferInstance) (T.ym k j) (fun U => O.F k j (thetaConn U)) U
            ∂(T.ym k j)| ≤ ε) :
    |T.wcorr k j (O.F k j) n| ≤ C * Kv * Lg * Real.exp (-(lam * ((n * T.a k) / (2 * T.L₁)))) + 5 * ε :=
  wcorr_le_blockedW (Gr := SU2) 2 (d := 4) geodSU2 T B (SlabObs.ofOld O) n hgap hC f g A' B' mf mg bf bg dfA dgB vf hvf hsumv hLg hlip hsep hEF hEG hdec

end Instance

end ProofPhase.General
