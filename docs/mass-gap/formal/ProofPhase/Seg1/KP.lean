/-
Proof phase, cycle 4, workstream 2 (c4b-seg1): a Kotecky–Preiss theorem for hard-core polymer gases with
configuration-dependent activities, in Moebius form with exponential tails (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c4b-seg1/NOTE.md`.
-/

import ProofPhase.Seg1.Mobius

/-!
# The Kotecky–Preiss theorem in Moebius form

**The gas.** Sites: a finite type `V`. Polymers: finite subsets `γ ⊆ V`, with real activities `ζ γ` (which may depend
on a configuration `ω`). Hard core: a family is admissible when its polymers are nonempty and pairwise disjoint
(`families`). The partition function of a region `Y` is `gasZ ζ Y = ∑_{admissible F in Y} ∏_{γ ∈ F} ζ γ`; it satisfies
the polymer recursion `Z(Y ∪ y) = Z(Y) + ∑_{γ ∋ y, γ ⊆ Y ∪ y} ζ γ · Z((Y ∪ y) \ γ)` (`gasZ_insert`), depends only on
the activities of polymers inside `Y` (`gasZ_congr`), and `Z(∅) = 1`.

**The cluster potentials.** `clusterPot ζ ω X` is the Moebius coefficient of `Y ↦ log Z(Y)` at `X`. By Moebius
inversion `log Z(W) = ∑_{X ⊆ W} clusterPot X` (`log_gasZ_eq_sum`, D), and `clusterPot X` depends only on the
activities of the polymers inside `X` (`clusterPot_congr`, D): this is the decomposition of the log-partition function
into **local** terms that the cluster expansion produces (they equal the sums of the connected clusters with support
exactly `X`; we never need that formula).

**The theorem** (`kotecky_preiss`, S). Let `σ` be an admissible weight (`Weight`: `≥ 0` on nonempty sets, `0` on
singletons, subadditive on overlapping unions; e.g. `λ·diam + (|·| − 1)`). Suppose the activities are bounded,
`|ζ γ ω| ≤ ζ̄ γ`, and satisfy the **Kotecky–Preiss criterion in site form**
`∑_{γ ∋ y} ζ̄ γ · 2^{|γ|} · e^{σ γ} ≤ 1` for every site `y` (`KPCrit`). Then every `Z(Y)` is positive and, for every
region `W` and site `y ∈ W`,

  `∑_{X ⊆ W, X ∋ y} sup_ω |clusterPot ζ ω X| · e^{σ X} ≤ log 2`,

a bound **independent of `W`** (hence of the volume) and uniform in the configuration.

**Proof** (Dobrushin-style induction, no tree-graph combinatorics, no counting of connected sets). By strong induction
on `W` one shows that the ratio deviation `u_y(Y) = Z(Y ∪ y)/Z(Y) − 1` (`Y ⊆ W \ y`) has Moebius coefficients majorised
uniformly in `ω` with anchored weighted norm `≤ 1/2`. The polymer recursion writes `u_y = ∑_{γ ∋ y} ζ γ · P_{γ \ y}`
with `P_C(Y) = 1[C ⊆ Y] Z(Y \ C)/Z(Y)`; removing the sites of `C` one at a time, `P_C` is a product of an up-set
indicator and inverse ratios `Z(Y')/Z(Y' ∪ c)` of strictly smaller regions, each with norm `≤ 2` by the induction
hypothesis (geometric series), glued at the points `c ∈ γ` (`Mobius.wnorm_conv_le`). The criterion closes the induction;
the logarithmic series turns norm `1/2` into `log 2`.

Mark: S for `kotecky_preiss` (a complete proof of a KP-type cluster-expansion bound), D for the inversion/locality
identities. Group-blind: nothing here knows about Yang–Mills.
-/

open Finset

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Seg1

variable {V : Type*} [DecidableEq V]

/-! ## The hard-core polymer gas -/

/-- Admissible families in `Y`: sets of nonempty, pairwise disjoint subsets of `Y`. -/
def families (Y : Finset V) : Finset (Finset (Finset V)) :=
  (Y.powerset.filter (·.Nonempty)).powerset.filter fun F => ∀ γ ∈ F, ∀ γ' ∈ F, γ ≠ γ' → Disjoint γ γ'

theorem mem_families {Y : Finset V} {F : Finset (Finset V)} :
    F ∈ families Y ↔ (∀ γ ∈ F, γ ⊆ Y ∧ γ.Nonempty) ∧ ∀ γ ∈ F, ∀ γ' ∈ F, γ ≠ γ' → Disjoint γ γ' := by
  unfold families
  simp only [mem_filter, mem_powerset]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun γ hγ => by have := h1 hγ; rw [mem_filter, mem_powerset] at this; exact this, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun γ hγ => by rw [mem_filter, mem_powerset]; exact h1 γ hγ, h2⟩

/-- **The partition function** of the hard-core gas in the region `Y`. -/
def gasZ (ζ : Finset V → ℝ) (Y : Finset V) : ℝ := ∑ F ∈ families Y, ∏ γ ∈ F, ζ γ

theorem families_empty : families (∅ : Finset V) = {∅} := by
  ext F
  rw [mem_families, mem_singleton]
  constructor
  · rintro ⟨h1, -⟩
    exact eq_empty_of_forall_notMem fun γ hγ => by
      obtain ⟨hs, x, hx⟩ := h1 γ hγ
      exact notMem_empty x (hs hx)
  · rintro rfl; simp

theorem gasZ_empty (ζ : Finset V → ℝ) : gasZ ζ ∅ = 1 := by simp [gasZ, families_empty]

/-- **Locality of the partition function** (D): `Z(Y)` depends only on the activities of polymers inside `Y`. -/
theorem gasZ_congr {ζ ζ' : Finset V → ℝ} {Y : Finset V} (h : ∀ γ ⊆ Y, ζ γ = ζ' γ) : gasZ ζ Y = gasZ ζ' Y :=
  sum_congr rfl fun _ hF => prod_congr rfl fun γ hγ => h γ ((mem_families.1 hF).1 γ hγ).1

/-- For fixed `γ ∋ y`, the families of `Y'` containing `γ` are `γ` plus a family of `Y' \ γ`. -/
theorem sum_families_mem (ζ : Finset V → ℝ) {Y' γ : Finset V} (hγY : γ ⊆ Y') (hγ : γ.Nonempty) :
    ∑ F ∈ (families Y').filter (fun F => γ ∈ F), ∏ δ ∈ F, ζ δ = ζ γ * gasZ ζ (Y' \ γ) := by
  unfold gasZ
  rw [mul_sum]
  refine sum_nbij' (fun F => F.erase γ) (fun F' => insert γ F') ?_ ?_ ?_ ?_ ?_
  · intro F hF
    rw [mem_filter] at hF
    obtain ⟨⟨h1, h2⟩, hγF⟩ := hF.imp_left mem_families.1
    refine mem_families.2 ⟨fun δ hδ => ?_, fun δ hδ δ' hδ' hne => h2 δ (mem_of_mem_erase hδ) δ'
      (mem_of_mem_erase hδ') hne⟩
    have hδF := mem_of_mem_erase hδ
    have hne : δ ≠ γ := ne_of_mem_erase hδ
    have hdis := h2 δ hδF γ hγF hne
    refine ⟨fun x hx => mem_sdiff.2 ⟨(h1 δ hδF).1 hx, fun hxγ => disjoint_left.1 hdis hx hxγ⟩, (h1 δ hδF).2⟩
  · intro F' hF'
    obtain ⟨h1, h2⟩ := mem_families.1 hF'
    have hγF' : γ ∉ F' := fun h => by
      obtain ⟨x, hx⟩ := hγ
      exact (mem_sdiff.1 ((h1 γ h).1 hx)).2 hx
    refine mem_filter.2 ⟨mem_families.2 ⟨fun δ hδ => ?_, fun δ hδ δ' hδ' hne => ?_⟩, mem_insert_self _ _⟩
    · rcases mem_insert.1 hδ with rfl | hδ
      · exact ⟨hγY, hγ⟩
      · exact ⟨(h1 δ hδ).1.trans sdiff_subset, (h1 δ hδ).2⟩
    · have key : ∀ δ ∈ F', Disjoint γ δ := fun δ hδ =>
        disjoint_left.2 fun x hxγ hxδ => (mem_sdiff.1 ((h1 δ hδ).1 hxδ)).2 hxγ
      rcases mem_insert.1 hδ with e1 | h1' <;> rcases mem_insert.1 hδ' with e2 | h2'
      · exact absurd (e1.trans e2.symm) hne
      · rw [e1]; exact key δ' h2'
      · rw [e2]; exact (key δ h1').symm
      · exact h2 δ h1' δ' h2' hne
  · intro F hF; exact insert_erase (mem_filter.1 hF).2
  · intro F' hF'
    obtain ⟨h1, -⟩ := mem_families.1 hF'
    refine erase_insert fun h => ?_
    obtain ⟨x, hx⟩ := hγ
    exact (mem_sdiff.1 ((h1 γ h).1 hx)).2 hx
  · intro F hF
    exact (mul_prod_erase F ζ (mem_filter.1 hF).2).symm

/-- **The polymer recursion** (S, combinatorial). -/
theorem gasZ_insert (ζ : Finset V → ℝ) {y : V} {Y : Finset V} (hy : y ∉ Y) :
    gasZ ζ (insert y Y) =
      gasZ ζ Y + ∑ γ ∈ (insert y Y).powerset.filter (fun γ => y ∈ γ), ζ γ * gasZ ζ (insert y Y \ γ) := by
  set G := (insert y Y).powerset.filter (fun γ => y ∈ γ)
  have hsplit := (sum_filter_add_sum_filter_not (families (insert y Y)) (fun F => ∃ γ ∈ F, y ∈ γ)
    (fun F => ∏ γ ∈ F, ζ γ)).symm
  unfold gasZ at hsplit ⊢
  rw [hsplit, add_comm]
  congr 1
  · -- families without a polymer through `y` are the families of `Y`
    refine sum_congr ?_ fun _ _ => rfl
    ext F
    rw [mem_filter, mem_families, mem_families]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun γ hγ => ⟨fun x hx => ?_, (h1 γ hγ).2⟩, h2⟩
      have hxy := mem_insert.1 ((h1 γ hγ).1 hx)
      rcases hxy with rfl | hx'
      · exact absurd ⟨γ, hγ, hx⟩ h3
      · exact hx'
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun γ hγ => ⟨(h1 γ hγ).1.trans (subset_insert _ _), (h1 γ hγ).2⟩, h2⟩, ?_⟩
      rintro ⟨γ, hγ, hyγ⟩
      exact hy ((h1 γ hγ).1 hyγ)
  · -- families with a polymer through `y`: sum over that polymer
    rw [show (∑ γ ∈ G, ζ γ * ∑ F ∈ families (insert y Y \ γ), ∏ δ ∈ F, ζ δ) =
        ∑ γ ∈ G, ∑ F ∈ (families (insert y Y)).filter (fun F => γ ∈ F), ∏ δ ∈ F, ζ δ from
      sum_congr rfl fun γ hγ => by
        have hγ' := mem_filter.1 hγ
        rw [sum_families_mem ζ (mem_powerset.1 hγ'.1) ⟨y, hγ'.2⟩]; rfl]
    -- each such family has exactly one polymer through `y`
    have hone : ∀ F ∈ (families (insert y Y)).filter (fun F => ∃ γ ∈ F, y ∈ γ),
        ∏ δ ∈ F, ζ δ = ∑ γ ∈ G.filter (fun γ => γ ∈ F), ∏ δ ∈ F, ζ δ := by
      intro F hF
      obtain ⟨hF1, γ₀, hγ₀, hyγ₀⟩ := mem_filter.1 hF
      obtain ⟨h1, h2⟩ := mem_families.1 hF1
      have : G.filter (fun γ => γ ∈ F) = {γ₀} := by
        ext γ
        rw [mem_filter, mem_singleton, mem_filter, mem_powerset]
        constructor
        · rintro ⟨⟨-, hyγ⟩, hγ⟩
          by_contra hne
          exact disjoint_left.1 (h2 γ hγ γ₀ hγ₀ hne) hyγ hyγ₀
        · rintro rfl; exact ⟨⟨(h1 γ hγ₀).1, hyγ₀⟩, hγ₀⟩
      rw [this, sum_singleton]
    rw [sum_congr rfl hone]
    refine sum_comm' fun F γ => ?_
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hF, -⟩, hγG, hγF⟩; exact ⟨⟨hF, hγF⟩, hγG⟩
    · rintro ⟨⟨hF, hγF⟩, hγG⟩; exact ⟨⟨hF, γ, hγF, (mem_filter.1 hγG).2⟩, hγG, hγF⟩

/-! ## Cluster potentials -/

variable {Ω : Type*}

/-- The partition function at the configuration `ω`. -/
abbrev Zc (ζ : Finset V → Ω → ℝ) (ω : Ω) (Y : Finset V) : ℝ := gasZ (fun γ => ζ γ ω) Y

/-- **The cluster potential** of `X`: the Moebius coefficient of `log Z` at `X`. -/
def clusterPot (ζ : Finset V → Ω → ℝ) (ω : Ω) (X : Finset V) : ℝ := mob (fun Y => Real.log (Zc ζ ω Y)) X

/-- Its configuration-uniform size. -/
def clusterBar (ζ : Finset V → Ω → ℝ) (X : Finset V) : ℝ := ⨆ ω, |clusterPot ζ ω X|

/-- **Local decomposition of the free energy** (D, Moebius inversion). -/
theorem log_gasZ_eq_sum (ζ : Finset V → Ω → ℝ) (ω : Ω) (W : Finset V) :
    Real.log (Zc ζ ω W) = ∑ X ∈ W.powerset, clusterPot ζ ω X :=
  (sum_mob (fun Y => Real.log (Zc ζ ω Y)) W).symm

/-- **Locality of the cluster potentials** (D): `clusterPot X` depends only on the activities of polymers inside
`X`. -/
theorem clusterPot_congr {ζ ζ' : Finset V → Ω → ℝ} {ω ω' : Ω} {X : Finset V}
    (h : ∀ γ ⊆ X, ζ γ ω = ζ' γ ω') : clusterPot ζ ω X = clusterPot ζ' ω' X :=
  mob_congr fun Y hY => by unfold Zc; rw [gasZ_congr fun γ hγ => h γ (hγ.trans hY)]

theorem clusterPot_empty (ζ : Finset V → Ω → ℝ) (ω : Ω) : clusterPot ζ ω ∅ = 0 := by
  rw [clusterPot, mob_empty]; unfold Zc; rw [gasZ_empty, Real.log_one]

/-! ## The Kotecky–Preiss induction -/

section KP

variable [Fintype V] {σ : Finset V → ℝ}

/-- **The Kotecky–Preiss criterion in site form** for the activity bounds `ζ̄`. -/
def KPCrit (σ : Finset V → ℝ) (zb : Finset V → ℝ) : Prop :=
  ∀ y : V, ∑ γ ∈ (univ : Finset (Finset V)).filter (fun γ => y ∈ γ), zb γ * 2 ^ γ.card * Real.exp (σ γ) ≤ 1

/-- The ratio deviation `Z(Y ∪ y)/Z(Y) − 1`. -/
def ratioDev (ζ : Finset V → Ω → ℝ) (y : V) (ω : Ω) (Y : Finset V) : ℝ := Zc ζ ω (insert y Y) / Zc ζ ω Y - 1

/-- The inverse ratio `Z(Y)/Z(Y ∪ y)`. -/
def invRatio (ζ : Finset V → Ω → ℝ) (y : V) (ω : Ω) (Y : Finset V) : ℝ := Zc ζ ω Y / Zc ζ ω (insert y Y)

/-- `P_C(Y) = 1[C ⊆ Y] Z(Y \ C)/Z(Y)`. -/
def Pc (ζ : Finset V → Ω → ℝ) (C : Finset V) (ω : Ω) (Y : Finset V) : ℝ :=
  if C ⊆ Y then Zc ζ ω (Y \ C) / Zc ζ ω Y else 0

/-- The induction statement for a region `W`. -/
def Good (σ : Finset V → ℝ) (ζ : Finset V → Ω → ℝ) (W : Finset V) : Prop :=
  (∀ ω, ∀ Y ⊆ W, 0 < Zc ζ ω Y) ∧
    ∀ y ∈ W, ∃ c : Finset V → ℝ, (∀ A, 0 ≤ c A) ∧ MajBy (W.erase y) (ratioDev ζ y) c ∧
      wnorm σ {y} (W.erase y) c ≤ 1 / 2

/-- From the ratio bound: the inverse ratio has norm `≤ 2` (geometric series). -/
theorem inv_of_good (hσ : Weight σ) {ζ : Finset V → Ω → ℝ} {W : Finset V} (hW : Good σ ζ W) {c : V}
    (hc : c ∈ W) :
    ∃ c' : Finset V → ℝ, (∀ A, 0 ≤ c' A) ∧ MajBy (W.erase c) (invRatio ζ c) c' ∧
      wnorm σ {c} (W.erase c) c' ≤ 2 := by
  obtain ⟨c0, hc0, m0, hn0⟩ := hW.2 c hc
  have hK : ({c} : Finset V).Nonempty := singleton_nonempty c
  have hn0' : 0 ≤ wnorm σ {c} (W.erase c) c0 := wnorm_nonneg hc0
  obtain ⟨m, hn⟩ := MajBy.tsum (σ := σ) hσ hK (f := fun n ω Y => (- ratioDev ζ c ω Y) ^ n)
    (h := invRatio ζ c) (c := fun n => cpow c0 n) (t := fun n => (1 / 2 : ℝ) ^ n)
    (fun n A => cpow_nonneg hc0 n A) (fun n => m0.neg.pow n)
    (fun ω Y hY => by
      have hu := abs_le_wnorm hσ hK hc0 m0 ω hY
      have hv : |- ratioDev ζ c ω Y| < 1 := by rw [abs_neg]; linarith
      have hpos1 : 0 < Zc ζ ω Y := hW.1 ω Y (hY.trans (erase_subset _ _))
      have hpos2 : 0 < Zc ζ ω (insert c Y) :=
        hW.1 ω _ (insert_subset hc (hY.trans (erase_subset _ _)))
      have := hasSum_geometric_of_abs_lt_one hv
      convert this using 1
      unfold invRatio ratioDev
      have e : (1 : ℝ) - -(Zc ζ ω (insert c Y) / Zc ζ ω Y - 1) = Zc ζ ω (insert c Y) / Zc ζ ω Y := by ring
      rw [e, inv_div])
    (fun n => (wnorm_cpow_le hσ hc0 n).trans (pow_le_pow_left₀ hn0' hn0 n))
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  refine ⟨fun A => ∑' n, cpow c0 n A, fun A => tsum_nonneg fun n => cpow_nonneg hc0 n A, m, ?_⟩
  rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hn
  linarith [show ((1 : ℝ) - 1 / 2)⁻¹ = 2 by norm_num]

/-- From the ratio bound: the log-ratio has norm `≤ log 2` (logarithmic series). -/
theorem log_of_good (hσ : Weight σ) {ζ : Finset V → Ω → ℝ} {W : Finset V} (hW : Good σ ζ W) {y : V}
    (hy : y ∈ W) :
    ∃ c' : Finset V → ℝ, (∀ A, 0 ≤ c' A) ∧
      MajBy (W.erase y) (fun ω Y => Real.log (Zc ζ ω (insert y Y)) - Real.log (Zc ζ ω Y)) c' ∧
      wnorm σ {y} (W.erase y) c' ≤ Real.log 2 := by
  obtain ⟨c0, hc0, m0, hn0⟩ := hW.2 y hy
  have hK : ({y} : Finset V).Nonempty := singleton_nonempty y
  have hn0' : 0 ≤ wnorm σ {y} (W.erase y) c0 := wnorm_nonneg hc0
  have hlog : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) / (n + 1)) (Real.log 2) := by
    have := Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / 2) (by norm_num [abs_of_pos])
    convert this using 1
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv, neg_neg]
  obtain ⟨m, hn⟩ := MajBy.tsum (σ := σ) hσ hK
    (f := fun (n : ℕ) ω Y => (-(1 / ((n : ℝ) + 1))) * (- ratioDev ζ y ω Y) ^ (n + 1))
    (h := fun ω Y => Real.log (Zc ζ ω (insert y Y)) - Real.log (Zc ζ ω Y))
    (c := fun (n : ℕ) A => 1 / ((n : ℝ) + 1) * cpow c0 (n + 1) A) (t := fun (n : ℕ) => (1 / 2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1))
    (fun n A => mul_nonneg (by positivity) (cpow_nonneg hc0 _ A))
    (fun n => (m0.neg.pow (n + 1)).const_mul (a := fun _ => -(1 / ((n : ℝ) + 1)))
      (fun _ => by rw [abs_neg, abs_of_pos (by positivity)]))
    (fun ω Y hY => by
      have hu := abs_le_wnorm hσ hK hc0 m0 ω hY
      have hv : |- ratioDev ζ y ω Y| < 1 := by rw [abs_neg]; linarith
      have hpos1 : 0 < Zc ζ ω Y := hW.1 ω Y (hY.trans (erase_subset _ _))
      have hpos2 : 0 < Zc ζ ω (insert y Y) :=
        hW.1 ω _ (insert_subset hy (hY.trans (erase_subset _ _)))
      have := (Real.hasSum_pow_div_log_of_abs_lt_one hv).neg
      convert this using 1
      · funext n; ring
      · unfold ratioDev
        have e : (1 : ℝ) - -(Zc ζ ω (insert y Y) / Zc ζ ω Y - 1) = Zc ζ ω (insert y Y) / Zc ζ ω Y := by ring
        rw [e, neg_neg, Real.log_div hpos2.ne' hpos1.ne'])
    (fun (n : ℕ) => by
      rw [wnorm_const_mul]
      have h1 := (wnorm_cpow_le hσ hc0 (n + 1)).trans (pow_le_pow_left₀ hn0' hn0 (n + 1))
      calc 1 / ((n : ℝ) + 1) * wnorm σ {y} (W.erase y) (cpow c0 (n + 1))
          ≤ 1 / ((n : ℝ) + 1) * (1 / 2) ^ (n + 1) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (1 / 2 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) := by ring)
    hlog.summable
  refine ⟨fun A => ∑' n : ℕ, 1 / ((n : ℝ) + 1) * cpow c0 (n + 1) A,
    fun A => tsum_nonneg fun n => mul_nonneg (by positivity) (cpow_nonneg hc0 _ A), m, ?_⟩
  rwa [hlog.tsum_eq] at hn

/-- **Removing the sites of `C` one at a time** (S): `P_C` has a majorant of norm `≤ e^{σ K} 2^{|C|}` for every anchor
`K ⊇ C`, given the induction hypothesis on all proper subregions. -/
theorem P_bound (hσ : Weight σ) {ζ : Finset V → Ω → ℝ} {W : Finset V} {y : V} (hy : y ∈ W)
    (hsub : ∀ W' ⊂ W, Good σ ζ W') (hpos : ∀ ω, ∀ Y ⊆ W.erase y, 0 < Zc ζ ω Y) :
    ∀ C : Finset V, C ⊆ W.erase y → ∀ K : Finset V, C ⊆ K →
      ∃ c : Finset V → ℝ, (∀ A, 0 ≤ c A) ∧ MajBy (W.erase y) (Pc ζ C) c ∧
        wnorm σ K (W.erase y) c ≤ Real.exp (σ K) * 2 ^ C.card := by
  intro C
  induction C using Finset.induction_on with
  | empty =>
    intro _ K _
    refine ⟨unitM, unitM_nonneg, (majBy_one (W.erase y)).congr fun ω Y hY => ?_, by rw [wnorm_unitM]; simp⟩
    unfold Pc
    rw [ite_eq_left_of_eq_true _ _ (eq_true (empty_subset Y)), sdiff_empty, div_self (hpos ω Y hY).ne']
  | insert c C hc ih =>
    intro hCU K hCK
    have hcU : c ∈ W.erase y := hCU (mem_insert_self c C)
    have hCU' : C ⊆ W.erase y := (subset_insert c C).trans hCU
    obtain ⟨cP, hcP0, mP, hnP⟩ := ih hCU' K ((subset_insert c C).trans hCK)
    have hcK : c ∈ K := hCK (mem_insert_self c C)
    have hW' : W.erase y \ C ⊂ W := by
      refine ssubset_of_subset_of_ne (sdiff_subset.trans (erase_subset y W)) fun h => ?_
      have : y ∈ W.erase y \ C := by rw [h]; exact hy
      exact (notMem_erase y W) (mem_sdiff.1 this).1
    have hcW' : c ∈ W.erase y \ C := mem_sdiff.2 ⟨hcU, hc⟩
    obtain ⟨c', hc'0, m', hn'⟩ := inv_of_good hσ (hsub _ hW') hcW'
    have hE : (W.erase y \ C).erase c = W.erase y \ insert c C := by
      ext x; simp only [mem_erase, mem_sdiff, mem_insert, not_or]; tauto
    rw [hE] at m' hn'
    have mq := majBy_shift (D := W.erase y) (E := insert c C) m'
    have hcq0 : ∀ A, 0 ≤ (fun A => if Disjoint A (insert c C) then c' A else 0) A := fun A => by
      dsimp only; split_ifs; exact hc'0 A; exact le_rfl
    refine ⟨conv (conv cP (deltaM c)) (fun A => if Disjoint A (insert c C) then c' A else 0),
      conv_nonneg (conv_nonneg hcP0 (deltaM_nonneg c)) hcq0,
      ((mP.mul (majBy_upS (W.erase y) c)).mul mq).congr fun ω Y hY => ?_, ?_⟩
    · -- the identity `P_{insert c C} = P_C · 1[c ∈ ·] · (inverse ratio shifted by insert c C)`
      unfold Pc upS
      by_cases h : insert c C ⊆ Y
      · have hcY : c ∈ Y := h (mem_insert_self c C)
        have hCY : C ⊆ Y := (subset_insert c C).trans h
        have e : insert c (Y \ insert c C) = Y \ C := by
          ext x; by_cases hx : x = c
          · subst hx; simp [hcY, hc]
          · simp [hx]
        rw [ite_eq_left_of_eq_true _ _ (eq_true hCY), ite_eq_left_of_eq_true _ _ (eq_true (singleton_subset_iff.2 hcY)), ite_eq_left_of_eq_true _ _ (eq_true h), invRatio, e]
        have h1 := hpos ω (Y \ C) (sdiff_subset.trans hY)
        have h2 := hpos ω Y hY
        field_simp
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]
        by_cases hcY : c ∈ Y
        · have hC : ¬ C ⊆ Y := fun hC => h (insert_subset hcY hC)
          simp [hC]
        · have hc' : ¬ ({c} : Finset V) ⊆ Y := by simpa using hcY
          simp [hc']
    · calc wnorm σ K (W.erase y) (conv (conv cP (deltaM c)) _)
          ≤ wnorm σ K (W.erase y) (conv cP (deltaM c)) *
              wnorm σ {c} (W.erase y) (fun A => if Disjoint A (insert c C) then c' A else 0) :=
            wnorm_conv_le hσ hcK (conv_nonneg hcP0 (deltaM_nonneg c)) hcq0
        _ ≤ (wnorm σ K (W.erase y) cP * wnorm σ {c} (W.erase y) (deltaM c)) * 2 := by
            rw [wnorm_shift]
            refine mul_le_mul (wnorm_conv_le hσ hcK hcP0 (deltaM_nonneg c)) hn' (wnorm_nonneg hc'0) ?_
            exact mul_nonneg (wnorm_nonneg hcP0) (wnorm_nonneg (deltaM_nonneg c))
        _ ≤ (Real.exp (σ K) * 2 ^ C.card * 1) * 2 := by
            rw [wnorm_deltaM hσ hcU]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnP zero_le_one) (by norm_num)
        _ = Real.exp (σ K) * 2 ^ (insert c C).card := by
            rw [card_insert_of_notMem hc, pow_succ]; ring

/-- The ratio deviation through the polymer recursion: `u_y = ∑_{γ ∋ y} ζ γ · P_{γ \ y}` on the subsets of `W \ y`. -/
theorem ratioDev_eq {ζ : Finset V → Ω → ℝ} {W : Finset V} {y : V} (hy : y ∈ W) (ω : Ω) {Y : Finset V}
    (hY : Y ⊆ W.erase y) (hpos : 0 < Zc ζ ω Y) :
    ratioDev ζ y ω Y = ∑ γ ∈ W.powerset.filter (fun γ => y ∈ γ), ζ γ ω * Pc ζ (γ.erase y) ω Y := by
  have hyY : y ∉ Y := fun h => (notMem_erase y W) (hY h)
  have hZ : Zc ζ ω (insert y Y) = Zc ζ ω Y + ∑ γ ∈ (insert y Y).powerset.filter (fun γ => y ∈ γ),
      ζ γ ω * Zc ζ ω (insert y Y \ γ) := gasZ_insert _ hyY
  have hset : (W.powerset.filter (fun γ => y ∈ γ)).filter (fun γ => γ.erase y ⊆ Y) =
      (insert y Y).powerset.filter (fun γ => y ∈ γ) := by
    ext γ; simp only [mem_filter, mem_powerset]
    constructor
    · rintro ⟨⟨-, hyγ⟩, hγY⟩
      refine ⟨fun x hx => ?_, hyγ⟩
      by_cases hxy : x = y
      · rw [hxy]; exact mem_insert_self y Y
      · exact mem_insert_of_mem (hγY (mem_erase.2 ⟨hxy, hx⟩))
    · rintro ⟨hγY, hyγ⟩
      refine ⟨⟨hγY.trans (insert_subset hy (hY.trans (erase_subset y W))), hyγ⟩, fun x hx => ?_⟩
      obtain ⟨hxy, hxγ⟩ := mem_erase.1 hx
      rcases mem_insert.1 (hγY hxγ) with h | h
      · exact absurd h hxy
      · exact h
  have hdiff : ∀ γ : Finset V, y ∈ γ → insert y Y \ γ = Y \ γ.erase y := by
    intro γ hyγ; ext x; simp only [mem_sdiff, mem_insert, mem_erase]; constructor
    · rintro ⟨hx | hx, hxγ⟩
      · exact absurd (hx ▸ hyγ) hxγ
      · exact ⟨hx, fun h => hxγ h.2⟩
    · rintro ⟨hx, hxγ⟩
      exact ⟨Or.inr hx, fun h => hxγ ⟨fun e => hyY (e ▸ hx), h⟩⟩
  unfold Pc
  simp_rw [mul_ite, mul_zero]
  rw [← sum_filter, hset, ratioDev, hZ]
  rw [show (Zc ζ ω Y + ∑ γ ∈ (insert y Y).powerset.filter (fun γ => y ∈ γ), ζ γ ω * Zc ζ ω (insert y Y \ γ)) /
      Zc ζ ω Y - 1 = (∑ γ ∈ (insert y Y).powerset.filter (fun γ => y ∈ γ), ζ γ ω * Zc ζ ω (insert y Y \ γ)) /
      Zc ζ ω Y by field_simp; ring, sum_div]
  refine sum_congr rfl fun γ hγ => ?_
  rw [hdiff γ (mem_filter.1 hγ).2, mul_div_assoc]

/-- **The inductive step** (S): if every proper subregion is good, so is `W`. -/
theorem good_of_sub (hσ : Weight σ) {ζ : Finset V → Ω → ℝ} {zb : Finset V → ℝ} (hzb : ∀ γ, 0 ≤ zb γ)
    (hz : ∀ γ ω, |ζ γ ω| ≤ zb γ) (hKP : KPCrit σ zb) {W : Finset V} (hsub : ∀ W' ⊂ W, Good σ ζ W') :
    Good σ ζ W := by
  have hratio : ∀ y ∈ W, ∃ c : Finset V → ℝ, (∀ A, 0 ≤ c A) ∧ MajBy (W.erase y) (ratioDev ζ y) c ∧
      wnorm σ {y} (W.erase y) c ≤ 1 / 2 := by
    intro y hy
    have hUW : W.erase y ⊂ W := erase_ssubset hy
    have hpos : ∀ ω, ∀ Y ⊆ W.erase y, 0 < Zc ζ ω Y := fun ω Y hY => (hsub _ hUW).1 ω Y hY
    have hterm : ∀ γ ∈ W.powerset.filter (fun γ => y ∈ γ), ∃ c : Finset V → ℝ, (∀ A, 0 ≤ c A) ∧
        MajBy (W.erase y) (Pc ζ (γ.erase y)) c ∧
        wnorm σ {y} (W.erase y) c ≤ Real.exp (σ γ) * 2 ^ (γ.card - 1) := by
      intro γ hγ
      obtain ⟨hγW, hyγ⟩ := mem_filter.1 hγ
      have hCU : γ.erase y ⊆ W.erase y := erase_subset_erase y (mem_powerset.1 hγW)
      obtain ⟨c0, hc00, m0, hn0⟩ := P_bound hσ hy hsub hpos (γ.erase y) hCU γ (erase_subset y γ)
      refine ⟨fun A => if γ.erase y ⊆ A then c0 A else 0, fun A => by
        dsimp only; split_ifs; exact hc00 A; exact le_rfl, ?_, ?_⟩
      · intro ω A hA
        dsimp only
        by_cases hA' : γ.erase y ⊆ A
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hA')]; exact m0 ω A hA
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hA')]
          have e : Pc ζ (γ.erase y) ω = fun Y => upS (γ.erase y) Y * (Zc ζ ω (Y \ γ.erase y) / Zc ζ ω Y) := by
            funext Y; unfold Pc upS; split_ifs <;> simp
          rw [e, mob_upS_mul_eq_zero _ _ hA', abs_zero]
      · rw [← card_erase_of_mem hyγ]
        exact (wnorm_trunc_le (insert_erase hyγ).symm hc00).trans hn0
    choose! cγ hcγ0 mγ hnγ using hterm
    refine ⟨fun A => ∑ γ ∈ W.powerset.filter (fun γ => y ∈ γ), zb γ * cγ γ A,
      fun A => sum_nonneg fun γ hγ => mul_nonneg (hzb γ) (hcγ0 γ hγ A), ?_, ?_⟩
    · refine (MajBy.sum _ fun γ hγ => (mγ γ hγ).const_mul (a := fun ω => ζ γ ω) (fun ω => hz γ ω)).congr
        fun ω Y hY => (ratioDev_eq hy ω hY (hpos ω Y hY)).symm
    · rw [wnorm_sum]
      calc ∑ γ ∈ W.powerset.filter (fun γ => y ∈ γ), wnorm σ {y} (W.erase y) (fun A => zb γ * cγ γ A)
          = ∑ γ ∈ W.powerset.filter (fun γ => y ∈ γ), zb γ * wnorm σ {y} (W.erase y) (cγ γ) :=
            sum_congr rfl fun γ _ => wnorm_const_mul _ _ _ _
        _ ≤ ∑ γ ∈ W.powerset.filter (fun γ => y ∈ γ), zb γ * (Real.exp (σ γ) * 2 ^ (γ.card - 1)) :=
            sum_le_sum fun γ hγ => mul_le_mul_of_nonneg_left (hnγ γ hγ) (hzb γ)
        _ = 1 / 2 * ∑ γ ∈ W.powerset.filter (fun γ => y ∈ γ), zb γ * 2 ^ γ.card * Real.exp (σ γ) := by
            rw [mul_sum]
            refine sum_congr rfl fun γ hγ => ?_
            have hc : γ.card - 1 + 1 = γ.card := Nat.sub_add_cancel (card_pos.2 ⟨y, (mem_filter.1 hγ).2⟩)
            rw [← hc, pow_succ, Nat.add_sub_cancel]
            ring
        _ ≤ 1 / 2 * ∑ γ ∈ (univ : Finset (Finset V)).filter (fun γ => y ∈ γ), zb γ * 2 ^ γ.card * Real.exp (σ γ) := by
            refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg ?_ fun γ _ _ => ?_) (by norm_num)
            · intro γ hγ; exact mem_filter.2 ⟨mem_univ γ, (mem_filter.1 hγ).2⟩
            · exact mul_nonneg (mul_nonneg (hzb γ) (by positivity)) (Real.exp_pos _).le
        _ ≤ 1 / 2 * 1 := mul_le_mul_of_nonneg_left (hKP y) (by norm_num)
        _ = 1 / 2 := by ring
  refine ⟨fun ω Y hY => ?_, hratio⟩
  by_cases hYW : Y = W
  · subst hYW
    rcases Y.eq_empty_or_nonempty with h0 | ⟨y, hy⟩
    · rw [h0]; unfold Zc; rw [gasZ_empty]; exact one_pos
    · obtain ⟨c, hc0, m, hn⟩ := hratio y hy
      have hU := (hsub _ (erase_ssubset hy)).1 ω (Y.erase y) subset_rfl
      have hu := abs_le_wnorm hσ (singleton_nonempty y) hc0 m ω (subset_refl (Y.erase y))
      have e : Zc ζ ω Y = Zc ζ ω (Y.erase y) * (ratioDev ζ y ω (Y.erase y) + 1) := by
        unfold ratioDev; rw [insert_erase hy]; field_simp; ring
      rw [e]
      have : -(1 / 2 : ℝ) ≤ ratioDev ζ y ω (Y.erase y) := by
        have := neg_abs_le (ratioDev ζ y ω (Y.erase y)); linarith
      exact mul_pos hU (by linarith)
  · exact (hsub Y (ssubset_of_subset_of_ne hY hYW)).1 ω Y subset_rfl

/-- Every region is good (strong induction). -/
theorem good_all (hσ : Weight σ) {ζ : Finset V → Ω → ℝ} {zb : Finset V → ℝ} (hzb : ∀ γ, 0 ≤ zb γ)
    (hz : ∀ γ ω, |ζ γ ω| ≤ zb γ) (hKP : KPCrit σ zb) (W : Finset V) : Good σ ζ W :=
  Finset.strongInduction (fun _ ih => good_of_sub hσ hzb hz hKP ih) W

theorem union_singleton_erase {y : V} {X : Finset V} (hy : y ∈ X) : X.erase y ∪ {y} = X := by
  ext x; by_cases hx : x = y
  · subst hx; simp [hy]
  · simp [hx]

/-- A cluster potential through `y` inside `W` is bounded by the majorant of the log-ratio at `y`. -/
theorem abs_clusterPot_le {ζ : Finset V → Ω → ℝ} {W : Finset V} {y : V} {c : Finset V → ℝ}
    (m : MajBy (W.erase y) (fun ω Y => Real.log (Zc ζ ω (insert y Y)) - Real.log (Zc ζ ω Y)) c) (ω : Ω)
    {X : Finset V} (hXW : X ⊆ W) (hyX : y ∈ X) : |clusterPot ζ ω X| ≤ c (X.erase y) := by
  have e : clusterPot ζ ω X = mob (fun Y => Real.log (Zc ζ ω (insert y Y)) - Real.log (Zc ζ ω Y)) (X.erase y) := by
    rw [clusterPot]; conv_lhs => rw [← insert_erase hyX]
    exact mob_insert (notMem_erase y X)
  rw [e]
  exact m ω _ (mem_powerset.2 (erase_subset_erase y hXW))

/-- **The Kotecky–Preiss theorem with exponential tails** (S). Under an admissible weight `σ`, activity bounds
`|ζ γ ω| ≤ ζ̄ γ` and the criterion `∑_{γ ∋ y} ζ̄ γ 2^{|γ|} e^{σ γ} ≤ 1`: every partition function is positive, every
cluster potential is bounded uniformly in the configuration, and for every region `W` and site `y ∈ W`,
`∑_{X ⊆ W, X ∋ y} sup_ω |clusterPot X| · e^{σ X} ≤ log 2`. -/
theorem kotecky_preiss (hσ : Weight σ) {ζ : Finset V → Ω → ℝ} {zb : Finset V → ℝ} (hzb : ∀ γ, 0 ≤ zb γ)
    (hz : ∀ γ ω, |ζ γ ω| ≤ zb γ) (hKP : KPCrit σ zb) :
    (∀ ω Y, 0 < Zc ζ ω Y) ∧ (∀ X, BddAbove (Set.range fun ω => |clusterPot ζ ω X|)) ∧
      ∀ W : Finset V, ∀ y ∈ W,
        ∑ X ∈ W.powerset.filter (fun X => y ∈ X), clusterBar ζ X * Real.exp (σ X) ≤ Real.log 2 := by
  have hg := good_all hσ hzb hz hKP
  refine ⟨fun ω Y => (hg Y).1 ω Y subset_rfl, fun X => ?_, fun W y hy => ?_⟩
  · rcases X.eq_empty_or_nonempty with h0 | ⟨y, hy⟩
    · exact ⟨0, by rintro _ ⟨ω, rfl⟩; dsimp only; rw [h0, clusterPot_empty, abs_zero]⟩
    · obtain ⟨c, -, m, -⟩ := log_of_good hσ (hg X) hy
      exact ⟨c (X.erase y), by rintro _ ⟨ω, rfl⟩; exact abs_clusterPot_le m ω subset_rfl hy⟩
  · obtain ⟨c, hc0, m, hn⟩ := log_of_good hσ (hg W) hy
    refine le_trans ?_ hn
    unfold wnorm
    calc ∑ X ∈ W.powerset.filter (fun X => y ∈ X), clusterBar ζ X * Real.exp (σ X)
        ≤ ∑ X ∈ W.powerset.filter (fun X => y ∈ X), c (X.erase y) * Real.exp (σ (X.erase y ∪ {y})) := by
          refine sum_le_sum fun X hX => ?_
          obtain ⟨hXW, hyX⟩ := mem_filter.1 hX
          rw [union_singleton_erase hyX]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact Real.iSup_le (fun ω => abs_clusterPot_le m ω (mem_powerset.1 hXW) hyX) (hc0 _)
      _ = ∑ A ∈ (W.erase y).powerset, c A * Real.exp (σ (A ∪ {y})) := by
          refine sum_nbij' (fun X => X.erase y) (fun A => insert y A) ?_ ?_ ?_ ?_ ?_
          · intro X hX
            exact mem_powerset.2 (erase_subset_erase y (mem_powerset.1 (mem_filter.1 hX).1))
          · intro A hA
            exact mem_filter.2 ⟨mem_powerset.2 (insert_subset hy ((mem_powerset.1 hA).trans (erase_subset y W))),
              mem_insert_self y A⟩
          · intro X hX; exact insert_erase (mem_filter.1 hX).2
          · intro A hA
            exact erase_insert fun h => (notMem_erase y W) (mem_powerset.1 hA h)
          · intro X _; rfl

end KP

end ProofPhase.Seg1
