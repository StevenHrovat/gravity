/-
The Existence Turing Machine round: rooted running systems, derived from G0 in finitely many steps (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/ETM.md`, section 6.
-/

import ProofPhase.ETM.Instances

/-!
# Rooted running systems

**The thesis restated (the owner).** Every meaning of existence that is in accordance with the root G0, through which
the whole chain derives its physical existence; otherwise an infinite series. Read: *rooted* = *well-founded*. Every
derivation, followed backwards, reaches G0 in finitely many steps. In Lean an inductive definition is exactly that:
every proof of `Rooted P` is a finite tree of constructors whose leaves are G0.

**Pre-systems (`Pre`).** The data of a running system without its laws: states, step, factor, mass, floor.
`Pre.IsInstance` is the law (`RunSys`): factor in `[0, 1]`, mass `≥ 0`, `mass (step x) ≤ e^floor · fac x · mass x`.

**G0 and the constructors (`Rooted`).**
* `root` (**G0**): a positive weight transported by a positive (stochastic) kernel, compared with a second one: the
  Markov system `markov K` (states: pairs of probability laws; factor: a Dobrushin coefficient; mass: their
  total-variation distance). With the identity kernel on `Bool` it is the bare tick (`tick`): binary existence, mass
  `1`, factor `1`, persisting at every step (`tick_persists`).
* `reflectSzego`, `reflectElec` (**the reflection**): one boundary with a positive form (an `Encoder`) per step, read
  through the Szego or the electric profile; the factor is multiplied by it and the mass by the running product.
* `twice` (**composition of steps**): two steps as one, factors multiplied, floors added.
* `subset` (**restriction to a sub-box, "establishing itself as a subset"**): anything that embeds into a rooted system
  (injective, commuting with the step, preserving factor, mass and floor) is rooted.
* `scale` (normalising the weight) and `relax` (raising the floor).

**The form layer (`Rooted.good`, `rooted_is_instance`).** By induction over the derivation: every rooted pre-system is
a DMP instance (a running system, hence with its unique trace into the ledger space), and its mass never increases.
This is true for every content because it says nothing about content: it is the form layer, the design.

**The content layer, checked separately.**
* (i) *The known systems are rooted*: Markov chains (`markov_rooted`), SU(N) box chains for every `N`
  (`ymBoxes_rooted`, using the strict twist bound to place the twist ratio in the disk), Szego chains of encoders
  (`szegoChain_rooted`) and of coefficients in the closed disk (`szegoCoeffs_rooted`, where the sign is used), the
  certificate of a refutation under restrictions (`proofCert_rooted`, `proof_certified`), the shrinker's metric
  (`shrinker_rooted`).
* (ii) *G0 is not trivial*: the tick carries a persisting unit of existence (`tick_persists`); rooted systems realise
  every factor in `[0, 1]` and every starting mass (`rooted_factor_mass`); and not every running system is rooted: the
  shrinker's curvature satisfies the law with floor `log 2` and is not rooted (`curvature_not_rooted`).

**Encoders realise exactly the closed disk** (`encoder_realize` with `Encoder.norm_refl_le`): every real `c` with
`|c| ≤ 1` is the reflection coefficient of an encoder on `ℂ` over `ℝ`. So the reflection constructor accepts a
coefficient exactly when a positive form carries it; each instance supplies that from its own content.

No axioms beyond the standard ones.
-/

open Finset ProofPhase.Unified ProofPhase.Mixing
open scoped ComplexConjugate

noncomputable section

namespace ProofPhase.ETM

/-! ## 1. Pre-systems and the law -/

/-- **A pre-system**: the data of a running system, without its laws. -/
structure Pre where
  /-- States. -/
  X : Type
  /-- The step. -/
  step : X → X
  /-- The factor. -/
  fac : X → ℝ
  /-- The mass. -/
  mass : X → ℝ
  /-- The floor. -/
  floor : ℝ

namespace Pre

/-- **A DMP instance**: the laws of a running system hold. -/
def IsInstance (P : Pre) : Prop :=
  (∀ x, 0 ≤ P.fac x) ∧ (∀ x, P.fac x ≤ 1) ∧ (∀ x, 0 ≤ P.mass x) ∧
    ∀ x, P.mass (P.step x) ≤ Real.exp P.floor * P.fac x * P.mass x

/-- An instance, together with: the mass never increases. -/
def Good (P : Pre) : Prop := P.IsInstance ∧ ∀ x, P.mass (P.step x) ≤ P.mass x

/-- The running system of an instance. -/
def toRunSys (P : Pre) (h : P.IsInstance) : RunSys.{0} P.floor :=
  ⟨P.X, P.step, P.fac, P.mass, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- **The reflection**: one more boundary per step, factor `f n` at step `n`; the state remembers the step count. -/
def reflect (P : Pre) (f : ℕ → ℝ) : Pre :=
  ⟨P.X × ℕ, fun p => (P.step p.1, p.2 + 1), fun p => f p.2 * P.fac p.1,
    fun p => (∏ j ∈ range p.2, f j) * P.mass p.1, P.floor⟩

/-- **Composition of steps**: two steps as one. -/
def twice (P : Pre) : Pre :=
  ⟨P.X, P.step ∘ P.step, fun x => P.fac x * P.fac (P.step x), P.mass, 2 * P.floor⟩

/-- Normalising the weight. -/
def scale (P : Pre) (r : ℝ) : Pre := ⟨P.X, P.step, P.fac, fun x => r * P.mass x, P.floor⟩

/-- Raising the floor. -/
def relax (P : Pre) (δ' : ℝ) : Pre := ⟨P.X, P.step, P.fac, P.mass, δ'⟩

/-- **An embedding** of `Q` into `P`: `Q` establishes itself as a subset of `P`. -/
structure Embed (Q P : Pre) where
  toFun : Q.X → P.X
  inj : Function.Injective toFun
  step_comm : ∀ x, toFun (Q.step x) = P.step (toFun x)
  fac_eq : ∀ x, P.fac (toFun x) = Q.fac x
  mass_eq : ∀ x, P.mass (toFun x) = Q.mass x
  floor_eq : P.floor = Q.floor

end Pre

/-- The pre-system of a running system. -/
def RunSys.toPre {δ : ℝ} (S : RunSys.{0} δ) : Pre := ⟨S.X, S.step, S.fac, S.mass, δ⟩

theorem RunSys.toPre_isInstance {δ : ℝ} (S : RunSys.{0} δ) : S.toPre.IsInstance :=
  ⟨S.fac_nonneg, S.fac_le_one, S.mass_nonneg, S.pays⟩

/-! ## 2. G0 and the constructors -/

/-- **Rooted pre-systems**: derived from G0 by finitely many constructors. -/
inductive Rooted : Pre → Prop
  /-- **G0**: a positive weight transported by a positive (stochastic) kernel, compared with a second one. -/
  | root {Y : Type} [Fintype Y] [DecidableEq Y] (K : Y → Y → ℝ) (hK : IsStoch K) (η : ℝ) (hη : Contracts K η)
      (h0 : 0 ≤ η) (h1 : η ≤ 1) : Rooted (RunSys.markov K hK η hη h0 h1).toPre
  /-- **The reflection**, Szego profile: one encoder per step. -/
  | reflectSzego {P : Pre} {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
      (X : ℕ → Encoder 𝕜 E) : Rooted P → Rooted (P.reflect fun n => szego (X n).refl)
  /-- **The reflection**, electric profile: one real encoder per step, with a nonnegative coefficient. -/
  | reflectElec {P : Pre} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (X : ℕ → Encoder ℝ E)
      (hc : ∀ n, 0 ≤ (X n).refl) : Rooted P → Rooted (P.reflect fun n => elec (X n).refl)
  /-- **Composition of steps.** -/
  | twice {P : Pre} : Rooted P → Rooted P.twice
  /-- Normalising the weight. -/
  | scale {P : Pre} {r : ℝ} (hr : 0 ≤ r) : Rooted P → Rooted (P.scale r)
  /-- Raising the floor. -/
  | relax {P : Pre} {δ' : ℝ} (h : P.floor ≤ δ') : Rooted P → Rooted (P.relax δ')
  /-- **Restriction to a subset**: whatever establishes itself as a subset of a rooted system is rooted. -/
  | subset {P Q : Pre} (e : Q.Embed P) : Rooted P → Rooted Q

/-! ## 3. The form layer: every rooted system is a DMP instance -/

theorem elec_mem_unit {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) : 0 ≤ elec c ∧ elec c ≤ 1 := by
  unfold elec
  exact ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩

theorem good_of_floor {P : Pre} (h : P.IsInstance) (hf : P.floor ≤ 0) : P.Good := by
  refine ⟨h, fun x => (h.2.2.2 x).trans ?_⟩
  have he : Real.exp P.floor ≤ 1 := Real.exp_le_one_iff.2 hf
  have h1 : Real.exp P.floor * P.fac x ≤ 1 :=
    (mul_le_of_le_one_left (h.1 x) he).trans (h.2.1 x)
  nlinarith [h.2.2.1 x, mul_nonneg (Real.exp_pos P.floor).le (h.1 x)]

theorem reflect_good {P : Pre} (hP : P.Good) {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (hf1 : ∀ n, f n ≤ 1) :
    (P.reflect f).Good := by
  obtain ⟨⟨hfa0, hfa1, hm0, hlaw⟩, hanti⟩ := hP
  have hp : ∀ n, 0 ≤ ∏ j ∈ range n, f j := fun n => prod_nonneg fun j _ => hf0 j
  refine ⟨⟨fun p => mul_nonneg (hf0 _) (hfa0 _), fun p => (mul_le_of_le_one_left (hfa0 _) (hf1 _)).trans (hfa1 _),
    fun p => mul_nonneg (hp _) (hm0 _), fun p => ?_⟩, fun p => ?_⟩
  · show (∏ j ∈ range (p.2 + 1), f j) * P.mass (P.step p.1) ≤
      Real.exp P.floor * (f p.2 * P.fac p.1) * ((∏ j ∈ range p.2, f j) * P.mass p.1)
    rw [prod_range_succ]
    calc (∏ j ∈ range p.2, f j) * f p.2 * P.mass (P.step p.1)
        ≤ (∏ j ∈ range p.2, f j) * f p.2 * (Real.exp P.floor * P.fac p.1 * P.mass p.1) :=
          mul_le_mul_of_nonneg_left (hlaw _) (mul_nonneg (hp _) (hf0 _))
      _ = Real.exp P.floor * (f p.2 * P.fac p.1) * ((∏ j ∈ range p.2, f j) * P.mass p.1) := by ring
  · show (∏ j ∈ range (p.2 + 1), f j) * P.mass (P.step p.1) ≤ (∏ j ∈ range p.2, f j) * P.mass p.1
    rw [prod_range_succ]
    exact mul_le_mul (mul_le_of_le_one_right (hp _) (hf1 _)) (hanti _) (hm0 _) (hp _)

theorem twice_good {P : Pre} (hP : P.Good) : P.twice.Good := by
  obtain ⟨⟨hfa0, hfa1, hm0, hlaw⟩, hanti⟩ := hP
  refine ⟨⟨fun x => mul_nonneg (hfa0 _) (hfa0 _), fun x => (mul_le_of_le_one_left (hfa0 _) (hfa1 _)).trans (hfa1 _), hm0,
    fun x => ?_⟩, fun x => (hanti _).trans (hanti x)⟩
  show P.mass (P.step (P.step x)) ≤ Real.exp (2 * P.floor) * (P.fac x * P.fac (P.step x)) * P.mass x
  calc P.mass (P.step (P.step x)) ≤ Real.exp P.floor * P.fac (P.step x) * P.mass (P.step x) := hlaw _
    _ ≤ Real.exp P.floor * P.fac (P.step x) * (Real.exp P.floor * P.fac x * P.mass x) :=
        mul_le_mul_of_nonneg_left (hlaw x) (mul_nonneg (Real.exp_pos _).le (hfa0 _))
    _ = Real.exp (2 * P.floor) * (P.fac x * P.fac (P.step x)) * P.mass x := by
        rw [two_mul, Real.exp_add]; ring

theorem scale_good {P : Pre} (hP : P.Good) {r : ℝ} (hr : 0 ≤ r) : (P.scale r).Good := by
  obtain ⟨⟨hfa0, hfa1, hm0, hlaw⟩, hanti⟩ := hP
  refine ⟨⟨hfa0, hfa1, fun x => mul_nonneg hr (hm0 x), fun x => ?_⟩, fun x => mul_le_mul_of_nonneg_left (hanti x) hr⟩
  show r * P.mass (P.step x) ≤ Real.exp P.floor * P.fac x * (r * P.mass x)
  have := mul_le_mul_of_nonneg_left (hlaw x) hr
  linarith [show r * (Real.exp P.floor * P.fac x * P.mass x) = Real.exp P.floor * P.fac x * (r * P.mass x) by ring]

theorem relax_good {P : Pre} (hP : P.Good) {δ' : ℝ} (h : P.floor ≤ δ') : (P.relax δ').Good := by
  obtain ⟨⟨hfa0, hfa1, hm0, hlaw⟩, hanti⟩ := hP
  exact ⟨⟨hfa0, hfa1, hm0, fun x => (hlaw x).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h) (hfa0 x)) (hm0 x))⟩, hanti⟩

theorem subset_good {P Q : Pre} (e : Q.Embed P) (hP : P.Good) : Q.Good := by
  obtain ⟨⟨hfa0, hfa1, hm0, hlaw⟩, hanti⟩ := hP
  refine ⟨⟨fun x => e.fac_eq x ▸ hfa0 _, fun x => e.fac_eq x ▸ hfa1 _, fun x => e.mass_eq x ▸ hm0 _,
    fun x => ?_⟩, fun x => ?_⟩
  · calc Q.mass (Q.step x) = P.mass (e.toFun (Q.step x)) := (e.mass_eq _).symm
      _ = P.mass (P.step (e.toFun x)) := by rw [e.step_comm]
      _ ≤ Real.exp P.floor * P.fac (e.toFun x) * P.mass (e.toFun x) := hlaw _
      _ = Real.exp Q.floor * Q.fac x * Q.mass x := by rw [e.floor_eq, e.fac_eq, e.mass_eq]
  · calc Q.mass (Q.step x) = P.mass (e.toFun (Q.step x)) := (e.mass_eq _).symm
      _ = P.mass (P.step (e.toFun x)) := by rw [e.step_comm]
      _ ≤ P.mass (e.toFun x) := hanti _
      _ = Q.mass x := e.mass_eq x

/-- **Every rooted pre-system is a DMP instance, and its mass never increases** (induction over the derivation). -/
theorem Rooted.good {P : Pre} (h : Rooted P) : P.Good := by
  induction h with
  | root K hK η hη h0 h1 => exact good_of_floor (RunSys.toPre_isInstance _) le_rfl
  | reflectSzego X _ ih => exact reflect_good ih (fun n => (szego_mem (X n)).1) (fun n => (szego_mem (X n)).2)
  | reflectElec X hc _ ih =>
    refine reflect_good ih (fun n => (elec_mem_unit (hc n) ?_).1) (fun n => (elec_mem_unit (hc n) ?_).2) <;>
      exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (X n).norm_refl_le)
  | twice _ ih => exact twice_good ih
  | scale hr _ ih => exact scale_good ih hr
  | relax hδ _ ih => exact relax_good ih hδ
  | subset e _ ih => exact subset_good e ih

/-- **The sharpened thesis, as a theorem**: every rooted running system is a DMP instance, with its unique map into the
ledger space. -/
theorem rooted_is_instance {P : Pre} (h : Rooted P) :
    P.IsInstance ∧ ∃! _ : RunSys.Hom (P.toRunSys h.good.1) (RunSys.univ.{0} P.floor), True :=
  ⟨h.good.1, RunSys.exists_unique_hom _⟩

/-! ## 4. Encoders realise the closed disk -/

/-- **Every real `c` with `|c| ≤ 1` is a reflection coefficient**: `ψ = 1`, `ψ' = c + i √(1 − c²)` in `ℂ` over `ℝ`. -/
theorem encoder_realize {c : ℝ} (hc : |c| ≤ 1) : ∃ X : Encoder ℝ ℂ, X.refl = c := by
  have hs : 0 ≤ 1 - c ^ 2 := by nlinarith [abs_le.1 hc]
  have hn : ‖(⟨c, Real.sqrt (1 - c ^ 2)⟩ : ℂ)‖ = 1 := by
    have h2 : ‖(⟨c, Real.sqrt (1 - c ^ 2)⟩ : ℂ)‖ ^ 2 = 1 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_mk, Real.mul_self_sqrt hs]; ring
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 h2
  refine ⟨⟨1, ⟨c, Real.sqrt (1 - c ^ 2)⟩, by rw [hn, norm_one], one_ne_zero⟩, ?_⟩
  simp [Encoder.refl, Complex.inner]

/-- Every factor in `[0, 1]` is a Szego factor of an encoder. -/
theorem szego_realize {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) : ∃ X : Encoder ℝ ℂ, szego X.refl = f := by
  obtain ⟨X, hX⟩ := encoder_realize (c := Real.sqrt (1 - f)) (by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact Real.sqrt_le_one.2 (by linarith))
  refine ⟨X, ?_⟩
  rw [hX, szego, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by linarith)]
  ring

/-! ## 5. The tick and the chains -/

/-- `δ_true`, `δ_false`: binary existence. -/
def p0 : RunSys.ProbPair Bool :=
  ⟨(fun b => if b then 1 else 0, fun b => if b then 0 else 1),
    fun b => by cases b <;> simp, fun b => by cases b <;> simp, by simp, by simp⟩

/-- **The tick**: G0 with the identity kernel on `Bool`. -/
def tick : RunSys.{0} 0 := RunSys.markov (idK Bool) isStoch_idK 1 isStoch_idK.contracts_one zero_le_one le_rfl

theorem tick_rooted : Rooted tick.toPre := Rooted.root _ _ _ _ _ _

theorem tick_step : tick.step p0 = p0 := by
  apply Subtype.ext
  show (pushv p0.1.1 (idK Bool), pushv p0.1.2 (idK Bool)) = p0.1
  ext y <;> cases y <;> simp [pushv, idK, p0]

theorem tick_mass : tick.mass p0 = 1 := by
  show tv p0.1.1 p0.1.2 = 1
  simp [tv, p0]

/-- **G0 carries a persisting unit of existence**: from binary existence the tick keeps mass `1` and factor `1` at
every step; it never balances. -/
theorem tick_persists (n : ℕ) : tick.mass (tick.step^[n] p0) = 1 ∧ tick.fac (tick.step^[n] p0) = 1 := by
  have : tick.step^[n] p0 = p0 := Function.iterate_fixed tick_step n
  rw [this, tick_mass]
  exact ⟨rfl, rfl⟩

/-- A chain on `ℕ`. -/
def chainPre (f m : ℕ → ℝ) (δ : ℝ) : Pre := ⟨ℕ, Nat.succ, f, m, δ⟩

/-- The chain of a factor stream sits in the tick reflected by that stream and scaled. -/
def chainEmbed (f : ℕ → ℝ) (m₀ : ℝ) :
    (chainPre f (fun n => m₀ * ∏ j ∈ range n, f j) 0).Embed ((tick.toPre.reflect f).scale m₀) where
  toFun (i : ℕ) := (p0, i)
  inj _ _ h := (Prod.mk.inj h).2
  step_comm (i : ℕ) := by
    show (p0, i + 1) = (tick.step p0, i + 1)
    rw [tick_step]; rfl
  fac_eq (i : ℕ) := by
    show f i * tick.fac p0 = f i
    exact mul_one _
  mass_eq (i : ℕ) := by
    show m₀ * ((∏ j ∈ range i, f j) * tick.mass p0) = m₀ * ∏ j ∈ range i, f j
    rw [tick_mass, mul_one]
  floor_eq := rfl

/-- **A Szego chain of encoders is rooted.** -/
theorem chain_rooted_szego {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (X : ℕ → Encoder 𝕜 E) {m₀ : ℝ} (hm : 0 ≤ m₀) :
    Rooted (chainPre (fun n => szego (X n).refl) (fun n => m₀ * ∏ j ∈ range n, szego (X j).refl) 0) :=
  Rooted.subset (chainEmbed _ m₀) (Rooted.scale hm (Rooted.reflectSzego X tick_rooted))

/-- **An electric chain of real encoders with nonnegative coefficients is rooted.** -/
theorem chain_rooted_elec {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (X : ℕ → Encoder ℝ E)
    (hc : ∀ n, 0 ≤ (X n).refl) {m₀ : ℝ} (hm : 0 ≤ m₀) :
    Rooted (chainPre (fun n => elec (X n).refl) (fun n => m₀ * ∏ j ∈ range n, elec (X j).refl) 0) :=
  Rooted.subset (chainEmbed _ m₀) (Rooted.scale hm (Rooted.reflectElec X hc tick_rooted))

/-- **Every constant factor in `[0, 1]` with any starting mass is rooted** (Szego realisation). -/
theorem chain_rooted_const {f m₀ : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) (hm : 0 ≤ m₀) :
    Rooted (chainPre (fun _ => f) (fun n => m₀ * f ^ n) 0) := by
  obtain ⟨X, hX⟩ := szego_realize h0 h1
  have r := chain_rooted_szego (fun _ => X) hm
  simp only [hX, prod_const, card_range] at r
  exact r

/-! ## 6. The content layer (i): the known systems are rooted -/

/-- **Markov chains** are G0 itself. -/
theorem markov_rooted {Y : Type} [Fintype Y] [DecidableEq Y] (K : Y → Y → ℝ) (hK : IsStoch K) (η : ℝ)
    (hη : Contracts K η) (h0 : 0 ≤ η) (h1 : η ≤ 1) : Rooted (RunSys.markov K hK η hη h0 h1).toPre :=
  Rooted.root K hK η hη h0 h1

section YangMills

open ProofPhase.General

variable (N : ℕ) [NeZero N] [Fact (1 < N)] (L : ℕ) [NeZero L]

/-- **SU(N) box chains are rooted**, every `N`: the strict twist bound places the twist ratio `Z_tw,k / Z` in
`(0, 1)`, so a positive form carries it, and the electric reflection of the tick gives the chain. -/
theorem ymBoxes_rooted {β : ℝ} (hβ : β ≠ 0) (P : Finset (LatticePlaquette 3 L)) (c : ZMod L) {T : ℕ} [NeZero T]
    (hT : Even T) {k : ZMod N} (hk : k ≠ 0) : Rooted (RunSys.ymBoxes N L hβ P c hT hk).toPre := by
  have hr := sunTwistRatio_mem N L hβ P c hT hk
  obtain ⟨X, hX⟩ := encoder_realize (c := sunZtw N L β P c T k / sunZ N L β P T)
    (abs_le.2 ⟨by linarith [hr.1], hr.2.le⟩)
  have r := chain_rooted_elec (fun _ => X) (fun _ => hX ▸ hr.1.le) zero_le_one
  simp only [hX, one_mul] at r
  exact r

end YangMills

/-- **Szego chains of encoders are rooted** (GRH's chain, given encoders). -/
theorem szegoChain_rooted {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (X : ℕ → Encoder 𝕜 E) : Rooted (RunSys.szegoChain X).toPre := by
  have r := chain_rooted_szego X zero_le_one
  simp only [one_mul] at r
  exact r

/-- **Szego chains of coefficients in the closed disk are rooted**: the sign `‖k i‖ ≤ 1` is exactly what lets a
positive form carry each coefficient. -/
theorem szegoCoeffs_rooted {𝕜 : Type} [RCLike 𝕜] (k : ℕ → 𝕜) (hk : ∀ i, ‖k i‖ ≤ 1) :
    Rooted (RunSys.szegoCoeffs k hk).toPre := by
  choose X hX using fun i => encoder_realize (c := ‖k i‖) (by rw [abs_of_nonneg (norm_nonneg _)]; exact hk i)
  have hs : ∀ i, szego (X i).refl = szego (k i) := fun i => by
    rw [hX, szego, szego, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have r := chain_rooted_szego X zero_le_one
  simp only [hs, one_mul] at r
  exact r

/-- **The certificate of a refutation under restrictions is rooted**: factor `1 − θ`, mass `|Q 0| (1 − θ)^i`. -/
theorem proofCert_rooted {θ m₀ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hm : 0 ≤ m₀) :
    Rooted (chainPre (fun _ => 1 - θ) (fun n => m₀ * (1 - θ) ^ n) 0) :=
  chain_rooted_const (by linarith) (by linarith) hm

/-- **The rooted certificate bounds the costly lines**: under the restriction steps, `|Q i| ≤ |Q 0| (1 − θ)^i` for
`i ≤ b` (the ledger). -/
theorem proof_certified {Line : Type*} (Q : ℕ → Finset Line) {θ : ℝ} (hθ1 : θ ≤ 1) {b : ℕ}
    (h : ∀ i < b, ((Q (i + 1)).card : ℝ) ≤ (1 - θ) * (Q i).card) :
    ∀ i ≤ b, ((Q i).card : ℝ) ≤ (Q 0).card * (1 - θ) ^ i := by
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have := h i (by omega)
    have := ih (by omega)
    rw [pow_succ]
    nlinarith [show (0 : ℝ) ≤ 1 - θ by linarith]

/-- **The shrinker's metric is rooted**: factor `1/2`, mass `2^{−k}`. -/
theorem shrinker_rooted {lam : ℝ} (hlam : lam ≠ 0) : Rooted (RunSys.shrinker hlam).toPre := by
  have r := chain_rooted_const (f := 1 / 2) (m₀ := 1) (by norm_num) (by norm_num) zero_le_one
  have e : (fun n : ℕ => (1 : ℝ) * (1 / 2) ^ n) = fun k => shrink lam (RunSys.dyadicTime lam k) :=
    funext fun k => by rw [RunSys.shrink_dyadic hlam, one_mul]
  rw [e] at r
  exact r

/-! ## 7. The content layer (ii): G0 is not trivial -/

/-- **Rooted systems realise every factor in `[0, 1]` and every starting mass.** -/
theorem rooted_factor_mass {f m₀ : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) (hm : 0 ≤ m₀) :
    ∃ P : Pre, Rooted P ∧ ∃ x : P.X, P.fac x = f ∧ P.mass x = m₀ :=
  ⟨_, chain_rooted_const h0 h1 hm, (0 : ℕ), rfl, by simp [chainPre]⟩

/-- **Not every running system is rooted**: the shrinker's curvature satisfies the law with floor `log 2`, and it is
not rooted (its mass grows; rooted masses never do). -/
theorem curvature_not_rooted {lam : ℝ} (hlam : 0 < lam) : ¬ Rooted (RunSys.curvature hlam).toPre := fun h => by
  have := h.good.2 (0 : ℕ)
  change einsteinAt lam (RunSys.dyadicTime lam (0 + 1)) ≤ einsteinAt lam (RunSys.dyadicTime lam 0)
    at this
  rw [RunSys.einstein_dyadic hlam.ne', RunSys.einstein_dyadic hlam.ne'] at this
  norm_num at this
  linarith

/-- **The rooted round.** The form layer: every rooted system is a DMP instance whose mass never increases. The
content layer: G0 carries a persisting unit of existence; the known systems are rooted; rooted systems realise every
factor and every mass; and the shrinker's curvature, a running system, is not rooted. -/
theorem rooted_round :
    (∀ P : Pre, Rooted P → P.IsInstance ∧ ∀ x, P.mass (P.step x) ≤ P.mass x) ∧
    (∀ n, tick.mass (tick.step^[n] p0) = 1) ∧
    (∀ f m₀ : ℝ, 0 ≤ f → f ≤ 1 → 0 ≤ m₀ → ∃ P : Pre, Rooted P ∧ ∃ x : P.X, P.fac x = f ∧ P.mass x = m₀) ∧
    (∀ lam : ℝ, ∀ hlam : 0 < lam, ¬ Rooted (RunSys.curvature hlam).toPre) :=
  ⟨fun _ h => h.good, fun n => (tick_persists n).1, fun _ _ h0 h1 hm => rooted_factor_mass h0 h1 hm,
    fun _ hlam => curvature_not_rooted hlam⟩

end ProofPhase.ETM
