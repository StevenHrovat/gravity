/-
The Existence Turing Machine round: running systems and DMP's universal property (2026-11-23).
Released under Apache 2.0.

Paper: `docs/unified/ETM.md`.
-/

import ProofPhase.Unified.Ledger

/-!
# Running systems, and the ledger as their terminal object

**The definition (`RunSys δ`).** A running system with floor `δ` has
* states `X` (configurations of the carried positive weight) and a transfer step `step : X → X`;
* at every state, the **encoder factor** `fac x ∈ [0, 1]` of the boundary the next step crosses (reflection
  positivity is what puts it in `[0, 1]`, `Unified/Encoder.lean`);
* the **mass** `mass x ≥ 0`, the size of the positive weight carried (the certificate);
* the **ledger law** `mass (step x) ≤ e^δ · fac x · mass x`: every step pays its encoder factor, up to the floor `δ`,
  the same at every step.

**Morphisms (`Hom`).** Maps of states that commute with the step and preserve the factor and the mass. Invariant subsets
(`sub`, with the inclusion `subIncl`) and coarse-grainings by a compatible relation (`quot`, with `toQuot`) are
morphisms: subsystems and factor maps. `RunSys δ` is a category (`category`).

**The universal object (`univ δ`).** Its states are the **ledgers** (`Ledger δ`): a stream of factors in `[0, 1]` and a
stream of masses paying them, step by step. Its step is the shift.

**The universal property (`univIsTerminal`).** Every running system has exactly one morphism into `univ δ`: the map
`trace` sending a state to its ledger (`trace_unique`). So every running system factors through the ledger, uniquely.

**Vacuity check.**
* `univ δ` is not a point: it realises every factor stream (`univ_fac_stream`) and every starting mass
  (`univ_mass`); two states with different factors are different (`univ_nontrivial`).
* Morphisms that forget the factor and the mass would make the one-point system terminal (`bare_point_terminal`);
  with them, the one-point system is not terminal (`no_hom_to_point`).
* The floor is content: for `δ < δ'` some `δ'`-ledger is no `δ`-ledger (`floor_strict`).
* The theorems of the ledger are proved once on `univ` and pulled back along `trace`: `RunSys.carry`,
  `RunSys.contract`, `RunSys.decay_cost` are literally the universal statements at the traced point.

**Subsets.** Every running system establishes itself as a subset of `univ δ`: `trace` factors as a surjective morphism
onto the invariant subset `image S` followed by its inclusion (`toImage_surjective`, `subIncl_injective`,
`establishes_subset`). Two states have the same trace exactly when their factor and mass streams agree
(`trace_eq_iff`).

No axioms beyond the standard ones; nothing is assumed.
-/

open Finset CategoryTheory

noncomputable section

namespace ProofPhase.ETM

universe u v w

/-! ## 1. Ledgers -/

/-- **A ledger** with floor `δ`: a stream of encoder factors in `[0, 1]` and a stream of masses that pays it. -/
@[ext]
structure Ledger (δ : ℝ) where
  /-- The factor of step `n`. -/
  f : ℕ → ℝ
  /-- The mass before step `n`. -/
  m : ℕ → ℝ
  f_nonneg : ∀ n, 0 ≤ f n
  f_le_one : ∀ n, f n ≤ 1
  m_nonneg : ∀ n, 0 ≤ m n
  /-- Each step pays its factor up to the floor. -/
  pays : ∀ n, m (n + 1) ≤ Real.exp δ * f n * m n

namespace Ledger

variable {δ : ℝ}

/-- The ledger one step later. -/
def shift (L : Ledger δ) : Ledger δ :=
  ⟨fun n => L.f (n + 1), fun n => L.m (n + 1), fun _ => L.f_nonneg _, fun _ => L.f_le_one _, fun _ => L.m_nonneg _,
    fun _ => L.pays _⟩

/-- **The ledger theorem on a ledger**: `m n ≤ (∏_{i<n} e^δ f i) · m 0` (from `ProofPhase.Unified.carry`). -/
theorem carry (L : Ledger δ) (n : ℕ) : L.m n ≤ (∏ i ∈ range n, Real.exp δ * L.f i) * L.m 0 :=
  ProofPhase.Unified.carry (Cert := fun i e => L.m i ≤ e) (f := fun i => Real.exp δ * L.f i) (n := n)
    (fun i _ _ he => (L.pays i).trans
      (mul_le_mul_of_nonneg_left he (mul_nonneg (Real.exp_pos δ).le (L.f_nonneg i)))) (le_refl (L.m 0))

/-- **Contraction**: factors at most `θ` give `m n ≤ (e^δ θ)^n · m 0`. -/
theorem contract (L : Ledger δ) {θ : ℝ} (hθ : ∀ n, L.f n ≤ θ) (n : ℕ) :
    L.m n ≤ (Real.exp δ * θ) ^ n * L.m 0 := by
  refine (L.carry n).trans (mul_le_mul_of_nonneg_right ?_ (L.m_nonneg 0))
  have := prod_le_prod₀ (s := range n) (f := fun i => Real.exp δ * L.f i) (g := fun _ => Real.exp δ * θ)
    (fun i _ => mul_nonneg (Real.exp_pos δ).le (L.f_nonneg i))
    (fun i _ => mul_le_mul_of_nonneg_left (hθ i) (Real.exp_pos δ).le)
  rwa [prod_const, card_range] at this

/-- **Costs and floor**: with positive factors, `m n ≤ e^{n δ − Σ c} m 0`, `c i = −log f i`. -/
theorem decay_cost (L : Ledger δ) (hf : ∀ n, 0 < L.f n) (n : ℕ) :
    L.m n ≤ Real.exp (n * δ - ∑ i ∈ range n, -Real.log (L.f i)) * L.m 0 := by
  have h := L.carry n
  have e : (∏ i ∈ range n, Real.exp δ * L.f i) = Real.exp (n * δ - ∑ i ∈ range n, -Real.log (L.f i)) := by
    rw [← ProofPhase.Unified.prod_exp_cost]
    exact prod_congr rfl fun i _ => by rw [sub_neg_eq_add, Real.exp_add, Real.exp_log (hf i)]
  rwa [e] at h

end Ledger

/-! ## 2. Running systems and their morphisms -/

/-- **A running system** with floor `δ`: a transfer step on states carrying a positive weight, an encoder factor in
`[0, 1]` at every state, and the ledger law `mass (step x) ≤ e^δ · fac x · mass x`. -/
structure RunSys (δ : ℝ) where
  /-- The states: configurations of the carried positive weight. -/
  X : Type u
  /-- The transfer step. -/
  step : X → X
  /-- The encoder factor of the boundary the next step crosses. -/
  fac : X → ℝ
  /-- The size of the positive weight carried (the certificate). -/
  mass : X → ℝ
  fac_nonneg : ∀ x, 0 ≤ fac x
  fac_le_one : ∀ x, fac x ≤ 1
  mass_nonneg : ∀ x, 0 ≤ mass x
  /-- The ledger law: every step pays its encoder factor, up to the floor. -/
  pays : ∀ x, mass (step x) ≤ Real.exp δ * fac x * mass x

namespace RunSys

variable {δ : ℝ}

/-- **A morphism of running systems**: commutes with the step, preserves the encoder factor and the mass. -/
@[ext]
structure Hom (S : RunSys.{u} δ) (T : RunSys.{v} δ) where
  /-- The map of states. -/
  toFun : S.X → T.X
  step_comm : ∀ x, toFun (S.step x) = T.step (toFun x)
  fac_eq : ∀ x, T.fac (toFun x) = S.fac x
  mass_eq : ∀ x, T.mass (toFun x) = S.mass x

/-- The identity morphism. -/
def Hom.id (S : RunSys.{u} δ) : Hom S S := ⟨fun x => x, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- Composition. -/
def Hom.comp {S : RunSys.{u} δ} {T : RunSys.{v} δ} {R : RunSys.{w} δ} (g : Hom T R) (f : Hom S T) : Hom S R where
  toFun x := g.toFun (f.toFun x)
  step_comm x := by rw [f.step_comm, g.step_comm]
  fac_eq x := by rw [g.fac_eq, f.fac_eq]
  mass_eq x := by rw [g.mass_eq, f.mass_eq]

/-- **Running systems form a category.** -/
instance category : Category.{u} (RunSys.{u} δ) where
  Hom S T := RunSys.Hom S T
  id S := Hom.id S
  comp f g := Hom.comp g f
  id_comp _ := Hom.ext rfl
  comp_id _ := Hom.ext rfl
  assoc _ _ _ := Hom.ext rfl

/-- A morphism commutes with every iterate of the step. -/
theorem Hom.iterate_comm {S : RunSys.{u} δ} {T : RunSys.{v} δ} (f : Hom S T) (n : ℕ) (x : S.X) :
    f.toFun (S.step^[n] x) = T.step^[n] (f.toFun x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    show f.toFun (S.step^[n] (S.step x)) = T.step^[n] (T.step (f.toFun x))
    rw [ih, f.step_comm]

/-! ## 3. The universal object: the space of ledgers -/

/-- **The universal running system**: states are ledgers, the step is the shift, the factor and the mass are read at
step `0`. -/
def univ (δ : ℝ) : RunSys.{u} δ where
  X := ULift.{u} (Ledger δ)
  step L := ⟨L.down.shift⟩
  fac L := L.down.f 0
  mass L := L.down.m 0
  fac_nonneg L := L.down.f_nonneg 0
  fac_le_one L := L.down.f_le_one 0
  mass_nonneg L := L.down.m_nonneg 0
  pays L := L.down.pays 0

/-- **The ledger of a state**: its factor and mass streams along the run. -/
def ledger (S : RunSys.{u} δ) (x : S.X) : Ledger δ where
  f n := S.fac (S.step^[n] x)
  m n := S.mass (S.step^[n] x)
  f_nonneg _ := S.fac_nonneg _
  f_le_one _ := S.fac_le_one _
  m_nonneg _ := S.mass_nonneg _
  pays n := by
    show S.mass (S.step^[n + 1] x) ≤ _
    rw [Function.iterate_succ_apply']
    exact S.pays _

theorem ledger_step (S : RunSys.{u} δ) (x : S.X) : S.ledger (S.step x) = (S.ledger x).shift :=
  Ledger.ext rfl rfl

/-- **The trace**: the morphism sending each state to its ledger. -/
def trace (S : RunSys.{u} δ) : Hom S (univ.{v} δ) where
  toFun x := ⟨S.ledger x⟩
  step_comm x := congrArg ULift.up (S.ledger_step x)
  fac_eq _ := rfl
  mass_eq _ := rfl

/-- Any morphism into the universal object sends a state to its ledger. -/
theorem hom_univ_ledger {S : RunSys.{u} δ} (φ : Hom S (univ.{v} δ)) (x : S.X) : (φ.toFun x).down = S.ledger x := by
  have key : ∀ n x, (φ.toFun x).down.f n = S.fac (S.step^[n] x) ∧ (φ.toFun x).down.m n = S.mass (S.step^[n] x) := by
    intro n
    induction n with
    | zero => intro x; exact ⟨φ.fac_eq x, φ.mass_eq x⟩
    | succ n ih =>
      intro x
      have e : (φ.toFun x).down.shift = (φ.toFun (S.step x)).down := by rw [φ.step_comm]; rfl
      obtain ⟨h1, h2⟩ := ih (S.step x)
      refine ⟨?_, ?_⟩
      · show (φ.toFun x).down.shift.f n = _
        rw [e]; exact h1
      · show (φ.toFun x).down.shift.m n = _
        rw [e]; exact h2
  exact Ledger.ext (funext fun n => (key n x).1) (funext fun n => (key n x).2)

/-- **Uniqueness**: the trace is the only morphism into the universal object. -/
theorem trace_unique {S : RunSys.{u} δ} (φ : Hom S (univ.{v} δ)) : φ = S.trace :=
  Hom.ext (funext fun x => congrArg ULift.up (hom_univ_ledger φ x))

/-- **The universal property, existence and uniqueness**: every running system factors through the ledger,
uniquely. -/
theorem exists_unique_hom (S : RunSys.{u} δ) : ∃! _ : Hom S (univ.{v} δ), True :=
  ⟨S.trace, trivial, fun φ _ => trace_unique φ⟩

/-- **DMP's universal property**: the space of ledgers is the terminal running system. -/
def univIsTerminal : Limits.IsTerminal (univ.{u} δ) :=
  Limits.IsTerminal.ofUniqueHom (fun S => trace S) (fun _ φ => trace_unique φ)

/-- The universal object traces itself by the identity. -/
theorem univ_trace : (univ.{u} δ).trace = Hom.id (univ.{u} δ) := (trace_unique (Hom.id _)).symm

/-! ## 4. The ledger theorems, proved once on `univ` and pulled back along the trace -/

/-- **The ledger theorem on any running system**: the universal statement `Ledger.carry` at the traced point. -/
theorem carry (S : RunSys.{u} δ) (x : S.X) (n : ℕ) :
    S.mass (S.step^[n] x) ≤ (∏ i ∈ range n, Real.exp δ * S.fac (S.step^[i] x)) * S.mass x :=
  ((S.trace : Hom S (univ.{u} δ)).toFun x).down.carry n

/-- **Contraction on any running system**, pulled back from `Ledger.contract`. -/
theorem contract (S : RunSys.{u} δ) {θ : ℝ} (hθ : ∀ x, S.fac x ≤ θ) (x : S.X) (n : ℕ) :
    S.mass (S.step^[n] x) ≤ (Real.exp δ * θ) ^ n * S.mass x :=
  ((S.trace : Hom S (univ.{u} δ)).toFun x).down.contract (fun _ => hθ _) n

/-- **Costs and floor on any running system**, pulled back from `Ledger.decay_cost`. -/
theorem decay_cost (S : RunSys.{u} δ) (hf : ∀ x, 0 < S.fac x) (x : S.X) (n : ℕ) :
    S.mass (S.step^[n] x) ≤
      Real.exp (n * δ - ∑ i ∈ range n, -Real.log (S.fac (S.step^[i] x))) * S.mass x :=
  ((S.trace : Hom S (univ.{u} δ)).toFun x).down.decay_cost (fun _ => hf _) n

/-! ## 5. Vacuity check -/

/-- Along the universal object, the factor and the mass of the `n`-th state are the ledger's `n`-th entries. -/
theorem univ_iterate (L : (univ.{u} δ).X) (n : ℕ) :
    (univ.{u} δ).fac ((univ.{u} δ).step^[n] L) = L.down.f n ∧
      (univ.{u} δ).mass ((univ.{u} δ).step^[n] L) = L.down.m n := by
  have h := hom_univ_ledger (Hom.id (univ.{u} δ)) L
  exact ⟨(congrFun (congrArg Ledger.f h) n).symm, (congrFun (congrArg Ledger.m h) n).symm⟩

/-- **The universal object realises every factor stream.** -/
theorem univ_fac_stream (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hf1 : ∀ n, f n ≤ 1) :
    ∃ L : (univ.{u} δ).X, ∀ n, (univ.{u} δ).fac ((univ.{u} δ).step^[n] L) = f n :=
  ⟨⟨⟨f, fun _ => 0, hf0, hf1, fun _ => le_rfl, fun _ => by simp⟩⟩, fun n => (univ_iterate _ n).1⟩

/-- **The universal object realises every starting mass**, with a lossless factor stream (`f = 1`) paying exactly the
floor. -/
theorem univ_mass (m₀ : ℝ) (hm : 0 ≤ m₀) : ∃ L : (univ.{u} δ).X, (univ.{u} δ).mass L = m₀ ∧
    ∀ n, (univ.{u} δ).fac ((univ.{u} δ).step^[n] L) = 1 := by
  refine ⟨⟨⟨fun _ => 1, fun n => Real.exp (n * δ) * m₀, fun _ => zero_le_one, fun _ => le_rfl,
    fun n => mul_nonneg (Real.exp_pos _).le hm, fun n => ?_⟩⟩, by simp [univ], fun n => (univ_iterate _ n).1⟩
  show Real.exp (((n + 1 : ℕ) : ℝ) * δ) * m₀ ≤ Real.exp δ * 1 * (Real.exp (n * δ) * m₀)
  have e : ((n + 1 : ℕ) : ℝ) * δ = δ + n * δ := by push_cast; ring
  refine le_of_eq ?_
  rw [mul_one, ← mul_assoc, ← Real.exp_add, e]

/-- **The universal object is not a point**: it has states with different factors. -/
theorem univ_nontrivial : ∃ a b : (univ.{u} δ).X, (univ.{u} δ).fac a ≠ (univ.{u} δ).fac b :=
  ⟨⟨⟨fun _ => 0, fun _ => 0, fun _ => le_rfl, fun _ => zero_le_one, fun _ => le_rfl, fun _ => by simp⟩⟩,
    ⟨⟨fun _ => 1, fun _ => 0, fun _ => zero_le_one, fun _ => le_rfl, fun _ => le_rfl, fun _ => by simp⟩⟩,
    by simp [univ]⟩

/-- The one-point running system with factor `0` and mass `0`. -/
def point (δ : ℝ) : RunSys.{u} δ where
  X := PUnit
  step := id
  fac _ := 0
  mass _ := 0
  fac_nonneg _ := le_rfl
  fac_le_one _ := zero_le_one
  mass_nonneg _ := le_rfl
  pays _ := by simp

/-- **Without the factor and the mass, the point would be terminal**: every step map has exactly one
step-commuting map to the one-point system. -/
theorem bare_point_terminal (X : Type u) (step : X → X) :
    ∃! g : X → PUnit.{v + 1}, ∀ x, g (step x) = g x :=
  ⟨fun _ => PUnit.unit, fun _ => rfl, fun _ _ => funext fun _ => rfl⟩

/-- **With them, it is not**: a system with a state of positive factor or positive mass has no morphism to the point
(any point system with constant factor and mass, here `0`). -/
theorem no_hom_to_point (S : RunSys.{u} δ) (x : S.X) (hx : S.fac x ≠ 0 ∨ S.mass x ≠ 0) :
    IsEmpty (Hom S (point.{v} δ)) :=
  ⟨fun φ => hx.elim (fun h => h (φ.fac_eq x).symm) (fun h => h (φ.mass_eq x).symm)⟩

/-- **Raising the floor**: a running system with floor `δ` is one with any floor `δ' ≥ δ`. -/
def relax (S : RunSys.{u} δ) {δ' : ℝ} (h : δ ≤ δ') : RunSys.{u} δ' where
  X := S.X
  step := S.step
  fac := S.fac
  mass := S.mass
  fac_nonneg := S.fac_nonneg
  fac_le_one := S.fac_le_one
  mass_nonneg := S.mass_nonneg
  pays x := (S.pays x).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h) (S.fac_nonneg x)) (S.mass_nonneg x))

/-- **The floor is content**: for `δ < δ'` the lossless ledger growing at `e^{δ'}` per step is a `δ'`-ledger and
no `δ`-ledger. -/
theorem floor_strict {δ' : ℝ} (h : δ < δ') :
    (∃ L : Ledger δ', L.f = (fun _ => 1) ∧ L.m = fun n : ℕ => Real.exp (n * δ')) ∧
    ¬ ∃ L : Ledger δ, L.f = (fun _ => 1) ∧ L.m = fun n : ℕ => Real.exp (n * δ') := by
  refine ⟨⟨⟨fun _ => 1, fun n => Real.exp (n * δ'), fun _ => zero_le_one, fun _ => le_rfl,
    fun _ => (Real.exp_pos _).le, fun n => ?_⟩, rfl, rfl⟩, ?_⟩
  · show Real.exp (((n + 1 : ℕ) : ℝ) * δ') ≤ Real.exp δ' * 1 * Real.exp (n * δ')
    have e : ((n + 1 : ℕ) : ℝ) * δ' = δ' + n * δ' := by push_cast; ring
    refine le_of_eq ?_
    rw [mul_one, ← Real.exp_add, e]
  · rintro ⟨L, hf, hm⟩
    have := L.pays 0
    rw [hf, hm] at this
    have h2 : Real.exp δ' ≤ Real.exp δ := by simpa using this
    linarith [Real.exp_le_exp.1 h2]

/-! ## 6. Subsets and factor maps -/

/-- **A subsystem**: an invariant subset of states. -/
def sub (S : RunSys.{u} δ) (P : S.X → Prop) (hP : ∀ x, P x → P (S.step x)) : RunSys.{u} δ where
  X := {x // P x}
  step x := ⟨S.step x.1, hP _ x.2⟩
  fac x := S.fac x.1
  mass x := S.mass x.1
  fac_nonneg x := S.fac_nonneg x.1
  fac_le_one x := S.fac_le_one x.1
  mass_nonneg x := S.mass_nonneg x.1
  pays x := S.pays x.1

/-- The inclusion of a subsystem. -/
def subIncl (S : RunSys.{u} δ) (P : S.X → Prop) (hP : ∀ x, P x → P (S.step x)) : Hom (S.sub P hP) S :=
  ⟨Subtype.val, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem subIncl_injective (S : RunSys.{u} δ) (P : S.X → Prop) (hP : ∀ x, P x → P (S.step x)) :
    Function.Injective (S.subIncl P hP).toFun := Subtype.val_injective

/-- **A factor map (coarse-graining)**: the quotient by a relation compatible with the step, the factor and the mass. -/
def quot (S : RunSys.{u} δ) (R : S.X → S.X → Prop) (hs : ∀ x y, R x y → R (S.step x) (S.step y))
    (hf : ∀ x y, R x y → S.fac x = S.fac y) (hm : ∀ x y, R x y → S.mass x = S.mass y) : RunSys.{u} δ where
  X := Quot R
  step := Quot.map S.step hs
  fac := Quot.lift S.fac hf
  mass := Quot.lift S.mass hm
  fac_nonneg := Quot.ind S.fac_nonneg
  fac_le_one := Quot.ind S.fac_le_one
  mass_nonneg := Quot.ind S.mass_nonneg
  pays := Quot.ind S.pays

/-- The quotient map is a morphism. -/
def toQuot (S : RunSys.{u} δ) (R : S.X → S.X → Prop) (hs : ∀ x y, R x y → R (S.step x) (S.step y))
    (hf : ∀ x y, R x y → S.fac x = S.fac y) (hm : ∀ x y, R x y → S.mass x = S.mass y) : Hom S (S.quot R hs hf hm) :=
  ⟨Quot.mk R, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem toQuot_surjective (S : RunSys.{u} δ) (R : S.X → S.X → Prop) (hs : ∀ x y, R x y → R (S.step x) (S.step y))
    (hf : ∀ x y, R x y → S.fac x = S.fac y) (hm : ∀ x y, R x y → S.mass x = S.mass y) :
    Function.Surjective (S.toQuot R hs hf hm).toFun := Quot.exists_rep

/-- **The subset a running system establishes in the universal object**: the image of its trace, an invariant
subset. -/
def image (S : RunSys.{u} δ) : RunSys.{u} δ :=
  (univ.{u} δ).sub (fun L => ∃ x, (S.trace : Hom S (univ.{u} δ)).toFun x = L) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨S.step x, (S.trace : Hom S (univ.{u} δ)).step_comm x⟩)

/-- The corestriction of the trace onto its image. -/
def toImage (S : RunSys.{u} δ) : Hom S S.image where
  toFun x := ⟨(S.trace : Hom S (univ.{u} δ)).toFun x, x, rfl⟩
  step_comm x := Subtype.ext ((S.trace : Hom S (univ.{u} δ)).step_comm x)
  fac_eq _ := rfl
  mass_eq _ := rfl

theorem toImage_surjective (S : RunSys.{u} δ) : Function.Surjective S.toImage.toFun := by
  rintro ⟨_, x, rfl⟩
  exact ⟨x, rfl⟩

/-- **Every running system establishes itself as a subset of the universal object**: its trace is a surjective
morphism onto an invariant subset followed by the (injective) inclusion. -/
theorem establishes_subset (S : RunSys.{u} δ) :
    Hom.comp ((univ.{u} δ).subIncl _ _) S.toImage = (S.trace : Hom S (univ.{u} δ)) := Hom.ext rfl

/-- **Two states have the same trace exactly when their factor and mass streams agree.** -/
theorem trace_eq_iff (S : RunSys.{u} δ) (x y : S.X) :
    (S.trace : Hom S (univ.{v} δ)).toFun x = (S.trace : Hom S (univ.{v} δ)).toFun y ↔
      ∀ n, S.fac (S.step^[n] x) = S.fac (S.step^[n] y) ∧ S.mass (S.step^[n] x) = S.mass (S.step^[n] y) := by
  constructor
  · intro h n
    have h' := congrArg ULift.down h
    exact ⟨congrFun (congrArg Ledger.f h') n, congrFun (congrArg Ledger.m h') n⟩
  · intro h
    exact congrArg ULift.up (Ledger.ext (funext fun n => (h n).1) (funext fun n => (h n).2))

end RunSys

end ProofPhase.ETM
