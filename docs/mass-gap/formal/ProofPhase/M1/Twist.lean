/-
Proof phase, M1 tools (m1-tools): the twisted blocking (Z2 label field plus a smooth part averaged by Balaban's rule),
its algebra, and the transfer of reflection positivity to a blocked law (2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/m1-tools/TWIST.md`.
-/

import Mathlib

/-!
# The twisted blocking

**Setting (abstract).** Fine bonds `ι` with endpoints `src, tgt : ι → V`, coarse bonds `κ` with endpoints
`csrc, ctgt : κ → W`, and the coarse sites embedded as fine sites (block centres) `emb : W → V`. A block average
`M : (ι → G) → (κ → G)` (Balaban's (0.4) in M1) and the straight-path decimation `Dec : (ι → G) → (κ → G)` of
label fields (the product of the labels along the straight fine path of each coarse bond).

**The twisted blocking** of a configuration `U` with label field `λ` (values central, in M1 `±1`):
`twistBlock M Dec λ U c = Dec λ c * M (λ • U) c`, where `(λ • U) b = λ b * U b` is the label-corrected (smooth)
field; the next label field is `Dec λ`.

* **`twistBlock_one`**: with trivial labels it is `M` (small fields: no labels are ever created there).
* **`twistBlock_pureGauge`**: if the labels are a pure Z2 gauge (`λ b = w (src b) * w (tgt b)`, `w` central with
  `w² = 1`), the twisted blocking equals `M`. So only the gauge-invariant Z2 content of `λ` matters (the "twist").
* **`twistBlock_gauge`**: covariance under every gauge transformation, given covariance of `M` and central labels.
* **`twistBlock_sym`**: commutes with a lattice symmetry (in particular a link reflection) whenever `M` and `Dec` do.
* **`twistBlock_local`**: a coarse bond of the twisted blocking reads only the fine bonds that `M` and `Dec` read.
* **`rp_map`**: reflection positivity passes to a pushforward by any measurable map that commutes with the reflections
  and maps "positive-half" observables to positive-half observables. With the two previous items this is the link
  reflection positivity of every twisted-blocked layer (`TWIST.md` 3), once the label creation rule has the same two
  properties (paper).

**Claim level.** All proved; only the standard axioms (`axioms.log`). That Balaban's average and the decimation satisfy the
hypotheses (covariance, symmetry, locality) is the paper statement of `TWIST.md` 1 and 3.
-/

open MeasureTheory

noncomputable section

namespace ProofPhase.M1

variable {G : Type*} [Group G] {ι κ : Type*}

/-- Label-corrected field. -/
def lmul (lam U : ι → G) : ι → G := fun b => lam b * U b

/-- **The twisted blocking.** -/
def twistBlock (M Dec : (ι → G) → (κ → G)) (lam U : ι → G) : κ → G :=
  fun c => Dec lam c * M (lmul lam U) c

/-- Trivial labels: the twisted blocking is `M`. -/
theorem twistBlock_one (M Dec : (ι → G) → (κ → G)) (hDec : Dec (fun _ => 1) = fun _ => 1) (U : ι → G) :
    twistBlock M Dec (fun _ => 1) U = M U := by
  have h1 : lmul (fun _ => (1 : G)) U = U := by funext b; simp [lmul]
  funext c
  simp [twistBlock, h1, hDec]

/-- **Pure-gauge labels change nothing.** If `λ b = w (src b) * w (tgt b)` with `w` central and `w² = 1`, `M` is
covariant under central gauge transformations, and `Dec` maps such a label field to the coarse one built from
`w ∘ emb`, then the twisted blocking is `M`. -/
theorem twistBlock_pureGauge {V W : Type*} (src tgt : ι → V) (csrc ctgt : κ → W) (emb : W → V)
    (M Dec : (ι → G) → (κ → G)) (w : V → G) (hwc : ∀ v g, w v * g = g * w v) (hw2 : ∀ v, w v * w v = 1)
    (hM : ∀ U : ι → G, M (fun b => w (src b) * U b * (w (tgt b))⁻¹)
      = fun c => w (emb (csrc c)) * M U c * (w (emb (ctgt c)))⁻¹)
    (hDec : Dec (fun b => w (src b) * w (tgt b)) = fun c => w (emb (csrc c)) * w (emb (ctgt c)))
    (U : ι → G) :
    twistBlock M Dec (fun b => w (src b) * w (tgt b)) U = M U := by
  have hinv : ∀ v, (w v)⁻¹ = w v := fun v => inv_eq_of_mul_eq_one_right (hw2 v)
  have hl : lmul (fun b => w (src b) * w (tgt b)) U = fun b => w (src b) * U b * (w (tgt b))⁻¹ := by
    funext b
    simp only [lmul, hinv]
    rw [mul_assoc, hwc (tgt b) (U b), ← mul_assoc]
  have key : ∀ a b m : G, (∀ g, a * g = g * a) → (∀ g, b * g = g * b) → a * a = 1 → b * b = 1 →
      a * b * (a * m * b) = m := by
    intro a b m ha hb ha2 hb2
    calc a * b * (a * m * b) = b * a * (a * m * b) := by rw [ha b]
      _ = b * (a * a) * m * b := by simp only [mul_assoc]
      _ = b * m * b := by rw [ha2, mul_one]
      _ = m * b * b := by rw [hb m]
      _ = m := by rw [mul_assoc, hb2, mul_one]
  funext c
  simp only [twistBlock, hl, hM, hDec]
  rw [hinv]
  exact key _ _ _ (hwc _) (hwc _) (hw2 _) (hw2 _)

/-- **Gauge covariance.** With central labels, a block average covariant under the gauge transformation `u` gives a
twisted blocking covariant under `u`. -/
theorem twistBlock_gauge {V W : Type*} (src tgt : ι → V) (csrc ctgt : κ → W) (emb : W → V)
    (M Dec : (ι → G) → (κ → G)) (u : V → G) (lam : ι → G) (hlc : ∀ b g, lam b * g = g * lam b)
    (hDc : ∀ c g, Dec lam c * g = g * Dec lam c)
    (hM : ∀ U : ι → G, M (fun b => u (src b) * U b * (u (tgt b))⁻¹)
      = fun c => u (emb (csrc c)) * M U c * (u (emb (ctgt c)))⁻¹) (U : ι → G) :
    twistBlock M Dec lam (fun b => u (src b) * U b * (u (tgt b))⁻¹)
      = fun c => u (emb (csrc c)) * twistBlock M Dec lam U c * (u (emb (ctgt c)))⁻¹ := by
  have hl : lmul lam (fun b => u (src b) * U b * (u (tgt b))⁻¹)
      = fun b => u (src b) * lmul lam U b * (u (tgt b))⁻¹ := by
    funext b
    simp only [lmul]
    rw [← mul_assoc, ← mul_assoc, hlc b (u (src b))]
    simp only [mul_assoc]
  funext c
  simp only [twistBlock, hl, hM]
  rw [← mul_assoc, ← mul_assoc, hDc c (u (emb (csrc c)))]
  simp only [mul_assoc]

/-- **Symmetries.** If a symmetry acts on fine and coarse configurations compatibly with pointwise products, and `M`
and `Dec` commute with it, so does the twisted blocking (labels transformed along). -/
theorem twistBlock_sym (M Dec : (ι → G) → (κ → G)) (θf : (ι → G) → (ι → G)) (θc : (κ → G) → (κ → G))
    (hθf : ∀ lam U, θf (lmul lam U) = lmul (θf lam) (θf U))
    (hθc : ∀ A B : κ → G, θc (fun c => A c * B c) = fun c => θc A c * θc B c)
    (hM : ∀ U, M (θf U) = θc (M U)) (hDec : ∀ lam, Dec (θf lam) = θc (Dec lam)) (lam U : ι → G) :
    twistBlock M Dec (θf lam) (θf U) = θc (twistBlock M Dec lam U) := by
  funext c
  simp only [twistBlock, ← hθf, hM, hDec]
  exact (congrFun (hθc (Dec lam) (M (lmul lam U))) c).symm

/-- **Locality.** If `M c` and `Dec c` read only the fine bonds in `R c`, so does the twisted blocking (as a
function of the pair `(λ, U)`). -/
theorem twistBlock_local (M Dec : (ι → G) → (κ → G)) (R : κ → Set ι)
    (hM : ∀ U U' c, (∀ b ∈ R c, U b = U' b) → M U c = M U' c)
    (hDec : ∀ lam lam' c, (∀ b ∈ R c, lam b = lam' b) → Dec lam c = Dec lam' c)
    (lam lam' U U' : ι → G) (c : κ) (hl : ∀ b ∈ R c, lam b = lam' b) (hU : ∀ b ∈ R c, U b = U' b) :
    twistBlock M Dec lam U c = twistBlock M Dec lam' U' c := by
  simp only [twistBlock]
  rw [hDec lam lam' c hl, hM (lmul lam U) (lmul lam' U') c (fun b hb => by simp [lmul, hl b hb, hU b hb])]

/-- **Reflection positivity passes to blocked laws.** `μ` reflection positive for `Θα` on the observables `Pα`; `B`
measurable, commuting with the reflections, and mapping `Pβ`-observables to `Pα`-observables: then `μ.map B` is
reflection positive for `Θβ` on `Pβ` (measurable observables). -/
theorem rp_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (Θα : α → α) (Θβ : β → β)
    (B : α → β) (hB : Measurable B) (hΘβ : Measurable Θβ) (hcomm : ∀ x, B (Θα x) = Θβ (B x))
    (Pα : (α → ℝ) → Prop) (Pβ : (β → ℝ) → Prop) (hhalf : ∀ F, Pβ F → Pα (F ∘ B))
    (hRP : ∀ G, Pα G → 0 ≤ ∫ x, G x * G (Θα x) ∂μ) (F : β → ℝ) (hF : Pβ F) (hFm : StronglyMeasurable F) :
    0 ≤ ∫ y, F y * F (Θβ y) ∂(μ.map B) := by
  have hm : AEStronglyMeasurable (fun y => F y * F (Θβ y)) (μ.map B) :=
    (hFm.mul (hFm.comp_measurable hΘβ)).aestronglyMeasurable
  rw [integral_map hB.aemeasurable hm]
  have h : (fun x => F (B x) * F (Θβ (B x))) = fun x => (F ∘ B) x * (F ∘ B) (Θα x) := by
    funext x; simp [Function.comp, hcomm]
  rw [h]
  exact hRP (F ∘ B) (hhalf F hF)

end ProofPhase.M1
