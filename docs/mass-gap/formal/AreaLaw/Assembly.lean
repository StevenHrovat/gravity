/-
The assembly of the strong-coupling area law (BLUEPRINT.md, P7 and P9). Area-law project, 2026-11-21. Released under Apache 2.0.

# Part 1 (abstract)

A finite graph `H` of maximum degree `≤ Δ`, a root set `R`, and functions `I IC : Finset V → ℝ` with `I ∅ = 1`, the
factorisations `I (X ∪ Y) = I X * I Y`, `IC (X ∪ Y) = IC X * I Y` for non-touching `X`, `Y` (with `Y` off `R` for `IC`), the
bounds `|I X| ≤ ε ^ |X|`, `|IC X| ≤ M ε ^ |X|`, and `IC X = 0` unless `A ≤ |X|`. Then (`area_bound_abstract`)

  |∑_X IC X / ∑_X I X| ≤ M · e^{2|R|} · (√(e^{Δ+1} ε))^A   for 0 ≤ ε ≤ 1 / (4 e^{Δ+1} (Δ+1)^4).

Route: `sum_avoid_eq_XiAvoid` (the sum of `I` over the sets avoiding `T` is the polymer gas `XiAvoid` of the connected
polymers with `touch` incompatibility: decomposition into connected components); `sum_IC_eq` (split `X` into the part
joined to `R` inside `X` and the rest); `cluster_ratio_touch_explicit` (P8) for the ratios; the rooted-set count.

# Part 2 (lattice)

`wilson_area_law`: plaquettes, "share a link", `R` = plaquettes containing a link of the loop, `I = Iint`, `IC = ICint`,
under a minimal-area hypothesis `hArea`; `wilson_area_law_rect`: the rectangle, with `rect_parity_area` (P5) in place of `hArea`.

The section `Rooted` restates, unchanged up to names, the definitions and lemmas of
`Balaban/Polymer/RootedAnimals.lean` (scottnarmstrong/balaban-lean, Apache 2.0) that are used here: that file's `.olean`
is not built in this workspace, so it cannot be imported.
-/

import AreaLaw.ClusterRatio
import AreaLaw.Integrals
import AreaLaw.MinArea

open scoped Classical

open Finset SimpleGraph Balaban.Polymer AreaLaw.ClusterRatio

set_option linter.unusedSectionVars false

noncomputable section

namespace AreaLaw.Assembly

/-! ## Rooted sets (restated from `Balaban.Polymer.RootedAnimals`) -/

section Rooted

variable {V : Type*} (G : SimpleGraph V)

/-- The vertex `v` is joined to `w` by a walk of `G` all of whose vertices lie in `C`. -/
def WalkIn (C : Finset V) (v w : V) : Prop :=
  ∃ p : G.Walk v w, ∀ x ∈ p.support, x ∈ C

/-- `C` is rooted at `N`: every vertex of `C` is joined, by a walk inside `C`, to a vertex of `N`. -/
def Rooted (N : Set V) (C : Finset V) : Prop :=
  ∀ v ∈ C, ∃ w ∈ N, WalkIn G C v w

variable {G}

theorem WalkIn.trans {C : Finset V} {u v w : V} (h₁ : WalkIn G C u v) (h₂ : WalkIn G C v w) :
    WalkIn G C u w := by
  obtain ⟨p, hp⟩ := h₁
  obtain ⟨q, hq⟩ := h₂
  refine ⟨p.append q, fun x hx => ?_⟩
  rw [Walk.mem_support_append_iff] at hx
  exact hx.elim (hp x) (hq x)

theorem WalkIn.refl {C : Finset V} {v : V} (hv : v ∈ C) : WalkIn G C v v :=
  ⟨Walk.nil, by simpa using hv⟩

theorem WalkIn.of_mem_support {C : Finset V} {v w x : V} (p : G.Walk v w)
    (hp : ∀ y ∈ p.support, y ∈ C) (hx : x ∈ p.support) : WalkIn G C v x :=
  ⟨p.takeUntil x hx, fun y hy => hp y (p.support_takeUntil_subset_support hx hy)⟩

theorem WalkIn.of_mem_support' {C : Finset V} {v w x : V} (p : G.Walk v w)
    (hp : ∀ y ∈ p.support, y ∈ C) (hx : x ∈ p.support) : WalkIn G C x w :=
  ⟨p.dropUntil x hx, fun y hy => hp y (p.support_dropUntil_subset_support hx hy)⟩

theorem WalkIn.mem_right {C : Finset V} {v w : V} (h : WalkIn G C v w) : w ∈ C := by
  obtain ⟨p, hp⟩ := h
  exact hp w p.end_mem_support

theorem WalkIn.mem_left {C : Finset V} {v w : V} (h : WalkIn G C v w) : v ∈ C := by
  obtain ⟨p, hp⟩ := h
  exact hp v p.start_mem_support

theorem Rooted.eq_empty_of_empty {C : Finset V} (hC : Rooted G (∅ : Set V) C) : C = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun v hv => ?_
  obtain ⟨w, hw, -⟩ := hC v hv
  exact hw

/-- The part of `C` joined inside `C` to a vertex of `N₁`. -/
def splitOff (N₁ : Set V) (C : Finset V) : Finset V :=
  C.filter fun v => ∃ w ∈ N₁, WalkIn G C v w

theorem splitOff_subset (N₁ : Set V) (C : Finset V) : splitOff (G := G) N₁ C ⊆ C :=
  Finset.filter_subset _ _

theorem rooted_splitOff {N₁ N' : Set V} {C : Finset V} (_hC : Rooted G (N₁ ∪ N') C) :
    Rooted G N₁ (splitOff (G := G) N₁ C) := by
  intro v hv
  simp only [splitOff, Finset.mem_filter] at hv
  obtain ⟨hvC, w, hw, p, hp⟩ := hv
  refine ⟨w, hw, p, fun x hx => ?_⟩
  simp only [splitOff, Finset.mem_filter]
  exact ⟨hp x hx, w, hw, WalkIn.of_mem_support' p hp hx⟩

theorem rooted_sdiff_splitOff {N₁ N' : Set V} {C : Finset V} (hC : Rooted G (N₁ ∪ N') C) :
    Rooted G N' (C \ splitOff (G := G) N₁ C) := by
  intro v hv
  rw [Finset.mem_sdiff] at hv
  obtain ⟨hvC, hvs⟩ := hv
  obtain ⟨w, hw, p, hp⟩ := hC v hvC
  have hnot : ∀ x ∈ p.support, x ∉ splitOff (G := G) N₁ C := by
    intro x hx hxs
    simp only [splitOff, Finset.mem_filter] at hxs
    obtain ⟨-, w', hw', hxw'⟩ := hxs
    apply hvs
    simp only [splitOff, Finset.mem_filter]
    exact ⟨hvC, w', hw', (WalkIn.of_mem_support p hp hx).trans hxw'⟩
  have hwN' : w ∈ N' := by
    rcases hw with hw | hw
    · exact absurd (by
        simp only [splitOff, Finset.mem_filter]
        exact ⟨hvC, w, hw, p, hp⟩) hvs
    · exact hw
  exact ⟨w, hwN', p, fun x hx => Finset.mem_sdiff.2 ⟨hp x hx, hnot x hx⟩⟩

theorem splitOff_union_sdiff (N₁ : Set V) (C : Finset V) :
    splitOff (G := G) N₁ C ∪ (C \ splitOff (G := G) N₁ C) = C :=
  Finset.union_sdiff_of_subset (splitOff_subset N₁ C)

theorem card_splitOff_add (N₁ : Set V) (C : Finset V) :
    (splitOff (G := G) N₁ C).card + (C \ splitOff (G := G) N₁ C).card = C.card := by
  rw [add_comm]
  exact Finset.card_sdiff_add_card_eq_card (splitOff_subset N₁ C)

variable (G)

/-- The graph `G` with a root vertex `none` adjoined, joined to the vertices of `N`. -/
def rootGraph (N : Finset V) : SimpleGraph (Option V) where
  Adj a b :=
    match a, b with
    | some v, some w => G.Adj v w
    | none, some w => w ∈ N
    | some v, none => v ∈ N
    | none, none => False
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by
    intro a h
    cases a <;> simp_all⟩

variable {G}

variable [Fintype V]

instance (N : Finset V) : (rootGraph G N).LocallyFinite := fun _ => inferInstance

/-- The finite family of sets rooted at `N`. -/
def rootedSets (N : Set V) : Finset (Finset V) :=
  Finset.univ.filter (Rooted G N)

theorem mem_rootedSets {N : Set V} {C : Finset V} : C ∈ rootedSets (G := G) N ↔ Rooted G N C := by
  simp [rootedSets]

variable [G.LocallyFinite]

theorem degree_rootGraph_le {b b_root : ℕ} (hb : ∀ v, G.degree v ≤ b) (N : Finset V)
    (hN : N.card ≤ b_root) (a : Option V) :
    (rootGraph G N).degree a ≤ max (b + 1) b_root := by
  cases a with
  | none =>
    rw [← card_neighborFinset_eq_degree]
    refine le_trans ?_ (hN.trans (le_max_right _ _))
    calc _ ≤ (N.image some).card := by
          apply Finset.card_le_card
          intro x hx
          rw [mem_neighborFinset] at hx
          cases x with
          | none => exact absurd hx (by simp [rootGraph])
          | some w => exact Finset.mem_image.2 ⟨w, hx, rfl⟩
      _ ≤ N.card := Finset.card_image_le
  | some v =>
    rw [← card_neighborFinset_eq_degree]
    refine le_trans ?_ ((Nat.add_le_add_right (hb v) 1).trans (le_max_left _ _))
    calc _ ≤ (insert none ((G.neighborFinset v).image some)).card := by
          apply Finset.card_le_card
          intro x hx
          rw [mem_neighborFinset] at hx
          cases x with
          | none => simp
          | some w => exact Finset.mem_insert_of_mem (Finset.mem_image.2
              ⟨w, (mem_neighborFinset _ _ _).2 hx, rfl⟩)
      _ ≤ ((G.neighborFinset v).image some).card + 1 := Finset.card_insert_le _ _
      _ ≤ _ := by
          exact Nat.add_le_add_right
            (Finset.card_image_le.trans (card_neighborFinset_eq_degree G v).le) 1

omit [Fintype V] [G.LocallyFinite] in
theorem connected_insert_none (N : Finset V) {C : Finset V} (hC : Rooted G (N : Set V) C) :
    ((rootGraph G N).induce ((insert none (C.image some) : Finset (Option V)) : Set (Option V))).Connected := by
  set S : Finset (Option V) := insert none (C.image some) with hS
  have hnone : (none : Option V) ∈ S := by simp [hS]
  have hsome : ∀ {v}, v ∈ C → (some v : Option V) ∈ S := by intro v hv; simp [hS, hv]
  have lift : ∀ {v w : V} (p : G.Walk v w) (hp : ∀ x ∈ p.support, x ∈ C)
      (hv : (some v : Option V) ∈ (S : Set (Option V))) (hw : (some w : Option V) ∈ (S : Set (Option V))),
      ((rootGraph G N).induce (S : Set (Option V))).Reachable ⟨some v, hv⟩ ⟨some w, hw⟩ := by
    intro v w p
    induction p with
    | nil => intro _ hv hw; exact SimpleGraph.Reachable.refl _
    | @cons a b c h q ih =>
      intro hp hv hw
      have hb : b ∈ C := hp b (by simp)
      have hbS : (some b : Option V) ∈ (S : Set (Option V)) := hsome hb
      refine SimpleGraph.Adj.reachable (G := (rootGraph G N).induce (S : Set (Option V)))
        (u := ⟨some a, hv⟩) (v := ⟨some b, hbS⟩) h |>.trans (ih (fun x hx => hp x (by simp [hx])) hbS hw)
  have hreach : ∀ x : (S : Set (Option V)),
      ((rootGraph G N).induce (S : Set (Option V))).Reachable x ⟨none, hnone⟩ := by
    rintro ⟨x, hx⟩
    cases x with
    | none => exact SimpleGraph.Reachable.refl _
    | some v =>
      have hvC : v ∈ C := by simpa [hS] using hx
      obtain ⟨w, hw, p, hp⟩ := hC v hvC
      have hwC : w ∈ C := hp w p.end_mem_support
      have hwS := hsome hwC
      refine (lift p hp hx hwS).trans ?_
      exact SimpleGraph.Adj.reachable (G := (rootGraph G N).induce (S : Set (Option V)))
        (u := ⟨some w, hwS⟩) (v := ⟨none, hnone⟩) (by exact hw)
  have : Nonempty (S : Set (Option V)) := ⟨⟨none, hnone⟩⟩
  exact ⟨fun x y => (hreach x).trans (hreach y).symm⟩

theorem card_rooted_le {b b_root : ℕ} (hb : ∀ v, G.degree v ≤ b) (N : Finset V)
    (hN : N.card ≤ b_root) (n : ℕ) :
    ((rootedSets (G := G) (N : Set V)).filter fun C => C.card = n).card
      ≤ (max (b + 1) b_root) ^ (2 * n) := by
  have hA := card_animals_le (rootGraph G N) (degree_rootGraph_le hb N hN) none (n + 1)
  rw [Nat.add_sub_cancel] at hA
  refine le_trans ?_ hA
  refine Finset.card_le_card_of_injOn (fun C => insert none (C.image some)) (fun C hC => ?_)
    (fun C _ D _ h => ?_)
  · simp only [Finset.mem_coe, Finset.mem_filter, mem_rootedSets] at hC
    rw [Finset.mem_coe, mem_animals]
    refine ⟨by simp, ?_, connected_insert_none N hC.1⟩
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _ (Option.some_injective _),
      hC.2]
  · simp only at h
    ext v
    have := congrArg (fun S : Finset (Option V) => some v ∈ S) h
    simpa using this

theorem sum_rooted_le_one {b b_root : ℕ} (hb : ∀ v, G.degree v ≤ b) (N : Finset V)
    (hN : N.card ≤ b_root) {t : ℝ} (ht : 0 ≤ t)
    (hz : ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t < 1) :
    ∑ C ∈ rootedSets (G := G) (N : Set V), t ^ C.card
      ≤ 1 / (1 - ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t) := by
  set Δ : ℕ := max (b + 1) b_root with hΔ
  set z : ℝ := (Δ : ℝ) ^ 2 * t with hzdef
  have hz0 : 0 ≤ z := by positivity
  have hmaps : ∀ C ∈ rootedSets (G := G) (N : Set V), C.card ∈ range (Fintype.card V + 1) := by
    intro C _; rw [Finset.mem_range]; exact Nat.lt_succ_of_le (Finset.card_le_univ _)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ n ∈ range (Fintype.card V + 1),
      ∑ C ∈ (rootedSets (G := G) (N : Set V)).filter (fun C => C.card = n), t ^ C.card ≤ z ^ n := by
    intro n _
    rw [Finset.sum_congr rfl (g := fun _ => t ^ n) (fun C hC => by
      rw [(Finset.mem_filter.1 hC).2]), Finset.sum_const, nsmul_eq_mul]
    calc _ ≤ ((Δ ^ (2 * n) : ℕ) : ℝ) * t ^ n := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast card_rooted_le hb N hN n
      _ = z ^ n := by rw [hzdef, mul_pow, ← pow_mul]; push_cast; ring
  calc _ ≤ ∑ n ∈ range (Fintype.card V + 1), z ^ n := Finset.sum_le_sum hfib
    _ ≤ (1 - z)⁻¹ := sum_le_hasSum _ (fun i _ => by positivity) (hasSum_geometric_of_lt_one hz0 hz)
    _ = 1 / (1 - z) := (one_div _).symm

theorem sum_rooted_le {ι : Type*} [DecidableEq ι] {b b_root : ℕ} (hb : ∀ v, G.degree v ≤ b)
    (N : ι → Finset V) (hN : ∀ i, (N i).card ≤ b_root) {t : ℝ} (ht : 0 ≤ t)
    (hz : ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t < 1) (s : Finset ι) :
    ∑ C ∈ rootedSets (G := G) (⋃ i ∈ s, (N i : Set V)), t ^ C.card
      ≤ (1 / (1 - ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t)) ^ s.card := by
  set A : ℝ := 1 / (1 - ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t) with hA
  have hA0 : 0 ≤ A := by
    have : 0 < 1 - ((max (b + 1) b_root : ℕ) : ℝ) ^ 2 * t := by linarith
    positivity
  induction s using Finset.induction_on with
  | empty =>
    have hU : (⋃ i ∈ (∅ : Finset ι), (N i : Set V)) = ∅ := by simp
    rw [hU, Finset.card_empty, pow_zero]
    calc _ ≤ ∑ C ∈ ({∅} : Finset (Finset V)), t ^ C.card := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro C hC
            rw [mem_rootedSets] at hC
            simpa using hC.eq_empty_of_empty
          · intros; positivity
      _ = 1 := by simp
  | insert a s ha ih =>
    rw [Finset.card_insert_of_notMem ha, pow_succ']
    have hU : (⋃ i ∈ insert a s, (N i : Set V)) = (N a : Set V) ∪ ⋃ i ∈ s, (N i : Set V) := by
      rw [Finset.set_biUnion_insert]
    rw [hU]
    set R1 := rootedSets (G := G) (N a : Set V)
    set R' := rootedSets (G := G) (⋃ i ∈ s, (N i : Set V))
    set R := rootedSets (G := G) ((N a : Set V) ∪ ⋃ i ∈ s, (N i : Set V))
    let φ : Finset V → Finset V × Finset V := fun C =>
      (splitOff (G := G) (N a : Set V) C, C \ splitOff (G := G) (N a : Set V) C)
    let g : Finset V × Finset V → ℝ := fun p => t ^ p.1.card * t ^ p.2.card
    have hinj : Set.InjOn φ R := by
      intro C _ D _ h
      simp only [φ, Prod.mk.injEq] at h
      calc C = splitOff (G := G) (N a : Set V) C ∪ (C \ splitOff (G := G) (N a : Set V) C) :=
            (splitOff_union_sdiff _ _).symm
        _ = splitOff (G := G) (N a : Set V) D ∪ (D \ splitOff (G := G) (N a : Set V) D) := by
            rw [h.2, h.1]
        _ = D := splitOff_union_sdiff _ _
    have h1 : ∑ C ∈ R, t ^ C.card = ∑ C ∈ R, g (φ C) := by
      refine Finset.sum_congr rfl fun C _ => ?_
      simp only [g, φ]
      rw [← pow_add, card_splitOff_add]
    rw [h1, ← Finset.sum_image hinj]
    have hsub : R.image φ ⊆ R1 ×ˢ R' := by
      intro p hp
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hp
      rw [mem_rootedSets] at hC
      exact Finset.mem_product.2 ⟨mem_rootedSets.2 (rooted_splitOff hC),
        mem_rootedSets.2 (rooted_sdiff_splitOff hC)⟩
    calc _ ≤ ∑ p ∈ R1 ×ˢ R', g p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by simp only [g]; positivity)
      _ = (∑ C ∈ R1, t ^ C.card) * ∑ C ∈ R', t ^ C.card := by
          rw [Finset.sum_product, Finset.sum_mul_sum]
      _ ≤ A * A ^ s.card :=
          mul_le_mul (sum_rooted_le_one hb (N a) (hN a) ht hz) ih
            (Finset.sum_nonneg fun _ _ => by positivity) hA0

end Rooted

/-! ## Walks inside a set, components -/

section Graph

variable {V : Type*} (H : SimpleGraph V)

theorem walkIn_mono {S T : Finset V} (hST : S ⊆ T) {a b : V} (h : WalkIn H S a b) : WalkIn H T a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun x hx => hST (hp x hx)⟩

theorem walkIn_symm {S : Finset V} {a b : V} (h : WalkIn H S a b) : WalkIn H S b a := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, fun x hx => hp x (by rwa [Walk.support_reverse, List.mem_reverse] at hx)⟩

theorem walkIn_adj {S : Finset V} {a b : V} (ha : a ∈ S) (hb : b ∈ S) (h : H.Adj a b) : WalkIn H S a b :=
  ⟨Walk.cons h Walk.nil, fun x hx => by
    simp at hx
    rcases hx with rfl | rfl <;> assumption⟩

/-- A walk inside `U` starting in `S` stays in `S` when `S` is closed under adjacency inside `U`. -/
theorem walk_stays {U S : Finset V} (hcl : ∀ x ∈ S, ∀ y ∈ U, H.Adj x y → y ∈ S) :
    ∀ {a b : V} (p : H.Walk a b), (∀ x ∈ p.support, x ∈ U) → a ∈ S → b ∈ S := by
  intro a b p
  induction p with
  | nil => exact fun _ h => h
  | cons h q ih =>
    intro hp ha
    exact ih (fun x hx => hp x (by simp [hx])) (hcl _ ha _ (hp _ (by simp)) h)

theorem walkIn_stays {U S : Finset V} (hcl : ∀ x ∈ S, ∀ y ∈ U, H.Adj x y → y ∈ S) {a b : V}
    (h : WalkIn H U a b) (ha : a ∈ S) : b ∈ S := by
  obtain ⟨p, hp⟩ := h
  exact walk_stays H hcl p hp ha

theorem isAnimal_of_walkIn [Fintype V] {S : Finset V} (hne : S.Nonempty)
    (h : ∀ a ∈ S, ∀ b ∈ S, WalkIn H S a b) : IsAnimal H S := by
  refine ⟨hne, ?_⟩
  have lift : ∀ {a b : V} (p : H.Walk a b) (_hp : ∀ x ∈ p.support, x ∈ S)
      (ha : a ∈ (S : Set V)) (hb : b ∈ (S : Set V)),
      (H.induce (S : Set V)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
    intro a b p
    induction p with
    | nil => intro _ _ _; exact Reachable.refl _
    | @cons a c b h q ih =>
      intro hp ha hb
      have hc : c ∈ (S : Set V) := hp c (by simp)
      exact (SimpleGraph.Adj.reachable (G := H.induce (S : Set V)) (u := ⟨a, ha⟩) (v := ⟨c, hc⟩) h).trans
        (ih (fun x hx => hp x (by simp [hx])) hc hb)
  obtain ⟨v, hv⟩ := hne
  have : Nonempty (S : Set V) := ⟨⟨v, hv⟩⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨p, hp⟩ := h x.1 x.2 y.1 y.2
  exact lift p hp x.2 y.2

theorem walkIn_of_isAnimal {S : Finset V} (h : IsAnimal H S) {a b : V} (ha : a ∈ S) (hb : b ∈ S) :
    WalkIn H S a b := by
  obtain ⟨p⟩ := h.2.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  have key : ∀ (x y : (S : Set V)) (q : (H.induce (S : Set V)).Walk x y), WalkIn H S x.1 y.1 := by
    intro x y q
    induction q with
    | nil => exact WalkIn.refl (Finset.mem_coe.mp (Subtype.prop _))
    | cons h q ih =>
      exact (walkIn_adj H (Finset.mem_coe.mp (Subtype.prop _)) (Finset.mem_coe.mp (Subtype.prop _)) h).trans ih
  exact key _ _ p

/-- The component of `v` in `X`. -/
def compOf (X : Finset V) (v : V) : Finset V := X.filter (fun u => WalkIn H X v u)

theorem mem_compOf {X : Finset V} {v u : V} : u ∈ compOf H X v ↔ u ∈ X ∧ WalkIn H X v u := by
  simp [compOf]

theorem self_mem_compOf {X : Finset V} {v : V} (hv : v ∈ X) : v ∈ compOf H X v :=
  (mem_compOf H).mpr ⟨hv, WalkIn.refl hv⟩

theorem compOf_subset (X : Finset V) (v : V) : compOf H X v ⊆ X := filter_subset _ _

theorem walkIn_compOf {X : Finset V} {v a : V} (ha : a ∈ compOf H X v) : WalkIn H (compOf H X v) v a := by
  obtain ⟨-, p, hp⟩ := (mem_compOf H).mp ha
  exact ⟨p, fun x hx => (mem_compOf H).mpr ⟨hp x hx, WalkIn.of_mem_support p hp hx⟩⟩

theorem isAnimal_compOf [Fintype V] {X : Finset V} {v : V} (hv : v ∈ X) : IsAnimal H (compOf H X v) :=
  isAnimal_of_walkIn H ⟨v, self_mem_compOf H hv⟩ (fun _ ha _ hb =>
    (walkIn_symm H (walkIn_compOf H ha)).trans (walkIn_compOf H hb))

theorem compOf_closed {X : Finset V} {v u w : V} (hu : u ∈ compOf H X v) (hw : w ∈ X)
    (h : u = w ∨ H.Adj u w) : w ∈ compOf H X v := by
  rcases h with rfl | h
  · exact hu
  obtain ⟨huX, hvu⟩ := (mem_compOf H).mp hu
  exact (mem_compOf H).mpr ⟨hw, hvu.trans (walkIn_adj H huX hw h)⟩

theorem compOf_eq_of_mem {X : Finset V} {v u : V} (hu : u ∈ compOf H X v) : compOf H X u = compOf H X v := by
  obtain ⟨-, hvu⟩ := (mem_compOf H).mp hu
  ext w
  rw [mem_compOf, mem_compOf]
  exact ⟨fun h => ⟨h.1, hvu.trans h.2⟩, fun h => ⟨h.1, (walkIn_symm H hvu).trans h.2⟩⟩

end Graph

/-! ## The polymer-gas identities (P7) -/

section Gas

variable {V : Type*} [Fintype V] (H : SimpleGraph V)

/-- `X` and `Y` are disjoint and no vertex of `X` is adjacent to a vertex of `Y`. -/
def NoTouch (X Y : Finset V) : Prop := Disjoint X Y ∧ ∀ u ∈ X, ∀ v ∈ Y, ¬ H.Adj u v

theorem I_biUnion (I : Finset V → ℝ) (hI0 : I ∅ = 1)
    (hIu : ∀ X Y, NoTouch H X Y → I (X ∪ Y) = I X * I Y) :
    ∀ Γ : Finset (BlockPolymer H), Compat (touch H) Γ →
      I (Γ.biUnion Subtype.val) = ∏ γ ∈ Γ, I γ.1 := by
  intro Γ
  induction Γ using Finset.induction_on with
  | empty => intro _; simp [hI0]
  | insert γ Γ hγ ih =>
    intro hc
    have hc' : Compat (touch H) Γ := fun x hx y hy hxy =>
      hc x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy
    rw [biUnion_insert, prod_insert hγ, ← ih hc']
    apply hIu
    have hnt : ∀ γ' ∈ Γ, ¬ touch H γ γ' := fun γ' hγ' ht =>
      hc γ (mem_insert_self _ _) γ' (mem_insert_of_mem hγ') (fun e => hγ (e ▸ hγ')) (Or.inl ht)
    refine ⟨Finset.disjoint_left.mpr fun u hu hu' => ?_, fun u hu v hv hadj => ?_⟩
    · obtain ⟨γ', hγ', hu'⟩ := mem_biUnion.mp hu'
      exact hnt γ' hγ' ⟨u, hu, u, hu', Or.inl rfl⟩
    · obtain ⟨γ', hγ', hv'⟩ := mem_biUnion.mp hv
      exact hnt γ' hγ' ⟨u, hu, v, hv', Or.inr hadj⟩

/-- The components of `X`, as polymers. -/
def compFam (X : Finset V) : Finset (BlockPolymer H) :=
  univ.filter (fun γ => ∃ v ∈ X, γ.1 = compOf H X v)

theorem compFam_subset {X : Finset V} {γ : BlockPolymer H} (hγ : γ ∈ compFam H X) : γ.1 ⊆ X := by
  obtain ⟨v, -, e⟩ := (mem_filter.mp hγ).2
  rw [e]; exact compOf_subset H X v

theorem compFam_compat (X : Finset V) : Compat (touch H) (compFam H X) := by
  intro γ hγ γ' hγ' hne hl
  obtain ⟨v, -, e⟩ := (mem_filter.mp hγ).2
  obtain ⟨v', -, e'⟩ := (mem_filter.mp hγ').2
  apply hne
  have key : ∀ {γ₁ γ₂ : BlockPolymer H} {v₁ v₂ : V}, γ₁.1 = compOf H X v₁ → γ₂.1 = compOf H X v₂ →
      touch H γ₁ γ₂ → γ₁ = γ₂ := by
    intro γ₁ γ₂ v₁ v₂ e₁ e₂ ht
    obtain ⟨u, hu, w, hw, huw⟩ := ht
    rw [e₁] at hu
    rw [e₂] at hw
    have hw1 : w ∈ compOf H X v₁ := compOf_closed H hu (compOf_subset H X v₂ hw) huw
    apply Subtype.ext
    rw [e₁, e₂, ← compOf_eq_of_mem H hw1, compOf_eq_of_mem H hw]
  rcases hl with h | h
  · exact key e e' h
  · exact (key e' e h).symm

theorem biUnion_compFam (X : Finset V) : (compFam H X).biUnion Subtype.val = X := by
  ext v
  rw [mem_biUnion]
  constructor
  · rintro ⟨γ, hγ, hv⟩; exact compFam_subset H hγ hv
  · intro hv
    exact ⟨⟨compOf H X v, isAnimal_compOf H hv⟩, mem_filter.mpr ⟨mem_univ _, v, hv, rfl⟩,
      self_mem_compOf H hv⟩

theorem compOf_biUnion {Γ : Finset (BlockPolymer H)} (hc : Compat (touch H) Γ) {γ : BlockPolymer H}
    (hγ : γ ∈ Γ) {v : V} (hv : v ∈ γ.1) : compOf H (Γ.biUnion Subtype.val) v = γ.1 := by
  ext u
  rw [mem_compOf]
  constructor
  · rintro ⟨-, hvu⟩
    refine walkIn_stays H (S := γ.1) (fun x hx y hy hxy => ?_) hvu hv
    obtain ⟨γ', hγ', hy'⟩ := mem_biUnion.mp hy
    by_contra hyγ
    have hne : γ ≠ γ' := fun e => hyγ (e ▸ hy')
    exact hc γ hγ γ' hγ' hne (Or.inl ⟨x, hx, y, hy', Or.inr hxy⟩)
  · intro hu
    exact ⟨mem_biUnion.mpr ⟨γ, hγ, hu⟩,
      walkIn_mono H (subset_biUnion_of_mem Subtype.val hγ) (walkIn_of_isAnimal H γ.2 hv hu)⟩

theorem compFam_biUnion {Γ : Finset (BlockPolymer H)} (hc : Compat (touch H) Γ) :
    compFam H (Γ.biUnion Subtype.val) = Γ := by
  ext γ
  simp only [compFam, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, e⟩
    obtain ⟨γ', hγ', hv'⟩ := mem_biUnion.mp hv
    rw [compOf_biUnion H hc hγ' hv'] at e
    have : γ = γ' := Subtype.ext e
    exact this ▸ hγ'
  · intro hγ
    obtain ⟨v, hv⟩ := γ.2.1
    exact ⟨v, mem_biUnion.mpr ⟨γ, hγ, hv⟩, (compOf_biUnion H hc hγ hv).symm⟩

/-- **P7, denominator.** The sum of `I` over the sets avoiding `T` is the partition function of the gas of connected
    polymers avoiding `T`, with activity `I` and incompatibility `touch`. -/
theorem sum_avoid_eq_XiAvoid (I : Finset V → ℝ) (hI0 : I ∅ = 1)
    (hIu : ∀ X Y, NoTouch H X Y → I (X ∪ Y) = I X * I Y) (T : Finset V) :
    ((∑ X ∈ univ.filter (fun X : Finset V => Disjoint X T), I X : ℝ) : ℂ) =
      XiAvoid (touch H) (fun γ : BlockPolymer H => γ.1) T (fun γ => (I γ.1 : ℂ)) := by
  have hXA : XiAvoid (touch H) (fun γ : BlockPolymer H => γ.1) T (fun γ => (I γ.1 : ℂ)) =
      ∑ Γ ∈ (univ : Finset (Finset (BlockPolymer H))).filter
        (fun Γ => Compat (touch H) Γ ∧ ∀ x ∈ Γ, Disjoint x.1 T), ∏ x ∈ Γ, (I x.1 : ℂ) := by
    convert XiAvoid_eq (touch H) (fun γ : BlockPolymer H => γ.1) T (fun γ => (I γ.1 : ℂ))
  rw [hXA, Complex.ofReal_sum]
  refine Finset.sum_nbij' (compFam H) (fun Γ => Γ.biUnion Subtype.val) ?_ ?_ ?_ ?_ ?_
  · intro X hX
    rw [mem_filter] at hX ⊢
    exact ⟨mem_univ _, compFam_compat H X, fun γ hγ => hX.2.mono_left (compFam_subset H hγ)⟩
  · intro Γ hΓ
    rw [mem_filter] at hΓ ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [disjoint_biUnion_left]
    exact hΓ.2.2
  · intro X _
    exact biUnion_compFam H X
  · intro Γ hΓ
    exact compFam_biUnion H (mem_filter.mp hΓ).2.1
  · intro X _
    conv_lhs => rw [← biUnion_compFam H X]
    rw [I_biUnion H I hI0 hIu _ (compFam_compat H X), Complex.ofReal_prod]

/-- The vertices in `R`, in `Y`, or adjacent to `Y`. -/
def SY (R Y : Finset V) : Finset V := univ.filter (fun v => v ∈ R ∨ ∃ u ∈ Y, u = v ∨ H.Adj u v)

theorem subset_SY_left (R Y : Finset V) : R ⊆ SY H R Y := fun v hv => by simp [SY, hv]

theorem subset_SY_right (R Y : Finset V) : Y ⊆ SY H R Y := fun v hv => by
  simp only [SY, mem_filter, mem_univ, true_and]
  exact Or.inr ⟨v, hv, Or.inl rfl⟩

theorem sdiff_splitOff_disjoint (R X : Finset V) :
    Disjoint (X \ splitOff (G := H) (R : Set V) X) (SY H R (splitOff (G := H) (R : Set V) X)) := by
  rw [Finset.disjoint_left]
  intro v hv hS
  obtain ⟨hvX, hvn⟩ := mem_sdiff.mp hv
  apply hvn
  simp only [SY, mem_filter, mem_univ, true_and] at hS
  simp only [splitOff, mem_filter]
  refine ⟨hvX, ?_⟩
  rcases hS with hR | ⟨u, hu, rfl | hadj⟩
  · exact ⟨v, hR, WalkIn.refl hvX⟩
  · simp only [splitOff, mem_filter] at hu
    exact hu.2
  · simp only [splitOff, mem_filter] at hu
    obtain ⟨huX, w, hw, huw⟩ := hu
    exact ⟨w, hw, (walkIn_adj H hvX huX hadj.symm).trans huw⟩

theorem splitOff_union {R Y X' : Finset V} (hY : Rooted H (R : Set V) Y) (hX' : Disjoint X' (SY H R Y)) :
    splitOff (G := H) (R : Set V) (Y ∪ X') = Y := by
  ext v
  simp only [splitOff, mem_filter]
  constructor
  · rintro ⟨hv, w, hw, hvw⟩
    by_contra hvY
    have hvX' : v ∈ X' := (mem_union.mp hv).resolve_left hvY
    have hwX' : w ∈ X' := by
      refine walkIn_stays H (S := X') (fun x hx y hy hxy => ?_) hvw hvX'
      rcases mem_union.mp hy with hyY | hyX
      · exfalso
        refine Finset.disjoint_left.mp hX' hx ?_
        simp only [SY, mem_filter, mem_univ, true_and]
        exact Or.inr ⟨y, hyY, Or.inr hxy.symm⟩
      · exact hyX
    exact Finset.disjoint_left.mp hX' hwX' (subset_SY_left H R Y (by simpa using hw))
  · intro hv
    obtain ⟨w, hw, hvw⟩ := hY v hv
    exact ⟨mem_union_left _ hv, w, hw, walkIn_mono H subset_union_left hvw⟩

/-- **P7, numerator.** Split `X` into the part joined to `R` inside `X` (a set rooted at `R`) and the rest, which avoids
    `SY R Y`. -/
theorem sum_IC_eq (I IC : Finset V → ℝ) (R : Finset V)
    (hICu : ∀ X Y, NoTouch H X Y → Disjoint Y R → IC (X ∪ Y) = IC X * I Y) :
    ∑ X : Finset V, IC X = ∑ Y ∈ rootedSets (G := H) (R : Set V),
      IC Y * ∑ X' ∈ univ.filter (fun X' : Finset V => Disjoint X' (SY H R Y)), I X' := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij'
    (fun X => (⟨splitOff (G := H) (R : Set V) X, X \ splitOff (G := H) (R : Set V) X⟩ :
      Σ _ : Finset V, Finset V))
    (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro X _
    rw [mem_sigma]
    refine ⟨mem_rootedSets.mpr (rooted_splitOff (N' := Set.univ) (fun v hv => ⟨v, Or.inr trivial,
      WalkIn.refl hv⟩)), mem_filter.mpr ⟨mem_univ _, sdiff_splitOff_disjoint H R X⟩⟩
  · intro p _
    exact mem_univ _
  · intro X _
    exact splitOff_union_sdiff _ _
  · rintro ⟨Y, X'⟩ hp
    rw [mem_sigma, mem_rootedSets, mem_filter] at hp
    have hYX : Disjoint X' Y := hp.2.2.mono_right (subset_SY_right H R Y)
    have e1 : splitOff (G := H) (R : Set V) (Y ∪ X') = Y := splitOff_union H hp.1 hp.2.2
    simp only [e1]
    rw [union_sdiff_left, sdiff_eq_self_of_disjoint hYX]
  · intro X _
    simp only
    conv_lhs => rw [← splitOff_union_sdiff (G := H) (R : Set V) X]
    have hd := sdiff_splitOff_disjoint H R X
    refine hICu _ _ ⟨Finset.disjoint_sdiff, fun u hu v hv hadj => ?_⟩ (hd.mono_right (subset_SY_left H R _))
    refine Finset.disjoint_left.mp hd hv ?_
    simp only [SY, mem_filter, mem_univ, true_and]
    exact Or.inr ⟨u, hu, Or.inr hadj⟩

theorem card_SY_le {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) (R Y : Finset V) :
    (SY H R Y).card ≤ R.card + (Δ + 1) * Y.card := by
  have hsub : SY H R Y ⊆ R ∪ Y.biUnion (fun u => insert u (H.neighborFinset u)) := by
    intro v hv
    simp only [SY, mem_filter, mem_univ, true_and] at hv
    rcases hv with h | ⟨u, hu, h⟩
    · exact mem_union_left _ h
    · refine mem_union_right _ (mem_biUnion.mpr ⟨u, hu, ?_⟩)
      rcases h with rfl | h
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem ((H.mem_neighborFinset u v).mpr h)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
  refine card_biUnion_le.trans ?_
  calc ∑ u ∈ Y, (insert u (H.neighborFinset u)).card ≤ ∑ _u ∈ Y, (Δ + 1) :=
        sum_le_sum fun u _ => (card_insert_le _ _).trans
          (by rw [card_neighborFinset_eq_degree]; exact Nat.add_le_add_right (hdeg u) 1)
    _ = (Δ + 1) * Y.card := by rw [sum_const, smul_eq_mul, mul_comm]

end Gas

/-! ## The abstract area law (P9) -/

section Abstract

variable {V : Type*} [Fintype V] (H : SimpleGraph V)

/-- **The abstract area law.** For `0 ≤ ε ≤ 1 / (4 e^{Δ+1} (Δ+1)^4)`:
    `|∑ IC / ∑ I| ≤ M e^{2|R|} (√(e^{Δ+1} ε))^A`, and the denominator is nonzero. -/
theorem area_bound_abstract {Δ : ℕ} (hdeg : ∀ v, H.degree v ≤ Δ) (R : Finset V) (I IC : Finset V → ℝ)
    {ε M : ℝ} {A : ℕ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / (4 * Real.exp ((Δ : ℝ) + 1) * ((Δ : ℝ) + 1) ^ 4))
    (hI0 : I ∅ = 1) (hIu : ∀ X Y, NoTouch H X Y → I (X ∪ Y) = I X * I Y)
    (hICu : ∀ X Y, NoTouch H X Y → Disjoint Y R → IC (X ∪ Y) = IC X * I Y)
    (hIb : ∀ X, |I X| ≤ ε ^ X.card) (hICb : ∀ X, |IC X| ≤ M * ε ^ X.card)
    (hA : ∀ X, IC X ≠ 0 → A ≤ X.card) :
    ∑ X ∈ (univ : Finset V).powerset, I X ≠ 0 ∧
      |(∑ X ∈ (univ : Finset V).powerset, IC X) / (∑ X ∈ (univ : Finset V).powerset, I X)| ≤
        M * Real.exp (2 * R.card) * Real.sqrt (Real.exp ((Δ : ℝ) + 1) * ε) ^ A := by
  set D : ℝ := (Δ : ℝ) + 1 with hD
  have hD1 : 1 ≤ D := by have := Nat.cast_nonneg (α := ℝ) Δ; linarith
  have hE1 : Real.exp 1 ≤ Real.exp D := Real.exp_le_exp.mpr hD1
  have hpos : 0 < 4 * Real.exp D * D ^ 4 := by positivity
  have hε1 : ε ≤ 1 / (2 * Real.exp 1 * D ^ 2) := by
    refine hε.trans (one_div_le_one_div_of_le (by positivity) ?_)
    have hD24 : D ^ 2 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
    nlinarith [mul_le_mul hE1 hD24 (by positivity) (Real.exp_pos D).le, Real.exp_pos 1]
  set x : ℝ := Real.exp D * ε with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ (1 / (2 * D ^ 2)) ^ 2 := by
    have h1 := (le_div_iff₀ hpos).mp hε
    rw [hx, div_pow, one_pow, le_div_iff₀ (by positivity)]
    nlinarith [h1]
  set s : ℝ := Real.sqrt x with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0
  have hsD : s ≤ 1 / (2 * D ^ 2) := by
    calc Real.sqrt x ≤ Real.sqrt ((1 / (2 * D ^ 2)) ^ 2) := Real.sqrt_le_sqrt hx1
      _ = 1 / (2 * D ^ 2) := Real.sqrt_sq (by positivity)
  have hzs : D ^ 2 * s ≤ 1 / 2 := by
    calc D ^ 2 * s ≤ D ^ 2 * (1 / (2 * D ^ 2)) := mul_le_mul_of_nonneg_left hsD (by positivity)
      _ = 1 / 2 := by field_simp
  have hD2 : 1 ≤ D ^ 2 := one_le_pow₀ hD1
  have hs1 : s ≤ 1 := by nlinarith
  have hM : 0 ≤ M := by
    have := hICb ∅
    simp only [card_empty, pow_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  -- the gas
  set K : BlockPolymer H → ℂ := fun γ => (I γ.1 : ℂ) with hKdef
  set Z : Finset V → ℝ := fun T => ∑ X ∈ univ.filter (fun X : Finset V => Disjoint X T), I X with hZdef
  have hZ : ∀ T, (Z T : ℂ) = XiAvoid (touch H) (fun γ : BlockPolymer H => γ.1) T K :=
    fun T => sum_avoid_eq_XiAvoid H I hI0 hIu T
  have hden : ∑ X ∈ (univ : Finset V).powerset, I X = Z ∅ := by
    rw [powerset_univ]
    simp [hZdef]
  have hK : ∀ γ : BlockPolymer H, ‖K γ‖ ≤ ε ^ γ.1.card := fun γ => by
    simp only [hKdef, Complex.norm_real, Real.norm_eq_abs]; exact hIb _
  have hclu := fun S => cluster_ratio_touch_explicit H hdeg hε0 hε1 K hK S
  have hXi : Xi (touch H) K = (Z ∅ : ℂ) := by rw [hZ ∅, XiAvoid_empty]
  have hZ0 : Z ∅ ≠ 0 := by
    have := (hclu ∅).1
    rw [hXi] at this
    exact_mod_cast this
  have hratio : ∀ S, |Z S / Z ∅| ≤ Real.exp S.card := by
    intro S
    have h := (hclu S).2
    rwa [← hZ S, hXi, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs] at h
  have hnum : ∑ X ∈ (univ : Finset V).powerset, IC X =
      ∑ Y ∈ rootedSets (G := H) (R : Set V), IC Y * Z (SY H R Y) := by
    rw [powerset_univ]; exact sum_IC_eq H I IC R hICu
  refine ⟨hden ▸ hZ0, ?_⟩
  rw [hnum, hden, Finset.sum_div]
  have hterm : ∀ Y ∈ rootedSets (G := H) (R : Set V),
      |IC Y * Z (SY H R Y) / Z ∅| ≤ M * Real.exp R.card * s ^ A * s ^ Y.card := by
    intro Y _
    rw [mul_div_assoc, abs_mul]
    by_cases h0 : IC Y = 0
    · rw [h0, abs_zero, zero_mul]; positivity
    have hAY := hA Y h0
    have hc0 : ((SY H R Y).card : ℝ) ≤ (R.card : ℝ) + ((Δ : ℝ) + 1) * (Y.card : ℝ) := by
      exact_mod_cast card_SY_le H hdeg R Y
    have hcard : ((SY H R Y).card : ℝ) ≤ (R.card : ℝ) + (Y.card : ℝ) * D := by
      rw [hD, mul_comm]; exact hc0
    have hsq : s ^ Y.card * s ^ Y.card = (Real.exp D * ε) ^ Y.card := by
      rw [← mul_pow, ← sq, hs2]
    calc |IC Y| * |Z (SY H R Y) / Z ∅|
        ≤ (M * ε ^ Y.card) * Real.exp ((R.card : ℝ) + (Y.card : ℝ) * D) :=
          mul_le_mul (hICb Y) ((hratio _).trans (Real.exp_le_exp.mpr hcard)) (abs_nonneg _) (by positivity)
      _ = M * Real.exp R.card * (Real.exp D * ε) ^ Y.card := by
          rw [Real.exp_add, Real.exp_nat_mul, mul_pow]; ring
      _ = M * Real.exp R.card * (s ^ Y.card * s ^ Y.card) := by rw [hsq]
      _ ≤ M * Real.exp R.card * (s ^ A * s ^ Y.card) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0 hs1 hAY)
            (by positivity)) (by positivity)
      _ = M * Real.exp R.card * s ^ A * s ^ Y.card := by ring
  have hroot : ∑ Y ∈ rootedSets (G := H) (R : Set V), s ^ Y.card ≤ 2 ^ R.card := by
    have hmaxR : ((max (Δ + 1) 1 : ℕ) : ℝ) = D := by
      rw [max_eq_left (by omega), hD]; push_cast; ring
    have hq : 0 < 1 - D ^ 2 * s := by linarith
    have hz : ((max (Δ + 1) 1 : ℕ) : ℝ) ^ 2 * s < 1 := by rw [hmaxR]; linarith
    have h := sum_rooted_le (G := H) (b := Δ) (b_root := 1) hdeg (fun v => ({v} : Finset V))
      (fun v => by simp) hs0 hz R
    have hU : (⋃ i ∈ R, (({i} : Finset V) : Set V)) = (R : Set V) := by ext; simp
    rw [hU, hmaxR] at h
    refine h.trans (pow_le_pow_left₀ (one_div_pos.mpr hq).le ?_ _)
    rw [div_le_iff₀ hq]; linarith
  have h2 : (2 : ℝ) ^ R.card ≤ Real.exp R.card := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _
  have he2 : Real.exp (2 * (R.card : ℝ)) = Real.exp R.card * Real.exp R.card := by
    rw [← Real.exp_add]; ring_nf
  calc |∑ Y ∈ rootedSets (G := H) (R : Set V), IC Y * Z (SY H R Y) / Z ∅|
      ≤ ∑ Y ∈ rootedSets (G := H) (R : Set V), |IC Y * Z (SY H R Y) / Z ∅| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ Y ∈ rootedSets (G := H) (R : Set V), M * Real.exp R.card * s ^ A * s ^ Y.card := sum_le_sum hterm
    _ = M * Real.exp R.card * s ^ A * ∑ Y ∈ rootedSets (G := H) (R : Set V), s ^ Y.card := by rw [mul_sum]
    _ ≤ M * Real.exp R.card * s ^ A * 2 ^ R.card := mul_le_mul_of_nonneg_left hroot (by positivity)
    _ ≤ M * Real.exp R.card * s ^ A * Real.exp R.card := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = M * Real.exp (2 * R.card) * s ^ A := by rw [he2]; ring

end Abstract

/-! ## The lattice instantiation -/

section LatticeInst

open MeasureTheory

variable {d N : ℕ}

/-- The plaquette graph: distinct plaquettes sharing a link. -/
def plaqGraph (d N : ℕ) : SimpleGraph (LatticePlaquette d N) where
  Adj p q := p ≠ q ∧ (plaqLinks p ∩ plaqLinks q).Nonempty
  symm := ⟨fun p q h => ⟨h.1.symm, by rw [Finset.inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun p h => h.1 rfl⟩

variable [Fintype (LatticePlaquette d N)]

/-- The plaquettes containing a link of the path `C`. -/
def loopPlaqs (C : List (PathStep d N)) : Finset (LatticePlaquette d N) :=
  univ.filter (fun p => (plaqLinks p ∩ pathLinks C).Nonempty)

theorem linksOf_disjoint {X Y : Finset (LatticePlaquette d N)} (h : NoTouch (plaqGraph d N) X Y) :
    Disjoint (linksOf X) (linksOf Y) := by
  rw [Finset.disjoint_left]
  intro l hlX hlY
  rw [linksOf, mem_biUnion] at hlX hlY
  obtain ⟨p, hp, hlp⟩ := hlX
  obtain ⟨q, hq, hlq⟩ := hlY
  by_cases hpq : p = q
  · subst hpq; exact Finset.disjoint_left.mp h.1 hp hq
  · exact h.2 p hp q hq ⟨hpq, l, mem_inter.mpr ⟨hlp, hlq⟩⟩

theorem loop_linksOf_disjoint (C : List (PathStep d N)) {X Y : Finset (LatticePlaquette d N)}
    (h : NoTouch (plaqGraph d N) X Y) (hY : Disjoint Y (loopPlaqs C)) :
    Disjoint (pathLinks C ∪ linksOf X) (linksOf Y) := by
  refine Finset.disjoint_union_left.mpr ⟨?_, linksOf_disjoint h⟩
  rw [Finset.disjoint_left]
  intro l hlC hlY
  rw [linksOf, mem_biUnion] at hlY
  obtain ⟨q, hq, hlq⟩ := hlY
  refine Finset.disjoint_left.mp hY hq ?_
  simp only [loopPlaqs, mem_filter, mem_univ, true_and]
  exact ⟨l, mem_inter.mpr ⟨hlq, hlC⟩⟩

variable {G : Type*} [Group G] [MeasurableSpace G] [HasHaarProbability G] {n : ℕ} [HasGaugeTrace G n]
  [Fintype (LatticeLink d N)]

/-- **The area law on the lattice**, for a closed path `C` and a minimal-area hypothesis `hArea` (every set `O` of
    plaquettes forming with `C` a closed surface mod 2 has at least `A` plaquettes). `Δ` bounds the degree of the
    plaquette graph (`≤ 4 (2 (d - 1) - 1)`; kept as a hypothesis). With `ε = e^{nβ} - 1`:
    `|⟨W_C⟩| ≤ n e^{2 |R_C|} (√(e^{Δ+1} ε))^A`, `R_C` the plaquettes containing a link of `C`. -/
theorem wilson_area_law (hbd : ∀ g : G, |gaugeReTr G n g| ≤ n)
    (hmeas : ∀ p : LatticePlaquette d N, Measurable (xp (G := G) n p))
    (z : G) (hz : ∀ g : G, Commute z g) (hzz : z * z = 1)
    (hrep : HasGaugeTrace.rep (G := G) (n := n) z = -1)
    (hzm : MeasurePreserving (z * ·) (haarG G) (haarG G))
    {β : ℝ} (hβ : 0 ≤ β) (C : List (PathStep d N)) (hW : Measurable (wilsonLoop (G := G) n C))
    {Δ : ℕ} (hdeg : ∀ p, (plaqGraph d N).degree p ≤ Δ)
    (hsmall : Real.exp (n * β) - 1 ≤ 1 / (4 * Real.exp ((Δ : ℝ) + 1) * ((Δ : ℝ) + 1) ^ 4))
    {A : ℕ} (hArea : ∀ O : Finset (LatticePlaquette d N),
      (∀ ℓ, Even (visits ℓ C + plaqVisits ℓ O)) → A ≤ O.card) :
    ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N) ≠ 0 ∧
    |(∫ U, wilsonLoop n C U * ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U)
        ∂(productHaar G d N)) /
      (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N))| ≤
      n * Real.exp (2 * (loopPlaqs C).card) *
        Real.sqrt (Real.exp ((Δ : ℝ) + 1) * (Real.exp (n * β) - 1)) ^ A := by
  rw [integral_expand_Z hbd hmeas hβ, integral_expand_W hbd hmeas hβ C hW]
  have hε0 : 0 ≤ Real.exp (n * β) - 1 := by
    have : 0 ≤ (n : ℝ) * β := mul_nonneg (Nat.cast_nonneg n) hβ
    linarith [Real.add_one_le_exp ((n : ℝ) * β)]
  refine area_bound_abstract (plaqGraph d N) hdeg (loopPlaqs C) (Iint (G := G) n β) (ICint (G := G) n β C)
    hε0 hsmall ?_ ?_ ?_ ?_ ?_ ?_
  · simp [Iint]
  · intro X Y h
    convert I_union (G := G) (n := n) hmeas β (linksOf_disjoint h)
  · intro X Y h hY
    convert IC_union (G := G) (n := n) hmeas β C hW (loop_linksOf_disjoint C h hY)
  · intro X; exact abs_I_le hbd hβ X
  · intro X; exact abs_IC_le hbd hβ C X
  · intro X hX
    by_contra hlt
    push Not at hlt
    apply hX
    refine IC_eq_zero_of_no_parity hbd hmeas z hz hzz hrep hzm hβ C hW X (fun O hO => ?_)
    by_contra hall
    push Not at hall
    have h1 := hArea O (fun ℓ => Nat.not_odd_iff_even.mp (hall ℓ))
    have h2 := card_le_card (mem_powerset.mp hO)
    omega

/-- **The area law for the rectangular loop** `C = rectPath x μ ν R T`, with `A = min (R T, N² - R T)` from the
    minimal-area lemma `rect_parity_area` (P5). -/
theorem wilson_area_law_rect (hbd : ∀ g : G, |gaugeReTr G n g| ≤ n)
    (hmeas : ∀ p : LatticePlaquette d N, Measurable (xp (G := G) n p))
    (z : G) (hz : ∀ g : G, Commute z g) (hzz : z * z = 1)
    (hrep : HasGaugeTrace.rep (G := G) (n := n) z = -1)
    (hzm : MeasurePreserving (z * ·) (haarG G) (haarG G))
    {β : ℝ} (hβ : 0 ≤ β) (x : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ < ν) (R T : ℕ)
    (hR : 1 ≤ R) (hT : 1 ≤ T) (hRN : R < N) (hTN : T < N)
    (hW : Measurable (wilsonLoop (G := G) n (rectPath x μ ν R T)))
    {Δ : ℕ} (hdeg : ∀ p, (plaqGraph d N).degree p ≤ Δ)
    (hsmall : Real.exp (n * β) - 1 ≤ 1 / (4 * Real.exp ((Δ : ℝ) + 1) * ((Δ : ℝ) + 1) ^ 4)) :
    ∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N) ≠ 0 ∧
    |(∫ U, wilsonLoop n (rectPath x μ ν R T) U *
          ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N)) /
      (∫ U, ∏ p ∈ (univ : Finset (LatticePlaquette d N)), Real.exp (β * xp n p U) ∂(productHaar G d N))| ≤
      n * Real.exp (2 * (loopPlaqs (rectPath x μ ν R T)).card) *
        Real.sqrt (Real.exp ((Δ : ℝ) + 1) * (Real.exp (n * β) - 1)) ^ (min (R * T) (N * N - R * T)) :=
  wilson_area_law hbd hmeas z hz hzz hrep hzm hβ (rectPath x μ ν R T) hW hdeg hsmall
    (fun O hO => (rect_parity_area x hμν R T hR hT hRN hTN O hO).trans (card_le_card (filter_subset _ _)))

-- #print axioms area_bound_abstract  -- [propext, Classical.choice, Quot.sound]
-- #print axioms wilson_area_law  -- [propext, Classical.choice, Quot.sound]
-- #print axioms wilson_area_law_rect  -- [propext, Classical.choice, Quot.sound]

end LatticeInst

end AreaLaw.Assembly
