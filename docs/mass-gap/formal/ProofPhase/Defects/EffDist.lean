/-
Proof phase, cycle 5, workstream 4 (c5d-supplier): the effective distance of a defect set and its Peierls bound
(2026-11-22). Released under Apache 2.0.

Note: `docs/mass-gap/weak-coupling/proof-phase/c5d-supplier/NOTE.md`, Part B.
-/

import Mathlib

/-!
# Effective distance with free defects, and the Peierls bound for it

**Setting.** A finite simple graph `G` on the sites `V` (for the torus: links adjacent when they share a plaquette, or
any finite-degree adjacency the route chooses), a set `Bad` of defect sites. A walk pays one unit for every **good** site
it visits after its start (each site counted once); defect sites are free.

* `walkCost G Bad p`: the number of distinct good sites in `p.support.tail`.
* `effDist G Bad u S`: the least cost of a walk from `u` to a point of `S` (a natural number).
* `effWeight G Bad lam S u = e^{-λ effDist}`: the weight a Dobrushin argument propagates when defects are free.

**Deterministic facts (D).** `effDist_self`, the triangle inequality `effDist_le_add` (walks concatenate), the weight
estimate `effWeight_le_mul` (`w(y) ≤ e^{λ ρ(x,y)} w(x)`), and `effDist_le_dist`-type comparisons are elementary.

**The Peierls bound (S).** If the defect set is random with law `q` (weights on `Finset V`) and **dominated on cylinders**,
`∑_B q B · 1[U ⊆ B] ≤ p₀^{|U|}` for every `U` (true for Bernoulli(`p₀`) and for every field stochastically dominated by
it), and every site has at most `Δ` neighbours, then (`expect_effWeight_le`)

  `E_q e^{-λ effDist(u, S)} ≤ ∑_{n = d}^{|V|-1} (Δ (p₀ + e^{-λ}))^n ≤ (Δ (p₀ + e^{-λ}))^d / (1 − Δ (p₀ + e^{-λ}))`,

`d ≤ dist_G(u, S)`. The proof: the minimising walk can be shortened to a self-avoiding path (`bypass`), so
`e^{-λ effDist} ≤ ∑_{paths} e^{-λ cost}`; along a path the sites are distinct, so the expectation of the product of
`(1 if bad, e^{-λ} if good)` over `n` sites is at most `(p₀ + e^{-λ})^n` by expanding the product (`expect_prod_le`); and
there are at most `Δ^n` walks of length `n` from `u` (`sum_card_walks_le`). No volume enters: the bound is uniform in
the size of `V`. This is the subcriticality condition of disagreement percolation in path-counting form: a good step
costs `e^{-λ}`, a defect costs its probability `p₀`, the branching is `Δ`.
-/

open Finset SimpleGraph

set_option linter.unusedSectionVars false

noncomputable section

namespace ProofPhase.Defects

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Cost of a walk and the effective distance -/

/-- The cost of a walk: the number of distinct **good** sites (not in `Bad`) it visits after its start. -/
def walkCost (Bad : Finset V) {u v : V} (p : G.Walk u v) : ℕ :=
  (p.support.tail.toFinset.filter (fun x => x ∉ Bad)).card

/-- The effective distance from `u` to the set `S`: the least cost of a walk from `u` to a point of `S`. -/
def effDist (Bad : Finset V) (u : V) (S : Finset V) : ℕ :=
  sInf {c | ∃ s ∈ S, ∃ p : G.Walk u s, walkCost G Bad p = c}

/-- The effective weight `e^{-λ effDist(u, S)}`. -/
def effWeight (Bad : Finset V) (lam : ℝ) (S : Finset V) (u : V) : ℝ :=
  Real.exp (-(lam * (effDist G Bad u S : ℝ)))

variable {G}

theorem effDist_le_cost (Bad : Finset V) {u s : V} {S : Finset V} (hs : s ∈ S) (p : G.Walk u s) :
    effDist G Bad u S ≤ walkCost G Bad p :=
  Nat.sInf_le ⟨s, hs, p, rfl⟩

theorem exists_walk_effDist (hG : G.Preconnected) (Bad : Finset V) (u : V) {S : Finset V} (hS : S.Nonempty) :
    ∃ s ∈ S, ∃ p : G.Walk u s, walkCost G Bad p = effDist G Bad u S := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨p⟩ := hG u s
  have hne : ({c | ∃ s ∈ S, ∃ p : G.Walk u s, walkCost G Bad p = c} : Set ℕ).Nonempty := ⟨_, s, hs, p, rfl⟩
  exact Nat.sInf_mem hne

theorem walkCost_nil (Bad : Finset V) (u : V) : walkCost G Bad (Walk.nil : G.Walk u u) = 0 := by
  simp [walkCost]

theorem effDist_self (Bad : Finset V) {u : V} {S : Finset V} (hu : u ∈ S) : effDist G Bad u S = 0 :=
  Nat.le_zero.1 ((effDist_le_cost Bad hu Walk.nil).trans (walkCost_nil Bad u).le)

theorem walkCost_append_le (Bad : Finset V) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkCost G Bad (p.append q) ≤ walkCost G Bad p + walkCost G Bad q := by
  unfold walkCost
  have h : (p.append q).support.tail = p.support.tail ++ q.support.tail := by
    rw [Walk.support_append, ← p.cons_tail_support]
    rfl
  rw [h, List.toFinset_append, filter_union]
  exact card_union_le _ _

/-- **Triangle inequality** for the effective distance (walks concatenate). -/
theorem effDist_le_add (hG : G.Preconnected) (Bad : Finset V) (x y : V) {S : Finset V} (hS : S.Nonempty) :
    effDist G Bad x S ≤ effDist G Bad x {y} + effDist G Bad y S := by
  obtain ⟨y', hy', p, hp⟩ := exists_walk_effDist hG Bad x (singleton_nonempty y)
  rw [mem_singleton] at hy'
  subst hy'
  obtain ⟨s, hs, q, hq⟩ := exists_walk_effDist hG Bad y' hS
  calc effDist G Bad x S ≤ walkCost G Bad (p.append q) := effDist_le_cost Bad hs _
    _ ≤ walkCost G Bad p + walkCost G Bad q := walkCost_append_le Bad p q
    _ = _ := by rw [hp, hq]

theorem effWeight_nonneg (Bad : Finset V) (lam : ℝ) (S : Finset V) (u : V) : 0 ≤ effWeight G Bad lam S u :=
  (Real.exp_pos _).le

theorem effWeight_of_mem (Bad : Finset V) (lam : ℝ) {S : Finset V} {u : V} (hu : u ∈ S) :
    effWeight G Bad lam S u = 1 := by
  simp [effWeight, effDist_self Bad hu]

/-- **`w(y) ≤ e^{λ ρ(x, y)} w(x)`** for the effective weight. -/
theorem effWeight_le_mul (hG : G.Preconnected) (Bad : Finset V) {lam : ℝ} (hlam : 0 ≤ lam) {S : Finset V}
    (hS : S.Nonempty) (x y : V) :
    effWeight G Bad lam S y ≤ Real.exp (lam * (effDist G Bad x {y} : ℝ)) * effWeight G Bad lam S x := by
  unfold effWeight
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h : (effDist G Bad x S : ℝ) ≤ effDist G Bad x {y} + effDist G Bad y S := by
    exact_mod_cast effDist_le_add hG Bad x y hS
  nlinarith

/-- With `ρ(x, y) ≤ D`: `w(y) ≤ e^{λ D} w(x)`. -/
theorem effWeight_le_of_effDist (hG : G.Preconnected) (Bad : Finset V) {lam : ℝ} (hlam : 0 ≤ lam)
    {S : Finset V} (hS : S.Nonempty) {x y : V} {D : ℝ} (hxy : (effDist G Bad x {y} : ℝ) ≤ D) :
    effWeight G Bad lam S y ≤ Real.exp (lam * D) * effWeight G Bad lam S x :=
  (effWeight_le_mul hG Bad hlam hS x y).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hxy hlam))
      (effWeight_nonneg Bad lam S x))

/-! ## Paths -/

/-- Shortening a walk to a path does not increase its cost. -/
theorem walkCost_bypass_le (Bad : Finset V) {u v : V} (p : G.Walk u v) :
    walkCost G Bad p.bypass ≤ walkCost G Bad p := by
  unfold walkCost
  refine card_le_card fun x hx => ?_
  rw [mem_filter, List.mem_toFinset] at hx ⊢
  refine ⟨?_, hx.2⟩
  have hnd := (p.bypass_isPath).support_nodup
  rw [← p.bypass.cons_tail_support, List.nodup_cons] at hnd
  have hxu : x ≠ u := fun h => hnd.1 (h ▸ hx.1)
  have hx' : x ∈ p.support := p.support_bypass_subset_support (List.mem_of_mem_tail hx.1)
  rw [← p.cons_tail_support, List.mem_cons] at hx'
  exact hx'.resolve_left hxu

/-- On a path the tail of the support has exactly `length` distinct sites. -/
theorem card_tail_of_isPath {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.support.tail.toFinset.card = p.length := by
  have hnd := hp.support_nodup
  rw [← p.cons_tail_support, List.nodup_cons] at hnd
  rw [List.toFinset_card_of_nodup hnd.2, List.length_tail, Walk.length_support]
  simp

/-! ## The expansion of a product over distinct sites -/

/-- **Expectation of a product over distinct sites.** If `∑_B q B 1[U ⊆ B] ≤ p₀^{|U|}` for every `U`, then
`∑_B q B ∏_{v ∈ T} (1 if v ∈ B else r) ≤ (p₀ + r)^{|T|}` for `0 ≤ r ≤ 1`. -/
theorem expect_prod_le (q : Finset V → ℝ) {p0 : ℝ} (hp0 : 0 ≤ p0)
    (hcyl : ∀ U : Finset V, ∑ B, q B * (if U ⊆ B then 1 else 0) ≤ p0 ^ U.card) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (T : Finset V) :
    ∑ B, q B * ∏ v ∈ T, (if v ∈ B then 1 else r) ≤ (p0 + r) ^ T.card := by
  have hexp : ∀ B : Finset V, ∏ v ∈ T, (if v ∈ B then (1 : ℝ) else r) =
      ∑ U ∈ T.powerset, (if U ⊆ B then (1 - r) ^ U.card else 0) * r ^ (T.card - U.card) := by
    intro B
    have h1 : ∏ v ∈ T, (if v ∈ B then (1 : ℝ) else r) = ∏ v ∈ T, ((if v ∈ B then 1 - r else 0) + r) :=
      prod_congr rfl fun v _ => by split_ifs <;> ring
    rw [h1, prod_add]
    refine sum_congr rfl fun U hU => ?_
    rw [mem_powerset] at hU
    congr 1
    · by_cases hUB : U ⊆ B
      · rw [prod_congr rfl (fun v hv => (by simp [hUB hv] : (if v ∈ B then 1 - r else 0) = 1 - r)),
          prod_const]
        simp [hUB]
      · simp only [hUB, ↓reduceIte]
        obtain ⟨v, hvU, hvB⟩ := not_subset.1 hUB
        exact prod_eq_zero hvU (by simp [hvB])
    · rw [prod_const, card_sdiff_of_subset hU]
  have hr1' : 0 ≤ 1 - r := by linarith
  calc ∑ B, q B * ∏ v ∈ T, (if v ∈ B then 1 else r)
      = ∑ U ∈ T.powerset, ((1 - r) ^ U.card * r ^ (T.card - U.card)) *
          ∑ B, q B * (if U ⊆ B then 1 else 0) := by
        simp_rw [hexp, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun U _ => sum_congr rfl fun B _ => ?_
        split_ifs <;> ring
    _ ≤ ∑ U ∈ T.powerset, ((1 - r) ^ U.card * r ^ (T.card - U.card)) * p0 ^ U.card := by
        refine sum_le_sum fun U _ => mul_le_mul_of_nonneg_left (hcyl U) ?_
        exact mul_nonneg (pow_nonneg hr1' _) (pow_nonneg hr0 _)
    _ ≤ ∑ U ∈ T.powerset, p0 ^ U.card * r ^ (T.card - U.card) := by
        refine sum_le_sum fun U _ => ?_
        have h1 : (1 - r) ^ U.card ≤ 1 := pow_le_one₀ hr1' (by linarith)
        have h2 : 0 ≤ r ^ (T.card - U.card) * p0 ^ U.card := mul_nonneg (pow_nonneg hr0 _) (pow_nonneg hp0 _)
        nlinarith
    _ = (p0 + r) ^ T.card := sum_pow_mul_eq_add_pow p0 r T

/-- `e^{-λ cost(p)}` as a product over the visited sites. -/
theorem exp_walkCost_eq (Bad : Finset V) (lam : ℝ) {u v : V} (p : G.Walk u v) :
    Real.exp (-(lam * (walkCost G Bad p : ℝ))) =
      ∏ x ∈ p.support.tail.toFinset, (if x ∈ Bad then 1 else Real.exp (-lam)) := by
  rw [prod_ite, prod_const_one, one_mul, prod_const, ← Real.exp_nat_mul]
  unfold walkCost
  congr 1
  ring

/-! ## Counting walks -/

/-- At most `Δ^n` walks of length `n` start at `u`. -/
theorem sum_card_walks_le {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ) (n : ℕ) (u : V) :
    ∑ v, (G.finsetWalkLength n u v).card ≤ Δ ^ n := by
  induction n generalizing u with
  | zero =>
    rw [pow_zero]
    calc ∑ v, (G.finsetWalkLength 0 u v).card = (G.finsetWalkLength 0 u u).card := by
          refine sum_eq_single u (fun v _ hv => ?_) (fun h => absurd (mem_univ u) h)
          refine card_eq_zero.2 (eq_empty_of_forall_notMem fun p hp => hv ?_)
          exact (Walk.eq_of_length_eq_zero (mem_finsetWalkLength_iff.1 hp)).symm
      _ ≤ 1 := by
          refine card_le_one.2 fun p hp p' hp' => ?_
          rw [mem_finsetWalkLength_iff] at hp hp'
          rw [(Walk.length_eq_zero_iff.1 hp).eq_nil, (Walk.length_eq_zero_iff.1 hp').eq_nil]
  | succ n ih =>
    calc ∑ v, (G.finsetWalkLength (n + 1) u v).card
        ≤ ∑ v, ∑ w : G.neighborSet u, (G.finsetWalkLength n w v).card := by
          refine sum_le_sum fun v _ => ?_
          simp only [finsetWalkLength]
          refine card_biUnion_le.trans (le_of_eq ?_)
          simp
      _ = ∑ w : G.neighborSet u, ∑ v, (G.finsetWalkLength n w v).card := sum_comm
      _ ≤ ∑ _w : G.neighborSet u, Δ ^ n := sum_le_sum fun w _ => ih w
      _ = G.degree u * Δ ^ n := by rw [sum_const, card_univ, card_neighborSet_eq_degree, smul_eq_mul]
      _ ≤ Δ * Δ ^ n := Nat.mul_le_mul_right _ (hdeg u)
      _ = Δ ^ (n + 1) := by ring

/-! ## The Peierls bound -/

/-- **Peierls bound for the effective weight** (S). Random defect set with cylinder-dominated law `q`, degree `≤ Δ`,
`d ≤ dist_G(u, s)` for all `s ∈ S`: `E_q e^{-λ effDist(u, S)} ≤ ∑_{n ∈ [d, |V|)} (Δ (p₀ + e^{-λ}))^n`. -/
theorem expect_effWeight_le (hG : G.Preconnected) {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (q : Finset V → ℝ) (hq : ∀ B, 0 ≤ q B) {p0 : ℝ} (hp0 : 0 ≤ p0)
    (hcyl : ∀ U : Finset V, ∑ B, q B * (if U ⊆ B then 1 else 0) ≤ p0 ^ U.card)
    {lam : ℝ} (hlam : 0 ≤ lam) {S : Finset V} (hS : S.Nonempty) (u : V) {d : ℕ}
    (hd : ∀ s ∈ S, d ≤ G.dist u s) :
    ∑ B, q B * effWeight G B lam S u ≤
      ∑ n ∈ Ico d (Fintype.card V), ((Δ : ℝ) * (p0 + Real.exp (-lam))) ^ n := by
  classical
  set r := Real.exp (-lam)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  -- the sum over paths from `u` to `S` with length in `[d, |V|)`
  set F : Finset V → ℝ := fun B => ∑ s ∈ S, ∑ n ∈ Ico d (Fintype.card V),
    ∑ p ∈ (G.finsetWalkLength n u s).filter (fun p => p.IsPath),
      Real.exp (-(lam * (walkCost G B p : ℝ))) with hF
  have hstep1 : ∀ B, effWeight G B lam S u ≤ F B := by
    intro B
    obtain ⟨s, hs, p, hp⟩ := exists_walk_effDist hG B u hS
    set p' := p.bypass
    have hpath : p'.IsPath := p.bypass_isPath
    have hlen : p'.length ∈ Ico d (Fintype.card V) := by
      refine mem_Ico.2 ⟨(hd s hs).trans (SimpleGraph.dist_le p'), hpath.length_lt⟩
    have hmem : p' ∈ (G.finsetWalkLength p'.length u s).filter (fun p => p.IsPath) :=
      mem_filter.2 ⟨mem_finsetWalkLength_iff.2 rfl, hpath⟩
    have hcost : (walkCost G B p' : ℝ) ≤ effDist G B u S := by
      rw [← hp]; exact_mod_cast walkCost_bypass_le B p
    have hle : effWeight G B lam S u ≤ Real.exp (-(lam * (walkCost G B p' : ℝ))) :=
      Real.exp_le_exp.2 (by nlinarith)
    refine hle.trans ?_
    have h0 : ∀ s' (p'' : G.Walk u s'), 0 ≤ Real.exp (-(lam * (walkCost G B p'' : ℝ))) :=
      fun _ _ => (Real.exp_pos _).le
    refine le_trans ?_ (single_le_sum (fun s' _ => sum_nonneg fun _ _ => sum_nonneg fun p'' _ => h0 s' p'') hs)
    refine le_trans ?_ (single_le_sum (fun _ _ => sum_nonneg fun p'' _ => h0 s p'') hlen)
    exact single_le_sum (fun p'' _ => h0 s p'') hmem
  -- expectation of one path term
  have hpath_exp : ∀ s n (p : G.Walk u s), p ∈ (G.finsetWalkLength n u s).filter (fun p => p.IsPath) →
      ∑ B, q B * Real.exp (-(lam * (walkCost G B p : ℝ))) ≤ (p0 + r) ^ n := by
    intro s n p hp
    rw [mem_filter, mem_finsetWalkLength_iff] at hp
    simp_rw [exp_walkCost_eq]
    have := expect_prod_le q hp0 hcyl hr0 hr1 p.support.tail.toFinset
    rwa [card_tail_of_isPath hp.2, hp.1] at this
  have hx0 : 0 ≤ p0 + r := add_nonneg hp0 hr0
  calc ∑ B, q B * effWeight G B lam S u ≤ ∑ B, q B * F B :=
        sum_le_sum fun B _ => mul_le_mul_of_nonneg_left (hstep1 B) (hq B)
    _ = ∑ s ∈ S, ∑ n ∈ Ico d (Fintype.card V), ∑ p ∈ (G.finsetWalkLength n u s).filter (fun p => p.IsPath),
          ∑ B, q B * Real.exp (-(lam * (walkCost G B p : ℝ))) := by
        simp only [hF, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun s _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun n _ => ?_
        rw [sum_comm]
    _ ≤ ∑ s ∈ S, ∑ n ∈ Ico d (Fintype.card V),
          ∑ _p ∈ (G.finsetWalkLength n u s).filter (fun p => p.IsPath), (p0 + r) ^ n :=
        sum_le_sum fun s _ => sum_le_sum fun n _ => sum_le_sum fun p hp => hpath_exp s n p hp
    _ ≤ ∑ s ∈ S, ∑ n ∈ Ico d (Fintype.card V), ((G.finsetWalkLength n u s).card : ℝ) * (p0 + r) ^ n := by
        refine sum_le_sum fun s _ => sum_le_sum fun n _ => ?_
        rw [sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le _ _) (pow_nonneg hx0 _)
    _ = ∑ n ∈ Ico d (Fintype.card V), (∑ s ∈ S, ((G.finsetWalkLength n u s).card : ℝ)) * (p0 + r) ^ n := by
        rw [sum_comm]
        exact sum_congr rfl fun n _ => by rw [sum_mul]
    _ ≤ ∑ n ∈ Ico d (Fintype.card V), ((Δ : ℝ) ^ n) * (p0 + r) ^ n := by
        refine sum_le_sum fun n _ => mul_le_mul_of_nonneg_right ?_ (pow_nonneg hx0 _)
        calc ∑ s ∈ S, ((G.finsetWalkLength n u s).card : ℝ) ≤ ∑ s, ((G.finsetWalkLength n u s).card : ℝ) :=
              sum_le_sum_of_subset_of_nonneg (subset_univ S) fun _ _ _ => Nat.cast_nonneg _
          _ ≤ (Δ : ℝ) ^ n := by exact_mod_cast sum_card_walks_le hdeg n u
    _ = ∑ n ∈ Ico d (Fintype.card V), ((Δ : ℝ) * (p0 + r)) ^ n := sum_congr rfl fun n _ => (mul_pow _ _ _).symm

/-- **Peierls bound, closed form.** Under `x := Δ (p₀ + e^{-λ}) < 1`: `E_q e^{-λ effDist(u, S)} ≤ x^d / (1 − x)`. -/
theorem expect_effWeight_le_geom (hG : G.Preconnected) {Δ : ℕ} (hdeg : ∀ v, G.degree v ≤ Δ)
    (q : Finset V → ℝ) (hq : ∀ B, 0 ≤ q B) {p0 : ℝ} (hp0 : 0 ≤ p0)
    (hcyl : ∀ U : Finset V, ∑ B, q B * (if U ⊆ B then 1 else 0) ≤ p0 ^ U.card)
    {lam : ℝ} (hlam : 0 ≤ lam) {S : Finset V} (hS : S.Nonempty) (u : V) {d : ℕ}
    (hd : ∀ s ∈ S, d ≤ G.dist u s) (hx : (Δ : ℝ) * (p0 + Real.exp (-lam)) < 1) :
    ∑ B, q B * effWeight G B lam S u ≤
      ((Δ : ℝ) * (p0 + Real.exp (-lam))) ^ d / (1 - (Δ : ℝ) * (p0 + Real.exp (-lam))) := by
  refine (expect_effWeight_le hG hdeg q hq hp0 hcyl hlam hS u hd).trans ?_
  exact geom_sum_Ico_le_of_lt_one
    (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hp0 (Real.exp_pos _).le)) hx

end ProofPhase.Defects
