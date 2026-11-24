/-
P vs NP, proof systems, Lean part 4: Tseitin formulas, the conserved parity flux, and their width bound (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/PROOF-SYSTEMS.md`, section 5.
-/

import ProofPhase.Proof.Cut

/-!
# Tseitin formulas: a conserved flux whose refutation must carry it across a boundary

**Setting.** A finite set `V` of vertices, a finite set `E` of edges (the variables), `I v ⊆ E` the edges at `v`, and a
charge `c v` (`true` = odd). The Tseitin constraint at `v` says that the number of true edges at `v` has parity `c v`:
the edge values are a flow mod 2 whose divergence at `v` is `c v` (Kirchhoff's law mod 2). When the total charge is odd
the constraints contradict each other (every edge is counted at both of its ends), and the formula is unsatisfiable.
It is encoded blockwise as a CNF (`block`): one clause for every wrong-parity pattern of the edges at `v`.

**Proved here.**
* `satB_block_iff`: the CNF block at `v` holds exactly when the parity at `v` is `c v`.
* `toggle`, `invisible`: flipping an edge at `u` toggles the constraint at `u`; flipping an edge not at `v` leaves `v`
  unchanged. These are the two properties the cut principle (`Cut.lean`) asks of a boundary variable.
* `width_ge`: **every resolution refutation of a Tseitin formula has width at least the edge expansion**: if every
  vertex set `S` of middle size (`K < 2 |S| ≤ 2 K`) has at least `e` boundary edges (edges at exactly one vertex of
  `S`), and every proper sub-system is satisfiable, then width `≥ e`; `tl_size_ge`: then every tree-like refutation
  has more than `2^(e - 1 - w)` leaves, `w` the largest vertex degree.

**Hypotheses, stated:** satisfiability of every proper sub-system (`hsat`; classical for a connected graph: flip a path
from a violated vertex to a vertex outside `S`) and the expansion count (`hexp`; for an explicit expander family it
is a theorem of graph theory, not formalized). With a family of bounded-degree expanders (`e` linear in `|V|`, `w`
bounded) this is the exponential tree-like lower bound; the DAG-like bound needs the DAG size-width relation, not
formalized (`SizeWidth.lean`).

**New here:** everything in this file.
-/

namespace ProofPhase.Proof

namespace Tseitin

variable {E V : Type*} [DecidableEq E] [Fintype V] [DecidableEq V] (I : V → Finset E) (c : V → Bool)

/-- The parity of the true edges at `v` (`true` = odd). -/
def odd (a : E → Bool) (v : V) : Bool := decide (((I v).filter fun e => a e = true).card % 2 = 1)

/-- The clause excluding the pattern "exactly the edges of `T` are true" on the edges `J`. -/
def patClause (J T : Finset E) : Clause E := J.image fun e => (e, decide (e ∉ T))

/-- The Tseitin block at `v`: one clause for each wrong-parity pattern of the edges at `v`. -/
def block (v : V) : CNF E :=
  ((I v).powerset.filter fun T => decide (T.card % 2 = 1) ≠ c v).image (patClause (I v))

variable {I c}

omit [DecidableEq V] [Fintype V] in
theorem falsifies_patClause {J T : Finset E} {a : E → Bool} :
    Falsifies a (patClause J T) ↔ ∀ e ∈ J, a e = decide (e ∈ T) := by
  simp only [Falsifies, patClause, Finset.mem_image, forall_exists_index, and_imp]
  constructor
  · intro h e he
    have := h _ e he rfl
    by_cases heT : e ∈ T <;> simp_all
  · rintro h l e he rfl
    have := h e he
    by_cases heT : e ∈ T <;> simp_all

omit [DecidableEq V] [Fintype V] in
/-- **The CNF block is the parity constraint.** -/
theorem satB_block_iff (a : E → Bool) (v : V) : SatB (block I c) a v ↔ odd I a v = c v := by
  constructor
  · intro h
    by_contra hne
    refine h (patClause (I v) ((I v).filter fun e => a e = true)) ?_ ?_
    · refine Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩, rfl⟩
      exact hne
    · rw [falsifies_patClause]
      intro e he
      by_cases hae : a e = true <;> simp [he, hae]
  · intro h A hA hF
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hTI, hTc⟩ := Finset.mem_filter.mp hT
    rw [Finset.mem_powerset] at hTI
    rw [falsifies_patClause] at hF
    have hfil : ((I v).filter fun e => a e = true) = T := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, hae⟩
        have := hF e he
        rw [hae] at this
        exact of_decide_eq_true this.symm
      · intro heT
        exact ⟨hTI heT, by rw [hF e (hTI heT)]; exact decide_eq_true heT⟩
    apply hTc
    rw [← h, odd, hfil]

omit [DecidableEq V] [Fintype V] in
/-- **An edge at `u` toggles the constraint at `u`.** -/
theorem toggle {x : E} {u : V} (hx : x ∈ I u) (a : E → Bool) :
    SatB (block I c) (flip x a) u ↔ ¬ SatB (block I c) a u := by
  rw [satB_block_iff, satB_block_iff]
  have key : odd I (flip x a) u = !odd I a u := by
    unfold odd
    have hfl : ∀ e, flip x a e = if e = x then !a x else a e := fun e => by
      by_cases h : e = x
      · subst h; simp [flip]
      · simp [flip, h]
    cases hax : a x
    · -- x becomes true: the filter gains x
      have hset : ((I u).filter fun e => flip x a e = true) = insert x ((I u).filter fun e => a e = true) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_insert, hfl]
        by_cases h : e = x
        · subst h; simp [hax, hx]
        · simp [h]
      have hnot : x ∉ (I u).filter fun e => a e = true := by simp [hax]
      rw [hset, Finset.card_insert_of_notMem hnot]
      by_cases hp : ((I u).filter fun e => a e = true).card % 2 = 1 <;> simp [hp] <;> omega
    · -- x becomes false: the filter loses x
      have hmem : x ∈ (I u).filter fun e => a e = true := by simp [hax, hx]
      have hset : ((I u).filter fun e => flip x a e = true) = ((I u).filter fun e => a e = true).erase x := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_erase, hfl]
        by_cases h : e = x
        · subst h; simp [hax]
        · simp [h]
      have hpos := Finset.card_pos.mpr ⟨x, hmem⟩
      rw [hset, Finset.card_erase_of_mem hmem]
      by_cases hp : ((I u).filter fun e => a e = true).card % 2 = 1 <;> simp [hp] <;> omega
  rw [key]
  cases odd I a u <;> cases c u <;> simp

omit [DecidableEq V] [Fintype V] in
/-- **An edge not at `v` is invisible to `v`.** -/
theorem invisible {x : E} {v : V} (hx : x ∉ I v) (a : E → Bool) :
    SatB (block I c) (flip x a) v ↔ SatB (block I c) a v := by
  have hset : ((I v).filter fun e => flip x a e = true) = ((I v).filter fun e => a e = true) :=
    Finset.filter_congr fun e he => by
      have hex : e ≠ x := fun h => hx (h ▸ he)
      simp [flip, Function.update_of_ne hex]
  rw [satB_block_iff, satB_block_iff, odd, odd, hset]

variable [Fintype E]

/-- The boundary of a vertex set `S`: the edges at exactly one vertex of `S`. -/
def boundary (I : V → Finset E) (S : Finset V) : Finset E :=
  Finset.univ.filter fun x => ∃ u ∈ S, x ∈ I u ∧ ∀ v ∈ S, v ≠ u → x ∉ I v

/-- **Width at least the edge expansion.** -/
theorem width_ge {K e W : ℕ} (hK : 1 ≤ K) (hKV : K < Fintype.card V)
    (hsat : ∀ S : Finset V, S ≠ Finset.univ → ∃ a : E → Bool, ∀ v ∈ S, odd I a v = c v)
    (hexp : ∀ S : Finset V, K < 2 * S.card → S.card ≤ K → e ≤ (boundary I S).card)
    (h : WD (allAx (block I c)) W ∅) : e ≤ W := by
  refine ProofPhase.Proof.width_ge hK hKV (fun S hS hImp => ?_) (fun S h1 h2 => ⟨boundary I S, hexp S h1 h2, ?_⟩) h
  · obtain ⟨a, ha⟩ := hsat S hS
    exact hImp a (fun v hv => (satB_block_iff a v).mpr (ha v hv)) (falsifies_empty a)
  · intro x hx
    obtain ⟨u, hu, hxu, hrest⟩ := (Finset.mem_filter.mp hx).2
    exact ⟨u, hu, toggle hxu, fun v hv hvu => invisible (hrest v hv hvu)⟩

/-- **Tree-like size at least `2^(e - 1 - w)`**, with `w` the largest degree (every clause of the block at `v` has
`|I v|` literals). -/
theorem tl_size_ge {K e w : ℕ} (hK : 1 ≤ K) (hKV : K < Fintype.card V)
    (hsat : ∀ S : Finset V, S ≠ Finset.univ → ∃ a : E → Bool, ∀ v ∈ S, odd I a v = c v)
    (hexp : ∀ S : Finset V, K < 2 * S.card → S.card ≤ K → e ≤ (boundary I S).card)
    (hdeg : ∀ v, (I v).card ≤ w) (hwe : w < e) {s : ℕ} (h : TL (allAx (block I c)) ∅ s) :
    2 ^ (e - 1 - w) < s := by
  have hw : ∀ A ∈ allAx (block I c), A.card ≤ w := by
    intro A hA
    obtain ⟨v, -, hAv⟩ := Finset.mem_biUnion.mp hA
    obtain ⟨T, -, rfl⟩ := Finset.mem_image.mp hAv
    exact Finset.card_image_le.trans (hdeg v)
  refine tl_size_gt hw (by omega) (fun hW => ?_) h
  have := width_ge hK hKV hsat hexp hW
  omega

end Tseitin

end ProofPhase.Proof
