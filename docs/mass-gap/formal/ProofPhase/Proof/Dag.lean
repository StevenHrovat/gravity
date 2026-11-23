/-
P vs NP, the edge: the DAG-like size-width relation for resolution, as confinement times resolution (2026-11-23).
Released under Apache 2.0.

Paper: `docs/pnp/EDGE.md`, section 6.
-/

import ProofPhase.Proof.Cut

/-!
# DAG-like size-width (Ben-Sasson and Wigderson): confinement times resolution

**DAG-like proofs.** `RD F P C`: the clause `C` is derivable from `F` by resolution and weakening with every line in the
finite set `P`. A DAG-like refutation (lines reused freely) whose distinct lines form `P` gives `RD F P ∅`, so `P.card`
is at most its size.

**Restriction** (`RD.restr`): fixing a literal `ℓ` true maps a derivation from `F` with lines `P` to a derivation from
`F|ℓ` with lines `rP ℓ P` (the lines without `ℓ`, with `¬ℓ` deleted). Lines containing `ℓ` disappear.

**Main result** (`size_width`). Let the axioms have at most `w` literals, let the variables number `n`, and call a line
**fat** when it has more than `w + d` literals. If `F` has no refutation of width `w + d + b`, every DAG-like
refutation with line set `P` satisfies

  `(2n)^b ≤ |P| · (2n − (w + d + 1))^b`,   hence (`size_width_exp`)   `exp (b (w + d + 1) / 2n) ≤ |P|`.

The proof is the Ben-Sasson-Wigderson argument, in two terms:
* **confinement**: a fat line asserts more than `w + d` literals, so the most frequent literal sits in at least a
  `(w + d + 1) / 2n` share of the fat lines (`exists_heavy`, double counting);
* **resolution**: fixing that literal removes that share (`card_fat_rP_le`), and one step of width is paid for it
  (`WD.combine`). After `b` steps no fat line is left, unless `|P|` was at least `(1 − (w+d+1)/2n)^(−b)`.

**With the cut principle** (`dag_size_ge`): for a block system whose middle regions have `e` boundary variables
(`width_ge`, `Cut.lean`), every DAG-like refutation has `(2n)^b ≤ |P| (2n − (w+d+1))^b` whenever `w + d + b < e`.
With `d = b ≈ (e − w)/2` this is `|P| ≥ exp((e − w)^2 / (8n))` up to rounding: size exponential in
confinement squared over the number of variables.

**New here:** everything in this file.
-/

namespace ProofPhase.Proof

variable {α : Type*} [DecidableEq α]

/-- `RD F P C`: `C` is derivable from `F` by resolution and weakening, every line lying in `P`. -/
inductive RD (F : CNF α) (P : Finset (Clause α)) : Clause α → Prop
  | ax {A : Clause α} : A ∈ F → A ∈ P → RD F P A
  | res {C₁ C₂ : Clause α} (y : α × Bool) : RD F P C₁ → RD F P C₂ → y ∈ C₁ → nl y ∈ C₂ →
      C₁.erase y ∪ C₂.erase (nl y) ∈ P → RD F P (C₁.erase y ∪ C₂.erase (nl y))
  | weak {C D : Clause α} : RD F P C → C ⊆ D → D ∈ P → RD F P D

/-- The lines of `P` restricted by `ℓ`: lines containing `ℓ` are dropped, `¬ℓ` is deleted from the others. -/
def rP (ℓ : α × Bool) (P : Finset (Clause α)) : Finset (Clause α) :=
  (P.filter fun C => ℓ ∉ C).image fun C => C.erase (nl ℓ)

/-- The fat lines: more than `T` literals. -/
def fat (T : ℕ) (P : Finset (Clause α)) : Finset (Clause α) := P.filter fun C => T < C.card

theorem mem_rP {ℓ : α × Bool} {P : Finset (Clause α)} {C : Clause α} (hC : C ∈ P) (hℓ : ℓ ∉ C) :
    C.erase (nl ℓ) ∈ rP ℓ P :=
  Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr ⟨hC, hℓ⟩, rfl⟩

namespace RD

variable {F : CNF α} {P : Finset (Clause α)}

/-- **A thin DAG-like derivation is a width-bounded one.** -/
theorem toWD {W : ℕ} (hP : ∀ D ∈ P, D.card ≤ W) {C : Clause α} (h : RD F P C) : ∃ C' ⊆ C, WD F W C' := by
  induction h with
  | ax hA hAP => exact ⟨_, subset_rfl, WD.ax hA (hP _ hAP)⟩
  | @res C₁ C₂ y _ _ hy hny hR ih1 ih2 =>
    obtain ⟨P', hP's, hP'⟩ := ih1
    obtain ⟨Q', hQ's, hQ'⟩ := ih2
    by_cases hyP : y ∈ P'
    · by_cases hyQ : nl y ∈ Q'
      · have hsub : P'.erase y ∪ Q'.erase (nl y) ⊆ C₁.erase y ∪ C₂.erase (nl y) :=
          Finset.union_subset_union (Finset.erase_subset_erase _ hP's) (Finset.erase_subset_erase _ hQ's)
        exact ⟨_, hsub, WD.res y hP' hQ' hyP hyQ ((Finset.card_le_card hsub).trans (hP _ hR))⟩
      · exact ⟨Q', fun z hz => Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun e => hyQ (e ▸ hz), hQ's hz⟩),
          hQ'⟩
    · exact ⟨P', fun z hz => Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hyP (e ▸ hz), hP's hz⟩), hP'⟩
  | weak _ hCD _ ih =>
    obtain ⟨C', hC', h'⟩ := ih
    exact ⟨C', hC'.trans hCD, h'⟩

omit [DecidableEq α] in
theorem nl_inj {a b : α × Bool} (h : nl a = nl b) : a = b := by
  rw [← nl_nl a, h, nl_nl]

/-- **Restriction of a DAG-like derivation.** -/
theorem restr {ℓ : α × Bool} {C : Clause α} (h : RD F P C) :
    ℓ ∉ C → RD (ProofPhase.Proof.restrict ℓ F) (rP ℓ P) (C.erase (nl ℓ)) := by
  induction h with
  | ax hA hAP =>
    intro hℓ
    exact RD.ax (mem_restrict.mpr ⟨_, hA, hℓ, rfl⟩) (mem_rP hAP hℓ)
  | weak _ hCD hD ih =>
    intro hℓ
    exact RD.weak (ih fun h => hℓ (hCD h)) (Finset.erase_subset_erase _ hCD) (mem_rP hD hℓ)
  | @res C₁ C₂ y _ _ hy hny hR ih1 ih2 =>
    intro hℓ
    by_cases h1ℓ : ℓ ∈ C₁
    · have hyl : y = ℓ := by
        by_contra hne
        exact hℓ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun e => hne e.symm, h1ℓ⟩))
      have h2ℓ : ℓ ∉ C₂ := fun h => hℓ (Finset.mem_union_right _
        (Finset.mem_erase.mpr ⟨by rw [hyl]; exact ne_nl ℓ, h⟩))
      refine RD.weak (ih2 h2ℓ) (fun z hz => ?_) (mem_rP hR hℓ)
      obtain ⟨hz1, hz2⟩ := Finset.mem_erase.mp hz
      exact Finset.mem_erase.mpr ⟨hz1, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by rw [hyl]; exact hz1, hz2⟩)⟩
    · by_cases h2ℓ : ℓ ∈ C₂
      · have hyl : nl y = ℓ := by
          by_contra hne
          exact hℓ (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun e => hne e.symm, h2ℓ⟩))
        have hy' : y = nl ℓ := by rw [← hyl, nl_nl]
        refine RD.weak (ih1 h1ℓ) (fun z hz => ?_) (mem_rP hR hℓ)
        obtain ⟨hz1, hz2⟩ := Finset.mem_erase.mp hz
        exact Finset.mem_erase.mpr ⟨hz1, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by rw [hy']; exact hz1, hz2⟩)⟩
      · have hyn : y ≠ nl ℓ := fun e => h2ℓ (by rw [e, nl_nl] at hny; exact hny)
        have hyl : y ≠ ℓ := fun e => h1ℓ (e ▸ hy)
        have hnyl : nl y ≠ nl ℓ := fun e => hyl (nl_inj e)
        have heq : (C₁.erase (nl ℓ)).erase y ∪ (C₂.erase (nl ℓ)).erase (nl y) =
            (C₁.erase y ∪ C₂.erase (nl y)).erase (nl ℓ) := by
          ext z
          simp only [Finset.mem_union, Finset.mem_erase]
          tauto
        rw [← heq]
        exact RD.res y (ih1 h1ℓ) (ih2 h2ℓ) (Finset.mem_erase.mpr ⟨hyn, hy⟩) (Finset.mem_erase.mpr ⟨hnyl, hny⟩)
          (heq ▸ mem_rP hR hℓ)

end RD

/-- Restriction removes the fat lines containing `ℓ`. -/
theorem card_fat_rP_le (T : ℕ) (ℓ : α × Bool) (P : Finset (Clause α)) :
    (fat T (rP ℓ P)).card ≤ ((fat T P).filter fun C => ℓ ∉ C).card := by
  have hsub : fat T (rP ℓ P) ⊆ ((fat T P).filter fun C => ℓ ∉ C).image fun C => C.erase (nl ℓ) := by
    intro D hD
    obtain ⟨hDP, hDT⟩ := Finset.mem_filter.mp hD
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hDP
    obtain ⟨hCP, hℓC⟩ := Finset.mem_filter.mp hC
    refine Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hCP, ?_⟩, hℓC⟩, rfl⟩
    exact lt_of_lt_of_le hDT (Finset.card_erase_le)
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- **Confinement, by double counting**: some literal lies in at least a `(T + 1) / |L|` share of the fat lines. -/
theorem exists_heavy {T : ℕ} {Q : Finset (Clause α)} {L : Finset (α × Bool)} (hQL : ∀ C ∈ Q, C ⊆ L)
    (hT : ∀ C ∈ Q, T < C.card) (hQ : Q.Nonempty) :
    ∃ ℓ ∈ L, Q.card * (T + 1) ≤ L.card * (Q.filter fun C => ℓ ∈ C).card := by
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := Q) (t := L) (r := fun C z => z ∈ C)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at hdc
  have hcard : ∀ C ∈ Q, (L.filter fun z => z ∈ C).card = C.card := fun C hC => by
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (hQL C hC)]
  have hsum : Q.card * (T + 1) ≤ ∑ z ∈ L, (Q.filter fun C => z ∈ C).card := by
    rw [← hdc, Finset.sum_congr rfl hcard]
    have := Finset.card_nsmul_le_sum Q (fun C => C.card) (T + 1) (fun C hC => hT C hC)
    simpa [smul_eq_mul] using this
  obtain ⟨C0, hC0⟩ := hQ
  have hL : L.Nonempty := by
    have h0 : 0 < C0.card := lt_of_le_of_lt (Nat.zero_le _) (hT C0 hC0)
    obtain ⟨z, hz⟩ := Finset.card_pos.mp h0
    exact ⟨z, hQL C0 hC0 hz⟩
  by_contra hno
  push Not at hno
  have hlt := Finset.sum_lt_sum_of_nonempty hL hno
  rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hlt
  have := Nat.mul_le_mul_left L.card hsum
  omega

/-- The arithmetic of one restriction step. -/
theorem step_arith {M T a a' k b : ℕ} (hTM : T + 1 ≤ M) (hk : a' + k ≤ a) (hM : a * (T + 1) ≤ M * k)
    (h : a * (M - (T + 1)) ^ (b + 1) < M ^ (b + 1)) : a' * (M - (T + 1)) ^ b < M ^ b := by
  obtain ⟨r, rfl⟩ : ∃ r, M = T + 1 + r := ⟨M - (T + 1), by omega⟩
  have hr : T + 1 + r - (T + 1) = r := by omega
  rw [hr] at h ⊢
  have h0 := Nat.mul_le_mul_left (T + 1 + r) hk
  have h1 : (T + 1 + r) * a' ≤ a * r := by nlinarith
  have h2 : (T + 1 + r) * (a' * r ^ b) < (T + 1 + r) * (T + 1 + r) ^ b := by
    calc (T + 1 + r) * (a' * r ^ b) = ((T + 1 + r) * a') * r ^ b := by ring
      _ ≤ (a * r) * r ^ b := Nat.mul_le_mul_right _ h1
      _ = a * r ^ (b + 1) := by ring
      _ < (T + 1 + r) ^ (b + 1) := h
      _ = (T + 1 + r) * (T + 1 + r) ^ b := by ring
  exact Nat.lt_of_mul_lt_mul_left h2

omit [DecidableEq α] in
theorem thin {T : ℕ} {P : Finset (Clause α)} (h : (fat T P).card = 0) : ∀ C ∈ P, C.card ≤ T := by
  intro C hC
  by_contra hlt
  have : C ∈ fat T P := Finset.mem_filter.mpr ⟨hC, by omega⟩
  rw [Finset.card_eq_zero] at h
  rw [h] at this
  exact Finset.notMem_empty _ this

theorem size_width_aux (w d M : ℕ) (hTM : w + d + 1 ≤ M) :
    ∀ N b : ℕ, ∀ (F : CNF α) (P : Finset (Clause α)) (L : Finset (α × Bool)), L.card ≤ N → L.card ≤ M →
      (∀ A ∈ F, A.card ≤ w) → (∀ C ∈ P, C ⊆ L) → RD F P ∅ →
      (fat (w + d) P).card * (M - (w + d + 1)) ^ b < M ^ b → WD F (w + d + b) ∅ := by
  intro N
  induction N with
  | zero =>
    intro b F P L hLN _ _ hPL h _
    have hthin : ∀ C ∈ P, C.card ≤ w + d + b := fun C hC => by
      have := Finset.card_le_card (hPL C hC)
      omega
    obtain ⟨C', hC', hd⟩ := h.toWD hthin
    rwa [Finset.subset_empty.mp hC'] at hd
  | succ N ih =>
    intro b F P L hLN hLM hw hPL h hcnt
    by_cases ha : (fat (w + d) P).card = 0
    · have hthin : ∀ C ∈ P, C.card ≤ w + d + b := fun C hC => (thin ha C hC).trans (by omega)
      obtain ⟨C', hC', hd⟩ := h.toWD hthin
      rwa [Finset.subset_empty.mp hC'] at hd
    cases b with
    | zero => rw [pow_zero, pow_zero, mul_one] at hcnt; omega
    | succ b =>
      have hQ : (fat (w + d) P).Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero ha)
      obtain ⟨ℓ, hℓL, hheavy⟩ := exists_heavy (T := w + d) (Q := fat (w + d) P) (L := L)
        (fun C hC => hPL C (Finset.mem_filter.mp hC).1) (fun C hC => (Finset.mem_filter.mp hC).2) hQ
      have hL'c : ((L.erase ℓ).erase (nl ℓ)).card + 1 ≤ L.card := by
        have := Finset.card_erase_le (s := L.erase ℓ) (a := nl ℓ)
        have := Finset.card_erase_of_mem hℓL
        have := Finset.card_pos.mpr ⟨ℓ, hℓL⟩
        omega
      have hsplit : ((fat (w + d) P).filter fun C => ℓ ∈ C).card + ((fat (w + d) P).filter fun C => ℓ ∉ C).card =
          (fat (w + d) P).card := Finset.card_filter_add_card_filter_not _
      -- branch 1: `ℓ` true removes the heavy share
      have r1 : WD (ProofPhase.Proof.restrict ℓ F) (w + d + b) ∅ := by
        refine ih b _ (rP ℓ P) ((L.erase ℓ).erase (nl ℓ)) (by omega) (by omega) (card_restrict_le hw) (fun D hD z hz => ?_) ?_ ?_
        · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hD
          obtain ⟨hCP, hℓC⟩ := Finset.mem_filter.mp hC
          obtain ⟨hz1, hz2⟩ := Finset.mem_erase.mp hz
          exact Finset.mem_erase.mpr ⟨hz1, Finset.mem_erase.mpr ⟨fun e => hℓC (e ▸ hz2), hPL C hCP hz2⟩⟩
        · simpa using h.restr (ℓ := ℓ) (Finset.notMem_empty ℓ)
        · have := card_fat_rP_le (w + d) ℓ P
          exact step_arith hTM (a' := (fat (w + d) (rP ℓ P)).card) (by omega)
            (le_trans hheavy (Nat.mul_le_mul_right _ hLM)) hcnt
      -- branch 2: `ℓ` false keeps every fat line but removes the variable
      have r2 : WD (ProofPhase.Proof.restrict (nl ℓ) F) (w + d + (b + 1)) ∅ := by
        refine ih (b + 1) _ (rP (nl ℓ) P) ((L.erase ℓ).erase (nl ℓ)) (by omega) (by omega) (card_restrict_le hw)
          (fun D hD z hz => ?_) ?_ ?_
        · obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hD
          obtain ⟨hCP, hℓC⟩ := Finset.mem_filter.mp hC
          obtain ⟨hz1, hz2⟩ := Finset.mem_erase.mp hz
          rw [nl_nl] at hz1
          exact Finset.mem_erase.mpr ⟨fun e => hℓC (e ▸ hz2), Finset.mem_erase.mpr ⟨hz1, hPL C hCP hz2⟩⟩
        · simpa using h.restr (ℓ := nl ℓ) (Finset.notMem_empty (nl ℓ))
        · have h1 := card_fat_rP_le (w + d) (nl ℓ) P
          have h2 := Finset.card_filter_le (fat (w + d) P) (fun C => nl ℓ ∉ C)
          exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (h1.trans h2)) hcnt
      have r1' : WD (ProofPhase.Proof.restrict ℓ F) (w + (d + b)) ∅ := by rw [← Nat.add_assoc]; exact r1
      have r2' : WD (ProofPhase.Proof.restrict (nl ℓ) F) (w + (d + b + 1)) ∅ := by
        rw [show w + (d + b + 1) = w + d + (b + 1) by omega]; exact r2
      have := WD.combine hw ℓ r1' r2'
      rwa [show w + (d + b + 1) = w + d + (b + 1) by omega] at this

/-- **DAG-like size-width.** If `F` (axioms of at most `w` literals, `n` variables) has no refutation of width
`w + d + b`, every DAG-like refutation with line set `P` has `(2n)^b ≤ |P| (2n − (w + d + 1))^b`. -/
theorem size_width [Fintype α] {F : CNF α} {P : Finset (Clause α)} {w d b : ℕ} (hw : ∀ A ∈ F, A.card ≤ w)
    (hTM : w + d + 1 ≤ 2 * Fintype.card α) (h : RD F P ∅) (hW : ¬ WD F (w + d + b) ∅) :
    (2 * Fintype.card α) ^ b ≤ P.card * (2 * Fintype.card α - (w + d + 1)) ^ b := by
  by_contra hlt
  push Not at hlt
  have hcardL : (Finset.univ : Finset (α × Bool)).card = 2 * Fintype.card α := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, mul_comm]
  have hfat : (fat (w + d) P).card ≤ P.card := Finset.card_filter_le _ _
  exact hW (size_width_aux w d _ hTM _ b F P Finset.univ le_rfl hcardL.le hw (fun C _ => Finset.subset_univ C) h
    (lt_of_le_of_lt (Nat.mul_le_mul_right _ hfat) hlt))

/-- **The exponential form**: `exp (b (w + d + 1) / 2n) ≤ |P|`. -/
theorem size_width_exp [Fintype α] {F : CNF α} {P : Finset (Clause α)} {w d b : ℕ} (hw : ∀ A ∈ F, A.card ≤ w)
    (hTM : w + d + 1 ≤ 2 * Fintype.card α) (h : RD F P ∅) (hW : ¬ WD F (w + d + b) ∅) :
    Real.exp (b * ((w + d + 1 : ℕ) / (2 * Fintype.card α : ℕ) : ℝ)) ≤ P.card := by
  have hN := size_width hw hTM h hW
  set M := 2 * Fintype.card α with hMdef
  set T := w + d + 1 with hTdef
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hcast : ((M - T : ℕ) : ℝ) = (M : ℝ) - T := by rw [Nat.cast_sub hTM]
  have hN' : (M : ℝ) ^ b ≤ P.card * ((M : ℝ) - T) ^ b := by
    rw [← hcast]; exact_mod_cast hN
  set x : ℝ := (T : ℝ) / M with hx
  have hrx : ((M : ℝ) - T) / M = 1 - x := by rw [hx]; field_simp
  have hr0 : 0 ≤ ((M : ℝ) - T) / M := by
    apply div_nonneg _ hM.le
    have : (T : ℝ) ≤ M := by exact_mod_cast hTM
    linarith
  have hkey : (1 : ℝ) ≤ P.card * (((M : ℝ) - T) / M) ^ b := by
    rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hM b), one_mul]
    exact hN'
  have hexp : (((M : ℝ) - T) / M) ^ b ≤ Real.exp (-x) ^ b := by
    apply pow_le_pow_left₀ hr0
    rw [hrx]
    linarith [Real.add_one_le_exp (-x)]
  rw [← Real.exp_nat_mul] at hexp
  have hP : (0 : ℝ) ≤ P.card := by positivity
  have h3 : (1 : ℝ) ≤ P.card * Real.exp (↑b * -x) := hkey.trans (mul_le_mul_of_nonneg_left hexp hP)
  have h4 : Real.exp (↑b * -x) = (Real.exp (b * x))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  rw [h4, ← div_eq_mul_inv, one_le_div (Real.exp_pos _)] at h3
  exact h3

/-- **Confinement times resolution, for block systems.** With the cut principle (`width_ge`): if every middle region
has `e` boundary variables, every DAG-like refutation has `(2n)^b ≤ |P| (2n − (w + d + 1))^b` whenever
`w + d + b < e`. -/
theorem dag_size_ge [Fintype α] {V : Type*} [Fintype V] [DecidableEq V] {Ax : V → CNF α} {K e w d b : ℕ}
    (hK : 1 ≤ K) (hKV : K < Fintype.card V)
    (hsat : ∀ S : Finset V, S ≠ Finset.univ → ¬ Implies Ax S ∅)
    (hexp : ∀ S : Finset V, K < 2 * S.card → S.card ≤ K → ∃ B : Finset α, e ≤ B.card ∧
      ∀ x ∈ B, ∃ u ∈ S, (∀ a, SatB Ax (flip x a) u ↔ ¬ SatB Ax a u) ∧
        ∀ v ∈ S, v ≠ u → ∀ a, SatB Ax (flip x a) v ↔ SatB Ax a v)
    (hw : ∀ A ∈ allAx Ax, A.card ≤ w) (hwe : w + d + b < e) (hTM : w + d + 1 ≤ 2 * Fintype.card α)
    {P : Finset (Clause α)} (h : RD (allAx Ax) P ∅) :
    (2 * Fintype.card α) ^ b ≤ P.card * (2 * Fintype.card α - (w + d + 1)) ^ b :=
  size_width hw hTM h fun hW => by
    have := width_ge hK hKV hsat hexp hW
    omega

end ProofPhase.Proof
