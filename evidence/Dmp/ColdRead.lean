import Dmp.Gate
import Dmp.Record
import Dmp.Standing
import Dmp.Floor
import Dmp.Field
import Dmp.Layer
import Dmp.Recipe
import Dmp.Theory
import Dmp.Complete
import Dmp.Layouts

/-!
# The cold read: counter-models against the physics claims (docs/cold-read-physics.md)

A second, independent attack (C22: "proven" is an act with two witnesses) on the physics drafts (gravity#17, #18, #19, #20) and on
the owner's deductions of 2026-10-27, written blind to the first attack. Every declaration here carries the prefix `cr_` (or `Cr`),
imports only files on `main`, and is named for what it proves. Nothing here changes DMP or the files it imports. Each section is a
counter-model (the axioms as modelled hold and the claim fails), an arithmetic on record, or the statement of what an
existing theorem does and does not say. The targets, steelmen, attacks and verdicts are in docs/cold-read-physics.md; the labels R1 to R29
below are the labels of its table rows.
-/

namespace Dmp

/-! ## R1. "No hair by the type": a record that carries content keeps K1, K2 and K3

`Physics.Entry.ext` (gravity#17, claim B2) says two entries that agree on time and verdicts are equal, and reads this as DMP's
no-hair theorem "by the type". The same step with a content field in the entry keeps every law of Gate.lean and Record.lean, so
the content-free readout is a choice of type, not a consequence of the axioms as modelled. -/

/-- A record entry with one more field. K1 to K3 say nothing about it. -/
structure CrEntry where
  t : Nat
  v1 : Verdict
  v2 : Verdict
  outcome : Verdict
  content : Nat
  deriving DecidableEq, Repr

/-- The state with the content-carrying record. -/
structure CrState where
  log : List CrEntry
  performed : Nat

/-- Record.lean's `step`, with the request's content written into the entry. -/
def cr_step (j1 j2 : Evidence → Verdict) (s : CrState) (r : Request) (content : Nat) : CrState :=
  let v1 := guard j1 r.e1 r.t
  let v2 := guard j2 r.e2 r.t
  let o := gate v1 v2
  { log := s.log ++ [⟨r.t, v1, v2, o, content⟩],
    performed := if o = .pass then s.performed + 1 else s.performed }

/-- K3 with content in the entry: exactly one entry per request. -/
theorem cr_step_records_once (j1 j2 : Evidence → Verdict) (s : CrState) (r : Request) (c : Nat) :
    (cr_step j1 j2 s r c).log.length = s.log.length + 1 := by
  simp [cr_step]

/-- K1 and K2 with content in the entry: an act is performed only with both witnesses on good evidence. -/
theorem cr_performed_only_with_both (j1 j2 : Evidence → Verdict) (s : CrState) (r : Request) (c : Nat)
    (h : (cr_step j1 j2 s r c).performed = s.performed + 1) : r.e1.ok r.t = true ∧ r.e2.ok r.t = true := by
  simp only [cr_step] at h
  split at h
  · rename_i hp
    have := act_needs_both_with_evidence j1 j2 r.e1 r.e2 r.t hp
    exact ⟨this.1, this.2.1⟩
  · omega

/-- And the readout is no longer content-free: two entries that agree on the time and the three verdicts differ. So `Entry.ext`
    is a fact about the chosen type; "no hair" is a definition of the model, not a theorem of the axioms. -/
theorem cr_no_hair_is_by_the_type :
    ∃ e e' : CrEntry, e.t = e'.t ∧ e.v1 = e'.v1 ∧ e.v2 = e'.v2 ∧ e.outcome = e'.outcome ∧ e ≠ e' :=
  ⟨⟨0, .pass, .pass, .pass, 0⟩, ⟨0, .pass, .pass, .pass, 1⟩, rfl, rfl, rfl, rfl, by decide⟩

/-! ## R2. T32's mass is coupled: a line added below changes the mass above

gravity#17 section 4.1 (`NoGo.dmp_field_isolated`) says DMP's field is uncoupled, reading `Field.Held.mass` as a number carried by
each standing. T32 defines mass as "one plus the number of members that derive through it", and Theory.lean computes it so
(`Recipe.mass`). Under that definition the mass at the root changes when a line is laid under a descendant: the field of T32 is
coupled, one way, along the chain. -/

/-- Layout A of Layouts.lean with one more information layer laid under its knowledge layer. -/
def crLayoutA5 : Recipe := Layouts.layoutA.extend (Layouts.line .information Layouts.knowledgeDot (some 1))

/-- The galaxy's mass before and after: 4 becomes 5. -/
theorem cr_mass_at_root_changes_when_a_line_is_added_below :
    Layouts.layoutA.mass 0 = 4 ∧ crLayoutA5.mass 0 = 5 := ⟨by decide, by decide⟩

/-- The extension is well formed and proven under the full ledger, so this is a configuration Gravity marks proven, not a corner. -/
theorem cr_extended_layout_is_proven : crLayoutA5.verdict Layouts.classes Layouts.allAgree = .proven := by decide

/-! ## R3. `NoGoVector.gravity_has_no_edge` proves `∀ dist, ∃ M`; the field of one fixed mass, in the same whole units, has an edge

The theorem of gravity#17 chooses the mass after the distance. For a fixed mass the toy field `M / dist²` in whole units is zero
beyond a finite distance, so the encoding does not say what its name says; "no edge" needs real numbers the file does not have. -/

theorem cr_toy_field_of_fixed_mass_has_an_edge (M : Nat) : ∃ dist : Nat, 0 < dist ∧ M / (dist * dist) = 0 := by
  refine ⟨M + 1, Nat.succ_pos M, Nat.div_eq_of_lt ?_⟩
  have h : M + 1 ≤ (M + 1) * (M + 1) := Nat.le_mul_self (M + 1)
  omega

/-! ## R4. `Ground.pressed_collapse` has no pressing in its statement

Its hypotheses are two good evidences; its conclusion is one judge that passes both. Neither mentions the pair. The same
conclusion holds for a minted pair, and a pressed pair with refusing judges passes nothing: in Ground.lean the owner of a witness
and the judgment of a witness are never connected (`controls` is a proposition about owner numbers, `guard` takes a judge). The
connection exists only in Layer.lean (`bend`), which is the theorem that carries T-P. -/

/-- The conclusion of `pressed_collapse`, for a minted pair. -/
theorem cr_pressed_collapse_conclusion_holds_for_a_minted_pair (p : Pair) (_hm : p.minted) (e1 e2 : Evidence) (t : Nat)
    (h1 : e1.ok t = true) (h2 : e2.ok t = true) : ∃ j : Evidence → Verdict, gate (guard j e1 t) (guard j e2 t) = .pass :=
  pressed_collapse e1 e2 t h1 h2

/-- A pressed pair whose two judges refuse passes nothing: the pressing as modelled in Ground.lean forces no collapse either. -/
theorem cr_pressed_pair_with_refusing_judges_passes_nothing (p : Pair) (_hp : p.outOfSpec) (e1 e2 : Evidence) (t : Nat) :
    gate (guard (fun _ => .refuse) e1 t) (guard (fun _ => .refuse) e2 t) ≠ .pass := by
  intro h
  have := (gate_pass_iff _ _).mp h
  simp [guard] at this

/-! ## R5. `Recipe.dmpComplete`, once `agree` is read as the input it is

Complete.lean proves `verdict = proven ↔ wf ∧ ∀ i < n, agree i = true`. The ledger `agree` is a function of the line number alone:
it cannot see the line it certifies. -/

/-- Every well-formed recipe is proven under the ledger that says yes to every index. -/
theorem cr_wf_is_proven_under_a_yes_ledger (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) :
    r.verdict fcl (fun _ => true) = .proven :=
  (Recipe.verdict_proven_iff fcl r _).mpr ⟨hwf, fun _ _ => rfl⟩

/-- Two well-formed recipes with the same number of lines get the same verdict under every ledger, whatever their lines, kinds and
    Dualities: "both chains prove it" is modelled as a function of the line number, blind to what the line is. -/
theorem cr_ledger_is_blind_to_the_lines (fcl : List FailureClass) (r r' : Recipe) (hwf : r.wf fcl) (hwf' : r'.wf fcl)
    (hn : r.n = r'.n) (agree : Nat → Bool) : r.verdict fcl agree = r'.verdict fcl agree := by
  simp [Recipe.verdict, (Recipe.wfB_iff fcl r).mpr hwf, (Recipe.wfB_iff fcl r').mpr hwf', hn]

/-! ## R6. A system in which nothing ever happens keeps every theorem

Axiom 1's balance "is the one commitment that asks for something to happen". The verdict takes no judge and no request as an
argument, and two judges that refuse everything perform nothing over any run: a proven configuration that never acts is a model of
the axioms as modelled. The empty recipe is proven too (`Cmb.empty_recipe_proven`, finding F9). -/

/-- Two refusing judges perform no act, whatever the requests. -/
theorem cr_refusing_judges_perform_nothing (rs : List Request) :
    ∀ s : State, (run (fun _ => .refuse) (fun _ => .refuse) s rs).performed = s.performed := by
  induction rs with
  | nil => intro s; rfl
  | cons r rs ih =>
    intro s
    simp only [run]
    rw [ih]
    simp [step, guard, gate, Verdict.stricter, Verdict.rank]

/-- Layout A is proven, and under refusing judges nothing ever happens in it: safety is proven, liveness is not stated. -/
theorem cr_proven_and_nothing_happens :
    Layouts.layoutA.verdict Layouts.classes Layouts.allAgree = .proven ∧
    ∀ rs s, (run (fun _ => .refuse) (fun _ => .refuse) s rs).performed = s.performed :=
  ⟨rfl, fun rs s => cr_refusing_judges_perform_nothing rs s⟩

/-! ## R7. K1 to K3 as modelled let the same message pass twice

C2.L3 (no replay) is listed as derived from Axiom 2 ("evidence is live for one point of use"). In the model of Axiom 2 the same
request, presented twice with evidence read live both times, is performed twice: no replay needs a memory of the first answer,
which Axiom 2 says is never evidence. The replay memory of R1Model.lean is construction, not a theorem of the axioms. -/

theorem cr_same_request_twice_performs_twice (j1 j2 : Evidence → Verdict) (s : State) (r : Request)
    (h1 : r.e1.ok r.t = true) (h2 : r.e2.ok r.t = true) (hj1 : j1 r.e1 = .pass) (hj2 : j2 r.e2 = .pass) :
    (run j1 j2 s [r, r]).performed = s.performed + 2 := by
  simp [run, step, guard, h1, h2, hj1, hj2, gate, Verdict.stricter, Verdict.rank]

/-! ## R8. "Counts always" (Axiom 3) says more than "random bytes of the same length" (T31)

The record's count distinguishes two histories of the same inside that random bytes of one length would not, and every entry
carries its time (`Record.step_records_at_act`). The floor of T31 is therefore not the whole emission: the counts and their times
are a channel Axiom 3 opens by design. -/

theorem cr_count_distinguishes_histories (j1 j2 : Evidence → Verdict) (s : State) (rs rs' : List Request)
    (h : rs.length ≠ rs'.length) : (run j1 j2 s rs).log.length ≠ (run j1 j2 s rs').log.length := by
  rw [run_records_all, run_records_all]
  omega

/-! ## R9. In DMP the crossing is not permanent: a contained item is offered re-admission (T27)

Deduction 9 says the crossing "hashes it to its existence permanently". Floor.lean offers re-admission on every contained item. -/

theorem cr_contained_item_is_offered_readmission (i : Item) (h : i.contained = true) : offered i .readmit = true := by
  simp [offered, h]

/-! ## R10. Axiom 3's tree is never a manifoldlike causal set: any two ancestors of a line are comparable

Level 0k of gravity#19 reads Axiom 3's hierarchy as a causal set. In a causal set sprinkled into a spacetime of two or more
dimensions, an element has ancestors that are incomparable (spacelike) to each other; in a recipe, every line's ancestors lie on one
chain. -/

/-- The chain of a parent is inside the chain of its child. -/
theorem cr_chain_parent_sub (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (k p : Nat) (hk : k < r.n)
    (hp : (r.line k).parent = some p) (j : Nat) (hj : j ∈ r.chain p) : j ∈ r.chain k := by
  rw [r.chain_unfold fcl hwf k hk, hp]
  exact List.mem_cons_of_mem k hj

/-- Any two lines on the chain of a line are comparable: one is on the chain of the other. -/
theorem cr_ancestors_are_comparable (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) :
    ∀ k, k < r.n → ∀ i j, i ∈ r.chain k → j ∈ r.chain k → i ∈ r.chain j ∨ j ∈ r.chain i := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk i j hi hj
    have hu := r.chain_unfold fcl hwf k hk
    cases hp : (r.line k).parent with
    | none =>
      rw [hp] at hu
      simp only [] at hu
      rw [hu] at hi hj
      simp only [List.mem_singleton] at hi hj
      rw [hi, hj]
      exact Or.inl (r.chain_head k)
    | some p =>
      have hok := (hwf k hk).1
      rw [hp] at hok
      have hpk : p < k := hok.1
      rw [hp] at hu
      rw [hu] at hi hj
      simp only [List.mem_cons] at hi hj
      cases hi with
      | inl hik =>
        rw [hik]
        cases hj with
        | inl hjk => rw [hjk]; exact Or.inl (r.chain_head k)
        | inr hjp => exact Or.inr (cr_chain_parent_sub fcl r hwf k p hk hp j hjp)
      | inr hip =>
        cases hj with
        | inl hjk => rw [hjk]; exact Or.inl (cr_chain_parent_sub fcl r hwf k p hk hp i hip)
        | inr hjp => exact ih p hpk (by omega) i j hip hjp

/-! ## R11. The layer below never reaches the decision above

Deduction 5 says the keys of the layer below have "effects on our information". A line's decision is the meet along its chain, which
walks upward only (`Recipe.chain_le`): whatever a later line answers, an earlier line decides the same. -/

theorem cr_child_never_votes_on_parent (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (i k : Nat) (hi : i < r.n)
    (hik : i < k) (v : Nat → Verdict) (a : Verdict) :
    r.decide (fun j => if j = k then a else v j) i = r.decide v i := by
  unfold Recipe.decide
  congr 1
  apply List.map_congr_left
  intro j hj
  have hle := r.chain_le fcl hwf i hi j hj
  have : j ≠ k := by omega
  simp [this]

/-! ## R12. Five lines and a compliant act do not make a compliant system (deduction 6, T35)

A configuration with five lines passes an act at every line and is unproven when one line is not carried by both chains; a
configuration with a pressed root passes acts at every line and is out of spec. The act says nothing about the system. -/

/-- A ledger that does not carry line 4. -/
def cr_ledgerMissing4 : Nat → Bool := fun i => i != 4

theorem cr_five_lines_one_pass_not_complete :
    crLayoutA5.n = 5 ∧ crLayoutA5.decide (fun _ => .pass) 4 = .pass ∧
    crLayoutA5.verdict Layouts.classes cr_ledgerMissing4 = .unproven :=
  ⟨rfl, by decide, by decide⟩

/-- Layout B (a pressed root) with the same fifth line. -/
def crLayoutB5 : Recipe := Layouts.layoutB.extend (Layouts.line .information Layouts.knowledgeDot (some 1))

theorem cr_pressed_system_still_passes_acts :
    crLayoutB5.verdict Layouts.classes Layouts.allAgree = .outOfSpec ∧ crLayoutB5.decide (fun _ => .pass) 4 = .pass :=
  ⟨by decide, by decide⟩

/-! ## R13. "Independent but entangled" (deduction 7): a shared source is a shared cause (T29)

Two systems are entangled only through a shared quantum source or a past interaction; in DMP's vocabulary a shared source is a
member of a failure class, and once that class is declared the two are not independent. -/

theorem cr_shared_source_is_not_independent (fcl : List FailureClass) (source m : Nat) (w1 w2 : Witness)
    (h1 : w1.member source = m) (h2 : w2.member source = m) : ¬ independent (source :: fcl) w1 w2 :=
  shared_cause_breaks_independence fcl source w1 w2 (h1.trans h2.symm)

/-! ## R14. Extension is not proof (deduction 7: "all further ones are proven by extension")

`Complete.proven_extend` needs the ledger's yes for the new line as a hypothesis; without it the extension unproves the whole. -/

theorem cr_extension_without_the_ledger_unproves (fcl : List FailureClass) (r : Recipe) (l : Line) (agree : Nat → Bool)
    (ha : agree r.n = false) : (r.extend l).verdict fcl agree ≠ .proven :=
  (r.extend l).one_unproven_line_unproves fcl agree r.n (Nat.lt_succ_self r.n) ha

/-! ## R15. Level 0s: Bekenstein's bound "from Landauer plus collapse", with the temperature inserted

Landauer's price is k T ln 2 per bit. With the temperature free, the bits an energy buys are unbounded (a cold enough bath). With the
Hawking temperature inserted at the final mass, the count is twice the area law: the derivation exceeds the bound it was to derive.
The first law integrated, dS = β(E) dE, gives the area law, and that is Bardeen, Carter and Hawking's first law, not Landauer's.
Units: Planck units with π dropped, so β_H = 8M, A/4 = 4M². -/

/-- Bits bought by energy `E` at coldness `β` (β = 1/kT, reciprocal energy units); ln 2 ≈ 693/1000. -/
def cr_landauerBits (E β : Nat) : Nat := E * β * 1000 / 693

/-- For any energy and any target count there is a coldness at which the energy buys the target: Landauer alone bounds nothing. -/
theorem cr_landauer_with_free_temperature_bounds_nothing (E : Nat) (hE : 1 ≤ E) (N : Nat) : ∃ β, N ≤ cr_landauerBits E β := by
  refine ⟨N, ?_⟩
  unfold cr_landauerBits
  rw [Nat.le_div_iff_mul_le (by decide : 0 < 693)]
  have h1 : N * 693 ≤ N * 1000 := Nat.mul_le_mul_left N (by decide)
  have h2 : N * 1000 ≤ E * N * 1000 := by
    have : N ≤ E * N := by
      calc N = 1 * N := (Nat.one_mul N).symm
        _ ≤ E * N := Nat.mul_le_mul_right N hE
    exact Nat.mul_le_mul_right 1000 this
  exact Nat.le_trans h1 h2

/-- The inverse Hawking temperature of a black hole of mass `M`: β = 8M (π dropped). -/
def cr_betaHawking (M : Nat) : Nat := 8 * M

/-- Landauer's count at the endpoint: the whole energy `M` at the final temperature. -/
def cr_endpointCount (M : Nat) : Nat := M * cr_betaHawking M

/-- The first law integrated in unit steps of energy: Σ_{m=1}^{M} β(m). -/
def cr_firstLawCount : Nat → Nat
  | 0 => 0
  | M + 1 => cr_firstLawCount M + cr_betaHawking (M + 1)

/-- The Bekenstein–Hawking entropy A/4 in the same units: 4M². -/
def cr_bekensteinHawking (M : Nat) : Nat := 4 * (M * M)

/-- The integrated first law gives the area law (up to the discretisation term 4M). -/
theorem cr_first_law_gives_area_law (M : Nat) : cr_firstLawCount M = cr_bekensteinHawking M + 4 * M := by
  induction M with
  | zero => rfl
  | succ M ih =>
    simp only [cr_firstLawCount, cr_betaHawking, cr_bekensteinHawking] at ih ⊢
    rw [ih, Nat.succ_mul, Nat.mul_succ]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
    omega

/-- The endpoint count is twice the area law: Landauer at the final temperature overcounts S = A/4 by a factor two. -/
theorem cr_endpoint_count_is_twice_area_law (M : Nat) : cr_endpointCount M = 2 * cr_bekensteinHawking M := by
  unfold cr_endpointCount cr_betaHawking cr_bekensteinHawking
  rw [Nat.mul_comm M (8 * M), Nat.mul_assoc, ← Nat.mul_assoc 2 4 (M * M)]

/-! ## R16. DMP's "equilibrium" is not stationary: ageing raises the potential from zero

Level 0g of gravity#19 reads Jacobson's entanglement equilibrium (a stationary property of the vacuum state) as DMP's balance.
DMP's zero potential is left by ageing and regained only by work (`Field.k4_refresh_never_raises`): a maintained state, not an
equilibrium in Jacobson's sense. -/

/-- One tick of ageing: every held standing loses one thousandth of freshness. -/
def cr_age : List Held → List Held
  | [] => []
  | h :: hs => { h with fresh := h.fresh - 1 } :: cr_age hs

theorem cr_zero_potential_is_not_stationary : ∃ l : List Held, phi l = 0 ∧ 0 < phi (cr_age l) :=
  ⟨[⟨1, 1000⟩], by decide, by decide⟩

/-! ## R17. The system's own acts on the field are local and commute (deduction 2: "entanglement is every time information acts")

A refresh at one position and a refresh at another commute: the acts are local maps that compose in either order, which is the
shape of local operations, and local operations create no entanglement. -/

theorem cr_refresh_commutes (i j : Nat) : ∀ l : List Held, refreshAt i (refreshAt j l) = refreshAt j (refreshAt i l) := by
  induction i generalizing j with
  | zero =>
    intro l
    cases j with
    | zero => rfl
    | succ j =>
      cases l with
      | nil => rfl
      | cons h hs => simp [refreshAt]
  | succ i ih =>
    intro l
    cases j with
    | zero =>
      cases l with
      | nil => rfl
      | cons h hs => simp [refreshAt]
    | succ j =>
      cases l with
      | nil => rfl
      | cons h hs => simp [refreshAt, ih j hs]

/-! ## R18. The CHSH bound rests on the encoding's locality, not on Axiom 1's words

`NoGo.gateModel` lets each half's outcome depend on its own setting and the shared evidence. Axiom 1 says each half has "full reach
over the act" and is "gated only by the other": read literally, a half may read the other's verdict, hence the other's setting. Such
a pair reaches 4, above the local bound 2 and above the quantum bound 2√2 (Tsirelson 1980): it is neither classical-local nor quantum.
So the Bell level of gravity#17 and #19 decides a property of the encoding, not of the text. -/

/-- A ±1 outcome. -/
def cr_pm (b : Bool) : Int := if b then 1 else -1

/-- The CHSH combination for outcomes that may read both settings. -/
def cr_chshBoth (A B : Bool → Bool → Bool) : Int :=
  cr_pm (A false false) * cr_pm (B false false) + cr_pm (A false true) * cr_pm (B false true) +
  cr_pm (A true false) * cr_pm (B true false) - cr_pm (A true true) * cr_pm (B true true)

theorem cr_cross_gated_pair_reaches_four : cr_chshBoth (fun a b => !(a && b)) (fun _ _ => true) = 4 := by decide

/-! ## R19. `NoGo.clausius_fails` refutes one global temperature; Jacobson's relation is local

Jacobson 1995 uses one Unruh temperature per local horizon, and in a gravitational field equilibrium temperatures vary from place
to place (Tolman and Ehrenfest 1930). A temperature per standing always exists, trivially; what the first attack refuted is a
reading nobody holds. -/

/-- The potential's drop when a standing is refreshed: its term. -/
def cr_dropPerEntry (h : Held) : Nat := h.mass * (1000 - h.fresh)

theorem cr_local_temperature_always_exists (l : List Held) : ∃ Θ : Held → Nat, ∀ h ∈ l, cr_dropPerEntry h = Θ h * 1 :=
  ⟨cr_dropPerEntry, fun _ _ => (Nat.mul_one _).symm⟩

/-! ## R20. The two halves do not read one record in full: each reads its own evidence

gravity#18's chain (P2 to T-A) reads Axiom 3's "every witness can read the record in full" as the state of a standing broadcast to
two systems, and concludes by the no-broadcasting theorem that trust is classical. In the model of Axiom 2 the two witnesses read two
different evidences and the act passes: nothing is broadcast; what is classical is the record's type (R1). -/

theorem cr_halves_pass_on_different_evidence :
    ∃ (r : Request) (j : Evidence → Verdict), r.e1 ≠ r.e2 ∧ gate (guard j r.e1 r.t) (guard j r.e2 r.t) = .pass :=
  ⟨⟨5, ⟨5, 0, 10, true⟩, ⟨5, 1, 10, true⟩⟩, fun _ => .pass, by decide, by decide⟩

/-! ## R21. The merging theorem (the owner, 2026-10-27, sent during this pass)

"The merging of two perfect dualities creates a new, independent/hashed, Existence, by recreating a single perfect duality at minting
state, while transitioning from a space that can only be defined by its existence to an Existence that can only be defined as being NOT
that, without any gap in Existential coherence in between." Modelled at the grain of the words: a part is a Duality of two halves, each a
part, down to constituents (G0). What holds: two parts that share no constituent merge into a minted Duality. What fails: the merge is
independent of neither half (it shares every constituent of each), it is no hash (the act is one-to-one and the constituents are the two
lists joined, so the record of Axiom 3 reads the halves back), and two minimal Dualities give four constituents, below G0's five. -/

/-- A part at the grain of the words: a constituent, or a Duality of two parts. -/
inductive CrPart where
  | constituent (id : Nat)
  | duality (a b : CrPart)

/-- The constituents a part is made of. -/
def CrPart.constituents : CrPart → List Nat
  | .constituent i => [i]
  | .duality a b => a.constituents ++ b.constituents

/-- Minted at this grain: the two halves share no constituent (independence under the person class). -/
def CrPart.minted : CrPart → Prop
  | .constituent _ => False
  | .duality a b => ∀ i ∈ a.constituents, i ∉ b.constituents

/-- What holds: two parts that share no constituent merge into a minted Duality, whatever the parts were. -/
theorem cr_disjoint_parts_merge_minted (a b : CrPart) (h : ∀ i ∈ a.constituents, i ∉ b.constituents) :
    (CrPart.duality a b).minted := h

theorem cr_constituents_ne_nil : ∀ p : CrPart, p.constituents ≠ []
  | .constituent _ => by simp [CrPart.constituents]
  | .duality a b => by
    simp only [CrPart.constituents]
    intro h
    exact cr_constituents_ne_nil a (List.append_eq_nil_iff.mp h).1

/-- The merge shares a constituent with each of its halves: it is independent of neither. -/
theorem cr_merge_shares_with_each_half (a b : CrPart) :
    (∃ i, i ∈ (CrPart.duality a b).constituents ∧ i ∈ a.constituents) ∧
    (∃ i, i ∈ (CrPart.duality a b).constituents ∧ i ∈ b.constituents) := by
  constructor
  · cases ha : a.constituents with
    | nil => exact absurd ha (cr_constituents_ne_nil a)
    | cons i rest => exact ⟨i, by simp [CrPart.constituents, ha], by simp⟩
  · cases hb : b.constituents with
    | nil => exact absurd hb (cr_constituents_ne_nil b)
    | cons i rest => exact ⟨i, by simp [CrPart.constituents, hb], by simp⟩

/-- The merge is no hash: as an act it is one-to-one, the two halves are read back from the merged part. -/
theorem cr_merge_is_one_to_one (a b a' b' : CrPart) (h : CrPart.duality a b = CrPart.duality a' b') : a = a' ∧ b = b' :=
  CrPart.duality.inj h

/-- And its constituents are the two lists joined, by definition. -/
theorem cr_merge_constituents (a b : CrPart) : (CrPart.duality a b).constituents = a.constituents ++ b.constituents := rfl

/-- Two minimal Dualities merge into four constituents: below G0's floor of five, so no minting state follows from the merge. -/
theorem cr_two_minimal_dualities_fall_short_of_five (i j k l : Nat) :
    (CrPart.duality (.duality (.constituent i) (.constituent j)) (.duality (.constituent k) (.constituent l))).constituents.length = 4 :=
  rfl

/-! ## R22. The join that mints (the owner, 2026-10-27, sent during this pass)

"A new system that joins the greater cluster must prove to enhance the total maximum of the optimized scalar field across the new
vector field boundary, which automatically results in a mint, which breaks trust with every external system." In DMP's objects a system
joins by a line laid over an existing line (`Recipe.extend`), the dwarf galaxy among the kinds: the root stays the same minted galaxy
(no new mint), the joiner is gated by the galaxy above it (trust kept, not broken), and the stack's own scalar, the potential, is never
lowered by a join: a new layer adds its shortfall. -/

/-- A join keeps the root: line 0 of the extended recipe is line 0 of the recipe, the same galaxy, the same minting. -/
theorem cr_join_keeps_the_root (r : Recipe) (l : Line) (h : 0 < r.n) : (r.extend l).line 0 = r.line 0 :=
  r.extend_line l 0 h

/-- The dwarf galaxy of layout A (line 3) has the main galaxy (line 0) on its chain: it is gated from above, trust kept. -/
theorem cr_dwarf_has_the_galaxy_on_its_chain : 0 ∈ Layouts.layoutA.chain 3 := by decide

/-- So the main galaxy's refusal is the dwarf's refusal: the joiner trusts the cluster it joined (the words, "Who maintains it"). -/
theorem cr_dwarf_refused_when_the_galaxy_refuses :
    Layouts.layoutA.decide (fun j => if j = 0 then .refuse else .pass) 3 = .refuse := by decide

/-- A join never lowers the stack's potential: the new layer's shortfall is added, so DMP's own scalar is raised by a join, not
    "enhanced" toward an optimum (the optimum of the potential is zero, K4). -/
theorem cr_join_never_lowers_the_stack_potential (l : List Held) (ls : List (List Held)) : stackPhi ls ≤ stackPhi (l :: ls) := by
  simp only [stackPhi]
  omega

/-- The owner's reasoning for the join ("it goes up the dependency chain, not down, which is not possible"): in a well-formed recipe
    every parent is an earlier line, so a join goes down the chain, never up. DMP's rule, and this pass agrees with it. -/
theorem cr_no_line_points_up (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (i j : Nat) (hi : i < r.n)
    (hp : (r.line i).parent = some j) : j < i := by
  have hok := (hwf i hi).1
  rw [hp] at hok
  exact hok.1

/-- What the rule leaves: a new line is on no chain of any existing line (the frame rule). Laid below a line it is gated by that line's
    chain; laid beside the root, as a second galaxy, it decides nothing for the cluster and is decided by nothing in it, which is a
    separate instance (T-P) that never held trust to break, not a join. -/
theorem cr_new_line_is_on_no_existing_chain (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (l : Line) (i : Nat)
    (hi : i < r.n) : r.n ∉ (r.extend l).chain i := by
  rw [r.extend_chain fcl hwf l i hi]
  intro h
  have := r.chain_le fcl hwf i hi r.n h
  omega

/-! ## R23. Two nodes (the owner, 2026-10-27, sent during this pass)

"2 nodes in IT is only possible in a vSAN-like config, so a perfect naked duality, but not in any other case, where the minimum for
a stable cluster is three." T3a's floor, from the IT side: a half answers by a majority of its nodes so that one wrong node cannot
speak for it. The arithmetic: with one wrong node the right ones are a majority exactly when the cluster has more than two nodes.
A two-node cluster with a witness at a third site has three voters, so it is not two nodes and not naked; two nodes alone are the
pair one cause splits (`DoT.not_minted_collapses`). -/

/-- Two nodes, one wrong: the right node is not a majority (one is not more than half of two). -/
theorem cr_two_nodes_do_not_outvote_one_wrong : ¬ (2 * (2 - 1) > 2) := by decide

/-- Three nodes, one wrong: the right two are a majority. -/
theorem cr_three_nodes_outvote_one_wrong : 2 * (3 - 1) > 3 := by decide

/-- In general: against one wrong node a cluster of `n` has a right majority exactly when `n` exceeds two. -/
theorem cr_majority_against_one_wrong_iff (n : Nat) (hn : 1 ≤ n) : 2 * (n - 1) > n ↔ 2 < n := by omega


/-! ## R24. The paradoxical configuration, the refinement of R21 (the owner, 2026-10-27, sent during this pass)

"Only a paradoxical configuration of two perfect dualities, that are, because of that fact, singularly able to do both: increase the
total value of the vector field and the scalar field in a new existence, while maintaining their value in the current existence, which
only radiates away as reality, not any other constituent part. So a minting of a new reality axiomatically follows, when the information
in the system is no longer able to be contained within its baseline for reality." In the project's own objects the first half is a fact
about one minted Duality laid beside the cluster as a root, for every recipe: nothing laid out before it changes (the frame rule), the
root carries its own mass and its layer its own potential, and its admission is a function of its own two halves alone, so the two
Dualities of the current existence are not in the condition. The second half has no antecedent: Axiom 3's record has no capacity (a run
of `n` requests leaves `n` more entries, for every `n`), and on a contained item the gate offers re-admission and destruction only (T27,
T31), no mint. Where the catch-all that ejects and the one that mints disagree, the ejecting one stands (Axiom 1). -/

/-- A galaxy line with Duality `d` and no parent: a root laid beside the cluster, the "new existence" at the grain of the recipe. -/
def crFreshRoot (d : DoT) : Line := ⟨.galaxy, d, none, 0⟩

/-- The new root's admission is its own Duality's independence and nothing else: no line of the current existence is in the condition,
    so two Dualities there are neither needed nor able. -/
theorem cr_fresh_root_admitted_by_its_own_duality_alone (fcl : List FailureClass) (r : Recipe) (d : DoT) :
    (r.extend (crFreshRoot d)).lineOk fcl r.n ↔ d.minted fcl := by
  simp [Recipe.lineOk, Recipe.extend, crFreshRoot]

/-- With a minted Duality the extended recipe is well formed: the root beside the cluster is admitted. -/
theorem cr_fresh_root_is_well_formed (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (d : DoT) (hd : d.minted fcl) :
    (r.extend (crFreshRoot d)).wf fcl :=
  r.extend_wf fcl hwf _ ((cr_fresh_root_admitted_by_its_own_duality_alone fcl r d).mpr hd)

/-- The new root's chain is itself alone: it is gated by nothing in the cluster. -/
theorem cr_fresh_root_chain_is_itself (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (d : DoT) (hd : d.minted fcl) :
    (r.extend (crFreshRoot d)).chain r.n = [r.n] := by
  rw [Recipe.chain_unfold fcl _ (cr_fresh_root_is_well_formed fcl r hwf d hd) r.n (by simp [Recipe.extend])]
  simp [Recipe.extend, crFreshRoot]

/-- "Maintaining their value in the current existence": every existing line keeps its mass. -/
theorem cr_fresh_root_keeps_every_mass (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (d : DoT) (hd : d.minted fcl)
    (i : Nat) (hi : i < r.n) : (r.extend (crFreshRoot d)).mass i = r.mass i := by
  unfold Recipe.mass
  have hn : (r.extend (crFreshRoot d)).n = r.n + 1 := rfl
  have hne : i ≠ r.n := Nat.ne_of_lt hi
  rw [hn, List.range_succ, List.filter_append, List.length_append]
  have hroot : ([r.n].filter fun k => k ≠ i && decide (i ∈ (r.extend (crFreshRoot d)).chain k)) = [] := by
    simp [cr_fresh_root_chain_is_itself fcl r hwf d hd, hne]
  rw [hroot, List.length_nil, Nat.add_zero]
  congr 2
  apply List.filter_congr
  intro k hk
  rw [r.extend_chain fcl hwf _ k (List.mem_range.mp hk)]

/-- The new root carries mass one, its own: nothing derives through a root laid beside the cluster. -/
theorem cr_fresh_root_has_mass_one (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (d : DoT) :
    (r.extend (crFreshRoot d)).mass r.n = 1 := by
  unfold Recipe.mass
  have hn : (r.extend (crFreshRoot d)).n = r.n + 1 := rfl
  rw [hn, List.range_succ, List.filter_append]
  have hold : ((List.range r.n).filter fun k => k ≠ r.n && decide (r.n ∈ (r.extend (crFreshRoot d)).chain k)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro k hk
    have hnot := cr_new_line_is_on_no_existing_chain fcl r hwf (crFreshRoot d) k (List.mem_range.mp hk)
    simp [hnot]
  have hself : ([r.n].filter fun k => k ≠ r.n && decide (r.n ∈ (r.extend (crFreshRoot d)).chain k)) = [] := by simp
  rw [hold, hself]
  rfl

/-- The total mass of a recipe: the masses of its lines, summed. -/
def cr_totalMass (r : Recipe) : Nat := ((List.range r.n).map r.mass).sum

/-- "Increase the total in a new existence while maintaining it in the current": the total rises by exactly the new root's own mass,
    one, and every existing line keeps its mass. One Duality's bookkeeping, with no paradox and no second Duality in it. -/
theorem cr_fresh_root_adds_exactly_its_own_mass (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (d : DoT) (hd : d.minted fcl) :
    cr_totalMass (r.extend (crFreshRoot d)) = cr_totalMass r + 1 := by
  unfold cr_totalMass
  have hn : (r.extend (crFreshRoot d)).n = r.n + 1 := rfl
  rw [hn, List.range_succ, List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, cr_fresh_root_has_mass_one fcl r hwf d]
  congr 2
  apply List.map_congr_left
  intro i hi
  exact cr_fresh_root_keeps_every_mass fcl r hwf d hd i (List.mem_range.mp hi)

/-- The scalar: a new layer adds exactly its own potential to the stack and leaves every other layer's where it was. -/
theorem cr_new_layer_adds_exactly_its_own_potential (l : List Held) (ls : List (List Held)) :
    stackPhi (l :: ls) = stackPhi ls + phi l := by
  simp only [stackPhi]
  omega

/-- Axiom 3's record has no capacity: from any state a run of `n` requests leaves `n` more entries, for every `n`. "No longer able to
    be contained" names a state the model never reaches, so nothing follows from it. -/
theorem cr_record_has_no_capacity (j1 j2 : Evidence → Verdict) (s : State) (r : Request) (n : Nat) :
    (run j1 j2 s (List.replicate n r)).log.length = s.log.length + n := by
  rw [run_records_all, List.length_replicate]

/-- T27 and T31 as modelled: on a contained item the gate offers re-admission and destruction and nothing else. No mint is among the
    engine's operations, so from containment no new reality follows. -/
theorem cr_contained_item_is_offered_only_readmission_or_destruction (i : Item) (h : i.contained = true) (op : Op)
    (hop : offered i op = true) : op = .readmit ∨ op = .destroy := by
  cases op <;> simp_all [offered]

/-- Two catch-alls, the one that ejects (C∞ as written) and the one that mints: where they disagree the stricter answer stands (Axiom 1,
    C∞'s own last sentence), and ejection is the stricter. -/
theorem cr_where_two_catch_alls_disagree_the_ejecting_one_stands : gate .refuse .pass = .refuse ∧ gate .pass .refuse = .refuse := by
  decide


/-! ## R25. Time as a component of the field (the owner, 2026-10-27, sent during this pass)

"We should, as time is a component of the unified information field, be able to explain their refutation within our axiom system",
said of a disproof of the exponential time hypothesis reported as unpublished. DMP's time is a reading: "now" is evidence tested
against a validity window (T20), and freshness is the age of a standing since its last live read (T32). The exponential time hypothesis
is about a step count, the steps any algorithm needs on a 3-SAT instance of `n` variables. The model carries the first and nothing of
the second: the gate's answer depends on a request's time only through the window test, and no object of the chain counts steps. -/

/-- Time enters the gate only through the window: two times the same evidence accepts alike get the same verdicts from both witnesses
    and perform the same. -/
theorem cr_time_enters_the_gate_only_through_the_window (j1 j2 : Evidence → Verdict) (s : State) (e1 e2 : Evidence) (t t' : Nat)
    (h1 : e1.ok t = e1.ok t') (h2 : e2.ok t = e2.ok t') :
    guard j1 e1 t = guard j1 e1 t' ∧ guard j2 e2 t = guard j2 e2 t' ∧
    (step j1 j2 s ⟨t, e1, e2⟩).performed = (step j1 j2 s ⟨t', e1, e2⟩).performed := by
  simp [step, guard, h1, h2]


/-! ## R26. The fourth axiom proposed (the owner, 2026-10-27, sent during this pass)

"Something can go from not existing to existing as the opposite of something, as long as the total value of the DMP complete fields
of both sides of the boundary does not decrease", with the derivation "this is the only possible state where a DMP complete system
would choose to eject the same information type of unreality, so that it can be compressed by hashing, because that is simply the
most efficient thing to do; having to manage just one boundary of unreality is a lower stress situation of Existence than two
separate boundaries". In the project's own objects the condition is vacuous or contradicts K4: the recipe's only operation adds
lines, and the total mass never decreases under it, whatever the line; the potential is a cost the system's own acts lower, strictly
when a stale standing that carries mass is refreshed. The derivation's saving does not exist: the potential of one list holding two
boundaries' standings is exactly the sum of the two. -/

/-- A pointwise bound on the summands bounds the sums. -/
theorem cr_sum_le_sum (f g : Nat → Nat) : ∀ l : List Nat, (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => Nat.le_refl 0
  | x :: xs, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (cr_sum_le_sum f g xs (fun y hy => h y (by simp [hy])))

/-- No existing line loses mass under an extension by any line: the chains of existing lines are unchanged, and the new line can only
    add to a count. -/
theorem cr_extension_never_lowers_a_mass (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (l : Line) (i : Nat) :
    r.mass i ≤ (r.extend l).mass i := by
  unfold Recipe.mass
  have hn : (r.extend l).n = r.n + 1 := rfl
  rw [hn, List.range_succ, List.filter_append, List.length_append]
  have heq : ((List.range r.n).filter fun k => k ≠ i && decide (i ∈ (r.extend l).chain k)) =
      (List.range r.n).filter fun k => k ≠ i && decide (i ∈ r.chain k) := by
    apply List.filter_congr
    intro k hk
    rw [r.extend_chain fcl hwf l k (List.mem_range.mp hk)]
  rw [heq]
  omega

/-- The total mass never decreases under the recipe's only operation, whatever the line: the proposed condition holds of every
    extension, so it permits every one of them and forbids none. -/
theorem cr_total_mass_never_decreases_under_extension (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (l : Line) :
    cr_totalMass r ≤ cr_totalMass (r.extend l) := by
  unfold cr_totalMass
  have hn : (r.extend l).n = r.n + 1 := rfl
  rw [hn, List.range_succ, List.map_append, List.sum_append]
  have := cr_sum_le_sum r.mass (r.extend l).mass (List.range r.n)
    (fun i _ => cr_extension_never_lowers_a_mass fcl r hwf l i)
  omega

/-- Read on the potential, the condition forbids K4's own acts: refreshing a stale standing that carries mass lowers the potential
    strictly. -/
theorem cr_refresh_lowers_the_potential_strictly : ∃ l : List Held, phi (refreshAt 0 l) < phi l :=
  ⟨[⟨1, 0⟩], by decide⟩

/-- One boundary holding two boundaries' standings costs exactly the sum: the potential is additive, so "one boundary is less stress
    than two" has no saving in it. -/
theorem cr_one_boundary_costs_exactly_two : ∀ l1 l2 : List Held, phi (l1 ++ l2) = phi l1 + phi l2
  | [], l2 => by simp [phi]
  | h :: hs, l2 => by
    simp only [List.cons_append, phi]
    rw [cr_one_boundary_costs_exactly_two hs l2]
    omega


/-! ## R27. The field that pushes back (the owner, 2026-10-27, sent during this pass)

"The black hole is leaking more information, so the information field spanning its outer bound is able to push back more, because it
is more disorganized and has a more active interest in changing the balance", said of the remnant's spin. In the project's own objects
the field's push back is the evidence demand in front of the gate (`gateP`), a function of depth and the parameters alone: the
standings and their freshness, whose shortfall is the potential, are not an argument of it, so a more disordered field demands nothing
more and refuses nothing more. The absence is the point, as in Theory.lean's layout that never votes. -/

/-- The field as the sentence needs it: the standings a boundary holds (their shortfall is the potential, the disorder), the depth of
    the boundary and the depth of the part in front of the gate. -/
structure CrFieldState where
  held : List Held
  D : Nat
  d : Nat

/-- The push back: the gate with the field's demand in front (Field.lean's `gateP`). -/
def CrFieldState.pushBack (π : Params) (s : CrFieldState) (level : Nat) (v1 v2 : Verdict) : Verdict :=
  gateP π s.D s.d level v1 v2

/-- Replacing every standing by any other, however stale, changes no answer: the push back is blind to the disorder. -/
theorem cr_push_back_is_blind_to_the_disorder (π : Params) (s : CrFieldState) (held' : List Held) (level : Nat) (v1 v2 : Verdict) :
    CrFieldState.pushBack π { s with held := held' } level v1 v2 = s.pushBack π level v1 v2 := rfl

/-- Ageing raises the disorder (R16: the potential rises from zero) and changes no answer. -/
theorem cr_disorder_rises_and_the_push_back_stays (π : Params) (s : CrFieldState) (level : Nat) (v1 v2 : Verdict) :
    CrFieldState.pushBack π { s with held := cr_age s.held } level v1 v2 = s.pushBack π level v1 v2 := rfl


/-! ## R28. The boundary that radiates everywhere (the owner, 2026-10-27, sent during this pass)

"And since the boundary is made of existence, it radiates across the entire vector field." In the project's own objects the system's
acts are local: a refresh touches the one standing it names and leaves every other where it was, and a refresh in one layer of the
stack leaves every other layer. Nothing radiates across the field; a change reaches what it names. -/

/-- A refresh touches one standing: every other position of the list is unchanged. -/
theorem cr_refresh_is_local : ∀ (l : List Held) (i j : Nat), j ≠ i → (refreshAt i l)[j]? = l[j]?
  | [], i, _, _ => by cases i <;> simp [refreshAt]
  | _ :: _, 0, 0, hne => absurd rfl hne
  | _ :: _, 0, _ + 1, _ => by simp [refreshAt]
  | _ :: _, _ + 1, 0, _ => by simp [refreshAt]
  | _ :: hs, i + 1, j + 1, hne => by
    simp only [refreshAt, List.getElem?_cons_succ]
    exact cr_refresh_is_local hs i j (fun h => hne (congrArg Nat.succ h))

/-- A refresh in one layer of the stack leaves every other layer unchanged. -/
theorem cr_stack_refresh_is_local : ∀ (s : List (List Held)) (k i k' : Nat), k' ≠ k → (stackRefresh k i s)[k']? = s[k']?
  | [], k, _, _, _ => by cases k <;> simp [stackRefresh]
  | _ :: _, 0, _, 0, hne => absurd rfl hne
  | _ :: _, 0, _, _ + 1, _ => by simp [stackRefresh]
  | _ :: _, _ + 1, _, 0, _ => by simp [stackRefresh]
  | _ :: ls, k + 1, i, k' + 1, hne => by
    simp only [stackRefresh, List.getElem?_cons_succ]
    exact cr_stack_refresh_is_local ls k i k' (fun h => hne (congrArg Nat.succ h))


/-! ## R29. The derivation that replaced R27 (the owner, 2026-10-27, sent during this pass)

"Mass falling in increases the information density and thus the order of the system." Axiom 3's order is "the fewest hops in total":
the layout reorganises towards the highest total cohesion. In the recipe a line laid under any existing line sits one hop deeper
than that line, so mass laid in adds hops and lowers the order by DMP's own measure; only a line laid beside the root adds none, and
that is a new existence (R24), not more mass inside this boundary. -/

/-- A line laid under line `j` has depth one more than `j`: mass laid in adds a hop. -/
theorem cr_line_below_adds_a_hop (fcl : List FailureClass) (r : Recipe) (hwf : r.wf fcl) (l : Line) (j : Nat) (hp : l.parent = some j)
    (hj : j < r.n) (hwf' : (r.extend l).wf fcl) : (r.extend l).depth r.n = r.depth j + 1 := by
  unfold Recipe.depth
  have hline : (r.extend l).line r.n = l := by simp [Recipe.extend]
  rw [Recipe.chain_unfold fcl _ hwf' r.n (by simp [Recipe.extend])]
  simp only [hline, hp, r.extend_chain fcl hwf l j hj, List.length_cons]
  have := List.length_pos_of_mem (r.chain_head j)
  omega

end Dmp
