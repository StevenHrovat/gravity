import Dmp.MassGap

/-!
# The dictionary: a key network is a lattice gauge field

`docs/mass-gap/README.md` reads DMP against Yang-Mills theory on a lattice. This file proves the parts of that reading that are
mathematics, and marks where the reading stops.

**The reading.** Give every part its own key frame. For every pair of neighbouring parts, the network holds a **translation**: how a
key of the first part is read in the frame of the second. A **re-keying** (each part rotates its own keys by its own amount; DMP: "the
minting is a trust rotation: every key rotates") changes every translation, so no single translation means anything on its own; what
survives every re-keying is what a chain of translations does **around a closed loop**, its **holonomy**. A **shortfall** of a small
loop is how far its holonomy is from "nothing changed"; a weight times the shortfalls, summed, is a potential that is zero exactly when
every small loop is consistent. Physicists call exactly this a lattice gauge field (Wilson 1974): parts are sites, translations are
link variables, re-keying is a gauge transformation, loop holonomies are Wilson loops and the summed shortfall is the Wilson action.
DMP's VIBE potential has the same shape (weight times shortfall, zero in balance), but it measures freshness, not loop consistency:
the shape transfers, the content does not.

What this file proves:

1. Re-keying never changes a closed loop's holonomy (telescoping), so the Wilson-type potential is invariant under every re-keying.
2. A re-keyed trivial network is balanced (pure gauge has zero potential); with positive weight the potential is zero exactly when every
   checked loop is consistent.
3. **Balanced is not trivial.** On a 3 × 3 torus there is a network in which every small loop is consistent but the loop once around the
   torus is not, and no re-keying removes that: a global twist invisible to every local check.
4. **Light versus gluons, in one line of algebra.** Over an abelian group (the integers, the stand-in for U(1), light) re-keying the base
   point of a loop leaves the loop's value itself unchanged. Over the smallest non-abelian group (the six relabellings of a three-node
   cluster) re-keying the base point moves the value; only its class (here the number of fixed nodes, the trace) survives. The two-node
   relabellings commute; the three-node ones do not. That three is T3a's floor is a coincidence of small numbers, a reading.
5. **The skeleton of every known gap proof**: if each layer passes on at most a fraction `a/b < 1` of a disturbance, the disturbance at
   distance `n` is at most `(a/b)^n` of the original, with no reference to the system's size (exponential clustering, uniform in
   volume). Without contraction (`a = b`) a disturbance can travel undiminished: no decay, the massless case.

None of this proves anything about Yang-Mills theory. Points 1, 2 and 5 are textbook facts in DMP's vocabulary; point 3 is the
discrete form of flat connections with holonomy; point 4 is why a gap argument must use non-commutativity (the photon test of the
README): any argument blind to it would also give light a mass, and light is massless.
-/

namespace Dmp

/-! ## 1. Key networks over the integers -/

/-- A key network: for every ordered pair of parts, the translation from the first part's key frame to the second's. -/
abbrev KeyNet := Nat → Nat → Int

/-- A re-keying: every part rotates its own keys by its own amount. -/
abbrev Rekey := Nat → Int

/-- The network seen after re-keying: over an abelian group the translation from `a` to `b` gains `a`'s rotation and loses `b`'s. -/
def KeyNet.rekey (u : KeyNet) (g : Rekey) : KeyNet := fun a b => g a + u a b - g b

/-- The holonomy of a path (a list of parts): the composed translation along it. -/
def hol (u : KeyNet) : List Nat → Int
  | [] => 0
  | [_] => 0
  | a :: b :: rest => u a b + hol u (b :: rest)

/-- The last part of the path `a :: rest`. -/
def lastOf : Nat → List Nat → Nat
  | a, [] => a
  | _, b :: rest => lastOf b rest

theorem lastOf_append (a z : Nat) (rest : List Nat) : lastOf a (rest ++ [z]) = z := by
  induction rest generalizing a with
  | nil => rfl
  | cons b r ih => exact ih b

/-- Re-keying adds the start's rotation and subtracts the end's: everything in between telescopes away. -/
theorem hol_rekey (u : KeyNet) (g : Rekey) (a : Nat) (rest : List Nat) :
    hol (u.rekey g) (a :: rest) = g a + hol u (a :: rest) - g (lastOf a rest) := by
  induction rest generalizing a with
  | nil => simp [hol, lastOf]
  | cons b r ih =>
    simp only [hol, KeyNet.rekey, lastOf]
    rw [ih b]
    omega

/-- A closed loop based at `a`. -/
structure Loop where
  base : Nat
  rest : List Nat

def Loop.path (p : Loop) : List Nat := p.base :: (p.rest ++ [p.base])

def Loop.hol (u : KeyNet) (p : Loop) : Int := Dmp.hol u p.path

/-- **Re-keying never changes a closed loop's holonomy.** -/
theorem loop_hol_rekey (u : KeyNet) (g : Rekey) (p : Loop) : p.hol (u.rekey g) = p.hol u := by
  unfold Loop.hol Loop.path
  rw [hol_rekey, lastOf_append]
  omega

/-- The Wilson-type potential over a list of checked loops: weight times the size of each loop's inconsistency. -/
def wilsonPot (β : Nat) (u : KeyNet) : List Loop → Nat
  | [] => 0
  | p :: ps => β * (p.hol u).natAbs + wilsonPot β u ps

/-- The potential is invariant under every re-keying (gauge invariance). -/
theorem wilsonPot_rekey (β : Nat) (u : KeyNet) (g : Rekey) (ps : List Loop) : wilsonPot β (u.rekey g) ps = wilsonPot β u ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [wilsonPot, loop_hol_rekey, ih]

/-! ## 2. Balanced states -/

/-- The trivial network: every translation is "nothing changes". -/
def trivialNet : KeyNet := fun _ _ => 0

theorem hol_trivial (path : List Nat) : hol trivialNet path = 0 := by
  induction path with
  | nil => rfl
  | cons a r ih =>
    cases r with
    | nil => rfl
    | cons b r' => simp only [hol, trivialNet] at *; omega

/-- A re-keyed trivial network (pure gauge) is balanced on every list of loops. -/
theorem pure_gauge_balanced (β : Nat) (g : Rekey) (ps : List Loop) : wilsonPot β (trivialNet.rekey g) ps = 0 := by
  rw [wilsonPot_rekey]
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [wilsonPot, Loop.hol, hol_trivial, ih]; rfl

/-- With positive weight the potential is zero exactly when every checked loop is consistent. -/
theorem wilsonPot_zero_iff (β : Nat) (hβ : 0 < β) (u : KeyNet) (ps : List Loop) :
    wilsonPot β u ps = 0 ↔ ∀ p ∈ ps, p.hol u = 0 := by
  induction ps with
  | nil => simp [wilsonPot]
  | cons p ps ih =>
    simp only [wilsonPot, List.mem_cons, forall_eq_or_imp]
    rw [← ih]
    constructor
    · intro h
      have h1 : β * (p.hol u).natAbs = 0 := by omega
      have h2 : (p.hol u).natAbs = 0 := by
        rcases Nat.mul_eq_zero.mp h1 with h3 | h3
        · omega
        · exact h3
      exact ⟨Int.natAbs_eq_zero.mp h2, by omega⟩
    · rintro ⟨h1, h2⟩
      rw [h1, h2]; rfl

/-! ## 3. Balanced is not trivial: a global twist on a 3 × 3 torus -/

/-- Site `(x, y)` of the 3 × 3 torus. -/
def site (x y : Nat) : Nat := x % 3 + 3 * (y % 3)

/-- The nine small loops (plaquettes) of the torus. -/
def torusPlaquettes : List Loop :=
  (List.range 9).map fun s =>
    let x := s % 3
    let y := s / 3
    { base := site x y, rest := [site (x + 1) y, site (x + 1) (y + 1), site x (y + 1)] }

/-- The twisted network: crossing from column 2 to column 0 translates by one, back by minus one, everything else by nothing. -/
def twisted : KeyNet := fun a b =>
  if a % 3 = 2 ∧ b % 3 = 0 ∧ a / 3 = b / 3 then 1
  else if a % 3 = 0 ∧ b % 3 = 2 ∧ a / 3 = b / 3 then -1
  else 0

/-- The loop once around the torus along the first row. -/
def aroundLoop : Loop := { base := site 0 0, rest := [site 1 0, site 2 0] }

/-- Every small loop is consistent: the twisted network is balanced. -/
theorem twisted_balanced : wilsonPot 1 twisted torusPlaquettes = 0 := by decide

/-- But the loop around the torus is not. -/
theorem twisted_around : aroundLoop.hol twisted = 1 := by decide

/-- **Balanced is not trivial**: no re-keying turns the twisted network into one where the loop around the torus is consistent, although
    every small loop already is. -/
theorem balanced_not_trivial (g : Rekey) : aroundLoop.hol (twisted.rekey g) ≠ 0 := by
  rw [loop_hol_rekey, twisted_around]; decide

/-! ## 4. Light versus gluons: abelian and non-abelian re-keying -/

/-- Over the integers, re-keying a loop's base point by `g` (translate in, go around, translate out) leaves its value as it was. -/
theorem abelian_loop_value_fixed (g h : Int) : g + h - g = h := by omega

/-- A relabelling of a three-node cluster: where node 0, 1 and 2 go. -/
structure Perm3 where
  p0 : Fin 3
  p1 : Fin 3
  p2 : Fin 3
  deriving DecidableEq, Repr

def Perm3.app (σ : Perm3) : Fin 3 → Fin 3
  | 0 => σ.p0
  | 1 => σ.p1
  | 2 => σ.p2

/-- Composition: first `τ`, then `σ`. -/
def Perm3.comp (σ τ : Perm3) : Perm3 := ⟨σ.app (τ.app 0), σ.app (τ.app 1), σ.app (τ.app 2)⟩

/-- The six relabellings of three nodes, the symmetric group S₃, the smallest non-abelian group. -/
def allPerm3 : List Perm3 :=
  [⟨0, 1, 2⟩, ⟨0, 2, 1⟩, ⟨1, 0, 2⟩, ⟨1, 2, 0⟩, ⟨2, 0, 1⟩, ⟨2, 1, 0⟩]

/-- The inverse, by search over the six. -/
def Perm3.inv (σ : Perm3) : Perm3 := (allPerm3.find? fun τ => τ.comp σ == ⟨0, 1, 2⟩).getD ⟨0, 1, 2⟩

/-- The number of nodes a relabelling leaves in place: the trace of its permutation matrix, a class function. -/
def Perm3.fixed (σ : Perm3) : Nat :=
  (if σ.p0 = 0 then 1 else 0) + (if σ.p1 = 1 then 1 else 0) + (if σ.p2 = 2 then 1 else 0)

/-- The six are closed under composition and each has an inverse among them: a group. -/
theorem perm3_group : (∀ σ ∈ allPerm3, ∀ τ ∈ allPerm3, σ.comp τ ∈ allPerm3) ∧
    (∀ σ ∈ allPerm3, σ.inv.comp σ = ⟨0, 1, 2⟩ ∧ σ.comp σ.inv = ⟨0, 1, 2⟩) := by decide

/-- Three-node relabellings do not commute. -/
theorem perm3_not_abelian : ∃ σ ∈ allPerm3, ∃ τ ∈ allPerm3, σ.comp τ ≠ τ.comp σ := by decide

/-- **Re-keying the base point moves a non-abelian loop's value**: there is a loop value `h` and a re-keying `g` with
    `g h g⁻¹ ≠ h`. A single gluon-like loop value is not something every reader agrees on. -/
theorem nonabelian_loop_value_moves : ∃ g ∈ allPerm3, ∃ h ∈ allPerm3, (g.comp h).comp g.inv ≠ h := by decide

/-- **Only the class survives**: the number of fixed nodes (the trace) of `g h g⁻¹` is that of `h`, for every `g` and `h`. -/
theorem nonabelian_class_invariant : ∀ g ∈ allPerm3, ∀ h ∈ allPerm3, ((g.comp h).comp g.inv).fixed = h.fixed := by decide

/-- A relabelling of a two-node pair. -/
def allPerm2 : List (Bool → Bool) := [id, not]

/-- Two-node relabellings commute (S₂ is abelian), checked on both inputs. -/
theorem perm2_abelian : ∀ σ ∈ allPerm2, ∀ τ ∈ allPerm2, ∀ x : Bool, σ (τ x) = τ (σ x) := by
  intro σ hσ τ hτ x
  simp only [allPerm2, List.mem_cons, List.mem_nil_iff, or_false] at hσ hτ
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> cases x <;> rfl

/-! ## 5. The skeleton of a gap proof: contraction gives exponential clustering, uniform in volume -/

/-- **Contraction gives exponential decay.** If each layer passes on at most `a/b` of a disturbance (`infl (n+1) · b ≤ infl n · a`), the
    disturbance at distance `n` is at most `(a/b)^n` of the original. No system size appears: the bound is uniform in volume. -/
theorem contraction_decay (infl : Nat → Nat) (a b : Nat) (h : ∀ n, infl (n + 1) * b ≤ infl n * a) :
    ∀ n, infl n * b ^ n ≤ infl 0 * a ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    calc infl (k + 1) * b ^ (k + 1) = (infl (k + 1) * b) * b ^ k := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ (infl k * a) * b ^ k := Nat.mul_le_mul_right _ (h k)
      _ = a * (infl k * b ^ k) := by ac_rfl
      _ ≤ a * (infl 0 * a ^ k) := Nat.mul_le_mul_left _ ih
      _ = infl 0 * a ^ (k + 1) := by rw [Nat.pow_succ]; ac_rfl

/-- **Without contraction there is no decay**: at `a = b` a disturbance can travel undiminished to every distance (the massless case). -/
theorem no_contraction_no_decay (b : Nat) :
    ∃ infl : Nat → Nat, (∀ n, infl (n + 1) * b ≤ infl n * b) ∧ 0 < infl 0 ∧ ∀ n, infl n = infl 0 :=
  ⟨fun _ => 1, fun _ => Nat.le_refl _, by decide, fun _ => rfl⟩

end Dmp
