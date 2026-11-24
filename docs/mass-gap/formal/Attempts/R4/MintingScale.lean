/-
Round 4, attempt 4 (r4-minting), 2026-11-21. Released under Apache 2.0.

# The Yang–Mills counterpart, as a toy: a scale fixed at the root and carried exactly along an autonomous flow

Note: `docs/mass-gap/weak-coupling/attempts/r4-minting/NOTE.md`, sections 2–4. These are toys about a step map `σ` of one real coupling
`u` (one blocking doubling towards long distances: `u_{n+1} = σ(u_n)`, the step-scaling function). They contain no SU(2), no lattice,
no Wilson measure. They state what the RG-invariant scale Λ is, what its conservation does and does not give.

Physics (credited in the note): Callan (1970) and Symanzik (1970) for the renormalisation-group equation; Coleman and Weinberg (1973) for
dimensional transmutation; Gross, Wilczek and Politzer (1973) for the sign of the one-loop coefficient; Landau for the ultraviolet pole of
infrared-free theories; Aizenman and Duminil-Copin (2021) for the triviality of φ⁴₄.

What is proved:
1. `clock_iterate`, `lambda_conserved`: if the flow has a clock `Φ` (one doubling advances it by one: Abel's equation `Φ(σ u) = Φ u + 1`),
   then `Λ := 2^{Φ(u_n)} / L_n` (with `L_n = 2ⁿ L₀`) is the same at every layer: a scale fixed at the root and carried exactly.
2. `no_clock_of_fixed_point`, `photon_no_clock`: a fixed point of the flow admits no clock; the frozen flow (the photon, `σ = id`) has no Λ.
3. `mass_over_lambda_invariant`, `massless_with_scale`: a layer mass that depends only on the layer coupling (dimensional transmutation:
   "everything else follows") is a fixed number times Λ along the whole chain; the number zero is allowed (a scale without a gap).
4. `oneLoop_iterate`, `oneLoop_clock`: the one-loop flow in the inverse coupling `w = 1/u` (`w ↦ w − c`) has the clock `Φ(w) = −w/c`;
   `af_root_infinite_depth`: for `c > 0` (asymptotic freedom) every physical `w_N` is reached from a root whose inverse coupling grows
   without bound with the depth `N` (the root at infinite depth is free); `irFree_root_depth_bounded`: for `c = −d < 0` (φ⁴₄, QED)
   a positive bare coupling allows only `N < w_N / d` layers between root and physics (the Landau pole: the scale sits in the ultraviolet).
5. `crossing_of_no_fixed_point`, `no_crossing_of_fixed_point`, `crossing_of_clock`: for a continuous flow on a compact stretch `[a, b]`,
   strict growth (no fixed point) gives one number of doublings `N` that carries every start in `[a, b]` to `b`; a fixed point of a
   monotone flow blocks the crossing forever; a clock on the stretch plus the direction `u ≤ σ u` (asymptotic freedom's sign) gives
   the crossing.
-/

import Mathlib

namespace Attempts.R4.Minting

/-! ## 1. A clock and the conserved scale -/

/-- An Abel clock of the step map `σ` on `S`: one doubling advances it by exactly one. -/
def IsClock (σ Φ : ℝ → ℝ) (S : Set ℝ) : Prop := ∀ u ∈ S, Φ (σ u) = Φ u + 1

theorem clock_iterate {σ Φ : ℝ → ℝ} {S : Set ℝ} (hS : Set.MapsTo σ S S) (hc : IsClock σ Φ S) {u : ℝ} (hu : u ∈ S)
    (n : ℕ) : Φ (σ^[n] u) = Φ u + n ∧ σ^[n] u ∈ S := by
  induction n with
  | zero => simp [hu]
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨?_, hS ih.2⟩
    rw [hc _ ih.2, ih.1]
    push_cast
    ring

/-- **Λ is conserved.** With `L_n = 2ⁿ L₀` the box (or block) size at layer `n`, the scale `Λ_n := 2^{Φ(u_n)} / L_n` is the root's at
every layer. -/
theorem lambda_conserved {σ Φ : ℝ → ℝ} {S : Set ℝ} (hS : Set.MapsTo σ S S) (hc : IsClock σ Φ S) {u L0 : ℝ} (hu : u ∈ S)
    (hL0 : L0 ≠ 0) (n : ℕ) : (2 : ℝ) ^ Φ (σ^[n] u) / (2 ^ n * L0) = (2 : ℝ) ^ Φ u / L0 := by
  rw [(clock_iterate hS hc hu n).1, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- A fixed point of the flow admits no clock: Λ cannot be defined through a fixed point. -/
theorem no_clock_of_fixed_point {σ Φ : ℝ → ℝ} {S : Set ℝ} {u : ℝ} (hu : u ∈ S) (hf : σ u = u) : ¬ IsClock σ Φ S := by
  intro hc
  have h := hc u hu
  rw [hf] at h
  linarith

/-- **The photon has no Λ.** The frozen flow (no running) has no clock on any non-empty set. -/
theorem photon_no_clock (Φ : ℝ → ℝ) {S : Set ℝ} (hS : S.Nonempty) : ¬ IsClock id Φ S := by
  obtain ⟨u, hu⟩ := hS
  exact no_clock_of_fixed_point hu rfl

/-! ## 2. "Everything else follows": dimensional transmutation, and what it does not decide -/

/-- **A mass is a fixed number times Λ.** Let `G(u)` be a mass in the units of the layer whose coupling is `u` (one function for every
layer: the layer's theory is fixed by its coupling). Exact blocking keeps the physical mass, so in the twice coarser units it doubles:
`G(σ u) = 2 · G(u)`. Then `G(u_n) / 2^{Φ(u_n)}` (the mass over Λ) is the same at every layer. -/
theorem mass_over_lambda_invariant {σ Φ G : ℝ → ℝ} {S : Set ℝ} (hS : Set.MapsTo σ S S) (hc : IsClock σ Φ S)
    (hG : ∀ u ∈ S, G (σ u) = 2 * G u) {u : ℝ} (hu : u ∈ S) (n : ℕ) :
    G (σ^[n] u) / (2 : ℝ) ^ Φ (σ^[n] u) = G u / (2 : ℝ) ^ Φ u := by
  have hGn : G (σ^[n] u) = 2 ^ n * G u := by
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', hG _ (clock_iterate hS hc hu m).2, ih, pow_succ]
      ring
  rw [hGn, (clock_iterate hS hc hu n).1, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : (2 : ℝ) ^ Φ u ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  field_simp

/-- **The number may be zero.** The zero mass satisfies the doubling rule for every flow: conservation of Λ fixes the form `m = c · Λ`,
never `c > 0` (a scale without a gap: massless pions of massless QCD; an infrared fixed point). -/
theorem massless_with_scale (σ : ℝ → ℝ) (S : Set ℝ) :
    ∀ u ∈ S, (fun _ : ℝ => (0 : ℝ)) (σ u) = 2 * (fun _ : ℝ => (0 : ℝ)) u := by
  intro u _
  simp

/-! ## 3. The one-loop toy: where the scale sits (infrared for c > 0, ultraviolet for c < 0, nowhere for c = 0) -/

/-- One doubling of the one-loop flow in the inverse coupling `w = 1/u`: `w ↦ w − c` (for SU(N), `c = 2 b₀ ln 2 > 0`). -/
def oneLoop (c : ℝ) (w : ℝ) : ℝ := w - c

theorem oneLoop_iterate (c w : ℝ) (n : ℕ) : (oneLoop c)^[n] w = w - n * c := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold oneLoop
    push_cast
    ring

/-- The one-loop clock `Φ(w) = −w/c`: Λ·L = 2^{−w/c}, i.e. Λ = (1/L)·exp(−ln 2 · w/c) = (1/L)·exp(−1/(2 b₀ g²)) for SU(N). -/
theorem oneLoop_clock {c : ℝ} (hc : c ≠ 0) : IsClock (oneLoop c) (fun w => -w / c) Set.univ := by
  intro w _
  unfold oneLoop
  field_simp
  ring

/-- **Asymptotic freedom: the root can recede to infinite depth.** For `c > 0`, every physical inverse coupling `w_N` at the top of `N`
layers is reached from the root value `w_N + N c`, which exceeds any bound once `N` is large: the bare coupling tends to zero. -/
theorem af_root_infinite_depth {c : ℝ} (hc : 0 < c) (wN : ℝ) :
    (∀ N : ℕ, (oneLoop c)^[N] (wN + N * c) = wN) ∧ ∀ M : ℝ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → M ≤ wN + N * c := by
  refine ⟨fun N => by rw [oneLoop_iterate]; ring, fun M => ?_⟩
  obtain ⟨N0, hN0⟩ := exists_nat_ge ((M - wN) / c)
  refine ⟨N0, fun N hN => ?_⟩
  have h1 : (M - wN) / c ≤ N := le_trans hN0 (by exact_mod_cast hN)
  rw [div_le_iff₀ hc] at h1
  linarith

/-- **Infrared freedom (φ⁴₄, QED): the root cannot recede.** For `c = −d < 0`, a positive bare inverse coupling at the root and the
physical value `w_N` after `N` layers force `N · d < w_N`: the depth is bounded (the Landau pole sits in the ultraviolet), so removing
the cutoff at fixed physics is impossible unless `w_N → ∞`, the free theory. -/
theorem irFree_root_depth_bounded {d w0 wN : ℝ} (hw0 : 0 < w0) {N : ℕ} (h : (oneLoop (-d))^[N] w0 = wN) : N * d < wN := by
  rw [oneLoop_iterate] at h
  linarith

/-- The photon (`c = 0`): the coupling is the same at every layer (frozen act number), and there is no clock. -/
theorem photon_oneLoop (w : ℝ) (n : ℕ) : (oneLoop 0)^[n] w = w := by
  rw [oneLoop_iterate]; ring

/-! ## 3a. The tie to G0: following the running back to a root at infinite depth -/

/-- **Tied to the ground.** A physical inverse coupling `wv` is tied to the ground when, for every depth `N`, some root value `r N`
flows to `wv` in `N` doublings, and the roots tend to the free ground (`w = 1/u → +∞`, bare coupling to zero) as the depth grows. -/
def TiedToGround (σ : ℝ → ℝ) (wv : ℝ) : Prop :=
  ∃ r : ℕ → ℝ, (∀ N, σ^[N] (r N) = wv) ∧ Filter.Tendsto r Filter.atTop Filter.atTop

/-- **Asymptotic freedom keeps the tie.** For `c > 0` every physical value is tied to the ground. -/
theorem af_tied {c : ℝ} (hc : 0 < c) (wv : ℝ) : TiedToGround (oneLoop c) wv := by
  obtain ⟨hreach, hbig⟩ := af_root_infinite_depth hc wv
  exact ⟨fun N => wv + N * c, hreach, Filter.tendsto_atTop_atTop.mpr hbig⟩

/-- In the one-loop flow the root is forced: whatever reaches `wv` in `N` doublings started at `wv + N c`. -/
theorem oneLoop_root_forced {c wv : ℝ} {r : ℕ → ℝ} (h : ∀ N, (oneLoop c)^[N] (r N) = wv) (N : ℕ) : r N = wv + N * c := by
  have := h N
  rw [oneLoop_iterate] at this
  linarith

/-- **Infrared freedom breaks the tie** (φ⁴₄, QED): for `c = −d < 0` no physical value is tied to the ground; following the running
back towards the root the coupling grows (the Landau pole) instead of vanishing. -/
theorem irFree_not_tied {d : ℝ} (hd : 0 < d) (wv : ℝ) : ¬ TiedToGround (oneLoop (-d)) wv := by
  rintro ⟨r, hr, hlim⟩
  obtain ⟨i, hi⟩ := Filter.tendsto_atTop_atTop.mp hlim (wv + 1)
  have h1 := hi i le_rfl
  rw [oneLoop_root_forced hr i] at h1
  have : 0 ≤ (i : ℝ) * d := mul_nonneg (Nat.cast_nonneg i) hd.le
  linarith

/-- **The photon does not run, so it has no tie to make**: every root equals the physical value. -/
theorem photon_not_tied (wv : ℝ) : ¬ TiedToGround (oneLoop 0) wv := by
  rintro ⟨r, hr, hlim⟩
  obtain ⟨i, hi⟩ := Filter.tendsto_atTop_atTop.mp hlim (wv + 1)
  have h1 := hi i le_rfl
  rw [oneLoop_root_forced hr i] at h1
  linarith

/-! ## 4. Crossing the existence boundary: equivalent to "no fixed point" on the stretch -/

/-- **No fixed point gives a uniform crossing.** A continuous flow that strictly increases the coupling on the compact stretch `[a, b]`
carries every start in `[a, b]` to at least `b` within one number `N` of doublings. -/
theorem crossing_of_no_fixed_point {σ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hσ : ContinuousOn σ (Set.Icc a b))
    (hgrow : ∀ u ∈ Set.Icc a b, u < σ u) : ∃ N : ℕ, ∀ u0 ∈ Set.Icc a b, ∃ n ≤ N, b ≤ σ^[n] u0 := by
  obtain ⟨m, hm, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn (Set.nonempty_Icc.mpr hab)
    (f := fun u => σ u - u) (hσ.sub continuousOn_id)
  set δ := σ m - m with hδ
  have hδpos : 0 < δ := by have := hgrow m hm; rw [hδ]; linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨N, fun u0 hu0 => ?_⟩
  by_contra hcon
  push Not at hcon
  have key : ∀ n, n ≤ N → a + n * δ ≤ σ^[n] u0 := by
    intro n
    induction n with
    | zero => intro _; simpa using hu0.1
    | succ k ih =>
      intro hk
      have hk' : k ≤ N := Nat.le_of_succ_le hk
      have hv := ih hk'
      have hvb := hcon k hk'
      have hva : a ≤ σ^[k] u0 := by
        have : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg k) hδpos.le
        linarith
      have hmem : σ^[k] u0 ∈ Set.Icc a b := ⟨hva, hvb.le⟩
      have hstep : δ ≤ σ (σ^[k] u0) - σ^[k] u0 := (isMinOn_iff.mp hmin) _ hmem
      rw [Function.iterate_succ_apply']
      push_cast
      linarith
  have h1 := key N le_rfl
  have h2 := hcon N le_rfl
  have h3 : b - a < N * δ := by rwa [div_lt_iff₀ hδpos] at hN
  linarith

/-- **A fixed point blocks the crossing forever.** For a monotone flow with a fixed point `u_f`, every start at or below `u_f` stays at or
below it (an infrared fixed point: Banks–Zaks shape). -/
theorem no_crossing_of_fixed_point {σ : ℝ → ℝ} (hmono : Monotone σ) {uf u0 : ℝ} (hf : σ uf = uf) (h0 : u0 ≤ uf) :
    ∀ n, σ^[n] u0 ≤ uf := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc σ (σ^[k] u0) ≤ σ uf := hmono ih
      _ = uf := hf

/-- **Λ finite across the stretch, plus the direction, gives the crossing.** A clock on `[a, b]` excludes fixed points there; with the
direction `u ≤ σ u` (the sign of asymptotic freedom) and continuity the flow crosses `[a, b]` within one number of doublings. -/
theorem crossing_of_clock {σ Φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hσ : ContinuousOn σ (Set.Icc a b))
    (hdir : ∀ u ∈ Set.Icc a b, u ≤ σ u) (hc : IsClock σ Φ (Set.Icc a b)) :
    ∃ N : ℕ, ∀ u0 ∈ Set.Icc a b, ∃ n ≤ N, b ≤ σ^[n] u0 := by
  refine crossing_of_no_fixed_point hab hσ (fun u hu => lt_of_le_of_ne (hdir u hu) ?_)
  intro heq
  exact no_clock_of_fixed_point hu heq.symm hc

/-! ## 5. The selection principle: an act with a floor excludes an infrared fixed point -/

/-- An act chain has a **floor** when its existence at layer `n` (the box of side `2ⁿ L₀`) stays above one `m > 0` from some layer on. -/
def HasFloor (E : ℕ → ℝ) : Prop := ∃ m > 0, ∃ n0 : ℕ, ∀ n, n0 ≤ n → m ≤ E n

/-- **A floor forces the act number to grow without bound**: with existence at least `m` at side `2ⁿ L₀`, the act number
`zₙ = Eₙ · 2ⁿ L₀` exceeds every bound. -/
theorem floor_forces_unbounded {E : ℕ → ℝ} {L0 : ℝ} (hL0 : 0 < L0) (hf : HasFloor E) :
    ∀ M : ℝ, ∃ n : ℕ, M < E n * (2 ^ n * L0) := by
  intro M
  obtain ⟨m, hm, n0, h⟩ := hf
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (M / (m * L0)) (by norm_num : (1 : ℝ) < 2)
  refine ⟨max n0 N, ?_⟩
  set n := max n0 N
  have hpow : (2 : ℝ) ^ N ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (le_max_right n0 N)
  have hM : M < 2 ^ n * (m * L0) := (div_lt_iff₀ (mul_pos hm hL0)).mp (lt_of_lt_of_le hN hpow)
  have hE : m ≤ E n := h n (le_max_left n0 N)
  have hpos : 0 < (2 : ℝ) ^ n * L0 := mul_pos (pow_pos (by norm_num) n) hL0
  calc M < 2 ^ n * (m * L0) := hM
    _ = m * (2 ^ n * L0) := by ring
    _ ≤ E n * (2 ^ n * L0) := mul_le_mul_of_nonneg_right hE hpos.le

/-- **Selection principle (toy).** If the act number follows a monotone flow (`zₙ = σⁿ(z₀)`) that has a fixed point `u_f` at or above
its start (an infrared fixed point: long-distance scale invariance), the act has no floor: it behaves like payload. -/
theorem fixed_point_no_floor {σ : ℝ → ℝ} (hmono : Monotone σ) {uf z0 L0 : ℝ} (hL0 : 0 < L0) (hf : σ uf = uf)
    (h0 : z0 ≤ uf) (E : ℕ → ℝ) (hE : ∀ n, E n * (2 ^ n * L0) = σ^[n] z0) : ¬ HasFloor E := by
  intro hfl
  obtain ⟨n, hn⟩ := floor_forces_unbounded hL0 hfl uf
  rw [hE] at hn
  exact absurd (no_crossing_of_fixed_point hmono hf h0 n) (not_le.mpr hn)

/-- **Hostable with a non-trivial act ⇒ no infrared fixed point (toy).** An act chain with a floor, whose act number follows a monotone
flow, rules out every fixed point of the flow at or above the start. This selects; it does not derive: whether a given theory's act has
a floor is the hypothesis. -/
theorem floor_excludes_fixed_point {σ : ℝ → ℝ} (hmono : Monotone σ) {z0 L0 : ℝ} (hL0 : 0 < L0) (E : ℕ → ℝ)
    (hE : ∀ n, E n * (2 ^ n * L0) = σ^[n] z0) (hfl : HasFloor E) : ∀ uf, z0 ≤ uf → σ uf ≠ uf :=
  fun _ h0 hf => fixed_point_no_floor hmono hL0 hf h0 E hE hfl

end Attempts.R4.Minting
