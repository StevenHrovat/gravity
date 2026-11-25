# Round 2, attempt D: from a step-scaling recursion to (H1) `EffectiveConvergence` (2026-11-21)

Brief: state and prove the cleanest conditional theorem that reduces H1 (the quantum half) to a step-scaling statement for a
Schroedinger-functional-type (SF) box coupling; sort the inputs into (i) perturbative, (ii) non-perturbative, (iii) supplied by the
OpenAI construction; Lean if clean; photon test. Coordinator's addition: write the recursion and the L₁ condition in α_s as well as g²,
and say whether a natural α_s value marks the hand-over.

Claim levels: **proved (Lean)**, **proved (paper)**, **standard** (textbook or literature, cited from memory, not reproved here),
**heuristic**, **conjecture**.

Lean: `../../../formal/Attempts/R2/StepScaling.lean` (the recursion lemma), `../../../formal/Attempts/R2/StepScalingH1.lean` (the
conditional theorem). Both build in `~/formal-att-d` (`lake build Attempts.R2.StepScaling Attempts.R2.StepScalingH1`: "Build completed
successfully", no warnings in these files). No `sorry`. `#print axioms` on the main theorems: `propext`, `Classical.choice`,
`Quot.sound` only. No numerics were run, so nothing was pre-registered.

---

## 0. Result in one paragraph

The requested conditional theorem holds and is formalised (`gap_of_stepScaling`): a line of constant physics set by the box coupling
(α_s(L₁) = α*), weak bare coupling, bounded running per doubling, and **control of the block specifications by the coupling** give
`EffectiveConvergence` at L₁, and with (H2) the physical gap in units of L₁. But the bookkeeping shows where the weight sits. The
step-scaling recursion enters H1 only through "the scale-setting layer goes to infinity", which needs only *bounded* running. The
**exact** one- and two-loop coefficients are not needed for H1 or for the gap. They are needed for **asymptotic scaling**, i.e. for
identifying the line of constant physics with the bare-coupling law a(β) (`scaling_window`, and `scaling_drift` for the sharpness).
The sharp-coefficient obstruction of round 1 therefore does not bind H1 once the scale is set by a genuine coupling. It binds routes
that take the scale from one quantity (the bare law) and the contraction from another (κ, which does not run). The control hypothesis
carries all the non-perturbative content, and as a hypothesis it is stronger than H1. It splits into an **elementary transport lemma**
(proved on paper) and **one open statement at a weak-coupling scale**: relative convergence of the effective density, large fields
included. That statement is Stage A of `H1-OPENAI.md`. Photon test: for U(1) the coupling does not run, so a line of constant physics
from weak bare coupling does not exist and the theorem is empty (`photon_no_line`, Lean).

## 1. The recursion in g², β and α_s

Inverse coupling u_j of the box with side 2^j ℓ₀ (lattice units). Step-scaling recursion:

  u_{j+1} = u_j − c₀ − c₁/u_j + r_j,   |r_j| ≤ K/u_j² + η_j   (η_j lattice artefacts, O(a/L) = O(2^{−j}), summable).

The normalisation is free (`phi_rescale`, `step_rescale`, Lean). The rescaling u ↦ s·u maps (c₀, c₁) ↦ (s c₀, s² c₁) and shifts the
scale function by a constant. The one- and two-loop coefficients are universal for every coupling with g²_new = g² + O(g⁴)
(**standard**). With β₀ = 11N/3 and β₁ = 34N²/3 (pure gauge):

| normalisation | c₀ (per doubling) | c₁ | SU(2) | SU(3) |
|---|---|---|---|---|
| 1/α_s = 4π/g² | β₀ ln2/(2π) | β₁ ln2/(8π²) | 1/α(2L) = 1/α(L) − 0.809 − 0.398·α(L) | − 1.214 − 0.895·α |
| β = 2N/g² (SU(2): β = 1/(πα)) | | | β(2L) = β(L) − 0.2575 − 0.0403/β(L) | |

The SU(2) β-row is the normalisation of follow-up experiment 1, which measured the one-loop drift as −0.268 (fit) and −0.261 (fit over
L ≥ 8) against −0.2575. Two-loop asymptotic scaling in doublings:

  log₂(1/(aΛ)) = phi(u₀) + const,   phi(u) = u/c₀ − (c₁/c₀²) ln u.

**The L₁ condition.** L₁ is the box size at which the coupling takes a fixed value: α_s(L₁) = α*, equivalently g²(L₁) = 4πα*, or
u(L₁) = u*. For U(1) the inverse coupling does not decrease (pure compact U(1): no running, follow-up E1.2; with charged matter:
screening, α decreases with distance). From a weak bare coupling it therefore never reaches the O(1) value (section 5).

## 2. The recursion lemma (proved, Lean: `StepScaling.lean`)

- `phi_step`: one step changes phi by −1 up to |r|/c₀·(1 + |c₁|/(c₀u)) + (c₁² + 2|c₁|X²)/(c₀²u²), provided the step is at most half
  of u (|x| ≤ X ≤ u/2). The 1/u terms cancel exactly because phi carries the same c₁ as the recursion.
- `count_two_loop`: summed over the layers above a threshold U (steps in [x_min, X], 2X ≤ U), using the telescoping bound
  1/u_j² ≤ (1/x_min)(1/u_{j+1} − 1/u_j):
  |phi(u_J) − phi(u₀) + J| ≤ (A/x_min)(1/u_J − 1/u₀) + B·Σ η_j, **uniformly in u₀**, with A and B explicit (`cA`, `cB`).
- `crossing_exists`: with a decrement ≥ x_min > 0 above U, the first layer below U exists.
- `scaling_window`: crossing layer J_p of U, plus at most N further layers to the scale-setting layer J_t. Then
  |J_t − phi(u₀)| ≤ N + M, with M independent of u₀. In words: **the line of constant physics obeys two-loop asymptotic scaling.**
- `phi_diff_tendsto`, `scaling_drift` (sharpness): with any c₁' ≠ c₁ the distance |J_t − phi_{c₀,c₁'}(u₀)| grows like
  |c₁' − c₁|/c₀²·ln u₀ → ∞. The one-loop analogue (c ≠ c₀) is round 1's `scale_unbounded`.
- `floor_of_steps`, `photon_never_reaches`: if u_j − u_{j+1} ≤ η_j with Σ η ≤ H (no running, or screening, plus summable artefacts),
  then u_n ≥ u₀ − H for every n.

## 3. The conditional theorem (proved, Lean: `StepScalingH1.lean`)

Setting: levels k (bare theories). u k j is the box coupling at side ℓ₀2^j. J_k is the scale-setting layer, a_k = L₁/(ℓ₀2^{J_k})
(`spacing`), and the blocks have physical size exactly L₁ (`blockSize_eq`). P v k is the effective block specification at that side.

Hypotheses:
- **(UV)** u_k(0) → ∞: weak bare coupling.
- **(Run)** u_k(j) − u_k(j+1) ≤ C: bounded running per doubling.
- **(Tune)** u_k(J_k) → u*: line of constant physics, α_s(L₁) → α*.
- **(Ctrl)** reference specifications Q(w), one family per value w of the coupling, with
  SpecDist(Q(u_k(J_k)), P_k) ≤ η(J_k) and artefacts η(J) → 0 as the block side in lattice units grows.
- **(Cont)** SpecDist(Q(u*), Q(w)) ≤ ω(w − u*), with ω → 0 at 0.
- Fixed blocks and finite range: items 1 and 2 of `EffectiveConvergence`.

Results:
- `layers_tendsto`: (UV) + (Run) + (Tune) ⇒ J_k → ∞, hence a_k → 0 (`spacing_tendsto`).
- **`effectiveConvergence_of_stepScaling`**: (Tune) + (Ctrl) + (Cont) + J_k → ∞ ⇒ `EffectiveConvergence P block shell (Q u*)`, with
  δ_k = ω(u_k(J_k) − u*) + η(J_k). Uses the triangle inequality `specDist_trans`.
- **`gap_of_stepScaling`**: adds (H2) `LimitGDS block (Q u*)`. Block covariances then decay as C·e^{−mR}, with R in physical units
  (multiples of L₁), m > 0, uniformly in k ≥ k₀ and in the volume.

**What the theorem does and does not say.**
1. The exact coefficients are absent from the hypotheses. The gap comes out in units of L₁, the length where α_s = α*, and that
   needs no comparison with the bare law. The exact coefficients come back only when one asks whether L₁·Λ_bare-law stays fixed along
   the line. `scaling_window` answers yes, iff c₀ and c₁ are exact (`scaling_drift`). For a genuine coupling they are exact
   automatically (universality, **standard**); the follow-up confirmed c₀ numerically for the SF-type box coupling.
2. Round 1's sharp-coefficient lemma bound because the scale came from the bare law and the contraction from κ. κ has no tree-level
   coupling (follow-up E1.4), so the two scales can only agree through an exact coefficient. A coupling-defined scale removes that
   mismatch. It does not remove the work: everything sits in (Ctrl).
3. (Ctrl) is stronger than H1: restricted to the tuned line it *is* H1. So as a logical step the reduction is thin. Its value is the
   bookkeeping, and the split of (Ctrl) in section 4.
4. Only the H form is formalised. The W form (`EffectiveConvergenceW`) is the same argument with `InfluenceDevW` (which needs a
   triangle inequality of the same kind). Not done.

## 4. Splitting (Ctrl): transport plus one weak-scale statement

**Lemma T (transport, proved on paper, elementary; not in Lean).** Let ρ and ρ' be probability densities, with respect to the same
reference measure, on a finite-volume configuration space, and suppose sup|log ρ − log ρ'| ≤ ε.
- (a) For any measurable map or Markov kernel Φ (any number of blocking steps), the image laws satisfy the same bound. Reason:
  e^{−ε}μ ≤ μ' ≤ e^{ε}μ is preserved by pushforward.
- (b) For every block B of the image variables and every outside configuration, the conditional laws satisfy
  e^{−2ε} ≤ dq'/dq ≤ e^{2ε}. Reason: q'(dξ|η) = h q(dξ|η)/∫h dq(·|η), with h = dμ'/dμ ∈ [e^{−ε}, e^{ε}].
- Hence TVClose with e^{2ε} − 1 and SpecDist ≤ |B|(e^{2ε} − 1) (`specDist_of_tv`), **uniformly in the boundary condition**. The W
  form is analogous.

**Consequence.** Fix a weak-coupling scale L_p = 2^{−N}L₁. Then (Ctrl) at L₁, along the line, follows from:

- **(W_p) — OPEN.** Per volume, the effective density at scale L_p converges in relative sup norm:
  sup_U |log ρ_{k,p}(U) − log ρ_{∞,p}(U)| ≤ ε_k(v) → 0, **on all configurations, large fields included**.

This works because the theory at L₁ is the image of the theory at L_p under N blocking steps. The coupling at L₁ is then a continuous
functional of the L_p theory, provided the coupling is defined from block variables (a free-energy response of the effective theory
to a rotation of boundary block variables, rather than of fine links). So tuning at L_p and tuning at L₁ are the same condition.

The convergence is per volume (ε is extensive: ε ≤ (number of L_p cells)·δ_k). Per volume is enough for the gap in the order "mesh
first, then volume" (`H1-OPENAI.md` §4: in `gap_of_effective`, m and C do not depend on δ). The per-volume variant of
`EffectiveConvergence` and of `gap_of_stepScaling` is not formalised.

**Where the running from weak to O(1) coupling goes.** In this split, the N doublings from α_p at L_p to α* at L₁ are a property of
the single limit theory ρ_∞,p: which coupling it has after N blockings. Whether the coupling ever reaches an O(1) value (no infrared
fixed point below α*) is a statement about one theory, so it sits next to H2, not in H1. This is the catch of `H1-OPENAI.md` §4,
confirmed from the step-scaling side: H1 can be made "weak-coupling only" (W_p), but then the running through the intermediate range
belongs to the classical half.

## 5. Inputs, sorted

**(i) Perturbative, provable with known methods**
- c₀ and c₁ of the chosen box coupling.
  - One loop: exact finite-dimensional linear algebra per box size, as in follow-up experiment 1, plus the L → ∞ asymptotics (an
    analytic computation).
  - Two loop: known for the SF coupling in the literature (**standard**, from memory, not checked here).
  - Universality of c₀ and c₁ across couplings (**standard**).
- The formal expansion σ(u) = u − c₀ − c₁/u + O(u⁻²).
- These enter only asymptotic scaling (`scaling_window`), not the gap.
- Not perturbative, although it is often treated as such: a **rigorous** bound |r| ≤ K/u² on the remainder of the lattice coupling.
  It needs large-field control (ii). It also enters only asymptotic scaling.

**(ii) Non-perturbative**
- (a) **(W_p)**: relative convergence of the effective density at the weak scale on all configurations. The missing piece is lower
  bounds on large-field activities (`H1-OPENAI.md` Stage A). This is the open content of H1 in this form.
- (b) (Run) for the box coupling (bounded running per doubling). It is mild, and it follows from (W_p) at the weak end.
- (c) The limit theory's coupling reaches α* after finitely many doublings (no infrared fixed point). Property of one theory; with H2.
- (d) H2 (`LimitGDS`).

**Elementary, proved here:** the recursion bookkeeping (Lean), lemma T (paper), and the assembly (Lean).

**(iii) What the OpenAI construction supplies** (from `H1-OPENAI.md`; not re-read in the source)
- A tuned weak scale: their unit, where β = bar ≳ 9·10⁵ (`Selected.reaches`), i.e. g² ≈ 10⁻⁶, α ≈ 10⁻⁷. This is exactly (Tune) at L_p.
- Per-(level, volume) convergence of the small-field effective action and of their effective coupling (`Winter.convergence`): the
  small-field half of (W_p), per volume, which suffices.
- One-loop running with bounded drift (`Transfer`: |β_{m+1} − β_m − slope·log L_m| ≤ drift): (Run) for their coupling in their
  range. By `count_two_loop`, an O(1) error per step allows phi to drift by O(number of layers), so this alone gives no asymptotic
  scaling. They do not need it, because they tune; the gap theorem here does not need it either.
- Missing: large-field lower bounds (the other half of (W_p)) and anything beyond their unit.

## 6. A natural α_s value for the hand-over?

- **The bookkeeping marks one value.** The per-layer expansion (`phi_step`) needs a step of at most half the inverse coupling,
  Δ(1/α) ≤ (1/α)/2. With the one-loop step this is

  **α_h = 1/(2c₀^α) = π/(β₀ ln 2)**:  α_h ≈ 0.62 (SU(2)), 0.41 (SU(3)).

  Above α_h, one doubling more than doubles α_s, and no per-doubling perturbative bound can be organised. It is also where "the
  coupling is of order one" becomes literal on a dyadic ladder: the scale stops being resolved by doublings. Status: a property of
  the bookkeeping (proved as the validity condition of the lemma), a **heuristic** marker for the physics.
- **The rigorous perturbative control ends far lower.** The OpenAI small-field control ends at α ≈ 10⁻⁷. From 1/α ≈ 10⁷ down to 1/α ≈ 2
  at 0.81 per doubling is about 10⁷ doublings (consistent with `H1-OPENAI.md`'s 10⁷ e-folds).
- **Literature (standard, from memory, not checked).** The SF coupling's non-perturbative step-scaling function follows 2- to 3-loop
  perturbation theory up to roughly α ≈ 0.2 (SU(3)).
- **Heuristic comparison, bare and renormalised couplings not identified.** Our proven one-scale window is β < 0.09 for SU(2)
  (round 1), i.e. a bare α > 3.5.
- **Reading.** Between α_h ≈ 0.4–0.6 (where per-doubling bookkeeping ends) and α ≈ 3.5 (where our strong-coupling certificate
  starts) lies the stretch no method covers. In section 4 it sits with H2.
- **Two-loop term.** It is 0.49α (SU(2)) or 0.74α (SU(3)) relative to the one-loop step. That is smooth and marks no sharp value.

## 7. Unit tests

- **Photon (U(1)), proved (Lean): `photon_no_line`.**
  - If the coupling does not run (u_j − u_{j+1} ≤ η_j, Σ η ≤ H; this covers pure compact U(1), follow-up Δ_∞ = −0.0004, and
    screening), then (UV) and (Tune) contradict each other. There is no line of constant physics from weak bare coupling, so
    `gap_of_stepScaling` is empty.
  - Without (UV), e.g. U(1) at a fixed bare β in the Coulomb phase, the coupling is constant at every scale. Tuning is then trivial,
    and H1 may even hold, converging to the free photon block theory. That is harmless: H1 is not a gap claim, and H2 fails for the
    Gaussian photon limit by the sum rule (route (c): influence ≥ 1 at every box size).
  - No statement here gives U(1) a gap or a reach.
- **Z₂ (gap-only claim).**
  - The conclusion of `gap_of_stepScaling` is decay of block covariances, which is true for weak-coupling Z₂.
  - The hypotheses are not met: no continuous coupling, and no running towards strong coupling (the deconfined flow goes to weak
    coupling). So the theorem is silent rather than wrong.
  - It implies no area law, because its conclusion is decay only.

## 8. Not done

- **Rigorous one-loop number (optional item): not done, on purpose.** An interval-arithmetic enclosure of Δ(L) is cheap only for
  L ≤ 4. There Δ(2) = −0.346 and Δ(3) = −0.290 are dominated by lattice artefacts (follow-up E1.3), so it would certify nothing about
  c₀. c₀ itself is a textbook coefficient, and section 3 shows exact coefficients are not needed for H1 or the gap. Nothing was
  pre-registered, and nothing was run.
- Not formalised:
  - lemma T;
  - the per-volume variants;
  - the W-form version;
  - the identification of u with the follow-up's SF coupling on the lattice framework.

## 9. Verdicts

| statement | status |
|---|---|
| Two-loop layer count, uniform in u₀ (`count_two_loop`) | **proved, Lean** |
| Asymptotic scaling of the scale-setting layer with exact c₀, c₁ (`scaling_window`); drift with wrong c₁ (`scaling_drift`) | **proved, Lean** |
| Normalisation invariance g² / β / α_s (`phi_rescale`, `step_rescale`) | **proved, Lean** |
| (UV)+(Run)+(Tune)+(Ctrl)+(Cont) ⇒ H1; + H2 ⇒ gap in units of L₁ (`effectiveConvergence_of_stepScaling`, `gap_of_stepScaling`) | **proved, Lean** |
| Exact coefficients not needed for H1 or the gap, only for asymptotic scaling | **proved** (they appear in no hypothesis of the gap theorem) |
| Lemma T: relative-density closeness passes through blocking and to all conditional laws (factor e^{2ε}) | **proved, paper** |
| (Ctrl) along the line ⇐ (W_p) + lemma T, per volume | **proved, paper** (modulo a block-variable definition of the coupling) |
| (W_p): relative convergence at a weak scale, large fields included | **open** (the quantum half's real content) |
| The coupling of the limit theory reaches α* (no IR fixed point) | **open**, a one-theory statement, sits with H2 |
| α_h = π/(β₀ ln2) as the end of per-doubling bookkeeping | proved as the lemma's condition; **heuristic** as physics |
| Photon test | **passes** (Lean, `photon_no_line`; H2 fails for the photon limit) |

## 10. The single most promising next step

Formalise lemma T and the per-volume variant of `EffectiveConvergence`/`gap_of_effective` in Lean, with (W_p) as the only open
hypothesis of the quantum half. The project's H1 would then be, in Lean, exactly "relative convergence of the effective density at
one weak-coupling scale, large fields included". That is the OpenAI construction's missing large-field lower bound at its own unit:
one precise analytic target, with every other quantum-side input either elementary or a one-theory statement next to H2.
