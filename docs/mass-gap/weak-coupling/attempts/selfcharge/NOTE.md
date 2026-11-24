# Route (d): self-charge. Attempt note (2026-11-21)

Goal (RULES.md): a precise lemma towards `UniformGDS` (`../../../formal/OneScale/CorollaryB.lean`), or a documented failure with
the reason. Guiding principle (PREP.md): a gluon carries the colour it transmits, so "the carriers carry charge" and "the order of
transports matters" are one property; the attempt was to find the quantitative inequality in which non-commutativity costs enough to
bound the box influence.

Claim levels used below: **proved** (complete proof here, Lean where marked), **standard** (textbook fact, cited, not reproved),
**heuristic** (argument with a named gap), **conjecture**.

Lean: `../../../formal/Attempts/SelfCharge/Basic.lean` (built in `~/formal-att-d`, status in section 9).
Script: `charged_probe.py` (one small CPU check, section 7).

---

## 0. Result in one paragraph

All three candidates measure the same object: the **adjoint action** of the group, i.e. commutators. Equidistribution distinguishes
SU(2) from U(1) only for the adjoint (colour-carrying) part; the Ricci curvature of a bi-invariant metric is
Ric(X, X) = ¼ Σ_i ‖[X, E_i]‖²; and the one inequality with a sign that I found, the **diamagnetic deficit identity** (proved, Lean),
pays the summed adjoint loop shortfall. That object passes the photon and Z₂ tests for the right reason, because it vanishes
identically for abelian groups. It fails at weak coupling for one quantitative reason, proved as **local flatness**:
‖aka⁻¹k⁻¹ − 1‖ ≤ 2‖a − 1‖‖k − 1‖. Every per-link self-charge effect is O(g²), so it becomes O(1) only over about 1/g² lattice
units: the lattice scale, not a physical one. A bound produced at that scale would give a mass ~ g^p/a → ∞, which is false for
gauge-invariant influence (the **scale filter**, heuristic). The self-charge survives the continuum limit only through the
running coupling, b₀ ∝ (11/3)C_A. Inside b₀ the dominant part (paramagnetic, spin, "4") has the anti-screening sign, opposite to
the diamagnetic damping ("1/3"). Finally, the **sharp-coefficient lemma** (proved, Lean) shows that any layer inequality in which
self-charge "costs a fixed amount per layer" gives a uniform physical scale **only if the cost is the exact asymptotic-freedom
coefficient**. A soft inequality that loses any constant gives a scale that runs off to infinity in physical units. So route (d)
does not produce a reach. It reduces to (exact two-loop running for an influence-defined coupling) + (a one-scale certificate),
and it states precisely what a self-charge inequality would have to be (Conjecture SC, section 6.3).

---

## 1. What is required, and the tests

`UniformGDS`: at every level k, thin cubes of side ℓ_k = ⌈L₀/a_k⌉ satisfy GDS with one γ < 1 (PROOF-NOTE §1.7, §7). It must fail
for 4D U(1) at weak coupling (massless photon) and for 4D Z₂ at weak coupling (gap, no confinement; GDS^∂ implies the area law
for connected G by Chatterjee's theorem, and should fail for deconfined Z₂ as well, PROOF-NOTE §10.3).

## 2. Self-charge, made precise

- The field strength (and every disturbance of the gauge field) transforms in the **adjoint** representation Ad: G → GL(𝔤),
  Ad_k X = kXk⁻¹. "The carrier carries charge" means that Ad is non-trivial. For connected G that holds iff G is non-abelian; for a
  finite group the conjugation action is trivial iff the group is abelian. "Order of transports matters" is the same statement:
  Ad_k X − X = (kX − Xk)k⁻¹. (`nonabelian_loop_value_moves` in `evidence/Dmp/Gauge.lean` is the S₃ instance.)
- The kernel of Ad is the **centre**: centre elements carry no adjoint charge. That is consistent with MG3: the centre twists are
  invisible to every adjoint quantity below.

**Lemma 2.1 (local flatness; proved, Lean `norm_comm_le`, `norm_group_comm_le`, `group_comm_of_comm`).** In any normed ring,
ak − ka = (a−1)(k−1) − (k−1)(a−1), hence ‖ak − ka‖ ≤ 2‖a−1‖‖k−1‖. If the inverses have norm ≤ 1 (unitaries, operator norm), then
‖aka⁻¹k⁻¹ − 1‖ ≤ 2‖a−1‖‖k−1‖. If a and k commute, aka⁻¹k⁻¹ = 1 exactly.

*Meaning.* At weak coupling the links lie within O(g) of the identity, up to gauge, so every effect of non-commutativity between
two such elements is O(g²). This is the precise form of "the group looks flat locally".

**Lemma 2.2 (Haar average of the commutator; proved here, uses Schur's lemma, standard).** For an irreducible unitary
representation of dimension n and any a: ∫ ‖ka − ak‖²_F dk = 2n(1 − |χ(a)/n|²).

*Proof.* ‖ka − ak‖²_F = 2n − 2 Re tr(a* k* a k), and ∫ k* a k dk = (χ(a)/n)·1 by Schur. ∎

- U(1) (n = 1): 0.
- SU(2) fundamental, a = e^{iθσ₃}: 4 sin²θ ≈ 4θ². This is **first** order in the deviation of a, against **second** order
  (Lemma 2.1) when k is near 1. So the self-charge acts at first order only after the transports have spread over the group.
  That spreading is what weak coupling withholds.
- The average vanishes iff a is central (|χ(a)| = n).

## 3. Candidate (i): equidistribution of transports

**Standard fact 3.1.** Let k₁, …, k_m be independent heat-kernel steps at time s on a compact connected G, and ρ irreducible.
Then E ρ(k₁⋯k_m) = e^{−msC_ρ}·1, with C_ρ the Casimir. The product equidistributes at the rate set by the spectral gap.

**Photon test of the naive form: fails.** For U(1) with charge q, C = q²/2 > 0: phases equidistribute too, which is the
perimeter-law decay of charged Wilson lines. Equidistribution of the transport itself uses no non-commutativity.

**Repaired form: passes.** Use the transport acting on a disturbance, i.e. Ad. Then E Ad(k₁⋯k_m) = e^{−msC_A}. For U(1) and Z₂ the
adjoint is trivial (C_A = 0) and there is no decay. For SU(N), C_A = N. This is the "C_A = N versus 0" line of README §7.

**Why it does not survive weak coupling.**
1. *Scale.* At coupling g one link step has s ~ g², so msC_A = O(1) needs m ~ 1/(C_A g²) links: about a/g² in physical units,
   which → 0 as a → 0. It would "prove" a mass ~ g²/a → ∞.
2. *Gauge-variant.* The decay of E Ad(transport along a fixed path) is the self-energy of a static adjoint source, a linear UV
   divergence of the lattice. It is renormalised away in every physical quantity.
3. *Single path.* Influence on gauge-invariant observables does not run along one path with independent increments. It runs
   along all paths, and what matters is how paths **interfere**. That is candidate (iii), section 4.

Verdict: **fails** (wrong group class in the naive form, wrong scale in the repaired form).

## 4. Candidate (iii): the diamagnetic deficit, an exact inequality with a sign

**Setting.** Covariant random-walk representation: for a unitary connection U, a representation ρ of dimension n and m > 0 (or
Dirichlet data on a box),

  G_U^ρ(x, y) = Σ_{walks ω: x→y} w(ω) ρ(U_ω),   w(ω) = (2d + m)^{−|ω|−1},   G_0(x, y) = Σ_ω w(ω).

The covariant harmonic extension from the boundary of a box has the same form, with walks stopped at the boundary. This is the
linear response of a charged *scalar* disturbance to a change of boundary data.

**Theorem 4.1 (deficit identity; proved, Lean `deficit_identity`, `shortfall_eq`).** For any finite family of vectors v_i in a real
inner-product space, weights w_i and any constant c:

  ‖Σ w_i v_i‖² = c (Σ w_i)² − Σ_{i,j} w_i w_j (c − ⟨v_i, v_j⟩),

and if ‖v_i‖² = ‖v_j‖² = c then c − ⟨v_i, v_j⟩ = ½‖v_i − v_j‖² ≥ 0.

Applied with v_ω = ρ(U_ω) in the Hilbert–Schmidt inner product (c = n), the pair term is the **shortfall of the closed loop ωω'⁻¹**:

  ‖G_U^ρ(x, y)‖²_HS = n G_0(x, y)² − Σ_{ω, ω'} w(ω) w(ω') (n − Re χ_ρ(U_{ωω'⁻¹})).

This is the README's "loop shortfall" (weight times shortfall is the Wilson action), now appearing as the exact price the
response pays.

**Corollaries (proved, Lean).**
- `diamagnetic`: ‖G_U^ρ‖_HS ≤ √n G_0. Kato's inequality: the response is never above the free one.
- `photon_no_deficit`: if all transports agree there is no deficit. For U(1) and Z₂ the field disturbance is adjoint-neutral, so
  it propagates exactly like the free one: massless, as the photon must be. **Photon test: passed, for the right reason.**
- `deficit_strict`: if every pair of distinct walks has shortfall ≥ δ, the deficit is at least δ(W² − Σ w_i²).
- `su2_adj_shortfall`, `su2_adj_shortfall_zero_iff`: for SU(2), χ_adj = χ_f² − 1 = 4a₀² − 1. The adjoint shortfall
  3 − χ_adj = 4(1 − a₀²) vanishes exactly at the centre a₀ = ±1. The deficit is blind to centre twists (MG3), so it is not the
  centre mechanism of confinement. That matches the known perimeter law of adjoint loops (string breaking by gluons).

**Why it does not survive weak coupling.** Three independent reasons.
1. *Scale (section 7 checks it numerically).* A loop of length P has adjoint shortfall ~ C_A g² P at weak coupling. That is the
   perimeter self-energy, and Lemma 2.1 caps it at O(g²) per step. So the deficit becomes O(1) for walks longer than ~1/g², and
   the lowest eigenvalue of the covariant Laplacian is ~ g² in lattice units (Combes–Thomas then gives decay at a rate ~ g per
   lattice unit). The same holds for a U(1) **charged** probe. The deficit is the ordinary diamagnetism of charged particles. What
   is non-abelian is only that the gauge field's own disturbance is such a charged probe.
2. *Wrong operator (standard physics).* The gluon is a vector, not a scalar. Its quadratic fluctuation operator in a background
   (background Feynman gauge) is −D² − 2 ad F. The spin term 2 ad F is not of walk form with unitary weights, has no sign, and
   dominates:
   - it produces a negative mode in a constant chromomagnetic field (Nielsen–Olesen instability);
   - in the one-loop coefficient b₀ ∝ C_A(4 − 1/3), the paramagnetic spin part "4" anti-screens and the diamagnetic orbital part
     "1/3" screens (Nielsen 1981, Hughes 1980/81).

   So the diamagnetic "cost" is the minor part of the self-charge, and it pulls in the direction opposite to the net effect. At
   weak coupling, self-charge makes the field bind more strongly to itself as the scale grows (the coupling grows). It does not
   directly damp the response.
3. *Protection.* The lattice-scale decay of a charged scalar walk is an unprotected mass renormalisation. For the gluon, gauge
   invariance (transversality of the self-energy, Π(0) = 0) cancels it. Gauge-invariant influence stays photon-like up to the
   distance where the coupling has run (section 6.1).

Verdict: **exact and correctly signed, but it acts at the lattice scale, on the subdominant (scalar) part of the response.** Fails as
a route to `UniformGDS`.

## 5. Candidate (ii): curvature (Bakry–Émery, Shen–Zhu–Zhu)

**Standard fact 5.1** (Milnor 1976). For a bi-invariant metric, Ric(X, X) = ¼ Σ_i ‖[X, E_i]‖² = −¼ B(X, X), with B the Killing
form, and the sectional curvature is K(X, Y) = ¼‖[X, Y]‖² for orthonormal X, Y. The curvature **is** the adjoint action. U(1): 0.
Z₂: not a manifold.

**The criterion** (SZZ, arXiv:2204.12737): Ric + Hess S ≥ K > 0 on G^E gives a log-Sobolev inequality and the gap. Ric is O(1);
Hess S is O(β). So it holds only for β ≲ Ric/(C(d−1)): strong coupling.

**Why no version survives weak coupling.**
1. *Globally:* S has maxima on the compact G^E, where Hess S ≤ −cβ.
2. *Locally (small fields):* Hess S = β·(lattice curl-curl: gauge zero modes, photon-like low modes ~ β/ℓ²) + a field-dependent
   indefinite part of size β|F| ~ βg ~ 1/g. That is the spin term again, and it exceeds Ric = O(1) by a factor 1/g.
3. *Even granting a local criterion with K ~ Ric:* the resulting spatial decay rate (Stroock–Zegarlinski type, ~ log(1 + K/(Cβ)))
   is ~ g² per lattice unit, a UV rate that the scale filter (6.1) rejects.
4. *Multiscale:* after blocking to scale L, the curvature of the block variables stays O(1) while the blocked stiffness is β(L).
   The criterion applies once β(L) ≲ Ric/C, i.e. at the strong-coupling end. Getting there with a controlled blocked Gibbs measure
   is the Bridge itself (Balaban's large-field problem), not a consequence of curvature.

Photon test: Ric = 0, so the method is silent for U(1) at every coupling (silent, not wrong). Z₂: not applicable. Verdict:
**no weak-coupling content; the multiscale version is the Bridge.**

## 6. What survives

### 6.1 The scale filter (heuristic)

By Lemma 2.1, non-commutativity costs O(g²) per link and reaches O(1) only over ~1/g² lattice units. Any inequality that turned
this into decay of gauge-invariant correlations would give a rate ~ g^p/a, which → ∞ in physical units. Perturbation theory says
otherwise at distances 1/g² ≪ r ≪ ξ, where gauge-invariant correlations are power-like (e.g. ⟨tr F² tr F²⟩_c ~ r⁻⁸ at tree level,
two-gluon exchange, the same as two photons).

*Status:* heuristic. At fixed distance and β → ∞ on a fixed torus, the free-field limit is rigorous. The joint regime r ~ g^{−p}
(where g² log r → 0, so perturbation theory should hold) is standard physics, not proven here.

*Use:* a filter for any route (d) argument: **a self-charge bound that acts at the lattice scale is not merely too weak, it is
false.** The self-charge must enter the reach logarithmically, through the running: per e-fold of length Δ(1/g²) = 2b₀, with
b₀ = 11C_A/(48π²). For SU(2) Wilson that is Δβ = 8b₀ ln 2 = 0.2575 per doubling (README §5). For pure U(1), b₀ = 0 (no running,
Coulomb phase); for Z₂ there is no continuous coupling (the deconfined flow goes to weak coupling).

### 6.2 The sharp-coefficient lemma (proved, Lean)

Let y_j be an inverse coupling at layer j (block scale 2^j a), and suppose a proved layer inequality y_{j+1} ≤ y_j − c, c > 0
(`layers_decrease`). Then the threshold y* is reached within J = ⌈(y₀ − y*)/c⌉ layers (`layers_reach`). Let the lattice spacing
follow the true one-loop flow, aΛ = 2^{−y₀/c₀}, with c₀ the true per-layer decrement. The guaranteed block scale has
log₂(LΛ) = J − y₀/c₀ (`logScale`), and:
- `scale_bounded`: if c ≥ c₀, then log₂(LΛ) ≤ 1 − y*/c for all 0 ≤ y* ≤ y₀ (a uniform physical scale);
- `scale_unbounded`: if c < c₀, then log₂(LΛ) → +∞ as y₀ → ∞ (no uniform L₀).

**Consequence.** A self-charge inequality of the form "non-commutativity costs at least c per layer" yields `UniformGDS` only if c
is the exact asymptotic-freedom coefficient.

- The two-loop term, which produces the power-law prefactor of a(β), must also be matched, with a remainder that is summable along
  the flow. With y_j decreasing linearly, Σ_j y_j⁻² < ∞ uniformly. Only the one-loop bookkeeping is formalised.
- Soft methods (equidistribution rates, curvature constants, Dobrushin-type contractions) lose constants by construction. So they
  cannot give uniformity, however non-abelian their input.
- The same holds in other coordinates. For the lead route's κ(2ℓ) ≤ f(κ(ℓ)), near the photon-like fixed point κ* the deviation
  must escape with the exact marginal coefficient (x' = x + bx² + …, with b equal to the true one).

### 6.3 Conjecture SC (the precise form of route (d))

For SU(N) with the Wilson action, there are an influence-defined, gauge-invariant inverse coupling y(ℓ, β) and a threshold y* with:
1. y(2ℓ) ≤ y(ℓ) − c₀ − c₁/y(ℓ) + O(y(ℓ)⁻²) whenever y(ℓ) ≥ y*, with c₀ and c₁ the universal one- and two-loop coefficients. One
   candidate for y: −log of the block GDS constant on thin cubes of side ℓ.
2. y(ℓ) ≤ y* implies GDS(V_ℓ, γ).

Then `UniformGDS` follows, by section 6.2 and its two-loop refinement (bookkeeping only).

- Photon test: (1) fails for U(1) (c₀ = 0). Z₂ test: (1) fails (no continuous running; deconfined flow).
- Status: **conjecture**.
  - (1) is asymptotic freedom for a non-perturbatively defined coupling. That is Balaban's small-field territory, and it holds only
    while y is large.
  - (2) is a one-scale certificate, which our proven window gives only for β < 0.09.
  - The two ranges do not overlap. Route (d) supplies no crossing; it fixes what the crossing must look like.

## 7. Numerical check: at which scale does the deficit act? (new; CPU, one process, about 2 minutes)

`charged_probe.py` runs our heat baths (`lattice/su2.py`, `lattice/u1.py`) on periodic L⁴ lattices and computes λ_min of
−Δ_U = Σ_μ (2 − T_μ − T_μ†), (T_μψ)(x) = ρ(U_μ(x))ψ(x+μ̂). Sanity checks:
- ρ is a homomorphism to 10⁻¹⁶;
- tr Ad = 4a₀² − 1;
- λ_min = 0 on the free field.

Prediction from section 4.1: λ_min/g² ≈ constant in β for every charged probe, and λ_min = 0 for the neutral one. Results in
`charged_probe.json`:

λ_min divided by the squared coupling (g² = 4/β for SU(2), e² = 1/β for U(1)); mean of 3 configurations, 50 + 3×10 sweeps from a
cold start.

| probe | L | β = 4 / 16 / 64 (SU(2)); 2 / 8 / 32 (U(1)) | reading |
|---|---|---|---|
| SU(2) adjoint (the gluon's own disturbance) | 6 | 1.00 / 0.96 / 0.98 | **λ_min = (1.00 ± 0.04) g²**: constant over a factor 16 in g², the same on both volumes |
| | 8 | 1.03 / 0.99 / 0.98 | |
| SU(2) fundamental | 6 | 0.66 / 0.49 / 0.69 | ~ 0.4 to 0.7 g², lower on the larger volume (torus holonomy / rare flat regions) |
| | 8 | 0.49 / 0.42 / 0.41 | |
| U(1) charge 1 | 6 | 0.92 / 4.0 / 2.6 | positive (diamagnetic), dominated by the torus holonomies (flat U(1) connections are not pinned): no clean scaling |
| | 8 | 0.98 / 0.82 / 1.39 | |
| U(1) neutral (adjoint, the photon's own disturbance) | 6, 8 | 0 / 0 / 0 | exactly 0: no deficit (Theorem 4.1, `photon_no_deficit`) |

Solver note: the U(1)-neutral L = 8 rows in the json read 0.5858 = 2 − 2cos(2π/8). That is a Lanczos (`which="SA"`) artefact: the
solver missed the exact constant zero mode of the free Laplacian. Shift-invert gives 1.6·10⁻¹⁶. Cross-check on one β = 16, L = 8
SU(2) configuration: SA and shift-invert agree for the adjoint (0.24377) and the fundamental (0.10070, doubly degenerate).

**Reading.** The deficit carried by the gluon's own (adjoint) disturbance acts at the lattice scale. λ_min ≈ g² in lattice units
gives a decay rate ~ g per lattice spacing, i.e. ~ g/a in physical units, which → ∞ as a → 0. This holds over β = 4 to 64 with no
sign of a physical scale. It is what section 4 predicted. It is not a physical gap, and the scale filter (6.1) says it cannot be one
for gauge-invariant influence.
- Charged U(1) probes pay a deficit too: the mechanism is generic diamagnetism.
- The photon's own disturbance pays nothing.

This test is new. It does not re-verify an established number.

## 8. Photon and Z₂ checks, summary

| item | U(1), weak coupling | Z₂, weak coupling | right reason? |
|---|---|---|---|
| Lemma 2.1 (local flatness) | commutator ≡ 1: nothing proved | same | yes (abelian) |
| (i) naive equidistribution | **applies, would prove too much**: rejected | n/a | no |
| (i) adjoint equidistribution | C_A = 0: nothing | trivial conjugation: nothing | yes; fails anyway at weak coupling (scale) |
| (iii) deficit identity | v_ω all equal: no deficit, massless | same | yes; fails anyway at weak coupling (scale, spin term) |
| (ii) curvature | Ric = 0: silent | not defined | trivially |
| sharp-coefficient lemma / Conjecture SC | c₀ = 0: hypothesis fails | no running: hypothesis fails | yes |

No argument in this note proves a reach for U(1) or Z₂.

## 9. Verdicts

| statement | status |
|---|---|
| Lemma 2.1 local flatness (ring, group, abelian forms) | **proved, Lean** |
| Lemma 2.2 Haar average of the commutator | proved (given Schur) |
| Theorem 4.1 deficit identity, shortfall = ½ distance², diamagnetic, photon, strict | **proved, Lean** |
| SU(2) adjoint shortfall, zero exactly at the centre | **proved, Lean** (real algebra) and checked numerically |
| Candidate (i) as a route to `UniformGDS` | **fails** (photon test in the naive form; lattice scale in the adjoint form) |
| Candidate (ii) as a route | **fails** at weak coupling; the multiscale form is the Bridge |
| Candidate (iii) as a route | **fails**: exact and signed, but lattice-scale and only the scalar (diamagnetic) part; the dominant spin part has the opposite sign |
| Scale filter (lattice-scale self-charge bounds are false) | heuristic (perturbative) |
| Sharp-coefficient lemma (one-loop bookkeeping) | **proved, Lean** |
| Conjecture SC ⇒ `UniformGDS` | proved modulo the two-loop bookkeeping (not formalised) |
| Conjecture SC | **open**; (1) Balaban-type, (2) a one-scale certificate; the ranges do not meet |

**Lean status (2026-11-21).** `Attempts/SelfCharge/Basic.lean` builds in `~/formal-att-d`
(`lake build Attempts.SelfCharge.Basic`: "Build completed successfully"). It has no `sorry` and only three deprecation warnings
(`if_pos`/`if_neg`). Theorems:
- `comm_eq`, `norm_comm_le`, `group_comm_eq`, `norm_group_comm_le`, `group_comm_of_comm` (section 2);
- `norm_sq_sum`, `deficit_identity`, `shortfall_eq`, `shortfall_nonneg`, `diamagnetic`, `photon_no_deficit`, `deficit_strict`
  (section 4);
- `su2_adj_shortfall`, `su2_adj_shortfall_zero_iff` (centre invisibility);
- `layers_decrease`, `layers_reach`, `logScale`, `scale_bounded`, `scale_unbounded` (section 6.2).

These are abstract statements (normed rings, inner-product spaces, reals). Not formalised: the identification with covariant walks
on the lattice framework's `GaugeConnection`, Lemma 2.2 (Schur), and the two-loop bookkeeping.

## 10. The single most promising next step

Make the sharp-coefficient lemma a pre-registered test for the lead route. Define the influence coupling y(ℓ) := −log κ(ℓ)-type
from the lead route's box influence, at large β (β = 4–16 for SU(2), small boxes ℓ = 2–8, deep in the perturbative regime, cheap on
CPU). Measure whether y(2ℓ) − y(ℓ) approaches the universal drift (SU(2) Wilson normalisation: −0.2575 per doubling in β units,
adjusted to y's normalisation by the tree-level relation), and whether U(1) gives 0.
- If it does, the lead route's recursion carries the self-charge with the exact coefficient. Route (d) and the lead route merge,
  and the open part is exactly the one-scale certificate at the junction.
- If the drift is absent or has the wrong coefficient, no recursion for that κ can give a uniform scale (section 6.2), and the lead
  route needs a different influence quantity before any chessboard proof is attempted.

## References (ideas only; nothing copied)

- Shen, Zhu, Zhu, arXiv:2204.12737 (Bakry–Émery for lattice Yang–Mills).
- Milnor, "Curvatures of left invariant metrics on Lie groups", Adv. Math. 21 (1976) 293.
- Nielsen, "Asymptotic freedom as a spin effect", Am. J. Phys. 49 (1981) 1171.
- Hughes, Phys. Lett. B 97 (1980) 246 and Nucl. Phys. B 186 (1981) 376.
- Nielsen, Olesen, Nucl. Phys. B 144 (1978) 376 (unstable chromomagnetic mode).
- Simon, "Kato's inequality and the comparison of semigroups", J. Funct. Anal. 32 (1979) 97 (diamagnetic inequality).
- Combes, Thomas, Commun. Math. Phys. 34 (1973) 251 (exponential decay of resolvents).
- Low-lying, localised eigenmodes of covariant Laplacians in the Yang–Mills vacuum: Greensite, Olejník, Polikarpov, Syritsyn,
  Zakharov (2005), arXiv number not re-checked; to be read before quoting.

All bibliographic data above are from memory and **not re-checked** in this session; check them before quoting.
