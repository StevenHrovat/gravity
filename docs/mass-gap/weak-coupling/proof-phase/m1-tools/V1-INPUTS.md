# The two cited inputs of V1 under excision (m1-tools, 2026-11-22)

Brief: `V1-EXCISION.md` checked `[15]` section by section with the hole excised, but used two inputs from Balaban's
earlier papers in a modified form without proof: (i) gauge fixing with the gauge also fixed at the hole's boundary
sites; (ii) the propagator bounds for the locally modified constraint operator. Prove them, or reduce them to what
Balaban states. Read for this note: `[15]` Sects. A, C, E (the places where the inputs enter: pp. 279-281, 284-286,
293-295); `[6]` Sects. C-D (pp. 82-95: Theorem 2, the equations for the gauge transformation, the linear operators
`G'`, `H'`, `R` and the contraction). `[5]` (CMP 99, 389-434) is not at hand; what `[15]` quotes from it is used as
stated there. Lean: `formal/ProofPhase/M1/LocalMod.lean`. Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **Both inputs reduce to Balaban's unmodified statements plus two short lemmas proved here.** The hole changes
   Balaban's linear operators in two ways only: by a **compression** (the gauge is fixed, or the field is frozen, at
   the hole's sites: a Dirichlet condition) and by a **local perturbation** (the constraint reads the filling, and the
   background differs on the plaquettes at the hole's boundary). Both changes are confined to a set `S` near the hole
   of bounded size, because V1 with excision is used only for **subscale** holes (diameter `≤ L/4` in current units, so that every block face keeps at least half of its bonds
   at distance `≥ 2` from the hole;
   larger holes are carried in the large-field region, `TRAP.md` 0.2). Lemma FR (section 2) bounds the modified
   inverse by the unmodified one, in Balaban's weighted norms and in kernel decay; Lemma LP (section 3) gives the
   positivity of the modified operator that Lemma FR needs.
2. **Pinned inputs, corrected.** `[15]` uses three statements from the earlier papers at these places: `[6]` Theorem 2
   (axial to Landau gauge, `[15]` Sect. A, (19)-(21)); `[5]` Theorem 3.12 for the operator `H` (`[15]` (46); not
   Theorem 3.13 as `V1-EXCISION.md` said); `[5]` Theorem 3.13 for the operator `𝔊` (`[15]` Sect. E, (117)). Inside
   `[6]`, Theorem 2 rests on the bounds of `G'`, `H'` ((1.91)-(1.92)) and on `R` ((1.94)-(1.98)), quoted there from
   Balaban's propagator papers.
3. **One design addition, cheap: holes must be separated.** Lemma FR's constants grow with the number of holes that
   interact. With trapped holes at mutual distance `≥ R_sep(d, L)` (current units), the corrections of different holes
   form a convergent series (section 2, FR-multi). Holes closer than `R_sep` are merged into one record and carried in
   the large-field region until subscale, as for a large hole. Merging only regroups events that are already
   suppressed; nothing else changes (`TRAP.md`, rule added in `S1-ROWS.md` 2).
4. **Status.** Input (i): **paper** (compression, Lemma FR(b), with `[6]` Theorem 2's contraction unchanged). Input
   (ii): **paper** (Lemma FR(a) and Lemma LP, with `[5]` Theorems 3.12, 3.13 as quoted in `[15]`). The algebraic
   identity and the decay step of Lemma FR are **Lean** (`resolvent_two_sided`, `decay_through`). What stays cited is
   exactly what Balaban cites: the unmodified Theorems 3.12, 3.13 of `[5]`, and the bounds on `G'`, `H'`, `R` that
   `[6]` quotes. T3 and V1 are therefore **paper** with no input in modified form.

## 1. Where the inputs enter

| place | operator | Balaban's bound | how the hole changes it |
|---|---|---|---|
| `[15]` Sect. A, Prop 2 | gauge transformation `u` from axial to Landau gauge, `R_0 u_j = 1` | `[6]` Thm 2: unique `u`, bounds (1.36)-(1.39); proof: contraction (1.100)-(1.106) with `G'` (bounded `|·|_(-2) → |·|`, `|D·|_(-1)`), `R` (sup-norm bounded), `H'` (1.92) | the action with the hole's content frozen is invariant only under `u` with `u = 1` on the sites `S_H` of the hole's bonds: the unknown `ω = log u'` lives on sites outside `S_H`, equations at `S_H` are dropped: **compression** of the linear operator `Δ = D*D` on `N(Q')` to `{ω = 0 on S_H}` |
| `[15]` (46) | `H`: minimiser of the quadratic form under `L^j Q_j A = B`, `RD*A = 0` | `[5]` Thm 3.12: `|HB| ≤ B0 L^j |B|`, `|∇HB| ≤ B0 L^{j/2}|B|` | constraint `Q̃_1 = Q ∘ (𝟙 ⊕ dF)`, hole bonds frozen: compression to non-hole bonds plus a **local perturbation** of `Q*Q` near the hole |
| `[15]` (110)-(117) | `G_1 = (Δ_1 + DRD* + aQ*Q)^{-1}`, `𝔊 = G_1 - ...` | `[5]` Thm 3.13: norm `max{|·|_(-1), |∇·|_(-2)}` bounded by `|·|_(-3)` | compression to non-hole bonds; `Q → Q̃_1`; the background on the plaquettes with bonds in both `U` and `H` is `U_0 ∪ h` instead of a regular field: **local perturbation** |

In every row the change is supported in `S` = the sites and bonds within distance 2 of the hole together with the
bonds of the (at most `2^d`) blocks meeting it: `|S| ≤ C_d L^d`, `diam S ≤ C_d L` (current units), for a subscale hole (diameter `≤ L/4`; a hole between `L/4` and a block is carried one more step).

## 2. Lemma FR (finite-rank local modifications)

Let `K` be a bounded self-adjoint operator on a finite-dimensional real Hilbert space of fields on a finite set `X`
(the lattice of the region, with one Lie-algebra component per site or bond), `K ≥ m > 0`, `G = K^{-1}`. Norms: any
weighted sup norm `|f|_w = sup_x w(x)|f(x)|` with weights comparable on `S` (`w(x)/w(x') ≤ c_w` for `x, x' ∈ S`;
Balaban's `|·|_(n)` are of this type, with weights constant on each scale region, and `S` lies in one region).

**(a) Perturbation.** Let `V` be self-adjoint, supported on `S × S` (`V = P_S V P_S`), with `K + V ≥ m̃ > 0`, and
`G̃ = (K + V)^{-1}`. Then
`G̃ = G - G V G + G V G̃ V G` (**Lean** `resolvent_two_sided`),
and the last two terms factor through `S`. Consequently:
* *norms:* `‖G̃‖_{w→w'} ≤ ‖G‖_{w→w'} + ‖G‖_{w→w'} c_S ‖V‖ ‖G‖_{w→w'} (1 + ‖V‖ m̃^{-1} c_S)`, where `c_S` converts
  between `|·|_w` restricted to `S` and the Euclidean norm on `S` (`c_S ≤ |S| c_w` up to the weight at `S`);
* *decay:* if `|G(x, z)| ≤ C_0 e^{-δ d(x, z)}`, then `|G̃(x, y)| ≤ C_0 e^{-δ d(x,y)} [1 + |S|² C_0 ‖V‖ e^{δ D_S}
  (1 + C_0 ‖V‖ m̃^{-1})]`, `D_S = diam S` (**Lean** `decay_through` for each correction term: a kernel that factors
  through `S` keeps the decay, with the constant multiplied by `|S|² e^{δ D_S}`).

*Proof.* The identity: `resolvent_two_sided` (any ring). Norms and decay: the correction terms are compositions
`G P_S (·) P_S G` with a middle factor `V`, resp. `V G̃ V` restricted to `S × S`, whose Euclidean norm is at most
`‖V‖`, resp. `‖V‖² m̃^{-1}` (`‖G̃‖_{ℓ²} ≤ m̃^{-1}`); converting the middle factor's Euclidean bound to the weighted norms
costs `c_S`. ∎

**(b) Compression.** Let `E: ℝ^{S'} → H` be an injective map onto the components fixed at `S` (after dropping the
components that are linear combinations of others, e.g. a block entirely in `S` under the block-average constraint),
`P` the orthogonal projection onto `(ran E)^⊥`, `K_P = P K P` on `ran P`. Then (Schur complement)
`K_P^{-1} = P [G - G E (E* G E)^{-1} E* G] P`,
with `E* G E ≥ σ_min(E)² ‖K‖^{-1} > 0`, and `K_P ≥ m` (a compression keeps the lower bound). The correction term
factors through `S`, so the norm and decay bounds of (a) hold with `‖V‖ m̃^{-1}` replaced by
`‖K‖ σ_min(E)^{-2}`.

*Proof.* With `G = K^{-1}` in the block form `(ran P) ⊕ (ran E)`, the inverse of the `PP` block of `K` is the Schur
complement of the `EE` block of `G`: `(K_PP)^{-1} = G_PP - G_PE G_EE^{-1} G_EP`. `G_EE = E* G E ≥ ‖K‖^{-1} E*E`. ∎

**FR-multi (several holes).** Let `V = Σ_i V_i` with `V_i` supported on `S_i`, each `K + V_i ≥ m̃`, and
`d(S_i, S_j) ≥ R_sep`. Write `G̃ = G - Σ_i G V_i G̃`; the unknowns `X_i = V_i G̃` satisfy
`(𝟙 + V_i G) X_i = V_i G - Σ_{j ≠ i} V_i G X_j`, and `(𝟙 + V_i G)` is invertible on `S_i` (single-hole case (a)).
The off-diagonal coefficients are bounded by `C_FR e^{-δ d(S_i, S_j)}`. If `sup_i Σ_{j ≠ i} C_FR e^{-δ d(S_i, S_j)}
≤ 1/2` (true when `R_sep ≥ δ^{-1} log(C'_d C_FR)`, since at most `C_d n^{d-1}` holes lie at distance
`∈ [n R_sep, (n+1) R_sep)`), the system is solved by a convergent Neumann series and `G̃` has the bounds of (a) with
the constant doubled. ∎

## 3. Lemma LP (positivity of the modified operator)

**Statement.** On a small-field domain `Λ` (all plaquettes of `Λ` within `ε` of the identity, including those with bonds
in both `U` and the hole: they are plaquettes of `Λ`; a plaquette next to a hole that is not `ε`-small puts its
neighbourhood into the large-field region), the Hessian of `A_H` at `U_0`, on fields `A` that vanish on the hole's bonds,
satisfy the block-axial gauge (on a spanning forest of each block rooted at its centre and at `S_H`) and the linearised
constraint `Q̃_1 A = 0`, satisfies `⟨A, Hess A⟩ ≥ c_d L^{-(2d+2)} d^{-4} ‖A‖²` for `ε L² ≤ c_d`. The form
`Δ_1 + DRD* + a Q̃_1*Q̃_1` of `[15]` (110), compressed to the non-hole bonds, is bounded below by `c(d, L) > 0` in the
same regime.

*Proof.* (1) **Covariant Poincaré with the hole frozen.** Repeat `POINCARE.md` with the tree replaced by the forest
together with the hole's bonds (on which `A = 0`). For a bond `b` the closed loop (forest path, `b`, forest path)
bounds a staircase surface of `≤ d L²` plaquettes, which may cross the hole. The linearised covariant Stokes identity
`Σ_{b ∈ γ} Ad(T_b) A(b) = Σ_{p ∈ Σ} Ad(T_p) (DA)(p) + Σ_{b' interior} Ad(T_{b'}) (Ad(hol_{p(b')}) - 𝟙) A(b')`
holds for every background (the transports `T` may be far from the identity: `Ad` preserves norms). Its curvature
terms involve only interior bonds `b'` carrying `A`, i.e. non-hole bonds, and the plaquettes next to them, which are
plaquettes of `Λ`, so `|Ad(hol) - 𝟙| ≤ C ε`. Plaquettes inside the hole contribute `(DA)(p) = 0`. Hence
`|A(b)| ≤ Σ_{p ∈ S_b} |(DA)(p)| + C ε Σ_{b' ∈ S_b} |A(b')|`, and the counting of `POINCARE.md` (with
`sum_sq_le_of_paths`) gives `‖A‖² ≤ C d⁴ L^{2d+2} (Σ_p |DA(p)|² + C ε² L⁴ ‖A‖²)`; absorb the last term for
`ε L² ≤ c_d`. The Hessian of a sum of regular plaquette terms is `Σ_p |DA(p)|² + O(ε)‖A‖²`. (2) **The gauge part** of
`[15]`'s form: on fields `ω` with `ω = 0` on `S_H`, `Σ_{non-hole} |Dω|² = Σ_{all} |Dω|²` (a bond with both ends in
`S_H` or inside the hole has `Dω = 0`; a bond from `S_H` to outside has `Dω = ± Ad(·)ω(x)`, independent of the hole's
content), so the gauge part is a compression of Balaban's and keeps his lower bound. (3) **The constraint part:** for
a subscale hole (diameter `≤ L/4`) each coarse bond of `Λ` keeps at least half of its owned face bonds at distance `≥ 2` from the hole
(`E7J.md` 2(a)); on these `Q̃_1` agrees with `Q_1`, so `Q̃_1 Q̃_1* ≥ ½ L^{1-d} (1 - O(ε))` as for Balaban's `Q`.
(1)-(3) combine as in Balaban's decomposition of the form ([5] (3.119)-(3.120), as `[15]` uses it): `c(d, L) > 0`. ∎

## 4. The two inputs

**Input (i): gauge fixing with the hole's sites fixed.** `[6]` Theorem 2 with the gauge group `{u : u = 1 on S_H}`:
there is exactly one `u` with `R_0 u_j = 1` on `Λ_j` and `u = 1` on `S_H`, such that `U^{u^{-1}}` satisfies (1.36)-(1.39)
of `[6]` with the Landau condition dropped at `S_H`. *Proof.* `[6]`'s proof (Sect. D, (1.75)-(1.106), Proposition 5)
is a contraction in `ω = log u'` whose linear operators are `G'` (inverse of `Δ` on `N(Q')`), `R` and `H'`. Replace
`Δ` by its compression to `{ω = 0 on S_H}`: Lemma FR(b) gives the modified `G'_S`, with the bounds of `G'` times a
constant `C(d, L)`; `R_S = 𝟙 - G'_S Q'*(…)` and `H'_S` are built from it by the same formulas, and the identity
`Q' G'_S R_S = 0` used after (1.100) holds by construction. The nonlinear estimates (1.81)-(1.89), (1.97)-(1.99) are
pointwise and unchanged. The contraction (1.102)-(1.106) closes with the changed constants, for `α_0 + α_1` smaller by
a factor depending on `d, L`. Uniqueness as in `[6]` (the identity `u = 1` solves the problem for `U_2`). ∎ (paper;
`[6]` Sect. E, the linearizing transformation, uses `H'` in the same way and was not re-read line by line.)

**Input (ii): propagator bounds for the modified constraint operator.** The modified `H̃` satisfies `[15]` (46) and
the modified `𝔊̃` satisfies `[15]` (117), with `B_0` replaced by `C(d, L) B_0`. *Proof.* `G̃_1` = compression (hole
bonds frozen) of Balaban's `G_1` at the filled background `U_0 ∪ F(U_0)` (regular, `TRAP-CHECKS.md` T1, T4), plus the
local perturbation `V` = (form at `U_0 ∪ h` minus form at `U_0 ∪ F`, on the plaquettes at the hole's boundary) +
`a(Q̃_1*Q̃_1 - Q_1*Q_1)`: supported on `S`, `‖V‖ ≤ C(d, L)`. Lemma LP gives `m̃ ≥ c(d, L)`. Lemma FR(b) then (a)
(FR-multi for several holes) gives the norm bound (117) and the decay of the kernel. `H̃ = G̃ Q̃*(Q̃ G̃ Q̃*)^{-1}`:
`Q̃ G̃ Q̃*` is Balaban's `Q G Q*` plus a perturbation supported on the coarse bonds whose blocks meet `S` (finitely
many), positive by (3) of Lemma LP; Lemma FR(a) on the coarse lattice gives (46). ∎ (paper)

## 5. Effect

* `V1-EXCISION.md`: inputs (i), (ii) are now proved here; T3 and V1 are **paper** with only Balaban's own citations
  (`[5]` Theorems 3.12, 3.13, `[6]` Theorem 2's linear bounds), as in `[15]` itself.
* Corrections to `V1-EXCISION.md`: (46) is `[5]` Theorem 3.12; the regularity of the plaquettes next to the hole
  comes from `Λ` being a small-field domain, not from the definition of the hole.
* New rule for `TRAP.md`: holes closer than `R_sep(d, L)` are merged (section 0.3).
