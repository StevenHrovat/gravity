# Round 3, attempt 2: must the running coupling reach order one? A twist-free-energy monotonicity (2026-11-21)

Brief: define a box coupling through a quantity that reflection positivity (RP) controls, the 't Hooft twist free energy
F(L) = −log(Z_tw/Z) of SU(2) on an L-box being the natural one, and prove a monotonicity in L for all β (or a quantitative
no-fixed-point statement). Together with attempt D's bounded running this would put the crossover of `../ROUND-2.md` in reach. Unit
tests: photon (U(1)), Z₂, and the requirement that the argument use non-abelian content.

Claim levels: **proved (Lean)**, **proved (paper)** (complete argument here), **standard** (literature, cited, not reproved),
**read** (checked in the source this session), **recalled** (from memory, not re-read), **heuristic**, **conjecture**.

Files: this note; `PREREG.md` (written before the one computation); `frozen_twist.py`, `frozen_twist.json` (exact counts, one CPU
process, under 2 seconds, all pre-registered checks pass). Lean: `../../../formal/Attempts/R3/MonotoneCrossing.lean`,
`../../../formal/Attempts/R3/MonotoneTwistEater.lean`, built in `~/formal-att-r3-2` (`lake build Attempts.R3.MonotoneCrossing
Attempts.R3.MonotoneTwistEater`: "Build completed successfully", no warnings in these files). Final clean rebuild (old oleans of
these modules deleted first) with `build_check.sh` in this folder, which builds only in `~/formal-att-r3-2` and prints the axioms. No `sorry`, no `native_decide`, no new
axioms. `#print axioms` on all 15 theorems shows only propext, Classical.choice and Quot.sound, and some theorems need fewer.

---

## 0. Result in one paragraph

**The monotonicity is not proved.** It fails at one identifiable step, and that step is the crossover itself in another form. What
the attempt does establish:

1. **Exactly what the crossover needs from a coupling: no fixed point on one compact stretch.** Monotone running is not enough
   (`monotone_not_enough`: a frozen coupling is monotone). What is needed is that the continuum step-scaling function have no fixed
   point on the compact stretch [u*, U] between the target coupling and the perturbative hand-over. By compactness that gives a
   uniform decrement per doubling, so the coupling crosses in a bounded number of doublings, uniformly in the bare coupling and with
   small lattice artefacts allowed (`uniform_decrement`, `crossing_within`, `reach_of_noFixedPoint`, Lean). A finite grid of
   certified values plus a Lipschitz bound is enough to supply that decrement (`grid_certificate`, Lean). This is attempt D's open
   item (ii)(c) in quantitative form. It is strictly weaker than confinement, because it says nothing below u*.
2. **The non-abelian content of a twist argument, made exact.** The SU(2) twisted torus has a configuration of **zero action** (a
   "twist eater": two holonomies whose commutator is the centre element −1). For any abelian group no such configuration exists: the
   twist costs action in every cross-section. Both are in Lean (`su2_twist_eater`, `eater_twisted_flat`, `no_flat_twist_comm`).
   "Gluons carry the charge they transmit" becomes, at the level of the centre, **"the centre element is a commutator."**
3. **A third unit test, beyond U(1) and Z₂: the finite subgroups of SU(2).** They are non-abelian, and their centre element is a
   commutator, so twist eaters exist. Yet at β = ∞ their twist free energy is the same at **every** box size:
   F_∞ = log(|Hom|/|Hom_tw|), which is 2.04 (Q8), 4.11 (2T), 3.89 (2O) and 5.07 (2I) (proved on paper; exact counts computed). An
   argument that uses only RP, compactness and "the centre is a commutator" therefore proves too much. A valid proof must also use the
   continuum of fluctuations, which is where b₀ > 0 lives.
4. **Where the monotonicity breaks.** RP controls the twist free energy one direction at a time, in a fixed slice volume
   (transfer-matrix positivity, Perron–Frobenius, log-convexity), and those facts hold for every group. A change of the box size
   compares two different volumes, and no RP inequality runs between volumes. Every known inequality that does compare scales
   (Migdal–Kadanoff/Hoelder decimation, chessboard) is one-sided and group-blind. To control a ratio Z_tw/Z one needs bounds in both
   directions at matched effective parameters. That is exactly the unproved inequality (3.5) of Ito and Seiler in Tomboulis's 2007
   argument, and it is false for U(1).

A correction to round 1 comes out on the way. For a single-plane twist on a symmetric torus, the SU(2) twist free energy at weak
coupling is **entropic, about (3/2)·log β, not "classical twisted action/g²"** (heuristic), because the classical cost is zero
(Lean). The twist note's T5 conclusion survives; its premise does not.

## 1. History, and the step that is hard

- **'t Hooft (1978, 1979, recalled).** Twisted boundary conditions; the magnetic (vortex) free energy F_m and its Z_N Fourier
  transform, the electric flux free energy F_e. He classified the phases by their behaviour as L → ∞ (confinement: F_m → 0
  exponentially in the cross-section; Coulomb: both finite; Higgs: F_m grows).
- **Mack and Petkova (1979, 1980, 1982; read: abstracts and INSPIRE records).** Compared SU(2) with Z₂, used the vortex free energy as
  the phase criterion, and gave a sufficient condition for confinement from fast decay of the vortex free energy. They wrote SU(2) as
  a Z₂ model with monopoles and fluctuating couplings: the SO(3) × Z₂ split also used below.
- **Yaffe (1980, recalled).** The same mechanism for SU(N) and Z_N.
- **Borgs and Seiler (1983, recalled).** RP correlation inequalities between twists and Polyakov loops at nonzero temperature.
- **Tomboulis and Yaffe (1985; read in Kanazawa, arXiv:0808.3442).** For a loop C in the μν-plane linked once by the vortex,
  ⟨W(C)⟩ ≤ 2{½(1 − Z₋/Z)}^{A_C/(L_μ L_ν)}, using site RP in planes perpendicular to the flux. An area law follows if
  1 − Z₋/Z decays like e^{−ρ L_μ L_ν}. The inequality works **within one volume**: it turns an input about F_m(L) into an output.
  Kanazawa notes that the required decay was verified only at strong coupling (Muenster, cluster expansion).
- **Kovacs and Tomboulis (2000, hep-lat/0002004; read: abstract).** Measured the SU(2) vortex free energy at β = 2.3, 2.4, 2.5 with
  multihistogram methods: it decays with L, consistent with confinement.
- **Tomboulis (2007, arXiv:0707.2179).** Claims confinement for all β, using Migdal–Kadanoff decimations made into inequalities.
  The ratio Z₋/Z is carried to the coarse lattice through interpolation parameters α(t) for Z and α⁺(t) for Z⁺ = ½(Z + Z₋).
- **Ito and Seiler (arXiv:0711.4930; read: full text, sections 2–3 and 5).** The claim needs a t* with α(t*) = α⁺(t*). They reduce
  its existence to the inequality A(α) > A⁺(α) between derivatives of the decimated free energies (their (3.5)) and say it is not
  proven. In their words: "It is not clear where and how his claim is proven for large β". They also say such a t* "does not exist
  in the case of G = U(1)", and that the MK recursion cannot tell abelian from non-abelian groups. Round 1's twist note recorded the
  same.

**The hard step, in general form.** Write F_m(2L) − F_m(L) = −log[(Z_tw/Z)(2L) / (Z_tw/Z)(L)]. Any inequality between the two sides
compares two **different** measures: the 2L torus with the L torus, or the fine lattice with the decimated one. A *ratio* needs a
lower bound on Z_tw and an upper bound on Z at **matched** effective parameters. The available inter-scale inequalities (Hoelder/MK
bond moving, chessboard) give one direction only, and they hold for every compact group with a positive character expansion, so
for U(1) and Z₂ as well. Tomboulis's α = α⁺ is the matching condition. Ito and Seiler show it is the unproved part, and that it fails
for U(1). Section 6.2 restates this step without decimation bounds. It does not get easier there: it becomes the renormalisation
flow itself.

## 2. The coupling and what positivity gives

Wilson SU(2) on an L₁×L₂×L₃×L₄ periodic lattice. The twist with c = −1 in the 12-plane flips one 12-plaquette at (x₁, x₂) = (−1, −1)
for every (x₃, x₄). Z_tw denotes the twisted partition function.

- **Magnetic:** F_m = −log(Z_tw/Z).
- **Electric (one direction):** F_e = −log(Z_e(1)/Z_e(0)), Z_e(1), Z_e(0) = (Z ∓ Z_tw)/2.
- **Duality:** F_e = dual(F_m), dual(F) = −log tanh(F/2). This map is an order-reversing involution on (0, ∞) (`dual_dual`,
  `dual_strictAntiOn`, `dual_pos`, Lean). "F_m decreases with L", "F_e increases with L" and "the coupling grows" are one statement.
- **A coupling.** Any fixed decreasing bijection of F_m defines a box coupling. The heuristic of section 4.3 suggests the
  tree-normalised choice u_tw(L) := C·exp(2F_m(L)/3) ∝ β at weak coupling, so that attempt D's recursion applies to u_tw. Nothing below
  depends on the normalisation.

**B1 (transfer-matrix form; standard, 't Hooft 1979; proof sketch here).** Take x₁ as time. Flipping the 12-plaquettes at x₂ = −1
between two time slices equals applying, on one slice, the centre transformation Ω̂ that multiplies all 2-links at x₂ = −1 by −1. The
spatial plaquettes on that slice contain those links twice and do not change. So Z_tw = Tr(Ω̂ T^{L₁}), Z = Tr(T^{L₁}).
- T is the transfer matrix of the 234-slice. It is positive and self-adjoint by link or site RP (`Positivity`).
- Ω̂ commutes with T, and Ω̂² = 1. Its eigenspaces are the electric-flux sectors e₂ = 0, 1.
- Hence Z_tw/Z = (1 − ρ)/(1 + ρ), with ρ = Tr(P₁T^{L₁})/Tr(P₀T^{L₁}) = e^{−F_e} ∈ [0, 1].
- So F_m ≥ 0 (also from character positivity), and F_m < ∞.

**B2 (one direction to infinity; proved, paper).** Fix L₂, L₃, L₄. Then F_m → 0 as L₁ → ∞, for **every** compact group with a
positive plaquette weight.
- The kernel of T is strictly positive, so T has a simple top eigenvalue λ₀ (Jentzsch).
- Its eigenvector is positive, and Ω̂ (measure preserving, positivity preserving) fixes it, so it lies in the e₂ = 0 sector.
- Then ρ ≤ (λ₁/λ₀)^{L₁−1}·Tr(P₁T)/λ₀ → 0.
- Reading: a slice of fixed size is a quantum system with a gap, and an electric flux through it costs finite energy. This holds for
  Z₂ and U(1) too, so it is not a confinement statement.

**B3 (directions along the sheet; standard, RP).** For a twist in the 12-plane, reflections perpendicular to 3 and 4 preserve the
twisted measure. So log Z_tw and log Z are each convex in L₃ (Tr of powers of a positive operator, Theorem C of
`OneScale/Doubling.lean`). Their difference has no sign.

**B4 (crossing the sheet; proved, paper).** For reflections perpendicular to 1 or 2 the twisted measure is not RP: the flipped
crossing weight e^{−(β/2)Re tr U} has character coefficients of sign (−1)^{2j}. RP with the sheet on one side gives
Z_tw² ≤ Z·Z(sheet and mirror sheet) = Z². That is because two sheets are removed by a centre gauge transformation on the slab between
them. So it is no new information.

**What RP reaches, in one sentence.** Every RP statement about F_m lives in one torus and varies one length while the slice stays
fixed (B1–B4). It holds for every compact group. Doubling all four lengths changes the slice volume, and RP contains no map between
transfer matrices on different slices. This is the twist version of attempt (b)'s P1: RP transports inward and within one measure,
never across volumes.

## 3. The target, sharpened: no fixed point on a compact stretch (Lean, `MonotoneCrossing.lean`)

Notation as in attempt D: u_j is the inverse coupling of the box 2^j ℓ₀, σ is the (continuum) step-scaling function with
u_{j+1} = σ(u_j) + η_j and artefacts η_j, a = u* (where α_s = α*), and b = U is where perturbative bookkeeping hands over
(D's `count_two_loop` above U).

- `monotone_not_enough`: for every a ≤ b there is a non-increasing sequence from b that never goes below a. Monotonicity ("F does
  not increase", "the coupling does not decrease") cannot by itself put the crossover in reach. U(1) is the example (frozen), and so
  is any theory with an infrared fixed point.
- `uniform_decrement`: if σ is continuous on [a, b] and σ(u) < u there (**no fixed point, NFP**), then some δ > 0 has σ(u) ≤ u − δ
  on all of [a, b]. Compactness turns the qualitative statement into a quantitative one.
- `crossing_within`, `reach_of_noFixedPoint`: then, with η_j ≤ δ/2, every start u₀ ≤ b falls below a within ⌈(b − a)/(δ/2)⌉ + 1
  doublings. The bound is uniform in u₀, so it is uniform in the bare coupling. This is the input (ii)(c) "the limit theory's
  coupling reaches α* after finitely many doublings" of `../r2-stepscaling/NOTE.md` §5, in the form `gap_of_stepScaling` needs.
- `grid_certificate`: σ K-Lipschitz on [a, b], plus σ(g_i) ≤ g_i − 2δ at grid points g_i that are h-dense in [a, b], with
  (K + 1)h ≤ δ, gives σ(u) ≤ u − δ on [a, b]. So finitely many certified step-scaling values plus one Lipschitz bound would give NFP.

**Conclusion of section 3.** The crossover needs exactly:
- **(NFP)** the continuum step-scaling function of some RP-defined coupling has no fixed point on [u*, U];
- small artefacts;
- D's perturbative counting above U.

NFP is weaker than confinement. It says nothing below u*: the coupling may do anything once it is strong.

## 4. The non-abelian content: twist eaters (Lean, `MonotoneTwistEater.lean`)

### 4.1 Statements

- `prod_plaq2_comm`, `no_flat_twist_comm`: in an abelian group, the product of all plaquette variables of a periodic 2D
  cross-section is 1. So a twisted-flat cross-section forces c = 1.
- `eater_plaq`, `eater_twisted_flat`: in any group, take c = a b a⁻¹ b⁻¹. Put a on the p-links of the slice x_p = −1, b on the
  q-links of the slice x_q = −1, and 1 elsewhere. This is twisted-flat: every twisted plaquette variable is 1, in every dimension d
  and every size L.
- `su2_commutator`, `su2_twist_eater`: in SU(2), −1 = A B A⁻¹ B⁻¹ with A = diag(i, −i), B = ((0, 1), (−1, 0)), so the twisted SU(2)
  torus has a zero-action configuration. (SU(N) with c = e^{2πi/N}: clock and shift matrices, standard, not formalised.)
- `commutator_trivial_of_comm`: the one-line abelian contrast.

### 4.2 Classical twisted action at fixed ℓ⁴ (Wilson normalisation S = β Σ(1 − Re tr U_p/N))

| group | minimal twisted action | how |
|---|---|---|
| Z₂ | exactly 2β·ℓ² (one flipped plaquette per slice, ℓ² slices), growing with ℓ | Lean obstruction + explicit configuration |
| U(1), c = e^{iπ} | between 2β and (π²/2)β for every ℓ, i.e. bounded and frozen | per slice the ℓ² angles sum to π mod 2π. Lower bound: 1 − cos θ ≥ 2θ²/π² and Cauchy–Schwarz give ≥ 2/ℓ² per slice. Upper bound: spread angle π/ℓ², ℓ⁴(1 − cos(π/ℓ²)) ≤ π²/2 (proved, paper) |
| SU(2), SU(N) | **0** | Lean |

### 4.3 Consequence for the size of F at weak coupling (heuristic, Laplace's method at fixed ℓ, β → ∞)

The minimum sets are the flat configurations. In maximal-tree gauge there are |G|^{V−1}·|Hom| of them (periodic) and
|G|^{V−1}·|Hom_tw| (twisted). Here Hom = commuting 4-tuples, and Hom_tw = 4-tuples with [g₁, g₂] = c and all other pairs commuting.
For SU(2), dim Hom(Z⁴, SU(2)) = 6 (maximal torus T⁴ times SU(2)/U(1)) and dim Hom_tw = 3 (one SO(3)-orbit, g₃, g₄ = ±1). Each
missing flat direction costs β^{−1/2}, so

  Z_tw/Z ≈ C(ℓ)·β^{−3/2},   F_m^{SU(2)}(ℓ, β) ≈ (3/2) log β + c(ℓ),

up to possible logarithmic corrections from the singular (reducible) strata of Hom. Compare U(1): F_m ≈ β·s_ℓ with s_ℓ ∈ [2, π²/2];
Z₂: F_m ≈ 2βℓ².

- **Correction to round 1.** Twist note T5/T6 assumed that SU(2) at weak coupling has t ≈ "classical twisted action, large", in the
  same range as U(1). For the single-plane twist on a symmetric torus the classical part is zero, and t grows only like (3/2) log β.
  T5's conclusion (no structural recursion contracts on the U(1) range) is unchanged, because the U(1) range [t*_U(β_c), ∞) still
  covers these values.
- **Lattice units are artefact dominated.** With β(2L) ≈ β(L) − 0.2575 (one loop, D), the running moves F by about
  −(3/2)(0.2575)/β ≈ −0.15 per doubling at β = 2.5 (heuristic). At fixed ℓ and β → ∞ this goes to 0, while the finite-size part
  c(2ℓ) − c(ℓ) does not depend on β. So the literal brief statement "F(2ℓ) ≤ F(ℓ) for all β, all ℓ" holds at large β only if c(ℓ) is
  non-increasing, a sign condition on one-loop lattice artefacts with no reason to hold. The right statement lives along a line of
  constant physics, i.e. NFP of the continuum step-scaling function (section 3). (For U(1) the classical cost ℓ⁴(1 − cos(π/ℓ²))
  increases with ℓ, so U(1) violates even the non-strict lattice statement, as it must.)

### 4.4 Reading (DMP, the owner's root swap)

- In the gluing picture ('t Hooft) the twisted torus is the periodic one glued with the colour rotations Ad(A), Ad(B). These are
  rotations by π about two orthogonal axes: they commute in SO(3), but their lifts anticommute in SU(2).
- The twist is a change of the colour frame (the root's frame) around the torus. For SU(2) the frame can absorb it without cost,
  through non-commuting holonomies. For U(1) and Z₂ it cannot, and the cost is classical.
- This is the "self-charge" of the guiding principle at the level of the centre. It is a reading, not a proof step.

## 5. Unit tests

| statement | U(1), 4D weak coupling | Z₂, 4D weak coupling | finite subgroups (Q8, 2T, 2O, 2I), large β | verdict |
|---|---|---|---|---|
| B1–B4 (RP facts) | hold | hold | hold | identities and one-volume facts, no reach claimed |
| twist eater exists (Lean) | no (abelian) | no | **yes** | separates abelian from non-abelian, not more |
| "F(2ℓ) ≤ F(ℓ), all β, all ℓ" (the brief's form) | false (classical cost rises to π²β/2) | false (2βℓ² grows) | constant at β = ∞ (non-strict holds, strict fails) | any proof of it must fail for U(1) and Z₂ |
| NFP on a stretch [a, b] (section 3) | false for every stretch: σ = id | the coupling runs to weak coupling | false at the frozen value F_∞ if it lies in [a, b] | the target statement; the tests show what it needs |
| `reach_of_noFixedPoint` (Lean) | hypothesis false, conclusion not claimed | same | same | conditional, empty for the tests |

**Photon.** U(1) has no centre twist of the SU(2) kind, but c = e^{iπ} ∈ U(1) gives the analogous flux free energy. It is frozen,
F_m → about π²β_R/2 in the Coulomb phase (round 1, input (U1)), and classically it lies between 2β and π²β/2 at every ℓ (section 4.2).
So the coupling defined from it never runs towards order one. Nothing here gives U(1) a reach; NFP fails for it on every stretch.

**Z₂.** The interface free energy grows like 2βℓ². "F decreases with L" fails, and so does NFP. Every argument here that uses only
RP and compactness (B1–B4) is valid for Z₂ and claims no monotonicity. The abelian obstruction (Lean) is what distinguishes Z₂ from
SU(2).

**Finite subgroups (new test; proved, paper; numbers exact).** For a finite G with Wilson weight (Re tr g = 2 only at g = 1),
Z(β) → #flat/|G|^{#links} as β → ∞. In maximal-tree gauge, #flat = |G|^{V−1}·|Hom| and #twisted-flat = |G|^{V−1}·|Hom_tw|. Hence
lim_{β→∞} Z_tw/Z = |Hom_tw|/|Hom| **for every ℓ ≥ 1**. From `frozen_twist.json` (all pre-registered checks pass: group orders,
|Hom(Z², G)| = |G|·k(G), the hand count for Q8, |Hom_tw| = 0 for Z₂ and Z₄):

| G | order | classes | \|Hom(Z⁴, G)\| | \|Hom_tw\| | F_∞ |
|---|---|---|---|---|---|
| Z₂, Z₄ | 2, 4 | 2, 4 | 16, 256 | 0 | ∞ |
| Q8 | 8 | 5 | 736 | 96 | 2.04 |
| 2T | 24 | 7 | 5856 | 96 | 4.11 |
| 2O | 48 | 8 | 18816 | 384 | 3.89 |
| 2I | 120 | 9 | 76320 | 480 | 5.07 |

The pre-registered prediction (finite, between 1 and 6) holds. The values grow with the group towards SU(2), where the zero-
dimensional count becomes the (3/2) log β of section 4.3.
- These groups have twist eaters, and are non-abelian, yet their twist free energy at large β is frozen. They are deconfined at large
  β (standard: finite gauge groups have a frozen phase; 2I is the classic SU(2) stand-in only below its transition, recalled).
- So an argument built from RP, compactness and "c is a commutator" would prove NFP for 2I across F = 5.07, which is false.
- A valid proof must use the **continuum of fluctuations** around the flat sectors. That is the b₀ > 0 of asymptotic freedom, the
  non-abelian content in its quantitative form.
- In the weak-coupling region the needed decrease per doubling is only the one-loop amount (O(1/β), section 4.3). So the realistic
  split is the one of section 3: perturbation theory above U, NFP on the compact stretch.

## 6. Where the monotonicity breaks, and what would get past it

### 6.1 The step

NFP at one value u ∈ [u*, U] says: in the continuum theory whose box of side L has twist free energy F_m(L) = F(u), the box of side
2L has a strictly smaller one. Proving it needs a comparison between the twisted/periodic ratios of two volumes. Section 2 shows
that RP gives none. Section 1 shows that the scale-comparing inequalities are one-sided and group-blind (Ito–Seiler's (3.5)).
Section 5 shows that any comparison must see the fluctuation entropy around flat sectors (b₀). Without the decimation bounds, the
step is the renormalisation flow itself.

### 6.2 The twist is transported exactly by an equivariant blocking (proved, paper, sketch)

The twisted torus is the periodic torus glued by Ad(A), Ad(B) ('t Hooft, standard). Take a block-spin map built from parallel
transports, as in Balaban's averaged links. It is gauge covariant and commutes with global conjugation. Then it maps Ad(A), Ad(B)
-glued fine configurations to Ad(A), Ad(B)-glued block configurations, when the blocks tile the torus. So with the exact effective
action S_eff,

  F_m(L; fine lattice) = F_m(L/2; S_eff),

with **the same** S_eff for the twisted and the periodic ensemble. Tomboulis's matching condition α = α⁺ is therefore automatic for
the exact renormalisation group. It is an artefact of replacing the exact flow by MK upper bounds. The price is that one must control
the exact effective action, including its terms that wind around the torus, which carry the twist at the coarsest scales. "F
decreases under doubling" is then the statement that the exact flow moves S_eff towards colour disorder. That is the crossover, now
stated for one functional (with W_p of `../ROUND-2.md` supplying the weak end).

### 6.3 What would get past it

1. **Measure NFP first** (section 7). If the continuum twisted step-scaling function has a margin δ on [u*, U], `grid_certificate`
   says how a proof could use the numbers: finitely many certified values plus a Lipschitz bound. Certifying each value needs
   continuum control of a finite-volume quantity (W_p-type, finite volume, no large-L limit). That is a finite but hard problem, and
   it is the same kind of problem as attempt A's certified 2D example.
2. **An analytic inequality would have to contain three things:**
   - (i) the twist eaters (c ∈ [G, G]), against U(1) and Z₂;
   - (ii) the fluctuation entropy around flat sectors, against the finite subgroups;
   - (iii) a two-sided comparison between volumes.

   No such inequality is known. A natural candidate shape (**conjecture**, no evidence beyond the tests) bounds F_m(2L) by F_m(L)
   minus a strictly positive function of the adjoint (SO(3)) frame decorrelation across the box, measured within the 2L torus by an
   RP-controlled adjoint Polyakov-loop correlator. By `AdjointOnly` (round 1, attempt b) such a bound is empty for U(1) and Z₂ by
   construction. It would still need (ii).
3. **Conjecture B (bounded twist free energy).** F_m^{SU(2)}(ℓ; β) ≤ A + (3/2)·log(1 + β), uniformly in ℓ. It fails for U(1) (∝ β)
   and Z₂ (∝ βℓ²), and it holds for the finite subgroups, so it is a "no Higgs/Z₂-type growth" statement, not confinement. It is the
   weakest non-trivial infrared statement in this language. It is not enough for the crossover, but it would exclude the Z₂-like
   branch of the flow. Not proved.

## 7. Request to r3-blocked (GPU, to be run by the coordinating session; nothing was run here)

**Wanted: the twisted step-scaling of SU(2) across the crossover, as a test of NFP.**

- **Observable.** F_m(ℓ, β) = −log(Z_tw/Z) on symmetric ℓ⁴ periodic lattices, Wilson SU(2). One twist in the 12-plane: the ℓ²
  plaquettes at (x₁, x₂) = (ℓ−1, ℓ−1), for all (x₃, x₄), get coupling −β.
- **Estimator** (Kovacs–Tomboulis interpolation). Give the sheet plaquettes coupling β' and integrate:
  −log(Z_tw/Z) = ∫_{−β}^{β} dβ' ⟨½ Σ_{p∈sheet} tr U_p⟩_{β'}.
  - 20 Gauss–Legendre nodes in β';
  - at each node, ≥ 2000 measurements separated by ≥ 5 (heat bath + 4 overrelaxation) sweeps;
  - bootstrap errors over nodes and measurements.
  - Check the integrand's smoothness at β' ≈ 0; add nodes there if the bootstrap error of the integral exceeds 0.02.
- **Grid.** β ∈ {2.3, 2.4, 2.5, 2.6, 2.7} (the TTL scan values, a√σ known) × ℓ ∈ {4, 6, 8, 12, 16}. Report F_m with errors. The
  physical box sizes ℓa√σ then span about 0.6 to 6.
- **Pre-registered readings.**
  1. *Lattice monotonicity:* F_m(2ℓ) < F_m(ℓ) for each available pair (4,8), (6,12), (8,16) at each β, at 2σ.
  2. *NFP in the continuum:* interpolate F_m in ℓa√σ. Form the step-scaling pairs Σ(u) = F_m(2L) at F_m(L) = u, over u ∈ [F_m at
     L√σ ≈ 3, F_m at L√σ ≈ 0.6]. Extrapolate in (a/L)² over the three resolutions. Pass if Σ(u) < u − δ with δ > 0 at 2σ on the
     whole stretch. Report the smallest margin δ and the u where it occurs: this is the δ of `reach_of_noFixedPoint`.
  3. *Value at L₁:* F_m at L√σ = 3 and 3.9 (where attempt C places the switch-on). This is u* in the twist scheme, to compare with
     F_∞(2I) = 5.07, the frozen value of the strongest finite-subgroup test.
- **Controls** (same code, cheap):
  - U(1) at β = 1.1 (Coulomb phase), ℓ ∈ {4, 8}, twist e^{iπ}: expected flat or increasing (the photon gate for this observable);
  - SU(2) at β = 2.5, ℓ = 8 with the twist in the 34-plane instead: expected equal to the 12-plane value within errors (symmetry,
    a code check).
- **Optional, same ensembles.** The twisted-Polyakov-loop ratio (de Divitiis et al., recalled) on the twisted ensemble at β' = −β,
  to convert u* into a conventional coupling for comparison with attempt C's α_s* = 16/π².
- **Cost.** About 25 (β, ℓ) points × 20 nodes, dominated by ℓ = 16. Leg B's code already has the heat bath. Only the per-plaquette
  coupling on the sheet is new.

## 8. Verdicts

| statement | status |
|---|---|
| Monotone running is not enough for a crossing (`monotone_not_enough`) | **proved, Lean** |
| No fixed point on [a, b] ⇒ uniform decrement ⇒ crossing in ≤ ⌈2(b − a)/δ⌉ + 1 doublings, artefacts ≤ δ/2 included (`uniform_decrement`, `crossing_within`, `reach_of_noFixedPoint`) | **proved, Lean** |
| Finite grid + Lipschitz ⇒ uniform decrement (`grid_certificate`) | **proved, Lean** |
| 't Hooft duality F_e = −log tanh(F_m/2) is an order-reversing involution (`dual_dual`, `dual_strictAntiOn`, `dual_pos`) | **proved, Lean** |
| Abelian groups: no twisted-flat cross-section (`no_flat_twist_comm`); twist eater for any c = [a, b] in any d, L (`eater_twisted_flat`); SU(2) zero twisted action (`su2_twist_eater`) | **proved, Lean** |
| Transfer-matrix form Z_tw = Tr(Ω̂ T^{L₁}), F_m ≥ 0 (B1); F_m → 0 as one length → ∞, every group (B2); B3, B4 | standard / **proved, paper** |
| U(1) classical twisted action ∈ [2β, π²β/2] for all ℓ; Z₂ exactly 2βℓ² | **proved, paper** |
| Finite groups: lim_{β→∞} F_m = log(\|Hom\|/\|Hom_tw\|), the same for every ℓ; values for Q8, 2T, 2O, 2I | **proved, paper**; numbers exact (`frozen_twist.json`) |
| Equivariant blocking transports the twist exactly (Tomboulis's α = α⁺ automatic for the exact flow) | **proved, paper (sketch)** |
| F_m^{SU(2)} ≈ (3/2) log β + c(ℓ) at fixed ℓ; running ≈ −0.15 per doubling at β = 2.5 | **heuristic** |
| The lattice-unit statement "F(2ℓ) ≤ F(ℓ) for all β, ℓ" is decided by the sign of finite-size artefacts | **heuristic** |
| NFP for the continuum twisted step-scaling function on [u*, U] | **open** (the crossover in this language) |
| Conjecture B (F_m ≤ A + (3/2) log(1 + β) uniformly in ℓ); the frame-decorrelation inequality | **conjecture** |
| Photon, Z₂, finite-subgroup tests | **pass** (section 5) |

## 9. The single most promising next step

Run the measurement of section 7. It is the first direct test of NFP in an RP-controlled scheme. It turns the crossover into a
number: the margin δ, and the u where the margin is smallest. With `reach_of_noFixedPoint` and `grid_certificate`, that number tells
exactly what a proof must certify, and where. If the margin is comfortably positive, the next proof target is a certified
finite-volume continuum bound at a handful of u values (attempt A's method, in 4D and in one finite box). If the margin is small
anywhere, the crossover has a near fixed point, and that is where any analytic argument must work hardest.
