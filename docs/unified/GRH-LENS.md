# The two open encoder steps through the lens of GRH

Status: 2026-11-23. Answers the owner's direction recorded in `docs/mass-gap/weak-coupling/PREP.md`: the entry "Direction
for the next round", the entry "Leads 1 to 3 point to one route" with its correction (the half-turn), and the entry on the
quantitative bound through the irreducibility of GRH at G0.

The two steps, from `ENCODER.md` section 6:
- **Yang-Mills:** raise the twist ratio `Z_tw/Z` at the hand-over box from the proved self-dual 0.414 to the needed
  `(mu_4 - 1)/(mu_4 + 1) = 0.743`, for every outside.
- **NP vs coNP:** find a step that reads two boundaries at once.

Files:
- Lean: `ProofPhase/Unified/GRHLens.lean`. `grhlens-axioms.sh` and `grhlens-axioms.log` list 32 declarations: 30 on the
  standard axioms, 2 on none, no sorry.
- Third-layer check: `grh_lens_check.py` and `grh_lens_check.log`. CPU only, reads saved data only. The coordinator's
  `rotation_check.py` and `rotation_check.log` check the half-turn on the sphere.

Status marks as in `ENCODER.md`: **Lean**, **classical**, **numerical**, **external**, **reading**, **open**, **fails**.

## 1. In plain words

**How GRH gets its bound.** Every scale's reflection coefficient comes from one positive object: one measure, one form.
Positivity of that object puts every coefficient in the unit disk at once. That is all it does: every sequence inside the
disk belongs to some positive measure (Verblunsky's theorem). Positivity says "inside the disk", never "where in the disk".

**The one structure, with the owner's half-turn as its spine** (section 6, Lean):
- The encoder number `c` lives on the Riemann sphere. Positivity means `c` lies in one hemisphere, the unit disk.
- The electric-magnetic duality is one rotation of the sphere by 180 degrees. It carries the disk (the Szego picture) onto
  the right half-plane (the electric picture).
- Its axis passes through the hand-over point `sqrt 2 - 1`, the midpoint between the lossless point `c = 0` and the
  closure `c = 1`.
- Both loss profiles are functions of one quantity: the hyperbolic (Poincare) distance of `c` from the lossless point. The
  electric cost is that distance itself; the Szego factor is `4f/(1 + f)^2` of the electric factor `f`.
- Steps along a chain add these distances. The half-turn swaps the two ways of composing: product of `c` (side by side)
  and hyperbolic addition (in series).

**The three leads.**
- **Lead 1 (global, not stepwise)** holds as a description of GRH and fails for the Yang-Mills step. Positivity of any
  global object gives only "inside the disk", which for the twist ratio is already proved.
- **Lead 2 (one structure)** holds, in the stronger form above.
- **Lead 3 (two boundaries by construction)** fails. Positive pairings of proof lines break exactly at the rounding step.
  The two-boundary split that does price lines (interpolation) has the same kind of half-turn, swapping the two sides; it
  leaves the cost unchanged.

**What would lift `c` from 0.414 to 0.743.** Not the half-turn and not positivity: both are symmetries or signs, and
neither picks a side or a distance. What moves `c` along the hyperbolic line is composition in series. Costs add, so
- three hand-over boxes in series, with no loss, would clear the one-box floor (cost 2.644 > 1.913) [Lean for the
  numbers];
- two would not: they reach exactly `c = 1/sqrt 2 = 0.707` [Lean].
- The lift therefore needs three things, all open:
  1. the box sits on the electric side of the axis;
  2. the loss per composition is below 0.244 (`flux_superadd_iter` has this loss as `2C`);
  3. both hold uniformly over outsides.

**What turns irreducibility into uniform slack** (the owner's chosen route).
- Nothing in the GRH structure does. GRH's irreducible positivity is a sign with zero slack: margin about `1e-9` per
  step, and exactly 0 at a finite closure.
- The mathematics that turns irreducibility into a quantity needs a uniform bound on ratios of weights, uniform over
  outsides:
  - Perron-Frobenius gives a gap per finite system, with no control of its size;
  - Doeblin's minorization and Birkhoff's projective contraction give slack from such a ratio bound.
- For the box of fixed physical size that ratio bound is O1 again.

**Three later leads (section 9).**
- **O1 in twist form:** twist free energy at most 0.297 at the hand-over box, for every outside [Lean].
- **Integrality fails, and points the wrong way for O1.** A count floors the action per tick, not the free energy per
  physical box, and asymptotic freedom lets entropy win as the tick shrinks. On the twist side the integer (Bogomolny)
  floor makes twists rare, while O1 needs them nearly free. GRH shows the same pattern: positivity gives a zero-free
  region whose slack shrinks like `1/log t`, and integer zero counts certify only finite ranges.
- **The two-box encoder** exists [Lean]: the departure from independence of two neighbouring boxes is a determinant. O1
  and the NP rounding step share the two-boundary shape but differ in kind: O1 is a lower bound on a sum, NP a lower
  bound on a minimum.

**What moved.** Neither open step moved. New in Lean:
- the half-turn structure;
- the hyperbolic ledger, with the exact count of lossless hand-over steps (two short, three clear);
- O1 as a sector domination and in twist form;
- the mass gap as a sign at every section;
- the two-box defect.

## 2. How GRH gets its encoder bound

**The structure** [classical]:
- A positive measure `mu` on the circle has a Hermitian Toeplitz form `t(j - i)`.
- Its Szego recursion has reflection (Verblunsky) coefficients `alpha_n`, the encoders of `ENCODER.md` 3.2.
- **Verblunsky:** nontrivial probability measures on the circle correspond one-to-one to sequences in the open unit disk.
- **Geronimus:** the `alpha_n` are the Schur parameters of the Schur function `f` of `mu`. The Caratheodory function
  `F(z) = integral (e^{i theta} + z)/(e^{i theta} - z) dmu` and `f` are joined by `F = (1 + z f)/(1 - z f)`, and
  `Re F >= 0` exactly when `|f| <= 1`. Each Schur step `f -> (f - alpha)/(z (1 - conj(alpha) f))` is a disk automorphism,
  an element of SU(1,1).
- **Szego (Kolmogorov-Krein):** the product of all step factors is a global quantity,
  `prod (1 - |alpha_n|^2) = exp(integral log w dtheta/2pi)`, with `w` the density of `mu`. The ledger's total cost is
  the entropy of one measure.

**The mechanism has two halves:**
1. One positive object gives every scale's bound at once. No step estimates are used.
2. The bound is "inside the disk" and nothing more: the parameters are free coordinates (Verblunsky).

GRH's open step is half 1 for the explicit form (positivity from the primes, the characters and the real place alone;
`ScaleSign`, `scaleSign_iff`, Lean). Half 2 is why GRH needs nothing quantitative: the sign is the whole statement.

## 3. Lead 1: global, not stepwise

**What holds.** Yang-Mills has global positive objects of exactly GRH's kind.

(a) **The electric sector measure of one box.** The centre `Z_2` has two sectors, electric flux `e = 0, 1`, with weights
`Z_{e=0} = (Z + Z_tw)/2` and `Z_{e=1} = (Z - Z_tw)/2`.
- Their positivity is "the encoder is in the disk": `z2_sectors` (Lean). For weights `p0 > 0`, `p1 >= 0`, the coefficient
  `c = (p0 - p1)/(p0 + p1)` is in `[-1, 1]`, the electric factor is `p1/p0` and the Szego factor is
  `4 p0 p1/(p0 + p1)^2`.
- `z2_realize` (Lean): every `c` in `[-1, 1]` arises this way.
- For SU(N) the group is `Z_N` and the weights are 't Hooft's Fourier transform `Z_e = (1/N) sum_k omega^{-ek} Z_k`
  [classical].

(b) **The transfer matrix's spectral measure along time.**
- Reflection positivity makes the correlation at distance `k` a positive spectral sum `t(k) = sum_a w_a x_a^k` with
  `x_a = e^{-E_a}` in `[0, 1]` (`Bridge/Spectral.lean`, `M1/UVTVOS.lean`, Lean). This is a Hankel (interval) structure.
- Under the Szego map `x = cos theta` it becomes a circle problem with real Verblunsky coefficients (Geronimus relations)
  [classical].
- What positivity gives here (Lean, `GRHLens.lean` section 3):
  - `mom_logconvex`: `t(k+1)^2 <= t(k) t(k+2)`.
  - `stepRatio_mono`, `effMass_anti`: the step factor rises with `k`, and the effective mass falls with distance.
  - `step_le_of_support`: a spectral gap (`x <= rho`) bounds every step factor by `rho`.
  - `localizing_nonneg`: a gap makes every finite section of `rho t(i+j) - t(i+j+1)` positive. The converse is the
    Hausdorff moment theorem [classical; not formalized].
- So **the mass gap at rate `-log rho` is a sign at every scale**, the same shape as `ScaleSign`.

(c) **The box-size sequence.** No positive object is known whose Schur parameters are the twist ratios `c(L)`. If there
were one, it would constrain nothing. `grh_lens_check.py` part 2 [numerical]: the beta = 2.3 twist ratios at `L = 6, 8`,
eight random values and six copies of 0.743 each build a positive Toeplitz form. The smallest eigenvalues are `+2.9e-5`,
`+1.5e-3` and `+4.5e-5`, and the round trip is exact to `5e-14`. The proposed consistency check is vacuous.

**What fails, and why.**
- GRH's mechanism yields "inside the disk". For the twist ratio that is `0 <= Z_tw <= Z`, already in hand:
  `su2_Ztw_lt_Z` (Lean) and `0 < Z_tw` (stated).
- O1 asks for `Z_tw/Z >= 0.743`, a location inside the disk. Freeness says no positivity statement about these objects
  can force it.
- The localizing form turns the **gap** into a sign, but the gap is the conclusion, not O1.

**Verdict: lead 1 fails for the Yang-Mills step.** It transfers as a mechanism and delivers only qualitative bounds.

**The side result that survives** [Lean]. Along a reflection-positive chain the effective per-step cost falls with
distance. A certificate read from short-distance correlation ratios always overestimates the true rate.
- Data [numerical, part 3, `ttl_summary.json`]: across 5 SU(2) runs, 29 glueball and 34 torelon consecutive
  effective-mass pairs.
- No rise larger than 2 sigma; the largest is 1.88 sigma.

**The saved twist data** [numerical, part 1; a proxy, `c6b-flipdata/RESULT.md`]:
- The SU(2) flip-probability proxy gives `c` between 0.946 and 1.000 on `x = L sqrt(sigma)` from 2.10 to 4.20; the lowest
  2-sigma value is 0.943.
- Care points:
  - it is built from torelon energies with `p <= 1/2` by construction;
  - it covers one outside only, the periodic box;
  - it has no point below `x = 2.1`, while the hand-over lies near `x = 1.7` to 1.8.
- The 4D `Z_2` gauge theory at `L = 4` gives `c = 0.995` and 0.977 at beta 0.05 and 0.30 (confined), and `2.8e-8` at
  beta 0.60 (deconfined).
- PREP records `c = 0.863` at beta 2.3, `L = 6` on small tori (`ONEBOX-CHECK.md` 9; numerical, not certified).

## 4. Lead 2: the two loss profiles are one structure

**What holds** (Lean, `GRHLens.lean` section 1):
- `re_cayley`: for every complex `c`, `Re((1 - c)/(1 + c)) = (1 - |c|^2)/|1 + c|^2`.
- `schur_iff_caratheodory`: for `c != -1`, `|c| <= 1` exactly when `Re((1 - c)/(1 + c)) >= 0`.
- `cayley_ofReal`, `elec_eq_szego`: on the real line the Cayley transform is the electric profile, and
  `elec c = szego c/(1 + c)^2`.

**The general encoder** [classical structure; identities Lean]:

> An encoder is a positive-definite function `phi` on the group `A` of the one rotation, with `phi(identity) = 1`.
> Equivalently (Bochner, Herglotz) it is a probability measure on the dual group, the **sectors**. Its reflection
> coefficients are its Schur face (in the closed disk exactly when the measure is positive). The electric factor is the
> real part of its Caratheodory face. The Szego factor is the defect `1 - |c|^2`.

| use case | rotation group | sectors | reflection coefficient | depth of the Schur algorithm |
|---|---|---|---|---|
| Yang-Mills, SU(2) | centre `Z_2` | electric flux `e = 0, 1` | `Z_tw/Z` | 1 |
| Yang-Mills, SU(N) | centre `Z_N` | electric flux `Z_N` | `Z_k/Z`, `k = 1 .. N-1` | `N - 1` |
| GRH | scale shift `Z` | the circle (zeros as atoms) | Verblunsky `alpha_m` | infinite (`N` at a finite closure) |
| NP vs coNP | parity flip `Z_2` | boundary parity | 0 for a fixed-parity law (`encoder_check.py`) | 1 |

Section 6 gives this structure its geometric form, the half-turn.

**Verdict: lead 2 holds.**

## 5. Lead 3: two boundaries by construction

**What GRH's pairing is.**
- Weil's form is one fixed positive quadratic form on test functions, `f -> W(f * f~)`, with the mirror `f~` built in.
- Positivity is a property of the true object, and it is preserved by every operation on test functions.

**The proof analogue, and where it breaks** (Lean, `Proof/CPPairs.lean`, `Proof/CPDuality.lean`):
- A positive pairing on pairs of lines is a pseudo-expectation (a positive moment matrix). The all-1/2 point is its
  degree-1 case (`half_clause`).
- Additions and positive scalings keep it (`holds_add`, `holds_scale`); rounding breaks it (`half_breaks_rounding`).
- Hence `creative_pair` and `refutation_needs_pair`: if the axioms have a fractional solution, every refutation contains
  a rounding of a combination of at least two lines.
- Positivity cannot price that step:
  - Tseitin formulas on expanders keep a positive pseudo-expectation up to linear degree (Grigoriev 2001);
  - yet they have quasi-polynomial cutting-planes refutations (Dadush-Tiwari 2020) [classical; recorded in
    `docs/pnp/CP-DUALITY.md` section 6].
- Single-line pairing floors also fail for weighted lines (`two_cheap`, Lean; `CP-DUALITY.md` section 3).

**The two-boundary step that does price lines** is feasible interpolation:
- The split `A(x, y) and B(x, z)` is unsatisfiable exactly when the two boundary laws are disjoint (`split_unsat_iff`,
  `interpolant_separates`, Lean).
- Pudlak 1997 turns cutting-planes proofs into monotone real circuits on that interface [classical]. It is a circuit-size
  statement, not a positive form.
- Its open case at constant width is the interface hardness of `CP-DUALITY.md` section 4 [open].
- For Frege, interpolation fails under cryptographic assumptions (Krajicek-Pudlak 1998; Bonet-Pitassi-Raz 2000)
  [classical].

**Does the two-boundary pairing have a rotation of the same kind?** Yes, and it behaves like Yang-Mills' half-turn.
- Swapping the two sides `A <-> B` is an involution. It carries every separator `I` of `(A, B)` to the separator `not I`
  of `(B, A)` (`separates_swap`, Lean).
- For monotone interpolation the swap, composed with negating the shared variables, carries a monotone function to its
  monotone dual. Monotone circuit size is the same for a function and its dual (swap AND and OR) [classical].
- So the rotation exchanges the two pictures (clique side and colouring side, in Pudlak's example) and leaves the cost
  unchanged. Like the half-turn in Yang-Mills, it cannot create the cost.

**Verdict: lead 3 fails.** No positive bilinear form on pairs of lines can force a rounding cost the way Weil's pairing
forces the sign. The two-boundary step itself is real (`refutation_needs_pair`, Lean); its price is open.

## 6. The generalization at the core: one encoder on the sphere, the half-turn as its duality

**6.1 The half-turn** (Lean, `GRHLens.lean` section 4; coordinator's `rotation_check.log`, numerical).
- The electric profile `elec(c) = (1 - c)/(1 + c)` is the Moebius map of `(1/sqrt 2) [[-1, 1], [1, 1]]` (`halfTurn_mobius`).
- That matrix is symmetric and squares to the identity (`halfTurn_transpose`, `halfTurn_mul_self`). So it is orthogonal,
  a rotation of the Riemann sphere by 180 degrees, in SU(2) up to a phase.
- Its fixed points `sqrt 2 - 1` (`elec_selfdual`) and `-(1 + sqrt 2)` (`elec_fixed_neg`) are antipodal
  (`fixed_antipodal`).
- On the pair `(Z, Z_tw)` it is the `Z_2` Fourier (Hadamard) transform read as a ratio.

**6.2 One encoder structure on the sphere.** The Szego profile and the electric profile are one structure.
- **Where `c` lives.** On the sphere. Positivity is "`c` in the Schur hemisphere", the unit disk.
- **The cost.** The hyperbolic (Poincare) distance of `c` from the lossless point 0: `-log elec(c) = log((1 + c)/(1 - c))`
  (`elec_cost`, Lean).
  - The electric factor is `e^{-d}`.
  - The Szego factor is `4 e^{-d}/(1 + e^{-d})^2 = 1/cosh^2(d/2)` (`szego_of_elec`, Lean).
  - So the Szego profile (the disk's Poincare factor `1 - |c|^2`) and the electric profile are two functions of the one
    distance `d`. They read the same geometry in the disk model and in the half-plane model.
- **The steps.** Disk automorphisms, SU(1,1): the Schur steps of GRH, and the hyperbolic addition
  `a (+) b = (a + b)/(1 + a b)` along the real diameter. Under it the electric factors multiply and the costs add
  (`elec_oplus`, Lean).
- **The duality.** The half-turn, SU(2). It carries the disk model onto the half-plane model and swaps the two
  compositions: the product of reflection coefficients is carried to hyperbolic addition of electric factors
  (`elec_mul`, Lean). Physically:
  - parallel: twists side by side, `Z_2` characters multiply;
  - series: flux through boxes in a row, electric factors multiply.

  The series/parallel reading is [classical, heuristic for non-independent boxes].
- **The hand-over.** The axis point `sqrt 2 - 1` sits at 45 degrees on the sphere, the midpoint of the 90-degree arc from
  the lossless point (`c = 0`) to the closure (`c = 1`), which the half-turn swaps. At it the two costs are equal,
  `log(1 + sqrt 2) = 0.881` (`selfdual_cost`, Lean).

> **The general encoder (stated with the half-turn).** An encoder is a point `c` of the Riemann sphere, given by a
> positive-definite function on the rotation group (section 4). Positivity places it in the Schur hemisphere. Its cost is
> the hyperbolic distance from the lossless point. Steps along a chain are hyperbolic isometries (SU(1,1)), and costs add
> along a geodesic. The electric-magnetic duality is one half-turn of the sphere (SU(2)), whose axis is the self-dual
> point. Both loss profiles are functions of the one distance.

**6.3 What the half-turn does not do.** It is a symmetry of the description. It exchanges the pictures and fixes its
axis, so it never decides which side of the axis a box is on, or how far from it. In 't Hooft's terms:
- the confining side is `c -> 1` (magnetic free);
- the Higgs side is `c -> 0` (electric free).

Choosing the side is the dynamics, not the duality. The proved hand-over says only that every box is at least 0.881 from
the lossless point on one side or the other (`max(F_e, F_tw) >= 0.881`, `HandOver.lean`). O1 needs the electric side, at
distance at least 1.913.

**6.4 What would lift `c`** (Lean for the arithmetic, `GRHLens.lean` section 5; `grh_lens_check.py` part 4).
Composition in series moves `c` along the hyperbolic line, adding costs:

| boxes in series (no loss) | `c` | sphere angle | cost |
|---|---|---|---|
| 1 hand-over box | 0.4142 | 45.0 deg | 0.881 |
| 2 | 0.7071 = `1/sqrt 2` | 70.5 deg | 1.763 (short: `two_steps_short`, `mu >= 6`) |
| O1 floor (`mu_4`) | 0.7427 | 73.2 deg | 1.913 |
| 3 | 0.8673 | 81.9 deg | 2.644 (clears: `three_steps_clear`, `mu <= 14`) |

With a loss `l` per composition (`flux_superadd_iter`: `F(kL) >= k (F(L) - 2C)`, Lean), three boxes suffice while
`l < 0.244`, four while `l < 0.403`. So the lift has three parts, all **open**:
1. the box at `L` is on the electric side with `F_e(L)` near the hand-over value (the hand-over gives only one of
   `F_e`, `F_tw`);
2. the loss `2C` per composition is below `F_e(L) - 1.913/k` for some `k` (the relation of the two floors, III.5.8);
3. both hold uniformly over outsides.

Hand-over points are closed upward, so box size `kL` is allowed. Nothing in the half-turn or in positivity supplies
parts 1 to 3.

**6.5 What turns irreducibility into uniform slack** (the owner's route for the quantitative bound).
- **GRH's irreducibility gives no slack.** The positive form cannot be assembled from parts (`GRH/Transfer.lean`, Lean),
  but its positivity is semidefinite: the margin is about `1e-9` per step (`INDUCTION.md`), and exactly 0 at a finite
  closure (`ENCODER.md` 3.2). In the structure above, all its operations are isometries or signs: SU(1,1) steps preserve
  distance, the SU(2) half-turn exchanges models, positivity picks a hemisphere. **Nothing in the GRH structure turns
  irreducibility into slack.**
- **What does, in known mathematics** [classical]:
  - **Perron-Frobenius, Jentzsch, Krein-Rutman:** an irreducible (positivity-improving) operator has a simple top
    eigenvalue strictly above the rest. This is slack per finite system, with no control of its size. It is why every
    finite torus has a rate (Lean, Doeblin rate per torus).
  - **Doeblin:** a minorization `K(x, .) >= eps nu(.)` for every starting point gives slack `eps`.
  - **Birkhoff-Hopf:** a positive map whose image cone has finite Hilbert projective diameter `Delta` contracts the
    projective metric by `tanh(Delta/4) < 1`. On the two-sector cone the Hilbert metric is
    `|log(p1/p0) - log(q1/q0)|`, the same hyperbolic distance as the electric cost (`elec_cost`). So Birkhoff's theorem
    is the quantitative bridge in exactly this geometry.
- **In each case the slack is a function of a uniform bound on ratios of weights over all starting points (outsides).**
  For a box of fixed physical size that bound is O1 again, in the form of condition A or the one-box statement. For
  `k >= 2` channels the per-channel Doeblin bound already fails to give a column sum below 1 once `C >= log 2`
  (`CHAIN.md` 4, Lean).
- So the sharp answer: irreducibility becomes uniform slack only through a uniform ratio bound, and that bound is the open
  step itself. GRH does not contain one, since it has no outside to be uniform over.

**6.6 HTF.md stays binding.**
- The composite HTF carries no gauge-invariant information by itself and has no hopping term. The pure theory is the
  `kappa = 0` edge of the complementarity diagram (Osterwalder-Seiler 1978, Fradkin-Shenker 1979), where the Higgs-side
  expansion has no small parameter (`c9a-crossover/HTF.md`).
- In gauge-Higgs theory, `kappa` is what supplies the uniform ratio bound of 6.5. Without it the HTF cannot supply parts
  1 to 3 of 6.4.
- That the HTF "makes" the half-turn is a [reading]. The half-turn itself is an exact fact about the encoder number
  (Lean).

**6.7 The kinds of open step.**

| problem | open step | is it this structure's positivity? |
|---|---|---|
| GRH | every reflection coefficient in the disk (the sign) | **yes**: the open step is positivity |
| Yang-Mills | `Z_tw/Z >= c0 > 0.743`, equivalently `mu Z_{e=1} <= Z_{e=0}` (`oneBox_sector`, `ymOneBox_iff_refl`, Lean): the electric side, at hyperbolic distance at least 1.913 | **no**: a side and a distance, beyond the sign |
| NP vs coNP | a price on the rounding of two lines | **no**: positivity proves the step must occur, and rounding breaks it |

**Reading** [reading]. The owner's correction ("one, seen through the rotation the HTF makes") has an exact form: one
encoder on the sphere, one half-turn between its two pictures. The owner's earlier entry "positivity can not keep it away
from zero" matches 6.3 and 6.5: positivity fixes the hemisphere, the half-turn fixes the axis, and neither fixes the
distance. GRH asks only for the hemisphere; O1 and the crossing cost ask for a distance.

## 7. What moved on the two open steps

- **Yang-Mills: not moved.** Nothing lifts 0.414 to 0.743. New exact content:
  - the half-turn structure (6.1, 6.2);
  - the hyperbolic ledger with the count of hand-over boxes in series (two short, three clear, 6.4);
  - the three open parts of a lift (side, loss below 0.244 for three boxes, uniformity);
  - O1 as the sector domination `mu Z_{e=1} <= Z_{e=0}`;
  - the mass gap as a sign at every section of the localizing form;
  - the falling effective mass.

  On irreducibility (6.5): GRH gives no slack; the known bridges (Doeblin, Birkhoff) need a uniform ratio bound, which is
  O1.
- **NP vs coNP: not moved.** The positivity route is closed by known results (section 5). The side swap is a symmetry of
  the cost. The step stays at interpolation's interface hardness (`CP-DUALITY.md` section 4), open.

## 8. Status

| item | status |
|---|---|
| Cayley identity, Schur iff Caratheodory, electric = defect / `(1+c)^2` | Lean |
| `Z_2` sector form, freeness, O1 as sector domination | Lean |
| log-convexity, rising step factor, falling effective mass, gap => localizing sign | Lean |
| half-turn: symmetric, involution, Moebius action = `elec`, two antipodal fixed points | Lean |
| hyperbolic ledger: cost = Poincare distance, Szego = function of electric, series/parallel swap, two steps short, three clear | Lean |
| NP side swap negates the separator | Lean |
| O1 in twist form (`F_tw <= 0.297`), independent boxes multiply, two-box defect = determinant | Lean |
| integrality as a uniform free-energy floor | fails (section 9.2) |
| Turing's method, zero-density, de la Vallee Poussin's region, Tomboulis-Yaffe | classical |
| gap <= localizing sign (Hausdorff), Verblunsky, Geronimus, Szego, Perron-Frobenius, Doeblin, Birkhoff-Hopf, 't Hooft's `Z_N` Fourier transform, monotone duality | classical |
| twist ratios on saved data, Verblunsky freeness on data, effective-mass monotonicity on data, sphere angles | numerical |
| SOS does not price CP (Grigoriev; Dadush-Tiwari), interpolation (Pudlak), Frege barrier | classical |
| the HTF performs the half-turn | reading |
| lead 1 for the Yang-Mills step | fails |
| lead 2 | holds (as the half-turn structure) |
| lead 3 | fails |
| O1, the sign, the crossing cost | open |

## 9. Three later leads: integrality, the twist side, two boxes

### 9.1 O1 in its twist form

- By the half-turn, `e^{-F_e} = tanh(F_tw/2)`, which is `elec(c)` with `c = e^{-F_tw}` [classical; Lean as `elec`].
- So O1 is equivalent to `F_tw(L) <= log((mu_4 + 1)/(mu_4 - 1)) = 0.297` at the hand-over box, for every outside
  (`oneBox_twist_form`, Lean).
- At the self-dual point `F_tw = F_e = 0.881`.
- O1 asks that the twist be nearly free: an **upper** bound on a free energy, equivalently the lower bound
  `Z_tw >= 0.743 Z`.

### 9.2 Integrality

**The question:** is there an integer-valued invariant of the box whose every nonzero value costs, in free energy and
uniformly over outsides, more than `log mu_4`? **No**, for a structural reason. On the twist side the sign is reversed.

**What integrality gives.** "Nonzero implies at least 1" for the count. That floors the **action** of the configurations
carrying the invariant:
- Bogomolny: `S >= 8 pi^2 |Q|/g^2`, and `4 pi^2/g^2` with a twist of nonzero twist product (`CONTAINMENT.md` 6.2);
- the forced sheet: at least `2/c` sheet plaquettes (`two_le_mul_card_sheetIn`, `exists_sheet_both_sides`, Lean).

It does not floor the free energy, which is that action minus the log of the number of placements. Nothing in a count
bounds the second term.

**Uniformity fails twice.**
- The per-plaquette cost of a sheet has essential infimum 0 (`FluxRate.lean` claim level, `WellDefined.lean`). The sheet
  count gives no action floor uniform over outsides.
- The quantum of action is per tick. At fixed physical size the Bogomolny floor `pi^2 beta(a) ~ (11/3) log(1/(a Lambda))`
  loses to the position entropy `4 log(L/a)` as `a -> 0` (`CONTAINMENT.md` 6.2, one-loop sketch). After asymptotic
  freedom, the floor per physical box is a scale-free function of `L Lambda` (dimensional transmutation). Integrality
  does not set it.

**The sign is reversed on the twist side.**
- An action floor on twists makes them rare: `F_tw` large, so `F_e` small, which is the electric-free, weak-coupling side.
- O1 needs `F_tw <= 0.297`: the twist's action floor must **lose** to the entropy of its placements, by a margin and
  uniformly.
- A count gives lower bounds on action. O1 needs an upper bound on a free energy, which can only come from exhibiting
  enough twisted configurations, a lower bound on `Z_tw`.
- Moreover, the single-plane twist of the hand-over has twist product 0. Flat twist-eater configurations with `Q = 0`
  exist, so its Bogomolny floor is 0 (`CONTAINMENT.md` 6.2).
- So the integrality lead supports the side already covered by asymptotic freedom, not O1. This matches the fourth
  addendum: the balance between running action and placement entropy falls where perturbation theory stops.

**The known route on the twist side** [classical].
- Tomboulis and Yaffe (1985) proved that a small twist (vortex) free energy implies confinement. Proving the small twist
  free energy itself, uniformly, is the open part.
- An attempted proof of that for SU(2) at all beta (Tomboulis 2007) is not regarded as complete [classical; cited from
  memory, not checked here].

### 9.3 Does GRH show integrality beating entropy?

**No. It shows the same non-uniformity.** [classical]
- **Integer counts certify finite ranges only.** Zero counts are integers (argument principle: `N(T)` is a contour
  integral of `xi'/xi` divided by `2 pi i`). Turing's method combines an integer count with an averaged bound on `S(T)`
  to certify that all zeros up to a height lie on the line. It certifies finite ranges only; nothing extends (PREP,
  hand-over entry).
- **A count below 1 is never reached.** To exclude zeros from a region one would need a count below 1. Zero-density
  bounds `N(sigma, T) << T^{A(1 - sigma)} (log T)^B` stay above 1 for large `T`.
- **Positivity gives slack, but not uniform slack.** The one place GRH-type positivity gives a quantitative zero-free
  region is de la Vallee Poussin's: the positive polynomial `3 + 4 cos theta + cos 2 theta = 2 (1 + cos theta)^2`,
  applied to the nonnegative coefficients of `log zeta`, gives no zeros for `sigma > 1 - c/log(|t| + 2)`. The slack comes
  from positivity on the prime side and **shrinks like `1/log t`**.
- This is the Yang-Mills pattern: Perron-Frobenius slack per torus, shrinking with the volume.

### 9.4 The two-box encoder

**The object** (Lean, `GRHLens.lean` section 7). Two boxes share a face; their labels have a joint law `p` on
`Z_2 x Z_2`.
- `xor_product`: if the boxes are independent, the coefficient of the summed label is the product of the two coefficients
  (side by side). By the half-turn the electric factors then compose by hyperbolic addition (`elec_mul`).
- `twoBox_defect`: the departure from the product is the determinant `4 (p00 p11 - p01 p10)/S^2` of the joint law. It
  vanishes exactly for independent boxes.
- The half-turn on two boxes is the tensor square of the Hadamard matrix [classical].
- Reading the determinant as the shared root (the labels tied through the common face, the owner's "entangled") is
  [reading].
- `flux_superadd`'s loss `2C` is the two-box term of the chain. That it is controlled by this defect is a heuristic: the
  Lean identity is for `Z_2` labels, `flux_superadd` for power sums, and their identification is not proved.
- The spanning data (cheap sheets span at beta 2.3, finite clusters at 3.5; `COARSE-TEST.md` 7, via PREP) are
  exploratory.

**Do O1 and the NP rounding step become the same kind of statement? Partly.**
- **Same shape.** Each is a statement about what passes a shared face, uniformly over everything else: all outsides, or
  all derivations and splits. Neither can be certified from one side alone:
  - one line is lossless (`thr_share_one`, Lean);
  - one box's integer floor is per tick and loses to entropy (9.2).
- **Different kind.** O1 is a lower bound on a **sum**: twisted configurations must be abundant, `Z_tw >= 0.743 Z`, and
  entropy works for it. The NP step is a lower bound on a **minimum**: every refutation must be large, against one best
  derivation. Positivity and entropy act on sums and have no grip on minima. That is why pseudo-expectations fail to
  price cutting planes (section 5).
- **Verdict:** same two-boundary shape [reading], not the same mathematical kind. A partial negative.
