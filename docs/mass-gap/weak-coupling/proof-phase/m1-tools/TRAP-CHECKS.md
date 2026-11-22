# Trapping checks T1-T4 (m1-tools, 2026-11-22)

Brief: the four open checks of `TRAP.md` 0.6 for trapping with excision: T1 the per-block filling is well defined and
regular; T2 the excised blocking is link-reflection positive; T3 P2′ (and the rest of §6) applies with excision; T4 the
filled field is small-field across block faces inside a hole. Paper level; claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **T1 holds (paper).** Filling a hole inside one block is a finite-dimensional least-action problem with small-field
   boundary data. A minimiser exists (compact group); every configuration with a deep plaquette costs more action than a
   smooth extension of the data, so the minimiser is small-field; there it is unique up to gauge (the Wilson action is
   strictly convex near the identity in an axial gauge, with a Poincaré bound on the hole) and analytic in the data
   (implicit function theorem).
2. **T2 holds (paper), with one refinement of the rule.** A face-crossing bond inside a hole belongs to no block; it is
   filled in a second stage from the two already-filled blocks it joins. Every ingredient then reads only bonds of the
   blocks (or block pairs) of the coarse bond it feeds, and commutes with the reflections, so `rp_map`
   (`Twist.lean`) gives link reflection positivity of every excised layer.
3. **T3 holds for P2′ as written; one adaptation is needed in V1.** P2′ concerns the true Wilson measure with the hole
   frozen, which is unchanged by excision. But V1's constrained minimiser now has the constraint on the average of the
   **filled** field, whose hole part is a function of the surroundings. That is `[15]`'s problem plus a small analytic
   term localised at the hole's boundary. `[15]`'s contraction arguments are stable under such perturbations, but this was
   not checked line by line. **Routine, not done.**
4. **T4 holds (paper).** Each block's filling is within `O(ε_k D0^{d/2})` of the least-action continuation of all the
   surroundings, so plaquettes straddling a face inside a hole are at most `O(ε_k D0^{d/2})` from the identity, with
   `ε_k D0^{d/2} = g_k p0(g_k) (100 M R_h)^{d/2} ≪ 1`. The filled field is small-field with a polylogarithmically larger constant, inside the analyticity
   domains Balaban uses.

## 1. T1: the per-block filling

**Setting.** A trapped hole `H` (fine bonds), a block `B` of the next scale, data = the bonds of `B \ H`, regular (all
plaquettes of the corrected field within `ε` of the identity, `ε = ε_k` in scale units), and `|H ∩ B| ≤ |H| ≤ (100 M
R_h)^d`. **Problem:** minimise the Wilson action of the plaquettes of `B` over the bonds of `H ∩ B`.

* **Existence:** the bonds of `H ∩ B` range over a compact product of copies of SU(2); the action is continuous.
* **The minimiser is small-field:** in an axial gauge from the data, the smooth extension (the data's interpolation)
  has action `≤ C ε² |H| = C g² p0² polylog`, while any configuration with a plaquette at distance `≥ r` from the
  identity has action `≥ c r²`. So the minimiser has all plaquettes within `r_* = C ε |H|^{1/2}` of the identity,
  `≪ 1`.
* **Uniqueness modulo gauge, analyticity:** on small fields, in the axial gauge, the second variation of the Wilson
  action is `≥ γ0 ‖∂B'‖² - O(r_*)‖B'‖²` (as [V] (1.7)) and the Poincaré bound with Dirichlet data on `B \ H` gives
  `‖∂B'‖² ≥ c(D0)‖B'‖²`; so the action is strictly convex on the small-field set, the minimiser is unique, and by the
  implicit function theorem it is analytic in the data (and extends to complex data near the real ones).
* **Covariance and symmetry:** the problem is gauge covariant and symmetric under the lattice symmetries that preserve
  `B`; the minimiser (unique modulo gauge) is a covariant, symmetric function of the data.

## 2. T2: link reflection positivity of the excised blocking

**Rule, refined.** Stage 1: fill `H ∩ B` (interior bonds of each block `B`) from the data of `B`, as in T1. Stage 2:
each face-crossing bond `b ∈ H` between blocks `B, B'` is filled by least action given the filled `B ∪ B'` (a
one-bond problem, same arguments). Balaban's average of a coarse bond `c` reads `B(c_-) ∪ B(c_+)` and the face bonds
between them.

**Check.** Reflection `Θ` in a plane on block faces (between fine sites). (i) Commutation: blocks map to blocks, face
bonds to face bonds; the filling problems are mapped to the reflected problems and their minimisers correspond
(uniqueness modulo gauge, T1); Balaban's average commutes ([I] p. 252, (0.5)); trapping decisions are made from
plaquette traces, which commute. (ii) Half property: a coarse bond in the positive half has both blocks and its face in
the positive half, and every ingredient of its value reads only bonds of those blocks and that face. The face bonds
crossing the reflection plane feed only coarse bonds crossing it, which are in neither half. By `rp_map`
(`Twist.lean`) each excised layer of the Wilson measure is link-reflection positive. ∎ (paper)

## 3. T3: does the rest of the argument see the excision?

* **P2′:** concerns the Wilson measure with the hole frozen and its back-reaction on the surroundings' integrals. The
  measure is unchanged by excision (excision changes only the blocking map). Unchanged.
* **Exactness:** `map_resample_eq` holds for any measurable blocking, with the records in the conditioning variable.
  Unchanged.
* **V1 (the constrained minimiser):** the constraint is now `M(V ∪ F(V)) = W` with `F` the filling of the hole from the
  surrounding `V`. Write `Ṽ = V ∪ F(V)`. Minimising the true action (hole frozen) over `V` with `M(Ṽ) = W` is
  minimising `A(Ṽ) + δA(V)` where `δA` is the difference between the true action of the plaquettes touching the hole
  (with the frozen content) and their action in `Ṽ`: an analytic function of the bonds within distance 1 of `∂H`, of
  size `O(1)` but constant up to terms `O(ε²)` in the small-field variables. `[15]`'s proof (expansion, linearising
  contraction, critical-point contraction) is stable under adding such a localised analytic term whose derivative is
  `O(ε)` (it changes the current `J` by a localised `O(ε)` term and the quadratic form by `O(1)` on a bounded set,
  which Balaban's bounds absorb as they absorb his boundary terms). **Not checked line by line; routine.**
* **E3, E5-E9:** expand around the same constrained minimiser; nothing else changes.

## 4. T4: the filled field across faces

The data of every block around a hole are small-field and are restrictions of one regular configuration (the
surroundings). By T1 each block's filling is within `O(ε |H|^{1/2})` of the minimiser of the action with the data of
**all** blocks (both are least-action extensions of nearby data on overlapping regions; their difference solves a
linear problem with data of size `O(ε)` on the cut faces). A plaquette straddling a face inside the hole is therefore
within `O(ε D0^{d/2})` of the identity; with `ε = g_k p0(g_k)` and `D0 ≤ 100 M R_h`, this is `g_k · polylog(g_k^{-2})
≪ 1`, inside Balaban's small-field domain after enlarging his constants by a polylogarithmic factor (his thresholds
carry such factors anyway). ∎ (paper, sketch-level constants)

## 5. Effect

TRAP is now: accounting (paper, `TRAP.md`), T1, T2, T4 (paper, here), T3 (paper except the V1 adaptation, routine, not
done). The deep-core part of M1 rests on: TRAP (as above), P2′ (proof given Balaban's bounds I1-I3), P4 (citation level).
