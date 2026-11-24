# Are Sp(2) and G2 rigid? (ledger rows IX.6j, IX.6p)

*Research round, 2026-11-24. Notes only: no paper edits, no Lean, nothing committed. Tests the owner's witness reading (`PREP.md`,
2026-11-24, "The two hidden witnesses", item 4; "The fake G2 is cancelled by the start's reflection positivity"; "Only a start that
forces a decidable reading"), which needs both Sp(2) and G2 rigid. Builds on `docs/unified/PERELMAN-DMP.md` section 2 (the same
computation for SU(N)) and does not repeat its background.*

Marks as in the ledger: **[classical]** known, with a reference; **[external]** published by others and read here; **[paper]**
argued here in prose from classical theorems; **[reading]** a DMP reading; **[open]** not settled by anyone, as far as found.
"Recalled" means the reference was not re-read this round.

"Rigid" has two strengths, and this round needs both (Kreck-Lueck 2005, Definition 0.2, read):
* **strongly rigid**: every homotopy equivalence `N -> M` from a closed manifold is homotopic to a homeomorphism, i.e. the
  structure set `S^TOP(M)` is one point;
* **rigid**: every closed manifold homotopy equivalent to M is homeomorphic to it. For simply connected M this holds exactly when
  the self-homotopy equivalences of M act transitively on `S^TOP(M)` (Kreck-Lueck, Theorem 1.1, read).

## 0. The result in six lines

1. **Sp(2) is strongly rigid [paper, independent read: confirmed].** `S^TOP(Sp(2))` is a point. The coordinator's sketch is
   right in every step. Two points were left implicit and are filled in here: spectral-sequence differentials could have killed
   the top class (they cannot), and "detected by the Kervaire invariant" is Sullivan's formula with Wu classes zero.
2. **Sp(2), smooth [paper; partly open].** Every closed smooth manifold homotopy equivalent to Sp(2) is diffeomorphic to
   `Sp(2) # Sigma` for an exotic 10-sphere `Sigma` in `Theta_10 = Z/6`. Which of these six are diffeomorphic to Sp(2) (the
   inertia group) is not settled. The order-3 ones are not reached by a diffeomorphism homotopic to the standard homeomorphism.
3. **G2 is not strongly rigid [paper].** `S^TOP(G2)` has **exactly two** elements. The coordinator's "likely not a point" is
   confirmed and made exact. The second element is a homotopy equivalence `h: X -> G2` whose normal invariant is the class
   `x_3^2` in degree 6, pulled back from `S^6 = G2/SU(3)`.
4. **The fake X is invisible to every characteristic class [paper].** X is stably parallelisable, h is tangential, and X can be
   taken smooth. All Pontryagin, Stiefel-Whitney and Kirby-Siebenmann classes agree with those of G2.
5. **Whether X is homeomorphic to G2 is open [open].** It holds exactly when G2 has a self-homotopy equivalence that is not
   homotopic to a homeomorphism. Kreck and Lueck's construction of such maps (built on the Kervaire-invariant-one element `nu^2` in
   dimension 6) is blocked for G2 at one precise point (2.5). I found no paper that settles it.
6. **For the readings:** the witness reading survives, but in a weaker form than for SU(3) and Sp(2). G2 can at best be rigid,
   not strongly rigid, and whether it is rigid is a single, sharply stated test. The "room" for the fake G2 is exactly the class
   `x_3^2` the owner named.

No solution of an open problem is claimed. Everything settled here is a standard surgery computation from classical theorems. I
found no published statement of either result (negative search, section 4).

---

## 1. Sp(2) = Spin(5): independent read of the sketch (row IX.6j)

### 1.1 Data

* Sp(2) is a closed, simply connected, parallelisable (Lie group) 10-manifold **[classical]**.
* `H^*(Sp(2); Z) = Lambda(x_3, x_7)`, torsion free, so cohomology lives in degrees 0, 3, 7, 10 **[classical]**.
* Cells: `Sp(2) = S^3 cup_omega e^7 cup e^10`, with the 7-cell attached by the generator `omega = nu' + alpha_1(3)` of
  `pi_6(S^3) = Z/12` **[external]** (Maruyama-Oshima 2008, section 2, read). The sketch's "cells in dimensions 0, 3, 7, 10" is
  right. The attaching map matters for the homotopy type (Sp(2) is not `S^3 x S^7`). It does not matter for the surgery count,
  which sees only the cohomology.
* Parallelisable implies that all Stiefel-Whitney classes and hence all Wu classes `v_i`, i > 0, vanish **[classical]**.

### 1.2 Facts about G/TOP used (here and for G2) [classical, recalled]

* `pi_i(G/TOP)` = Z, 0, Z/2, 0 for i = 0, 1, 2, 3 mod 4 (i >= 1), and `pi_i(G/TOP) = L_i(1)` (Kirby-Siebenmann 1977).
* **At odd primes** `G/TOP[1/2] = BO[1/2]` (Sullivan). **At 2** `G/TOP_(2)` is a product of Eilenberg-MacLane spaces
  `prod_{i>=1} K(Z/2, 4i-2) x K(Z_(2), 4i)` (Kirby-Siebenmann, Essay V; Madsen-Milgram 1979, ch. 4). The coordinates are the
  Kervaire classes `k_{4i-2}` and the Morgan-Sullivan classes `l_{4i}`. (For G/PL the bottom k-invariant `delta Sq^2` is
  non-zero. For G/TOP it vanishes.)
* **Sullivan's formula** in dimension 4k + 2 (Rourke-Sullivan 1971): the surgery obstruction of a normal invariant
  `f: M -> G/TOP` is `<V(M)^2 . f^*k, [M]>` in `L_{4k+2} = Z/2`, where `k = sum k_{4i+2}` and V is the total Wu class.
* **Additivity at the top cell.** If `c: M -> S^n` collapses the complement of a disc, then `c^*: pi_n(G/TOP) -> [M, G/TOP]` acts on
  normal invariants by connected sum with a normal map to `S^n`, and the surgery obstruction adds: `theta(x # t) = theta(x) + theta(t)`.
  Also `theta: pi_n(G/TOP) -> L_n` is an isomorphism for n >= 5 (because `S^TOP(S^n)` is a point).

### 1.3 Normal invariants: `[Sp(2), G/TOP] = Z/2`, from the top cell [paper]

* Odd primes: `[Sp(2), BO[1/2]]` is a quotient of `sum_i H^{4i}(Sp(2); Z[1/2]) = 0` (no cohomology in degrees 4, 8). So it is 0.
* At 2, by the product splitting: `H^2(;Z/2) = H^4(;Z_(2)) = H^6(;Z/2) = H^8(;Z_(2)) = 0` and `H^10(Sp(2); Z/2) = Z/2`. So
  `[Sp(2), G/TOP] = Z/2`, and the non-zero element is `t = c^*(generator of pi_10(G/TOP))`.
* **The gap in the sketch, closed.** The sketch reads the answer off the diagonal terms `H^p(M; pi_p(G/TOP))` (only p = 10
  survives: `pi_3 = pi_7 = 0`). In that spectral sequence there are possible differentials into the top term, from
  `H^3(M; pi_4) = Z` and `H^7(M; pi_8) = Z`. They could have killed it. They do not, for two independent reasons: (a) the
  product splitting above has no differentials at all; (b) `theta(c^* t) = theta(t) = 1` by additivity, so `c^* t != 0`.

### 1.4 Surgery obstruction and structure set: a point [paper]

* `theta(t) = 1` (additivity). Equivalently, by Sullivan's formula with `V = 1`, `theta(f) = <f^* k_10, [Sp(2)]>`: the top class is
  detected by the Kervaire invariant, as the sketch says.
* So `theta: [Sp(2), G/TOP] = Z/2 -> L_10 = Z/2` is an isomorphism, with kernel 0.
* Surgery exact sequence (TOP, n = 10, simply connected): `L_11(1) = 0 -> S^TOP(Sp(2)) -> [Sp(2), G/TOP] -> L_10(1)`. Hence
  `S^TOP(Sp(2))` is **one point**: every homotopy equivalence from a closed topological manifold to Sp(2) is homotopic to a
  homeomorphism. **The sketch is confirmed.**

What the non-trivial normal invariant is: the 10-dimensional Kervaire problem on the top cell. It has surgery obstruction 1, so it
is not realised by any homotopy equivalence. (This is the obstruction behind Kervaire's 1960 non-smoothable 10-manifold
**[classical]**.)

### 1.5 Literature on homotopy Sp(2)s [external / classical, partly recalled]

* **Principal `S^3`-bundles over `S^7`** are classified by `pi_6(S^3) = Z/12`, and Sp(2) is the one with the generator.
  **Hilton-Roitberg (1969)**, recalled: the bundle with class `7 omega` is an H-space ("the criminal") that is not homotopy
  equivalent to any Lie group, although its product with `S^3` is diffeomorphic to `Sp(2) x S^3`. It is **not homotopy
  equivalent to Sp(2)**, so it does not bear on rigidity. It shows only that Sp(2) is fixed by its homotopy type, not by its
  rational type or its "H-space type". Durán-Mendoza-Rigas (arXiv 0708.1577, abstract and summary read) treat the same bundles
  and confirm `Sp(2) x S^3 = E_{7 omega} x S^3`.
* **Gromoll-Meyer (1974)**, recalled: the exotic 7-sphere arises as a biquotient `Sp(2)//Sp(1)`. This is a quotient *of* Sp(2) and
  says nothing about fake Sp(2)s.
* **No published statement** that `S^TOP(Sp(2))` is a point, or of the inertia group of Sp(2), was found (negative search).
  Kreck-Lueck (2005) treat `S^k x S^d`. Their Theorem 0.13(a) says `S^3 x S^7` is strongly rigid **[external]**, which is the same
  computation for Sp(2)'s rational twin.

### 1.6 Sp(2), smooth [paper; open part marked]

* `Theta_10 = Z/6` (`bP_11 = 0`, and the Kervaire invariant vanishes in dimension 10) **[classical, Kervaire-Milnor 1963,
  recalled]**.
* The smooth surgery sequence has the same shape, with `[Sp(2), G/O]` a quotient of `pi_10(G/O)` via `c^*`, because
  `pi_3(G/O) = pi_7(G/O) = 0` (cokernel of J). Also `theta = 0` on `pi_10(G/O)` (no smooth Kervaire problem in dimension 10). So
  every closed smooth manifold homotopy equivalent to Sp(2) is **diffeomorphic to `Sp(2) # Sigma`** for some `Sigma` in
  `Theta_10` **[paper]**. All of these are homeomorphic to Sp(2) (1.4).
* **The 3-part.** At p = 3, `G/O_(3) = BSO_(3) x Cok J_(3)`, and `Cok J_(3)` is 9-connected with `pi_10 = Z/3` (beta_1).
  Hence `[Sp(2), G/O]_(3) = Z/3` and `c^*` is injective there. So for `Sigma` of order 3, `Sp(2) # Sigma` is **not**
  diffeomorphic to Sp(2) by a diffeomorphism homotopic to the standard homeomorphism. That is, `Sigma` is not in the *homotopy*
  inertia group **[paper]**.
* **Open:** the inertia group `I(Sp(2))` itself. A self-homotopy equivalence of Sp(2) is homotopic to a homeomorphism (1.4), but
  its smooth normal invariant can still be an exotic sphere. Settling it needs the self-equivalences of Sp(2) (the method of
  Wang 2021 for SU(3), via Frank's pairing on the clutching function, is the natural route) **[open]**. Also open: the 2-part
  (`eta mu`) of the homotopy inertia group, where differentials from `H^3(pi_4 G/O)` and `H^7(pi_8 G/O)` were not computed.

---

## 2. G2 (row IX.6p)

### 2.1 Data

* G2 is a closed, simply connected, parallelisable 14-manifold. Cells: `S^3 cup e^5 cup e^6 cup e^8 cup e^9 cup e^11 cup e^14`
  **[external]** (Maruyama-Oshima 2008, section 5, read).
* `H^*(G2; Z/2) = F_2[x_3]/(x_3^4) (x) Lambda(x_5)`, with `x_5 = Sq^2 x_3` and `x_6 = x_3^2 = Sq^1 x_5` **[classical]**
  (Borel 1954, recalled). Classes in degrees 3, 5, 6, 8 (`x_3 x_5`), 9 (`x_3^3`), 11 (`x_3^2 x_5`), 14.
* **Integral cohomology [paper, derived by Bocksteins; agrees with Borel]:** Z in degrees 0, 3, 11, 14, and Z/2 in degrees 6
  (generated by `x_3^2`) and 9 (`x_3^3`). **Zero in degrees 4, 5, 8, 10, 12.** In particular `H^8(G2; Z) = 0`: the mod 2 class
  `x_3 x_5` in degree 8 is the reduction of nothing. It is the partner of `x_3^3` under the Bockstein (`Sq^1(x_3 x_5) = x_3^3`).
* Fibration `SU(3) -> G2 -p-> S^6`. Its transgression sends `x_5` to `2 u_6`. So `x_3^2 = p^* u_6` is pulled back from `S^6`
  (integrally and mod 2) **[paper]**. The clutching function is the generator of `pi_5(SU(3)) = Z`, because `pi_5(G2) = 0`.
* Homotopy groups **[external]** (Mimura 1967, quoted in Maruyama-Oshima Table 5, read): `pi_6 = Z/3`, `pi_8 = Z/2 <eta_6^2>`,
  `pi_9 = Z/6`, `pi_11 = Z + Z/2`, `pi_14 = Z/168 + Z/2`, `pi_15 = Z/2`. Zero in degrees 4, 5, 7, 10, 12, 13. The top cell
  splits off stably (Browder-Spanier, cited there).
* Wu classes vanish (parallelisable) **[classical]**.

### 2.2 Normal invariants: four elements [paper]

* Odd primes: `H^{4i}(G2; Z[1/2]) = 0` for i = 1, 2, 3. So 0.
* At 2, the product splitting gives the coordinates
  `H^2(Z/2) = 0, H^4(Z_(2)) = 0, H^6(Z/2) = Z/2, H^8(Z_(2)) = 0, H^10(Z/2) = 0, H^12(Z_(2)) = 0, H^14(Z/2) = Z/2`.
* **Degree 8 contributes nothing.** G/TOP's degree-8 factor has coefficients `Z_(2)`, and `H^8(G2; Z) = 0`. The mod 2 class
  `x_3 x_5` is not a coordinate.
* So `[G2, G/TOP]` has **four elements** `(a_6, a_14)` in `Z/2 x Z/2`: `a_6 = f^* k_6` (a multiple of `x_3^2`) and
  `a_14 = f^* k_14`.
* Two of them are named: `t = c^*(generator of pi_14(G/TOP))`, i.e. (0, 1), and `p^* iota`, with `iota` the generator of
  `pi_6(G/TOP) = Z/2`. Its coordinates are `(x_3^2, 0)`: the degree-14 coordinate vanishes, since it is pulled back from
  `H^14(S^6) = 0`.

### 2.3 Surgery obstruction and structure set: exactly two elements [paper]

* By Sullivan's formula with `V = 1`: `theta(a_6, a_14) = a_14`. So `theta(p^* iota) = 0`, and the kernel is `{0, p^* iota}`.
* **Check without the formula.** The top-cell action `x -> x # t` is free on the four elements (it flips `a_14`), and it flips
  `theta` (additivity). So each orbit `{x, x # t}` contains exactly one element of the kernel, and the kernel has exactly two
  elements whatever `theta(p^* iota)` is. The formula only says which two.
* A second consistency check (sketch): `p^* iota` is the pull-back of the 6-dimensional Kervaire problem along the bundle, whose
  fibre SU(3) has signature 0. The transfer of a Kervaire obstruction along a fibre of zero symmetric signature is zero.
* `L_15(1) = 0`, so the L-group acts trivially and `S^TOP(G2)` injects into the normal invariants. Every kernel element is
  realised (n = 14 >= 5).
* **Result: `S^TOP(G2) = {id, h}` has exactly two elements.** The second is a homotopy equivalence `h: X -> G2` from a closed
  topological 14-manifold, with normal invariant `p^* iota = x_3^2`. **G2 is not strongly rigid.**

### 2.4 What the fake X is [paper]

* `iota` is the image of `nu^2` in `pi_6(SG) = pi_6^s` (`nu^2` has Kervaire invariant 1: `S^3 x S^3` with the Lie framing)
  **[classical]**. So `p^* iota` is the image of the map `nu^2 . p: G2 -> S^6 -> SG`.
* So the normal invariant maps to zero in `[G2, BTOP]`. **h is tangential**, and X is **stably parallelisable**, like G2.
* It also lifts to G/O, and its smooth surgery obstruction is the same (zero). So **X can be taken smooth**: there is a closed
  smooth manifold homotopy equivalent to G2 whose homotopy equivalence is not homotopic to any homeomorphism.
* Every characteristic class agrees: rational Pontryagin classes (all zero, `H^{4i}(G2; Q) = 0` below the top), Stiefel-Whitney
  classes (homotopy invariant), and Kirby-Siebenmann (`H^4 = 0`). **No characteristic class can tell X from G2.** The only
  difference is a mod 2 splitting invariant along a 6-dimensional Z/2-cycle (Sullivan's characteristic variety). That is a
  property of h, not of X alone.

### 2.5 Is X homeomorphic to G2? [open, reduced to one test]

**Reduction [paper, from Kreck-Lueck Theorem 1.1].** X is homeomorphic to G2 iff `[h]` lies in the orbit of `[id]` under the
self-homotopy equivalences of G2. With only two elements this means: **X is homeomorphic to G2 iff G2 has a self-homotopy
equivalence g that is not homotopic to a homeomorphism** (its normal invariant is then necessarily `x_3^2`).

* Every self-equivalence acts as the identity on `H^*(G2; Z/2)`, since each degree is one-dimensional. So by Ranicki's composition
  formula (`[f_2 . f_1] = (f_2)_*[f_1] + [f_2]`, quoted in Kreck-Lueck section 7) the normal invariant is a **homomorphism** from
  the self-equivalence group to Z/2 **[paper, sketch]**. G2 is rigid iff this homomorphism is onto.

**The model case [external, Kreck-Lueck Theorem 0.13(d), read].** `S^k x S^d` with k = 2 mod 4 has the same kind of Z/2: a normal
invariant in `H^k(; Z/2)` that the surgery obstruction does not see. It is rigid iff a self-equivalence carries a framed
k-manifold of Kervaire invariant 1. So such rigidity is tied to the Kervaire-invariant-one problem (Remark 0.14). For G2 the
relevant dimension is k = 6, where Kervaire invariant one *exists* (`nu^2`). So the classical obstruction does not rule G2 out.

**Why the standard construction does not apply directly [paper].** Kreck-Lueck build the self-equivalence (section 2, read) as a
pinch map `id # alpha: M # S^n -> M`, with `alpha: S^n -> M` built from a *sphere* `phi: S^d -> M` meeting a k-cycle once,
composed with the Kervaire element. For G2 that would need an 8-sphere dual to `x_3^2`, i.e. one that is non-zero on `x_3 x_5`
in `H^8(;Z/2)`. **None exists:** `x_3 x_5` is a product, so it vanishes on every map from `S^8` (and indeed
`pi_8(G2) = Z/2 <eta_6^2>`). The dual cycle is a torsion (Bockstein) class, not a sphere.

**What would decide it (sketch, not a proof).** Pinch maps `g_alpha` for `alpha` in `pi_14(G2) = Z/168 + Z/2` are still
self-equivalences (`alpha` has Hurewicz image 0). By S-duality on the framed G2, the 6-coordinate of the normal invariant of
`g_alpha` should be read from the stable image of `alpha` as `nu^2` on the 8-cell (the S-dual of `p^*(nu^2)`). So the concrete
test is:

> **Does some element of `pi_14(G2)` (2-primary generators `<nu-bar_6 + epsilon_6>` and `i_*[nu_5^2] . nu_11`, Mimura) carry
> `nu^2` on the 8-cell stably?** A yes, or any other self-equivalence of G2 with normal invariant `x_3^2`, makes X homeomorphic
> to G2 (G2 rigid). A homeomorphism invariant separating X from G2 makes it non-rigid, with exactly two homotopy G2s.

The S-duality formula for pinch maps and the reading of these generators are sketches. I did not verify them. **Status: open.**

**Smooth G2, not done.** `Theta_14 = Z/2` (Kervaire-Milnor, recalled). The smooth question adds `G2 # Sigma^14` and the fake X's
smoothings. This round does not treat it **[open]**.

### 2.6 Literature for G2 [external where read; negative search otherwise]

* No paper on "homotopy G2", "fake G2", the structure set of G2, or the rigidity of compact Lie groups beyond SU(3) was found.
  Searches covered surgery on Lie groups, Borel manifolds, inertia groups and self-maps of G2.
* **Kreck-Lueck, "Topological rigidity for non-aspherical manifolds"** (arXiv math/0509238; PAMQ 5 (2009)), read: the
  definitions, the criterion (Theorem 1.1), the construction of self-equivalences (Theorem 2.2) and products of spheres
  (Theorem 0.13). This is the framework used above. Lie groups are not treated.
* **Maruyama-Oshima, "Homotopy groups of the spaces of self-maps of Lie groups"**, J. Math. Soc. Japan 60 (2008) (arXiv
  0712.2080), read in part: the cell structures, `pi_*(G2)` and `[Sigma G2, G2] = Z/2 + Z/2`. Self-maps of G2 were also studied
  by Oka (Proc. Edinburgh Math. Soc. 1986) and by Oshima (several papers, cited there; not read). None of these computes normal
  invariants. Their group of self-equivalences is the input the test in 2.5 needs.
* **S. Biswas, arXiv 2604.15984 (2026)** (abstract read): decides which self-maps of the Stiefel manifolds `V_{n,2}` are homotopic
  to almost-diffeomorphisms, "via normal invariants of specific tangential homotopy equivalences". This is the same method the G2
  test needs, on a related space (`G2/SU(2) = V_{7,2}`). It is worth reading in full if the test is pursued.

---

## 3. What this means for the owner's readings

The witness reading (IX.6o) needs Sp(2) and G2 both rigid. **Sp(2) passes, in the strong form that SU(2) and SU(3) also have**
**[paper]**: its structure set is a point, so the rank-2 groups SU(3) and Sp(2) are fixed by their homotopy type, and even each
homotopy equivalence to them is rigid. **G2 is different, and that much is settled [paper]**: it is not strongly rigid. There
are exactly two homotopy-equivalence classes of "presentations" of G2, and the second one is carried by exactly the class
`x_3^2` the owner pointed to. Whether the second presentation is G2 itself, seen through a symmetry (a self-equivalence), is the
open test in 2.5 **[open]**.

The reading "the fake G2 is cancelled by the start's reflection positivity" (IX.6q) therefore has a precise mathematical
counterpart: **"cancelled" = absorbed by a self-equivalence of G2**, i.e. the normal-invariant homomorphism from G2's
self-equivalences onto Z/2 exists **[reading]**. It predicts rigid, and the test can falsify it.

If the test comes out negative, a finer notion still fits without forcing anything: **G2 is rigid up to one Z/2 that carries no
order**. The difference between G2 and X lives in `H^6(G2; Z) = Z/2`, which is torsion. It is invisible to every rational
invariant and every characteristic class, and both manifolds are stably parallelisable **[paper]**. That a Z/2 cannot carry an
ordering is classical (no ordered ring has characteristic 2, X.70a). Reading this as "the start forces a decidable reading up to
a sign-free Z/2" would be a **[reading]**, and a weaker one than the witness reading asks for. The test should come first.

---

## 4. Proposed replacement rows (for the coordinator; not applied)

| IX.6j | Sp(2) = Spin(5) is strongly topologically rigid: `S^TOP(Sp(2))` is a point, so every homotopy equivalence from a closed topological manifold to Sp(2) is homotopic to a homeomorphism. Cells 0, 3, 7, 10 (7-cell on the generator of `pi_6(S^3) = Z/12`); `[Sp(2), G/TOP] = H^10(Sp(2); Z/2) = Z/2` (Sullivan's splitting at 2, nothing at odd primes, no differentials); the surgery obstruction is the Kervaire invariant (Sullivan's formula, Wu classes 0), an isomorphism onto `L_10 = Z/2`; `L_11 = 0`. Smooth: every smooth homotopy Sp(2) is diffeomorphic to `Sp(2) # Sigma`, `Sigma` in `Theta_10 = Z/6`; the order-3 `Sigma` are not in the homotopy inertia group. (Sp(2) and G2 pass the rational test that excludes SU(N), N >= 4; the witness reading IX.6o needs both rigid) | paper (a surgery computation from classical theorems; independent read confirms the coordinator's sketch; no published statement found) | Kirby-Siebenmann 1977; Sullivan; Rourke-Sullivan, Ann. of Math. 94 (1971); Madsen-Milgram 1979, ch. 4; Kervaire-Milnor 1963; Maruyama-Oshima, J. Math. Soc. Japan 60 (2008) section 2; Kreck-Lueck, PAMQ 5 (2009); `docs/unified/G2-SP2-RIGIDITY.md` 1 | smooth only: the inertia group of Sp(2) in `Theta_10` |
| IX.6p | `S^TOP(G2)` has exactly two elements, so G2 is not strongly rigid: `[G2, G/TOP]` has four elements (`H^6(G2; Z/2) = Z/2` from `pi_6(G/TOP)`, `H^14(G2; Z/2) = Z/2` from the top cell; `H^8(G2; Z) = 0` and the odd primes contribute nothing), the surgery obstruction is the top coordinate, `L_15 = 0`. The second structure `h: X -> G2` has normal invariant `x_3^2`, pulled back from `S^6 = G2/SU(3)`; h is tangential, X is stably parallelisable and can be taken smooth, and no characteristic class separates X from G2. X is homeomorphic to G2 iff G2 has a self-homotopy equivalence not homotopic to a homeomorphism (Kreck-Lueck); whether it does is not decided (the Kreck-Lueck construction needs an 8-sphere dual to `x_3^2`, and none exists since `x_3 x_5` is decomposable) | paper (the two-element structure set, from classical theorems); open (whether X is homeomorphic to G2) | Borel 1954; Mimura 1967 via Maruyama-Oshima 2008 Table 5; Kirby-Siebenmann 1977; Rourke-Sullivan 1971; Kreck-Lueck, PAMQ 5 (2009), Thm 0.13, 1.1, 2.2; `docs/unified/G2-SP2-RIGIDITY.md` 2 | a self-equivalence of G2 with normal invariant `x_3^2` (test: does some element of `pi_14(G2)` carry `nu^2` on the 8-cell stably?), or an invariant separating X from G2; the smooth case (`Theta_14 = Z/2`) |

Knock-on edits for the coordinator to weigh (not applied):
* **IX.6o** (witness reading): the dependency stays IX.6j, IX.6p. Its care point could say "Sp(2) passes (strongly rigid); G2 is
  not strongly rigid, and its rigidity is one open test".
* **IX.6q** (the fake G2): the room is confirmed to be exactly `x_3^2`, and the fake exists as a structure. "Cancelled" has the
  counterpart "absorbed by a self-equivalence" (section 3).
* `PREP.md` "The two hidden witnesses", item 4: "the structure set is likely not a point" becomes "has exactly two elements".

---

## Sources

* M. Kreck, W. Lueck, "Topological rigidity for non-aspherical manifolds", arXiv math/0509238; *Pure Appl. Math. Q.* 5 (2009).
  Read this round: Definition 0.2, Theorems 0.6, 0.13, 1.1, 1.2, 2.2, Remark 0.14, section 7 (end).
* K. Maruyama, H. Oshima, "Homotopy groups of the spaces of self-maps of Lie groups", *J. Math. Soc. Japan* 60 (2008), 767ff.;
  arXiv 0712.2080. Read this round: Theorems 1, 2, section 2, section 5 with Table 5.
* M. Mimura, "The homotopy groups of Lie groups of low rank", *J. Math. Kyoto Univ.* 6 (1967) (via Maruyama-Oshima; not read).
* A. Borel, cohomology of G2 (1954) (recalled); W. Browder, E. Spanier, "H-spaces and duality", *Pacific J. Math.* 12, 411-414
  (cited by Maruyama-Oshima; not read).
* R. Kirby, L. Siebenmann, *Foundational Essays* (1977); D. Sullivan, Geometric Topology notes (1970); C. Rourke, D. Sullivan,
  "On the Kervaire obstruction", *Ann. of Math.* 94 (1971); I. Madsen, R. J. Milgram, *The Classifying Spaces for Surgery and
  Cobordism of Manifolds* (1979); A. Ranicki, *Algebraic L-theory and Topological Manifolds* (1992); C. T. C. Wall, *Surgery on
  Compact Manifolds* (1970); M. Kervaire, J. Milnor, *Ann. of Math.* 77 (1963); M. Kervaire, "A manifold which does not admit any
  differentiable structure", *Comment. Math. Helv.* 34 (1960) (all recalled).
* P. Hilton, J. Roitberg, "On principal S^3-bundles over spheres", *Ann. of Math.* 90 (1969) (recalled); C. Durán, A. Mendoza,
  A. Rigas, arXiv 0708.1577 (summary read); D. Gromoll, W. Meyer, *Ann. of Math.* 100 (1974) (recalled).
* X. Wang, *Acta Math. Sinica (Engl. Ser.)* 37 (2021), 941-956 (the SU(3) case and its smooth method, read in the previous round,
  `PERELMAN-DMP.md`).
* S. Biswas, "Rigidity of self-maps of V_{n,2} and manifolds tangentially homotopy equivalent to V_{n,2} x S^k", arXiv
  2604.15984 (abstract read). S. Basu, R. Kasilingam, P. Magar-Sawant, arXiv 2302.02301 (smooth structures in dimensions 8 to 10;
  abstract read; may settle the 2-part of Sp(2)'s homotopy inertia group).
