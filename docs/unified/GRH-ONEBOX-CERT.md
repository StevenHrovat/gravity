# The one-box certificate: Weil's form is positive where only 2 and 3 enter

Working note, 2026-11-23; its analytic estimates have been read by the coordinator only, not independently (paper Part III 4.4, V.8). Follows `docs/rh-guide/grh/SEMILOCAL.md` (sections 0 to 2) and the blueprint in
`BLOWUP.md` section 1 (Chen-Hou: a finite part handled by rigorous numerics, an analytic tail, constants that close
an inequality). Scripts: `grh_onebox_cert.py` (the certificate), `grh_onebox_cert_diag.py` (diagnostics, not part of
the proof). Lean: `ProofPhase/GRH/OneBoxCert.lean`, audit `grhonebox-axioms.sh` / `.log`.

**Claim marks.** **[certified]** = enclosed in ball arithmetic (Arb, through python-flint 0.9.0) by the script, with
the log named; **[proved here]** = analytic step proved in this note; **[classical]** = textbook fact, used as is;
**[numerical]** = floating point, a check and not part of the proof; **[Lean]** = machine-checked.

---

## 0. In plain words

- **What is certified.** Take Weil's form for the Riemann zeta function, in the conventions of
  `docs/rh-guide/grh/weil_numerics.py`. Restrict it to test functions supported in `[-a, a]` with `a = 13/20 = 0.65`.
  At this size only the primes 2 and 3 enter: the prime terms come from the lags `log 2` and `log 3`, and every other
  prime power has `log n >= 2a`, so its term vanishes identically. This restricted form is the full Weil form at this
  support. The certificate shows it is positive for **every** square-integrable `f` on `[-0.65, 0.65]`, real or
  complex, with an explicit margin: `W(f) >= 3.398e-11 * ||f||^2`. **[certified]**
- **Two more supports.** The same run certifies `a = 3/5` (margin `1.5e-9`) and `a = 69/100` (margin `6.417e-13`).
  Positivity at one support implies it at every smaller one, because a function supported in `[-a', a']` is also
  supported in `[-a, a]`. So the `a = 0.69` run covers every support with `e^{2a} <= e^{1.38} = 3.97`: the whole
  range in which only the terms of 2 and 3 enter and the square 4 = 2^2 does not yet. **[certified]**
- **How tight it is.** For each support the script also evaluates `W` on one explicit polynomial. That gives an upper
  bound for the smallest value of `W(f)/||f||^2`. At `a = 0.65` the smallest value lies between `3.398e-11` and
  `3.960e-11`, so the certificate keeps 86 percent of the true margin. **[certified]**
- **How.** Split `f` into a polynomial part of degree below 100 and the rest. On the polynomial part, `W` is a
  100 x 100 matrix: it is computed with rigorous error balls and shown positive definite by a Cholesky factorisation
  in ball arithmetic. On the rest, `W` is at least `0.64 ||g||^2`. The reason is the real place: its weight
  `Re psi(1/4 + ir/2)` grows like `log |r|`, and functions orthogonal to all polynomials of degree below 100 live at
  frequencies above about 113. The coupling between the two parts is computed exactly for the next 42 degrees, and
  beyond them from the explicit singularities of `W` applied to a polynomial: a logarithm at the two ends of the
  interval, and jumps where the shifts by `log 2` and `log 3` cut the interval. Every estimate is proved in section 2.
  Every constant is enclosed. Nothing rests on a sampled value or an extrapolation.
- **Independence.** The certificate uses no zero of zeta and no form of RH. It is built from the real place, the pole
  and the primes 2 and 3 alone.
- **The margins collapse.** The certified margins are `1.5e-9`, `3.4e-11` and `6.4e-13` at `a = 0.60, 0.65, 0.69`,
  and about `3.6e-15` at `a = 0.75` (upper bound from the trial polynomial). The logarithm of the margin falls faster
  than linearly in `a`. A certificate of this kind therefore needs more precision and a larger basis at every larger
  support, and it cannot carry itself to large supports. Section 5 has the numbers.
- **What it is not.** It is one support (and everything below it), not GRH, and not RH. It says nothing about larger
  supports. Section 7.

---

## 1. The statement

**Conventions** (those of `weil_numerics.py`, checked there against the zeros of zeta to `1e-16`). Let
`f in L^2(-a, a)`, extended by zero. Write `F(r) = int f(x) e^{irx} dx`, `h(t) = int f(y) conj f(y - t) dy`,
`S(t) = h(t) + h(-t) = 2 Re h(t)`, and `c_n = Lambda(n) / sqrt(n)`. Then

    W(f) = POLE + REAL - sum_{n >= 2} c_n S(log n),
    POLE = 2 Re[ F(i/2) conj F(-i/2) ]        (= 2 F(i/2) F(-i/2) for real f),
    REAL = -log(pi) h(0) + (1/2pi) int |F(r)|^2 Re psi(1/4 + ir/2) dr.

`h` vanishes outside `[-2a, 2a]`, so only `n` with `log n < 2a` contribute. For `log 3 < 2a < log 4` these are
`n = 2, 3`; for `log 4 < 2a < log 5` also `n = 4` (prime power of 2, `c_4 = log 2 / 2`). `Re psi` is bounded below,
so `REAL` is well defined in `(-inf, +inf]`; it is finite exactly on the form domain
`D = { f : int |F|^2 log(2 + |r|) dr < inf }`, and outside it `W(f) = +inf`.

**Theorem (one-box certificate).** **[certified]** For `(a, c)` in

| support `a` | `e^{2a}` | primes entering | certified margin `c` | log |
|---|---|---|---|---|
| `3/5` | 3.320 | 2, 3 | `1.500e-9` | `grh_onebox_cert-a0.60.log` |
| **`13/20`** | **3.669** | **2, 3** | **`3.398e-11`** | **`grh_onebox_cert-a0.65.log`** |
| `69/100` | 3.975 | 2, 3 | `6.417e-13` | `grh_onebox_cert-a0.69.log` |

and every `f in L^2(-a, a)`, real or complex:

    W(f) >= c ||f||^2.

**Remarks.**
- *Complex `f`.* The kernel of `W` is real and even, so `W(u + iv) = W(u) + W(v)` for real `u, v` (the cross terms
  are odd in `r`, or purely imaginary). It suffices to treat real `f`, and the script does. **[proved here]**
- *Smaller supports.* `W(f)` does not depend on `a`; the theorem at `a` implies `W(f) >= c ||f||^2` for `f`
  supported in any `[-a', a']` with `a' <= a`. **[proved here]**
- *Why `a = 13/20` is the headline.* It sits in the middle of the window `log 3 < 2a < log 4`: the prime 3 enters
  substantially (its lag overlaps the support over a length `2a - log 3 = 0.20`, against `0.10` at `a = 0.6`), the
  square 4 is still absent, and the margin `3.4e-11` is two orders above the ball radii of the computation, so the
  certificate is not tight against the arithmetic. The run at `69/100` covers the window up to its edge.

---

## 2. The proof, step by step

Notation. `I = (-a, a)`. `p_n(x) = sqrt((2n+1)/(2a)) P_n(x/a)` are the orthonormal Legendre polynomials on `I`,
`Poly_N` their span for `n < N`, `P_N` the orthogonal projection onto it and `Q_N = 1 - P_N`. The runs use
`N = 100`, `D = 40`, `M = N + D + 2 = 142`. "Script [k]" refers to the section of `grh_onebox_cert.py` and the
line `[k]` of its log.

### 2.1 The frequency form and the monotone symbol

**Lemma 1.** **[proved here]** For `f in L^2(I)`,
`W(f) = POLE + (1/2pi) int |F(r)|^2 phi(r) dr` with

    phi(r) = phi_inf(r) - 2 sum_{log n < 2a} c_n cos(r log n),   phi_inf(r) = -log pi + Re psi(1/4 + ir/2).

*Proof.* `h` is the inverse Fourier transform of `|F|^2`, which is in `L^1`, so
`S(t) = (1/pi) int |F|^2 cos(rt) dr` for every `t`, and `h(0) = (1/2pi) int |F|^2`. Insert both into the definition.

**Lemma 2.** **[classical]** `Re psi(1/4 + it) = psi(1/4) + sum_{k >= 0} t^2 / ((k + 1/4)((k + 1/4)^2 + t^2))`. Every
term increases with `|t|`, so `phi_inf` is even and increasing in `|r|`. Consequently, with `C = sum c_n`:

    phi(r) >= phi_inf(rho) - 2C   for |r| >= rho,          phi(r) >= phi_inf(0) - 2C =: -Phi^-   for all r.

(From `psi(z) = -gamma + sum_k [1/(k+1) - 1/(k+z)]`.)

### 2.2 The real place in x-space

**Lemma 3.** **[proved here]** For `f in L^2(I)` (both sides in `(-inf, +inf]`),

    REAL(f) = c0 h(0) + int_0^{2a} (h(0) - Re h(t)) / t dt - int_0^{2a} K(t) S(t) dt,
    c0 = -log pi - gamma - log(4a),     K(t) = e^{-t/2} / (1 - e^{-2t}) - 1/(2t).

*Proof.* `psi(s) = -gamma + int_0^inf (e^{-t} - e^{-st}) / (1 - e^{-t}) dt`. With `s = 1/4 + ir/2` the integrand's
real part is `(e^{-t} - e^{-t/4}) / (1 - e^{-t}) + e^{-t/4}(1 - cos(rt/2)) / (1 - e^{-t})`. The first summand is
absolutely integrable; the second is nonnegative. So Fubini and Tonelli apply after integrating against `|F|^2`, and
`(1/2pi) int |F|^2 (1 - cos(rt/2)) dr = h(0) - Re h(t/2)`. Substitute `t = 2x` and write
`2e^{-x/2}/(1 - e^{-2x}) = 1/x + 2K(x)`, using `Re h(x) = 0` for `x > 2a`. The constant collects to

    lim_{eps -> 0} [ int_eps^inf 2e^{-2x}/(1 - e^{-2x}) dx - int_eps^{2a} dx/x ] = -log(2a) - log 2 = -log(4a).

`K` has removable singularities at `0` and poles at `i pi k`, `k != 0`, so it is analytic on `|t - a| < sqrt(a^2 + pi^2)`.

**Lemma 4 (Taylor remainder of K).** **[proved here + certified]** Let `K_D` be the Taylor polynomial of degree `D`
of `K` at `t = a`. Its coefficients are enclosed by Arb's power-series arithmetic. By Cauchy's estimate on the circle
`|t - a| = R = 2.8`:

    sup_{0 <= t <= 2a} |K - K_D| <= eps_D := M_R (a/R)^{D+1} / (1 - a/R),     M_R = max_{|t-a| = R} |K|.

`M_R` is enclosed by evaluating `K` on 4000 complex boxes covering the circle (script [1]). Values:
`eps_D <= 6.2e-28, 1.6e-26, 1.9e-25` at `a = 0.60, 0.65, 0.69`. Let `W_D` be `W` with `K` replaced by `K_D`. Since
`|S(t)| <= 2 ||f||^2`, we get `|W(f) - W_D(f)| <= 4a eps_D ||f||^2 =: e_K ||f||^2`.

### 2.3 The Gram block (finite part and coupling)

**Computation** (script [2]). **[certified]** With `t = a tau` and `x = a xi`,
`h_ij(a tau) = (sqrt((2i+1)(2j+1))/2) H_ij(tau)` with `H_ij(tau) = int_{tau-1}^{1} P_i(e) P_j(e - tau) de`, a
polynomial in `tau` of degree `<= i + j + 1`. Then, for `i < N` and `j < M`,

    G_ij := W_D(p_i, p_j) = c0 delta_ij + (n_i n_j / 2) int_0^2 [ (Sig_ij(0) - Sig_ij(tau)) / (2 tau)
                            - a K_D(a tau) Sig_ij(tau) ] dtau - sum_n c_n (n_i n_j / 2) Sig_ij(log n / a)
                            + A_i B_j + B_i A_j,

where `Sig = H + H^T`, `n_i = sqrt(2i+1)`, `A_i = int p_i e^{-x/2}`, `B_i = int p_i e^{x/2}`
(`A_i = n_i sqrt(a/2) 2 (-1)^i i_i(a/2)`, `B_i = n_i sqrt(a/2) 2 i_i(a/2)`, with `i_n` from Arb's Bessel `I`). Both quadratures are Gauss-Legendre with nodes and weights
enclosed by Arb (`legendre_p_root`). They are **exact**: `Q_eta = floor((N+M)/2) + 1` nodes integrate the
`e`-integrand of degree `<= N + M - 2`; `Q_tau = floor((N+M+D)/2) + 2` nodes integrate the `tau`-integrand of degree
`<= N + M + D - 1`. So the only error in `G` is the ball radius, `<= 3e-81` (log [2]). The working precision is
`200 + 1.3 M + 64` bits: the radius of the Legendre recurrence in ball arithmetic grows like `2.42^n`, and at 192
bits the radii reached `3.6e-4` before this was fixed.

### 2.4 The operator of W on a polynomial

**Lemma 5.** **[proved here]** For a polynomial `u` of degree `< N` there is `Hu in L^2(I)` with
`W(u, g) = <Hu, g>` for every `g` in the form domain, namely

    Hu(x) = c0 u(x) + int_0^{2a} [u(x) - (u~(x+t) + u~(x-t))/2] / t dt - int_{-a}^{a} K(|x - s|) u(s) ds
            + A_u e^{x/2} + B_u e^{-x/2} - sum_n c_n [u~(x - log n) + u~(x + log n)]

(`u~` = zero extension). Splitting `u~(x+t) = u(x+t) - u(x+t) 1[x+t > a]` and integrating the Taylor expansion:

    Hu = q_u + (u/2) l + k_u + A_u e^{x/2} + B_u e^{-x/2} + j_u,
    l(x) = log(2a/(a - x)) + log(2a/(a + x)),
    j_u(x) = -sum_n c_n [ u(x - log n) 1[x > log n - a] + u(x + log n) 1[x < a - log n] ],

where `q_u` is a polynomial of degree `<= deg u`, and `k_u = -int K(|x-s|) u(s) ds`. With `K_D` in place of `K`,
`k_u^D` is a polynomial of degree `<= deg u + D + 1`: on each side of `s = x` the kernel is a polynomial in `x - s`.
So for `M >= N + D + 1`:

    Q_M H_D u = Q_M[(u/2) l + j_u] + A_u Q_M e^{x/2} + B_u Q_M e^{-x/2}.

*Proof of `W(u, g) = <Hu, g>`.* Polarise Lemma 3 for `u` and `g in D`. The only non-absolutely-convergent piece is
`int_0^{2a} (1/t) int [u(y) - u~(y+t)] g(y) dy dt` near `y + t = a`. There the bound
`int |u g|(y) log(2a/(a-y)) dy < inf` (Cauchy-Schwarz, `log in L^2`) gives absolute convergence, so Fubini applies.

**Check** (script [4c]). **[certified]** The identity says that for `m >= N + D + 1` the Gram entries
`G_im = <H_D p_i, p_m>` equal the projections of the singular part plus the pole part, computed by the completely
different route of 2.5. Column `m = M - 1` agrees for all 100 rows to `9e-133` in each of the three runs. This is the strongest internal test of the whole construction: it ties the quadrature of 2.3 to the
closed forms of 2.5.

### 2.5 The residual: coupling block and singular tails

Let `r(u) = ||Q_N H u||`. Then, with all inequalities **[proved here]** and all matrices **[certified]**:

1. `||Q_N H u|| <= ||Q_N H_D u|| + 2a eps_D ||u||`. The operator `H - H_D` has kernel `-(K - K_D)(|x-s|)`, of
   Hilbert-Schmidt norm `<= 2a eps_D`.
2. `||Q_N H_D u||^2 = ||(P_M - P_N) H_D u||^2 + ||Q_M H_D u||^2`, and the first term is `u^T R_M u` with
   `R_M = C C^T`, `C = (G_im)_{i < N <= m < M}` (script [3]).
3. `||Q_M H_D u|| <= ||Q_M[(u/2) l + j_u]|| + delta_p ||u||` with
   `delta_p = ||Q_M e^{+-x/2}|| (||e^{x/2}|| + ||e^{-x/2}||)`, `||e^{+-x/2}|| = sqrt(2 sinh a)`, and
   `||Q_M e^{+-x/2}||^2 = 2a sum_{n >= M} (2n+1) i_n(a/2)^2 <= 2a (2M+1) t_M^2 / (1 - (a/(2(2M+1)))^2)`,
   `t_M = (a/2)^M cosh(a/2) / (2M+1)!!`, from `0 <= i_n(z) <= z^n cosh z / (2n+1)!!` (Poisson integral). This is
   `< 1e-360` (script [4d]).
4. `||Q_M[(u/2) l + j_u]||^2 <= 3 u^T (T_L + T_R + T_J) u` (`||a+b+c||^2 <= 3 sum ||.||^2`), where `T_X` is the Gram
   matrix of `Q_M` applied to the piece `X`, computed as `Gram - Proj Proj^T` (script [4a], [4b]):
   - `T_L`: piece `(p_i/2) log(2a/(a-x))`. With `w = (a-x)/(2a)`, `P_n(1 - 2w) = sum_k binom(n,k) binom(n+k,k)
     (-w)^k` (integer coefficients) and `int_0^1 w^k log(1/w) dw = 1/(k+1)^2`,
     `int_0^1 w^k log^2(1/w) dw = 2/(k+1)^3`. So Gram and projections are exact rationals, evaluated at
     `5.3 M + 400` bits.
   - `T_R`: the mirror piece; `T_R = diag((-1)^i) T_L diag((-1)^i)` by `x -> -x`.
   - `T_J`: the jump piece `j_u`, a polynomial on each of the 5 sub-intervals cut by `+-(a - log 2)`,
     `+-(a - log 3)`; exact Gauss-Legendre on each.
5. Together: `r(u) <= sqrt(u^T Rt u) + delta ||u||` with `Rt = R_M + 3T`, `delta = 2a eps_D + delta_p` (Minkowski in
   the plane). Hence `r(u)^2 <= (1+beta) u^T Rt u + (1 + 1/beta) delta^2 ||u||^2` for any `beta > 0`; the script uses
   `beta = 1e-6`.

### 2.6 The bound mu on the complement

**Lemma 6.** **[proved here + certified]** For `g` orthogonal to `Poly_N` (in the form domain),

    W(g) >= mu ||g||^2,    mu = phi_min (1 - eta) - Phi^- eta - 2 eps_N^2,

with `phi_min = phi_inf(rho) - 2C > 0` (Lemma 2), `Phi^- = 2C - phi_inf(0)`,

    eta  = (2a/pi) rho sum_{n >= N} (a rho)^{2n} / ((2n+1)!!)^2   (bounded by its first term / (1 - (a rho/(2N+3))^2)),
    eps_N^2 = 2a sum_{n >= N} (2n+1) i_n(a/2)^2                    (bounded as in 2.5 item 3).

*Proof.* `G(r) = <g, e^{-irx}> = <g, Q_N e^{-irx}>`, so `|G(r)| <= ||g|| eps_N(r)` with
`eps_N(r)^2 = ||Q_N e^{irx}||^2 = 2a sum_{n >= N} (2n+1) j_n(ar)^2`, because `<e^{irx}, p_n>` is
`sqrt((2n+1)/(2a)) 2a i^n j_n(ar)`. The Poisson integral gives `|j_n(z)| <= z^n / (2n+1)!!` for real `z`, so
`(1/2pi) int_{|r|<rho} |G|^2 <= eta ||g||^2` (integrate the bound termwise). With Lemma 1:
`(1/2pi) int |G|^2 phi >= phi_min (1/2pi) int_{|r|>rho} |G|^2 - Phi^- (1/2pi) int_{|r|<rho} |G|^2
>= (phi_min (1 - eta) - Phi^- eta) ||g||^2` by Plancherel. And `POLE(g) = 2 Re(A_g conj B_g) >= -2 eps_N^2 ||g||^2`,
since `A_g = <g, Q_N e^{-x/2}>`, and likewise for `B_g`. `rho` is chosen on a grid to maximise `mu` (script [5]):
`rho = 123, 113, 107` and `mu >= 0.7151, 0.6367, 0.5751`. `phi_inf(rho)` is Arb's digamma.

### 2.7 Assembly

**Lemma 7.** **[proved here]** Write `f = u + g` with `u = P_N f`. Then `W(f) = W(u) + 2<Q_N H u, g> + W(g)` (Lemma 5,
`g` orthogonal to `Poly_N`), so for `0 <= c < mu`:

    W(f) - c||f||^2 >= W(u) - c||u||^2 - 2 r(u) ||g|| + (mu - c)||g||^2 >= W(u) - c||u||^2 - r(u)^2/(mu - c)
                    >= u^T [ G - (c + e_K) I - ((1+beta) Rt + (1+1/beta) delta^2 I) / (mu - c) ] u.

The last matrix (`N x N`, Legendre coefficients of `u`, `||u||^2 = u^T u`) is factored as `L D L^T` in ball
arithmetic with every pivot certified `> 0` (script [6]). The ball result covers every exact matrix inside the
balls, so the exact matrix is positive semidefinite and `W(f) >= c ||f||^2`. **[certified]** The largest `c` with a
successful factorisation is found by bisection in `log c`; the logs report the certified one.

**Upper bound** (script [7]). **[certified]** An approximate lowest eigenvector `u` of `G` (inverse iteration on
midpoints) is fixed, and `u^T G u / u^T u + e_K` is evaluated in ball arithmetic. Since `W(u) <= u^T G u + e_K ||u||^2`,
this bounds `inf W(f)/||f||^2` from above.

**What is analytic and what is numerical.**

| ingredient | analytic (proved in this note) | enclosed numerically (script section) |
|---|---|---|
| frequency form, monotone `phi_inf` | Lemmas 1, 2 | `phi_inf(rho)`, `phi_inf(0)` [5] |
| x-space form of the real place | Lemma 3 | `c0`, `c_n` [header] |
| `K -> K_D` | Lemma 4 (Cauchy) | Taylor coefficients, `M_R` [1] |
| Gram block `G`, coupling `C` | exactness of Gauss | all entries [2], `R_M` [3] |
| structure of `H u` | Lemma 5 | consistency check [4c] |
| singular tails | 2.5 items 1-5 | `T_L` (exact rationals) [4a], `T_J` [4b], `delta` [4d] |
| complement bound `mu` | Lemma 6 (Poisson-integral bounds) | `eta`, `eps_N`, `mu` [5] |
| assembly | Lemma 7 | LDL^T with all pivots `> 0` [6] |

---

## 3. The certified numbers

All with `N = 100`, `D = 40`, `M = 142`; about 50 s CPU per support. A re-run at `a = 0.65` reproduced the log
identically apart from the timings.

| `a` | `e_K = 4a eps_D` | `delta` | `rho` | `eta` | `mu >=` | certified `c` | upper bound (trial polynomial) | `c / upper` |
|---|---|---|---|---|---|---|---|---|
| 3/5 | `1.5e-27` | `7.4e-28` | 123 | `1.2e-3` | 0.715195 | `1.500e-9` | `1.6077e-9` | 0.93 |
| 13/20 | `4.3e-26` | `2.1e-26` | 113 | `4.7e-4` | 0.636772 | `3.398e-11` | `3.9604e-11` | 0.86 |
| 69/100 | `5.2e-25` | `2.6e-25` | 107 | `1.3e-3` | 0.575148 | `6.417e-13` | `1.0097e-12` | 0.64 |

So the smallest value of `W(f)/||f||^2` over `L^2(-a, a)` lies in `[1.500e-9, 1.608e-9]`,
`[3.398e-11, 3.961e-11]` and `[6.417e-13, 1.010e-12]` respectively. **[certified]**

Comparison with `SEMILOCAL.md` **[numerical]**: its table uses the smaller basis `(1 - t^2)^2 P_j`, `j < 10`. That
basis forces `f` to vanish at the ends, so its values are higher (at `a = 0.55`: `3.7e-7` there against `5.3e-8` on
all polynomials of degree below 40, in a floating-point check). The full polynomial space is the right one here: the
near-minimisers do not vanish at the ends.

---

## 4. Checks and negative controls

- **Conventions** [8] **[numerical]**: `G_00`, `G_11`, `G_44` and `G_00 + 2G_02 + G_22` were recomputed from the
  frequency-side definition of `weil_numerics.py` (scipy quadrature to `r = 12000` plus the averaged `1/r^2` tail).
  They agree to `2e-7` at all three supports.
- **Symmetry** [2]: `|G_ij - G_ji| <= 8e-97`. Both triangles come from different quadrature terms.
- **Structure** [4c]: as in 2.4.
- **Negative control, small basis**: at `a = 0.6` with `N = 64`, `mu` is only `0.27`, and the factorisation fails at
  every `c >= 1e-40`. The test can fail; it does not pass by construction.
- **Negative control, larger support** (`grh_onebox_cert-a0.75-fail.log`, `grh_onebox_cert_diag-a0.75.log`): at
  `a = 3/4` (square 4 now enters), with `N = 180` (`mu = 0.39`), the certificate fails. The diagnostic shows why:
  `lambda_min` of `G`, `G - R/mu` and `G - (R + T)/mu` are all positive (`3.64e-15, 3.56e-15, 3.34e-15`), but
  `G - (R + 3T)/mu` has `lambda_min = -3.1`. The factor 3 from combining the three singular pieces by the triangle
  inequality (2.5 item 4) overwhelms the high-degree directions when `mu` is small. This is a weakness of the bound,
  not a sign problem: computing the joint Gram of the pieces exactly, with the cross terms, would remove the factor.
  That is the next step for `a` between `log 4 / 2` and `log 5 / 2` (section 6). The run at `a = 4/5`, `N = 220`
  (`mu = 0.52`) failed the same way (not kept as a log).

---

## 5. The shape of the margins

| `a` | 0.60 | 0.65 | 0.69 | 0.75 |
|---|---|---|---|---|
| smallest `W/||f||^2` (upper bound) | `1.61e-9` | `3.96e-11` | `1.01e-12` | `3.6e-15` (midpoint, diag) |
| `log10` | -8.79 | -10.40 | -12.00 | -14.44 |
| drop per 0.01 in `a` | | 0.32 | 0.40 | 0.41 |

The drop per unit of support grows, so the margin falls faster than exponentially in `a` over this range **[certified
values, numerical slope]**. This is the collapse that `SEMILOCAL.md` section 0 describes ("super-exponentially
collapsing margin") and that `INDUCTION.md` section 1 shows to be at least exponential. The reason is concentration:
a function of support `2a` can be made small at all frequencies above the first zero's height except in a band whose
weight decays like a prolate eigenvalue.

**What this means for certificates.** A finite certificate of this kind must resolve the margin. That needs the Gram
matrix to absolute accuracy far below `c(a)`, a basis large enough that `mu` is a fixed fraction above the margin's
needs, and losses in the coupling (`c / upper` falls from 0.93 to 0.64 between `a = 0.60` and `0.69`) that stay below
the margin. The precision can be bought, since the cost in bits grows like `-log c(a)`. But the losses are
structural, and the margin falls faster than any fixed loss ratio can be kept. So the computation certifies
individual supports one at a time and **cannot carry itself to large supports**. The step from one support to the next
has to come from a statement that is multiplicative in the margin (the structure `INDUCTION.md` asks for), not from
running the certificate at a larger `a`.

---

## 6. Lean

`ProofPhase/GRH/OneBoxCert.lean` **[Lean]**, built with `sync-build.sh ProofPhase.GRH.OneBoxCert`. Audit in
`grhonebox-axioms.log`: 10 declarations, each depending only on `propext`, `Classical.choice` and `Quot.sound`;
no `sorry`, `admit`, `native_decide` or `axiom`.

- `schur_scalar`: `c nu^2 + r^2/(mu - c) <= Wu`, `mu ng^2 <= Wg` and `|B| <= r ng` give
  `c(nu^2 + ng^2) <= Wu + 2B + Wg` (Lemma 7, scalar form).
- `schur_sign`: the strict sign, proved through `ProofPhase.Unified.sign_transport` (part (c) of the transport
  theorem). The uncoupled value `Wu + Wg` is the margin, the cross term `2B` the uncertainty.
- `onebox_positive`, `onebox_sign`: on a real inner product space with a symmetric bilinear `W` and a subspace `S`
  with orthogonal projection, the three inputs (finite part, cross term, tail) give `W f f >= c ||f||^2` for every
  `f`, and `> 0` for `f != 0`.
- `ldl_nonneg`, `fin_of_ldl`: a factorisation `G - cI - R/(mu - c) = L D L^T` with `D >= 0`, for the Gram matrix of
  `W` in an orthonormal basis and a residual matrix `R` bounding `rho^2`, gives the finite-part input.
- `OneBoxEnclosures S W rho c mu`: the enclosures as named hypotheses. `onebox_cert_13_20`, `onebox_cert_3_5` and
  `onebox_cert_69_100` instantiate them with the exact values `(c, mu) = (3398e-14, 0.6367)`, `(15e-10, 0.7151)` and
  `(6417e-16, 0.5751)`.

What Lean proves is the implication: from the enclosures to positivity. It does not define Weil's form, the digamma
integral or the Legendre basis, and it computes none of the enclosures. Those are the script's (sections 2 and 3).

---

## 7. What is and is not certified

**Certified:**
- `W(f) >= c ||f||^2` for every `f in L^2(-a, a)`, real or complex, at `a = 3/5, 13/20, 69/100` with the margins of
  section 3. Hence also for every smaller support.
- Two-sided enclosures of the smallest value of `W/||f||^2` at these three supports.
- The abstract implication (Lean), with the numbers as named hypotheses.

**Not certified, and not claimed:**
- Nothing about supports with `e^{2a} > 3.975`, in particular not the part of the 2-and-3 window with
  `log 4 < 2a < log 5`. The attempts at `a = 0.75` and `0.80` failed for the reason given in section 4.
- Nothing about GRH, RH, other L-functions or large supports. This is a statement about one bounded support of one
  form. Under RH, which others prove externally (`GRH-TIE-IN.md`), the same positivity follows at every support. The
  certificate does not use that and does not add to it.
- The steps marked [classical] (the series of `psi` and its integral representation, the Poisson integrals of the
  spherical Bessel functions, Gauss-Legendre exactness, Cauchy's estimate) are used as textbook facts and are not
  formalised.
- The correctness of python-flint / Arb itself is trusted, as for any computer-assisted proof of this kind.

---

## 8. Files and reproduction

- `grh_onebox_cert.py`: the certificate. `py docs/unified/grh_onebox_cert.py 13/20 100 40` (about 50 s). Arguments
  `A N D [rho|auto] [c] [dump.json]`.
- `grh_onebox_cert-a0.60.log`, `-a0.65.log`, `-a0.69.log`: the certified runs.
- `grh_onebox_cert-a0.75-fail.log`, `grh_onebox_cert_diag.py`, `grh_onebox_cert_diag-a0.75.log`: the failing run at
  `a = 3/4` and its diagnosis (not part of the proof).
- `ProofPhase/GRH/OneBoxCert.lean`, `grhonebox-axioms.sh`, `grhonebox-axioms.log`.

## 9. Next steps (not done here)

1. Replace the factor 3 in 2.5 item 4 by the exact joint Gram of the three singular pieces (cross terms log x log and
   log x jump, by the same moment formulas on sub-intervals). By the diagnostic, this should certify `a = 3/4`, and
   probably the window up to `log 5 / 2`, with `N` about 180 to 220.
2. Replace the crude `phi >= phi_inf - 2C` by an enclosed minimum of `phi` on `[rho, R]`. This raises `mu`.
