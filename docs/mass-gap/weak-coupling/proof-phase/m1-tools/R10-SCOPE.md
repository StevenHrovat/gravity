# Step 3 (E8) and R10 scoped: analytic observables, and why the interface over-asks (m1-tools, 2026-11-22)

Brief (coordinator):
1. Step 3, the insertion of the footprint-weighted lifetime into [V] (1.80)-(1.85), line by line.
2. A bounded scoping round on R10: does an approximation route avoid the analyticity obstacle (prove transfer and
   decay for analytic observables, extend by `L²` approximation)? What does it give: same rate with an
   observable-dependent prefactor, a slower rate, nothing uniform? Is that enough for the main theorem: do `MassGapLoc`,
   `TorusDecayLoc` and the interface need constants uniform over all observables, or only per pair?

Read for this note: [V] pp. 383-386 ((1.79)-(1.85)); `formal/ProofPhase/Objects.lean` (`MassGapLoc`, `LimitRP`),
`Torus/Local.lean` (`TorusDecayLoc`), `V3/W1Route.lean` (`ObsTransferPhysTW`). Claim marks as in `NOTE.md`.

## 0. Result in plain words

1. **Step 3 closes, and no insertion is needed: I had misread (1.80).** Balaban's factor `exp(-κ_j(Z))` controls
   `K ≤ n0 - j + R_j` steps. Here `n0` is the last step at which the iterated region `S^{n-j}(Z)` still has non-zero
   linear size; it grows with the size of `Z` and is **not** bounded by `R_j`. The cost (1.81) is the sum of the current
   sizes, `Σ_n O(1) M^d R_n^{d+1} d'_n(S^{n-j}(Z))`, with `d'_n ≤ L^{-(n-j)/2} d'_j(Z)` ([I] (6.31)), i.e. geometric,
   plus `R_j` steps at bounded size. That **is** the footprint-weighted lifetime of `R2-REPAIR.md`. A conserved-flux
   sheet is carried inside `S^{n-j}(Z)` while it is larger than a cube; it becomes small at `n0`; its few-cube phase
   (`≤ log_L(C M R) + 0.4 log g^{-2}`) ends within the remaining `R_j` steps. `REGULAR.md` 0.4 ("lifetime `≤ R_j`") was
   wrong. The E8 row closes **as written in [V]**, with `R2-REPAIR.md`'s footprint lemma as an independent check.
2. **R10 for analytic observables: paper sketch, Balaban's own machinery, no frozen region.** For `F` a polynomial of
   degree `≤ n` in the matrix entries (characters) of the variables in a bounded region, `e^{tF}` is entire. For
   `|t| ≤ t_0(n, N)` it is a small local analytic term that fits Balaban's E-term bounds at the scale where it is
   inserted (`N` the number of variables). Running the induction with it, the `t`-dependent part of the effective action
   at `L_*` is a sum of terms localised near `supp F`, with decay `e^{-κ d}` ([III] (2.26)-(2.33)). A Cauchy estimate in
   `t` gives `E[F | V_K]` and the conditional covariances with the **same decay rate `m`** and a prefactor `C(n, N)`
   that depends on the observable. No frozen region and no new estimate is needed.
3. **Bounded measurable observables by approximation alone: nothing uniform.** For fixed `F`, Peter-Weyl / Fejér
   approximants `F_n` (`‖F_n‖_∞ ≤ ‖F‖_∞`) converge in `L²(μ)`. With
   `|Cov(F, G) - Cov(F_n, G_n)| ≤ 2‖F - F_n‖_{L²}‖G‖_∞ + 2‖G - G_n‖_{L²}‖F‖_∞`, `Cov(F, G) → 0`, but at a rate set by
   how fast `F` is approximated, which can be arbitrarily slow. No uniform exponential bound comes out of this route.
4. **But the mass-gap statement does not need it: reflection positivity upgrades.**
   * `MassGapLoc` (`Objects.lean` 478) has prefactor 2 and one rate for all bounded families. That is exactly what the
     spectral theorem gives once there is a gap. With RP, the reflected forms are `⟨F, T^n F⟩` for a positive
     self-adjoint contraction `T` (the transfer matrix) on the OS Hilbert space. If, for a **dense** set of `F`,
     `|⟨F, T^n F⟩ - |⟨Ω, F⟩|²| ≤ C_F e^{-m n}` with **one** `m` and **any** `C_F`, then the spectral measure of every
     such `F` on `Ω^⊥` lives on `[0, e^{-m}]`. By density the spectrum of `T` on `Ω^⊥` lies in `[0, e^{-m}]`, so
     `|⟨F, T^n F⟩ - |⟨Ω, F⟩|²| ≤ ‖F‖² e^{-m n}` for **every** `F`.
   * Character polynomials of the links of the positive half are dense (Peter-Weyl on finitely many links, then local
     functions are dense).
   * RP of the bare measure is proved (`rp_gaugeMeasure`, `LimitRP`). So `TorusDecayLoc` (at every level, `C = 2`) and
     `MassGapLoc` follow from decay at rate `m` on the analytic dense class, with **observable-dependent** constants.
5. **So the interface over-asks.** `ObsTransferPhysTW` (and through it `TorusDecayLoc` in the blocked route) asks for
   constants `c, K` uniform over **all** bounded measurable observables of extent `≤ R`. The main theorem needs only:
   * a rate `m` uniform over a dense class, with constants per observable;
   * the spectral upgrade by reflection positivity of the bare measure.
   
   **Proposed interface change** (for the coordinator, not M1):
   * `ObsTransferPhysTW_dense`: the same statement for `F, G` in the class of character polynomials of bounded degree on
     a bounded set of variables, with `c = c(F, G)` and one `m`;
   * a lemma `spectral_upgrade`: RP plus dense-class decay at rate `m` implies uniform decay `‖F‖² e^{-m n}`. This is a
     clean Lean target: a finite-lattice transfer matrix from `rp_gaugeMeasure`, plus the spectral theorem for a
     positive contraction.
6. **Status.**
   * Step 3: **closed** (as written in [V]; no change).
   * R10: **paper sketch for the analytic dense class** (one extra local analytic term in Balaban's induction plus
     Cauchy in `t`), **enough for the main theorem** given the interface change and the spectral upgrade (which uses
     only RP of the bare measure, already proved).
   * The uniform-over-measurable form the current interface asks for is **not needed**, and is not proved.

## 1. Step 3, line by line against [V] pp. 383-386

* **(1.79):** the bound of `T'_k(X)1` by `exp(-Σ κ-type factors)`, holding "for all large field regions".
* **The statement (1.80):** the factor `exp(-κ_j(Z))` controls `K` steps without new large fields, where `K` is the
  least integer with `S^K(Z)` satisfying (i), (ii) (small, aged `N = R_j`); `κ_j(Z) ≥ Σ_{n=j}^{j+K} O(1) M^d
  R_n^{d+1} d'_n(S^{n-j}(Z))`.
* **(1.81)**, Balaban's proof: `d'_n(S^{n-j}(Z)) ≤ 2^{-(n-j)} d'_j(Z)` (via [I] (6.31)); `n0` is the last `n` with
  `d'_n > 0`; then `K ≤ n0 - j + R_j`, and the sum is `≤ O(1) M^d L^{d+1} R_j^{d+2} (d'_j(Z) + 1)`. The bound does not
  depend on `n0 - j`: the geometric part sums to a multiple of `d'_j`.
* **A carried sheet:** its irregular set at scale `n` lies in the cover of its physical support, which lies in
  `S^{n-j}(Z)` (cover plus 10 layers). No large fields arise outside `S^{n-j}(Z)` because of it, so it is in Balaban's
  "no new large fields" case.
* **(1.83):** the per-step update `κ_{j+1}(S(Z_0)) = κ_j(Z_0) - O(1) M^d R^{d+1} d'_{j+1}(S(Z_0))` applies step by step.
* **(1.84)-(1.85):** cover the merging with new regions, unchanged.
* **At `n0 + 1`:** the region is small. The sheet is then in its few-cube phase, which ends (localised, then R1)
  within `≤ log_L(C M R) + 0.4 log g^{-2} ≤ R_j` steps, so the next field is regular when (ii) is reached. The region is
  renormalised by the conditional step (E9 at regular `W`).
* **Laws:** while `W` is irregular the region is left as it is (branch of `NOTE.md` 3); (1.79) still bounds it.

## 2. R10 for analytic observables (sketch)

* **Class:** `F = P(U_b, b ∈ A)` with `P` a polynomial of degree `≤ n` in the matrix entries, `A` a set of `N`
  variables (fine links, or block variables at a fixed physical scale), `|F| ≤ 1` on real configurations.
* **Insertion:** replace the density by `e^{tF}` times it. On the complex neighbourhood of radius `r` of Balaban's
  analyticity domains, `|F| ≤ e^{C n N r}`, so for `|t| ≤ t_0 = c e^{-C n N r}` the term `tF` satisfies the E-term
  bounds ([I] (1.18)) at its scale and is carried by the induction like any local term.
* **Output:** `log Z(t)` and the effective action at `L_*` are analytic in `t` for `|t| ≤ t_0`. The `t`-dependent part
  is a sum of localised terms over domains meeting `A`, each `≤ e^{-κ d(X)}`.
* **(i)** `E[F | V_K] = ∂_t A_K^{(t)}|_{t=0}(V_K)` (Cauchy, constant `1/t_0`), which depends on `V_K` near `A` up to
  `e^{-κ D}`.
* **(ii)** The conditional covariance is `∂_s ∂_t` with two insertions: only domains meeting both supports contribute,
  `≤ C t_0^{-1} s_0^{-1} e^{-κ D}`.
* **Rate:** `κ` in scale-`j` units at each scale `j < K`, hence physical `m ~ κ/L_*`, independent of `F`.
* **Constants:** `C(n, N) ~ e^{2C n N r}`, which depend on the observable. **Not written out:** the bookkeeping of the
  inserted term through all steps. It is the same as for any local E-term, so no new estimate, but it is not checked
  line by line.

## 3. The upgrade by reflection positivity

On a finite lattice (each level `k`, volume `j`), RP in the time direction (`rp_gaugeMeasure`) gives the
Osterwalder-Seiler transfer matrix `T`, a positive self-adjoint contraction on the Hilbert space of gauge-invariant
square-integrable functions of the positive half, with `wcorr(F, n) = ⟨F, T^n F⟩ - |⟨Ω, F⟩|²`.
* **Spectral measures:** for `F` in a dense class `D` with `|wcorr(F, n)| ≤ C_F e^{-m n a_k}` for all `n`, the spectral
  measure `μ_F` restricted to `Ω^⊥` satisfies `∫ λ^n dμ_F ≤ C_F e^{-m n a_k}` for all `n`, so `supp μ_F ⊂ [0, e^{-m a_k}]`.
* **Density:** `D` dense in `Ω^⊥` gives `spec(T|_{Ω^⊥}) ⊂ [0, e^{-m a_k}]`.
* **Conclusion:** `|wcorr(F, n)| ≤ ‖F‖² e^{-m n a_k} ≤ e^{-m n a_k}` for all `|F| ≤ 1`. This is `TorusDecayLoc` with
  `C = 1` at each level, the rate `m` coming only from the dense class.
* `MassGapLoc` follows through the existing limit arguments (limit points of uniformly bounded sequences).

**Caveat:** the dense class must give the rate at **every** level `k ≥ k_0`, which it does: Balaban's rate is uniform in
`k`, and the constants may depend on `k` and `F`, because the upgrade happens level by level.

**Second caveat (periodic time):** on a torus of time length `N`, correlations are
`tr(T^{N-n} F T^n F)/tr(T^N)`, not `⟨F, T^n F⟩`. The upgrade still works, but through the transfer matrix's spectral
decomposition with two-sided weights `(λ_i/λ_0)^n (λ_j/λ_0)^{N-n}`: dense-class decay for `n ≤ N/2` forces
`λ_1/λ_0 ≤ e^{-m a_k}` and hence the uniform bound up to the finite-volume terms. These are the same terms the
existing torus statements (`2n + 2·thick + 2 ≤ side`) already accommodate. The Lean target `spectral_upgrade` should be
stated in this torus form.

**Update (REVIEW-2 G4):**
* The upgrade of sections 0.4 and 3 on finite tori is withdrawn. With per-observable constants and `n ≤ N/2` it has no content.
* The upgrade must be done in the infinite-volume/continuum limit (`LimitRP`), targeting `MassGapLoc`, not `TorusDecayLoc`.
* The dense class must consist of character polynomials of block variables at a fixed physical scale (constants uniform in the spacing), not of fine links.
* See `REVIEW2-RESPONSE.md` 5.

**Update (REVIEW-2 follow-up N-2):** density of the block-observable class holds in the OS norm, not via martingale convergence in `L²` (`REVIEW3-RESPONSE.md` 8).
