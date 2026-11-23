# Every SU(N), with the primes as the base

2026-11-23. Lean: `docs/mass-gap/formal/ProofPhase/General/SUNTwist*.lean` (6 modules, 169 declarations, standard axioms
only, `sunprimes-axioms.log`). CPU check: `sun_primes_check.py`, `.log`. Background: the owner's readings in
`mass-gap/weak-coupling/PREP.md` (the last entries: the SU(N) tunnelling identity, "SU(5) and SU(11) are the known
working candidates", "from two towards three through all prime numbers as the base N of existence"), `GRH-LENS.md`
sections 6 and 9, `ENCODER.md`, `zn_tunnel_check.py`.

**Status marks.** **[Lean]** = proved in Lean, standard axioms only (`propext`, `Classical.choice`, `Quot.sound`);
**[classical]** = known mathematics, recalled; **[numerical]** = checked by computation, which can refute or guide but
never establish; **[reading]** = interpretation (the owner's or the coordinator's), not a theorem; **[open]** = not proved
by anyone. Nothing marked [open] is used as proved.

---

## 1. In plain words

**What was known.** For SU(2) the twisted box was strictly between nothing and everything: with the centre twist
`-1` through one plane, `0 < Z_tw < Z` on every finite lattice, at every coupling `beta != 0` (`su2_Ztw_lt_Z`). The
electric weight `Z - Z_tw` was a reflection-positivity norm, the half-turn of the sphere.

**What is new.** The same now holds for **every SU(N)** and **every centre element** `omega^k = e^{2 pi i k/N}`:

* **The strict twist bound.** For the SU(N) Wilson action, every `beta != 0`, every `k != 0`, every box size, every even
  time extent, every background: `0 < Z_tw,k < Z`, and `Z_tw,k = Z_tw,N-k` [Lean]. So the twist ratio
  `c_k = Z_tw,k / Z` lies strictly between 0 and 1 for every nontrivial centre element of every SU(N).
* **Why it needed a new idea.** The SU(2) proof used that the twist undoes itself (`-1` squared is `1`). For `N >= 3`
  the twist by `omega` is undone only by `omega^-1`. The proof now pairs each twist with its inverse: the time
  reflection turns a twist into its inverse, so the twisted box and the inverse-twisted box have the same weight, and
  `2 (Z - Z_tw,k)` is still a squared length [Lean]. Strictness comes, as for SU(2), from one transfer step of the
  Polyakov line, now with Schur's lemma on SU(N) [Lean].
* **The electric sectors are lengths too.** The electric sectors are the Fourier transform of the twisted boxes,
  `Z_e = (1/N) sum_k omega^{-ek} Z_tw,k`. Each one is a squared length in the reflection geometry, so `Z_e >= 0` for
  every `N`, every `e`, every `beta` [Lean]. The brief expected this to need the transfer-matrix reading and allowed a
  named hypothesis; it does not: reflection positivity alone proves it. They are real, `Z_e = Z_{N-e}`, they add up to
  `Z`, and for `beta != 0` some sector `e != 0` carries a strictly positive weight [Lean].
* **The duality.** The Fourier matrix `F` is unitary, `F^2` is charge conjugation `k -> -k`, and `F^4 = 1` [Lean].
  For SU(2), conjugation is trivial and `F` is a half-turn; for every `N >= 3`, `F^2 != 1` and `F` is a quarter-turn
  [Lean]. SU(2)'s duality is its own inverse because SU(2) is self-dual (pseudo-real); SU(3) and beyond need two
  applications to reach conjugation [classical].
* **The primes as the base.** The centre of SU(N) is built from prime powers (Chinese remainder theorem), and its Fourier
  kernel splits the same way [Lean]. For prime `N`, every nontrivial sector generates the whole centre, and the sector
  symmetries `k -> m k` act transitively on the nontrivial sectors [Lean]; for composite `N` some nontrivial sector
  lives in a smaller centre [Lean]. The sector symmetries form the group whose characters are Dirichlet's characters,
  and the electric transform carries each primitive Dirichlet character to its inverse times its Gauss sum [Lean, from
  Mathlib]. For prime `N` every nontrivial character is primitive [Lean].
* **The owner's candidates.** SU(2), SU(3), SU(5), SU(11) are instantiated one by one (all four `N` are prime) [Lean];
  every `N` in between is covered by the general theorems, and `N = 4, 6, 8, 9, 10` are checked to have a sub-centre
  [Lean].

**What it does not do.** Every strict inequality here holds on each finite lattice, with no control of its size. It
gives no lower bound on `Z - Z_tw,k` uniform in the volume, so no flux free energy, no confinement and no mass gap.
**O1** (the uniform one-box bound, `Z_tw / Z >= 0.743` for every outside) stays **open**, now as one condition per
nontrivial sector. **GRH beyond Dirichlet** stays **open**: the Dirichlet characters enter here only as the characters of
the sector-symmetry group, and nothing here uses or proves a statement about zeros.

---

## 2. The twist bound for every SU(N)

### 2.1 The general chain (any compact group, any twist with an inverse) — `SUNTwist.lean`

The time chain of `Flip/Bound` (`T` even, positive weights). A twist `g` of one slice need not be involutive; it needs a
right inverse `h` (`g (h x) = x`), both measure preserving and leaving the slice weight invariant.

| statement | Lean name | status |
|---|---|---|
| `∫ A · (A∘σ_g∘Θ) · B = Z_tw(h)`: the reflected pairing is the inverse twist | `integral_cross_eq` | [Lean] |
| `Z_tw(g) = Z_tw(h)` (symmetry of the reflection form) | `cZtw_eq_inv` | [Lean] |
| `2 Z - Z_tw(g) - Z_tw(h) = ⟨A∘σ - A, A∘σ - A⟩`; hence `2 (Z - Z_tw(g)) = ⟨A∘σ - A, A∘σ - A⟩` (the unitary form `Z - Re⟨A, A∘σ⟩ = ½‖A∘σ - A‖²` of the brief) | `cZ2_sub_eq`, `cZ_sub_cZtw_eq_u` | [Lean] |
| `Z_tw(g) ≤ Z` | `cZtw_le_cZ_u` | [Lean] |
| strict from one boundary moment (Cauchy-Schwarz) | `cZtw_lt_cZ_of_moment_u` | [Lean] |
| the boundary moment of `φ(a₀) χ(a_{T/2})` is `⟨φ∘h - φ, 𝒦^{T/2} χ⟩_V` | `moment_u` | [Lean] |
| strict from one transfer step: `⟨φ∘h - φ, 𝒦 χ⟩_V ≠ 0` implies `Z_tw(g) < Z` for every even `T` ("charge 1 under `Z_N`" replaces "odd under `Z_2`"; descent for any sector predicate) | `cZtw_lt_cZ_of_step_u`, `secVanish_descend` | [Lean] |
| a `Z_N` family of twists (`g_k g_l = g_{k+l}`): `∫ A(σ_k U) A(σ_l Θ U) B = Z_{k-l}`; the matrix `Z_{k-l}` is positive semidefinite | `ZFam.integral_pair_eq`, `ZFam.form_sum_nonneg` | [Lean] |
| **electric sectors are norms**: `N · Re 𝓕Z(e) = ⟨f_re, f_re⟩ + ⟨f_im, f_im⟩ ≥ 0`, `f = Σ_k ω^{-ke} A∘σ_k` | `ZFam.elec_nonneg` | [Lean] |
| `Z_{-k} = Z_k`, `Z_k ≤ Z`, `Z_0 = Z` | `ZFam.Zk_neg`, `ZFam.Zk_le`, `ZFam.Zk_zero` | [Lean] |

### 2.2 Schur's lemma on SU(N) — `SUNTwistSchur.lean`

| statement | Lean name | status |
|---|---|---|
| `∫ e^{β Re tr v} Re tr(v M) dv = λ_N(β) Re tr M` for every `M` (Haar measure, every `N`) | `schur_SUN`, `integral_bwN_tr_mul` | [Lean] |
| off-diagonal entries of `S = ∫ e^{β Re tr v} v dv` vanish (conjugation by `diag(i, -i, 1, ...)` ∈ SU(N)); diagonal entries are equal (signed transposition ∈ SU(N)); `S₀₀` is real (inversion) | `schurM_offdiag`, `schurM_diag`, `schurM_im` | [Lean] |
| `∫ tr v dv = 0` on SU(N), `N ≥ 2` (the centre element `ω ≠ 1` multiplies the trace) | `integral_traceN_eq_zero` | [Lean] |
| `λ_N(β) ≠ 0` for `β ≠ 0`, `N ≥ 2` (`β N λ_N(β) = ∫ (e^{βt} - 1) β t > 0`) | `schurCN_ne_zero` | [Lean] |
| the centre twists `zN k = ω^k · 1`: central, `zN (k + l) = zN k · zN l`, `zN (-k) = (zN k)⁻¹`, `Re tr zN k ≠ N` for `k ≠ 0` | `zN_central`, `zN_add`, `zN_neg`, `reTr_zN_ne` | [Lean] |

Schur's lemma itself is [classical]; the formalisation for every `N` is new here.

### 2.3 The SU(N) Wilson chain — `SUNTwistWilson.lean`

`sunZ N L β P T` = periodic partition function of `ℤ/Tℤ × (ℤ/Lℤ)³`; `sunZtw N L β P c T k` = the same with the
't Hooft twist by `ω^k` in the plane `(t, x¹)` at `x¹ = c`, on top of any spatial twist `P`.

| statement | Lean name | status |
|---|---|---|
| `Z_tw,0 = Z` | `sunZtw_zero` | [Lean] |
| `Z_tw,k = Z_tw,N-k` (every `β`, `T` even) | `sunZtw_neg` | [Lean] |
| `0 < Z_tw,k` (every `β`), `Z_tw,k ≤ Z` (every `β`, `T` even) | `sunZtw_pos`, `sunZtw_le` | [Lean] |
| **`Z_tw,k < Z` for every `β ≠ 0`, every `k ≠ 0`** (`N ≥ 2`, every `L ≥ 1`, every even `T`, every `P`, `c`) | `sunZtw_lt` | [Lean] |
| `c_k = Z_tw,k / Z ∈ (0, 1)` | `sunTwistRatio_mem` | [Lean] |
| the one-step non-degeneracy: `⟨φ∘h - φ, 𝒦(φ∘h - φ)⟩_V = λ_N(β)^L κ ∫ (Re tr(ω^{-k} P) - Re tr P)² ≠ 0` (`φ = Re tr P / V`, `P` the Polyakov line) | `sun_vip_twDiff`, `kop_twDiffN`, `stepK_polyObsN`, `lineIntN` | [Lean] |
| electric sectors `Z_e`: real, `Z_e = Z_{N-e}`, `Z_e ≥ 0`, `Σ_e Z_e = Z` | `sunZe_im`, `sunZe_neg`, `sunZe_nonneg`, `sum_sunZe` | [Lean] |
| for `β ≠ 0` some `e ≠ 0` has `Z_e > 0` (the twisted box carries electric flux) | `exists_sunZe_pos` | [Lean] |

**Named hypotheses: none.** The brief allowed a named hypothesis for whatever part of the strict bound or of `Z_e ≥ 0`
was too large; both are proved outright.

**Not formalised** (as for SU(2)): the bridge from this chain to `RouteB.twistZ` on the symmetric torus `(ℤ/Nℤ)⁴`, and the
transfer-matrix reading `Z_tw,k = tr(Ω^k 𝒯^T)`, under which `Z_e / Z_0 = e^{-T (E_e - E_0)}` (the tunnelling identity of
`zn_tunnel_check.py`, [numerical] in the model, [classical] as the standard reading).

---

## 3. Electric sectors and the Fourier matrix — `SUNTwistSectors.lean`

For any even `Z : ZMod N → ℝ` (in the application: the twisted partition functions).

| statement | Lean name | status |
|---|---|---|
| `Z_e = (1/N) Σ_k ω^{-ek} Z_k = (1/N) 𝓕Z(e)` (Mathlib's `ZMod.dft`) | `elecZ`, `elecZ_eq` | definition |
| `Z_e` real, `Z_e = Z_{-e}` | `elecZ_im`, `elecZ_neg` | [Lean] |
| inversion `Z_k = Σ_e ω^{ek} Z_e`; `Σ_e Z_e = Z_0` | `twisted_eq_sum_elec`, `sum_elecZ` | [Lean] |
| `F_{jk} = ω^{jk}/√N` is unitary | `fourierMat_unitary` | [Lean] |
| `F² = C`, `C_{jk} = [j + k = 0]` (conjugation, the N-ality pairing); `C² = 1`; `F⁴ = 1` | `fourierMat_mul_self`, `conjMat_mul_self`, `fourierMat_pow_four` | [Lean] |
| `N = 2`: `F² = 1`, a half-turn (Hadamard) | `fourierMat_two_sq` | [Lean] |
| `N ≥ 3`: `F² ≠ 1`, a quarter-turn | `fourierMat_sq_ne_one` | [Lean] |

The facts are [classical] (discrete Fourier analysis on `ℤ/Nℤ`). Reading `F` as the electric-magnetic duality of SU(N)
and `F²` as charge conjugation is the 't Hooft picture [classical]; that it is "the half-turn of the sphere" for SU(2)
and a quarter-turn for SU(N), `N ≥ 3`, continues `GRH-LENS.md` 6.1 [reading for the geometric language, Lean for the
matrix facts].

---

## 4. Primes as the base — `SUNTwistPrimes.lean`

| statement | Lean name | status |
|---|---|---|
| `ZMod N ≃+* Π_{p ∣ N} ZMod (p^{v_p(N)})` (CRT over the prime powers) | `centreCRT` | [Lean], CRT [classical] |
| `ZMod 6 ≃+* ZMod 2 × ZMod 3`, `ZMod 10 ≃+* ZMod 2 × ZMod 5` | `centre6`, `centre10` | [Lean] |
| the Fourier kernel factorises: `ω_{mn}^j = ω_m^{bj} ω_n^{aj}` for `ma + nb = 1` | `stdAddChar_crt` | [Lean] |
| prime `p`: every nonzero sector generates `ZMod p` | `prime_generates` | [Lean] |
| prime `p`: the units act transitively on nonzero sectors | `prime_units_transitive` | [Lean] |
| composite `N ≥ 2`: some nonzero sector generates a proper sub-centre (the smallest prime factor) | `composite_subcentre` | [Lean] |
| a unit `m` permutes the sectors `k ↦ mk`, fixes 0; charge conjugation is the unit `-1` | `unitPerm`, `unitPerm_zero`, `unitPerm_neg_one` | [Lean] |
| the electric transform intertwines: `𝓕(Φ ∘ m·)(e) = 𝓕Φ(m⁻¹e)` | `dft_comp_unit` | [Lean] |
| primitive Dirichlet character `χ` mod `N`: `Σ_k ω^{-ek} χ(k) = χ⁻¹(-e) τ(χ)` (the Gauss sum is the Fourier coefficient linking the multiplicative character to the additive, electric sectors) | `elec_dirichlet` (from Mathlib's `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`) | [Lean], [classical] |
| prime `p`: every nontrivial character is primitive; `τ(χ, ψ) τ(χ⁻¹, ψ⁻¹) = p` | `isPrimitive_of_prime`, `gaussSum_prime` | [Lean], [classical] |

**Care points.**
* The base pieces are **prime powers**, not primes: `ZMod 4` is not `ZMod 2 × ZMod 2` [classical]. For prime `N` the
  centre is the field `F_p`.
* The characters of the sector-symmetry group `(ZMod N)ˣ` are exactly the Dirichlet characters mod `N` [classical]. The
  Lean statements above are about these characters and their Gauss sums, not about L-functions or their zeros.

**What is the owner's reading** [reading]:
* "Primes as the base N of existence": that the physically relevant gauge groups are organised by the primes in their
  centres, and that the prime SU(N) are the irreducible building blocks. The Lean content is the CRT decomposition and the
  prime/composite dichotomy above; the ontological reading is not a theorem.
* "From two towards three through all primes": SU(2) (centre `Z_2`, `(Z/2)ˣ` trivial, the duality a half-turn), then
  SU(3) (`Z_3`, `(Z/3)ˣ = {1, -1}` = identity and conjugation, `su3_units` [Lean], the duality a quarter-turn), then every
  prime. The ordering by primes is a reading.
* "Through GRH": the sector symmetries of SU(N) form the group whose L-functions satisfy the Dirichlet GRH, which was
  proved in Lean by others on 2026-11-20 (external, not checked here). That this proved GRH acts on the Yang-Mills sectors
  in any quantitative way is **not** shown: nothing in this round uses the location of zeros. GRH beyond Dirichlet
  stays [open].
* DMP identifications (centre sectors as "nodes", tunnelling as "acts", the electric factor as "the tick of causality")
  are [reading], as in `PREP.md`.

---

## 5. The owner's candidates — `SUNTwistInstances.lean`

| `N` | strict bound `0 < Z_tw,k < Z`, `k ≠ 0`, `β ≠ 0` | pairs `Z_tw,k = Z_tw,N-k` | Fourier | prime structure | Dirichlet |
|---|---|---|---|---|---|
| 2 | `su2N_Ztw_lt`, `suN_ratio` | trivial (`1 = -1`) | half-turn, `F² = 1` | prime; `(Z/2)ˣ` has 1 element | none nontrivial |
| 3 | `su3_Ztw_lt`, `suN_ratio` | `su3_pairs`: `Z_1 = Z_2` | quarter-turn | prime; units `{1, -1}` (`su3_units`) | — |
| 5 | `su5_Ztw_lt`, `suN_ratio` | `su5_pairs`: `Z_1 = Z_4`, `Z_2 = Z_3` | quarter-turn | prime; 4 units | `suN_dirichlet`: primitive, `𝓕χ = χ⁻¹(-e) τ`, `τ τ' = 5` |
| 11 | `su11_Ztw_lt`, `suN_ratio` | `su11_pairs`: `Z_k = Z_{11-k}` | quarter-turn | prime; 10 units | `suN_dirichlet`: same with 11 |

All [Lean]. Electric sectors for SU(5) and SU(11) (`suN_elec`): real, nonnegative, `Z_e = Z_{N-e}`, summing to `Z`,
and some `e ≠ 0` has `Z_e > 0` [Lean]. Every `N` in between is covered by the general theorems; `composite_examples`
checks that `N = 4, 6, 8, 9, 10` have a nontrivial sector in a proper sub-centre [Lean].

The SU(2) instance is the statement of `su2_Ztw_lt_Z` (`Flip/Strict`) proved again by the `Z_N` route; the
identification of the two SU(2) chain weights (and of `zN 1` with `-1`) is not formalised.

On the physics [classical]: SU(5) is the Georgi-Glashow unification group, SU(11) Georgi's family-unification model;
both are candidates in the literature, neither confirmed. The test here is of the twist bound and the sector structure of
their centres, not of the models.

---

## 6. CPU check — `sun_primes_check.py`, `.log` [numerical]

1. In the tunnelling model of `zn_tunnel_check.py` (`N = 2` to 11): the matrix `Z_{k-l}` is positive semidefinite, its
   eigenvalues are exactly `N Z_e`, and `Z_e ≥ 0`. This is the model version of `ZFam.elec_nonneg`; an even sequence that
   is not a norm (`1, 0.9, -0.5, 0.9`) gives `Z_2 < 0`, so the check can fail.
2. CRT: for `(m, n) = (2, 3), (2, 5), (3, 4), (4, 9), (5, 11)` the kernel factorises and the DFT of `Z_mn` equals the
   relabelled Kronecker product of the DFTs of `Z_m` and `Z_n`.
3. Generators: prime `N` (2, 3, 5, 7, 11) have every nonzero sector as a generator; composite `N` have sectors in proper
   sub-centres.
4. For every nontrivial character mod 3, 5, 7, 11: `𝓕χ = χ⁻¹(-e) τ(χ)` to `1e-14`, and `|τ(χ)|² = p`.
5. `F` unitary, `F² = C`, order 2 for `N = 2`, 4 for `N = 3, 4, 5, 6, 7, 11`.

---

## 7. Status table

| item | status |
|---|---|
| `Z_tw,k ≤ Z`, `Z_tw,k = Z_tw,N-k`, `2(Z - Z_tw,k)` a reflection norm, any chain, any twist with an inverse | [Lean] |
| strict bound `0 < Z_tw,k < Z` for SU(N), every `N ≥ 2`, `β ≠ 0`, `k ≠ 0`, even `T` | [Lean] |
| Schur's lemma on SU(N), `λ_N(β) ≠ 0` for `β ≠ 0` | [Lean] (lemma [classical]) |
| electric sectors real, `Z_e = Z_{N-e}`, `Z_e ≥ 0` (reflection positivity), `Σ Z_e = Z`, some `Z_{e≠0} > 0` | [Lean] |
| Fourier matrix unitary, `F² = C`, `F⁴ = 1`; half-turn `N = 2`, quarter-turn `N ≥ 3` | [Lean] (facts [classical]) |
| CRT over prime powers, kernel factorisation, prime centres generated by any nonzero sector, composite sub-centres | [Lean] (facts [classical]) |
| sector automorphisms `(ZMod N)ˣ`, Dirichlet characters, Gauss sums as Fourier coefficients | [Lean] via Mathlib, [classical] |
| instances SU(2), SU(3), SU(5), SU(11) | [Lean] |
| bridge from the chain to `twistZ` on `(ℤ/Nℤ)⁴` | not formalised |
| transfer-matrix reading `Z_e/Z_0 = e^{-T(E_e - E_0)}` | [classical] reading; [numerical] in the tunnelling model |
| any bound uniform in the volume; flux free energy; confinement; mass gap | not given by this round |
| O1, the uniform one-box bound (`Z_tw/Z ≥ 0.743` for every outside), now one condition per nontrivial sector | **[open]** |
| GRH beyond Dirichlet | **[open]** |
| primes as "the base N of existence"; DMP identifications | [reading] |

---

## 8. Reproduction

* Lean: inside the WSL replay distro, from the repository root, `bash docs/unified/sunprimes-axioms.sh >
  docs/unified/sunprimes-axioms.log 2>&1` (builds `ProofPhase.General.SUNTwistInstances`, prints the axioms of all 169
  declarations, greps for `sorry`/`admit`/`native_decide`/`axiom`). Result: 165 declarations on
  `[propext, Classical.choice, Quot.sound]`, 4 (`unitPerm*`) on `[propext, Quot.sound]`; no `sorry`.
* CPU: `python sun_primes_check.py > sun_primes_check.log` (numpy only, seconds).
* No existing file was edited; the six Lean modules are new and are not yet imported by any aggregate module.
