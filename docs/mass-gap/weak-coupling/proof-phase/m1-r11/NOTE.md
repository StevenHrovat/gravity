# R11: the formal assembly accepts a measurable blocking

File: `formal/ProofPhase/Interface/MeasBlocking.lean` (namespace `ProofPhase.Interface`). No existing file was edited.
Build: green (9018 jobs); axioms: see `axioms.log` (standard three only; no sorry, native_decide or axiom).

## Verified: the theta/half claim is true
Every use of the fields `.theta` / `.half` of `RPBlocking` in the formal tree:
* `Objects.lean` 421-422: `blocked_wilson_rp` (reflection positivity of the blocked Wilson measure).
* `Repair/MulNoise.lean` 146, 156 and `Repair/Noisy.lean` 83-84, 114-131: noisy / multiplicative-noise blockings
  (they feed `noisy_blocked_wilson_rp`).
* `RouteA/Blocking.lean` 572-596: construction and composition of blockings (smear block, identity, composition).
None is on the gap/transfer path. The path of `yang_mills_assembly_v4_bdd` is: `BlockGapBddW` and `ObsTransferPhysTW`
(statements use only `(B k j).B`), `torusDecayLoc_of_blockGapBddW` (proof uses `(B k j).B`, `(B k j).meas` and, through
`cov_map`/`cov_transfer`, nothing else), `bothOrdersLoc_of_torusDecayLoc`, `limitRP` (bare measure). So the claim holds.

## Proved
* `MeasBlocking G d N M` (fields `B`, `meas`), `MeasBlockingFamily T`, `RPBlocking.toMeas`, `blockingFamilyToMeas`.
* `MeasBlockGapBddW`, `MeasBlockGapUnifW`, `MeasObsTransferPhysTW`: the same statements as the originals for the bare map;
  `*_toMeas_iff` lemmas (all `Iff.rfl`) show the originals are the special case.
* `measTorusDecayLoc_of_blockGapBddW`: the body of the original proof, verbatim (it never used more than `B`, `meas`).
* `yang_mills_assembly_v4_bdd_meas`, `yang_mills_assembly_v4_meas` (homogeneous gap), `MeasOpenInputsV4`,
  `yang_mills_assembly_v4_inputs_meas`, `measOpenInputsV4_of_openInputsV4`: same five-fold conclusion as v4
  (`TorusDecayLoc ∧ MassGapLoc ∧ MassGapMFLoc ∧ LimitRP ∧ NonTrivial`).
* `MeasBlocking.viaState`, `measBlockedLaw_viaState`: a blocking through any measurable intermediate block state with a
  measurable SU(2) encoding (this is the slot for M1's SO(3) x Z2 state).

## Open / not done
* The SU(2) encoding of SO(3) x Z2 itself (lift of SO(3) bonds times z, Z2 axial gauge, gauge covariance) is NOT done: the
  development has no SO(3) x Z2 state type, and a measurable SO(3) -> SU(2) section is a large development. `viaState` is
  the interface it plugs into. The encoding's gauge-covariance is also what `GaugeInvariant` observables in
  `MeasObsTransferPhysTW` will need.
* Variants not ported: `_strategyA`, the V3 chain (`LevelDprimeW`, `H1LocalLipW`), `OneBox`, `Book/TwoSize`. They also use
  only `.B`/`.meas` on the gap side but were not requested.
* A measurable blocking is not required to give reflection positivity of blocked layers (`blocked_wilson_rp`); the
  assembly never needs it, since `LimitRP` comes from the bare measure. Anything wanting RP of block observables still
  needs `RPBlocking`.

---

# R12: randomized blockings and the dense-class spectral upgrade

New files (namespace `ProofPhase.Interface`, no existing file edited): `RandBlocking.lean`, `SpectralUpgrade.lean`,
`DenseTransfer.lean`. Build green (9021 jobs); `axioms.sh` now covers all four Interface files, `axioms.log` shows the standard
three axioms only; no sorry, native_decide or axiom.

## Change 1: blockings with auxiliary randomness (`RandBlocking.lean`)
* `RandBlocking G d N M`: a noise space `Ω` with `MeasurableSpace`, a probability measure `P`, a measurable map
  `B : GaugeConnection G d N × Ω → GaugeConnection G d M`. `RandBlockingFamily T`; joint law `randJointLaw T B k j = ym ⊗ P`;
  block law `randBlockedLaw = (ym ⊗ P).map B`.
* Deterministic special case: `MeasBlocking.toRand` (`Ω = Unit`, `P = dirac`), `measFamilyToRand`;
  `randBlockedLaw_measFamilyToRand` (the block law is the old one); `randBlockGapBddW_measFamilyToRand_iff`,
  `randBlockGapUnifW_measFamilyToRand_iff`.
* Statements: `RandBlockGapBddW`, `RandBlockGapUnifW` (integrals of `f ∘ B` over `ym ⊗ P`), `RandObsTransferPhysTW` (fine
  observables enter as `F ∘ fst`; the conditional expectations are given the sigma-algebra `comap B` on the joint space).
* Ported: `randTorusDecayLoc_of_blockGapBddW`, `yang_mills_assembly_v4_bdd_rand`, `yang_mills_assembly_v4_rand`,
  `RandOpenInputsV4`, `yang_mills_assembly_v4_inputs_rand`: same five-fold conclusion.
* **What on the gap/transfer path needs determinism: nothing.** The one place the blocking acts is `cov_transfer`, which is
  generic (any probability space, any measurable map). The port applies it on `ym ⊗ P` through the new `cov_transfer_rand`, which
  brings the fine covariance back to `ym` with `integral_comp_fst` (a fine observable has the same integral over `μ ⊗ P` as over
  `μ`). `wcorr` is a statement about the fine measure, so `TorusDecayLoc`, `bothOrdersLoc_of_torusDecayLoc` and `limitRP` are
  untouched.
* Constructor for M1: `RandBlocking.viaState` (state `X` computed from fine configuration and noise, measurable SU(2) encoding)
  with `randBlockedLaw_viaState`. A swallowed bond with a fresh Haar value is `Ω = Haar^{swallowable bonds}`, `φ(U, ξ)` = Balaban
  average on non-swallowed bonds and `ξ_c` on swallowed ones; the measurability of `φ` is what M1 owes.
* Not proved: `RandObsTransferPhysTW (measFamilyToRand B)` from `MeasObsTransferPhysTW B` (the deterministic transfer as a
  special case). The gap statements are proved equivalent; the transfer one needs `condExp` under `μ ⊗ dirac` transported along
  `x ↦ (x, ())`, and Mathlib has no `condExp`/`map` lemma for that. Not needed for the assembly. The V3 chain variants,
  `_strategyA`, `OneBox` are not ported (as in R11).

## Change 2: spectral upgrade (`SpectralUpgrade.lean`, `DenseTransfer.lean`)
Abstract lemma, elementary (no spectral theorem, no completeness, no `‖T‖ ≤ 1`):
* `psd_cauchy_schwarz`, `moment_logconvex` (`a_{k+1}^2 ≤ a_k a_{k+2}`, parity split: form `⟪x,y⟫` for even `k`, `⟪x,Ty⟫` for odd
  `k`), `logconvex_ratio`, `inner_le_of_moment_decay` (decay at rate `m` forces `⟪G,TG⟫ ≤ e^{-m}‖G‖²`), `inner_le_closure`
  (continuity), `norm_le_of_inner_le` (a positive symmetric form bounded by `q‖·‖²` on an invariant subspace bounds `‖T·‖` by
  `q`), `iter_norm_bound`.
* **`spectral_upgrade`**: `T : H →L[ℝ] H` symmetric and positive, `H0` a submodule with `T H0 ⊆ H0`, `D` with
  `(H0 : Set H) ⊆ closure D`, and for every `G ∈ D` a `C` with `⟪G,T^n G⟫ ≤ C e^{-(m n)}` for all `n`; then
  `⟪F,T^n F⟫ ≤ e^{-(m n)} ‖F‖²` for all `F ∈ H0` and all `n`. Also `spectral_upgrade_step` (`⟪F,TF⟫ ≤ e^{-m}‖F‖²`) and
  `spectral_upgrade_cross` (`‖T^n G‖ ≤ e^{-(m n)}‖G‖`, `|⟪F,T^n G⟫| ≤ e^{-(m n)}‖F‖‖G‖`).
* `DenseTransfer.lean`: `ObsClass T`, `ObsTransferPhysTWDense T B Cls` (one rate `m`, `k₀` depending on the extent `R`, constants
  `c, K` chosen after the observables and before the separation `D`, observables restricted to a class),
  `obsTransferPhysTWDense_of_uniform` (the uniform statement implies it, for every class), and the randomized versions.

## Connection to the assembly: not done, and what it needs
1. **A correction to `R10-SCOPE.md` section 3.** Per-observable constants on a fixed periodic torus are vacuous: at fixed
   `(k, j)` the time length `N` is finite and the torus statement covers `n ≤ N/2`, finitely many `n`, so every `F` has a `C_F`
   with `|wcorr(F,n)| ≤ C_F e^{-m n}` for free, and no upgrade can start from it. The claim that the constants may depend on `k`
   and `F` "because the upgrade happens level by level" does not hold on the torus. The dense hypothesis must be a statement for
   all `n ∈ ℕ`: on the time-infinite cylinder over a fixed spatial cross-section (the one-sided form, `T` the transfer operator of
   that cylinder), or with `C_F` uniform in the volume.
2. **Cylinder versus cubic torus.** M1's decay is proved on tori `side^4`; the one-sided form needs the decay on
   `ℤ × (side)^3`. Torus constants `C(n, N)` that do not depend on the torus size (as in R10 section 2) give it only after a volume
   limit, not at finite `j`. The upgrade then gives spectral radius at most `e^{-m}` on the cylinder, uniformly in level and volume
   because `m` is. Returning to the cubic-torus statement `TorusDecayLoc` needs the finite-time correction
   (`tr(T^{N-n} F T^n F)/tr T^N` versus `⟨F,T^n F⟩`), which the project does not have. The alternative is to aim at `MassGapLoc`
   directly on the limit, which is what the main theorem uses.
3. **The OS transfer operator is not in the development.** `rp_gaugeMeasure`/`LimitRP` give only `∫ F · (F ∘ Θ) ≥ 0` for the
   plane reflection `thetaConn` and `F` depending on `posHalfLinks`. `Flip/Strict.lean` has `kop` with `vip_kop` (symmetry) on a
   time chain, but that is a separate chain model, and its own note says the bridge to the 4D `GaugeConnection` torus is not
   formalised. Needed for `spectral_upgrade`: (a) `H` = quotient of positive-half functions by the null vectors of the RP form;
   (b) `T` = unit time shift on `H`, bounded by RP Cauchy-Schwarz and symmetric; (c) positivity of `T`, which needs reflection
   through a half-lattice plane (link reflection) and not only the site reflection that `LimitRP` states, or a square root of a
   positive two-step shift; (d) `⟨F, T^n F⟩ = ∫ F(S_n) F(Θ)` (what `wcorr` computes); (e) `H0` = orthogonal complement of the
   vacuum, `T`-invariant; (f) the dense class (character polynomials of bounded degree in the links of a bounded region) is dense
   in `H0` (Peter-Weyl on finitely many links, then local functions dense in `L²`).
   (a), (b), (d), (e), (f) are routine but long; (c) needs a check that the Wilson measure has half-lattice RP in the project.
4. After that, the final step is the converse direction already in the project (`cov_transfer`,
   `bothOrdersLoc_of_torusDecayLoc`): the upgraded decay is the `MassGapLoc` input with prefactor 1.
The abstract lemma and the dense-class Prop are the reusable parts; items (a)-(f) are a development of the size of the RouteB
chain work.
