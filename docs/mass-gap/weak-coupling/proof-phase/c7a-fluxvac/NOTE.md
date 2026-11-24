# Cycle 7, workstream 1 (c7a-fluxvac): does the flux act's accumulation give the vacuum doubling with bounded loss? (2026-11-22)

Task: state the candidate implications (flux super-additivity + sector transfer => vacuum doubling; what carries the doubling across
the switch; the gluing deficit through flux sectors), prove what is provable (Lean under `formal/ProofPhase/FluxVac/`), find the
missing piece X, run the unit tests (photon, SU(2) x U(1), 2I, Z2 both phases, mixture, Heller endpoint), and give predictions for
the running joint z0/z_e measurement.

Claim levels: **Lean** (built, no `sorry`, no new axiom, no `native_decide`), **exact** (closed formula), **paper** (argued here),
**known** (literature, recalled, not re-read), **reading**, **SPECULATIVE**.

---

## 0. In plain words

1. **Answer: no, not by itself, and the reason is structural.** The flux act z_e = L E_e is extensive along the box (a string spans
   it: z_e ~ sigma L^2, doubling with a large gain). The vacuum act z0 = L E0 doubles only in the sense of *persistence*: E0 is an
   intensive energy, and z0(2L) >= 2 z0(L) - c says E0(2L) >= E0(L) - c/(2L). The flux surplus can pay for the vacuum only while the
   lowest centre-even state *is* made of flux (a pair of tubes), and that stretch (from about the deconfinement length L sqrt(sigma)
   ~ 1.4 to the switch ~ 2.0 to 2.3) is shorter than one doubling. Above the switch the lowest state is a localized glueball that does
   not span the box; its persistence is what carries the doubling, and the flux act says nothing about it (SU(2) x U(1): flux grows,
   photon stays; Heller endpoint: flux grows, massless scalar).
2. **What is proved (Lean, `ProofPhase.FluxVac.Branches`, 23 declarations):**
   * the **upper sector transfer is a theorem**: the flux-pair observable Phi^2 (square of Route B's summed Wilson line) is a
     centre-even vacuum observable, so **E0(L) <= E_pp(L)**, the decay rate of every non-vanishing connected limit of the pair
     correlation (`pairObs`, `su2_E0_le_pairRate`, `su2_z0_le_pairAct`). The lower sector transfer is not a theorem and cannot be one
     from group-blind tools (product test).
   * the **window implication** (exact algebra): lower sector transfer at the big box + upper at the small box + one flux doubling
     => one vacuum doubling with loss a + 2b + 2c_e (`doubling_of_window`; pair form `doubling_of_pair_window`).
   * the **branch form**: the vacuum law is not needed for z0 itself; a doubling lower envelope suffices (`envelope_floor`,
     `su2_gap_of_envelope`). With the lower sector transfer as z0 >= min(2 z_e - a, mu), flux doubling + **doubling of the non-flux
     branch mu** => the gap on the SU(2) boxes (`branches_floor`, `su2_gap_of_branches`).
   * the **escape form**: if every doubling either keeps the vacuum law up to c or is paid by flux,
     z0(2L) >= min(2 z0(L) - c, K z_e(2L)), flux accumulation supplies the escape condition and the gap follows
     (`escape_floor`, `escape_of_flux`, `su2_gap_of_flux_escape`). Here the flux act is genuinely used: it discharges every
     excitation that spans the box.
   * unit tests in Lean: the product satisfies flux doubling with gain and both sector transfers and violates the vacuum law
     (`product_test`); the escape form fails for it (`product_escape_test`); a constant flux act (photon, frozen 2I) gives the flux
     branch no positive start (`photon_flux_test`).
   * the **sector-resolved gluing deficit**: 1 + delta0 = (1 + delta) rho(L)^2 / rho(2L), rho = Z_{e=0}/Z (`vac_deficit_eq`,
     `vac_deficit_le`): flux saturation (rho -> 1) only identifies the vacuum-sector deficit with the full one.
3. **Which direction the existing inequalities give.** Every rigorous link between the vacuum gap and flux energies runs one way:
   E0 <= E_pp (variational / RP, Lean here); delta(L) >= e^{-z_e(L)} (a small full gluing deficit *forces* flux growth: `gap_of_deficit`
   applied to a flux state, c6a); RP gives sub-additivity on the vacuum side (c6c). No lower bound of E0 by flux energies is known, and
   none can follow from reflection positivity, transfer-matrix positivity and centre symmetry: SU(2) x U(1) has all three, growing
   flux, and E0 -> 0.
4. **The missing piece X** (two equivalent forms, both Lean premises):
   * (branch form) **the non-flux branch persists**: mu(2L) >= 2 mu(L) - c_mu along the dyadic boxes, where mu is the act of the
     lowest centre-even state that is not a flux pair (above the switch: the glueball);
   * (escape form) **the transplant/spanning dichotomy**: every centre-even excitation of the 2L box either transplants into the L box
     with act loss <= c (it is localized below L), or spans the box and costs K flux acts.
   In the owner's cycle-5 language: **the information layer is stateless** (no non-flux mode spans the box; localized modes do not
   feel the box beyond a bounded act).
5. **Is it progress?** For the infinite chain: **a relabelling**, not a reduction to something strictly weaker. X is implied by the
   gap (finite-size theory of a massive theory: a localized particle's energy shift is exponentially small in L, known, Luescher 1986)
   and implies it (Lean). What the reduction does buy: (i) the upper sector transfer is now a theorem; (ii) the open content is
   confined to the non-flux, localized branch above the switch, the flux part being discharged by the measured flux super-additivity;
   (iii) a sharper failure list: X fails exactly for delocalized lightest states (photon, Heller scalar, 2I flat sectors, phase
   coexistence). And one negative result: **flux accumulation is neither necessary (Z2 weak coupling: gapped, flux act -> 0) nor
   sufficient (SU(2) x U(1)) for the vacuum doubling.**
6. **The owner's start condition.** The flux pair cannot supply z0(L0) >= 4 pi: on the flux-pair branch z0 = 2 z_e stays below about
   7 to 9 (one quantum plus about one) up to the switch. The 4 pi start lies on the glueball branch, at L sqrt(sigma) ~ 3.3 to 3.7
   (z0 = m L with m/sqrt(sigma) = 3.4 to 3.8). Reading: the flux-pair branch ends near where the vacuum act passes one quantum
   (pilot: z0 = 6.48 at 2.10); the "true act" of two quanta is a glueball box, not a pair box. Numerical, not derived.
7. **Predictions for the running measurement** (`PREREG.md`, written before its data were read): no pair with both ends on the
   flux-pair branch; at the pairs starting at L sqrt(sigma) >= 2.0 the vacuum gain is below 0.3 of twice the flux gain (model 0.05 to
   0.12); loss c <= 1 everywhere (model: c between -6 and -1); at L sqrt(sigma) <= 1.1, z0 > 2 z_e (no pair state); z0 < 4 pi up to
   3.10 and > 4 pi from 4.13.

---

## 1. The implications, stated precisely

Notation along dyadic periodic boxes L_n = 2^n L0 at fixed beta: z(n) = z0(L_n) = L_n E0(L_n) (c5e: E0 = the vacuum, centre-even box
gap); ze(n) = z_e(L_n) = L_n E_e(L_n) (periodic box, flux along one axis); `Doubles z c` :<=> for all n, z(n+1) >= 2 z(n) - c.
Sector transfer, both directions, with constants a, b >= 0:
* **UST** (upper sector transfer, small box): z(n) <= 2 ze(n) + b, or in pair form z(n) <= zpp(n) := L_n E_pp(L_n).
* **LST** (lower sector transfer): z(n) >= 2 ze(n) - a (window form) or z(n) >= min(2 ze(n) - a, mu(n)) (branch form, mu = act of
  the lowest non-pair centre-even state).

**(a) Below the switch.** UST(n) + LST(n+1) + flux doubling ze(n+1) >= 2 ze(n) - c_e => z(n+1) >= 2 z(n) - (a + 2b + 2c_e)
(`doubling_of_window`). Both directions of the sector transfer are needed, at different boxes. The data give c_e < 0 (c6b fit:
z_e(2L) - 2 z_e(L) ~ 2 (L sqrt(sigma))^2 + 0.9), so the loss is a + 2b minus a large gain.
*Domain.* The flux-pair branch starts where torelons are particles (about the deconfinement length, x = L sqrt(sigma) ~ 1.4; below,
electric flux states are Fourier components of centre tunnelling and there is no excited e = 0 pair state, paper, van Baal's
small-volume picture, recalled) and ends at the switch 2 E_e(L_s) = m(L_s), x_s ~ 2.0 to 2.35 (`predict_pairs.log`; pilot: already
glueball at 2.10). L_s / L_dec ~ 1.5 < 2: **the window contains no dyadic pair** (prediction P1).

**(b) Across and above the switch.** Straddling pairs (L below, 2L above): c = 2 z0(L) - z0(2L) = 2L (2 E_e(L) - E0(2L)) - (binding)
<= 0 whenever the pair at L is lighter than the glueball at 2L, i.e. automatically below the switch. Above the switch:
c = 2L (E0(L) - E0(2L)), the persistence of the glueball energy. The flux act enters only through the min in the branch form and the
escape branch:

* branch form (`branches_floor`, `su2_gap_of_branches`): LST(branch) + `Doubles ze c_e` + `Doubles mu c_mu` + start
  max(2c_e - a, c_mu) < min(2 ze(0) - a, mu(0)) => E0(L_n) >= (start - defect)/L0 for all n.
* escape form (`escape_floor`, `escape_of_flux`, `su2_gap_of_flux_escape`): z(n+1) >= min(2 z(n) - c, K ze(n+1)) + flux doubling with
  K(ze(0) - c_e) - 2(z(0) - c) >= max(0, c - K c_e) + 0 <= c < z(0) => E0(L_n) >= (z0(L0) - c)/L0 for all n.

The escape form is the precise version of "what carries the doubling across the switch": spanning excitations are paid for by
flux (the flux act's surplus is real and used), localized ones must transplant. The transplant step is X.

**(c) The gluing deficit through flux sectors.** delta(L) = Z(L^4)^2 / Z(L^3 x 2L) - 1 (c6a). Decompose Z by electric flux,
Z = sum_e Z_e with Z_{e=0} = (1/8) sum_k Z_{tw,k} (temporal twists k in Z2^3; transfer-matrix identity, standard, not formalised),
rho(T) = Z_{e=0}(T)/Z(T) in (0, 1]. Then exactly (`vac_deficit_eq`, `vac_deficit_le`)

  1 + delta0(L) = (1 + delta(L)) rho(L)^2 / rho(2L),   delta0 <= (1 + delta)/rho(2L) - 1,

delta0 the vacuum-sector deficit, which bounds the vacuum gap: z0(L) >= -log delta0(L) (c6a's `gap_of_deficit` on the e = 0 family).
And every flux state enters the full deficit from below: e^{-z_e(L)} <= delta(L) (`gap_of_deficit`, any excited state). So the flux
weights e^{-E_e T} feed delta **additively and with the positive sign**: flux growth is *necessary* for a small full deficit, and
flux saturation (all twist ratios -> 1, rho -> 1, p -> 1/2 in every plane) only makes delta0 = delta. The neutral content of delta
is untouched. Direction: wrong for a proof of the gap, right for a proof of confinement from the gap.

## 2. Lean (`formal/ProofPhase/FluxVac/Branches.lean`, namespace `ProofPhase.FluxVac`)

| name | statement | kind |
|---|---|---|
| `Doubles`, `Doubles.mono` | the doubling law with defect | def |
| `doubling_of_window` | 2 ze(n+1) - a <= z(n+1), z n <= 2 ze n + b, 2 ze n - c_e <= ze(n+1) => 2 z n - (a + 2b + 2c_e) <= z(n+1) | exact algebra |
| `doubling_of_pair_window` | zpp(n+1) - a <= z(n+1), z n <= zpp n, 2 zpp n - c_p <= zpp(n+1) => 2 z n - (a + c_p) <= z(n+1) | exact algebra |
| `min_doubles` | Doubles x c_x, Doubles y c_y => Doubles (min x y) (max c_x c_y) | exact |
| `envelope_floor` | y <= z, Doubles y c => 2^n (y 0 - c) <= z n - c | exact |
| `flux_branch_doubles` | Doubles ze c_e => Doubles (2 ze - a) (2c_e - a) | exact |
| `branches_floor` | min(2 ze - a, mu) <= z, Doubles ze c_e, Doubles mu c_mu => 2^n (min(2 ze 0 - a, mu 0) - max(2c_e - a, c_mu)) <= z n - max(...) | exact |
| `product_test` | ze = 4^{n+1}: Doubles ze (-1); 2 pi <= 2 ze n; min(2 ze n - a, 2 pi) <= 2 pi; for c < 2 pi not Doubles (const 2 pi) c | unit test |
| `photon_flux_test` | Doubles (const k) c_e => (2k - a) - (2c_e - a) <= 0 | unit test |
| `vac_deficit_eq`, `vac_deficit_le` | the sector-resolved deficit identity and bound (positive reals) | exact |
| `su2_hz`, `polyLine_centreFlip_ne` | -1 is central; a centre flip in direction i != 0 leaves the axis-0 Wilson lines unchanged | lattice |
| `pairObs L : VacObs L` | f = (polySum L 2)^2: measurable, bounded by (2 card)^2, centre-even under all flips (direction 0 via `polySum_flip`, others via `polyLine_centreFlip_ne`) | **substantive, group-blind** |
| `su2_E0_le_pairRate` | 0 < E0 beta L, h a connected limit of the pair correlation with h(2s) > 0 => E0 beta L <= rate h | **the upper sector transfer, on the SU(2) Wilson measure** |
| `su2_z0_le_pairAct` | same, z0 <= L rate h | same |
| `su2_gap_of_envelope` | 0 <= c < y 0, y n <= z0(2^n L0), Doubles y c => E0(2^n L0) >= (y 0 - c)/L0 and decay of every centre-even connected correlation at that rate | substantive via c5e |
| `su2_gap_of_branches` | LST(branch) + Doubles ze + Doubles mu + start => E0(2^n L0) >= (min(2 ze 0 - a, mu 0) - max(2c_e - a, c_mu))/L0 | substantive via c5e; premises open |
| `escape_floor` | min(2 z n - c, K ze(n+1)) <= z(n+1) and c + 2^{n+1}(z 0 - c) <= K ze(n+1) => c + 2^n (z 0 - c) <= z n | exact |
| `escape_of_flux` | K >= 0, c <= z 0, Doubles ze c_e, A := K(ze 0 - c_e) - 2(z 0 - c) >= max(0, c - K c_e) => the escape condition | exact |
| `product_escape_test` | z0 = 2 pi, ze >= 1, K > 2 pi, c < 2 pi => the escape law fails at n = 0 | unit test |
| `su2_gap_of_flux_escape` | the escape law on the SU(2) boxes + flux doubling + escape start + 0 <= c < z0(L0) => E0(2^n L0) >= (z0(L0) - c)/L0 | substantive via c5e; the escape law open |

Build: `wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c7a-fluxvac/build.sh`
("Build completed successfully"); `axioms.sh` -> `axioms.log`: every declaration depends only on `propext`, `Classical.choice`,
`Quot.sound`; no `sorry`, `native_decide` or `axiom`.

Not formalised: E_pp ~ 2 E_e (the pair operator's rate is the two-tube energy; true only when a weakly bound two-tube state exists,
i.e. on the flux-pair branch; false in small boxes, P4); the electric-flux sector identity Z_{e=0} = (1/8) sum_k Z_k; the spectral
representation behind the deficit lemmas (as in c6a).

## 3. Is any lower bound on the vacuum gap by flux energies known or provable?

* **Not from positivity or centre symmetry (paper, sharp).** SU(2) x U(1) with the product Wilson measure is reflection positive,
  has a positive transfer matrix, a centre element (-1, 1) acting on the SU(2) flux, flux energies growing like sigma L, and
  E0(L) <= 2 pi / L-ish (the photon, z0 -> 2 pi). Any inequality E0 >= F(E_e, ...) built from these properties alone is false. The Lean
  `product_test` records the act-level consequence: flux doubling (with gain) + UST + LST do not give the vacuum law.
* **Not from transfer-matrix positivity in the other form either.** For a positive transfer matrix and the pair operator Phi^2,
  the only general inequality is the variational one (E0 <= E_pp, Lean). Cauchy-Schwarz gives <Phi^2_t Phi^2_0> >= <Phi_t Phi_0>^2,
  but the connected part subtracts <Phi^2>^2, which is larger: no bound on E_pp by 2 E_e from it (paper).
* **What is known in the literature** (recalled): the converse direction is a theorem in special settings (Chatterjee 2021: decay
  under arbitrary boundary conditions => area law for connected groups); Kanazawa/Tomboulis-Yaffe bound centre-charged observables
  only (Route B, `Sector.lean`). Flux-tube models (Isgur-Paton) *describe* glueballs as closed flux loops, which is the physical
  content of Conjecture S, not a bound. In d = 2 the bound is exact and trivial (below).
* **Direction summary.** Upper side (variational, RP): E0 <= E_pp. Deficit side: delta(L) >= e^{-z_e(L)} (small deficit forces flux).
  Lower side (what the gap needs): nothing, and nothing group-blind can exist.

## 4. Unit tests

| model | flux doubling (premise) | UST | LST, branch form (mu) | mu doubles / escape law | implication fires? | truth | verdict |
|---|---|---|---|---|---|---|---|
| photon U(1), 4D Coulomb | **fails**: z_e = g^2/2 constant, only with c_e >= g^2/2; flux branch start <= 0 (`photon_flux_test`) | holds (z0 -> 2 pi, 2 z_e const; b ~ 2 pi) | holds with mu = photon act | fails (mu bounded, c_mu >= 2 pi; escape needs c >= 2 pi: the photon of box 2L does not fit in box L and costs no flux) | no | gapless | correct |
| SU(2) x U(1) | holds, with gain (SU(2) tubes) | holds | holds, mu = photon | **fails** (`product_test`, `product_escape_test`) | no | gapless | correct; the violated premise is exactly X |
| 2I, weak coupling / beta = infinity (frozen act numbers) | fails: p = 1/160 at every L, so F_e and the flux act are constant (c6b, exact) | — | mu = flat-sector tunnelling act -> 0 | fails (z0 -> 0; the lowest centre-even state is a global flat-sector state, spans the box, costs no centre flux) | no | no continuum gap | correct |
| Z2 strong coupling | holds (area law) | holds | holds, mu = smallest closed loop, localized | holds (localized excitation, finite-size shifts exponentially small) | yes | gapped, confined | correct |
| Z2 weak coupling (deconfined, gapped) | **fails**: E_e = tunnelling between holonomy sectors -> 0, z_e -> 0 | — | flux branch useless (no e = 0 pair state) | mu (vison/magnetic excitation, localized) doubles; the branch theorem with mu alone (`su2_gap_of_envelope`) would fire | the flux route: no; the mu route: yes | gapped | correct; shows flux accumulation is **not necessary** |
| mixture (phase coexistence on the first-order line of the fundamental-adjoint plane) | holds (both phases confine) | — | mu = tunnelling between the coexisting phases, z0 -> 0 | fails (the tunnelling state spans the box through an interface, not through centre flux) | no | box gaps close (each pure phase gapped) | correct (conservative, like 2I) |
| Heller endpoint | holds | holds | mu = massless scalar act, bounded | fails | no | massless 0++, confined | correct |
| 2D YM (SU(2) or U(1) on a circle; exact) | holds: E_j = (g^2 L/2) j(j+1), z_e = (3/8) g^2 L^2 | — | exact with no mu: z0 = g^2 L^2 = (8/3) z_e >= 2 z_e (every state is flux) | — | yes | gapped (no local modes in 2D) | correct: **the implication is exact when there is no information layer** |
| SU(2) | measured (c6b: gain 2x^2 + 0.9) | Lean (pair form) | branch form plausible with a <~ 1 (pilot: z0 = 6.48 vs 2 z_e = 7.19 at 2.10) | **open = X** | conditional | the claim | — |

Every model in which X fails has a delocalized lightest centre-even state (massless mode, topological sectors, phase coexistence);
every model in which it holds has a localized one. The flux premise separates confinement from deconfinement and is irrelevant to
which side of X a model is on.

## 5. Readings (owner's language)

* **Accumulation belongs to spanning objects.** The owner's "accumulation of acts" is extensivity; it holds for what spans the
  boundary (the flux sheet: act ~ area). The vacuum's lightest excitation in a large box does not span it; its act grows only because
  the time extent grows ("one tick per tick"), i.e. its *rate* persists. The doubling law with loss is a persistence law, not an
  accumulation law. (reading, matches c6c's correction)
* **"Anything within a boundary contributes the most efficient existence possible"** is, read literally, frustration-freeness (the
  global vacuum minimises every local term). That is the premise of Knabe-type finite-size criteria (Knabe 1988; Gosset-Mozgunov
  2016; recalled), whose conclusion has exactly the start-condition shape: one patch with act above a fixed constant => a gap in all
  volumes. The lattice Yang-Mills transfer matrix is not frustration-free (c5e 4.3); this is where the reading and the available
  theorem part. (reading)
* **Stateless information layer = X.** In the cycle-5 two-layer picture (binary existence/centre layer, stateless information layer),
  the flux act is the existence layer and is under control (measured super-additive); X says the information layer holds no state
  across scales: no information-layer mode spans the box (photon, Heller scalar: stateful) and localized ones do not feel the box.
  2D YM has no information layer, and there the implication is exact. (reading)
* **The two quanta.** On the flux-pair branch z0 = 2 z_e: two flux acts, an arrow (one tube each way), as the owner's "a true act
  needs a duality" suggests. But the pair branch ends near one quantum (z0 ~ 7 to 9 at the switch); the two-quanta box (z0 >= 4 pi)
  is a glueball box. SPECULATIVE: the switch sits where the pair's act passes one quantum because a pair below one quantum cannot be
  undercut by a localized state of one quantum.

## 6. Next step

1. **Read the running measurement against `PREREG.md` (P1 to P6)**; for P6 extract, post hoc and labelled, the plateau of the
   pair-operator-only correlation (O_pp at the four levels) next to the variational z0: the theorem says z0 <= z_pp.
2. **X at one scale, paper:** prove the transplant inequality for the lightest glueball in a convergent expansion (strong coupling of
   the blocked theory, or Z2 at strong coupling): a localized one-particle state's energy shift between boxes L and 2L is
   exponentially small (the lattice analogue of Luescher's finite-size formula, where the polymer expansion converges). That would
   give X on the stretch where the blocked theory is in the convergent region, not on the crossover.
3. **Lean, small:** the electric-flux sector identity Z_{e=0} = (1/8) sum_k Z_k on the chain (it would make `vac_deficit_eq` a
   statement about the SU(2) objects); and the escape law's spanning branch stated with the pair act z_pp (so that its flux side uses
   the proved UST object, not z_e).

## 7. Not checked

Luescher's finite-size formula, van Baal's small-volume flux picture, Knabe/Gosset-Mozgunov, Isgur-Paton, Chatterjee are recalled, not
re-read. The model numbers of `PREREG.md` (string formulas, m/sqrt(sigma) band, binding band) are assumptions, not fits. The unit-test
rows for 2I, mixture and the Heller endpoint are paper-level (expected spectra, not computed). The Z2 weak-coupling claim "no e = 0
pair state" is paper-level. No GPU; the only computation is `predict_pairs.py` (arithmetic, milliseconds).

## Files

`NOTE.md` (this), `PREREG.md`, `predict_pairs.py` + `predict_pairs.log`, `build.sh`, `axioms.sh` + `axioms.log`. Lean:
`../../../formal/ProofPhase/FluxVac/Branches.lean`.
