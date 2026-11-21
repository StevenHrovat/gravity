# Round 4, r4-actnumber: the act number z(L) = E_e(L)·L, prepared for the GPU (2026-11-21)

The data side of round 4. Task: prepare, pre-register and CPU-test a GPU measurement of the scout's act number (`../../round4-prep/
DMP-SCOUT.md` §2.9). Nothing was run on the GPU; the coordinating session runs `queue_actnumber_gpu.ps1` after Leg C. Claim levels as in
`../RULES.md`. This note contains no physics result: every number below is from tiny CPU test lattices and is marked as such.

## 0. In plain words

1. **What is measured.** In a periodic box of side L with 't Hooft's twist in the xy-plane, the cheapest state carrying one unit of
   centre flux along z (parallel to the twist) has energy E_e(L). z = E_e·L is a pure number (the act's cost in quanta ħ). It is read
   from the Euclidean-time correlator of z-Polyakov loops summed over the transverse plane, unsubtracted (⟨p⟩ = 0 by centre symmetry), with
   a cosh fit form that works whether E·T is large or of order one. z needs no lattice spacing; only the L axis does.
2. **What it can and cannot tell.** It is the gap of the flux sector of a finite box, not the glueball gap. It can show where z crosses 1
   (a tuning step, weaker than the gap) and whether it keeps growing by a margin per doubling (flux-sector confinement on the measured
   stretch, incomparable with the gap), and, for r4-minting, whether z(2L) depends on z(L) alone (one flow). It cannot show the sector
   transfer or anything rigorous. Growth would be evidence about pure SU(2) specifically: asymptotic freedom alone does not imply it
   (Banks–Zaks theories are asymptotically free and gapless).
3. **The plan.** 38 runs in the main queue: U(1) photon gate first (stops the queue if z is not frozen), SU(2) at β = 2.4 and 2.5 across L√σ = 0.73–3.61,
   small-L points at β = 2.6 and 2.7, deconfined Z₂ and frozen binary icosahedral (2I) controls, the symmetry control (twist in another
   plane), and reported extras (β = 2.3, a second Coulomb β, the untwisted box, 2I below its freezing). About 4.8 GPU hours (±50 %), core
   4.2 h; the cuts are listed in `PREREG.md`. An optional addendum (13 runs, about 1.3 h, switch `-AddendumW`) measures r4-conjw's
   four-move split of one doubling at the small end.
4. **Readings added at other attempts' request, before any data.** r4-minting: the collapse test, i.e. whether z(2L) plotted against
   z(L) at several β falls on one curve σ(u), with the minimum of σ(u)/u, and controls (U(1) on the diagonal, Z₂ and 2I below it); the
   Banks–Zaks point. r4-conjw: the inversion box z = log(1 + √2) = 0.881 in the two-state form (free); the four-move ratios (addendum);
   the exact F_e and F_m written up as optional, not prepared (about 2–3 h of code plus 50 GPU minutes).
5. **CPU status.** Self-test 28/28; pipeline test (all run types including the anisotropic boxes, and the full analysis) passes as a
   pipeline test; the photon gate's feasibility check at T = 32 passes: z is frozen at about 0.7 = 2πα_R (section 4.1).
6. **The literature exists.** The measurement is new for this project, not for physics: García Pérez, González-Arroyo and Martínez
   measured electric-flux energies in twisted SU(2) boxes from L√σ ≈ 0.8 to about 3 in 1993–95 (section 3). Their data predict our
   crossing near L√σ ≈ 1.3–1.6, and they warn about slow Monte Carlo tunnelling at small L, which shaped our checks.

## 1. Estimator, and why

- **Choice.** The z-Polyakov-loop correlator in the twisted box, as in García Pérez, González-Arroyo and Martínez (who used blocked and
  smeared Polyakov loops and the effective mass at t = 3). Ours: transverse-only smearing at three or four levels (the twist sits in the
  transverse plane, so the smearing staples contain no twisted plaquette and need no sign), a variational step, cosh effective masses,
  the TTL scan's plateau rule, and a second, non-linear operator (the sign of the summed loop, the correlator form of their 1993
  sign-flip count) as a systematic check.
- **Not chosen.** (a) The electric-flux free energy from twisted/periodic partition-function ratios with a temporal twist (de Forcrand
  and von Smekal 2002): an order of magnitude more GPU time per point (coupling integration or snake algorithm), and a free energy at one
  T rather than an energy. (b) The twisted-Polyakov-loop scheme (de Divitiis et al. 1994): a coupling from a correlator amplitude at
  fixed separation, ∝ g² at tree level; a fine running coupling but not existence × extent.
- **Sector.** e ∥ m (single-plane twist m_z, flux e_z): e × m = 0, no fractional momentum; the two classical vacua are the twist eaters
  P_z = ±1 (r3-monotone's `su2_twist_eater`), split by Q = ½ tunnelling at small L.

## 2. Code (all new, in this folder; `lattice/boundary.py`, `analyse.py`, `analyse_plateau.py`, `gpu/gauge.py` imported unchanged)

- `actnumber.py`: geometry with the sign sheet; twisted staples (quaternion and complex); SU(2) heat bath and overrelaxation in array
  code; the **fused path** = the unchanged fused CUDA kernels plus an exact re-update of the 4·L·T sheet links after every pass of a
  twist-plane direction (`SheetFix`); U(1), Z₂ and 2I updaters; twist-eater starts; the flux operators; the sheet-versus-bulk check;
  `selftest [--gpu] [--no-fused]`, `bench`, `run`, and `plannames` / `runplan NAME DIR` (the queue reads the job list from `PLAN`, one
  source of truth).
- `analyse_actnumber.py`: per-run E, z, the counting checks, z_up, the sign-operator estimate; readings (i)–(vi), gates and controls;
  `--photon-gate` for the queue.
- `pipeline_test.py`: the CPU end-to-end test. `queue_actnumber_gpu.ps1`: the GPU queue (waits for Leg C; not started).
- Why the fused path needs only the sheet fix-up: a checkerboard pass (μ, parity) reads no link it writes, so the wrongly updated sheet
  links of that pass are read by nobody before they are replaced; a heat-bath draw does not depend on the old value, and overrelaxation is
  redone from the value saved before the pass. The CPU self-test checks this against a numpy emulation of the kernel pass (exact for
  overrelaxation; sheet = bulk for heat bath); the GPU self-test checks it against the real kernel.

## 3. Literature, re-checked (the scout cited from memory)

| scout's claim | checked | status |
|---|---|---|
| fractional instantons in twisted boxes (García Pérez, González-Arroyo, Snippe, van Baal 1994) | not re-read; the directly relevant papers are the next two rows | memory |
| electric flux energies in twisted SU(2) boxes, small L, Q = ½ tunnelling | García Pérez, González-Arroyo, Martínez et al., Phys. Lett. B 305 (1993) 366, hep-lat/9302007 (HTML read via a summarising fetch): m = (1,1,1), N_s = 4, 6, 8, Q = ½ dilute gas, lattice instanton actions S_L(4, 6, 8) = 37.49, 38.64, 39.00 → 4π²; **Monte Carlo autocorrelation very large at large β** (a pair did not annihilate in several 10⁵ sweeps at β = 3, N_s = 4) | **read (summary)** |
| "how the string tension is built up" | González-Arroyo and Martínez, Nucl. Phys. B 459 (1996) 337, hep-lat/9507001 (**read in full**): N_s = 4, 6, 8, N_t = 128, 128, 64, β = 2.25–2.6, Polyakov-loop correlators, M(3); the flux energies interpolate smoothly from semiclassics to confinement; Σ_{e} = E/(|e| l_s) reaches σ within about 20 % at l_s ≈ 1.0–1.2 fm (l√σ ≈ 2.2–2.7 in their units σ = 5 fm⁻²); in the dilute region l_s E_(1,1,1) ≈ 2 (l_s/l̄)^α, α ≈ 2, l̄ ≈ 0.6–0.7 fm (l̄√σ ≈ 1.3–1.6); 10⁴–10⁵ thermalisation sweeps, N_skip 50–500 | **read** |
| electric flux free energies, de Forcrand and von Smekal 2002 | Phys. Rev. D 66 (2002) 011504, hep-lat/0107018, abstract read: 't Hooft loops of maximal size, electric flux free energies vanish exponentially with L below T_c, evidence for a mass gap | **read (abstract)**; "linear in L" not confirmed from the abstract |
| twisted-Polyakov-loop scheme, de Divitiis, Frezzotti, Guagnelli, Petronzio | hep-lat/9312085 (definition; Λ_TP/Λ_MSbar = 1.6136(2)), hep-lat/9407028 (non-perturbative running over a factor ~30 in energy); journal Nucl. Phys. B 422 (1994) 382 per a later citation | **read (abstracts)** |
| van Baal's thesis, Luescher 1983, Koller and van Baal | not re-read (not relied on; cited by hep-lat/9507001 as refs. 11, 12) | memory |
| T_c/√σ ≈ 0.71 for SU(2) | not re-read (Lucini, Teper, Wenger 2004: 0.709, recalled) | memory |
| 2I freezing near β ≈ 6 | not re-read; the CPU pipeline shows the β = 8 plaquette 0.993 (frozen) and β = 2.4 equal to SU(2) | memory + our check |

**Consequence for the expectations.** The scout's z = 1 near L√σ ≈ 1.5 is supported in spirit by hep-lat/9507001 (their diagonal flux
has l_s E = 2 at l̄√σ ≈ 1.3–1.6); their effective small-L exponent is about 2, not the asymptotic 11/3 (heuristic, logs and prefactors):
reading (v) is therefore reported without a criterion. Their measured rise is smooth with no intermediate scale, so the pre-registered
expectation is GROWS WITH MARGIN. The measurement is thus partly a re-measurement of known physics in a new form (one flux direction, the
act-number normalisation, the collapse test, and the controls), not a discovery.

## 4. CPU test results (pipeline only; not physics)

- Self-test 28/28 (`cpu-test/selftest.log`; list in `PREREG.md`).
- Pipeline test 390 s (`cpu-test/pipeline.log`, `summary.json`): every run type, the anisotropic boxes and every per-run quantity run.
  Toy numbers (not physics): SU(2) β = 2.4, L = 4 (L√σ = 1.03): z = 0.43 ± 0.04 (sign operator 0.40), yz-twist 0.53 ± 0.05, periodic
  0.87 ± 0.05; 2I β = 2.4: 0.32 ± 0.07; Z₂ and frozen 2I fall; U(1): 0.96, 0.71, 0.73 at L = 2, 4, 6 (toy gate passed). Two-site boxes
  are artefacts (the toy U(1) widening is 0.40–0.45 instead of ½ at L = 2 → 4).
- Synthetic check of readings (ii), (iii), (vi), (vii) and the light four-move control on points with a known answer: all recovered
  (crossing within 3 %, the method's interpolation bias at the coarse spacing).
- Photon feasibility: section 4.1.

### 4.1 Photon feasibility (U(1), β = 1.1, CPU)

T = 32 (the pipeline's T = 16 was too short), rotor estimator (the U(1) flux sectors are a tower E_n = n² e²/(2L); the two-state cosh
form is biased when E·T is of order one): z = 0.694 ± 0.020 (L = 4, 4 × 600 measurements) and 0.729 ± 0.036 (L = 6, 4 × 400), both
counted, flat within 5 %. So 2πα_R ≈ 0.7, α_R ≈ 0.11 against the bare 1/(4πβ) = 0.072; a free Villain-type matching gives 0.77. On these
tiny lattices the owner's α pointer already reads as an identity on data: the photon's act number is frozen and equals 2πα (with the
renormalised α near the U(1) transition). Not a result: two box sizes, CPU statistics.

## 5. What the coordinator must decide

1. **When to start the queue.** `pwsh -File queue_actnumber_gpu.ps1` (from this folder) can be started at any time: it waits for Leg C's
   addendum to finish ("ADDENDUM DONE" or "ADDENDUM not run" in `../r3-blocked/runs-gpu/queue_blocked.log`; or "BLOCKED DONE" with no
   addendum queue process alive) and for no blocked.py/boundary.py run to be left, checked twice 3 minutes apart. It does not look at
   other GPU users (other round-4 queues); if another GPU job is planned after Leg C, order them by hand.
2. **Whether to add the four-move addendum** (`-AddendumW`, +1.3 h). Recommended only if the main result shows a small margin at the
   small end (the addendum covers L√σ ≤ 1.55 only).
3. **Budget.** Main plan about 4.8 h ±50 % at estimated rates (the U(1)/Z₂/2I array-code rates are guesses); the queue's bench step logs
   the measured projection as its third line. If it projects more than 7 h, cut in the order given in `PREREG.md` (extras first).
4. **Whether to prepare the exact F_e/F_m measurement** (not prepared; about 2–3 h of code, 50 GPU min).
5. **Note for the GPU self-test.** The fused path (unchanged kernels plus the sheet fix-up) has been tested on the CPU only through a numpy
   emulation of the kernel pass; the first queue step checks it against the array path on the GPU (overrelaxation to 10⁻¹⁰, cubic and
   anisotropic, and sheet = bulk). If it fails, the queue falls back to the array path by itself, at a higher cost that the bench step
   will show.

## 6. Honest limits of this preparation

- No GPU code path was executed (rule: no GPU use by an attempt). The fused path and cupy array path are untested on real hardware.
- The GPU-time rates for U(1), Z₂ and 2I array code and the small-lattice floor (25 ms per sweep) are estimates, not measurements.
- Small-L ergodicity: García Pérez et al. saw very long autocorrelations from slow tunnelling at small L and large β. Our drift and τ
  checks catch it per run, but if they fail, the β = 2.6 and 2.7 small-L points simply will not count; the plan cannot buy the 10⁴–10⁵
  thermalisation sweeps they used.
- The large-end reading (iv) is partly circular (our a√σ comes from periodic torelons with the same formula).
- Two main lattice spacings with a ratio of 1.41 give a scaling check, not a continuum limit. The collapse test's (a/L)² extrapolation
  uses two or three resolutions (a/L = 1/4, 1/6, 1/8) and is reported as such.

## 7. Files (all in this folder)

- `PREREG.md`: the pre-registration (question, estimator, runs, counted points, readings (i)–(viii), controls and gates, limits).
- `actnumber.py`, `analyse_actnumber.py`, `pipeline_test.py`, `queue_actnumber_gpu.ps1`.
- `cpu-test/`: `selftest.log`, `pipeline.log`, `analysis.log`, `summary.json` and the toy `.npz` files; `u1-feasibility/`.
