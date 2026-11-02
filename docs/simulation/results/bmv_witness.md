# The Bose et al. spin entanglement witness: checked and corrected

Script: `docs/simulation/bmv_witness.py` (numpy, scipy; deterministic; about a minute). Numbers: `results/bmv_witness.json`. **34 of 34 checks pass.**

**Source read.** S. Bose, A. Mazumdar, G. W. Morley, H. Ulbricht, M. Toros, M. Paternostro, A. A. Geraci, P. F. Barker, M. S. Kim, G. Milburn,
"Spin entanglement witness for quantum gravity", arXiv:1707.06050. arXiv lists a single version, v1 of 19 July 2017, with the journal reference
Phys. Rev. Lett. 119, 240401 (2017). The published PRL text was **not** read: the publisher's accepted-manuscript page and a university repository
copy are outside this session's allowed network. Everything below refers to the arXiv text.

**The state** at the end of the two Stern-Gerlach interferometers (the unnumbered equation after Eq. (6)), with the overall phase omitted,
|up> = |0>, |down> = |1>:

    |Psi> = (1/2) [ |00> + e^{i a} |01> + e^{i b} |10> + |11> ],   a = Delta phi_LR,  b = Delta phi_RL,  Sigma = a + b.

Its entanglement depends only on Sigma (the paper says so as well): the negativity is sin(Sigma/2)/2.

## Verdict

- **The witness as printed is not a witness.** The paper defines W = |<sx (x) sz> - <sy (x) sz>| and states that W > 1 proves entanglement.
  Both terms share sz on the second spin, so the operator is sqrt2 s_n (x) sz with n = (x - y)/sqrt2.
  - A product state with spin 1 along n and spin 2 up gives **W = sqrt2 = 1.414**: the largest value any state, entangled or not, can give.
  - On the proposal's own states the printed W also misses entanglement. At a = 0, b = 1 rad (the paper's Sigma ~ O(1), inner branches
    closest) it is 0.65 while the state is clearly entangled (negativity 0.24).
  - At the phases where the arXiv text quotes W ~ 1.16 (Delta phi_LR = -0.2, Delta phi_RL = 0.7), the printed operator gives 0.33.
  - So it can fire on a product state and stay silent on an entangled one. The printed operator is most likely a misprint: a later analysis,
    Chevalier, Paige and Kim, arXiv:2005.13922 (Phys. Rev. A 102, 022428 (2020)), quotes the condition as |<sx sz> + <sy sy>| > 1. That form
    is valid but weak in this geometry (below).
- **The corrected witness** keeps the paper's two-setting design:
  - In the symmetric gauge (a = b = Sigma/2), **W_c = |<sx (x) sx> + <sy (x) sz>| <= 1** for every separable state, and **W_c = 1 + sin(Sigma/2)**
    on the BMV state. It detects every Sigma > 0, and W_c - 1 is twice the negativity.
  - In the lab gauge the x and y axes rotate by theta = (Delta phi_LR - Delta phi_RL)/2 (spin 1: x' = cos th x - sin th y, y' = sin th x + cos th y;
    spin 2: x'' = cos th x + sin th y; z unchanged). This is the "readjusted in accordance to these local phases" step that the paper asks for.
  - The angle is local data: the single-spin Bloch vectors are cos(Sigma/2)(cos th, -sin th, 0) and cos(Sigma/2)(cos th, sin th, 0). Measure them
    on calibration runs that are separate from the witness runs.
- **Gauge-free alternative: the trace-norm criterion**, ||T||_1 <= 1 for separable states, where T_ij = <s_i (x) s_j> is the 3 x 3 correlation
  matrix. It needs all nine settings and no phase knowledge. On the BMV state it is 1 + 2 sin(Sigma/2).
  - Caveat: the estimate is biased upward. On a product state the bias is +0.25, +0.075 and +0.023 at 100, 1000 and 10 000 runs per setting.
    Use it with a calibrated null. W_c has an unbiased linear estimator and is the one for the hypothesis test.
- **The variant |<sx (x) sz> + <sy (x) sy>|** is a valid witness, with product maximum 1, but it is weak here. In the paper's geometry (a = 0) it
  equals 1 - cos(Sigma), so it detects only Sigma > pi/2. At the paper's Sigma = 1 rad it reads 0.46. In the symmetric gauge it is 0 for every Sigma.
- **The proof** that a two-pair witness is valid: for unit axes a1 perp a2, b1 perp b2 and a product state with Bloch vectors u, v,
  |(u.a1)(v.b1) + (u.a2)(v.b2)| <= sqrt((u.a1)^2 + (u.a2)^2) sqrt((v.b1)^2 + (v.b2)^2) <= 1 by Cauchy-Schwarz. Convexity extends it to every
  separable state. The printed operator fails exactly because its two terms share b1 = b2 = z.

## Values at the paper's target phase, Sigma = 1 rad

| quantity | value | separable bound | entanglement shown? |
|---|---|---|---|
| printed W (a = 0) | 0.651 | sqrt2 (not 1) | no, and the bound is wrong |
| variant \|<xz> + <yy>\| (a = 0) | 0.460 | 1 | no |
| W_c (rotated axes) | 1.479 | 1 | yes |
| trace norm \|\|T\|\|_1 | 1.959 | 1 | yes (needs a calibrated null) |
| negativity | 0.240 | 0 | yes (needs tomography) |

## Under decoherence (Bridge B)

Independent dephasing at lambda per mass, under which a coherence decays as e^{-lambda t}, with the entangling rate omega (Sigma = omega t). In the
symmetric gauge the correlation matrix is T = [[q^2, 0, 0], [0, 0, q s], [0, q s, 0]] with q = e^{-lambda t} and s = sin(omega t/2). <xx> lives on
the coherences between branches that differ in both masses, and <yz>, <zy> on those that differ in one.

| criterion | entangled at some t iff omega/lambda exceeds |
|---|---|
| negativity (PPT) | **2** (reproduces `gravity_simulated.py` G2) |
| trace norm \|\|T\|\|_1 = q^2 + 2 q s | **2**, as tight as the negativity |
| W_c = q^2 + q s | **4**, from first order 1 + (omega/2 - 2 lambda) t |
| \|<yz> + <zy>\| = 2 q s | **3.8057**, with the maximum at a finite time. Closed form: u = omega/(2 lambda), the maximum is at tan(u lambda t) = u with value 2u e^{-arctan(u)/u}/sqrt(1+u^2), and the threshold solves value = 1 |
| best two-pair witness (axes re-optimised at every t) | **3.8057** = min(4, 3.8057) |

Every two-sphere geometry has omega/lambda <= 1 at the Diosi-Penrose rate (`gravity_simulated.py` G2), below every threshold here. The witness
correction does not change GUID's prediction: if decoherence at the DP rate is real, no BMV geometry of two spheres shows entanglement, whatever
gravity is. It does change what a positive result would need: a two-setting witness needs omega/lambda > 3.8, twice the margin that entanglement
itself needs.

## Runs needed (no decoherence)

With two settings and n runs each, <xx> = 1 has no shot noise on the pure state, and <yz> = sin(Sigma/2) has variance cos^2(Sigma/2)/n. So
k standard deviations need **n >= k^2 cot^2(Sigma/2)** runs per setting.

| Sigma | 3 sigma | 5 sigma |
|---|---|---|
| 1 rad (the paper's target) | 31 | 84 |
| pi/2 | 9 | 25 |
| 1e-2 | 3.6e5 | 1.0e6 |
| 1e-4 (the paper's "modest" variant) | 3.6e9 | 1.0e10 |

Monte Carlo check (20 000 simulated experiments of 2 x 84 runs at Sigma = 1): the mean estimate is 1.481 against 1 + sin(1/2) = 1.479, and the
mean significance is 5.06 sigma. At several seconds per run, the paper's modest variant at 1e-4 rad would take centuries.

## For the papers

- GUID v5.1 (`docs/quantum-gravity/`) does not quote the spin witness. It uses negativity and the PPT criterion, so nothing in the merged papers
  changes.
- GUID v6 quotes the printed witness only as checked and wrong, with the counterexample, and uses W_c (two settings) and the trace norm (nine
  settings) with the thresholds above.
- Open: whether the published PRL text prints the valid form. The later literature quotes |<sx sz> + <sy sy>|; if the PRL page becomes
  readable, re-check it and record the result here.
