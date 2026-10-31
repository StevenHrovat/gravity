# GUID and the Standard Model: statements fixed before the tests

This file fixes, before any fit or comparison is run, what GUID says about the Standard Model and how each statement will be scored. It
is committed before the scripts `standard_model.py` and `exotic_hadrons.py` exist, so the repository history shows that the statements
were not tuned to the data. Every statement will be reported with its verdict, including those that fail.

The statements come from Part I of the GUID v6 paper (`docs/guid-v6/part1.tex`), Sections "The physical reading", "Cosmology" and "Matter
in the existence frame", with Hypotheses 1', 4 and 6'. SM6 adds one new hypothesis, H8, which is marked as such.

## SM1. The spin ladder

Elementary quanta have spin 0, 1/2 or 1. The spin-2 wave is the classical frame's own, so there is no graviton as a quantum. There is no
elementary spin-3/2 or higher-spin quantum.

- **Test:** searches for elementary spin-3/2 states (gravitinos, superpartners in general), higher-spin resonances and quantum gravitons
  (Kaluza-Klein gravitons).
- **Scoring:** a discovered elementary spin-3/2 or spin-2 quantum refutes SM1. Null searches leave it *holds as a reading*, since the
  Standard Model makes the same statement for its own content.

## SM2. The Higgs vacuum grants every elementary rest mass (Hypothesis 1')

1. **Couplings.** Every massive elementary particle couples to the Higgs boson in proportion to its mass, y_f = sqrt2 m_f / v for fermions
   and g_hVV = 2 m_V^2 / v for the weak bosons. All coupling modifiers are kappa = 1.
2. **No other source of elementary rest mass.** Neutrino masses are Dirac masses from Yukawa couplings. There is no Majorana mass, so
   neutrinoless double-beta decay is absent (m_bb = 0) and lepton number is conserved.
3. **Massless bosons.** The photon and the gluons are massless.
4. **Weak boson masses.** At tree level m_W = g v / 2 and m_Z = m_W / cos theta_W (rho = 1).

**Tests:** for 1, the ATLAS and CMS Higgs coupling measurements, as a mass-coupling relation and as kappa values; for 2, the 0vbb
half-life bounds, with N_eff as a side test; for 4, the measured W and Z masses with the Standard Model's loop corrections. 3 is a reading
of the Standard Model.

## SM3. The information scalar couples only to the Maxwell term (Hypothesis 4)

Of the couplings, only alpha varies. The proton-to-electron mass ratio mu varies only through the electromagnetic parts of the proton and
electron masses.

- **Prediction:** R = (dln mu / dt) / (dln alpha / dt) is of order 1e-3 to 1e-2. Unification models give R of about -20 to -50.
- **Side prediction:** the scalar's contribution to the lepton anomalous magnetic moments is negligible at |lambda| < 3.1e-5.
- **Tests:** the bounds on the variation of mu (molecular spectra, clocks) against the bounds on alpha, and the electron and muon g-2.

## SM4. No unification within causality (Hypothesis 6')

The Standard Model couplings, run with Standard Model content alone, do not meet at one point. SM1 excludes superpartners. Any proton decay
comes only from a unification before the start.

- **Tests:** two-loop running from the measured couplings, with the minimal supersymmetric extension shown for contrast; proton-decay
  bounds.

## SM5. The electroweak split

The split is a smooth crossover near 160 GeV for the measured Higgs mass. Alpha is born near 1/128 at the Z mass and runs to 1/137 at low
energy.

- **Tests:** alpha(m_Z) from alpha(0) and the measured vacuum polarisation; lattice results on the crossover.

## SM6. Hadrons as trees of dualities (new Hypothesis H8, from Axioms 1 and 3)

Axiom 1 makes every part a Duality of two halves, and Axiom 3 makes every layer a tree rooted at its Duality. Read for the strong force,
**every hadron is a binary tree of two colour-conjugate halves, each internal node a bound duality**:

- meson: (q)(qbar);
- baryon: (q)[qq];
- tetraquark: [qq][qbar qbar] (compact) or (q qbar)(q qbar) (molecular);
- pentaquark: [qq][qq]qbar or (qqq)(q qbar).

All predictions come from one constituent-quark model with a colour-spin (chromomagnetic) interaction. It is fitted to conventional
ground-state mesons and baryons only and then applied without refitting:

- **(a) Compact exotics.** The masses of the compact two-half states: T_cc+ ([cc][ubar dbar]), T_bb- ([bb][ubar dbar]), T_bc, the fully heavy
  [cc][cbar cbar], and the hidden-charm and hidden-charm-strange pentaquarks. Each mass is compared with the measured mass where one
  exists. T_bb- and any other unobserved state are recorded as live predictions, with their binding relative to the lowest two-meson
  threshold.
- **(b) Molecular exotics.** Where both halves are colour singlets (a molecular duality), the state lies near the two-hadron threshold. The
  observed exotic hadrons are tested for threshold proximity against a null of random placement, with the look-elsewhere count stated.
- **(c) Partners.** The diquark-tree reading predicts partner states: isospin and charge partners, and spin multiplets. These are compared
  with searches. A predicted partner that searches exclude is reported as a failed prediction.

**Scoring:** by pull against the measured mass, with the model's own uncertainty taken from the spread of its fit to conventional hadrons
(stated before comparison). Generic statements are *holds as a reading*. Specific masses are *holds*, *refuted* or *live*.

## Rules for both scripts

- **Data.** Every measured value is verified against its source (arXiv text or the publisher), with the source cited per value.
- **Determinism.** Seeds are fixed and BLAS is pinned to one thread.
- **Choices.** Every choice made after seeing a comparison is listed in the results under "choices made after seeing the data".
- **Outcome.** A failed prediction is a result, not an error. The scripts exit 0 when their own numerical checks pass, whatever the
  physics verdicts.
