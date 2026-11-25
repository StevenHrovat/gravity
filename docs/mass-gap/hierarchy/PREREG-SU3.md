# Pre-registration: is the layer-by-layer flow driven by the carriers' self-charge? (2026-11-21, before computing)

**The owner's reading (2026-11-21).** In DMP terms the strong and weak forces are IM, the two-signed medium (a message passes a door only
with both signatures, C19), and electromagnetism is not: it is payload, which the gate does not read and which acts only on the system it
reaches. In gauge theory the matching property is the carriers' own charge: a gluon carries a colour and an anticolour (the adjoint
representation), a photon carries none. Its size is one number, the adjoint Casimir C_A: N for SU(N), 0 for U(1).

**The claim tested.** The zoom-out flow of the Migdal–Kadanoff recursion (README §5) is driven by C_A: per layer, 1/g² changes by
2·b₀·ln 2 with b₀ = 11·C_A/(48π²), so the change of 1/g² per layer is proportional to C_A, and U(1) (C_A = 0) does not flow.

**Prediction, fixed before the SU(3) run.** In the standard normalisation β = 2N/g², the per-layer drop of β at weak coupling is
4·N·b₀·ln 2: 0.2575 for SU(2) (the tree gave 0.252, 2 % below) and **0.5794 for SU(3)** (C_A = 3, N = 3). Per unit of 1/g² the ratio
SU(3) : SU(2) is C_A ratio = **1.5**; in β it is 2.25.

- **Pass:** the SU(3) tree's per-layer drop at weak coupling (start β = 15 and 24, read after the reshaping step) divided by the SU(2)
  tree's at the same 1/g² (start β = 10 and 16) is 2.25 within 5 %.
- **Fail:** outside 10 %. Between 5 and 10 %: reported as tension.
- **Validation first:** the new method (pointwise bond moving on the eigenvalue torus, character coefficients by Weyl integration)
  reproduces the committed SU(2) numbers (`results/mk_su2_d4.json`) to 3 digits; otherwise nothing is reported.

What this does and does not show: that the tree's flow is proportional to the self-charge is expected from one-loop physics; the test
anchors the DMP reading quantitatively in our own computation. It is not new physics and not a step of a proof.
