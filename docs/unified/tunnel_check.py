"""Two nodes bound by tunnelling: the electric factor is the tunnelling gap.
Two states L, R (two nodes), tunnelling amplitude t (H = -t X), Euclidean time T. The plain trace Z = tr e^{-TH} and the
twisted trace Z_tw = tr(X e^{-TH}) (X swaps the two nodes: the centre flip) give c = Z_tw / Z, and the encoder's electric
factor (1 - c)/(1 + c) equals e^{-T * gap} exactly, with gap = 2t the splitting between the bound (symmetric) state
(|L> + |R>)/sqrt 2 and the antisymmetric one: the Hadamard pair of the half-turn."""
import numpy as np

X = np.array([[0.0, 1.0], [1.0, 0.0]])
for t, T in ((0.3, 4.0), (0.05, 10.0), (1.0, 0.5), (0.2, 30.0)):
    H = -t * X
    w, v = np.linalg.eigh(H)
    P = v @ np.diag(np.exp(-T * w)) @ v.T
    Z, Ztw = np.trace(P), np.trace(X @ P)
    c = Ztw / Z
    elec = (1 - c) / (1 + c)
    gap = w[1] - w[0]
    print(f"t={t:<5} T={T:<5} c={c:.9f}  elec={elec:.9f}  exp(-T gap)={np.exp(-T * gap):.9f}  gap={gap:.4f} (2t={2 * t:.4f})")
    print(f"    ground state = {np.round(v[:, 0], 9)} (symmetric, both nodes bound to one root)")
