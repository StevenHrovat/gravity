# BYPASS.md 2: the cheapest Z2 label. An explicit bare configuration with exactly one plaquette at tr < 0
# (tau = -1, an "act"-like plaquette): rotate the four bonds of p about one axis by +-phi/4 so that p gets phi > pi/2
# and each of the 20 other plaquettes through those bonds gets phi/4. Cost in units of beta = 4/g^2 per (1 - tr/2).
# Compared with the threshold the count of labels on the coarse 2-skeleton needs: b * A > 2 (b = 2 * 11*2/(48 pi^2)).
import numpy as np
b = 2 * 22 / (48 * np.pi ** 2)
for phi in (np.pi / 2 + 1e-3, np.pi / 2 + 0.1):
    cost_beta = (1 - np.cos(phi)) + 20 * (1 - np.cos(phi / 4))
    A = 4 * cost_beta                      # action in units of 1/g^2
    print(f'phi = {phi:.4f}: cost = {cost_beta:.4f} beta = {A:.3f}/g^2;  b*A = {b*A:.3f} (needs > 2 for the 2-skeleton, '
          f'> 1 for the 1-skeleton)')
print(f'b = {b:.4f}; closed bubble around one bond (6 plaquettes at the equator): A = 24, b*A = {24*b:.3f}')
