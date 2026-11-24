"""The electric profile elec(c) = (1 - c)/(1 + c) as a rotation of the Riemann sphere.
Checks: its matrix is unitary (a rotation in PSU(2) = SO(3)), it is a half-turn (involution), its fixed points are
sqrt2 - 1 and -(1 + sqrt2), antipodal on the sphere, it maps the unit disk (Schur side) onto Re > 0 (Caratheodory side),
and it is the Z2 Fourier (Hadamard) transform of the pair (Z, Z_tw) read as a ratio."""
import numpy as np

M = np.array([[-1.0, 1.0], [1.0, 1.0]]) / np.sqrt(2)          # z -> (-z + 1)/(z + 1)
print("M M^dagger = identity:", np.allclose(M @ M.conj().T, np.eye(2)))
print("M^2 = identity (half-turn):", np.allclose(M @ M, np.eye(2)))


def elec(z):
    return (1 - z) / (1 + z)


fp = [np.sqrt(2) - 1, -(1 + np.sqrt(2))]
print("fixed points:", [f"{f:.12f} -> {elec(f):.12f}" for f in fp])
print("antipodal (z2 = -1/conj(z1)):", np.isclose(fp[1], -1 / np.conj(fp[0])))


def to_sphere(z):
    z = complex(z)
    d = 1 + abs(z) ** 2
    return np.array([2 * z.real / d, 2 * z.imag / d, (abs(z) ** 2 - 1) / d])


axis = to_sphere(fp[0])
rng = np.random.default_rng(1)
angles = []
for _ in range(5):
    z = complex(rng.normal(), rng.normal())
    p, q = to_sphere(z), to_sphere(elec(z))
    pp = p - axis * (p @ axis)
    qq = q - axis * (q @ axis)
    angles.append(np.degrees(np.arccos(np.clip(pp @ qq / np.linalg.norm(pp) / np.linalg.norm(qq), -1, 1))))
print("rotation angle about the fixed axis (deg):", [f"{a:.6f}" for a in angles])
print("chordal distances preserved:",
      all(np.isclose(np.linalg.norm(to_sphere(a) - to_sphere(b)), np.linalg.norm(to_sphere(elec(a)) - to_sphere(elec(b))))
          for a, b in [(0.3 + 0.2j, -0.5j), (2 + 1j, 0.1), (-0.7, 0.4 + 0.4j)]))

disk = [r * np.exp(1j * t) for r in np.linspace(0, 0.999, 40) for t in np.linspace(0, 2 * np.pi, 40)]
print("unit disk -> Re > 0:", all(elec(z).real > 0 for z in disk))

Z, Ztw = 1.0, 0.37
H = np.array([[1, 1], [1, -1]]) / np.sqrt(2)
even, odd = H @ np.array([Z, Ztw])
print(f"Hadamard on (Z, Z_tw): odd/even = {odd / even:.12f}, elec(Z_tw/Z) = {elec(Ztw / Z):.12f}")
print(f"self-dual cost -log(sqrt2 - 1) = {-np.log(fp[0]):.12f}, log(1 + sqrt2) = {np.log(1 + np.sqrt(2)):.12f}")
