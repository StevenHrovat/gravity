"""Workstream 1: one-loop (linearised, abelian) flux variance of a coarse plaquette under decimation and under the
slice-smeared blocking of ProofPhase/RouteA/Blocking.lean. Pre-registered in PREREG.md. CPU only."""
import os, json, time
os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
import numpy as np

D = 4

def unit(mu):
    e = [0] * D; e[mu] = 1; return tuple(e)

def add(x, y):
    return tuple(a + b for a, b in zip(x, y))

def scale(x, s):
    return tuple(s * a for a in x)

# a current: dict (site tuple, mu) -> coefficient (oriented along +mu)
def link_current(level, site, mu, w, cache):
    """Current of the level-`level` link at level-`level` site `site` (in level-0 units: site already scaled)."""
    key = (level, site, mu)
    if key in cache:
        return cache[key]
    if level == 0:
        cur = {(site, mu): 1.0}
        cache[key] = cur
        return cur
    h = 2 ** (level - 1)            # spacing of level-(level-1)
    out = {}
    def acc(cur, c):
        for k, v in cur.items():
            out[k] = out.get(k, 0.0) + c * v
    def step(x, nu, sign, c):
        # one level-(level-1) step from x along sign*nu; returns new site
        if sign > 0:
            acc(link_current(level - 1, x, nu, w, cache), c)
            return add(x, scale(unit(nu), h))
        y = add(x, scale(unit(nu), -h))
        acc(link_current(level - 1, y, nu, w, cache), -c)
        return y
    trans = [nu for nu in range(D) if nu != 0 and nu != mu]
    norm = 1.0 + w * 2 * len(trans)
    x = step(site, mu, +1, 1.0 / norm); step(x, mu, +1, 1.0 / norm)
    for nu in trans:
        for sgn in (+1, -1):
            c = w / norm
            x = step(site, nu, sgn, c)
            x = step(x, mu, +1, c)
            x = step(x, mu, +1, c)
            step(x, nu, -sgn, c)
    cache[key] = out
    return out

def plaquette_current(level, mu, nu, w):
    cache = {}
    ell = 2 ** level
    o = (0,) * D
    cur = {}
    def acc(c, s):
        for k, v in c.items():
            cur[k] = cur.get(k, 0.0) + s * v
    acc(link_current(level, o, mu, w, cache), 1)
    acc(link_current(level, scale(unit(mu), ell), nu, w, cache), 1)
    acc(link_current(level, scale(unit(nu), ell), mu, w, cache), -1)
    acc(link_current(level, o, nu, w, cache), -1)
    return cur

def variance(cur, L):
    J = np.zeros((D,) + (L,) * D)
    for (site, mu), v in cur.items():
        J[(mu,) + tuple(s % L for s in site)] += v
    k1 = 2 * np.pi * np.fft.fftfreq(L)
    grids = np.meshgrid(*([k1] * D), indexing="ij", sparse=True)
    khat2 = sum(4 * np.sin(g / 2) ** 2 for g in grids)
    tot = 0.0
    for mu in range(D):
        Jk = np.fft.fftn(J[mu])
        a = np.abs(Jk) ** 2
        with np.errstate(divide="ignore", invalid="ignore"):
            r = np.where(khat2 > 0, a / khat2, 0.0)
        tot += r.sum()
    return tot / L ** D

def main():
    t0 = time.time()
    res = {}
    for w in (0.0, 0.5, 1.0):
        for (mu, nu, name) in ((0, 1, "time-space"), (1, 2, "space-space")):
            row = {}
            for level in (1, 2, 3, 4):
                ell = 2 ** level
                L = 4 * ell if level < 4 else 3 * ell
                cur = plaquette_current(level, mu, nu, w)
                row[ell] = variance(cur, L)
                print(f"w={w} {name} ell={ell} L={L} sigma2={row[ell]:.5f}  ({time.time()-t0:.0f}s)", flush=True)
            res[f"w={w} {name}"] = row
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "selfenergy.json"), "w") as f:
        json.dump(res, f, indent=1)

if __name__ == "__main__":
    main()
