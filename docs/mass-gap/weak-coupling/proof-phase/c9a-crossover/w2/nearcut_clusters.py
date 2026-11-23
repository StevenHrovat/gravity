"""Clusters of near-cut plaquettes inside the box (CPU; DICHOTOMY.md section 8.6). For each saved chain-A snapshot of a
sampled box: the box plaquettes with |q0| < delta (q0 = (1/2) tr U_p), connected when they are faces of a common cube (the
adjacency of a dual sheet); the largest cluster as a fraction of all box plaquettes, and whether some cluster touches two
opposite faces of the box (a spanning near-cut cluster, along which a sheet would be nearly free).

Usage: py nearcut_clusters.py runs/narrow/launch_b*.json [--out runs/narrow/nearcut_clusters.json]
"""
import argparse
import json
import math

import numpy as np

import constrained as C
from lever_proxy import launch_snapshots, prod_seq


def find(par, i):
    while par[i] != i:
        par[i] = par[par[i]]
        i = par[i]
    return i


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("launches", nargs="+")
    ap.add_argument("--out", default="runs/narrow/nearcut_clusters.json")
    a = ap.parse_args()
    geo = C.Geometry(6)
    F, off, ell = geo.F, geo.off, geo.ell
    base = geo.plaq[:, 0] // 4
    x = np.stack(np.unravel_index(base, (F,) * 4), axis=-1) - off             # box coordinates of the base site
    dirs = []
    for m in range(4):
        for n in range(m + 1, 4):
            dirs.append((m, n))
    # the plane of each plaquette, in the order Geometry built them (per site: (0,1),(0,2),(0,3),(1,2),(1,3),(2,3))
    npl = len(geo.plaq)
    plane = np.array([dirs[i % 6] for i in range(npl)])
    # cubes containing each plaquette: for rho not in plane, base x and x - e_rho
    cube_members = {}
    for i in range(npl):
        m, n = plane[i]
        for rho in range(4):
            if rho in (m, n):
                continue
            tri = tuple(sorted((m, n, rho)))
            for s in (0, -1):
                cb = list(x[i])
                cb[rho] += s
                cube_members.setdefault((tuple(cb), tri), []).append(i)
    cubes = [v for v in cube_members.values() if len(v) > 1]
    res = {}
    for js in a.launches:
        for (tag, beta, ycl, pool, j, p, U, Y) in launch_snapshots(js):
            if ycl != "sampled":
                continue
            q0 = prod_seq(U, geo.plaq, geo.plaqd)[..., 0]
            for name, delta in (("dP6", math.log(6) / (2 * beta)), ("0.1", 0.1)):
                near = np.abs(q0) < delta
                par = list(range(npl))
                for mem in cubes:
                    nm = [k for k in mem if near[k]]
                    for k in nm[1:]:
                        ra, rb = find(par, nm[0]), find(par, k)
                        if ra != rb:
                            par[ra] = rb
                roots = {}
                for k in np.nonzero(near)[0]:
                    roots.setdefault(find(par, k), []).append(k)
                largest = max((len(v) for v in roots.values()), default=0)
                span = False
                for v in roots.values():
                    xs = x[v]
                    if any(xs[:, d].min() == 0 and xs[:, d].max() == ell - 1 for d in range(4)):
                        span = True
                        break
                r = res.setdefault(f"{beta}/{name}", dict(n=0, frac_near=0.0, largest_frac=0.0, spanning=0, delta=delta))
                r["n"] += 1
                r["frac_near"] += float(near.mean())
                r["largest_frac"] += largest / npl
                r["spanning"] += int(span)
    out = {k: dict(delta=v["delta"], snapshots=v["n"], frac_near=v["frac_near"] / v["n"],
                   largest_cluster_frac=v["largest_frac"] / v["n"], frac_snapshots_spanning=v["spanning"] / v["n"])
           for k, v in res.items()}
    json.dump(out, open(a.out, "w"), indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
