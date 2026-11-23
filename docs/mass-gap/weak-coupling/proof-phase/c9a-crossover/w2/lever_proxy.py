"""Cheap single-link proxy for the two-level influence-bad classification (INFLUENCE-BAD.md), on the saved snapshots of the
narrow W2 run. CPU only (numpy).

For each saved fine configuration (chain A box links at T/2 and at the end, a sample of K(Y, .) at the unperturbed outside):
* single-link law at link x: von Mises-Fisher with the field F(x) of the sampler's proposal (Wilson staple + constraint with
  the normaliser linearised at the current state: the first-order approximation of the single-link conditional law);
* influence of link y on link x: c_xy = max over 4 replacements of U_y (U_y -> R U_y, R in {i s1, i s2, i s3, -1}) of the
  Pinsker bound sqrt(KL/2) (<= 1) between vMF(F(x)) and vMF(F(x) + dF), dF the exact change of the linear part of F(x)
  (Wilson staples, and the constraint paths with the linearisation point Z = Y - lambda Phi_hat frozen);
  y ranges over every link F(x) depends on linearly: the staple links and the prefix/suffix links of its constraint paths;
* per local box B (each of the 81 blocks of the box, and each of the 16 aligned two-block cubes):
    kappa_B = (1/|B|) sum_{x in B} sum_{y not in B} c_xy     (outside influence per box link: the one-box sum with
                                                               single-link influences; same normalisation as R_low)
    D_B     = max_{y in B} sum_{x in B, x != y} c_xy          (Dobrushin column sum inside B)
* field-size classification for comparison: a block is bad at threshold t if one of its fine plaquettes or one of its block
  plaquettes (from Y) has 1 - (1/2) tr > t.

This is a proxy (single-link, first-order, Pinsker), not the pre-registered kappa_b (box influence from coupled chains); it ranks
blocks and locates candidates for the full computation, which needs a separate OK.

Usage: py lever_proxy.py runs/narrow/launch_b2.3_s101.json [more launch JSONs ...] [--max_snaps N] [--out lever_proxy.json]
"""
import argparse
import json
import math
import sys

import numpy as np

import constrained as C

ROTS = np.array([[0.0, 1.0, 0.0, 0.0], [0.0, 0.0, 1.0, 0.0], [0.0, 0.0, 0.0, 1.0], [-1.0, 0.0, 0.0, 0.0]])


def qm(a, b):
    return C.be_qmul_np(a, b)


def cj(a):
    return a * C.CONJ


def lz_np(be, a):
    return be.log_z(a)


def kl_vmf(be, F1, F2):
    """KL(vMF(F1) || vMF(F2)) on S^3 (Haar-normalised), arrays (..., 4)."""
    a1 = np.linalg.norm(F1, axis=-1)
    a2 = np.linalg.norm(F2, axis=-1)
    A = be.dlog_z(a1)
    mean = (A / np.maximum(a1, 1e-300))[..., None] * F1
    return np.maximum(np.sum(mean * (F1 - F2), axis=-1) - be.log_z(a1) + be.log_z(a2), 0.0)


def gather(U, lids, dags):
    g = U[lids]
    return np.where(dags[..., None].astype(bool), g * C.CONJ, g)


def prod_seq(U, lids, dags):
    out = gather(U, lids[..., 0], dags[..., 0])
    for k in range(1, lids.shape[-1]):
        out = qm(out, gather(U, lids[..., k], dags[..., k]))
    return out


class Proxy:
    def __init__(self, ell=6, kappa=16.0):
        self.geo = C.Geometry(ell)
        self.geo.to_device(np)
        self.be = C.Backend(False, 1)
        self.kappa = kappa
        g = self.geo
        self.dyn = g.dyn_lids
        self.dynpos = {int(l): i for i, l in enumerate(g.dyn_lids)}
        F, off, ell_ = g.F, g.off, g.ell
        # local boxes: blocks (side 2) and aligned two-block cubes (side 4) inside the box
        site_of = self.dyn // 4
        coords = np.stack(np.unravel_index(site_of, (F,) * 4), axis=-1) - off      # 0..ell-1
        self.blocks = []
        nb = ell_ // 2
        for b in np.ndindex(*(nb,) * 4):
            self.blocks.append(np.all(coords // 2 == np.array(b), axis=-1))
        self.cubes = []
        for b in np.ndindex(*(nb - 1,) * 4):
            lo = 2 * np.array(b)
            self.cubes.append(np.all((coords >= lo) & (coords < lo + 4), axis=-1))
        self.block_coords = np.array(list(np.ndindex(*(nb,) * 4)))

    def fields_and_terms(self, U, Y):
        """Baseline proposal field F(x) for every dynamic link x, and the list of linear terms (x, y, dag_y, A, B, scale) with
        dF = scale * f(A (dU_y^dag?) B) as described in the module docstring."""
        g, be, k = self.geo, self.be, self.kappa
        Fx = np.zeros((len(self.dyn), 4))
        terms = []
        U2 = U[None, None]
        Y2 = Y[None, None]
        S = C.PairSampler(be, g, 0.0, k, U2, Y2)
        for c in g.classes:
            lid = c["lid"]
            xi = np.array([self.dynpos[int(l)] for l in lid])
            # Wilson part (beta applied by the caller): staples V = s0 s1 s2; F_W = beta conj(sum V)
            st = gather(U, c["stp"], c["stpd"])                    # (n, 6, 3, 4)
            W = np.sum(qm(qm(st[:, :, 0], st[:, :, 1]), st[:, :, 2]), axis=1)
            # constraint part with the linearisation point Z
            Pre = prod_seq(U, c["e_pre"], c["e_pred"])               # (n, E, 4)
            Suf = prod_seq(U, c["e_suf"], c["e_sufd"])
            Yl = Y[c["e_l"]]
            Phi = S.phi(c["e_l"])[0, 0]                               # (n, E, 4)
            r = np.linalg.norm(Phi, axis=-1)
            lam = be.dlog_z(k * r)
            Z = Yl - (lam / np.maximum(r, 1e-12))[..., None] * Phi
            dagx = c["e_dag"].astype(bool)[..., None]
            w = (k * c["e_c"] * c["e_mask"])[..., None]
            M = qm(qm(Suf, cj(Z)), Pre)
            Fc = np.sum(np.where(dagx, M, cj(M)) * w, axis=1)
            Fx[xi] = np.zeros(4)                                      # beta added later: store W and Fc separately
            terms.append(dict(xi=xi, W=W, Fc=Fc, st=st, stp=c["stp"], stpd=c["stpd"], Pre=Pre, Suf=Suf, Z=Z, dagx=dagx,
                              w=w, e_pre=c["e_pre"], e_pred=c["e_pred"], e_suf=c["e_suf"], e_sufd=c["e_sufd"]))
        return terms

    def influences(self, U, Y, beta):
        """Sparse influence triples (x_dyn_index, y_lid, c_xy)."""
        be = self.be
        xs, ys, cs = [], [], []
        for t in self.fields_and_terms(U, Y):
            xi = t["xi"]
            F0 = beta * cj(t["W"]) + t["Fc"]                          # (n, 4)
            n = len(xi)
            # Wilson neighbours: staple s, position k
            st = t["st"]
            for kpos in range(3):
                a = np.tile(np.array([1.0, 0, 0, 0]), (n, 6, 1))
                for j in range(kpos):
                    a = qm(a, st[:, :, j])
                b = np.tile(np.array([1.0, 0, 0, 0]), (n, 6, 1))
                for j in range(kpos + 1, 3):
                    b = qm(b, st[:, :, j])
                ylid = t["stp"][:, :, kpos]
                dag = t["stpd"][:, :, kpos].astype(bool)[..., None]
                u = U[ylid]
                best = np.zeros((n, 6))
                for R in ROTS:
                    un = qm(R, u)
                    du = np.where(dag, cj(un) - cj(u), un - u)
                    dF = beta * cj(qm(qm(a, du), b))
                    kl = kl_vmf(be, np.broadcast_to(F0[:, None], dF.shape), F0[:, None] + dF)
                    best = np.maximum(best, np.minimum(1.0, np.sqrt(kl / 2)))
                xs.append(np.repeat(xi, 6))
                ys.append(ylid.reshape(-1))
                cs.append(best.reshape(-1))
            # constraint neighbours in prefix and suffix
            for side in ("pre", "suf"):
                L = t["e_" + side]
                D = t["e_" + side + "d"]
                E = L.shape[1]
                el = gather(U, L, D)                                  # (n, E, 3, 4)
                for kpos in range(3):
                    a = np.tile(np.array([1.0, 0, 0, 0]), (n, E, 1))
                    for j in range(kpos):
                        a = qm(a, el[:, :, j])
                    b = np.tile(np.array([1.0, 0, 0, 0]), (n, E, 1))
                    for j in range(kpos + 1, 3):
                        b = qm(b, el[:, :, j])
                    ylid = L[:, :, kpos]
                    valid = (ylid != self.geo.NL) & (t["w"][..., 0] != 0)
                    dag = D[:, :, kpos].astype(bool)[..., None]
                    u = U[ylid]
                    best = np.zeros((n, E))
                    for R in ROTS:
                        un = qm(R, u)
                        du = np.where(dag, cj(un) - cj(u), un - u)
                        dpart = qm(qm(a, du), b)                       # change of the prefix or suffix product
                        if side == "pre":
                            dM = qm(qm(t["Suf"], cj(t["Z"])), dpart)
                        else:
                            dM = qm(qm(dpart, cj(t["Z"])), t["Pre"])
                        dF = np.where(t["dagx"], dM, cj(dM)) * t["w"]
                        kl = kl_vmf(be, np.broadcast_to(F0[:, None], dF.shape), F0[:, None] + dF)
                        best = np.maximum(best, np.minimum(1.0, np.sqrt(kl / 2)))
                    best = np.where(valid, best, 0.0)
                    xs.append(np.repeat(xi, E))
                    ys.append(ylid.reshape(-1))
                    cs.append(best.reshape(-1))
        x = np.concatenate(xs)
        y = np.concatenate(ys)
        c = np.concatenate(cs)
        keep = c > 0
        return x[keep], y[keep], c[keep]

    def box_numbers(self, x, y, c, masks):
        """kappa_B and D_B for local boxes given as boolean masks over the dynamic links."""
        ydyn = np.array([self.dynpos.get(int(v), -1) for v in y])
        out_k, out_d = [], []
        for m in masks:
            inx = m[x]
            iny = (ydyn >= 0) & m[np.maximum(ydyn, 0)]
            kap = c[inx & ~iny].sum() / m.sum()
            sel = inx & iny & (x != ydyn)
            col = np.zeros(len(self.dyn))
            np.add.at(col, ydyn[sel], c[sel])
            out_k.append(kap)
            out_d.append(col[m].max() if m.any() else 0.0)
        return np.array(out_k), np.array(out_d)

    def fieldsize(self, U, Y, ts=(0.5, 1.0, 1.5)):
        """Per block: max over its fine plaquettes (base site in the block) and its block plaquettes of 1 - (1/2) tr."""
        g = self.geo
        pl = prod_seq(U, g.plaq, g.plaqd)[..., 0]                     # (nplaq,)
        base = g.plaq[:, 0] // 4
        coords = np.stack(np.unravel_index(base, (g.F,) * 4), axis=-1) - g.off
        bidx = np.ravel_multi_index(tuple((coords // 2).T), (g.ell // 2,) * 4)
        fine = np.zeros((g.ell // 2) ** 4)
        np.maximum.at(fine, bidx, 1.0 - pl)
        # block plaquettes from Y: coarse links (y, mu) with base y in the box
        site = {(tuple(int(v) for v in y), mu): i for i, (y, mu) in enumerate(g.cl_site)}
        E = np.eye(4, dtype=int)
        coarse = np.zeros_like(fine)
        for (y, mu), i in site.items():
            if not all(g.off <= v < g.off + g.ell for v in y):
                continue
            for nu in range(mu + 1, 4):
                k1 = (tuple(np.add(y, 2 * E[mu])), nu)
                k2 = (tuple(np.add(y, 2 * E[nu])), mu)
                k3 = (y, nu)
                if k1 in site and k2 in site and k3 in site:
                    p = qm(qm(qm(Y[i], Y[site[k1]]), cj(Y[site[k2]])), cj(Y[site[k3]]))[0]
                    b = np.ravel_multi_index(tuple((np.array(y) - g.off) // 2), (g.ell // 2,) * 4)
                    coarse[b] = max(coarse[b], 1.0 - p)
        worst = np.maximum(fine, coarse)
        return fine, coarse, worst


def launch_snapshots(js):
    """Yield (tag, beta, yclass, U_frame, Y) for every saved snapshot of a launch JSON."""
    J = json.load(open(js))
    z = np.load(J["npz"])
    confs, beta = C.load_confs(f"runs/conf_b{J['beta']}.npz")
    geo = C.Geometry(J["ell"])
    pairs = z["snap_pairs"]
    for tag in ("snap_mid", "snap_end"):
        S = z[tag]
        if S.size == 0:
            continue
        for k, p in enumerate(pairs):
            m = [mm for mm in J["instances"] if mm["first_pair"] <= p < mm["first_pair"] + 80][0]
            j = J["instances"].index(m)
            Uf = C.frame_links(confs[m["conf"]], geo, tuple(m["shift"]))
            if m["yclass"] == "A6":
                Uf = C.a6_outside(geo, Uf)
            Uf[geo.dyn_lids] = S[k].astype(np.float64)
            yield (tag, J["beta"], m["yclass"], m["pool"], j, int(p), Uf, z["Y_inst"][j].astype(np.float64))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("launches", nargs="+")
    ap.add_argument("--max_snaps", type=int, default=0)
    ap.add_argument("--out", default="runs/narrow/lever_proxy.json")
    a = ap.parse_args()
    P = Proxy()
    rows = []
    import time
    t0 = time.time()
    for js in a.launches:
        n = 0
        for (tag, beta, ycl, pool, j, p, U, Y) in launch_snapshots(js):
            x, y, c = P.influences(U, Y, beta)
            kb, db = P.box_numbers(x, y, c, P.blocks)
            kc, dc = P.box_numbers(x, y, c, P.cubes)
            fine, coarse, worst = P.fieldsize(U, Y)
            rows.append(dict(launch=js, tag=tag, beta=beta, yclass=ycl, pool=pool, job=j, pair=p,
                             kappa_block=kb.tolist(), D_block=db.tolist(), kappa_cube=kc.tolist(), D_cube=dc.tolist(),
                             fine_worst=fine.tolist(), coarse_worst=coarse.tolist()))
            n += 1
            if a.max_snaps and n >= a.max_snaps:
                break
        print(f"{js}: {n} snapshots, {time.time() - t0:.0f} s so far", flush=True)
    json.dump(dict(rows=rows, seconds=time.time() - t0), open(a.out, "w"))
    print(f"wrote {a.out}: {len(rows)} snapshots in {time.time() - t0:.0f} s")


if __name__ == "__main__":
    main()
