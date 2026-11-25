"""Refutation check of F_e(L) > 2 c(L) from saved 16^4 configurations (ONEBOX-CHECK.md, plan fixed before running). CPU only.

R(L) = L * dE_f^up - log(1 + S(L)),  S(L) = sum over momentum orbits of mult * exp(-L * dE^up(orbit)),
an upper bound on F_e(L) - 2 c(L) for chains of cross-section 16^3. Refuted at L if R(L) < 0 with one-sided bounds.

Usage: py onebox_check.py [--out runs/onebox_check.json]
"""
import argparse
import json
import math

import numpy as np

import coarse_test as T

T95, T99 = 2.353, 4.541
NT = 4  # correlator lags 0..3


def spatial_plane_sum(q, tau):
    """Sum of q0 over the 3 plaquette planes not containing axis tau; q: (L,L,L,L,6)."""
    idx = [i for i, (m, n) in enumerate(T.PLANES) if tau not in (m, n)]
    return q[..., idx].sum(axis=-1)


def polyakov_trace(U, k):
    """1/2 tr of the Polyakov loop along axis k, starting at x_k = 0; returns array over the other 3 axes (order kept)."""
    Uk = U[k]
    P = np.take(Uk, 0, axis=k)
    for j in range(1, Uk.shape[k]):
        P = T.qm(P, np.take(Uk, j, axis=k))
    return P[..., 0]


def lag_corr(A, sub=None):
    """A: (Lt, ...) complex or real slice operators; returns C[d] = mean_t Re(A[t] conj(A[t+d])) summed over trailing axes."""
    if sub is not None:
        A = A - sub
    out = []
    for d in range(NT):
        B = np.roll(A, -d, axis=0)
        out.append(np.mean(np.real(A * np.conj(B)), axis=0))
    return np.stack(out)  # (NT, ...)


def orbit_keys(L):
    n = np.arange(L)
    m = np.minimum(n, L - n)
    keys = {}
    for a in range(L):
        for b in range(L):
            for c in range(L):
                keys.setdefault(tuple(sorted((m[a], m[b], m[c]))), []).append((a, b, c))
    return keys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="runs/onebox_check.json")
    ap.add_argument("--sig", type=float, default=2.0, help="significance required of C(t), C(t+1) (plan: 2)")
    ap.add_argument("--rule", choices=["plan", "post"], default="plan", help="plan: pre-registered floors; post: RULES.md universal floor (POST-HOC)")
    args = ap.parse_args()
    result = {}
    for beta in (2.3, 3.5):
        confs = np.load(f"runs/conf_b{beta}.npz")["U"]
        nc, L = confs.shape[0], confs.shape[2]
        keys = orbit_keys(L)
        klist = sorted(keys)
        # per config: orbit correlators (NT, n_orbits) and per-sample arrays for the floor; Polyakov correlator (NT,)
        Cn_conf, Cp_conf = [], []
        samp_n, samp_p = [], []
        zero_means = []
        # first pass: p = 0 slice means for the vacuum subtraction (global over all configs and orientations)
        slices = []
        for ci in range(nc):
            q = T.plaquettes(confs[ci])
            per_o = []
            for tau in range(4):
                A = np.moveaxis(spatial_plane_sum(q, tau), tau, 0)  # (t, x1, x2, x3)
                per_o.append(np.fft.fftn(A, axes=(1, 2, 3)))
            slices.append(per_o)
            zero_means.append(np.mean([F[:, 0, 0, 0].real.mean() for F in per_o]))
        for ci in range(nc):
            others = [zero_means[j] for j in range(nc)]
            vac = float(np.mean(others))
            co, so = [], []
            for F in slices[ci]:
                F = F.copy()
                F[:, 0, 0, 0] -= vac
                C = lag_corr(F)  # (NT, L, L, L)
                Co = np.stack([np.mean([C[:, a, b, c] for (a, b, c) in keys[kk]], axis=0) for kk in klist], axis=1)
                co.append(Co)
                # per time-origin samples for the floor (orbit-averaged products at each t)
                per_t = []
                for d in range(NT):
                    B = np.roll(F, -d, axis=0)
                    prod = np.real(F * np.conj(B))  # (t, L, L, L)
                    per_t.append(np.stack([np.mean([prod[:, a, b, c] for (a, b, c) in keys[kk]], axis=0) for kk in klist], axis=1))
                so.append(np.stack(per_t))  # (NT, t, n_orb)
            Cn_conf.append(np.mean(co, axis=0))
            samp_n.append(np.concatenate(so, axis=1))
            # Polyakov
            cp, sp = [], []
            for tau in range(4):
                for k in range(4):
                    if k == tau:
                        continue
                    Pk = polyakov_trace(confs[ci], k)  # over axes != k, in original order
                    t_ax = tau if tau < k else tau - 1
                    Pk = np.moveaxis(Pk, t_ax, 0).reshape(L, -1).sum(axis=1)  # (t,)
                    cp.append(lag_corr(Pk))
                    sp.append(np.stack([Pk * np.roll(Pk, -d) for d in range(NT)]))
            Cp_conf.append(np.mean(cp, axis=0))
            samp_p.append(np.concatenate(sp, axis=1))
        Cn_conf = np.stack(Cn_conf)  # (nc, NT, n_orb)
        Cp_conf = np.stack(Cp_conf)  # (nc, NT)
        samp_n = np.concatenate(samp_n, axis=1)  # (NT, N, n_orb)
        samp_p = np.concatenate(samp_p, axis=1)  # (NT, N)

        def meff_bounds(Cc, samples):
            """Cc: (nc, NT); samples: (NT, N). Returns dict with the chosen t, m_eff, sigma, or None."""
            mean = Cc.mean(axis=0)
            jk = np.stack([np.delete(Cc, i, axis=0).mean(axis=0) for i in range(nc)])
            sjk = np.sqrt((nc - 1) / nc * np.sum((jk - jk.mean(axis=0)) ** 2, axis=0))
            sfl = samples.std(axis=1, ddof=1) / math.sqrt(samples.shape[1])
            sC = np.maximum(sjk, sfl) if args.rule == "plan" else sjk
            for t in (1, 0):
                if mean[t + 1] > args.sig * sC[t + 1] and mean[t] > args.sig * sC[t]:
                    m = math.log(mean[t] / mean[t + 1])
                    mj = []
                    ok = True
                    for i in range(nc):
                        if jk[i, t] <= 0 or jk[i, t + 1] <= 0:
                            ok = False
                            break
                        mj.append(math.log(jk[i, t] / jk[i, t + 1]))
                    s_jk = math.sqrt((nc - 1) / nc * np.sum((np.array(mj) - np.mean(mj)) ** 2)) if ok else float("inf")
                    s_fl = math.sqrt((sC[t] / mean[t]) ** 2 + (sC[t + 1] / mean[t + 1]) ** 2)
                    if args.rule == "plan":
                        return dict(t=t, m=m, sigma=max(s_jk, s_fl), sigma_jk=s_jk, sigma_floor=s_fl)
                    # statistical floor: the jackknife of m_eff itself (= the delta method with the C(t), C(t+1) covariance);
                    # s_nocov (delta method without the covariance) is reported, not used: it ignores the strong positive correlation
                    s_dm = math.sqrt((sjk[t] / mean[t]) ** 2 + (sjk[t + 1] / mean[t + 1]) ** 2)
                    s_res = 1.0 / L  # resolution floor 1/T, T = observed Euclidean time extent (16)
                    return dict(t=t, m=m, sigma=max(s_jk, s_res), sigma_jk=s_jk, sigma_nocov=s_dm, sigma_res=s_res)
            return None

        flux = meff_bounds(Cp_conf, samp_p)
        orbs = []
        for j, kk in enumerate(klist):
            b = meff_bounds(Cn_conf[:, :, j], samp_n[:, :, j])
            orbs.append(dict(key=[int(x) for x in kk], mult=len(keys[kk]), bound=b))
        n_used = sum(1 for o in orbs if o["bound"] is not None)
        res = dict(flux_corr_mean=[float(x) for x in Cp_conf.mean(axis=0)],
                   flux_corr_conf=[[float(x) for x in r] for r in Cp_conf], flux=flux, n_orbits=len(orbs), n_orbits_used=n_used,
                   n_states_used=int(sum(o["mult"] for o in orbs if o["bound"] is not None)), R={})
        for name, tq in (("central", 0.0), ("95", T95), ("99", T99)):
            Rl = {}
            for Lb in range(1, 9):
                S = sum(o["mult"] * math.exp(-Lb * (o["bound"]["m"] + tq * o["bound"]["sigma"])) for o in orbs if o["bound"] is not None)
                if flux is None:
                    Rl[Lb] = dict(R=None, LdEf=None, logS1=math.log1p(S))
                    continue
                dEf = flux["m"] + tq * flux["sigma"]
                Rl[Lb] = dict(R=Lb * dEf - math.log1p(S), LdEf=Lb * dEf, logS1=math.log1p(S))
            res["R"][name] = Rl
        low = sorted([o for o in orbs if o["bound"] is not None], key=lambda o: o["bound"]["m"])[:6]
        res["lowest_orbits"] = low
        result[str(beta)] = res
        print(f"beta {beta}: flux {flux}; orbits used {n_used}/{len(orbs)} ({res['n_states_used']} states)", flush=True)
        for o in low:
            print("   orbit", o["key"], o["mult"], {k: round(v, 3) for k, v in o["bound"].items()}, flush=True)
        print("   Polyakov C(t) per config:", [[round(x, 3) for x in r] for r in res["flux_corr_conf"]], flush=True)
        for Lb in range(1, 9):
            r = res["R"]
            if r["central"][Lb]["R"] is None:
                print(f"   L={Lb}: no flux bound; log(1+S) central {r['central'][Lb]['logS1']:.2f} 95% {r['95'][Lb]['logS1']:.2f} 99% {r['99'][Lb]['logS1']:.2f}", flush=True)
                continue
            print(f"   L={Lb}: R central {r['central'][Lb]['R']:.2f}  95% {r['95'][Lb]['R']:.2f}  99% {r['99'][Lb]['R']:.2f} "
                  f"(L dEf {r['95'][Lb]['LdEf']:.2f}, log(1+S) {r['95'][Lb]['logS1']:.2f})", flush=True)
    json.dump(result, open(args.out, "w"), indent=1)


if __name__ == "__main__":
    main()
