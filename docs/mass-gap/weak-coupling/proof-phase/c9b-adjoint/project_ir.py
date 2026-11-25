"""Projection of the decisive IR run from the GPU timing job (TIMING.md "Setup as run"; written before the job's data).
    py project_ir.py timing_job.npz timing_progress.jsonl
Rule (c9a-crossover/w2/PROJECTION.md section 8): central = projected x 1.33, band x [0.9, 1.9] (content-spread floor), +25 % drift for
runs much longer than the timed unit; any other beta: transfer factor 1.0 +- 0.3 on the per-trajectory cost, and T(beta) from that beta's
own pre-step. Sample sizes per class: PREREG-GPU.md 6d/6e. K = 8 independent replicas per ensemble (6b)."""
import json
import math
import sys

import numpy as np

import ir_condlaw as cl

TAU_TBP = 1.8  # T-B' (b = 4, 12^4): fallback if the timing job does not resolve tau_int (marked)
K = 8
N_EFF = {"ss": 2.7e3, "ts": 2.7e4, "rect": 1.3e6}  # per ensemble, summed over replicas (6d, 6e)


def main(npz, prog):
    d = np.load(npz)
    s_traj = float(np.median(d["s_traj"])) if len(d["s_traj"]) else float("nan")
    n = len(d["s_traj"])
    acc = float(np.mean(d["acc"])) if n else float("nan")
    lines = [json.loads(l) for l in open(prog)]
    t_bg = next((l["elapsed"] for l in lines if l.get("stage") == "background done"), float("nan"))
    t_tune_end = max((l["elapsed"] for l in lines if l.get("stage") == "tune"), default=float("nan"))
    tau_vx = max((cl.tauint(d["vx"][:, 0, i]) for i in range(4)), default=float("nan")) if n >= 8 else float("nan")
    tau_S = cl.tauint(d["S"]) if n >= 8 and "S" in d.files else float("nan")
    tau_m = np.nanmax([tau_vx, tau_S]) if not (math.isnan(tau_vx) and math.isnan(tau_S)) else float("nan")
    resolved = (not math.isnan(tau_m)) and tau_m < n / 4
    tau = tau_m if resolved else TAU_TBP
    t_eff = s_traj * 2 * tau  # B = 1
    T_tune = t_tune_end - t_bg  # mass + force timing + tuning of this one ensemble
    out = {"n_production": n, "s_traj": s_traj, "acc": acc, "eps": float(d["eps"]), "nleap": int(d["nleap"]),
           "s_force": float(d["s_force"]), "t_background_s": t_bg, "T_tune_s": T_tune,
           "tau_vx": tau_vx, "tau_S": tau_S, "tau_resolved": bool(resolved),
           "tau_used": tau, "tau_source": "timing job" if resolved else "T-B' (b = 4) fallback, marked", "t_eff_s": t_eff}

    def ens_cost(cls, moved=True):
        return T_tune + K * ((20 if moved else 0) + 20) * s_traj + N_EFF[cls] * t_eff

    # stages (PREREG-GPU sections 3, 6 with 6d/6f): moves w (unmoved), -w, wR, w e^{dX}
    def stage(nbg, plaq_kappas, with_rect, rect_bg=None):
        tot = 0.0
        for _ in range(nbg):
            tot += t_bg
            for cls, mult in (("ss", 1), ("ts", 2)):  # classes: s<-ss; s<-ts and t<-ts
                for moved in (False, True, True, True):
                    tot += mult * plaq_kappas * ens_cost(cls, moved)
        if with_rect:
            for _ in range(rect_bg or nbg):
                for _c in range(6):
                    for moved in (False, True, True, True):
                        tot += ens_cost("rect", moved)
        return tot / 3600
    stages = {
        "A (5 bg; plaquette x 3 kappa; rectangles x 1)": stage(5, 3, True),
        "A without rectangles": stage(5, 3, False),
        "B (7 more bg, same content)": stage(7, 3, True),
    }
    rows = {}
    for k, h in stages.items():
        long = h > 2 * (30 / 60)
        c = h * 1.33 * (1.25 if long else 1.0)
        rows[k] = {"projected_h": h, "central_h": c, "band_h": [h * 0.9, h * 1.9 * (1.25 if long else 1.0)]}
    out["stages_gpu_hours"] = rows
    out["per_ensemble_h"] = {cls: ens_cost(cls) / 3600 for cls in N_EFF}
    print(json.dumps(out, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
