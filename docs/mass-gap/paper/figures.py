"""Figures for the paper, from the stored results only.

    python figures.py        (run from docs/mass-gap/paper/)

fig-ttl.png     TTL * sqrt(sigma) against (a sqrt(sigma))^2, with the pre-registered constant fit and the post-hoc a^2 fit
fig-vortex.png  Creutz ratios (full, centre-projected, vortex-removed) against R, with the torelon string tension
"""
import json
import os

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

RES = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "results")
OUT = os.path.dirname(os.path.abspath(__file__))
plt.rcParams.update({"font.size": 10, "figure.dpi": 150})


def ttl():
    d = json.load(open(os.path.join(RES, "ttl_summary.json")))
    fit = json.load(open(os.path.join(RES, "ttl_extrapolation.json")))
    x = np.array([p["a_sqrt_sigma"][0] ** 2 for p in d])
    xe = np.array([2 * p["a_sqrt_sigma"][0] * p["a_sqrt_sigma"][1] for p in d])
    y = np.array([p["ttl_sqrt_sigma"][0] for p in d])
    ye = np.array([p["ttl_sqrt_sigma"][1] for p in d])
    w = 1 / ye ** 2
    const = np.sum(w * y) / np.sum(w)
    fig, ax = plt.subplots(figsize=(5.2, 3.4))
    ax.axhspan(1 / 3.74 - 0.009, 1 / 3.74 + 0.009, color="0.85", label="continuum value 1/3.74 (Teper)")
    ax.axhline(const, color="C1", ls="--", lw=1, label=f"constant fit (pre-registered): p = 0.014")
    xs = np.linspace(0, 0.13, 50)
    ax.plot(xs, fit["c"][0] + fit["k"][0] * xs, color="C0", lw=1, label=f"$c + k\\,(a\\sqrt{{\\sigma}})^2$ (post hoc): p = {fit['p']:.2f}")
    ax.errorbar(x, y, yerr=ye, xerr=xe, fmt="o", color="k", ms=4, capsize=2)
    for xi, yi, yei, p in zip(x, y, ye, d):
        ax.annotate(f"β={p['beta']}", (xi, yi + yei), textcoords="offset points", xytext=(0, 4), fontsize=7.5, ha="center")
    ax.set_xlabel("$(a\\sqrt{\\sigma})^2$  (grid spacing squared, in string-tension units)")
    ax.set_ylabel("TTL $\\cdot\\sqrt{\\sigma}$ = $\\sqrt{\\sigma}/m_{0^{++}}$")
    ax.set_xlim(-0.003, 0.135)
    ax.legend(fontsize=7.5, loc="upper left", frameon=False)
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig-ttl.png"))


def vortex():
    p = os.path.join(RES, "vortex_summary.json")
    if not os.path.exists(p):
        print("no vortex_summary.json yet; fig-vortex.png skipped")
        return
    runs = json.load(open(p))
    fig, axes = plt.subplots(1, len(runs), figsize=(5.2 * len(runs) / 1.6, 3.2), squeeze=False)
    for ax, r in zip(axes[0], runs):
        Rs = [3, 4]
        for key, lab, c, off in (("chi_full", "full", "k", -0.06), ("chi_proj", "centre-projected", "C0", 0),
                                 ("chi_removed", "vortices removed", "C3", 0.06)):
            v = np.array([r["R"][str(R)][key] for R in Rs])
            ax.errorbar(np.array(Rs) + off, v[:, 0], yerr=v[:, 1], fmt="o", color=c, ms=4, capsize=2, label=lab)
        if "followup" in r:
            v = np.array([r["followup"]["R"]["5"][k] for k in ("chi_proj", "chi_removed")])
            ax.errorbar([5, 5.06], v[:, 0], yerr=v[:, 1], fmt="o", color="none", ms=0, capsize=2)
            ax.errorbar([5], v[0, 0], yerr=v[0, 1], fmt="o", color="C0", ms=4, capsize=2)
            ax.errorbar([5.06], v[1, 0], yerr=v[1, 1], fmt="o", color="C3", ms=4, capsize=2)
            s = r["followup"]["sigma_a2"]
            ax.axhspan(s[0] - s[1], s[0] + s[1], color="0.85", label="$\\sigma a^2$ from torelons")
        ax.axhline(0, color="0.6", lw=0.6)
        ax.set_ylim(-0.03, 0.27)
        ax.set_title(f"β = {r['beta']}, {r['L']}$^4$", fontsize=9)
        ax.set_xlabel("loop size R")
        ax.set_xticks([3, 4, 5])
        ax.set_ylabel("Creutz ratio χ(R)")
    axes[0][-1].legend(fontsize=7, frameon=False, loc="upper right")
    fig.tight_layout()
    fig.savefig(os.path.join(OUT, "fig-vortex.png"))


if __name__ == "__main__":
    ttl()
    vortex()
