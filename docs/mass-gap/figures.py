"""Draw the figures of README.md from the stored results (results/*.json). Static PNGs for the repository page.

Colours: categorical slot 1 (blue) for gluons, SU(2); slot 2 (orange) for light, U(1); grey for references. Validated as a pair (CVD
Delta E 24.7, normal-vision 33.6, contrast >= 3:1 on the light surface). Every series is also direct-labelled.
"""

import json
import math
import os

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")
OUT = os.path.join(HERE, "figures")

SURFACE, INK, INK2, MUTED, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#8a8984", "#e6e5e0"
GLUON, LIGHT = "#2a78d6", "#eb6834"


def style(ax):
    ax.set_facecolor(SURFACE)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    for s in ("left", "bottom"):
        ax.spines[s].set_color(MUTED)
    ax.tick_params(colors=INK2, labelsize=9)
    ax.grid(True, color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)


def fig(w=7.2, h=4.0, n=1):
    f, axs = plt.subplots(1, n, figsize=(w, h), dpi=150)
    f.patch.set_facecolor(SURFACE)
    axs = [axs] if n == 1 else list(axs)
    for a in axs:
        style(a)
    return f, axs


def load(name):
    with open(os.path.join(RES, name)) as f:
        return json.load(f)


def zoom_figure():
    su2 = load("mk_su2_d4.json")["SU(2) d=4"]
    u1 = load("mk_u1_d4_tail.json")["U(1) d=4"]
    f, (ax,) = fig()
    ax.axhspan(0, 1.0, color="#f0efec", zorder=0)
    ax.text(0.3, 0.45, "strong coupling: a gap is a theorem here (on the lattice)", color=INK2, fontsize=8.5)
    for b in ("6.0", "10.0"):
        rows = su2[b]
        ax.plot([r["step"] for r in rows], [r["beta_hk"] for r in rows], color=GLUON, lw=2, marker="o", ms=4)
    ax.text(12.3, su2["10.0"][-1]["beta_hk"], "gluons, SU(2):\n−0.25 per layer", color=INK, fontsize=8.5, va="center")
    for b in ("1.5", "2.0"):
        rows = u1[b][:13]
        ax.plot([r["step"] for r in rows], [r["beta_hk"] for r in rows], color=LIGHT, lw=2, marker="o", ms=4)
    ax.text(12.3, u1["2.0"][12]["beta_hk"], "light, U(1):\nstalls (−3×10⁻¹¹)", color=INK, fontsize=8.5, va="center")
    ax.annotate("layer 1 only reshapes the weight\n(a one-off jump, not flow)", xy=(1, 9.87), xytext=(2.0, 10.75), color=INK2, fontsize=8,
                arrowprops=dict(arrowstyle="-", color=MUTED, lw=0.8))
    ax.set_xlim(-0.3, 15.8)
    ax.set_ylim(0, 11.9)
    ax.set_xlabel("zoom-out layer (each halves the resolution)", color=INK2, fontsize=9)
    ax.set_ylabel("coupling β = 4/g²  (higher = weaker)", color=INK2, fontsize=9)
    ax.set_title("The layer-by-layer zoom-out (Migdal–Kadanoff, d = 4)", color=INK, fontsize=10.5, loc="left")
    f.tight_layout()
    f.savefig(os.path.join(OUT, "zoom.png"), facecolor=SURFACE)


def drift_figure():
    u1 = load("mk_u1_d4_tail.json")["U(1) d=4"]
    su2 = load("mk_su2_d4.json")["SU(2) d=4"]
    f, (ax,) = fig()
    xs = [rows[-1]["beta_hk"] for rows in u1.values()]
    ys = [float(rows[-1]["drop"]) for rows in u1.values()]
    pts = [(r["beta_hk"], float(r["drop"])) for rows in su2.values() for r in rows[3:] if r["drop"] is not None]
    ax.scatter([p[0] for p in pts], [p[1] for p in pts], color=GLUON, s=22, zorder=3, edgecolor=SURFACE, linewidth=1)
    ax.scatter(xs, ys, color=LIGHT, s=30, zorder=3, edgecolor=SURFACE, linewidth=1)
    fx = [0.8 + 0.02 * i for i in range(80)]
    ax.plot(fx, [20.5 * math.exp(-14.41 * x) for x in fx], color=MUTED, lw=1.2, ls="--")
    ax.axhline(0.2575, color=MUTED, lw=1, ls=":")
    ax.text(5.6, 0.75, "dotted: one-loop asymptotic freedom, 0.2575", color=INK2, fontsize=8)
    ax.text(5.6, 0.045, "gluons, SU(2): 0.22 to 0.29 per layer", color=INK, fontsize=8.5)
    ax.text(2.45, 3e-11, "light, U(1): ≈ 20·e^(−14.4 β)\n(on the real lattice: exactly 0)", color=INK, fontsize=8.5)
    ax.set_yscale("log")
    ax.set_xlim(0.5, 10.5)
    ax.set_ylim(1e-13, 2)
    ax.set_xlabel("coupling β where the layer starts", color=INK2, fontsize=9)
    ax.set_ylabel("strengthening per layer (Δβ)", color=INK2, fontsize=9)
    ax.set_title("Per layer: gluons move steadily, light barely moves", color=INK, fontsize=10.5, loc="left")
    f.tight_layout()
    f.savefig(os.path.join(OUT, "drift.png"), facecolor=SURFACE)


def lattice_figures():
    path = os.path.join(RES, "lattice_summary.json")
    if not os.path.exists(path):
        return
    with open(path) as fh:
        res = json.load(fh)
    teper = [(2.2, 0.467, 1.44, 0.08), (2.3, 0.3687, 1.216, 0.023), (2.4, 0.2686, 0.959, 0.020), (2.5, 0.1834, 0.660, 0.022),
             (2.6, 0.1326, 0.51, 0.03), (2.7, 0.1005, 0.39, 0.03), (2.85, 0.0636, 0.229, 0.012)]
    su2 = [r for r in res if r.get("group", "SU(2)") == "SU(2)"]
    f, (a1, a2) = fig(w=8.6, h=3.8, n=2)
    a1.errorbar([t[0] for t in teper], [t[2] for t in teper], yerr=[t[3] for t in teper], fmt="s", color=MUTED, ms=4, lw=1, capsize=0)
    a1.errorbar([r["beta"] for r in su2], [r["a_m_0pp"][0] for r in su2], yerr=[r["a_m_0pp"][1] for r in su2], fmt="o",
                color=GLUON, ms=5, lw=1.5, capsize=0)
    a1.set_title("Gap in grid steps: shrinks to zero", color=INK, fontsize=10, loc="left")
    a1.set_xlabel("β (finer grid →)", color=INK2, fontsize=9)
    a1.set_ylabel("a · m(0⁺⁺)", color=INK2, fontsize=9)
    a1.set_ylim(0, 1.6)
    ratio_t = [(t[0], t[2] / t[1]) for t in teper]
    a2.axhspan(3.74 - 0.12, 3.74 + 0.12, color="#f0efec")
    a2.text(2.21, 3.93, "continuum 3.74 ± 0.12 (Teper)", color=INK2, fontsize=8)
    a2.plot([t[0] for t in ratio_t], [t[1] for t in ratio_t], "s", color=MUTED, ms=4)
    a2.errorbar([r["beta"] for r in su2], [r["m_0pp_over_sqrt_sigma"][0] for r in su2],
                yerr=[r["m_0pp_over_sqrt_sigma"][1] for r in su2], fmt="o", color=GLUON, ms=5, lw=1.5, capsize=0)
    a2.set_ylim(0, 5)
    a2.set_title("Gap in real units: stays", color=INK, fontsize=10, loc="left")
    a2.set_xlabel("β (finer grid →)", color=INK2, fontsize=9)
    a2.set_ylabel("m(0⁺⁺) / √σ", color=INK2, fontsize=9)
    for a in (a1, a2):
        a.set_xlim(2.15, 2.9)
    a1.text(2.62, 1.3, "■ Teper 1998\n● this code", color=INK2, fontsize=8)
    f.tight_layout()
    f.savefig(os.path.join(OUT, "gap.png"), facecolor=SURFACE)

    u1 = [r for r in res if r.get("group") == "U(1)"]
    if u1:
        f, (ax,) = fig(w=7.2, h=3.8)
        ps = [0.02 * i for i in range(1, 80)]
        ax.plot(ps, [2 * math.asinh(math.sin(p / 2)) for p in ps], color=MUTED, lw=1.2, ls="--")
        ax.text(1.05, 1.15, "massless: E → 0 with p", color=INK2, fontsize=8)
        for r in u1:
            L = r["L"]
            col = LIGHT if r["beta"] > 1.01 else INK2
            for nm in (1, 2):
                E, dE = r[f"E_p{nm}_used"]
                if math.isfinite(E):
                    ax.errorbar([2 * math.pi * nm / L], [E], yerr=[dE if math.isfinite(dE) else 0], fmt="o" if r["beta"] > 1.01 else "^",
                                color=col, ms=5, lw=1.5, capsize=0)
        ax.text(0.15, 2.45, "▲ U(1), β = 0.8 (confined phase): gapped", color=INK, fontsize=8.5)
        ax.text(0.15, 2.2, "● U(1), β = 1.2 (Coulomb phase): light", color=INK, fontsize=8.5)
        ax.set_xlim(0, 1.7)
        ax.set_ylim(0, 2.7)
        ax.set_xlabel("momentum p (lattice units)", color=INK2, fontsize=9)
        ax.set_ylabel("energy of the lightest state", color=INK2, fontsize=9)
        ax.set_title("The photon test, on the lattice", color=INK, fontsize=10.5, loc="left")
        f.tight_layout()
        f.savefig(os.path.join(OUT, "photon.png"), facecolor=SURFACE)


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    zoom_figure()
    drift_figure()
    lattice_figures()
    print("figures written to", OUT)
