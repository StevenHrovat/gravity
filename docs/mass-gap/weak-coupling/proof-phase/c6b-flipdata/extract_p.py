"""c6b-flipdata: read p(L) off existing flux (torelon) data, by the rules of PREREG.md.

Read-only on every input. CPU only. Run: CUDA_VISIBLE_DEVICES=-1 python -I extract_p.py
Writes p_table.csv, p_plot.svg, extract_p.log next to this file.
"""
import json, math, os, re
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
MG = os.path.abspath(os.path.join(HERE, "..", "..", ".."))  # docs/mass-gap
R = os.path.join(MG, "results")
PHI = math.log(1 + math.sqrt(2))   # F* of the duality F = -ln tanh(F/2)

def load(p):
    with open(os.path.join(MG, p)) as f:
        return json.load(f)

# ---------- scale: a sqrt(sigma) per beta from the TTL scan (A) ----------
ttl = load("results/ttl_summary.json")
SCALE = {r["beta"]: tuple(r["a_sqrt_sigma"]) for r in ttl}

def pfun(z, dz, g=1.0):
    rho = g * math.exp(-z)
    p = 0.5 * (1 - rho)
    dp = 0.5 * rho * dz
    # F_tw = -ln tanh(z/2) (g = 1 only); derivative dz / sinh z
    Ftw = -math.log(math.tanh(z / 2)) if z > 0 else float("inf")
    dF = dz / math.sinh(z) if z > 0 else float("nan")
    return rho, p, dp, Ftw, dF

rows = []
def add(src, group, beta, L, E, dE, tstar, E_next=None):
    a, da = SCALE[beta]
    x = L * a
    dx = L * da
    z, dz = L * E, L * dE
    rho, p, dp, Ftw, dF = pfun(z, dz)
    zlo = z - 2 * dz
    rho_hi = math.exp(-zlo)
    plo = 0.5 * (1 - rho_hi)
    p_g2 = 0.5 * (1 - 2 * rho)       # S1 band
    p_g05 = 0.5 * (1 - 0.5 * rho)
    z_next = None if E_next is None else (L * E_next[0], L * E_next[1])
    rows.append(dict(src=src, group=group, beta=beta, L=L, x=x, dx=dx, E=E, dE=dE, tstar=tstar,
                     z=z, dz=dz, rho=rho, p=p, dp=dp, Ftw=Ftw, dF=dF, plo=plo, zlo=zlo,
                     p_g2=p_g2, p_g05=p_g05, z_next=z_next))

# A: TTL scan
for r in ttl:
    ts = r["t_torelon"]
    nxt = r["torelon_meff"][ts + 1] if ts + 1 < len(r["torelon_meff"]) else None
    add("A", "primary", r["beta"], r["L"], r["torelon_mass"][0], r["torelon_mass"][1], ts, nxt)

# B: Luescher scan (beta = 2.3), plateau points only
lu = load("results/luscher_summary.json")
for L, E, dE, ts in lu["points"]:
    add("B", "primary", 2.3, int(L), E, dE, ts)

# C: lattice_summary SU(2) rows, effective mass at t = 1 -> 2 (index 1), no plateau rule
for r in load("results/lattice_summary.json"):
    if "group" in r:
        continue
    ti = r["t_index_used"]
    E, dE = r["torelon_meff"][ti]
    add("C", "secondary", r["beta"], r["L"], E, dE, ti)

rows.sort(key=lambda r: (r["group"] != "primary", r["x"]))
prim = [r for r in rows if r["group"] == "primary"]
sec = [r for r in rows if r["group"] == "secondary"]

out = []
def P(s=""):
    out.append(s)
    print(s)

P("== extract_p.py (c6b-flipdata) ==")
P("scales a sqrt(sigma) per beta (TTL scan): " + ", ".join(f"{b}: {v[0]:.4f}({v[1]:.4f})" for b, v in SCALE.items()))
P("")
hdr = "| src | beta | L | x = L sqrt(sigma) | a E_e | z = L E_e | p = (1-e^-z)/2 | F_tw | p_lo (z-2dz) | p band g=2..1/2 | z(t*+1) |"
P(hdr)
P("|" + "---|" * 11)
for r in rows:
    zn = "-" if r["z_next"] is None else f"{r['z_next'][0]:.2f}({r['z_next'][1]:.2f})"
    P(f"| {r['src']} | {r['beta']} | {r['L']} | {r['x']:.2f}({r['dx']:.2f}) | {r['E']:.4f}({r['dE']:.4f}) | "
      f"{r['z']:.2f}({r['dz']:.2f}) | {r['p']:.5f}({r['dp']:.5f}) | {r['Ftw']:.2e}({r['dF']:.1e}) | "
      f"{r['plo']:.4f} | {r['p_g2']:.4f}..{r['p_g05']:.4f} | {zn} |")

# ---------- verdict rules ----------
P("")
P("== verdicts (PREREG section 4) ==")
near = [(r["beta"], r["L"], round(r["x"], 2), r["plo"] >= 0.45) for r in prim]
P("NEAR HALF (p_lo >= 0.45) per primary point: " + str(near))
all_near = all(n[3] for n in near)
P(f"  -> all primary points near half: {all_near}")

falls = []
for b in sorted(set(r["beta"] for r in prim)):
    pts = sorted([r for r in prim if r["beta"] == b], key=lambda r: r["L"])
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            a, c = pts[i], pts[j]
            thr = max(2 * math.hypot(a["dp"], c["dp"]), 0.02)
            if c["p"] < a["p"] - thr:
                falls.append((b, a["L"], c["L"]))
P(f"FALLS pairs (same beta): {falls if falls else 'none'}")
pairs_checked = sum(1 for b in set(r['beta'] for r in prim)
                    for _ in [0] if len([r for r in prim if r['beta'] == b]) > 1)
P(f"  (betas with >= 2 primary points: {[b for b in sorted(set(r['beta'] for r in prim)) if len([r for r in prim if r['beta']==b])>1]})")

# trend: z = s x^2 - c, weighted
X = np.array([r["x"] ** 2 for r in prim])
Z = np.array([r["z"] for r in prim])
W = np.array([1.0 / r["dz"] ** 2 for r in prim])
A_ = np.vstack([X, -np.ones_like(X)]).T
cov = np.linalg.inv(A_.T @ (A_ * W[:, None]))
coef = cov @ (A_.T @ (W * Z))
s, c = coef
ds, dc = math.sqrt(cov[0, 0]), math.sqrt(cov[1, 1])
res = Z - A_ @ coef
chi2 = float(np.sum(W * res ** 2))
dof = len(prim) - 2
P(f"TREND fit z = s x^2 - c on primary points: s = {s:.3f} +- {ds:.3f}, c = {c:.2f} +- {dc:.2f}, chi2/dof = {chi2:.1f}/{dof}")
P(f"  GROWS (s > 0 at > 2 sigma): {s > 2 * ds}   (Luescher form would be s = 1, c = pi/3 = {math.pi/3:.3f})")
# unweighted check (weights dominated by the tiny errors at small x)
coef_u = np.linalg.lstsq(A_, Z, rcond=None)[0]
P(f"  unweighted check: s = {coef_u[0]:.3f}, c = {coef_u[1]:.2f}")

pmin = min(r["plo"] for r in prim)
x_min = min(r["x"] for r in prim)
x_max = max(r["x"] for r in prim)
against = [r for r in prim if r["x"] >= 2 and r["plo"] < 0.25]
floor_ok = (not against) and (not falls) and (s > 2 * ds)
P(f"FLOOR ON MEASURED RANGE x in [{x_min:.2f}, {x_max:.2f}]: p_min (smallest p_lo) = {pmin:.4f}; "
  f"points with p_lo < 0.25 and x >= 2: {len(against)}; verdict floor-on-range = {floor_ok}")
low = [r for r in prim if r["x"] < 2]
P(f"counted points with x < 2: {len(low)} -> transition region (x ~ 1.4) {'HAS DATA' if low else 'NO DATA'}")

# secondary vs primary overlap
for r in sec:
    for q in prim:
        if q["beta"] == r["beta"] and q["L"] == r["L"]:
            dd = abs(r["z"] - q["z"]) / math.hypot(r["dz"], q["dz"])
            P(f"secondary C (beta {r['beta']}, L {r['L']}) vs primary: |dz|/sigma = {dd:.2f}")
P("secondary C points p: " + ", ".join(f"({r['beta']},{r['L']}): {r['p']:.4f}" for r in sec))

# S2 check: E(t*+1) vs E(t*) for A
P("S2 check (A): z at t* and t*+1:")
for r in rows:
    if r["z_next"] is not None:
        d = (r["z"] - r["z_next"][0]) / math.hypot(r["dz"], r["z_next"][1])
        P(f"  beta {r['beta']} L {r['L']}: z(t*) = {r['z']:.2f}({r['dz']:.2f}), z(t*+1) = {r['z_next'][0]:.2f}({r['z_next'][1]:.2f}), diff/sigma = {d:+.2f}")

# alternative scales for the x axis: shift in x, and whether any verdict changes
alt = {2.3: [0.363, 0.371], 2.4: [0.273], 2.5: [0.199]}
P("alternative scales: x moves by <= 6 %; p_lo >= 0.45 depends only on z, not on x; the only x-dependent statement is x >= 2 for the "
  "'against' test: smallest primary x with the largest alternative scale shift -> " +
  f"{min(r['x'] for r in prim):.2f} (x0.94 .. x1.06 = {0.94*x_min:.2f} .. {1.06*x_min:.2f}); all primary points stay at x >= 2: "
  f"{all(0.94 * r['x'] >= 2 for r in prim)}")

# marks
P("")
P("== marks and comparison curves ==")
p_star = 0.5 * (1 - math.exp(-PHI))
P(f"self-dual level F_e = F_tw = ln(1+sqrt2) = {PHI:.4f}: p = {p_star:.4f}")
xL = math.sqrt(PHI + math.pi / 3)
xN = math.sqrt((math.pi / 3 + math.sqrt((math.pi / 3) ** 2 + 4 * PHI)) / 2)
P(f"curve S crossing z = F*: Luescher x = {xL:.3f}; Nambu-Goto (z = x sqrt(x^2 - pi/3)) x = {xN:.3f}  (r4-conjw quotes 1.39 to 1.55 for these)")
P("1/T_c mark: x = 1.41 (T_c/sqrt(sigma) = 0.71, recalled value)")

# curve V: vortex density
vs = load("results/vortex_summary.json")
dens = {}
for r in vs:
    sg = r["followup"]["sigma_a2"][0]
    dens[r["beta"]] = r["vortex_density"] / sg
P("vortex density / sigma a^2 (E): " + ", ".join(f"beta {b}: {v:.3f}" for b, v in dens.items()))
nbar = float(np.mean(list(dens.values())))

def p_V(x):
    return 0.5 * (1 - math.exp(-2 * nbar * x * x))

def p_S(x, kind):
    z = x * x - math.pi / 3 if kind == "L" else (x * math.sqrt(x * x - math.pi / 3) if x * x > math.pi / 3 else 0.0)
    return 0.5 * (1 - math.exp(-z)) if z > 0 else 0.0

P("curve values p at x = 0.7, 1.0, 1.4, 2.0, 2.8, 4.0:")
for name, fn in [("V (independent vortices)", p_V), ("S Luescher", lambda x: p_S(x, "L")), ("S Nambu-Goto", lambda x: p_S(x, "NG"))]:
    P(f"  {name}: " + ", ".join(f"{fn(x):.3f}" for x in (0.7, 1.0, 1.4, 2.0, 2.8, 4.0)))

# F: finite subgroups
ft = load("weak-coupling/attempts/r3-monotone/frozen_twist.json")
P("")
P("== exact controls F (beta = infinity, every box size) ==")
for g in ft["results"]:
    F = g["F_inf"]
    pinf = 0.0 if (F is None or (isinstance(F, float) and math.isinf(F))) else 1 / (1 + math.exp(F))
    P(f"  {g['group']}: Hom_tw/Hom = {g['hom_tw']}/{g['hom4']}  F_inf = {F}  p_inf = {pinf:.4f}")

# G: photon
P("")
P("== photon control G (U(1), beta = 1.1, twisted box, flux along twist) ==")
log = open(os.path.join(MG, "weak-coupling/attempts/r4-actnumber/runs-gpu/photon_gate.log")).read()
ph = []
for m in re.finditer(r"u1_b1\.1_L(\d+)\.npz\s+z = ([0-9.]+) \+- ([0-9.]+).*?\[(counted|not counted[^\]]*)\]", log):
    L, z, dz, st = int(m.group(1)), float(m.group(2)), float(m.group(3)), m.group(4)
    q = math.exp(-z)
    n = np.arange(-30, 31)
    num = float(np.sum(q ** (n[n % 2 != 0] ** 2.0)))
    den = float(np.sum(q ** (n[n % 2 == 0] ** 2.0)))
    rho_t = num / den
    ph.append((L, z, dz, st))
    P(f"  L {L}: z = {z:.3f}({dz:.3f}) [{st}]  one-state p = {(1-q)/2:.3f}({q*dz/2:.3f});  rotor-tower rho = {rho_t:.3f}, p = {(1-rho_t)/2:.3f}")
zs = [p[1] for p in ph if p[3] == "counted"]
P(f"  counted: z mean {np.mean(zs):.3f}; photon one-state p range {min((1-math.exp(-z))/2 for z in zs):.3f} .. {max((1-math.exp(-z))/2 for z in zs):.3f}")
P("  -> the photon has p = const > 0 (z frozen), i.e. it also has a floor; the floor alone does not separate it from SU(2).")

# ---------- csv, md, svg ----------
with open(os.path.join(HERE, "p_table.csv"), "w") as f:
    f.write("src,group,beta,L,x,dx,aE,daE,z,dz,rho,p,dp,Ftw,dFtw,p_lo,p_g2,p_g05\n")
    for r in rows:
        f.write(",".join(str(r[k]) for k in ["src", "group", "beta", "L", "x", "dx", "E", "dE", "z", "dz", "rho", "p", "dp", "Ftw", "dF", "plo", "p_g2", "p_g05"]) + "\n")

W_, H_ = 760, 440
ml, mr, mt, mb = 60, 20, 20, 50
def X_(x): return ml + (x / 5.0) * (W_ - ml - mr)
def Y_(p): return mt + (1 - p / 0.55) * (H_ - mt - mb)
s_ = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W_} {H_}" font-family="sans-serif" font-size="11">',
      f'<rect width="{W_}" height="{H_}" fill="white"/>']
for pv in (0, 0.1, 0.2, 0.3, 0.4, 0.5):
    s_.append(f'<line x1="{ml}" x2="{W_-mr}" y1="{Y_(pv):.1f}" y2="{Y_(pv):.1f}" stroke="#ddd"/><text x="{ml-6}" y="{Y_(pv)+4:.1f}" text-anchor="end">{pv:.1f}</text>')
for xv in range(0, 6):
    s_.append(f'<line x1="{X_(xv):.1f}" x2="{X_(xv):.1f}" y1="{mt}" y2="{H_-mb}" stroke="#eee"/><text x="{X_(xv):.1f}" y="{H_-mb+16}" text-anchor="middle">{xv}</text>')
s_.append(f'<text x="{(ml+W_-mr)/2}" y="{H_-8}" text-anchor="middle">L sqrt(sigma)</text>')
s_.append(f'<text x="14" y="{(mt+H_-mb)/2}" transform="rotate(-90 14 {(mt+H_-mb)/2})" text-anchor="middle">p = (1 - e^(-F_e))/2</text>')
s_.append(f'<line x1="{X_(0.5*1):.1f}" x2="{W_-mr}" y1="{Y_(0.5):.1f}" y2="{Y_(0.5):.1f}" stroke="#444" stroke-dasharray="4 3"/>')
s_.append(f'<line x1="{ml}" x2="{W_-mr}" y1="{Y_(p_star):.1f}" y2="{Y_(p_star):.1f}" stroke="#a60" stroke-dasharray="2 3"/><text x="{W_-mr-4}" y="{Y_(p_star)-4:.1f}" text-anchor="end" fill="#a60">F_e = F_tw (p = 0.293)</text>')
s_.append(f'<line x1="{X_(1.41):.1f}" x2="{X_(1.41):.1f}" y1="{mt}" y2="{H_-mb}" stroke="#c00" stroke-dasharray="5 3"/><text x="{X_(1.41)+3:.1f}" y="{mt+12}" fill="#c00">1/T_c ~ 1.4</text>')
s_.append(f'<rect x="{X_(1.39):.1f}" y="{mt}" width="{X_(1.55)-X_(1.39):.1f}" height="{H_-mt-mb}" fill="#c00" opacity="0.10"/><text x="{X_(1.55)+3:.1f}" y="{mt+26}" fill="#c00">self-dual 1.39-1.55 (prediction)</text>')
def poly(fn, col, dash, xs):
    pts = " ".join(f"{X_(x):.1f},{Y_(fn(x)):.1f}" for x in xs)
    return f'<polyline points="{pts}" fill="none" stroke="{col}" stroke-width="1.5" stroke-dasharray="{dash}"/>'
xs = [0.05 * i for i in range(1, 101)]
s_.append(poly(p_V, "#888", "6 3", xs))
s_.append(poly(lambda x: p_S(x, "L"), "#06c", "3 3", [x for x in xs if x >= 1.03]))
s_.append(poly(lambda x: p_S(x, "NG"), "#0a8", "3 3", [x for x in xs if x >= 1.03]))
cols = {2.3: "#000", 2.4: "#c50", 2.5: "#07a", 2.6: "#6a0", 2.7: "#a0a"}
for r in rows:
    cx, cy = X_(r["x"]), Y_(r["p"])
    col = cols[r["beta"]]
    s_.append(f'<line x1="{cy and X_(r["x"]-r["dx"]):.1f}" x2="{X_(r["x"]+r["dx"]):.1f}" y1="{cy:.1f}" y2="{cy:.1f}" stroke="{col}"/>')
    sh = '<circle cx="%.1f" cy="%.1f" r="4" fill="%s"/>' if r["group"] == "primary" else '<circle cx="%.1f" cy="%.1f" r="4" fill="white" stroke="%s"/>'
    s_.append(sh % (cx, cy, col))
for g in ph:
    pass
# photon points (twisted box, L sqrt(sigma) undefined): shown as horizontal ticks at the left, labelled
for i, (L, z, dz, st) in enumerate(ph):
    yy = Y_((1 - math.exp(-z)) / 2)
    s_.append(f'<path d="M{ml+4},{yy-4:.1f} l8,4 l-8,4 z" fill="{"#900" if st=="counted" else "none"}" stroke="#900"/>')
s_.append(f'<text x="{ml+16}" y="{Y_(0.25)-14:.1f}" fill="#900">U(1) photon, L = 4..10 (no sigma; triangles)</text>')
lx = 360
leg = [("#000", "SU(2) beta 2.3"), ("#c50", "2.4"), ("#07a", "2.5"), ("#6a0", "2.6"), ("#a0a", "2.7")]
for i, (c_, t_) in enumerate(leg):
    s_.append(f'<circle cx="{lx+i*70:.0f}" cy="{H_-mb-60}" r="4" fill="{c_}"/><text x="{lx+i*70+7:.0f}" y="{H_-mb-56}">{t_}</text>')
s_.append(f'<text x="{lx}" y="{H_-mb-40}" fill="#888">grey dashes: independent-vortex model V</text>')
s_.append(f'<text x="{lx}" y="{H_-mb-26}" fill="#06c">blue / green dots: Luescher / Nambu-Goto extrapolation (not data)</text>')
s_.append(f'<text x="{lx}" y="{H_-mb-12}">filled = primary, open = secondary; no SU(2) point at x &lt; 2</text>')
s_.append("</svg>")
with open(os.path.join(HERE, "p_plot.svg"), "w") as f:
    f.write("\n".join(s_))
with open(os.path.join(HERE, "extract_p.log"), "w") as f:
    f.write("\n".join(out) + "\n")
