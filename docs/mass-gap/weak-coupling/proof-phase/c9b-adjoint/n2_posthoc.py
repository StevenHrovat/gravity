"""c9b round 2, N2 POST-HOC diagnostics (NOT pre-registered; written after reading n2_sharp.log).
(a) P7(iii) reference: N1's 2.397 is the crude spatial column at the c4d box corner, not at the central fit.
(b) Weighted sup-form (Hamming) Dobrushin: spectral radius of the 2x2 link-type matrix of sharp coefficients, its Perron weights,
    and the resulting Hamming count kappa and box side l_min.  Numerical, fitted action only."""
import math, numpy as np, importlib.util, sys
spec = importlib.util.spec_from_file_location("n2", "n2_sharp_lib.py")
n2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(n2)

def crude_col(Fts, Fss, Ats, Ass):
    c = lambda b, a: math.tanh(abs(b)) + math.tanh(2 * abs(a) / 3)
    return 12 * c(Fss, Ass) + 6 * c(Fts, Ats)

print("POST-HOC (not pre-registered)")
print(f"(a) crude spatial column at the c4d box corner: {crude_col(*n2.BOX280):.4f} (N1 reported 2.397); central fit 2.3702")
print("(b) column-form type matrix A[t][u] = sum over receivers x of type t adjacent to one z of type u of C_xz (t,u in (spatial, temporal)):")
print("    A_ss = 12 C(s,ss) + 2 C(s,ts), A_st = 12 C(s,ts), A_ts = 4 C(t,ts), A_tt = 6 C(t,ts)")
print("    weighted condition: sum_x v_x C_xz <= rho v_z, i.e. v A <= rho v (v a left Perron vector of A)")
print("    (corrected after review: the first version used the row-form matrix [[., 4 C(s,ts)],[12 C(t,ts), .]], same rho, wrong weights)")
rows = list(n2.FITS) + [(2.3, 8, 2.80, "PASS(box corner)") + n2.BOX280]
for (b_, bb, L, content, Fts, Fss, Ats, Ass) in rows:
    co, _ = n2.fit_coeffs(Fts, Fss, Ats, Ass)
    C = {k: v[0] for k, v in co.items()}
    A = np.array([[12 * C[("s", "ss")] + 2 * C[("s", "ts")], 12 * C[("s", "ts")]],
                  [4 * C[("t", "ts")], 6 * C[("t", "ts")]]])
    ev, evec = np.linalg.eig(A.T)          # left Perron vector: v A <= rho v  (columns weighted)
    i = np.argmax(ev.real); rho = ev[i].real; v = np.abs(evec[:, i].real); v = v / v.max()
    line = f"  beta={b_} b={bb:2d} L={L:.2f} {content:16s} rho={rho:.4f} weights (s,t)=({v[0]:.3f},{v[1]:.3f})"
    if rho < 1:
        # source of one changed outside link z0: sum_x v_x C_x z0 <= rho v_z0 <= rho; Hamming count <= (1/v_min) rho/(1 - rho)
        kap = (rho / (1 - rho)) / v.min()
        line += f"  kappa_Ham <= {kap:.2f}  l_min = {n2.l_min(kap)}"
    print(line)

# (c) added after review: sensitivity of the W1-plus-smoothing count to the W1 column. c4d certifies 0.7318 for the plaquette
# fit (base) and 0.9640 with the fitted 1x2 rectangle (ext_R, b_R = 0.0084, a real coupling). The sharp TV and Lipschitz columns
# below are the plaquette ones (the rectangle's own TV contributions are NOT added), so with c_W = 0.964 the count is a lower
# estimate of what the rectangle-including action needs.
import math
co, _ = n2.fit_coeffs(0.054, 0.171, -0.000595, 0.00149)
C = {k: v[0] for k, v in co.items()}; Lm = {k: v[1] for k, v in co.items()}
MC = n2.class_matrix(lambda rt, pt: C[(rt, pt)]); ML = n2.class_matrix(lambda rt, pt: Lm[(rt, pt)])
ks, perm = n2.best_order(MC)
print("(c) W1-plus-smoothing count at 2.80 (central plaquette TV/Lipschitz columns) against the W1 column:")
for cw, lab in ((0.7318, "base, plaquettes (c4d)"), (0.7611, "ext_T (c4d)"), (0.9640, "ext_R, with rectangle (c4d)"),
                (0.99988, "ext_TR over the box (c4d, knife edge)")):
    D = math.pi * cw / (1 - cw)
    kap = ks * (MC.sum(axis=0).max() + ML.sum(axis=0).max() * D)
    print(f"    c_W = {cw:.4f} ({lab}): D = {D:8.2f} rad, kappa_Ham <= {kap:9.1f}, l_min = {n2.l_min(kap)}")
