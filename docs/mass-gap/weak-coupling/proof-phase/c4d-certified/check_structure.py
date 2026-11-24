"""Check that analyse_refit.py's neighbour structure (class-resolved pair table) equals the Dobrushin column structure of
AdjointW.lean: every link i != z shares at most one plaquette with z; a link lies in 6 plaquettes (temporal: 6 ts; spatial: 2 ts + 4 ss),
every plaquette has 3 other links, a link lies in 18 rectangles with 5 other links each."""
import os, sys, importlib.util
os.environ["CUDA_VISIBLE_DEVICES"] = "-1"
here = os.path.dirname(os.path.abspath(__file__))
p = os.path.join(here, "..", "c3b-refit", "analyse_refit.py")
spec = importlib.util.spec_from_file_location("ar", p); ar = importlib.util.module_from_spec(spec); sys.modules["ar"] = ar
spec.loader.exec_module(ar)
P = ar.pair_table_aniso()
for z, rows in P.items():
    nts = sum(r[0] for r in rows); nss = sum(r[1] for r in rows); nR = sum(r[2] for r in rows)
    maxshare = max(r[0] + r[1] for r in rows)
    print(f"z {z}: sum n_ts {nts} (= 3 x ts-plaquettes {nts//3}), sum n_ss {nss} (= 3 x ss-plaquettes {nss//3}), sum n_R {nR}, "
          f"max plaquettes shared with one link {maxshare}, neighbours {len(rows)}")
