"""GUID v6: run every script behind the paper and print its check count (Appendix A, Table "The scripts behind the paper").

Run from the repository root:   python3 docs/guid-v6/reproduce.py [--data <SPARC folder>]
The two rotation-curve scripts need the SPARC tables (not redistributed; see Appendix A); without --data or SPARC_DATA_DIR they are
skipped and reported as such. The data-confrontation script exits 1 by design (four confrontations fail at 95%, Section "data").
"""
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
args = sys.argv[1:]
data = os.environ.get("SPARC_DATA_DIR")
if "--data" in args:
    data = args[args.index("--data") + 1]

SCRIPTS = [
    ("docs/guid-v6/checks.py", [], 0),
    ("docs/qg-verdict/assembly.py", [], 0),
    ("docs/simulation/hosted_benchmarks.py", [], 0),
    ("docs/simulation/holographic_code.py", [], 0),
    ("docs/simulation/gravity_simulated.py", [], 0),
    ("docs/simulation/bmv_witness.py", [], 0),
    ("docs/simulation/sparc_rotation.py", ["--data"], 0),
    ("docs/simulation/remnant_history.py", ["--data"], 0),
    ("docs/simulation/predictions_vs_data.py", [], 1),
    ("docs/simulation/standard_model.py", [], 0),
    ("docs/simulation/exotic_hadrons.py", [], 0),
]

env = dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1", PYTHONDONTWRITEBYTECODE="1")
rows, ok_all = [], True
for script, extra, expected_exit in SCRIPTS:
    cmd = [sys.executable, str(ROOT / script)]
    if extra == ["--data"]:
        if not data:
            rows.append((script, "skipped (no SPARC data)", "-", "-"))
            continue
        cmd += ["--data", data]
    t0 = time.perf_counter()
    p = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
    dt = time.perf_counter() - t0
    tail = [l for l in p.stdout.splitlines() if re.search(r"\d+ of \d+", l)]
    summary = tail[-1].strip() if tail else "(no summary line)"
    good = p.returncode == expected_exit
    ok_all &= good
    rows.append((script, summary, f"exit {p.returncode} (expected {expected_exit})", f"{dt:.0f} s"))
    print(f"{'OK  ' if good else 'FAIL'} {script}: {summary}; exit {p.returncode}; {dt:.0f} s", flush=True)

print("\nscript | summary | exit | runtime")
for r in rows:
    print(" | ".join(r))
sys.exit(0 if ok_all else 1)
