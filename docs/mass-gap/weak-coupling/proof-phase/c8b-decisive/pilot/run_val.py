"""Run the validation jobs of val_jobs.txt, CPU only, N at a time."""
import os, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
env = dict(os.environ, CUDA_VISIBLE_DEVICES="-1")
jobs = []
for line in open(os.path.join(HERE, sys.argv[1] if len(sys.argv) > 1 else "val_jobs.txt")):
    t = line.split()
    if not t:
        continue
    name, g, b, l, bg, rest = t[0], t[1], t[2], t[3], t[4], t[5:]
    if os.path.exists(os.path.join(HERE, name + ".npz")):
        continue
    jobs.append((name, ["couple", g, b, l, bg, os.path.join(HERE, name + ".npz")] + rest + ["--cpu"]))
par = int(sys.argv[2]) if len(sys.argv) > 2 else 6
run = []
while jobs or run:
    run = [(n, p) for n, p in run if p.poll() is None]
    while jobs and len(run) < par:
        n, a = jobs.pop(0)
        run.append((n, subprocess.Popen([sys.executable, "-B", os.path.join(ROOT, "decisive.py")] + a, env=env,
                                        stdout=open(os.path.join(HERE, n + ".log"), "w"), stderr=subprocess.STDOUT, cwd=ROOT)))
    time.sleep(2)
print("validation jobs finished")
