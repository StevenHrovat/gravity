"""Summarise proof metrics CSVs (from ProofMetrics.lean). Read-only; prints tables used in NATIVE-OPTIMIZATION.md."""
import csv, statistics as st, sys, collections

AUTO = ("sizeOf_spec", "injEq", "inj", "ext_iff", "ext", "eq_def", "noConfusion")

def load(path, keep=None, prefix=""):
    rows = []
    with open(path, encoding="utf-8") as f:
        lines = [l for l in f if l.count(",") >= 19]
    for r in csv.DictReader(lines):
        n = r["name"]
        if keep is not None and n[len(prefix):] not in keep:
            continue
        if keep is None and n.split(".")[-1] in AUTO:
            continue
        for k in list(r):
            if k not in ("name", "module", "goal", "axioms"):
                r[k] = int(r[k])
        rows.append(r)
    return rows

def kind(r):
    # dominant logical shape of the theorem's own proof term
    if r["induct"]: return "induction"
    if r["contra"] and r["witness"]: return "witness+contradiction"
    if r["contra"]: return "contradiction"
    if r["witness"]: return "witness"
    if r["cases"]: return "case split"
    if (r["decide"] or r["rfl"]) and r["thmDeps"] == 0: return "computation"
    return "composition"

def q(xs, p):
    xs = sorted(xs); return xs[min(len(xs) - 1, int(p * len(xs)))]

def summary(name, rows):
    print(f"\n== {name}: {len(rows)} theorems")
    for k in ("depthThm", "depthAll", "closureThm", "thmDeps", "size"):
        xs = [r[k] for r in rows]
        print(f"  {k:11s} median {st.median(xs):7.1f}  mean {st.mean(xs):8.1f}  p90 {q(xs, .9):6d}  max {max(xs):6d}")
    c = collections.Counter(kind(r) for r in rows)
    print("  shape:", ", ".join(f"{k} {v} ({100*v/len(rows):.0f}%)" for k, v in c.most_common()))
    for k in ("witness", "existsUse", "cases", "induct", "contra", "clash", "classical", "decide", "rfl"):
        n = sum(1 for r in rows if r[k] > 0)
        print(f"  with {k:9s}: {n:5d} ({100*n/len(rows):4.0f}%)  total occurrences {sum(r[k] for r in rows)}")
    g = collections.Counter(r["goal"] for r in rows)
    print("  statement:", ", ".join(f"{k} {v}" for k, v in g.most_common()))
    ex = [r for r in rows if r["goal"] == "exists"]
    if ex:
        w = sum(1 for r in ex if r["witness"] > 0)
        print(f"  existence statements: {len(ex)}, with an explicit witness in the proof term: {w}")
    noC = sum(1 for r in rows if "C" not in r["axioms"].split("+"))
    print(f"  without Classical.choice (constructive in the kernel's sense): {noC} ({100*noC/len(rows):.0f}%)")
    roots = [r for r in rows if r["usedBy"] == 0]
    cr = collections.Counter(kind(r) for r in roots)
    print("  root shapes:", ", ".join(f"{k} {v}" for k, v in cr.most_common()))
    print(f"  roots (used by no other theorem): {len(roots)}")
    once = [r for r in rows if r["usedBy"] == 1]
    print(f"  used exactly once: {len(once)} ({100*len(once)/len(rows):.0f}%)")
    wrappers = [r for r in rows if r["thmDeps"] == 1 and r["cases"] == 0 and r["contra"] == 0 and r["induct"] == 0
                and r["witness"] == 0 and r["size"] <= 60]
    print(f"  thin wrappers (one lemma, no split, size <= 60): {len(wrappers)}")
    return roots

def top(rows, key, n=8):
    for r in sorted(rows, key=lambda r: -r[key])[:n]:
        print(f"    {r['name']:60s} depthThm {r['depthThm']:3d} closure {r['closureThm']:4d} size {r['size']:6d} "
              f"W{r['witness']} C{r['cases']} I{r['induct']} X{r['contra']} D{r['decide']}  {kind(r)}")

if __name__ == "__main__":
    sp = sys.argv[1]
    gate = set(open(f"{sp}/gate.txt").read().split())
    dmp = load(f"{sp}/dmp.csv", keep=gate, prefix="Dmp.")
    roots = summary("DMP evidence (gated)", dmp)
    print("  deepest:"); top(dmp, "depthThm")
    print("  largest closure:"); top(dmp, "closureThm")
    print("  roots by depth:"); top(roots, "depthThm", 12)
    by_mod = collections.defaultdict(list)
    for r in dmp: by_mod[r["module"]].append(r)
    print("  per module: module n medianDepth maxDepth shapes")
    for m, rs in sorted(by_mod.items()):
        c = collections.Counter(kind(r) for r in rs)
        print(f"    {m:16s} {len(rs):3d} {st.median([r['depthThm'] for r in rs]):4.1f} {max(r['depthThm'] for r in rs):3d}  "
              + ", ".join(f"{k} {v}" for k, v in c.most_common()))
    if len(sys.argv) > 2:
        pp = load(f"{sp}/pp.csv")
        roots = summary("ProofPhase", pp)
        print("  deepest:"); top(pp, "depthThm")
        print("  largest closure:"); top(pp, "closureThm")
        for sub in sys.argv[3:]:
            rs = [r for r in pp if r["module"].startswith(sub)]
            if rs: summary(sub, rs)
