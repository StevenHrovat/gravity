"""GUID v6: one count of every scored confrontation of Part III (Section "The tally", sec:tally).

Run:  python3 docs/simulation/tally.py      (after predictions_vs_data.py, standard_model.py and exotic_hadrons.py)
Reads docs/simulation/results/{predictions_vs_data,standard_model,exotic_hadrons}.json and writes docs/simulation/results/tally.json.
Deterministic: no random numbers, no clock, no network. Runtime well under a second.

Every scored row gets one tally class:
  shared                       the prediction is that of general relativity, LambdaCDM, the Standard Model (QCD included) or quantum
                               mechanics, so the row tests what GUID adopts, not what it adds;
  specific-sensitive           GUID-specific, and the datum (or a derivation) reaches where GUID departs from those theories;
  specific-not-yet-sensitive   GUID-specific, but GUID's departure is smaller than the datum's reach by a factor of ten or more, or
                               scales with a free parameter that may be zero.

Where the rows come from (a row may always carry its own "tally_class" and "tally_reason", which then override the tables below):
  predictions_vs_data.json  rows of kind 'scored'; their tally_class is computed in that script (table SENS there).
  standard_model.json       rows with scored = true; class from SM_CLASS below.
  exotic_hadrons.json       A.items of kind 'scored' (class EXO_A_CLASS below) and, once the file has it, every entry of the top-level
                            key "H9" (I1, I2, ...). An H9 entry counts as scored when it says "scored": true or "kind": "scored", or,
                            without either key, when its verdict starts with "holds" or "refuted" (a live or untested entry is not
                            scored); class from H9_CLASS below. So rerunning this script after exotic_hadrons.py has written its H9
                            rows picks them up; an H9 entry this table does not know fails the classification check until it is added.

The checks at the end must all pass (exit 0); a FAIL among the confrontations is a result, not a failed check.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
RES = ROOT / "results"
CLASSES = ("shared", "specific-sensitive", "specific-not-yet-sensitive")

SM_SAME = "the Standard Model makes the same statement for its own content"
SM_CLASS = {
    **{f"SM1.{i}": ("shared", SM_SAME) for i in range(1, 5)},
    **{f"SM2a.{i}": ("shared", "the Standard Model's Higgs couplings, proportional to mass") for i in range(1, 6)},
    "SM2b.1": ("specific-not-yet-sensitive", "Dirac neutrinos give no signal, but so can Majorana neutrinos: their effective mass "
                                             "scales with free phases and the lightest mass and may vanish, and with normal ordering it lies "
                                             "below these bounds"),
    "SM2b.2": ("specific-not-yet-sensitive", "as SM2b.1"),
    "SM2b.4": ("specific-not-yet-sensitive", "decoupled right-handed partners add a negligible Delta N_eff: the prediction is the Standard "
                                             "Model's 3.044, far inside the error"),
    "SM2b.5": ("specific-not-yet-sensitive", "as SM2b.4"),
    "SM2b.6": ("shared", "a tension of LambdaCDM with the oscillation data, for Dirac and Majorana neutrinos alike"),
    **{f"SM2d.{i}": ("shared", "the Standard Model's W mass with loops") for i in range(1, 5)},
    "SM3.1": ("specific-sensitive", "decided by derivation: the preregistered window misses the derived R by a factor 4.5"),
    "SM3.2": ("specific-not-yet-sensitive", "GUID's line Delta mu/mu = R Delta alpha/alpha passes through zero, and the variation scales "
                                            "with a free coupling that may be zero"),
    "SM3.4": ("specific-not-yet-sensitive", "as SM3.2"),
    "SM3.5": ("specific-not-yet-sensitive", "as SM3.2; the bound does not constrain alpha on GUID's line"),
    "SM3.6": ("specific-not-yet-sensitive", "the scalar's share of g-2 lies 36 to 38 orders of magnitude below the precision"),
    "SM3.8": ("shared", "the Standard Model's electron g-2 (the scalar's share is negligible, SM3.6)"),
    "SM3.9": ("shared", "as SM3.8"),
    "SM3.10": ("shared", "the Standard Model's muon g-2"),
    "SM4.1": ("shared", SM_SAME + ": its couplings do not meet"),
    "SM4.2": ("shared", "as SM4.1"),
    "SM4.5": ("shared", "the Standard Model without unification says the same; the bound is the proton-decay search's"),
    "SM5.1": ("shared", "the measured running coupling; Section data treats the same reading as a consistency row (D8.5)"),
}
EXO_A_CLASS = ("shared", "a standard QCD colour-spin model (Karliner and Rosner) on the compact trees of Hypothesis 8; the hypothesis "
                         "itself cannot fail on a single state, and the compact-diquark picture predates GUID")
H9_CLASS = {
    "I1": ("specific-not-yet-sensitive", "the open-against-hidden-flavour contrast is not significant"),
    "I3": ("specific-sensitive", "a rule GUID adds to QCD, decided by the catalogue of exotic hadrons"),
    "I4": ("specific-sensitive", "a splitting rule GUID adds to QCD, decided by the measured doublets"),
}


def load(name):
    return json.loads((RES / name).read_text())


ROWS = []


def add(section, rid, label, ok, cls, reason):
    ROWS.append(dict(section=section, id=rid, label=label, verdict="OK" if ok else "FAIL", tally_class=cls, reason=reason))


pvd = load("predictions_vs_data.json")
for r in pvd["rows"]:
    if r["kind"] == "scored":
        add("data", r["id"], r["observable"], r["verdict"] == "OK", r.get("tally_class"),
            r.get("sensitivity_reason") or ("shared with " + r["cls"].split("shared with ")[-1] if "shared with" in r["cls"] else r["cls"]))

sm = load("standard_model.json")
for r in sm["rows"]:
    if r.get("scored"):
        cls, why = (r["tally_class"], r.get("tally_reason", "")) if r.get("tally_class") else SM_CLASS.get(r["id"], (None, "not classified"))
        add("sm", r["id"], r["statement"], r["test"] == "OK", cls, why)

exo = load("exotic_hadrons.json")
for it in exo["A"]["items"]:
    if it["kind"] == "scored":
        cls, why = (it["tally_class"], it.get("tally_reason", "")) if it.get("tally_class") else EXO_A_CLASS
        name = it["label"].split(" vs ")[1] + " " + it.get("JPC", "") if " vs " in it["label"] else it["label"].split(" (")[0]
        add("exotics", "A:" + name.strip(), it["label"], it["verdict"] == "holds", cls, why)
h9 = exo.get("H9")
h9_present = isinstance(h9, dict)
for key, e in (h9.items() if h9_present else []):
    if not isinstance(e, dict):
        continue
    v = str(e.get("verdict", ""))
    flagged = e.get("scored") is True or e.get("kind") == "scored"
    unflagged = "scored" not in e and "kind" not in e and (v.startswith("holds") or v.startswith("refuted"))
    if not (flagged or unflagged):
        continue
    cls, why = (e["tally_class"], e.get("tally_reason", "")) if e.get("tally_class") else H9_CLASS.get(key, (None, "not classified"))
    add("exotics", "H9:" + key, "Hypothesis H9, " + key, not v.startswith("refuted"), cls, why)


def count(rows):
    out = dict(scored=len(rows), ok=sum(r["verdict"] == "OK" for r in rows), fail=[r["id"] for r in rows if r["verdict"] == "FAIL"])
    for c in CLASSES:
        sub = [r for r in rows if r["tally_class"] == c]
        out[c] = dict(n=len(sub), ok=sum(r["verdict"] == "OK" for r in sub), fail=[r["id"] for r in sub if r["verdict"] == "FAIL"])
    return out


SECTIONS = {"data": "sec:data (predictions_vs_data.py)", "sm": "sec:sm (standard_model.py)", "exotics": "sec:exotics (exotic_hadrons.py)"}
per = {s: count([r for r in ROWS if r["section"] == s]) for s in SECTIONS}
total = count(ROWS)

print("GUID v6: the tally of scored confrontations (Part III)")
print(f"{'section':<10}{'scored':>7}{'OK':>5}{'FAIL':>6}{'shared':>9}{'spec.sens.':>12}{'spec.n.y.s.':>13}")
for s, c in list(per.items()) + [("total", total)]:
    print(f"{s:<10}{c['scored']:>7}{c['ok']:>5}{len(c['fail']):>6}{c['shared']['n']:>9}{c['specific-sensitive']['n']:>12}"
          f"{c['specific-not-yet-sensitive']['n']:>13}")
for c in CLASSES:
    print(f"FAILs, {c}: {', '.join(total[c]['fail']) or 'none'}")
print(f"H9 rows present in exotic_hadrons.json: {'yes' if h9_present else 'no (rerun after exotic_hadrons.py writes them)'}")

# ---- checks ---------------------------------------------------------------------------------------------------------------------
CHECKS = []


def check(label, ok):
    CHECKS.append(dict(label=label, ok=bool(ok)))
    print(f"[C] {'OK  ' if ok else 'FAIL'} {label}")


s_pvd = pvd["summary"]
check(f"data: {per['data']['scored']} scored, {per['data']['ok']} OK, as predictions_vs_data.json says",
      per["data"]["scored"] == s_pvd["scored"] and per["data"]["ok"] == s_pvd["passed"])
check(f"Standard Model: {per['sm']['scored']} scored, {per['sm']['ok']} OK, as standard_model.json says",
      per["sm"]["scored"] == sm["summary"]["scored"] and per["sm"]["ok"] == sm["summary"]["consistent"])
n_a = sum(1 for r in ROWS if r["id"].startswith("A:"))
check(f"exotics: {n_a} model rows, {sum(1 for r in ROWS if r['id'].startswith('A:') and r['verdict'] == 'OK')} hold, as exotic_hadrons.json says",
      n_a == exo["A"]["n_scored"] and sum(1 for r in ROWS if r["id"].startswith("A:") and r["verdict"] == "OK") == exo["A"]["n_holds"])
unclassified = [r["id"] for r in ROWS if r["tally_class"] not in CLASSES]
check("every scored row has a tally class" + (f" (missing: {', '.join(unclassified)})" if unclassified else ""), not unclassified)
check("the classes and the verdicts add up to the total",
      sum(total[c]["n"] for c in CLASSES) == total["scored"] == total["ok"] + len(total["fail"])
      and all(sum(per[s][c]["n"] for s in SECTIONS) == total[c]["n"] for c in CLASSES))
ids = [r["section"] + ":" + r["id"] for r in ROWS]
check("no row is counted twice", len(ids) == len(set(ids)))
stale = sorted(set(SM_CLASS) - {r["id"] for r in ROWS if r["section"] == "sm"})
if stale:
    print(f"note: SM_CLASS lists rows that standard_model.json no longer scores: {', '.join(stale)}")

out = dict(script="docs/simulation/tally.py", sources=[f"docs/simulation/results/{n}" for n in
                                                       ("predictions_vs_data.json", "standard_model.json", "exotic_hadrons.json")],
           classes={"shared": "the prediction is that of GR, LambdaCDM, the Standard Model (QCD included) or quantum mechanics",
                    "specific-sensitive": "GUID-specific; the datum or a derivation reaches where GUID departs from those theories",
                    "specific-not-yet-sensitive": "GUID-specific; GUID's departure is smaller than the datum's reach by a factor of ten "
                                                  "or more, or scales with a free parameter that may be zero"},
           sections=SECTIONS, per_section=per, total=total, h9_present=h9_present, stale_sm_class_entries=stale, rows=ROWS, checks=CHECKS)
(RES / "tally.json").write_text(json.dumps(out, indent=1, ensure_ascii=True) + "\n")
n_ok = sum(c["ok"] for c in CHECKS)
print(f"\n{total['ok']} of {total['scored']} scored confrontations hold ({len(total['fail'])} FAIL); "
      f"{total['shared']['n']} shared, {total['specific-sensitive']['n']} GUID-specific and sensitive, "
      f"{total['specific-not-yet-sensitive']['n']} GUID-specific and not yet sensitive")
print(f"{n_ok} of {len(CHECKS)} checks passed")
sys.exit(0 if n_ok == len(CHECKS) else 1)
