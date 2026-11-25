#!/usr/bin/env bash
# Reproduce the paper GUID v8 (docs/paper) from a clone of this repository. See docs/paper/REPRODUCE.md for what each stage
# needs, how long it takes and what it prints.
#
#   tools/reproduce.sh paper      ledger check, privacy scan, the LaTeX source and (if pdflatex is installed) the PDF of
#                                 Draft 4 (docs/paper); "tools/reproduce.sh paper D5" builds Draft 5 (docs/paper/D5)
#   tools/reproduce.sh evidence   the DMP evidence chain: pin, setup file, build, kernel axiom report (expects "OK 285")
#   tools/reproduce.sh lean       the paper's Lean: build docs/mass-gap/formal against Mathlib and rerun all 26 axiom scripts,
#                                 comparing every declaration's axiom line with the committed log
#   tools/reproduce.sh certs      the certified first box: rerun the ball-arithmetic certificate at a = 3/5, 13/20, 69/100 and
#                                 compare the RESULT line with the committed log; also the scaled sha256 search (seconds)
#   tools/reproduce.sh kernels    the second kernels (leanchecker, nanoda) through tools/independent-check.sh (hours, once)
#   tools/reproduce.sh all        paper (Draft 4), evidence, lean, certs (not kernels); "tools/reproduce.sh all D5" builds Draft 5's paper
#
# Linux, macOS or WSL; bash. Exit 0 when every stage asked for passes, 1 otherwise.
set -uo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"
OUT=${REPRO_OUT:-$root/.reproduce}
mkdir -p "$OUT"
PY=""
for c in python3 python py; do   # the first Python that actually runs (on Windows, python3 may be a store stub)
  if command -v "$c" >/dev/null && "$c" -c "import sys" >/dev/null 2>&1; then PY=$(command -v "$c"); break; fi
done
fail=0
say() { printf '\n== %s\n' "$*"; }
bad() { echo "FAIL $*"; fail=1; }

stage_paper() {
  local d="${1:-}" dir name
  dir="docs/paper${d:+/$d}/latex"; name="guid-v8${d:+-$d}"
  say "paper: ledger, scrub, LaTeX (${d:-Draft 4})"
  [ -n "$PY" ] || { bad "python3 not found"; return; }
  bash tools/paper-gate.sh $d || bad "paper gate"
  "$PY" tools/paper-latex.py $d || { bad "LaTeX conversion"; return; }
  if command -v pdflatex >/dev/null; then
    (cd "$dir" && for i in 1 2; do pdflatex -interaction=nonstopmode -halt-on-error "$name.tex" >/dev/null || exit 1; done) \
      && grep -h "Output written" "$dir/$name.log" || bad "pdflatex"
  else
    echo "pdflatex not installed: the LaTeX source $dir/$name.tex was written; the PDF was not built"
  fi
}

stage_evidence() {
  say "evidence: the DMP evidence chain"
  command -v lake >/dev/null || { bad "lake not found (install elan, see REPRODUCE.md)"; return; }
  bash evidence/tools/check.sh 2>&1 | tail -3 | tee "$OUT/evidence.txt"
  grep -q "^OK 285 theorems" "$OUT/evidence.txt" || bad "evidence gate did not print OK 285"
}

# The axiom lines of a log, in either format the scripts print: Lean's "'X' depends on axioms: [..]" (or "does not depend on any
# axioms") and the own traversal's "X: [..]".
# Line endings are dropped first, so a Windows checkout (CRLF) compares the same as a Linux one.
axiom_lines() { tr -d '\r' < "$1" | grep -E "depends on axioms|does not depend on any axioms|^[A-Za-z_][A-Za-z0-9_.']*: \[[^]]*\]$" | sort -u; }
# Any axiom outside Lean's three standard ones, on those lines.
nonstd() { axiom_lines "$1" | grep -oE "\[[^]]*\]" | tr -d '[]' | tr ',' '\n' | tr -d ' ' | grep -vxE "propext|Classical\.choice|Quot\.sound|" ; }

stage_lean() {
  say "lean: build docs/mass-gap/formal and rerun every axiom script"
  command -v lake >/dev/null || { bad "lake not found (install elan, see REPRODUCE.md)"; return; }
  export FORMAL_DST=${FORMAL_DST:-$HOME/gravity-formal}
  echo "build folder $FORMAL_DST (the first build fetches the Mathlib cache, about 5 GB)"
  for s in docs/unified/*axioms*.sh; do
    name=$(basename "${s%.sh}")
    bash "$s" > "$OUT/$name.log" 2>&1
    new=$(axiom_lines "$OUT/$name.log" | wc -l); old=$(axiom_lines "docs/unified/$name.log" | wc -l)
    if grep -q "sorryAx" "$OUT/$name.log"; then bad "$name: sorryAx"
    elif [ "$new" = 0 ]; then bad "$name: no axiom lines in the output (did the build fail? see $OUT/$name.log)"
    elif [ -n "$(nonstd "$OUT/$name.log")" ]; then bad "$name: a non-standard axiom: $(nonstd "$OUT/$name.log" | sort -u | tr '\n' ' ')"
    elif ! diff <(axiom_lines "$OUT/$name.log") <(axiom_lines "docs/unified/$name.log") >/dev/null; then bad "$name: $new axiom lines, the committed log has $old (diff $OUT/$name.log docs/unified/$name.log)"
    else echo "ok   $name ($new declarations, standard axioms only, same as the committed log)"; fi
  done
}

stage_certs() {
  say "certs: the certified first box (python-flint), and the scaled sha256 search (Appendix T.6 of Draft 5)"
  [ -n "$PY" ] || { bad "python3 not found"; return; }
  "$PY" docs/unified/sha256_scaled.py > "$OUT/sha256_scaled.log" 2>&1
  if diff <(grep "^RESULT" "$OUT/sha256_scaled.log") <(grep "^RESULT" docs/unified/sha256_scaled.log) >/dev/null; then
    echo "ok   sha256 scaled search: $(grep -c '^RESULT' "$OUT/sha256_scaled.log") RESULT lines, the same as the committed log"
  else bad "sha256 scaled search: the RESULT lines differ from docs/unified/sha256_scaled.log"; fi
  "$PY" -c "import flint" 2>/dev/null || { bad "python-flint missing (pip install -r docs/paper/requirements.txt)"; return; }
  for a in 0.60:3/5 0.65:13/20 0.69:69/100; do
    tag=${a%%:*}; frac=${a#*:}
    "$PY" docs/unified/grh_onebox_cert.py "$frac" 100 40 > "$OUT/grh_onebox_cert-a$tag.log" 2>&1
    new=$(grep "^RESULT" "$OUT/grh_onebox_cert-a$tag.log"); old=$(grep "^RESULT" "docs/unified/grh_onebox_cert-a$tag.log")
    if [ -n "$new" ] && [ "$new" = "$old" ]; then echo "ok   a = $frac: $new"; else bad "a = $frac: got '$new', the log has '$old'"; fi
  done
}

stage_kernels() {
  say "kernels: leanchecker and nanoda (tools/independent-check.sh; see docs/unified/INDEPENDENT-CHECK.md)"
  bash tools/independent-check.sh setup && bash tools/independent-check.sh build && bash tools/independent-check.sh axioms \
    && bash tools/independent-check.sh replay-all && bash tools/independent-check.sh export && bash tools/independent-check.sh nanoda \
    || bad "independent check"
}

case "${1:-all}" in
  paper) stage_paper "${2:-}" ;;
  evidence) stage_evidence ;;
  lean) stage_lean ;;
  certs) stage_certs ;;
  kernels) stage_kernels ;;
  all) stage_paper "${2:-}"; stage_evidence; stage_lean; stage_certs ;;
  *) echo "usage: tools/reproduce.sh [paper [DN]|evidence|lean|certs|kernels|all [DN]]"; exit 2 ;;
esac
say "result"
if [ "$fail" = 0 ]; then echo "reproduce: OK"; else echo "reproduce: FAILED (see the lines above)"; fi
exit "$fail"
