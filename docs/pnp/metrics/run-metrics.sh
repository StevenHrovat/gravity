#!/usr/bin/env bash
# Proof metrics for NATIVE-OPTIMIZATION.md. Read-only on the repository: it copies evidence/ and the formal project into
# a build folder, builds the copies, and runs ProofMetrics.lean against them. Run inside the WSL replay distro (Lean
# 4.34.0), from the repository root as seen from WSL:
#   bash docs/pnp/metrics/run-metrics.sh
# Build folder: $METRICS_DST (default ~/formal-native). Seed $METRICS_DST/pp/.lake with a copy of a built .lake of the
# formal project first, or the Mathlib build takes hours. Writes dmp.csv, pp.csv, proof.csv there and the summary to
# docs/pnp/metrics/report.txt.
set -u
source ~/.elan/env
root="$(cd "$(dirname "$0")/../../.." && pwd)"
here="$root/docs/pnp/metrics"
dst=${METRICS_DST:-~/formal-native}
mkdir -p "$dst"
metrics() { # <project dir> <imports> <prefix> <out>
  local f; f=$(mktemp --suffix=.lean)
  { printf '%s\n' "$2"; tr -d '\r' < "$here/ProofMetrics.lean"; echo "#eval ProofMetrics.run \`$3"; } > "$f"
  (cd "$1" && lake env lean "$f" > "$4" 2>&1)
  rm -f "$f"
}
# 1. The gated evidence (core Lean): a copy, built.
rm -rf "$dst/evidence"; cp -a "$root/evidence" "$dst/evidence"
find "$dst/evidence" -name '*.lean' -o -name '*.toml' | xargs sed -i 's/\r$//'
(cd "$dst/evidence" && lake build > /dev/null)
metrics "$dst/evidence" "import Dmp" Dmp "$dst/dmp.csv"
# 2. ProofPhase (Mathlib): every module, in a copy.
(cd "$root/docs/mass-gap/formal" && FORMAL_DST="$dst/pp" bash sync-build.sh Influence > /dev/null 2>&1 || true)
mods=$(cd "$dst/pp" && find ProofPhase -name '*.lean' | sed 's/\.lean$//; s|/|.|g' | sort)
(cd "$dst/pp" && lake build $mods > /dev/null)
metrics "$dst/pp" "$(echo "$mods" | sed 's/^/import /')" ProofPhase "$dst/pp.csv"
# 3. The gate list, and the summary.
grep -hE '^theorem ' "$root"/evidence/Dmp/*.lean | sed -E 's/^theorem ([^ :({\[]+).*/\1/' | sort -u > "$dst/gate.txt"
(cd "$dst" && python3 "$here/analyse.py" . pp ProofPhase.DMP ProofPhase.Proof ProofPhase.Mixing ProofPhase.M1 \
  ProofPhase.General ProofPhase.Bridge) > "$here/report.txt"
echo "wrote $here/report.txt"
