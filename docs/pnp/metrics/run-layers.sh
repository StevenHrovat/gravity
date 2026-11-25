#!/usr/bin/env bash
# Per-layer proof costs for NATIVE-METHOD.md. Read-only on the repository (works on copies). Run inside the WSL replay
# distro from the repository root as seen from WSL:
#   bash docs/pnp/metrics/run-layers.sh
# Needs: $FORMAL_DST (default ~/formal-proof) seeded with a built .lake of the formal project; $METRICS_DST (default
# ~/formal-native) for the evidence copy. Writes docs/pnp/metrics/layers.txt.
set -u
source ~/.elan/env
root="$(cd "$(dirname "$0")/../../.." && pwd)"
here="$root/docs/pnp/metrics"
fdst=${FORMAL_DST:-~/formal-proof}
mdst=${METRICS_DST:-~/formal-native}
out="$here/layers.txt"
run() { # <project dir> <header lines> <tail file or empty> <eval lines>
  local f; f=$(mktemp --suffix=.lean)
  { printf '%s\n' "$2"; tr -d '\r' < "$here/ProofMetrics.lean"; tr -d '\r' < "$here/Layers.lean"
    [ -n "$3" ] && tr -d '\r' < "$3"; printf '%s\n' "$4"; } > "$f"
  (cd "$1" && lake env lean "$f" 2>&1)
  rm -f "$f"
}
(cd "$root/docs/mass-gap/formal" && FORMAL_DST="$fdst" bash sync-build.sh ProofPhase.Native.RouteBChain > /dev/null 2>&1)
rm -rf "$mdst/evidence"; mkdir -p "$mdst"; cp -a "$root/evidence" "$mdst/evidence"
find "$mdst/evidence" -name '*.lean' -o -name '*.toml' | xargs sed -i 's/\r$//'
(cd "$mdst/evidence" && lake build > /dev/null)
{
  echo "## ProofPhase: Route B correlation bound, before and after (three runs each)"
  for i in 1 2 3; do
    run "$fdst" "import ProofPhase.Native.RouteBChain" "" \
      "#eval ProofMetrics.layers \`ProofPhase [\`ProofPhase.RouteB.abs_nCorr_le]
#eval ProofMetrics.layers \`ProofPhase [\`ProofPhase.RouteB.abs_nCorr_le']"
  done
  echo "## DMP: the reflection ladder"
  run "$mdst/evidence" "import Dmp" "" \
    "#eval ProofMetrics.layers \`Dmp [\`Dmp.Cmb.producer_minted]
#eval ProofMetrics.layers \`Dmp [\`Dmp.Recipe.proven_pass_has_two_independent_witnesses]"
  echo "## DMP: a reflected check against the number of building blocks"
  run "$mdst/evidence" "import Dmp" "$here/ReflectionScale.lean" ""
} > "$out"
echo "wrote $out"
