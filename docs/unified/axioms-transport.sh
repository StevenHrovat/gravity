#!/usr/bin/env bash
# Transport theorem: build ProofPhase.Unified.All (the aggregator; imports Transport and TransportBridges) and
# ProofPhase.Unified.TransportInstances, one module at a time; run #print axioms on every declaration of
# ProofPhase/Unified/Transport*.lean and All.lean (names read from the sources), and grep for sorry / admit /
# native_decide / axiom. Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/axioms-transport.sh > docs/unified/axioms-transport.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
for m in All TransportInstances; do
  echo "== build ProofPhase.Unified.$m"
  bash sync-build.sh "ProofPhase.Unified.$m" 2>&1 | grep -E "Unified/(Transport|All).*(warning|error)|^error|Build completed" || true
done
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsTransport.XXXXXX.lean)
{
  echo "import ProofPhase.Unified.All"
  echo "import ProofPhase.Unified.TransportInstances"
  for f in Transport TransportBridges TransportInstances All; do
    grep -oE "^(theorem|def|structure) [A-Za-z_][A-Za-z0-9_'.]*" "ProofPhase/Unified/$f.lean" | awk '{print $2}' |
      while read -r n; do
        case "$n" in
          _root_.*) echo "#print axioms ${n#_root_.}" ;;
          *) echo "#print axioms ProofPhase.Unified.$n" ;;
        esac
      done
  done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Unified/Transport*.lean ProofPhase/Unified/All.lean ||
  echo "no sorry / admit / native_decide / axiom in ProofPhase/Unified/Transport*.lean, All.lean"
