#!/usr/bin/env bash
# Blowup blueprint (BLOWUP.md): build ProofPhase.Unified.Blowup, run #print axioms on every declaration of
# ProofPhase/Unified/Blowup.lean (names read from the source), and grep for sorry / admit / native_decide / axiom.
# Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/blowup-axioms.sh > docs/unified/blowup-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-unified; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-unified}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.Unified.Blowup"
bash sync-build.sh ProofPhase.Unified.Blowup 2>&1 | grep -E "Blowup.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsBlowup.XXXXXX.lean)
{
  echo "import ProofPhase.Unified.Blowup"
  grep -oE "^(theorem|def|structure) [A-Za-z_][A-Za-z0-9_']*" "ProofPhase/Unified/Blowup.lean" | awk '{print $2}' |
    while read -r n; do echo "#print axioms ProofPhase.Unified.$n"; done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Unified/Blowup.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Unified/Blowup.lean"
