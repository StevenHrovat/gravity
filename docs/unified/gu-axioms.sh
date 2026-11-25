#!/usr/bin/env bash
# Grand Unified scoping (GU-SCOPING.md section 4): build ProofPhase.General.GUCentre, run #print axioms on every declaration of
# ProofPhase/General/GUCentre.lean (names read from the source), and grep for sorry / admit / native_decide / axiom.
# Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/gu-axioms.sh > docs/unified/gu-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-gu; give it the Mathlib packages of a built folder, e.g. a link
# .lake/packages -> ~/formal/.lake/packages, to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-gu}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.General.GUCentre"
bash sync-build.sh ProofPhase.General.GUCentre 2>&1 | grep -E "GUCentre.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsGU.XXXXXX.lean)
{
  echo "import ProofPhase.General.GUCentre"
  grep -oE "^(theorem|def|structure) [A-Za-z_][A-Za-z0-9_']*" "ProofPhase/General/GUCentre.lean" | awk '{print $2}' |
    while read -r n; do echo "#print axioms ProofPhase.General.GU.$n"; done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/General/GUCentre.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/General/GUCentre.lean"
