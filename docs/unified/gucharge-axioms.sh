#!/usr/bin/env bash
# Grand Unified, the consequence from the G0 link (GU-SCOPING.md section 8): build ProofPhase.General.GUCharge, run #print axioms on every declaration of
# ProofPhase/General/GUCharge.lean (names read from the source), and grep for sorry / admit / native_decide / axiom.
# Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/gucharge-axioms.sh > docs/unified/gucharge-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-gu; give it the Mathlib packages of a built folder, e.g. a link
# .lake/packages -> ~/formal/.lake/packages, to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-gu}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.General.GUCharge"
bash sync-build.sh ProofPhase.General.GUCharge 2>&1 | grep -E "GUCharge.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsGUCharge.XXXXXX.lean)
{
  echo "import ProofPhase.General.GUCharge"
  grep -oE "^(theorem|def|structure) [A-Za-z_][A-Za-z0-9_']*" "ProofPhase/General/GUCharge.lean" | awk '{print $2}' |
    while read -r n; do echo "#print axioms ProofPhase.General.GU.$n"; done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/General/GUCharge.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/General/GUCharge.lean"
