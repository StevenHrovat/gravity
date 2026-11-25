#!/usr/bin/env bash
# Electric-SU(N) round: build ProofPhase.Unified.ElectricSUNRunning (it imports ElectricSUNPress), run #print axioms on every
# declaration of ProofPhase/Unified/ElectricSUNRunning.lean (names read from the source), and grep for
# sorry / admit / native_decide / axiom.
# Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/electricsun-running-axioms.sh > docs/unified/electricsun-running-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-elecsun; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-elecsun}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.Unified.ElectricSUNRunning"
bash sync-build.sh ProofPhase.Unified.ElectricSUNRunning 2>&1 | grep -E "Unified/ElectricSUN.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsElectricSUNRunning.XXXXXX.lean)
{
  echo "import ProofPhase.Unified.ElectricSUNRunning"
  for f in ElectricSUNRunning; do
    awk '/^(theorem|def|structure) [A-Za-z_]/ {n = $2; sub(/[^A-Za-z0-9_'"'"'₀₁₂₃].*$/, "", n); print n}' \
      "ProofPhase/Unified/$f.lean" | while read -r n; do echo "#print axioms ProofPhase.Unified.$n"; done
  done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Unified/ElectricSUNRunning.lean ||
  echo "no sorry / admit / native_decide / axiom in ProofPhase/Unified/ElectricSUNRunning.lean"
