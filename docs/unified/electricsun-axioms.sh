#!/usr/bin/env bash
# Electric-SU(N) round: build ProofPhase.Unified.ElectricSUNPress (it imports ElectricSUN), run #print axioms on every
# declaration of ProofPhase/Unified/ElectricSUN.lean and ElectricSUNPress.lean (names read from the source), and grep for
# sorry / admit / native_decide / axiom.
# Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/electricsun-axioms.sh > docs/unified/electricsun-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-elecsun; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-elecsun}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.Unified.ElectricSUNPress"
bash sync-build.sh ProofPhase.Unified.ElectricSUNPress 2>&1 | grep -E "Unified/ElectricSUN.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsElectricSUN.XXXXXX.lean)
{
  echo "import ProofPhase.Unified.ElectricSUNPress"
  for f in ElectricSUN ElectricSUNPress; do
    awk '/^(theorem|def|structure) [A-Za-z_]/ {n = $2; sub(/[^A-Za-z0-9_'"'"'₀₁₂₃].*$/, "", n); print n}' \
      "ProofPhase/Unified/$f.lean" | while read -r n; do echo "#print axioms ProofPhase.Unified.$n"; done
  done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Unified/ElectricSUN.lean ProofPhase/Unified/ElectricSUNPress.lean ||
  echo "no sorry / admit / native_decide / axiom in ProofPhase/Unified/ElectricSUN.lean, ElectricSUNPress.lean"
