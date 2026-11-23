#!/usr/bin/env bash
# GRH tie-in: build ProofPhase.GRH.TieInFF (it imports ProofPhase.GRH.TieIn), run #print axioms on every declaration of
# ProofPhase/GRH/TieIn.lean and ProofPhase/GRH/TieInFF.lean (names read from the source), and grep for sorry / admit /
# native_decide / axiom.
# Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/grhtiein-axioms.sh > docs/unified/grhtiein-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.GRH.TieInFF"
bash sync-build.sh ProofPhase.GRH.TieInFF 2>&1 | grep -E "GRH/TieIn.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsTieIn.XXXXXX.lean)
{
  echo "import ProofPhase.GRH.TieInFF"
  for f in TieIn TieInFF; do
    awk '
      /^namespace CurveModel/ { ns = "CurveModel." }
      /^end CurveModel/ { ns = "" }
      /^(theorem|def|structure) [A-Za-z_]/ {
        n = $2; sub(/[^A-Za-z0-9_'"'"'].*$/, "", n); print ns n
      }' "ProofPhase/GRH/$f.lean" | while read -r n; do echo "#print axioms ProofPhase.Unified.$n"; done
  done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/GRH/TieIn.lean ProofPhase/GRH/TieInFF.lean ||
  echo "no sorry / admit / native_decide / axiom in ProofPhase/GRH/TieIn.lean, ProofPhase/GRH/TieInFF.lean"
