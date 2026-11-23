#!/usr/bin/env bash
# Explicit formula: build ProofPhase.GRH.ExplicitFormulaTie (it imports ExplicitFormula, ExplicitFormulaPrime, TieIn), run
# #print axioms on every declaration of the three ExplicitFormula*.lean files (names read from the source), and grep for
# sorry / admit / native_decide / axiom.
# Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/explicitformula-axioms.sh > docs/unified/explicitformula-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
files="ExplicitFormulaPrime ExplicitFormula ExplicitFormulaTie"
cd "$src"
echo "== build ProofPhase.GRH.ExplicitFormulaTie"
bash sync-build.sh ProofPhase.GRH.ExplicitFormulaTie 2>&1 | grep -E "GRH/ExplicitFormula.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsEF.XXXXXX.lean)
{
  echo "import ProofPhase.GRH.ExplicitFormulaTie"
  for f in $files; do
    awk '
      { sub(/^@\[[a-z]+\] /, "") }
      /^(theorem|def|structure|abbrev) [A-Za-z_]/ {
        n = $2; sub(/[^A-Za-z0-9_ℝ'"'"'].*$/, "", n); print n
      }' "ProofPhase/GRH/$f.lean" | while read -r n; do echo "#print axioms ProofPhase.GRH.EF.$n"; done
  done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
paths=""; for f in $files; do paths="$paths ProofPhase/GRH/$f.lean"; done
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" $paths ||
  echo "no sorry / admit / native_decide / axiom in$paths"
