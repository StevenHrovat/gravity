#!/usr/bin/env bash
# Contour shift: build ProofPhase.GRH.ContourShiftExists (it imports ContourShiftTie, which imports the Mathlib-only core ContourShift, ContourShiftZeta,
# ContourShiftTest, ContourShiftLandau, ContourShiftRect, namespace ProofPhase.GRH.CS, and the explicit-formula files),
# run #print axioms on every declaration of the seven ContourShift*.lean files (names read from the source; the tie file
# ContourShiftTie and ContourShiftExists are in namespace ProofPhase.GRH.CSTie), list the imports of the core files (Mathlib and core only), and
# grep for sorry / admit / native_decide / axiom.
# Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/contourshift-axioms.sh > docs/unified/contourshift-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
core="ContourShiftRect ContourShiftLandau ContourShiftZeta ContourShiftTest ContourShift"
files="$core ContourShiftTie ContourShiftExists"
cd "$src"
echo "== build ProofPhase.GRH.ContourShiftExists"
bash sync-build.sh ProofPhase.GRH.ContourShiftExists 2>&1 | grep -E "GRH/ContourShift.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsCS.XXXXXX.lean)
{
  echo "import ProofPhase.GRH.ContourShiftExists"
  for f in $files; do
    ns=ProofPhase.GRH.CS; case "$f" in ContourShiftTie|ContourShiftExists) ns=ProofPhase.GRH.CSTie;; esac
    awk '
      { sub(/^@\[[a-z]+\] /, "") }
      /^(theorem|def|structure|abbrev) [A-Za-z_]/ {
        n = $2; sub(/[^A-Za-z0-9_ℝ₀'"'"'].*$/, "", n); print n
      }' "ProofPhase/GRH/$f.lean" | while read -r n; do echo "#print axioms $ns.$n"; done
  done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== imports of the core files (expected: Mathlib.* and ProofPhase.GRH.ContourShift* only)"
for f in $core; do grep -h "^import" "ProofPhase/GRH/$f.lean"; done | sort -u
echo "== source grep"
paths=""; for f in $files; do paths="$paths ProofPhase/GRH/$f.lean"; done
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" $paths ||
  echo "no sorry / admit / native_decide / axiom in$paths"
