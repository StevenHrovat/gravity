#!/usr/bin/env bash
# Birch-Swinnerton-Dyer round (BSD.md): build ProofPhase.Unified.BSDCore (the Mathlib-only core) and
# ProofPhase.Unified.BSDAPI (the instance of the DMP API), run #print axioms on every declaration of both files (names
# read from the source, nested namespaces tracked), list the imports of the core, and grep both files for
# sorry / admit / native_decide / axiom.
# Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/bsd-axioms.sh > docs/unified/bsd-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-bsd; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-bsd}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
# module file : namespace of its declarations
mods=("BSDCore:ProofPhase.BSD" "BSDAPI:ProofPhase.API.BSD")
cd "$src"
for m in "${mods[@]}"; do
  f=${m%%:*}
  echo "== build ProofPhase.Unified.$f"
  bash sync-build.sh "ProofPhase.Unified.$f" 2>&1 | grep -E "(warning|error).*$f\.lean|$f\.lean.*(warning|error)|^error|Build completed" || true
done
echo "== imports of the core (must be Mathlib only)"
grep -nE "^import" "$src/ProofPhase/Unified/BSDCore.lean"
cd "$FORMAL_DST"
source ~/.elan/env
for m in "${mods[@]}"; do
  f=${m%%:*}; ns=${m##*:}
  tmp=$(mktemp /tmp/AxiomsBSD.XXXXXX.lean)
  {
    echo "import ProofPhase.Unified.$f"
    awk -v ns="$ns" '
      /^namespace / { if ($2 != ns) sub_ns = $2 "." }
      /^end / { if ($2 != ns) sub_ns = "" }
      /^(theorem|def|structure|inductive|abbrev) / { name = $2; print "#print axioms " ns "." sub_ns name }
    ' "ProofPhase/Unified/$f.lean"
  } > "$tmp"
  echo "== $f: declarations: $(grep -c '#print' "$tmp")"
  echo "== $f: axioms"
  lake env lean "$tmp" 2>&1
  rm -f "$tmp"
  echo "== $f: source grep"
  grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" "ProofPhase/Unified/$f.lean" || echo "no sorry / admit / native_decide / axiom in ProofPhase/Unified/$f.lean"
done
echo "== External and OpenStep slots in the instance"
grep -nE "External \"|OpenStep \"" "ProofPhase/Unified/BSDAPI.lean" | sed -E 's/^([0-9]+):\s*/\1: /' | cut -c1-140
