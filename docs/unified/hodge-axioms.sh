#!/usr/bin/env bash
# Hodge round (HODGE.md): build ProofPhase.Unified.HodgeLinear (the Mathlib-only core) and ProofPhase.Unified.HodgeAPI
# (the instance of the DMP API), run #print axioms on every declaration of both files (full names rebuilt from the
# namespace blocks of the source), and grep both for sorry / admit / native_decide / axiom.
# Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/hodge-axioms.sh > docs/unified/hodge-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-hodge; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-hodge}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
mods=(HodgeLinear HodgeAPI)
cd "$src"
for f in "${mods[@]}"; do
  echo "== build ProofPhase.Unified.$f"
  bash sync-build.sh "ProofPhase.Unified.$f" 2>&1 | grep -E "(warning|error).*$f\.lean|$f\.lean.*(warning|error)|^warning|^error|Build completed" || true
done
cd "$FORMAL_DST"
source ~/.elan/env
for f in "${mods[@]}"; do
  tmp=$(mktemp /tmp/AxiomsHodge.XXXXXX.lean)
  {
    echo "import ProofPhase.Unified.$f"
    awk '
      /^namespace / { st[++d] = "n:" $2; next }
      /^(noncomputable )?section/ { st[++d] = "s:"; next }
      /^end( |$)/ { d--; next }
      /^(theorem|def|structure|inductive|abbrev) [A-Za-z_]/ {
        p = ""; for (i = 1; i <= d; i++) if (substr(st[i], 1, 2) == "n:") p = p substr(st[i], 3) ".";
        print "#print axioms " p $2
      }' "ProofPhase/Unified/$f.lean"
  } > "$tmp"
  echo "== $f: declarations: $(grep -c '#print' "$tmp")"
  echo "== $f: axioms"
  lake env lean "$tmp" 2>&1
  rm -f "$tmp"
  echo "== $f: source grep"
  grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" "ProofPhase/Unified/$f.lean" || echo "no sorry / admit / native_decide / axiom in ProofPhase/Unified/$f.lean"
done
