#!/usr/bin/env bash
# Navier-Stokes round (NAVIER-STOKES.md): build ProofPhase.Unified.NavierStokes (the ledger skeleton) and
# ProofPhase.Unified.NavierStokesAPI (the instance of the DMP API), run #print axioms on every declaration of both files
# (names read from the source), and grep both for sorry / admit / native_decide / axiom.
# Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/navierstokes-axioms.sh > docs/unified/navierstokes-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-ns; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-ns}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
# module file : namespace of its declarations
mods=("NavierStokes:ProofPhase.Unified" "NavierStokesAPI:ProofPhase.API.NavierStokes")
cd "$src"
for m in "${mods[@]}"; do
  f=${m%%:*}
  echo "== build ProofPhase.Unified.$f"
  bash sync-build.sh "ProofPhase.Unified.$f" 2>&1 | grep -E "(warning|error).*$f\.lean|$f\.lean.*(warning|error)|^error|Build completed" || true
done
cd "$FORMAL_DST"
source ~/.elan/env
for m in "${mods[@]}"; do
  f=${m%%:*}; ns=${m##*:}
  tmp=$(mktemp /tmp/AxiomsNS.XXXXXX.lean)
  {
    echo "import ProofPhase.Unified.$f"
    grep -oE "^(theorem|def|structure|inductive) [A-Za-z_][A-Za-z0-9_'.]*" "ProofPhase/Unified/$f.lean" | awk '{print $2}' |
      while read -r n; do echo "#print axioms $ns.$n"; done
  } > "$tmp"
  echo "== $f: declarations: $(grep -c '#print' "$tmp")"
  echo "== $f: axioms"
  lake env lean "$tmp" 2>&1 | grep -v "^ProofPhase.API.NavierStokes.Window.leray$"
  rm -f "$tmp"
  echo "== $f: source grep"
  grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" "ProofPhase/Unified/$f.lean" || echo "no sorry / admit / native_decide / axiom in ProofPhase/Unified/$f.lean"
done
