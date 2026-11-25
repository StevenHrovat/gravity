#!/usr/bin/env bash
# Uniformity along the chain: build the two Lean modules Doeblin and Chain of ProofPhase/Mixing, run #print axioms on
# every declaration of both, then grep the sources for sorry / admit / native_decide / axiom. Run inside the WSL replay
# distro (Lean 4.34.0, Mathlib v4.34.0), from the repository root as seen from WSL:
#   bash docs/pnp/axioms-chain.sh > docs/pnp/axioms-chain.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-chain; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-chain}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
for m in Doeblin Chain; do
  echo "== build ProofPhase.Mixing.$m"
  bash sync-build.sh ProofPhase.Mixing.$m 2>&1 | grep -E "warning|error|Build completed" || true
done
{
  echo "import ProofPhase.Mixing.Doeblin"
  echo "import ProofPhase.Mixing.Chain"
  for f in Doeblin Chain; do
    grep -hoE "^(theorem|def|abbrev|structure) [A-Za-z0-9_.']+" "$src/ProofPhase/Mixing/$f.lean" | awk '{print $2}' | while read -r n; do
      case "$n" in
        IsStoch) ;; # a structure of Props: no axioms to print for the type itself
        *) echo "#print axioms ProofPhase.Mixing.$n" ;;
      esac
    done
  done
} > /tmp/AxiomsChain.lean
cd "$FORMAL_DST"
source ~/.elan/env
echo "== axioms"
lake env lean /tmp/AxiomsChain.lean
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Mixing/Doeblin.lean ProofPhase/Mixing/Chain.lean || echo "no sorry / admit / native_decide / axiom in Doeblin.lean, Chain.lean"
