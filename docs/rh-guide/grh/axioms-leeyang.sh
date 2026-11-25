#!/usr/bin/env bash
# GRH attempt, Lee-Yang route: build ProofPhase.GRH.LeeYang, run #print axioms on every theorem, grep for sorry /
# admit / native_decide / axiom. Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/rh-guide/grh/axioms-leeyang.sh > docs/rh-guide/grh/axioms-leeyang.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-bridge; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-bridge}
src="$(cd "$(dirname "$0")/../../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.GRH.LeeYang"
bash sync-build.sh ProofPhase.GRH.LeeYang 2>&1 | grep -E "GRH/.*(warning|error)|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
{
  echo "import ProofPhase.GRH.LeeYang"
  for t in lee_yang_identity lee_yang_pair asano_bound asano chain3_ne_zero ising3_flip ising3_zeros_on_circle \
           pair_zeros_on_circle; do
    echo "#print axioms ProofPhase.GRH.$t"
  done
} > /tmp/AxiomsLY.lean
echo "== axioms"
lake env lean /tmp/AxiomsLY.lean
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/GRH/LeeYang.lean || echo "no sorry / admit / native_decide / axiom in LeeYang.lean"
