#!/usr/bin/env bash
# GRH attempt, mirror tool: build ProofPhase.GRH.Mirror, run #print axioms on every theorem, grep for
# sorry / admit / native_decide / axiom. Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/rh-guide/grh/axioms-mirror.sh > docs/rh-guide/grh/axioms-mirror.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-bridge; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-bridge}
src="$(cd "$(dirname "$0")/../../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.GRH.Mirror"
bash sync-build.sh ProofPhase.GRH.Mirror 2>&1 | grep -E "GRH/.*(warning|error)|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
{
  echo "import ProofPhase.GRH.Mirror"
  for t in zeta_neg_one_mirror eight_pi_sq_mirror zeta_neg_one_val; do
    echo "#print axioms ProofPhase.GRH.$t"
  done
} > /tmp/AxiomsMirror.lean
echo "== axioms"
lake env lean /tmp/AxiomsMirror.lean
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/GRH/Mirror.lean || echo "no sorry / admit / native_decide / axiom in Mirror.lean"
