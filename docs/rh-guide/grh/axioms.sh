#!/usr/bin/env bash
# GRH attempt, step 2a: build ProofPhase.GRH.Weil, run #print axioms on every theorem, grep for sorry / admit /
# native_decide / axiom. Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/rh-guide/grh/axioms.sh > docs/rh-guide/grh/axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-bridge; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-bridge}
src="$(cd "$(dirname "$0")/../../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.GRH.Weil"
bash sync-build.sh ProofPhase.GRH.Weil 2>&1 | grep -E "GRH/.*(warning|error)|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
{
  echo "import ProofPhase.GRH.Weil"
  for t in weilSum_re_nonneg_of_real real_of_weilSum_nonneg exists_step_injOn approx_finite weil_criterion_finite; do
    echo "#print axioms ProofPhase.GRH.$t"
  done
} > /tmp/AxiomsGRH.lean
echo "== axioms"
lake env lean /tmp/AxiomsGRH.lean
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/GRH/*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/GRH"
