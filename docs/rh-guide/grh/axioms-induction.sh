#!/usr/bin/env bash
# GRH attempt, induction over scales: build ProofPhase.GRH.Induction, run #print axioms on every theorem, grep for
# sorry / admit / native_decide / axiom. Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/rh-guide/grh/axioms-induction.sh > docs/rh-guide/grh/axioms-induction.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-bridge; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-bridge}
src="$(cd "$(dirname "$0")/../../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.GRH.Induction"
bash sync-build.sh ProofPhase.GRH.Induction 2>&1 | grep -E "GRH/.*(warning|error)|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
{
  echo "import ProofPhase.GRH.Induction"
  for t in norm_le_of_exp_bound toep_moment_bound atomic_toep_nonneg atoms_inside_circle atoms_on_circle; do
    echo "#print axioms ProofPhase.GRH.$t"
  done
} > /tmp/AxiomsInd.lean
echo "== axioms"
lake env lean /tmp/AxiomsInd.lean
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/GRH/Induction.lean || echo "no sorry / admit / native_decide / axiom in Induction.lean"
