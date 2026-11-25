#!/usr/bin/env bash
# GRH attempt, Tate round: build ProofPhase.GRH.Tate, run #print axioms on every theorem, grep for
# sorry / admit / native_decide / axiom. Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/rh-guide/grh/axioms-tate.sh > docs/rh-guide/grh/axioms-tate.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-bridge; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-bridge}
src="$(cd "$(dirname "$0")/../../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.GRH.Tate"
bash sync-build.sh ProofPhase.GRH.Tate 2>&1 | grep -E "GRH/.*(warning|error)|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
{
  echo "import ProofPhase.GRH.Tate"
  for t in local_factor_unimodular prime_lattices_disjoint form_two_point zero_diag_indefinite local_assembly_forces_arch runs_and_mirror_on_line; do
    echo "#print axioms ProofPhase.GRH.$t"
  done
} > /tmp/AxiomsTate.lean
echo "== axioms"
lake env lean /tmp/AxiomsTate.lean
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/GRH/Tate.lean || echo "no sorry / admit / native_decide / axiom in Tate.lean"
