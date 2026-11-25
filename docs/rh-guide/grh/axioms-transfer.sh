#!/usr/bin/env bash
# GRH attempt, transfer round: build ProofPhase.GRH.Transfer, run #print axioms on every theorem, grep for
# sorry / admit / native_decide / axiom. Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/rh-guide/grh/axioms-transfer.sh > docs/rh-guide/grh/axioms-transfer.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-bridge; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-bridge}
src="$(cd "$(dirname "$0")/../../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.GRH.Transfer"
bash sync-build.sh ProofPhase.GRH.Transfer 2>&1 | grep -E "GRH/.*(warning|error)|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
{
  echo "import ProofPhase.GRH.Transfer"
  for t in prod_one_sub_le_exp margin_pos_of_factors two_term_bound; do
    echo "#print axioms ProofPhase.GRH.$t"
  done
} > /tmp/AxiomsTransfer.lean
echo "== axioms"
lake env lean /tmp/AxiomsTransfer.lean
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/GRH/Transfer.lean || echo "no sorry / admit / native_decide / axiom in Transfer.lean"
