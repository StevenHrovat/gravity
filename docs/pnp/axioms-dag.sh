#!/usr/bin/env bash
# DAG-like size-width: build ProofPhase/Proof/Dag (and the Proof modules it imports), run
# #print axioms on every declaration of Dag.lean, then grep the Proof sources for sorry / admit / native_decide /
# axiom. Run inside the WSL replay distro (Lean 4.34.0, Mathlib v4.34.0), from the repository root as seen from WSL:
#   bash docs/pnp/axioms-edge.sh > docs/pnp/axioms-edge.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-proof; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-proof}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.Proof.Dag"
bash sync-build.sh ProofPhase.Proof.Dag 2>&1 | grep -E "warning|error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
names="RD rP fat mem_rP RD.toWD RD.nl_inj RD.restr card_fat_rP_le exists_heavy step_arith thin size_width_aux size_width size_width_exp dag_size_ge"
tmp=$(mktemp --suffix=.lean)
{
  echo "import ProofPhase.Proof.Dag"
  for t in $names; do echo "#print axioms ProofPhase.Proof.$t"; done
} > "$tmp"
echo "== axioms ($(echo $names | wc -w) declarations)"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Proof/*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Proof"
