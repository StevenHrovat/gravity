#!/usr/bin/env bash
# CP pairs (fan line, creative pair): build ProofPhase/Proof/CPPairs (and the Proof modules it imports), run
# #print axioms on every declaration of CPPairs.lean, then grep the Proof sources for sorry / admit / native_decide /
# axiom. Run inside the WSL replay distro (Lean 4.34.0, Mathlib v4.34.0), from the repository root as seen from WSL:
#   bash docs/pnp/axioms-edge.sh > docs/pnp/axioms-edge.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-proof; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-proof}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.Proof.CPPairs"
bash sync-build.sh ProofPhase.Proof.CPPairs 2>&1 | grep -E "warning|error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
names="Edge.fan Edge.fan_sum Edge.fan_iff Edge.fan_cheap Edge.HoldsAt Edge.addL Edge.scaleL Edge.roundL Edge.CPD Edge.holds_add Edge.holds_scale Edge.round_single Edge.creative_pair Edge.refutation_needs_pair"
tmp=$(mktemp --suffix=.lean)
{
  echo "import ProofPhase.Proof.CPPairs"
  for t in $names; do echo "#print axioms ProofPhase.Proof.$t"; done
} > "$tmp"
echo "== axioms ($(echo $names | wc -w) declarations)"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Proof/*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Proof"
