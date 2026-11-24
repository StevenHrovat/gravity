#!/usr/bin/env bash
# CP duality (two channels, positivity, pairs): build ProofPhase/Proof/CPDuality (and the Proof modules it imports), run
# #print axioms on every declaration of CPDuality.lean, then grep the Proof sources for sorry / admit / native_decide /
# axiom. Run inside the WSL replay distro (Lean 4.34.0, Mathlib v4.34.0), from the repository root as seen from WSL:
#   bash docs/pnp/axioms-edge.sh > docs/pnp/axioms-edge.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-proof; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-proof}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.Proof.CPDuality"
bash sync-build.sh ProofPhase.Proof.CPDuality 2>&1 | grep -E "warning|error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
names="Edge.ForcesTrue Edge.ForcesFalse Edge.thr_true_card Edge.thr_false_card Edge.thr_true_cert Edge.thr_false_cert Edge.thr_duality Edge.wline Edge.filter_all_but Edge.filter_all Edge.two_cheap Edge.lpVal Edge.half_clause Edge.half_breaks_rounding Edge.split_unsat_iff Edge.interpolant_separates"
tmp=$(mktemp --suffix=.lean)
{
  echo "import ProofPhase.Proof.CPDuality"
  for t in $names; do echo "#print axioms ProofPhase.Proof.$t"; done
} > "$tmp"
echo "== axioms ($(echo $names | wc -w) declarations)"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Proof/*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Proof"
