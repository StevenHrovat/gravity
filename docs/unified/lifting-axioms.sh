#!/usr/bin/env bash
# NP vs coNP lifting: build ProofPhase.Proof.LiftingNP (it imports Lifting), run #print axioms on every declaration of
# ProofPhase/Proof/Lifting.lean and LiftingNP.lean (names read from the sources), and grep for sorry / admit /
# native_decide / axiom. Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/lifting-axioms.sh > docs/unified/lifting-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-lifting; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-lifting}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.Proof.LiftingNP"
bash sync-build.sh ProofPhase.Proof.LiftingNP 2>&1 | grep -E "Proof/Lifting.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsLifting.XXXXXX.lean)
{
  echo "import ProofPhase.Proof.LiftingNP"
  for f in Lifting LiftingNP; do
    awk '/^(theorem|def|structure|abbrev|inductive) [A-Za-z_]/ {n = $2; sub(/[^A-Za-z0-9_.'"'"'].*$/, "", n); print n}' \
      "ProofPhase/Proof/$f.lean" | while read -r n; do echo "#print axioms ProofPhase.Proof.Lifting.$n"; done
  done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Proof/Lifting*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Proof/Lifting*.lean"
