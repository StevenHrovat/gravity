#!/usr/bin/env bash
# NP vs coNP sound APIs: build ProofPhase.Proof.SoundAPI (it imports LiftingNP), run #print axioms on every declaration
# of ProofPhase/Proof/SoundAPI.lean (names read from the source), and grep for sorry / admit / native_decide / axiom.
# Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/soundapi-axioms.sh > docs/unified/soundapi-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-soundapi; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-soundapi}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.Proof.SoundAPI"
bash sync-build.sh ProofPhase.Proof.SoundAPI 2>&1 | grep -E "Proof/SoundAPI.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsSoundAPI.XXXXXX.lean)
{
  echo "import ProofPhase.Proof.SoundAPI"
  awk '/^(theorem|def|structure|abbrev|inductive) [A-Za-z_]/ {n = $2; sub(/[^A-Za-z0-9_.'"'"'].*$/, "", n); print n}' \
    "ProofPhase/Proof/SoundAPI.lean" | while read -r n; do echo "#print axioms ProofPhase.Proof.Lifting.$n"; done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Proof/SoundAPI.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Proof/SoundAPI.lean"
