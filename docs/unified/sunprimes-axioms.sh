#!/usr/bin/env bash
# SU(N) with primes as the base: build ProofPhase.General.SUNTwistInstances (it imports SUNTwist, SUNTwistSchur,
# SUNTwistSectors, SUNTwistPrimes, SUNTwistWilson), run #print axioms on every declaration of the six
# ProofPhase/General/SUNTwist*.lean files (names read from the sources, dotted names such as ZFam.Zk included), and grep
# for sorry / admit / native_decide / axiom. Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/sunprimes-axioms.sh > docs/unified/sunprimes-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-suntwist; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-suntwist}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.General.SUNTwistInstances"
bash sync-build.sh ProofPhase.General.SUNTwistInstances 2>&1 | grep -E "General/SUNTwist.*error|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsSUNPrimes.XXXXXX.lean)
files="SUNTwist SUNTwistSchur SUNTwistSectors SUNTwistPrimes SUNTwistWilson SUNTwistInstances"
{
  echo "import ProofPhase.General.SUNTwistInstances"
  for f in $files; do
    awk '/^(theorem|def|structure|abbrev) [A-Za-z_]/ {n = $2; sub(/[^A-Za-z0-9_.'"'"'].*$/, "", n); print n}' \
      "ProofPhase/General/$f.lean" | while read -r n; do echo "#print axioms ProofPhase.General.$n"; done
  done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/General/SUNTwist*.lean ||
  echo "no sorry / admit / native_decide / axiom in ProofPhase/General/SUNTwist*.lean"
