#!/usr/bin/env bash
# The encoder: build ProofPhase.Unified.EncoderInstances (it imports Encoder), run #print axioms on every declaration of
# ProofPhase/Unified/Encoder.lean and EncoderInstances.lean (names read from the sources, with the Encoder. prefix inside
# `namespace Encoder`), and grep for sorry / admit / native_decide / axiom. Run inside the WSL replay distro from the
# repository root as seen from WSL:
#   bash docs/unified/encoder-axioms.sh > docs/unified/encoder-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-encoder; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-encoder}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.Unified.EncoderInstances"
bash sync-build.sh ProofPhase.Unified.EncoderInstances 2>&1 | grep -E "Unified/Encoder.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsEncoder.XXXXXX.lean)
{
  echo "import ProofPhase.Unified.EncoderInstances"
  for f in Encoder EncoderInstances; do
    awk '/^namespace Encoder/ {p = "Encoder."} /^end Encoder/ {p = ""}
         /^(theorem|def|structure) [A-Za-z_]/ {n = $2; sub(/[^A-Za-z0-9_'"'"'].*$/, "", n); print p n}' \
      "ProofPhase/Unified/$f.lean" | while read -r n; do echo "#print axioms ProofPhase.Unified.$n"; done
  done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Unified/Encoder*.lean ||
  echo "no sorry / admit / native_decide / axiom in ProofPhase/Unified/Encoder*.lean"
