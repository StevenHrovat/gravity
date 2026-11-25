#!/usr/bin/env bash
# Native reorganization: build ProofPhase/Proof/Native, check that its two main theorems have exactly the statements of
# the originals (the kernel accepts `rfl` between the two proofs only if their types agree), run #print axioms on every
# declaration of Native.lean, and grep the Proof sources for sorry / admit / native_decide / axiom. Run inside the WSL
# replay distro (Lean 4.34.0, Mathlib v4.34.0), from the repository root as seen from WSL:
#   bash docs/pnp/axioms-native.sh > docs/pnp/axioms-native.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-proof; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-proof}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.Proof.Native"
bash sync-build.sh ProofPhase.Proof.Native 2>&1 | grep -E "warning|error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
names="SDG SDG.good SDG.impliesL_univ exists_middleG crossG ClauseLine WD.toSDG mem_of_sensitive width_ge' SD.toSDG
  cross_any_system'"
tmp=$(mktemp --suffix=.lean)
{
  echo "import ProofPhase.Proof.Native"
  echo "example : @ProofPhase.Proof.Native.width_ge' = @ProofPhase.Proof.width_ge := rfl"
  echo "example : @ProofPhase.Proof.Native.cross_any_system' = @ProofPhase.Proof.cross_any_system := rfl"
  for t in $names; do echo "#print axioms ProofPhase.Proof.Native.$t"; done
} > "$tmp"
echo "== same statements (no output before the axiom lines = accepted), then axioms ($(echo $names | wc -w) declarations)"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Proof/*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Proof"
