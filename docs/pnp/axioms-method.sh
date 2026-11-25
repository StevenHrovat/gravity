#!/usr/bin/env bash
# Native method: build ProofPhase/Native/Method and ProofPhase/Native/RouteBChain, check that the re-proved bounds have
# exactly the statements of the originals (the kernel accepts `rfl` between the two proofs only if their types agree),
# run #print axioms on every declaration of both files, and grep the sources for sorry / admit / native_decide / axiom.
# Run inside the WSL replay distro (Lean 4.34.0, Mathlib v4.34.0), from the repository root as seen from WSL:
#   bash docs/pnp/axioms-method.sh > docs/pnp/axioms-method.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-proof; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-proof}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
for m in Method RouteBChain; do
  echo "== build ProofPhase.Native.$m"
  bash sync-build.sh ProofPhase.Native.$m 2>&1 | grep -E "^(warning|error).*Native/|Build completed" || true
done
cd "$FORMAL_DST"
source ~/.elan/env
method="fixed_after_aux fixed_after excess_iterate_le reaches_floor real_iterate real_never_arrives pairUp length_pairUp
  sum_pairUp le_two_mul_of_mem_pairUp ceil_half_step length_iterate_pairUp iterate_clog_pairUp"
route="abs_ccorr_le' abs_nCorr_le'"
tmp=$(mktemp --suffix=.lean)
{
  echo "import ProofPhase.Native.Method"
  echo "import ProofPhase.Native.RouteBChain"
  echo "example : @ProofPhase.RouteB.abs_ccorr_le' = @ProofPhase.RouteB.abs_ccorr_le := rfl"
  echo "example : @ProofPhase.RouteB.abs_nCorr_le' = @ProofPhase.RouteB.abs_nCorr_le := rfl"
  for t in $method; do echo "#print axioms ProofPhase.Native.$t"; done
  for t in $route; do echo "#print axioms ProofPhase.RouteB.$t"; done
} > "$tmp"
echo "== same statements (no output before the axiom lines = accepted), then axioms ($(echo $method $route | wc -w) declarations)"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Native/*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Native"
