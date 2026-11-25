#!/usr/bin/env bash
# GRH attempt, closed-orbit route: build ProofPhase.GRH.Orbits, run #print axioms on every theorem, grep for sorry /
# admit / native_decide / axiom. Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/rh-guide/grh/axioms-orbits.sh > docs/rh-guide/grh/axioms-orbits.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-bridge; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-bridge}
src="$(cd "$(dirname "$0")/../../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.GRH.Orbits"
bash sync-build.sh ProofPhase.GRH.Orbits 2>&1 | grep -E "GRH/.*(warning|error)|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
{
  echo "import ProofPhase.GRH.Orbits"
  for t in card_fixed_pow_eq_sum similitude_eigenvalue skew_shift_re_half kreinForm_hermitian kreinForm_indefinite \
           krein_mirror krein_off_line; do
    echo "#print axioms ProofPhase.GRH.$t"
  done
} > /tmp/AxiomsOrb.lean
echo "== axioms"
lake env lean /tmp/AxiomsOrb.lean
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/GRH/Orbits.lean || echo "no sorry / admit / native_decide / axiom in Orbits.lean"
