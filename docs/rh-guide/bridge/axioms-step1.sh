#!/usr/bin/env bash
# RH-YM bridge, step 1 (sign argument and OS link): build ProofPhase.Bridge.Poles and .OSLink, run #print axioms on
# every theorem, grep the sources for sorry / admit / native_decide / axiom. Run inside the WSL replay distro from the
# repository root as seen from WSL:
#   bash docs/rh-guide/bridge/axioms-step1.sh > docs/rh-guide/bridge/axioms-step1.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-bridge; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-bridge}
src="$(cd "$(dirname "$0")/../../mass-gap/formal" && pwd)"
cd "$src"
for m in Poles OSLink; do
  echo "== build ProofPhase.Bridge.$m"
  bash sync-build.sh ProofPhase.Bridge.$m 2>&1 | grep -E "Bridge/.*(warning|error)|Build completed" || true
done
cd "$FORMAL_DST"
source ~/.elan/env
{
  for m in Poles OSLink; do echo "import ProofPhase.Bridge.$m"; done
  for t in residue_nonneg_of_re_nonneg mem_ball_of_real lap_re_nonneg laplace_residue_nonneg laplace_ray_poles \
           lseries_re_nonneg lseries_residue_nonneg landau_ray_poles \
           integrable_pow_of_unit moment_gap_iff hdec_iff_spectral hdec_iff_energy gap_of_RP_spectral; do
    echo "#print axioms ProofPhase.Bridge.$t"
  done
} > /tmp/AxiomsBridge1.lean
echo "== axioms"
lake env lean /tmp/AxiomsBridge1.lean
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Bridge/Poles.lean ProofPhase/Bridge/OSLink.lean \
  || echo "no sorry / admit / native_decide / axiom in Poles.lean, OSLink.lean"
