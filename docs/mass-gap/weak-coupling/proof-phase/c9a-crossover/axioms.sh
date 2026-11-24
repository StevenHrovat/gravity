#!/usr/bin/env bash
# Print the axioms of the headline declarations of ProofPhase.Crossover.Openness.
set -euo pipefail
cd ~/formal-c9x
source ~/.elan/env
cat > /tmp/c9a_axioms.lean <<'LEAN'
import ProofPhase.Crossover.Openness
#print axioms ProofPhase.Crossover.isNearSpec_symm
#print axioms ProofPhase.Crossover.isInfluenceBoundOn_of_near
#print axioms ProofPhase.Crossover.influence_of_net
#print axioms ProofPhase.Crossover.oneBoxSum_of_near
#print axioms ProofPhase.Crossover.near_budget_lt_one
LEAN
lake env lean /tmp/c9a_axioms.lean
