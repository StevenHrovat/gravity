#!/usr/bin/env bash
# Print the axioms of the declarations of ProofPhase.Crossover.Dichotomy and .WellDefined (build first with build-dy.sh).
set -euo pipefail
cd ~/formal-dy
source ~/.elan/env
f=$(mktemp /tmp/dy_axioms_XXXX.lean)
{
  echo "import ProofPhase.Crossover.Dichotomy"
  echo "import ProofPhase.Crossover.WellDefined"
  for n in cob_restrict_eq_cob_restrict_compl cob_restrict_eq_zero_of_interior cob_restrict_eq_zero_of_exterior \
    boundaryCell_of_cob_restrict not_uncontained measure_uncontained sum_cob_restrict_eq_zero window_gap \
    exists_mem_of_full_of_pos no_uniform_lower_bound_on_full not_exists_full_with_bound; do
    echo "#print axioms ProofPhase.Crossover.$n"
  done
} > "$f"
lake env lean "$f"
rm -f "$f"
