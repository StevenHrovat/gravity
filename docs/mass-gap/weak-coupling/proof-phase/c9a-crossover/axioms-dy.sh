#!/usr/bin/env bash
# Print the axioms of the declarations of ProofPhase.Crossover.Dichotomy .WellDefined, .FluxRate, .HandOver, .CompositeHTF, .Neighbours, .RDoeblin and .Runs (build first with build-dy.sh).
set -euo pipefail
cd ~/formal-dy
source ~/.elan/env
f=$(mktemp /tmp/dy_axioms_XXXX.lean)
{
  echo "import ProofPhase.Crossover.Dichotomy"
  echo "import ProofPhase.Crossover.WellDefined"
  echo "import ProofPhase.Crossover.FluxRate"
  echo "import ProofPhase.Crossover.HandOver"
  echo "import ProofPhase.Crossover.CompositeHTF"
  echo "import ProofPhase.Crossover.Neighbours"
  echo "import ProofPhase.Crossover.RDoeblin"
  echo "import ProofPhase.Crossover.Runs"
  for n in cob_restrict_eq_cob_restrict_compl cob_restrict_eq_zero_of_interior cob_restrict_eq_zero_of_exterior \
    boundaryCell_of_cob_restrict not_uncontained measure_uncontained sum_cob_restrict_eq_zero window_gap \
    exists_mem_of_full_of_pos no_uniform_lower_bound_on_full not_exists_full_with_bound \
    exists_sheet_of_flux exists_sheet_both_sides card_fluxCells_le even_card_fluxCells two_le_card_fluxCells \
    two_le_mul_card_sheetIn cost_ge_threshold_count sheet_cost_ge \
    handover_ratio log_one_add_sqrt_two_le_max su2_handover \
    weight_fiber_eq weight_fiber_mul_card sum_pow_add_le flux_superadd flux_superadd_iter \
    handover_column_sum_iff column_requirement neg_log_one_sub_le doeblin_mass_tendsto_zero phys_rate_of_uniform \
    rdoeblin_family one_sub_pow_eq_exp rdoeblin_physical_decay floor_column_requirement floor_disagreement_requirement \
    min_le_of_sector_product selfdual_sector_ge_one electric_sum_lt_one_iff eig_norm_le_of_contraction iterate_contraction no_phase_mode runs_two_targets; do
    echo "#print axioms ProofPhase.Crossover.$n"
  done
} > "$f"
lake env lean "$f"
rm -f "$f"
