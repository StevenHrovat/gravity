#!/usr/bin/env bash
# m1-tools, Lean phase: build the four UV-TV modules in ~/formal-m1, print the axioms of every theorem, grep for
# sorry / native_decide / axiom declarations.
#   wsl -d ym-replay -u ym -- bash -l /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/m1-tools/axioms-uvtv.sh
# Needs ~/formal-m1 with a Mathlib .lake (mkdir -p ~/formal-m1 && cp -a ~/formal/.lake ~/formal-m1/); delete it afterwards.
set -uo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-m1 bash sync-build.sh ProofPhase.M1.UVTVScale 2>&1 | tail -1
FORMAL_DST=~/formal-m1 bash sync-build.sh ProofPhase.M1.UVTVInterface 2>&1 | tail -1
cd ~/formal-m1
source ~/.elan/env
{
  echo "import ProofPhase.M1.UVTVScale"
  echo "import ProofPhase.M1.UVTVInterface"
  echo "open ProofPhase.M1.UVTV"
  for t in ScaleHyp.v_nonneg ScaleHyp.v_self ScaleHyp.v_le ScaleHyp.indicator_eq_mul ScaleHyp.weighted_influence \
           ScaleHyp.weights ScaleHyp.one_sub_mul_cmin_pos ScaleHyp.real_disagree_le_phi ScaleHyp.exists_coupling_pointwise \
           ScaleHyp.srcKernel_le ScaleHyp.exists_coupling_target map_sum_smul real_sum_smul isProbabilityMeasure_sum_smul \
           real_mixture_le real_differOn_le measurableSet_differOn scale_front abs_integral_sub_le_differOn \
           scale_front_integral \
           bracket_nonneg bracket_mono front_lower front_half measure_compl_le_chain geom_sum_le_inv sum_geom_le \
           rpow_scale rpow_neg_lt_one front_advance front_advance_rpow \
           Bdd1.condExp Bdd1.mul Bdd1.integrable integrable_condExp_mul_condExp filtration_le condExp_ccov_step \
           sum_condExp_ccov condExp_top condExp_ccov_base total_cov_ae total_cov_integral_le integrable_ccov \
           ccov_integral_le_local statementB statementB_geom \
           integral_mul_eq_condExp_mul os_cross_le mem_closure_of_os mem_closure_of_tendsto gap_of_density gap_of_UVTV; do
    echo "#print axioms ProofPhase.M1.UVTV.$t"
  done
} > ~/formal-m1/AxiomsUVTV.lean
lake env lean ~/formal-m1/AxiomsUVTV.lean
echo "--- grep (sorry / native_decide / axiom declarations):"
grep -nE "\bsorry\b|native_decide|^axiom|^\s*axiom " ProofPhase/M1/UVTV*.lean || echo "none"
