#!/usr/bin/env bash
# P vs NP dictionary: build the three Lean modules of ProofPhase/Mixing, run #print axioms on every declaration, then
# grep the sources for sorry / admit / native_decide / axiom. Run inside the WSL replay distro (Lean 4.34.0, Mathlib
# v4.34.0), from the repository root as seen from WSL:
#   bash docs/pnp/axioms.sh > docs/pnp/axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-mix; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-mix}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
for m in Glauber TimeGap Link; do
  echo "== build ProofPhase.Mixing.$m"
  bash sync-build.sh ProofPhase.Mixing.$m 2>&1 | grep -E "warning|error|Build completed" || true
done
cd "$FORMAL_DST"
source ~/.elan/env
top="isProbabilityMeasure_bind bind_real integrable_kernel_real fst_preimage_subset snd_preimage_subset abs_sub_le_phi
  phi_one_le_card avg card_mul_pow_le one_sub_div_pow_le card_mul_exp_le
  acorr rateMeasure measurable_negLog rateMeasure_nonneg rateMeasure_Iio corr_rateMeasure corr_zero acorr_zero
  time_gap_iff exp_neg_neg_log gap_of_geometric geometric_of_gap"
sd="bind_map_fst bind_map_snd bind_disagree_le_of_ne bind_disagree_le_self sweep sweepC sweepC_map_fst sweepC_map_snd
  sweep_inv isProbabilityMeasure_sweepC sweepC_disagree_le sweepC_contract sweepsC isProbabilityMeasure_sweepsC
  sweepsC_map_fst sweepsC_map_snd sweepsC_disagree_le tv_sweep_le integral_sweep_le rsStep rsStepC avg_apply
  card_inv_mul_card rsStepC_map_fst rsStepC_map_snd rsStep_inv isProbabilityMeasure_rsStepC rsStepC_real
  phi_rsStepC_le rsStepsC isProbabilityMeasure_rsStepsC rsStepsC_map_fst rsStepsC_map_snd phi_rsStepsC_le tv_rs_le
  integral_rs_le mixing_sweep mixing_rs rsPow timeCorr timeCorr_le spectral_gap_of_column"
{
  for m in Glauber TimeGap Link; do echo "import ProofPhase.Mixing.$m"; done
  for t in $top; do echo "#print axioms ProofPhase.Mixing.$t"; done
  for t in $sd; do echo "#print axioms ProofPhase.Mixing.SiteDynamics.$t"; done
} > /tmp/AxiomsMixing.lean
echo "== axioms"
lake env lean /tmp/AxiomsMixing.lean
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Mixing/*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Mixing"
