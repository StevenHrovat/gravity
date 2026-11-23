#!/usr/bin/env bash
# RH-YM bridge, Part 1: build the four Lean modules of ProofPhase/Bridge, run #print axioms on every theorem, then grep
# the sources for sorry / admit / native_decide / axiom. Run inside the WSL replay distro (Lean 4.34.0, Mathlib v4.34.0),
# from the repository root as seen from WSL:
#   bash docs/rh-guide/bridge/axioms.sh > docs/rh-guide/bridge/axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-bridge; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-bridge}
src="$(cd "$(dirname "$0")/../../mass-gap/formal" && pwd)"
cd "$src"
for m in Pringsheim Landau Laplace Spectral; do
  echo "== build ProofPhase.Bridge.$m"
  bash sync-build.sh ProofPhase.Bridge.$m 2>&1 | grep -E "warning|error|Build completed" || true
done
cd "$FORMAL_DST"
source ~/.elan/env
{
  for m in Pringsheim Landau Laplace Spectral; do echo "import ProofPhase.Bridge.$m"; done
  for t in pringsheim_hasSum pringsheim_summable glue_differentiableOn pringsheim_extension \
           logMul_iterate_apply abscissaOfAbsConv_logMul_iterate eq_ofReal_re_of_nonneg term_logMul_iterate \
           landauCoeff_term_nonneg landauCoeff_summable iteratedDeriv_LSeries_eq landauDouble_nonneg landauDouble_row \
           landauDouble_col lseriesSummable_of_taylor landau_summable_left landau landau_ray landau_ray_differentiable \
           lap_eq_lapN_zero LapConv.mono pow_le_factorial_mul_exp norm_lapTerm_le integrable_lapTerm hasDerivAt_lapN \
           iteratedDeriv_lap lapN_ofReal integrable_moment lapConv_of_taylor laplace_conv_left laplace_landau laplace_ray \
           lap_ofReal_eq_corr integrable_corr corr_le_of_gap corr_ge gap_of_decay_nat spectral_gap_iff_nat \
           spectral_gap_iff decayRates_eq measurable_corr corrMeasure_nonneg lintegral_corrMeasure lapConv_corr_of_gap \
           not_lapConv_corr resolvent_singular; do
    echo "#print axioms ProofPhase.Bridge.$t"
  done
} > /tmp/AxiomsBridge.lean
echo "== axioms"
lake env lean /tmp/AxiomsBridge.lean
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Bridge/*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Bridge"
