#!/usr/bin/env bash
# ScaleHyp kit: build the five modules of formal/ProofPhase/ScaleHyp/ in ~/formal-sh, recompile each file to show its
# warnings, print the axioms of every declaration, grep for sorry / native_decide / axiom declarations.
#   wsl -d ym-replay -u ym -- bash -l /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/scalehyp/axioms.sh
# Needs ~/formal-sh with a Mathlib .lake (mkdir -p ~/formal-sh && cp -a ~/formal/.lake ~/formal-sh/); delete it afterwards.
set -uo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-sh bash sync-build.sh ProofPhase.ScaleHyp.ScaleInst 2>&1 | tail -1
cd ~/formal-sh
source ~/.elan/env
echo "--- warnings and errors per file (lake env lean):"
for m in MaxCoupling KernelCoupling BoxLaw Counting ScaleInst; do
  n=$(lake env lean ProofPhase/ScaleHyp/$m.lean 2>&1 | grep -cE "^ProofPhase.*: (warning|error)")
  echo "$m.lean: $n"
done
{
  echo "import ProofPhase.ScaleHyp.ScaleInst"
  for t in overlap excess maxCoupling measurable_diag measurable_excess overlap_comm overlap_le one_sub_overlap_ne_top \
           lintegral_excess lintegral_excess\' withDensity_excess_univ withDensity_excess_univ\' inv_smul_smul_of_univ \
           min_add_excess min_add_excess\' maxCoupling_map_fst maxCoupling_map_snd isProbabilityMeasure_maxCoupling \
           maxCoupling_apply_le le_overlap_of_ratio maxCoupling_real_le_of_ratio \
           mapParam mapParam_apply isMarkovKernel_mapParam measurable_overlap isFiniteKernel_withDensity_const \
           measurable_maxCoupling maxCouplingKernel maxCouplingKernel_apply isMarkovKernel_maxCouplingKernel \
           glue glue_of_mem glue_of_notMem glue_glue_right measurable_glue measurable_glue_left measurable_glue_swap \
           IsSplit lintegral_split isSplit_pi boxZ condDens boxZ_glue condDens_glue condDens_of_good measurable_boxZ \
           measurable_condDens lintegral_condDens boxLaw isMarkovKernel_condDensKernel boxLaw_apply isMarkovKernel_boxLaw \
           boxLaw_apply_set boxLaw_glue boxLaw_local boxLaw_dlr \
           hcount_of_range tdist natAbs_valMinAbs_add_le tdist_self tdist_triangle natAbs_valMinAbs_sub_le_of_cast \
           offsets boxes mem_boxes card_boxes coverage_boxes offsets_nonempty tdist_offsets_le tdist_boxes_le ball \
           card_ball_le nearW card_near_le torus_hcount \
           BoxDensities.μ BoxDensities.μ\' BoxDensities.q BoxDensities.q\' BoxDensities.ρ BoxDensities.ρ\' \
           BoxDensities.pairGlue BoxDensities.measurable_pairGlue BoxDensities.measurable_pairGlue_left \
           BoxDensities.measurable_ρ BoxDensities.measurable_ρ\' BoxDensities.measurable_ρ_apply \
           BoxDensities.measurable_ρ\'_apply BoxDensities.lintegral_ρ BoxDensities.lintegral_ρ\' BoxDensities.goodQ \
           BoxDensities.srcQ BoxDensities.Q BoxDensities.goodQ_apply BoxDensities.srcQ_apply BoxDensities.Q_fst \
           BoxDensities.Q_snd BoxDensities.spec BoxDensities.delta BoxDensities.delta_nonneg BoxDensities.Q_differOn_le \
           BoxDensities.scaleHyp BoxDensities.scaleHyp_γ BoxDensities.scaleHyp_torus BoxDensities.ofProduct \
           BoxDensities.nonempty_scaleHyp_torus_product; do
    echo "#print axioms ProofPhase.ScaleHypKit.$t"
  done
} > ~/formal-sh/AxiomsScaleHyp.lean
lake env lean ~/formal-sh/AxiomsScaleHyp.lean
echo "--- grep (sorry / native_decide / axiom declarations):"
grep -nE "\bsorry\b|native_decide|^axiom|^\s*axiom " ProofPhase/ScaleHyp/*.lean || echo "none"
