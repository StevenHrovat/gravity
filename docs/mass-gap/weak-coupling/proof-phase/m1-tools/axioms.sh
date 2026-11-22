#!/usr/bin/env bash
# m1-tools: #print axioms on every theorem of ProofPhase/M1 (run after build.sh Exact / Dilution / Vortex / Twist / CutAvoid / Assembly / FibreMass / LocalMod / Routine), then grep
# for sorry / native_decide / axiom.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/m1-tools/axioms.sh
cd ~/formal-m1
source ~/.elan/env
{
  echo "import ProofPhase.M1.Exact"
  echo "import ProofPhase.M1.Dilution"
  echo "import ProofPhase.M1.Vortex"
  echo "import ProofPhase.M1.Twist"
  echo "import ProofPhase.M1.CutAvoid"
  echo "import ProofPhase.M1.Assembly"
  echo "import ProofPhase.M1.FibreMass"
  echo "import ProofPhase.M1.LocalMod"
  echo "import ProofPhase.M1.Routine"
  for t in measurable_resample map_resample_eq map_comp_resample_eq map_resample_rnDeriv_eq sum_map_resample_eq \
           norm_wsum_sub_wsum_le spread_avg_le spread_iterate_le geom_of_quadratic spread_iterate_quadratic \
           starW_sub starW_rowsum starW_tv_le balaban_e_sum balaban_star_tv balaban_star_dilution \
           vortex_step blockTower_vortex blockTower_trivial_off vortex_plaquette vortex_persists \
           su2_negOne_central su2_negOne_ne_one su2_negOne_inv twistBlock_one twistBlock_pureGauge twistBlock_gauge twistBlock_sym twistBlock_local rp_map inner_ge_of_cap signCorrect_inner_ge cap_of_away angle_le_two_arccos M1Hypotheses.step_law m1_assembly m1_laws M1RowHypotheses.stepEstimates m1_assembly_rows map_prod_le_of_slices sum_sq_le_of_paths \
           M1RowHypothesesUpTo.stepEstimates m1_assembly_rows_upTo resolvent_left resolvent_right resolvent_two_sided decay_through \
           fibre_rep_of_map_le lintegral_gauge_leaf record_gas_le capSign_sq norm_capSign_smul; do
    echo "#print axioms ProofPhase.M1.$t"
  done
} > /tmp/AxiomsM1.lean
lake env lean /tmp/AxiomsM1.lean
grep -n "sorry\|native_decide\|^axiom" ProofPhase/M1/*.lean || echo "no sorry / native_decide / axiom in ProofPhase/M1"
