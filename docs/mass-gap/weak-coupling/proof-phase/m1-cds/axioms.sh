#!/usr/bin/env bash
# Build ProofPhase.OneBox.CouplingDS in ~/formal-cds, grep for sorry/native_decide/axiom, print the axioms of every theorem.
#   wsl -d ym-replay -u ym -- bash -l /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/m1-cds/axioms.sh
# Needs ~/formal-cds with a Mathlib .lake (mkdir -p ~/formal-cds && cp -a ~/formal/.lake ~/formal-cds/).
set -euo pipefail
src=/mnt/c/claude/gravity-ym/docs/mass-gap/formal
cd $src
FORMAL_DST=~/formal-cds bash sync-build.sh ProofPhase.OneBox.CouplingDS | tail -1
cd ~/formal-cds
echo "--- grep (sorry / native_decide / axiom declarations):"
grep -nE "\bsorry\b|native_decide|^axiom|^\s*axiom " ProofPhase/OneBox/CouplingDS.lean || echo "none"
cat > ~/formal-cds/cds_axioms.lean <<'LEAN'
import ProofPhase.OneBox.CouplingDS
open ProofPhase.OneBox ProofPhase.OneBox.CouplingSpec
#print axioms measurableSet_disagree
#print axioms IsSuppCoupling.isProbabilityMeasure
#print axioms IsSuppCoupling.ae_mem
#print axioms Q_fst'
#print axioms Q_snd'
#print axioms bind_map_fst
#print axioms bind_map_snd
#print axioms Q_compl_supp
#print axioms bind_supp
#print axioms isSuppCoupling_bind
#print axioms T_apply
#print axioms card_inv_mul_card
#print axioms isSuppCoupling_T
#print axioms isSuppCoupling_prod
#print axioms bind_real
#print axioms integrable_Q_real
#print axioms T_real
#print axioms bind_real_disagree_le_of_notMem
#print axioms good_block_le
#print axioms block_le_weight
#print axioms sum_blocks
#print axioms sum_good_compl
#print axioms phi_nonneg
#print axioms phi_T_le
#print axioms iter_succ
#print axioms isSuppCoupling_iter
#print axioms DSWeights.srcWeight_nonneg
#print axioms DSWeights.bound_nonneg
#print axioms DSWeights.θ_lt_one
#print axioms DSWeights.θ_nonneg
#print axioms DSWeights.fixed_point
#print axioms phi_iter_le
#print axioms eventually_phi_iter_le
#print axioms exists_iter_forall_le
#print axioms couplingDS_bound
#print axioms abs_integral_sub_le_phi
#print axioms couplingDS_integral_bound
LEAN
source ~/.elan/env
lake env lean ~/formal-cds/cds_axioms.lean
rm -f ~/formal-cds/cds_axioms.lean