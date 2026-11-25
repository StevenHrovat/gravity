#!/usr/bin/env bash
# c9b round 2: #print axioms on the headline declarations of Adjoint2/CostCoupling and Adjoint2/PatternAssembly
# (run after build-ir.sh ProofPhase.Adjoint2.PatternAssembly).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/axioms-ir.sh
cd ~/formal-ir
source ~/.elan/env
cat > /tmp/AxiomsIr.lean <<'LEAN'
import ProofPhase.Adjoint2.PatternAssembly
open ProofPhase.Adjoint2
#print axioms measurable_cst
#print axioms ecost_hamming
#print axioms ecost_bind_of_notMem
#print axioms block_cost_le
#print axioms cost_bind_le
#print axioms costPhi_T_le
#print axioms CostWeights.costPhi_iter_le
#print axioms costDS_bound
#print axioms abs_sub_le_card_disagree
#print axioms abs_integral_sub_le_osc
#print axioms abs_integral_sub_le_costSmooth
#print axioms isInfluenceBoundOn_of_costSmooth
#print axioms influence_source_block
#print axioms abs_covar_le_two
#print axioms cov_mixture
#print axioms abs_covar_mixture_le
#print axioms abs_covar_le_of_disintBound
#print axioms pair_bound_of_couplingDS
#print axioms fineDecayInv_of_fineOneBoxPat
#print axioms yang_mills_assembly_pat
LEAN
lake env lean /tmp/AxiomsIr.lean 2>&1 | tee /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/axioms-ir.log
grep -rn "sorry\|native_decide\|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/Adjoint2/ && echo "FOUND forbidden token" | tee -a /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/axioms-ir.log || echo "no sorry / native_decide / axiom in Adjoint2" | tee -a /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/axioms-ir.log
