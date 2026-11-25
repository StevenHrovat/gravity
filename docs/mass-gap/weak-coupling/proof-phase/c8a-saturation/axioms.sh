#!/usr/bin/env bash
# c8a-saturation: #print axioms on the headline theorems (run after build.sh ProofPhase.Saturation.Reduction).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8a-saturation/axioms.sh
cd ~/formal-c9a
source ~/.elan/env
cat > /tmp/AxiomsC8a.lean <<'LEAN'
import ProofPhase.Saturation.Reduction
open ProofPhase.Saturation
#print axioms tcount_move
#print axioms tcount_cancel
#print axioms length_ge_of_cross
#print axioms sum_surv_sheet_le
#print axioms twHol_move
#print axioms twHol_cancel
#print axioms termI_tw_eq
#print axioms vortex_saturation
#print axioms flip_saturation
#print axioms energy_entropy
#print axioms peierls_of_chessboard
#print axioms satQ_lt_one_iff
#print axioms tanh_half_le_satP
#print axioms satB_eq
#print axioms wilson_vortex_saturation
#print axioms wilson_window
#print axioms not_window_weak
#print axioms z2_vortex_saturation
#print axioms su2_vortex_saturation
#print axioms u1_vortex_saturation
#print axioms z2_background_saturation
#print axioms ztw_trivial
#print axioms flipP_trivial
#print axioms real_no_central_involution
#print axioms mixture_saturation
#print axioms flipP_product
#print axioms isInfluenceBoundOn_split
#print axioms oneBoxSum_add
#print axioms sum_le_of_oneBoxSum
#print axioms tie_forces_budget
#print axioms fineOneBox_of_split
#print axioms yang_mills_assembly_split
LEAN
lake env lean /tmp/AxiomsC8a.lean 2>&1 | tee /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8a-saturation/axioms.log
grep -rn "sorry\|native_decide\|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/Saturation/ && echo "FOUND forbidden token" || echo "no sorry / native_decide / axiom in Saturation"
