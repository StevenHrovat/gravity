#!/usr/bin/env bash
# c8d-strict: #print axioms on every theorem of ProofPhase/Flip/Strict.lean (run after build.sh), plus a grep for
# forbidden tokens. Output: axioms.log next to this script.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8d-strict/axioms.sh
cd ~/formal-c8d
source ~/.elan/env
out=/mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8d-strict/axioms.log
cat > /tmp/AxiomsC8d.lean <<'LEAN'
import ProofPhase.Flip.Strict
#print axioms ProofPhase.Flip.measurePreserving_mix
#print axioms ProofPhase.Flip.integral_mix
#print axioms ProofPhase.Flip.measurePreserving_restrictInj
#print axioms ProofPhase.Flip.val_halfT
#print axioms ProofPhase.Flip.neg_halfT
#print axioms ProofPhase.Flip.halfT_ne_zero
#print axioms ProofPhase.Flip.bdry_ctheta
#print axioms ProofPhase.Flip.bdry_depPos
#print axioms ProofPhase.Flip.measurable_bdry
#print axioms ProofPhase.Flip.bdry_flip0
#print axioms ProofPhase.Flip.measurePreserving_ctwist
#print axioms ProofPhase.Flip.cZtw_lt_cZ_of_moment
#print axioms ProofPhase.Flip.measurable_kop
#print axioms ProofPhase.Flip.isBdd_kop
#print axioms ProofPhase.Flip.bm_kop
#print axioms ProofPhase.Flip.bm_kop_iter
#print axioms ProofPhase.Flip.measurePreserving_kswap
#print axioms ProofPhase.Flip.vip_kop
#print axioms ProofPhase.Flip.vip_kop_iter
#print axioms ProofPhase.Flip.vip_eq_zero_of_self
#print axioms ProofPhase.Flip.stepVanish_descend
#print axioms ProofPhase.Flip.stepVanish_one
#print axioms ProofPhase.Flip.measurePreserving_sp
#print axioms ProofPhase.Flip.measurePreserving_tmsp
#print axioms ProofPhase.Flip.sp_stepMix_ne
#print axioms ProofPhase.Flip.sp_stepMix_eq
#print axioms ProofPhase.Flip.tm_stepMix_ne
#print axioms ProofPhase.Flip.tm_stepMix_eq
#print axioms ProofPhase.Flip.integral_step
#print axioms ProofPhase.Flip.natCast_ne
#print axioms ProofPhase.Flip.bm_cAm
#print axioms ProofPhase.Flip.cAm_stepMix
#print axioms ProofPhase.Flip.chain_aux
#print axioms ProofPhase.Flip.tLow_eq
#print axioms ProofPhase.Flip.tPos_eq
#print axioms ProofPhase.Flip.tFix_eq
#print axioms ProofPhase.Flip.cA_eq_cAm
#print axioms ProofPhase.Flip.cB_eq
#print axioms ProofPhase.Flip.half_chain
#print axioms ProofPhase.Flip.moment_odd
#print axioms ProofPhase.Flip.cZtw_lt_cZ_of_step
#print axioms ProofPhase.Flip.isBdd_of_continuous
#print axioms ProofPhase.Flip.integrable_of_continuous
#print axioms ProofPhase.Flip.integral_pos_of_continuous
#print axioms ProofPhase.Flip.integral_update
#print axioms ProofPhase.Flip.continuous_tr2
#print axioms ProofPhase.Flip.tr2_one
#print axioms ProofPhase.Flip.continuous_bw
#print axioms ProofPhase.Flip.bw_pos
#print axioms ProofPhase.Flip.bw_conj
#print axioms ProofPhase.Flip.continuous_entry
#print axioms ProofPhase.Flip.continuous_bwEntry
#print axioms ProofPhase.Flip.schurN_conj
#print axioms ProofPhase.Flip.suD_conj_01
#print axioms ProofPhase.Flip.suD_conj_10
#print axioms ProofPhase.Flip.suJ_conj_00
#print axioms ProofPhase.Flip.schurN_01
#print axioms ProofPhase.Flip.schurN_10
#print axioms ProofPhase.Flip.schurN_11
#print axioms ProofPhase.Flip.su2_entry11
#print axioms ProofPhase.Flip.su2_trace_im
#print axioms ProofPhase.Flip.integral_bw_tr_mul
#print axioms ProofPhase.Flip.schur_SU2
#print axioms ProofPhase.Flip.integral_tr2_eq_zero
#print axioms ProofPhase.Flip.exp_lt_one_of_neg'
#print axioms ProofPhase.Flip.expsub_mul_nonneg
#print axioms ProofPhase.Flip.expsub_mul_pos
#print axioms ProofPhase.Flip.schurC_ne_zero
#print axioms ProofPhase.Flip.lineInt
#print axioms ProofPhase.Flip.polyLine_eq
#print axioms ProofPhase.Flip.lineLinks_nodup
#print axioms ProofPhase.Flip.line_target
#print axioms ProofPhase.Flip.lineSite_L
#print axioms ProofPhase.Flip.prod_telescope
#print axioms ProofPhase.Flip.continuous_polyObs
#print axioms ProofPhase.Flip.measurePreserving_gaugeSub
#print axioms ProofPhase.Flip.stepK_gaugeSub
#print axioms ProofPhase.Flip.polyObs_gaugeSub
#print axioms ProofPhase.Flip.continuous_stepK
#print axioms ProofPhase.Flip.lineConst_pos
#print axioms ProofPhase.Flip.stepK_polyObs
#print axioms ProofPhase.Flip.sliceV_pos
#print axioms ProofPhase.Flip.continuous_sliceV
#print axioms ProofPhase.Flip.continuous_polyRatio
#print axioms ProofPhase.Flip.bm_polyRatio
#print axioms ProofPhase.Flip.oddUnder_polyRatio
#print axioms ProofPhase.Flip.kop_polyRatio
#print axioms ProofPhase.Flip.su2_vip_polyRatio
#print axioms ProofPhase.Flip.su2_Ztw_lt_Z
#print axioms ProofPhase.Flip.su2_Ze1_pos
#print axioms ProofPhase.Flip.su2_flipProb_lt_half
LEAN
lake env lean /tmp/AxiomsC8d.lean > "$out" 2>&1
echo "--- theorems checked: $(grep -c '^#print' /tmp/AxiomsC8d.lean)" >> "$out"
echo "--- lines mentioning an axiom other than propext / Classical.choice / Quot.sound:" >> "$out"
tr ',' '\n' < "$out" | grep -v "^---" | tr -d '[] ' | grep -v "^$" | grep -v "dependsonaxioms:" | grep -v "^propext$\|^Classical.choice$\|^Quot.sound$" >> "$out" || true
grep -n "sorryAx\|sorry\|native_decide\|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/Flip/Strict.lean >> "$out" && echo "FOUND forbidden token" >> "$out" || echo "no sorry / native_decide / axiom in Strict.lean" >> "$out"
tail -5 "$out"
