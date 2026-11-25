#!/usr/bin/env bash
# c9b-adjoint: #print axioms on the headline theorems (run after build.sh).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/axioms.sh
cd ~/formal-c9y
source ~/.elan/env
cat > /tmp/AxiomsC9b.lean <<'LEAN'
import ProofPhase.Adjoint2.Transfer
open ProofPhase.Adjoint2
#print axioms tiltZ_pos
#print axioms tiltAvg_sub_const
#print axioms abs_tiltAvg_add_sub_le_of_abs
#print axioms abs_tiltAvg_add_sub_le
#print axioms exp_add_sub_one
#print axioms abs_tiltAvg_transfer
#print axioms split_tilt
#print axioms sum_exp_sub_one_le
#print axioms column_lt_one_of_mix
#print axioms residual_budget
#print axioms log_three_gt
#print axioms delta0_add_delta1
#print axioms delta0_centre_flip
#print axioms delta0_centre_blind
#print axioms delta0_eq_zero_of_odd
#print axioms delta1_eq_zero_of_even
#print axioms integral_bind_eq
#print axioms abs_integral_bind_sub_le
LEAN
lake env lean /tmp/AxiomsC9b.lean 2>&1 | tee /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c9b-adjoint/axioms.log
grep -rn "sorry\|native_decide\|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/Adjoint2/ && echo "FOUND forbidden token" || echo "no sorry / native_decide / axiom in Adjoint2"
