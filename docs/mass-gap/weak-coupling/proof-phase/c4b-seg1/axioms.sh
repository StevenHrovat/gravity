#!/usr/bin/env bash
# c4b-seg1: #print axioms on the headline theorems (run after build.sh ProofPhase.Seg1.Envelope).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4b-seg1/axioms.sh
cd ~/formal-c4b
source ~/.elan/env
mods="${1:-ProofPhase.Seg1.Envelope}"
EXTRA="${EXTRA:-envelopeW_of_kp linkDiam_glue weight_envWeight pairSum_sets_eq envelopeW_of_polymerRep envelopeW_seg1}"
{
  for m in $mods; do echo "import $m"; done
  for t in mob_eq_of sum_mob mob_mul mob_shift wnorm_conv_le MajBy.tsum gasZ_insert gasZ_congr log_gasZ_eq_sum \
           clusterPot_congr inv_of_good log_of_good P_bound good_of_sub kotecky_preiss $EXTRA; do
    echo "#print axioms ProofPhase.Seg1.$t"
  done
} > /tmp/AxiomsC4b.lean
lake env lean /tmp/AxiomsC4b.lean
grep -n "sorry\|native_decide\|^axiom" ProofPhase/Seg1/*.lean || echo "no sorry / native_decide / axiom in ProofPhase/Seg1"
