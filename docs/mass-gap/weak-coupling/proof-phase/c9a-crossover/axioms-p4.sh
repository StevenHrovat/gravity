#!/usr/bin/env bash
# Print the axioms of the declarations of ProofPhase.Crossover.P4Chain (build first with build-p4.sh).
set -euo pipefail
cd ~/formal-p4
source ~/.elan/env
f=$(mktemp /tmp/p4_axioms_XXXX.lean)
{
  echo "import ProofPhase.Crossover.P4Chain"
  for n in p4Star_mono p4StarInv_mono m1HandOver_mono randBlockedLaw_prob integral_randBlockedLaw oneBoxLaw_of_p4Star \
    randBlockGapBddW_of_lawGapBddW randBlockGapBddW_of_p4Star yang_mills_assembly_p4Star lawGapBddWInv_of_oneBoxLawInv \
    oneBoxLawInv_of_p4StarInv randBlockGapBddWInv_of_lawGapBddWInv randObsTransferPhysTW_of_inv \
    randTorusDecayLoc_of_blockGapBddWInv randBlockGapBddWInv_of_p4StarInv yang_mills_assembly_p4StarInv \
    isInfluenceBound_iff_on_true influence_net_or_tail oneBoxSum_mono p4StarInv_of_net lawGapBddW_of_stageTwo \
    randBlockGapBddW_of_stageTwo yang_mills_assembly_stageTwo; do
    echo "#print axioms ProofPhase.Crossover.$n"
  done
} > "$f"
lake env lean "$f"
rm -f "$f"
