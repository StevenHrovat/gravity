#!/usr/bin/env bash
# c4a-condmass: #print axioms on the headline theorems (run after build.sh ProofPhase.V3.Top).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4a-condmass/axioms.sh
cd ~/formal-c4a
source ~/.elan/env
cat > /tmp/AxiomsC4a.lean <<'LEAN'
import ProofPhase.V3.Top
#print axioms ProofPhase.V3.sep_shift_mirror_time
#print axioms ProofPhase.V3.obsTransferPhysT_of_phys
#print axioms ProofPhase.V3.torusDecayLoc_of_blockGapUnifT
#print axioms ProofPhase.V3.levelTorusRouteT_of_level
#print axioms ProofPhase.V3.bothOrdersLoc_of_levelRouteT
#print axioms ProofPhase.V3.condDefect_eq_integral_condCov
#print axioms ProofPhase.V3.abs_condDefect_le_of_ae
#print axioms ProofPhase.V3.abs_cov_le_of_cellDobrushin
#print axioms ProofPhase.V3.condMassDecay_of_condMass
#print axioms ProofPhase.V3.obsQuasiLocT_of_obsTransferPhysT
#print axioms ProofPhase.V3.obsTransferPhysT_of_condMassDecay
#print axioms ProofPhase.V3.obsTransferPhysT_of_condMass
#print axioms ProofPhase.V3.blockGapUnifW_of_levelDprimeW
#print axioms ProofPhase.V3.levelDprimeW_of_h1LocalLip
#print axioms ProofPhase.V3.levelDprimeW_of_certified
#print axioms ProofPhase.V3.obsTransferPhysTW_of_condMass
#print axioms ProofPhase.V3.wcorr_le_blockedW
#print axioms ProofPhase.V3.torusDecayLoc_of_blockGapUnifW
#print axioms ProofPhase.V3.bothOrdersLoc_of_levelRouteW
#print axioms ProofPhase.V3.condMassAnn_of_condMassDecay
#print axioms ProofPhase.V3.condDecouple_of_condMassAnn
#print axioms ProofPhase.V3.condDecouple_of_condMass
#print axioms ProofPhase.V3.obsTransferPhysT_of_condDecouple
#print axioms ProofPhase.V3.obsTransferPhysTW_of_condDecouple
#print axioms ProofPhase.V3.condDecouple_of_obsTransferPhysT
#print axioms ProofPhase.V3.yang_mills_assembly_v3_W1_dec
#print axioms ProofPhase.V3.yang_mills_assembly_v3_W1_condMass
#print axioms ProofPhase.V3.yang_mills_assembly_v3_W1_smoother
#print axioms ProofPhase.V3.yang_mills_assembly_v3
#print axioms ProofPhase.V3.yang_mills_assembly_v3_W1
#print axioms ProofPhase.V3.yang_mills_assembly_v3_certified
#print axioms ProofPhase.V3.yang_mills_assembly_v3_sup
#print axioms ProofPhase.V3.openInputsV3_of_level
#print axioms ProofPhase.V3.openInputsV3_of_blockedTorusRoute
#print axioms ProofPhase.V3.not_trivial_v3
LEAN
lake env lean /tmp/AxiomsC4a.lean
grep -n "sorry\|native_decide\|^axiom" ProofPhase/V3/*.lean || echo "no sorry / native_decide / axiom in ProofPhase/V3"
