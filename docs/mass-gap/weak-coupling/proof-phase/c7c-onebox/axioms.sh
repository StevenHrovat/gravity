#!/usr/bin/env bash
# c7c-onebox: #print axioms on the headline theorems (run after build.sh ProofPhase.OneBox.Tests).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c7c-onebox/axioms.sh
cd ~/formal-c8a
source ~/.elan/env
cat > /tmp/AxiomsC7c.lean <<'LEAN'
import ProofPhase.OneBox.Tests
#print axioms ProofPhase.OneBox.theoremA_on
#print axioms ProofPhase.OneBox.admData_of_covariant
#print axioms ProofPhase.OneBox.gdsw_of_oneBox
#print axioms ProofPhase.OneBox.abs_cov_le_of_oneBox
#print axioms ProofPhase.OneBox.oneBoxSum_of_finiteRange
#print axioms ProofPhase.OneBox.lawGapBddW_of_oneBoxLaw
#print axioms ProofPhase.OneBox.blockGapBddW_of_oneBoxLaw
#print axioms ProofPhase.OneBox.yang_mills_assembly_v4_onebox
#print axioms ProofPhase.OneBox.fineDecayInv_of_fineOneBox
#print axioms ProofPhase.OneBox.torusDecayLoc_of_fineDecayInv
#print axioms ProofPhase.OneBox.yang_mills_assembly_onebox
#print axioms ProofPhase.OneBox.influence_telescope
#print axioms ProofPhase.OneBox.not_lawGapBddW_of_power
#print axioms ProofPhase.OneBox.not_oneBoxLaw_of_power
#print axioms ProofPhase.OneBox.not_fineOneBox_of_not_torusDecayLoc
LEAN
lake env lean /tmp/AxiomsC7c.lean 2>&1 | tee /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c7c-onebox/axioms.log
grep -rn "sorry\|native_decide\|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/OneBox/ && echo "FOUND forbidden token" || echo "no sorry / native_decide / axiom in OneBox"
