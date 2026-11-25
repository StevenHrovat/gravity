#!/usr/bin/env bash
# c8c-concrete: print the axioms of the main theorems (after build.sh of the module that contains them).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c8c-concrete/axioms.sh
cd ~/formal-c9c
source ~/.elan/env
cat > /tmp/c8c-axioms.lean <<'EOL'
import ProofPhase.OneBox2.CubeAnchor
#print axioms ProofPhase.OneBox2.liftBlockSpec
#print axioms ProofPhase.OneBox2.gaugeSpec_covariant
#print axioms ProofPhase.OneBox2.wilsonBlockSpec
#print axioms ProofPhase.OneBox2.wilsonBoxSpec_covariant
#print axioms ProofPhase.OneBox2.fineOneBox_of_wilsonOneBox
#print axioms ProofPhase.OneBox2.yang_mills_assembly_wilsonOneBox
#print axioms ProofPhase.OneBox2.influence_block
#print axioms ProofPhase.OneBox2.wilsonOneBox_strong
#print axioms ProofPhase.OneBox2.wilsonOneBox_strong_const
#print axioms ProofPhase.OneBox2.cubeBlockSpec
#print axioms ProofPhase.OneBox2.cubeLifted
#print axioms ProofPhase.OneBox2.cubeBoxSpec_univ
#print axioms ProofPhase.OneBox2.abs_cov_le_of_oneBox_unres
#print axioms ProofPhase.OneBox2.cubeDecay_of_wallCutOneBox
#print axioms ProofPhase.OneBox2.areaLaw_of_wallCutOneBox
#print axioms ProofPhase.OneBox2.wallCutOneBox_strong
#print axioms ProofPhase.OneBox2.lifted_influence_cut_id
EOL
cat /tmp/c8c-extra-axioms.lean 2>/dev/null | sed 's/^import.*//' >> /tmp/c8c-axioms.lean
lake env lean /tmp/c8c-axioms.lean 2>&1 | grep -v "^$" | head -80
