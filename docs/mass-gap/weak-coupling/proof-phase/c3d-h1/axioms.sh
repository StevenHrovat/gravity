#!/usr/bin/env bash
# c3d-h1: #print axioms on the headline theorems (run after build.sh ProofPhase.H1.Level).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3d-h1/axioms.sh
cd ~/formal-c3d
source ~/.elan/env
cat > /tmp/AxiomsC3d.lean <<'LEAN'
import ProofPhase.H1.Split
import ProofPhase.H1.Level
#print axioms ProofPhase.H1.exists_seq_of_unif
#print axioms ProofPhase.H1.localConvergenceW_iff
#print axioms ProofPhase.H1.tailSmall_of_envelope
#print axioms ProofPhase.H1.pairSumBdd_of_envelope
#print axioms ProofPhase.H1.nearUniform_of_stable
#print axioms ProofPhase.H1.flatW_far_le
#print axioms ProofPhase.H1.h1Local_iff_split
#print axioms ProofPhase.H1.h1Local_of_quasiLocal
#print axioms ProofPhase.H1.levelDprime_of_h1Local
#print axioms ProofPhase.H1.blockGapUnif_of_levelDprime
#print axioms ProofPhase.H1.blockGapUnif_of_blockedRoute
#print axioms ProofPhase.H1.torusDecayLoc_of_blockGapUnif
#print axioms ProofPhase.H1.levelTorusRoute_of_blockedTorusRoute
#print axioms ProofPhase.H1.bothOrdersLoc_of_levelRoute
#print axioms ProofPhase.H1.yang_mills_assembly_level
LEAN
lake env lean /tmp/AxiomsC3d.lean
grep -n "sorry\|native_decide\|^axiom" ProofPhase/H1/*.lean || echo "no sorry / native_decide / axiom in ProofPhase/H1"
