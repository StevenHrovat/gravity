#!/usr/bin/env bash
# Proof phase, assembly: #print axioms on the headline theorems (run after build-asm.sh).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/axioms-asm.sh
cd ~/formal-phase-asm
source ~/.elan/env
cat > /tmp/AxiomsAsm.lean <<'LEAN'
import ProofPhase.Assembly
open ProofPhase
#print axioms ProofPhase.yang_mills_assembly
#print axioms ProofPhase.assembly_routeA
#print axioms ProofPhase.assembly_routeB
#print axioms ProofPhase.latticeGap_of_slabDecay
#print axioms ProofPhase.massGap_of_latticeGap
#print axioms ProofPhase.slabDecay_of_uniformGDS
#print axioms ProofPhase.fluxGrowth_of_conjW
#print axioms ProofPhase.blockGap_of_blockedRoute
#print axioms ProofPhase.not_trivial
#print axioms ProofPhase.not_onLCP_of_bounded
#print axioms ProofPhase.bareRunning_witness
#print axioms ProofPhase.limitRP
#print axioms ProofPhase.spectral_gap_of_decay
#print axioms ProofPhase.blocked_wilson_rp
#print axioms ProofPhase.corr_le_of_decay
LEAN
lake env lean /tmp/AxiomsAsm.lean 2>&1
echo "--- sorry / native_decide / axiom declarations in ProofPhase:"
grep -nE "sorry|native_decide|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/*.lean || echo none
