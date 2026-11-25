#!/usr/bin/env bash
# Cycle 2, workstream A: #print axioms on the headline theorems (run after build-c2a.sh for both modules).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2a-adjoint/axioms-c2a.sh
cd ~/formal-c2a
source ~/.elan/env
cat > /tmp/AxiomsC2a.lean <<'LEAN'
import ProofPhase.Adjoint.CentreSplit
import ProofPhase.Adjoint.TwoType
#print axioms ProofPhase.Adjoint.centreFlip_centreFlip
#print axioms ProofPhase.Adjoint.centreAvg_flip
#print axioms ProofPhase.Adjoint.centreAvg_of_blind
#print axioms ProofPhase.Adjoint.centreAvg_eq_zero_of_odd
#print axioms ProofPhase.Adjoint.centreAvg_centrePart
#print axioms ProofPhase.Adjoint.pairOsc_add
#print axioms ProofPhase.Adjoint.flatW_add
#print axioms ProofPhase.Adjoint.limitDprime_of_halves
#print axioms ProofPhase.Adjoint.slabDecay_of_halves
#print axioms ProofPhase.Adjoint.massGap_of_goodBlocking_halves
#print axioms ProofPhase.Adjoint.blockedTorusRoute_of_halves
#print axioms ProofPhase.Adjoint.blockedSlabRoute_of_halves
#print axioms ProofPhase.Adjoint.pairDiff_of_pairOsc
#print axioms ProofPhase.Adjoint.influence_site_sharp
#print axioms ProofPhase.Adjoint.decay_of_sharpW
#print axioms ProofPhase.Adjoint.map_split
#print axioms ProofPhase.Adjoint.integral_gibbs_split
#print axioms ProofPhase.Adjoint.schur_weights
#print axioms ProofPhase.Adjoint.twoType_criterion
#print axioms ProofPhase.Adjoint.decay_twoType
#print axioms ProofPhase.Adjoint.decay_twoType_blocks
LEAN
lake env lean /tmp/AxiomsC2a.lean 2>&1
echo "--- sorry / native_decide / axiom declarations in Adjoint:"
grep -nE "sorry|native_decide|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/Adjoint/*.lean || echo none
