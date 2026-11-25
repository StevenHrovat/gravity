#!/usr/bin/env bash
# ws3-quantum: #print axioms on the headline theorems (run after build.sh of all four modules).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws3-quantum/axioms.sh
cd ~/formal-ws3
source ~/.elan/env
cat > /tmp/AxiomsWs3.lean <<'LEAN'
import ProofPhase.Quantum.LemmaT
import ProofPhase.Quantum.PerVolume
import ProofPhase.Quantum.LimitStates
import ProofPhase.Quantum.BlockedRoute
open ProofPhase.Quantum
#print axioms ProofPhase.Quantum.RelClose.map
#print axioms ProofPhase.Quantum.RelClose.bind
#print axioms ProofPhase.Quantum.relClose_withDensity_log
#print axioms ProofPhase.Quantum.relClose_normalize
#print axioms ProofPhase.Quantum.abs_integral_sub_le_of_relClose
#print axioms ProofPhase.Quantum.abs_integral_sub_le_osc
#print axioms ProofPhase.Quantum.relClose_locSpec
#print axioms ProofPhase.Quantum.tvClose_locSpec
#print axioms ProofPhase.Quantum.relClose_wilsonMeasure
#print axioms ProofPhase.Quantum.relClose_wilson_blocked
#print axioms ProofPhase.Quantum.relClose_wilson_gaugeSpec
#print axioms ProofPhase.Quantum.isProbabilityMeasure_noisyLaw
#print axioms ProofPhase.Quantum.tendsto_integral_blocked
#print axioms ProofPhase.Quantum.NoisyBlocking.perVolumeGap
#print axioms ProofPhase.Quantum.NoisyBlocking.perVolumeGap_eventually
#print axioms ProofPhase.Quantum.NoisyBlocking.exists_blockLimit
#print axioms ProofPhase.Quantum.NoisyBlocking.blockLimit_gap
#print axioms ProofPhase.Quantum.exists_infVol_limitPoint
#print axioms ProofPhase.Quantum.massGap_nonvacuous
#print axioms ProofPhase.Quantum.exists_limitState
#print axioms ProofPhase.Quantum.tendsto_integral_limitState
#print axioms ProofPhase.Quantum.slabDecay_of_blockedRoute
#print axioms ProofPhase.Quantum.openPieces_of_blockedRoute
#print axioms ProofPhase.Quantum.assembly_blockedRoute
#print axioms ProofPhase.Quantum.abs_cov_sub_le_condExp
#print axioms ProofPhase.Quantum.gaugeInvariant_comp_thetaConn
#print axioms ProofPhase.Quantum.linkMetric_triangle
#print axioms ProofPhase.Quantum.blockGap_linkMetric
#print axioms ProofPhase.Quantum.linkDist_not_definite
LEAN
lake env lean /tmp/AxiomsWs3.lean 2>&1
echo "--- sorry / native_decide / axiom declarations in ProofPhase/Quantum:"
grep -nE "sorry|native_decide|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/Quantum/*.lean || echo none
