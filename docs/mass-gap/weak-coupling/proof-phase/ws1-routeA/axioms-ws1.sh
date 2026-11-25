#!/usr/bin/env bash
# Workstream 1 (Route A): #print axioms on the headline theorems (run after build-ws1.sh for all three modules).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws1-routeA/axioms-ws1.sh
cd ~/formal-ws1
source ~/.elan/env
cat > /tmp/AxiomsWs1.lean <<'LEAN'
import ProofPhase.RouteA.Blocking
import ProofPhase.RouteA.BlockedSlab
import ProofPhase.RouteA.CentreBlind
#print axioms ProofPhase.RouteA.walk_thetaConn
#print axioms ProofPhase.RouteA.walk_rev
#print axioms ProofPhase.RouteA.projSU2_star
#print axioms ProofPhase.RouteA.smearBlock_zero
#print axioms ProofPhase.RouteA.smearBlock_thetaConn
#print axioms ProofPhase.RouteA.linkDep_smearBlock
#print axioms ProofPhase.RouteA.smearRP
#print axioms ProofPhase.RouteA.smearIter
#print axioms ProofPhase.RouteA.goodBlocking
#print axioms ProofPhase.RouteA.goodBlocking_rp
#print axioms ProofPhase.RouteA.cov_transfer
#print axioms ProofPhase.RouteA.gaugeInvariant_tShift
#print axioms ProofPhase.RouteA.gaugeInvariant_thetaConn
#print axioms ProofPhase.RouteA.wcorr_le_blocked
#print axioms ProofPhase.RouteA.slabDecay_of_blockedRoute
#print axioms ProofPhase.RouteA.massGap_of_blockedRoute
#print axioms ProofPhase.RouteA.massGap_of_goodBlocking
#print axioms ProofPhase.RouteA.torusDecay_of_blockedRouteU
#print axioms ProofPhase.RouteA.bothOrders_of_blockedRouteU
#print axioms ProofPhase.RouteA.xp_not_adjointOnly
#print axioms ProofPhase.RouteA.cov_adjointOnly_comm
LEAN
lake env lean /tmp/AxiomsWs1.lean 2>&1
echo "--- sorry / native_decide / axiom declarations in RouteA:"
grep -nE "sorry|native_decide|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/RouteA/*.lean || echo none
