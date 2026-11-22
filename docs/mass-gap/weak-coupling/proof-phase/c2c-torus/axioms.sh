#!/usr/bin/env bash
# Cycle 2, workstream C: #print axioms on the headline theorems (run after build.sh ProofPhase.Torus.Top).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2c-torus/axioms.sh
cd ~/formal-c2c
source ~/.elan/env
cat > /tmp/AxiomsC2c.lean <<'LEAN'
import ProofPhase.Torus.Top
import ProofPhase.Quantum.BlockedRoute
open ProofPhase
#print axioms ProofPhase.yang_mills_assembly
#print axioms ProofPhase.yang_mills_assembly_torus
#print axioms ProofPhase.yang_mills_assembly_slab
#print axioms ProofPhase.not_trivial_top
#print axioms ProofPhase.not_trivial
#print axioms ProofPhase.not_onLCP_of_bounded
#print axioms ProofPhase.assembly_routeA
#print axioms ProofPhase.assembly_routeB
#print axioms ProofPhase.fluxGrowth_of_conjW
#print axioms ProofPhase.OnLCP.eventually_actRate
#print axioms ProofPhase.exists_fluxLimitSU2
#print axioms ProofPhase.massGapLoc_of_massGap
#print axioms ProofPhase.Torus.torusDecayLoc_of_blockedRoute
#print axioms ProofPhase.Torus.bothOrdersLoc_of_torusDecayLoc
#print axioms ProofPhase.Torus.bothOrdersLoc_of_blockedRoute
#print axioms ProofPhase.Torus.gapVF_of_family
#print axioms ProofPhase.Torus.gapMF_of_family
#print axioms ProofPhase.Torus.torusDecayLoc_of_torusDecay
#print axioms ProofPhase.Torus.massGapMFLoc_of_massGapMF
#print axioms ProofPhase.Torus.obsTransferPhys_of_U
#print axioms ProofPhase.Torus.obsTransferPhys_of_cell
#print axioms ProofPhase.Torus.card_le_of_siteDist
#print axioms ProofPhase.Torus.linkDist_shiftLink
#print axioms ProofPhase.Torus.linkDist_mirrorLink_le
#print axioms ProofPhase.RouteA.slabDecay_of_blockedRoute
#print axioms ProofPhase.Quantum.slabDecay_of_blockedRoute
#print axioms ProofPhase.Quantum.openPieces_of_blockedRoute
LEAN
lake env lean /tmp/AxiomsC2c.lean 2>&1
echo "--- sorry / native_decide / axiom declarations in the touched files:"
grep -nE "sorry|native_decide|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/{Objects,Assembly}.lean /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/Torus/*.lean /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/Quantum/BlockedRoute.lean || echo none
