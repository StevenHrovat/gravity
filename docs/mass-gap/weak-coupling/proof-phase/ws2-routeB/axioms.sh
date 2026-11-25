#!/usr/bin/env bash
# Workstream 2: build all RouteB modules in ~/formal-ws2 and print the axioms of the headline theorems.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws2-routeB/axioms.sh
set -euo pipefail
src=/mnt/c/claude/gravity-ym/docs/mass-gap/formal
if grep -n "sorry\|native_decide\|^axiom " $src/ProofPhase/RouteB/*.lean; then echo "FORBIDDEN TOKEN FOUND"; exit 1; fi
cd $src
for m in HankelRate Chain FluxEnergy Duality Sector; do
  FORMAL_DST=~/formal-ws2 bash sync-build.sh ProofPhase.RouteB.$m 2>&1 | grep -E "error|Build completed" | tail -n 3
done
cd ~/formal-ws2
source ~/.elan/env
cat > /tmp/ws2_axioms.lean <<'EOF'
import ProofPhase.RouteB.FluxEnergy
import ProofPhase.RouteB.Duality
import ProofPhase.RouteB.Sector
open ProofPhase.RouteB
#print axioms RPSeq.abs_le_rate
#print axioms RPSeq.rate_sharp
#print axioms RPSeq.tendsto_effMass
#print axioms rpSeq_of_limit
#print axioms exists_limit
#print axioms cweight_factor
#print axioms chain_rp
#print axioms cform_slice
#print axioms ccorr_cs
#print axioms rpSeq_of_isTimeLimit
#print axioms exists_isTimeLimit
#print axioms fluxEnergy_props
#print axioms su2_fluxEnergy_props
#print axioms polySum_flip
#print axioms polySum_mean_zero
#print axioms su2_polySum_mean_zero
#print axioms twistZ_perm
#print axioms tHooft_rotation
#print axioms electric_eq_magnetic
#print axioms sectorTransfer_of_slabDecay
#print axioms sectorTransfer_of_torusDecay
EOF
lake env lean /tmp/ws2_axioms.lean
