#!/usr/bin/env bash
# Cycle 4, workstream 4: #print axioms on the headline theorems of Measured.lean (run after build-c4d.sh).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4d-certified/axioms-c4d.sh
cd ~/formal-c4d
source ~/.elan/env
cat > /tmp/AxiomsC4d.lean <<'LEAN'
import ProofPhase.Certified.Measured
#print axioms ProofPhase.Certified.abs_planeFactor_le
#print axioms ProofPhase.Certified.potential_measuredAction
#print axioms ProofPhase.Certified.kMeas_column_lt_one
#print axioms ProofPhase.Certified.measured_column_le
#print axioms ProofPhase.Certified.measured_dist_le
#print axioms ProofPhase.Certified.limitDprimeW_measured
#print axioms ProofPhase.Certified.measured_decay
#print axioms ProofPhase.Certified.exists_rate_measured
LEAN
lake env lean /tmp/AxiomsC4d.lean 2>&1
echo "--- sorry / native_decide / axiom declarations in Certified:"
grep -nE "sorry|native_decide|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/Certified/*.lean || echo none
