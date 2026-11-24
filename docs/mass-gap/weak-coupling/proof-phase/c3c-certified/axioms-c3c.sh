#!/usr/bin/env bash
# Cycle 3, workstream 3: #print axioms on the headline theorems (run after build-c3c.sh).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3c-certified/axioms-c3c.sh
cd ~/formal-c3c
source ~/.elan/env
cat > /tmp/AxiomsC3c.lean <<'LEAN'
import ProofPhase.Certified.AdjointW
#print axioms ProofPhase.Certified.decay_of_siteW
#print axioms ProofPhase.Certified.potential_twoCoupling
#print axioms ProofPhase.Certified.abs_twoCoupling_le
#print axioms ProofPhase.Certified.cornerColumn_lt_one
#print axioms ProofPhase.Certified.column_le
#print axioms ProofPhase.Certified.dist_le_of_common
#print axioms ProofPhase.Certified.limitDprimeW_twoCoupling
#print axioms ProofPhase.Certified.twoCoupling_decay
#print axioms ProofPhase.Certified.exists_rate_corner
LEAN
lake env lean /tmp/AxiomsC3c.lean 2>&1
echo "--- sorry / native_decide / axiom declarations in Certified:"
grep -nE "sorry|native_decide|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/Certified/*.lean || echo none
