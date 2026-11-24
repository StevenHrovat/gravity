#!/usr/bin/env bash
# Cycle 3, workstream 1 (c3a-uv): #print axioms on the headline theorems (run after build.sh ProofPhase.UV.Split).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c3a-uv/axioms.sh
cd ~/formal-c3a
source ~/.elan/env
cat > /tmp/AxiomsC3a.lean <<'LEAN'
import ProofPhase.UV.Split
#print axioms ProofPhase.UV.condDefect_eq
#print axioms ProofPhase.UV.abs_condDefect_le
#print axioms ProofPhase.UV.abs_cov_condExp_le
#print axioms ProofPhase.UV.abs_condDefect_sub_cov_le
#print axioms ProofPhase.UV.abs_condDefect_sub_cov_sub_le
#print axioms ProofPhase.UV.condDefect_eq_cov_of_indep
#print axioms ProofPhase.UV.condDefect_tower
#print axioms ProofPhase.UV.integral_abs_condExp_sub_le
#print axioms ProofPhase.UV.abs_condDefect_sub_le
#print axioms ProofPhase.UV.approx_tower
#print axioms ProofPhase.UV.twoStage
#print axioms ProofPhase.UV.condExp_comp_map
#print axioms ProofPhase.UV.condDefect_map
#print axioms ProofPhase.UV.approx_map
#print axioms ProofPhase.UV.twoStage_blocked
LEAN
lake env lean /tmp/AxiomsC3a.lean 2>&1
echo "--- sorry / native_decide / axiom declarations in ProofPhase/UV:"
grep -nE "sorry|native_decide|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/UV/*.lean || echo none
