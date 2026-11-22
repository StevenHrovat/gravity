#!/usr/bin/env bash
# Cycle 4, workstream 3 (c4c-seg2): #print axioms on the headline theorems (run after build.sh ProofPhase.Seg2.Filter).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4c-seg2/axioms.sh
cd ~/formal-c4c
source ~/.elan/env
cat > /tmp/AxiomsC4c.lean <<'LEAN'
import ProofPhase.Seg2.Filter
#print axioms ProofPhase.Seg2.condDefect_comm
#print axioms ProofPhase.Seg2.abs_condDefect_le_dev
#print axioms ProofPhase.Seg2.condDefect_eq_of_condUncorr
#print axioms ProofPhase.Seg2.abs_condDefect_le_smoother
#print axioms ProofPhase.Seg2.abs_condDefect_le_smoother'
#print axioms ProofPhase.Seg2.approx_of_smoother
#print axioms ProofPhase.Seg2.smoother_chain_of_steps
#print axioms ProofPhase.Seg2.smoother_chain
#print axioms ProofPhase.Seg2.abs_condDefect_le_chain
#print axioms ProofPhase.Seg2.abs_condDefect_le_chain_const
#print axioms ProofPhase.Seg2.condClause_eq
#print axioms ProofPhase.Seg2.condDecouple_of_smootherStable
#print axioms ProofPhase.Seg2.smootherStable_of_annealedContraction
#print axioms ProofPhase.Seg2.condDecouple_of_annealedContraction
set_option pp.explicit false in
#print ProofPhase.Seg2.SmootherStable
LEAN
lake env lean /tmp/AxiomsC4c.lean 2>&1
echo "--- sorry / native_decide / axiom declarations in ProofPhase/Seg2:"
grep -nE "sorry|native_decide|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/Seg2/*.lean || echo none
