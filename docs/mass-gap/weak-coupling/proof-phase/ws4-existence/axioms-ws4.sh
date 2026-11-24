#!/usr/bin/env bash
# ws4: #print axioms on the bridge theorems (run after build-ws4.sh).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws4-existence/axioms-ws4.sh
cd ~/formal-ws4
source ~/.elan/env
cat > /tmp/AxiomsWs4.lean <<'LEAN'
import ProofPhase.Existence.Bridge
open ProofPhase ProofPhase.Existence
#print axioms ProofPhase.Existence.plaqLaw_eq_wilsonMeasure
#print axioms ProofPhase.Existence.wilsonMeasure_SU2_eq_plaqLaw
#print axioms ProofPhase.Existence.WilsonData.side_vol
#print axioms ProofPhase.Existence.WilsonData.βv_vol
#print axioms ProofPhase.Existence.WilsonData.ym_vol
#print axioms ProofPhase.Existence.WilsonData.tendsto_a
#print axioms ProofPhase.Existence.massGapVF_toV_iff
#print axioms ProofPhase.Existence.slabDecay_of_torusDecay
#print axioms ProofPhase.Existence.massGapMF_of_torusDecay
#print axioms ProofPhase.Existence.bothOrders_of_torusDecay
LEAN
lake env lean /tmp/AxiomsWs4.lean 2>&1
echo "--- sorry / native_decide / axiom declarations in ProofPhase/Existence:"
grep -nE "sorry|native_decide|^axiom" /mnt/c/claude/gravity-ym/docs/mass-gap/formal/ProofPhase/Existence/*.lean || echo none
grep -c "warning" /tmp/ws4-build.log
