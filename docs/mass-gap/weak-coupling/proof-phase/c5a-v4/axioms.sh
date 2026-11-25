#!/usr/bin/env bash
# c5a-v4: #print axioms on the headline theorems (run after build.sh ProofPhase.V4.Top).
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c5a-v4/axioms.sh
cd ~/formal-c5a
source ~/.elan/env
cat > /tmp/AxiomsC5a.lean <<'LEAN'
import ProofPhase.V4.Top
#print axioms ProofPhase.OnLCP'.tendsto_a
#print axioms ProofPhase.OnLCP.eventually_mem_nhds
#print axioms ProofPhase.OnLCP.toOnLCP'
#print axioms ProofPhase.OnLCP'.eventually_actRate
#print axioms ProofPhase.fluxGrowth_of_conjW'
#print axioms ProofPhase.assembly_routeA'
#print axioms ProofPhase.not_onLCP'_of_bounded
#print axioms ProofPhase.V4.lawGapW_of_levelDprimeWOn
#print axioms ProofPhase.V4.lawGapBddW_of_lawGapW
#print axioms ProofPhase.V4.levelDprimeW_iff_on
#print axioms ProofPhase.V4.blockGapUnifW_iff_lawGapW
#print axioms ProofPhase.V4.blockGapBddW_iff_lawGapBddW
#print axioms ProofPhase.V4.blockGapBddW_of_unifW
#print axioms ProofPhase.V4.torusDecayLoc_of_blockGapBddW
#print axioms ProofPhase.V4.blockGapBddW_of_stageTwo
#print axioms ProofPhase.V4.blockGapBddW_of_levelDprimeWOn
#print axioms ProofPhase.V4.gibbsRep_of_uv1Polymer
#print axioms ProofPhase.V4.yang_mills_assembly_v4
#print axioms ProofPhase.V4.yang_mills_assembly_v4_bdd
#print axioms ProofPhase.V4.yang_mills_assembly_v4_inputs
#print axioms ProofPhase.V4.openInputsV4_of_unifW
#print axioms ProofPhase.V4.openInputsV4_of_levelTorusRouteW
#print axioms ProofPhase.V4.yang_mills_assembly_v4_strategyA
#print axioms ProofPhase.V4.not_trivial_v4
LEAN
lake env lean /tmp/AxiomsC5a.lean
grep -n "sorry\|native_decide\|^axiom" ProofPhase/V4/*.lean || echo "no sorry / native_decide / axiom in ProofPhase/V4"
