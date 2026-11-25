#!/usr/bin/env bash
# ws3-quantum: build one target in ~/formal-ws3 (one build at a time); prints ProofPhase errors only.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/ws3-quantum/build.sh ProofPhase.Quantum.<Module>
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-ws3 bash sync-build.sh "${1:-ProofPhase.Quantum.LemmaT}" > /tmp/ws3-build.log 2>&1
grep -A14 "error: ProofPhase" /tmp/ws3-build.log | head -${2:-200}
grep -E "Build completed|build failed|warning: .*sorry" /tmp/ws3-build.log | tail -5
