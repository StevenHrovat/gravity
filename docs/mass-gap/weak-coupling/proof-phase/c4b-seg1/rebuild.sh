#!/usr/bin/env bash
# c4b-seg1: clean rebuild of ProofPhase.Seg1 (removes the Seg1 build products first), then axioms into axioms.log.
set -euo pipefail
rm -rf ~/formal-c4b/.lake/build/lib/lean/ProofPhase/Seg1 ~/formal-c4b/.lake/build/ir/ProofPhase/Seg1
d=/mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c4b-seg1
bash $d/build.sh ProofPhase.Seg1.Envelope 400 | grep -E "Seg1|error|warning: ProofPhase/Seg1|Build" || true
bash $d/axioms.sh > $d/axioms.log 2>&1
cat $d/axioms.log
