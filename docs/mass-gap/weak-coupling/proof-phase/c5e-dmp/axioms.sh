#!/usr/bin/env bash
# Print the axioms of every theorem of ProofPhase.DMP (run after build.sh). Writes a scratch file in ~/formal-c5e only.
set -euo pipefail
cd ~/formal-c5e
source ~/.elan/env
names=$(grep -hoE "^(theorem|def) [A-Za-z0-9_'.]+" ProofPhase/DMP/Doubling.lean ProofPhase/DMP/VacuumAct.lean | awk '{print $2}')
{
  echo "import ProofPhase.DMP.VacuumAct"
  echo "open ProofPhase.DMP"
  for n in $names; do case $n in gap|act|floor) n="BoxGaps.$n";; esac; echo "#print axioms ProofPhase.DMP.$n"; done
} > /tmp/AxCheckDMP.lean
lake env lean /tmp/AxCheckDMP.lean 2>&1 | grep -E "depends on|does not depend|error" | sed 's/^.*\x27ProofPhase.DMP./ /' | sort | uniq -c | sort -rn | head -80
echo "count of names: $(echo "$names" | wc -w)"
grep -nE "sorry|native_decide|^axiom" ProofPhase/DMP/*.lean || echo "no sorry / native_decide / axiom in ProofPhase/DMP"
