#!/usr/bin/env bash
# Print the axioms of every theorem/def of ProofPhase.Flip (run after build.sh).
set -euo pipefail
cd ~/formal-c6a
source ~/.elan/env
names=$(grep -hoE "^(theorem|def) [A-Za-z0-9_'.₀]+" ProofPhase/Flip/Bound.lean ProofPhase/Flip/Floor.lean | awk '{print $2}')
{
  echo "import ProofPhase.Flip.Bound"
  echo "import ProofPhase.Flip.Floor"
  for n in $names; do echo "#print axioms ProofPhase.Flip.$n"; done
} > /tmp/AxCheckFlip.lean
lake env lean /tmp/AxCheckFlip.lean 2>&1 | grep -E "depends on|does not depend|error" | sed 's/^.*\x27ProofPhase.Flip./ /' | sed 's/\x27 depends on axioms://' | sort -k2 | head -80
echo "count of names: $(echo "$names" | wc -w)"
grep -nE "sorry|native_decide|^axiom" ProofPhase/Flip/*.lean || echo "no sorry / native_decide / axiom in ProofPhase/Flip"
