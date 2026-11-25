#!/usr/bin/env bash
# Print the axioms of every theorem/def of ProofPhase.FluxVac (run after build.sh).
set -euo pipefail
cd ~/formal-c7a
source ~/.elan/env
names=$(grep -hoE "^(theorem|def) [A-Za-z0-9_'.₀]+" ProofPhase/FluxVac/*.lean | awk '{print $2}')
{
  for f in ProofPhase/FluxVac/*.lean; do m=${f%.lean}; echo "import ${m//\//.}"; done
  for n in $names; do echo "#print axioms ProofPhase.FluxVac.$n"; done
} > /tmp/AxCheckFluxVac.lean
lake env lean /tmp/AxCheckFluxVac.lean 2>&1 | grep -E "depends on|does not depend|error" | sed 's/^.*\x27ProofPhase.FluxVac./ /' | sed 's/\x27 depends on axioms://' | sort -k2 | head -80
echo "count of names: $(echo "$names" | wc -w)"
grep -nE "sorry|native_decide|^axiom" ProofPhase/FluxVac/*.lean || echo "no sorry / native_decide / axiom in ProofPhase/FluxVac"
