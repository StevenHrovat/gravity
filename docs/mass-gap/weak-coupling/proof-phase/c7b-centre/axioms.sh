#!/usr/bin/env bash
# Print the axioms of every theorem/def of ProofPhase.Centre (run after build.sh).
set -euo pipefail
cd ~/formal-c7b
source ~/.elan/env
mods="Ginibre Comparison Z2Wilson Combined"
{
  for m in $mods; do echo "import ProofPhase.Centre.$m"; done
  for m in $mods; do
    for n in $(grep -hoE "^(theorem|def|instance) [A-Za-z0-9_'.₀]+" ProofPhase/Centre/$m.lean | grep -v instance | awk '{print $2}'); do
      echo "#print axioms ProofPhase.Centre.$n"
    done
  done
} > /tmp/AxCheckCentre.lean
# Z2 members live in namespace Z2
sed -i 's/ProofPhase.Centre.\(mul_val\|one_val\|inv_eq\|ext.\|neg\|comm\|gaugeReTr_eq\|rep_neg\|rep\)$/ProofPhase.Centre.Z2.\1/' /tmp/AxCheckCentre.lean
lake env lean /tmp/AxCheckCentre.lean 2>&1 | grep -E "depends on|does not depend|error" | sed 's/^.*Centre\./ /' | sort -u -k1,1 | head -150
grep -nE "sorry|native_decide|^axiom" ProofPhase/Centre/*.lean || echo "no sorry / native_decide / axiom in ProofPhase/Centre"
