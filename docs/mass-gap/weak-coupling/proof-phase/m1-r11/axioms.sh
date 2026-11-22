#!/usr/bin/env bash
# Run from the formal folder copy (e.g. FORMAL_DST). Prints axioms of every declaration of the Interface files
# (R11: MeasBlocking; R12: RandBlocking, SpectralUpgrade, DenseTransfer), then greps for sorry/native_decide/axiom.
set -e
cd "${FORMAL_DST:-$HOME/formal-r11}"
source ~/.elan/env
FILES="MeasBlocking RandBlocking SpectralUpgrade DenseTransfer"
{
for m in $FILES; do echo "import ProofPhase.Interface.$m"; done
echo "open ProofPhase.Interface"
for m in $FILES; do
  F=ProofPhase/Interface/$m.lean
  for n in $(grep -oP '^(theorem|def|structure|abbrev|instance) \K[A-Za-z_.0-9]+' "$F" | grep -v '^_root_'); do
    echo "#print axioms ProofPhase.Interface.$n"
  done
done
echo "#print axioms ProofPhase.RPBlocking.toMeas"
} > /tmp/AxR12.lean
lake env lean /tmp/AxR12.lean
for m in $FILES; do
  F=ProofPhase/Interface/$m.lean
  echo "--- grep sorry/native_decide/axiom in $m (expect none) ---"
  grep -n -w "sorry\|native_decide\|axiom" "$F" || echo "none"
done
