#!/usr/bin/env bash
# Run from the formal folder copy (e.g. FORMAL_DST). Prints axioms of every theorem of the new file, then greps.
set -e
cd "${FORMAL_DST:-$HOME/formal-r11}"
source ~/.elan/env
F=ProofPhase/Interface/MeasBlocking.lean
{
echo "import ProofPhase.Interface.MeasBlocking"
echo "open ProofPhase.Interface"
for n in $(grep -oP '^(theorem|def|structure|abbrev) \K[A-Za-z_.0-9]+' "$F" | grep -v '^_root_'); do
  echo "#print axioms ProofPhase.Interface.$n"
done
echo "#print axioms ProofPhase.RPBlocking.toMeas"
} > /tmp/AxR11.lean
lake env lean /tmp/AxR11.lean
echo "--- grep sorry/native_decide/axiom in the new file (expect none) ---"
grep -n -w "sorry\|native_decide\|axiom" "$F" || echo "none"
