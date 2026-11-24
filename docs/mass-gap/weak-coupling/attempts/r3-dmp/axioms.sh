#!/usr/bin/env bash
# Print the axioms of every r3-dmp theorem (run after build.sh), and check for sorry in the sources.
set -uo pipefail
cd ~/formal-att-r3-5
source ~/.elan/env
grep -n "sorry\|^axiom\|native_decide" Attempts/R3/Dmp*.lean || echo "no sorry/axiom/native_decide in sources"
{
  for m in DmpBridge DmpFlow DmpBalance DmpDuality; do echo "import Attempts.R3.$m"; done
  for f in Attempts/R3/Dmp*.lean; do
    grep -oP "^theorem \K[A-Za-z_.']+" "$f" | sed 's/^/#print axioms Attempts.R3.DmpHost./'
  done
} > /tmp/r3dmp_axioms.lean
lake env lean /tmp/r3dmp_axioms.lean 2>&1 | sed 's/^.*depends on axioms: //' | sort | uniq -c
lake env lean /tmp/r3dmp_axioms.lean 2>&1 | grep -c "depends on axioms"
grep -c "^#print" /tmp/r3dmp_axioms.lean
for f in Attempts/R3/Dmp*.lean; do echo "== warnings in $f"; lake env lean "$f" 2>&1 | grep -E "warning|error" | head -10; done
