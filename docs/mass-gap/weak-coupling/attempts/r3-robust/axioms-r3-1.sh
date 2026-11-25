#!/usr/bin/env bash
# Attempt r3-1: print the axioms of the main theorems (run after build-r3-1.sh), in ~/formal-att-r3-1 only.
cd ~/formal-att-r3-1 && source ~/.elan/env
cat > /tmp/r3-1-axioms.lean <<'LEAN'
import Attempts.R3.Robust
#print axioms Attempts.R3.gap_of_localFactors
#print axioms Attempts.R3.gap_of_localFactorsW
#print axioms Attempts.R3.gap_of_localFactorsW_fine
#print axioms Attempts.R3.levelFlat_of_local
#print axioms Attempts.R3.limit_decay
#print axioms Attempts.R3.continuum_decay
#print axioms Attempts.R3.effectiveConvergence_of_local
#print axioms Attempts.R3.limitGDS_of_flat
#print axioms Attempts.R3.flat_of_count
#print axioms Attempts.R3.theoremA_w
#print axioms Attempts.R3.influence_site
#print axioms Attempts.R3.specDist_site
LEAN
lake env lean /tmp/r3-1-axioms.lean
rm -f /tmp/r3-1-axioms.lean
grep -n "sorry\|native_decide\|^axiom" Attempts/R3/Robust.lean Attempts/R3/FlatFactors.lean Attempts/R3/TailDecay.lean || echo "no sorry/native_decide/axiom"
lake build Attempts.R3.Robust 2>&1 | grep -A3 "warning: Attempts/R3/\(Robust\|FlatFactors\|TailDecay\)" | head -30
