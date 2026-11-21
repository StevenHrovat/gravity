#!/usr/bin/env bash
# r3-monotone: clean rebuild of this attempt's Lean modules in ~/formal-att-r3-2 only, then axiom check.
set -u
DST="$HOME/formal-att-r3-2"
echo "target folder: $DST"
rm -rf "$DST/.lake/build/lib/lean/Attempts/R3/Monotone"* "$DST/.lake/build/ir/Attempts/R3/Monotone"*
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal && FORMAL_DST="$DST" bash sync-build.sh Attempts.R3.MonotoneCrossing 2>&1 | grep -E "^(error|warning)|Build|Monotone"
cd "$DST" && source ~/.elan/env && lake build Attempts.R3.MonotoneTwistEater 2>&1 | grep -E "^(error|warning)|Build|Monotone"
cat > "$DST/r3m_axioms.lean" <<'EOL'
import Attempts.R3.MonotoneCrossing
import Attempts.R3.MonotoneTwistEater
open Attempts.R3.Monotone
#print axioms uniform_decrement
#print axioms crossing_within
#print axioms reach_of_noFixedPoint
#print axioms monotone_not_enough
#print axioms grid_certificate
#print axioms dual_dual
#print axioms dual_strictAntiOn
#print axioms dual_pos
#print axioms prod_plaq2_comm
#print axioms no_flat_twist_comm
#print axioms eater_plaq
#print axioms eater_twisted_flat
#print axioms su2_commutator
#print axioms su2_twist_eater
#print axioms commutator_trivial_of_comm
EOL
lake env lean "$DST/r3m_axioms.lean"
rm -f "$DST/r3m_axioms.lean"
grep -n "sorry\|native_decide\|^axiom" Attempts/R3/Monotone*.lean || echo "no sorry/native_decide/axiom"
