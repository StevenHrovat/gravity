#!/usr/bin/env bash
# r4-conjw: build Attempts.R4.ConjW in ~/formal-att-r4-3 only, print axioms, scan for sorry/axiom/native_decide.
# Run: wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/attempts/r4-conjw/build.sh
set -u
DST="$HOME/formal-att-r4-3"
if [ ! -d "$DST/.lake" ]; then mkdir -p "$DST" && cp -a "$HOME/formal/.lake" "$DST/"; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal && FORMAL_DST="$DST" bash sync-build.sh Attempts.R4.ConjW 2>&1 | grep -E "^(error|warning)|Build|R4|rror" | head -60
cd "$DST" && source ~/.elan/env
cat > "$DST/r4c_axioms.lean" <<'EOL'
import Attempts.R4.ConjW
open Attempts.R4.ConjW
#print axioms four_move_identity
#print axioms conjW_doubling
#print axioms coulomb_moves
#print axioms coulomb_frozen_box
#print axioms scale_invariant_frozen
#print axioms sandwich_certifies
#print axioms power_sandwich_certifies
#print axioms relief_exponential
#print axioms self_dual_point
#print axioms self_dual_unique
EOL
lake env lean "$DST/r4c_axioms.lean"
rm -f "$DST/r4c_axioms.lean"
grep -n "sorry\|native_decide\|^axiom" Attempts/R4/*.lean || echo "no sorry/native_decide/axiom"
