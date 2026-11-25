#!/usr/bin/env bash
# DMP scout (round-4 prep): build Attempts.R4prep.ActIdentity in ~/formal-r4prep only, then print axioms and scan for sorry/axiom.
# Run: wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/round4-prep/build.sh
set -u
DST="$HOME/formal-r4prep"
if [ ! -d "$DST/.lake" ]; then mkdir -p "$DST" && cp -a "$HOME/formal/.lake" "$DST/"; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal && FORMAL_DST="$DST" bash sync-build.sh Attempts.R4prep.ActIdentity 2>&1 | grep -E "^(error|warning)|Build|R4prep|rror" | head -60
cd "$DST" && source ~/.elan/env
cat > "$DST/r4p_axioms.lean" <<'EOL'
import Attempts.R4prep.ActIdentity
open Attempts.R4prep.Act
#print axioms act_piece_floor
#print axioms act_chain_floor
#print axioms act_number_quadratic
#print axioms single_act_frozen
#print axioms coulomb_frozen
#print axioms string_quadruples
#print axioms power_doubling
#print axioms power_doubling_gt_one
#print axioms act_reach
#print axioms nonincreasing_never_reaches
#print axioms boundary_iff_ttl
EOL
lake env lean "$DST/r4p_axioms.lean"
rm -f "$DST/r4p_axioms.lean"
grep -n "sorry\|native_decide\|^axiom" Attempts/R4prep/*.lean || echo "no sorry/native_decide/axiom"
