#!/usr/bin/env bash
# r4-minting (round 4, attempt 4): build Attempts.R4.MintingDmp and Attempts.R4.MintingScale in ~/formal-att-r4-4 only,
# then print axioms of every theorem and scan the sources for sorry/axiom/native_decide.
# Run: wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/attempts/r4-minting/build.sh
set -u
DST="$HOME/formal-att-r4-4"
if [ ! -d "$DST/.lake" ]; then mkdir -p "$DST" && cp -a "$HOME/formal/.lake" "$DST/"; fi
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
for m in Attempts.R4.MintingDmp Attempts.R4.MintingScale; do
  FORMAL_DST="$DST" bash sync-build.sh "$m" 2>&1 | grep -E "^(error|warning)|Build|Minting|rror" | head -80
done
cd "$DST" && source ~/.elan/env
{
  echo "import Attempts.R4.MintingDmp"
  echo "import Attempts.R4.MintingScale"
  echo "open Attempts.R4.Minting"
  for f in Attempts/R4/MintingDmp.lean Attempts/R4/MintingScale.lean; do
    grep -oE "^theorem [A-Za-z0-9_.']+" "$f" | awk '{print "#print axioms " $2}'
  done
} > "$DST/r4m_axioms.lean"
lake env lean "$DST/r4m_axioms.lean"
rm -f "$DST/r4m_axioms.lean"
grep -n "sorry\|native_decide\|^axiom" Attempts/R4/Minting*.lean || echo "no sorry/native_decide/axiom"
