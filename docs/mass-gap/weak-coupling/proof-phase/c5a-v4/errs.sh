#!/usr/bin/env bash
# c5a-v4: sync, then compile one file directly and print only the error blocks (first lines + goal).
#   wsl -d ym-replay -u ym -- bash /mnt/c/.../c5a-v4/errs.sh ProofPhase/V4/Recursion.lean
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c5a bash sync-build.sh "${2:-ProofPhase.V4.Gap}" > /tmp/c5a-dep.log 2>&1 || true
cd ~/formal-c5a
source ~/.elan/env
lake env lean "$1" > /tmp/c5a-err.log 2>&1
awk '/: error/{p=1; n=0} /: warning/{p=0} p{ if (n<12 || /⊢/) print; n++ }' /tmp/c5a-err.log | head -${3:-150}
grep -c ": error" /tmp/c5a-err.log
