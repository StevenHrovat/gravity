#!/usr/bin/env bash
# Print the axioms of the c5c-repair theorems (after build.sh ProofPhase.Repair.V4Bridge).
set -uo pipefail
cd ~/formal-c5c
source ~/.elan/env
tr -d '\r' < /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c5c-repair/axioms.lean > /tmp/c5c-axioms.lean
lake env lean /tmp/c5c-axioms.lean 2>&1
