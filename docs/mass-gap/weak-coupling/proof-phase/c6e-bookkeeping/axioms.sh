#!/usr/bin/env bash
# Build the two top modules and print the axioms of the headline theorems.
set -uo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-c6e bash sync-build.sh ProofPhase.Book.TwoSize 2>&1 | grep -i "error\|sorry\|Build completed" | tail -5
FORMAL_DST=~/formal-c6e bash sync-build.sh ProofPhase.Book.KernelDensity 2>&1 | grep -i "error\|sorry\|Build completed" | tail -5
cd ~/formal-c6e; source ~/.elan/env
lake env lean /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c6e-bookkeeping/axioms.lean 2>&1 | grep -v "^$" | tr -d '\r' | tee /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c6e-bookkeeping/axioms.log
