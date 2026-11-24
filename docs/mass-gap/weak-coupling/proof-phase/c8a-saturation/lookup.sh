#!/usr/bin/env bash
# grep Mathlib (and the project copy) for a pattern: bash lookup.sh 'pattern' [subdir]
cd ~/formal-c9a/.lake/packages/mathlib
grep -rn -E "$1" Mathlib/${2:-} | head -${3:-30}
