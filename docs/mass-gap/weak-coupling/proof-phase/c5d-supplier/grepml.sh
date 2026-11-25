#!/usr/bin/env bash
# c5d-supplier: grep Mathlib sources (read-only helper).
cd ~/formal-c5d/.lake/packages/mathlib && grep -rn "$1" Mathlib | head -n "${2:-30}"
