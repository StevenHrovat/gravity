#!/usr/bin/env bash
# grep the pinned Mathlib of the private build folder:  bash grepml.sh <regex>
cd ~/formal-m1/.lake/packages/mathlib/Mathlib && grep -rn -E "$1" --include=*.lean . | head -${2:-20}
