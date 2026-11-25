#!/usr/bin/env bash
# Look up Mathlib lemma names in the formal project's Mathlib (read-only helper).
cd ~/formal/.lake/packages/mathlib/Mathlib
grep -rn "sSup_of_not_bddAbove\|theorem sSup_empty\|theorem sum_range_sub'\|theorem pow_unbounded_of_one_lt\|theorem Summable.sum_le_tsum\|theorem sum_le_tsum" . 2>/dev/null | grep -v "NNReal\|ENNReal\|WithTop\|Nat/" | head -20
