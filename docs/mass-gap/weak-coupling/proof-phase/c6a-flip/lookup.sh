cd ~/formal/.lake/packages/mathlib
grep -n "theorem\|def \|lemma" Mathlib/Analysis/Subadditive.lean | head -30
grep -rn "theorem integral_pos_iff_support_of_nonneg\b" Mathlib/MeasureTheory | head
grep -rn "theorem integral_comp_of_measurePreserving" /home/ym/formal/Positivity/Abstract.lean
sed -n 60,100p /home/ym/formal/Positivity/Abstract.lean
grep -rn "instance.*NeZero.*mul\|theorem NeZero.mul\|instance mul" Mathlib/Algebra/NeZero.lean Mathlib/Algebra/GroupWithZero/NeZero.lean 2>/dev/null | head
ls ~ ; ls ~/formal-c6a 2>/dev/null | head -3
