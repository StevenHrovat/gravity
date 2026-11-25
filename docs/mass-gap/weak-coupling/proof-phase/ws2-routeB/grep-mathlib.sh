cd ~/formal-ws2/.lake/packages/mathlib
grep -rn "theorem IsCompact.tendsto_subseq\|theorem tendsto_subseq_of_bounded\|FirstCountableTopology (∀\|FirstCountableTopology ((i\|theorem tendsto_pi_nhds" Mathlib | head
grep -rn "theorem tendsto_atTop_ciInf\|theorem abs_le_of_sq_le_sq\|theorem sq_le_sq'\|theorem abs_le_of_sq_le\|theorem pow_le_pow_left₀\|theorem abs_le_abs_of_sq_le_sq" Mathlib | head
