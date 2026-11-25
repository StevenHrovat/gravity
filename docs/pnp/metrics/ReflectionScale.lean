/-! Kernel cost of a reflected check against the number of building blocks (NATIVE-METHOD.md, section 1). Append after
`ProofMetrics.lean` and `Layers.lean`, with `import Dmp` first. A recipe of `n` lines (a galaxy and `n - 1` stacked
knowledge layers), its verdict proved by `rfl` (the kernel evaluates the checker), and the kernel re-check time. -/

namespace Dmp.Layouts
def chainN (k : Nat) : Recipe :=
  { n := k
    line := fun i => if i = 0 then line .galaxy galaxyDot none else line .information knowledgeDot (some (i - 1)) }
theorem v4 : (chainN 4).verdict classes allAgree = .proven := rfl
theorem v8 : (chainN 8).verdict classes allAgree = .proven := rfl
theorem v16 : (chainN 16).verdict classes allAgree = .proven := rfl
theorem v32 : (chainN 32).verdict classes allAgree = .proven := rfl
theorem v64 : (chainN 64).verdict classes allAgree = .proven := rfl
theorem v128 : (chainN 128).verdict classes allAgree = .proven := rfl
end Dmp.Layouts

#eval show CoreM Unit from do
  let env ← getEnv
  IO.println "recipe lines,proof-term size,kernel ns"
  for (k, n) in [(4, `Dmp.Layouts.v4), (8, `Dmp.Layouts.v8), (16, `Dmp.Layouts.v16), (32, `Dmp.Layouts.v32),
      (64, `Dmp.Layouts.v64), (128, `Dmp.Layouts.v128)] do
    IO.println s!"{k},{(ProofMetrics.statsOf env `Dmp n).size},{← ProofMetrics.kernelNs env n}"
