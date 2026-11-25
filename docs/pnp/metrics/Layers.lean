/-! Per-layer proof cost (NATIVE-METHOD.md). Append after `ProofMetrics.lean` (which supplies `statsOf`); then
`#eval ProofMetrics.layers `ProofPhase [`ProofPhase.RouteB.abs_nCorr_le]`.

For a root theorem: its project-theorem dependency DAG, layered by depth (layer 1 = theorems that use no other project
theorem), and per layer the number of theorems, the summed proof-term size (distinct nodes, auxiliary constants inlined)
and the summed kernel re-check time (each declaration type-checked again by the kernel under a fresh name; best of 5
runs, nanoseconds). Read-only: the re-checked copies live in a throw-away environment. -/

namespace ProofMetrics

partial def closureList (env : Environment) (pfx : Name) (roots : List Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut order : Array Name := #[]
  let mut todo := roots
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | n :: rest =>
      todo := rest
      if !seen.contains n then
        seen := seen.insert n
        order := order.push n
        todo := (statsOf env pfx n).thmDeps.toList ++ todo
  return order

def kernelNs (env : Environment) (n : Name) : IO Nat := do
  match env.find? n with
  | some (.thmInfo v) =>
    let decl := Declaration.thmDecl { v with name := n ++ `__recheck, all := [n ++ `__recheck] }
    let mut best := 0
    for i in [0:5] do
      let t0 ← IO.monoNanosNow
      match env.addDeclCore 0 512 decl none with
      | .ok _ => pure ()
      | .error _ => throw (IO.userError s!"kernel rejected re-check of {n}")
      let t1 ← IO.monoNanosNow
      if i == 0 || t1 - t0 < best then best := t1 - t0
    return best
  | _ => return 0

def layers (pfx : Name) (roots : List Name) : CoreM Unit := do
  let env ← getEnv
  let all := closureList env pfx roots
  let mut depth : Std.HashMap Name Nat := {}
  -- depth inside the closure: 1 + max over direct project-theorem dependencies
  for _ in [0:all.size] do
    for n in all do
      let ds := (statsOf env pfx n).thmDeps.toList
      let d := ds.foldl (fun m x => max m (depth.getD x 0)) 0 + 1
      depth := depth.insert n d
  let maxD := all.foldl (fun m n => max m (depth.getD n 0)) 0
  IO.println s!"roots {roots}: {all.size} theorems in {maxD} layers"
  IO.println "layer,theorems,termSize,kernelNs,names"
  let mut totS := 0
  let mut totK := 0
  for k in [1:maxD + 1] do
    let ns := all.filter (fun n => depth.getD n 0 == k)
    let mut s := 0
    let mut t := 0
    for n in ns do
      s := s + (statsOf env pfx n).size
      t := t + (← kernelNs env n)
    totS := totS + s
    totK := totK + t
    IO.println s!"{k},{ns.size},{s},{t},{" ".intercalate (ns.toList.map toString)}"
  IO.println s!"total,{all.size},{totS},{totK},"

end ProofMetrics
