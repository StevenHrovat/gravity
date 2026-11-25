import Lean
open Lean Meta

/-! Read-only proof metrics (NATIVE-OPTIMIZATION.md). Prepend the imports of the target library, then append
`#eval ProofMetrics.run `Dmp` (or `ProofPhase`). Prints one CSV line per theorem of the project. -/

namespace ProofMetrics

structure Stats where
  size : Nat := 0          -- distinct Expr nodes in the proof term (aux inlined)
  witness : Nat := 0       -- Exists.intro, Subtype.mk, Sigma.mk, PSigma.mk
  existsUse : Nat := 0     -- Exists.casesOn / Exists.elim / Exists.choose (consuming a witness)
  cases : Nat := 0         -- branching eliminations: casesOn of >= 2 constructors, matchers with >= 2 alts, dite/ite, Or.elim, byCases
  induct : Nat := 0        -- rec / brecOn / recOn / binductionOn / WellFounded.fix
  contra : Nat := 0        -- False.elim, absurd, byContradiction
  clash : Nat := 0         -- noConfusion (constructor clash: an impossible branch of a computation)
  classical : Nat := 0     -- Classical.em / byContradiction / byCases / choice / choose / propDecidable
  decide : Nat := 0        -- of_decide_eq_true, Decidable.decide (kernel computation)
  rfl : Nat := 0           -- Eq.refl / rfl
  thmDeps : NameSet := {}  -- project theorems used directly
  defDeps : NameSet := {}  -- project definitions used directly
  visitedC : NameSet := {}

def isAuxName (n : Name) : Bool :=
  n.isInternalDetail ||
  (match n with
   | .str _ s => s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "eq_" || s.startsWith "_" ||
                 s == "eq_def" || s.startsWith "spec_" || s == "induct" || s.startsWith "fun_cases"
   | _ => false)

def numCtors (env : Environment) (ind : Name) : Nat :=
  match env.find? ind with
  | some (.inductInfo v) => v.ctors.length
  | _ => 0

def isRecursive (env : Environment) (ind : Name) : Bool :=
  match env.find? ind with
  | some (.inductInfo v) => v.isRec
  | _ => false

def classify (env : Environment) (n : Name) (s : Stats) : Stats :=
  let s := if n == ``Exists.intro || n == ``Subtype.mk || n == ``Sigma.mk || n == ``PSigma.mk then
      { s with witness := s.witness + 1 } else s
  let s := if n == ``Exists.casesOn || n == ``Exists.elim || n == ``Exists.choose || n == ``Exists.rec ||
      n == ``Classical.choose || n == ``Exists.choose_spec || n == ``Classical.choose_spec then
      { s with existsUse := s.existsUse + 1 } else s
  let s := if n == ``False.elim || n == ``False.rec || n == ``False.casesOn || n == ``absurd ||
      n == ``Classical.byContradiction || n == ``Decidable.byContradiction || n == ``Empty.elim ||
      n == ``Empty.rec || n == ``Empty.casesOn || n == ``Not.elim then
      { s with contra := s.contra + 1 } else s
  let s := match n with
    | .str _ "noConfusion" => { s with clash := s.clash + 1 }
    | _ => s
  let s := if n == ``Classical.em || n == ``Classical.byContradiction || n == ``Classical.byCases ||
      n == ``Classical.choice || n == ``Classical.choose || n == ``Classical.propDecidable ||
      n == ``Classical.not_not then
      { s with classical := s.classical + 1 } else s
  let s := if n == ``of_decide_eq_true || n == ``Decidable.decide || n == ``of_decide_eq_false then
      { s with decide := s.decide + 1 } else s
  let s := if n == ``Eq.refl || n == ``rfl || n == ``Iff.refl || n == ``HEq.refl then { s with rfl := s.rfl + 1 } else s
  let s := if n == ``dite || n == ``ite || n == ``Or.elim || n == ``Decidable.byCases || n == ``Classical.byCases ||
      n == ``Or.casesOn || n == ``Or.rec || n == ``Decidable.casesOn || n == ``Decidable.rec || n == ``cond ||
      n == ``Bool.casesOn || n == ``Bool.rec || n == ``Or.resolve_left || n == ``Or.resolve_right then
      { s with cases := s.cases + 1 } else s
  let s := match n with
    | .str ind "casesOn" =>
      if n == ``Or.casesOn || n == ``Bool.casesOn || n == ``Decidable.casesOn || n == ``Exists.casesOn then s
      else if numCtors env ind ≥ 2 then { s with cases := s.cases + 1 } else s
    | .str ind "rec" | .str ind "recOn" | .str ind "brecOn" | .str ind "binductionOn" =>
      if n == ``Or.rec || n == ``Bool.rec || n == ``Decidable.rec || n == ``Exists.rec || n == ``False.rec ||
        n == ``Empty.rec then s
      else if isRecursive env ind then { s with induct := s.induct + 1 }
      else if numCtors env ind ≥ 2 then { s with cases := s.cases + 1 } else s
    | _ => s
  let s := if n == ``WellFounded.fix || n == ``WellFounded.fix_eq then { s with induct := s.induct + 1 } else s
  match Meta.Match.Extension.getMatcherInfo? env n with
  | some mi => if mi.numAlts ≥ 2 then { s with cases := s.cases + 1 } else s
  | none => s

partial def walk (env : Environment) (pfx : Name) (e : Expr) : StateM (Stats × Std.HashSet Expr) Unit := do
  let (s, vis) ← get
  if vis.contains e then return
  set (s, vis.insert e)
  modify fun (s, v) => ({ s with size := s.size + 1 }, v)
  match e with
  | .const n _ =>
    modify fun (s, v) => (classify env n s, v)
    if pfx.isPrefixOf n then
      if isAuxName n || (Meta.Match.Extension.getMatcherInfo? env n).isSome then
        let (s, _) ← get
        unless s.visitedC.contains n do
          modify fun (s, v) => ({ s with visitedC := s.visitedC.insert n }, v)
          match env.find? n with
          | some ci => match ci.value? (allowOpaque := true) with
            | some val => walk env pfx val
            | none => pure ()
          | none => pure ()
      else
        match env.find? n with
        | some (.thmInfo _) => modify fun (s, v) => ({ s with thmDeps := s.thmDeps.insert n }, v)
        | some _ => modify fun (s, v) => ({ s with defDeps := s.defDeps.insert n }, v)
        | none => pure ()
  | .app f a => walk env pfx f; walk env pfx a
  | .lam _ t b _ => walk env pfx t; walk env pfx b
  | .forallE _ t b _ => walk env pfx t; walk env pfx b
  | .letE _ t v b _ => walk env pfx t; walk env pfx v; walk env pfx b
  | .mdata _ b => walk env pfx b
  | .proj _ _ b => walk env pfx b
  | _ => pure ()

def statsOf (env : Environment) (pfx : Name) (n : Name) : Stats :=
  match env.find? n with
  | some ci => match ci.value? (allowOpaque := true) with
    | some val => ((walk env pfx val).run ({}, {})).2.1
    | none => {}
  | none => {}

partial def goalHead (e : Expr) : String :=
  match e with
  | .forallE _ _ b _ => goalHead b
  | .mdata _ b => goalHead b
  | _ => match e.getAppFn with
    | .const n _ => match n with
      | ``Exists => "exists" | ``Iff => "iff" | ``Eq => "eq" | ``Not => "not" | ``And => "and" | ``Or => "or"
      | ``Ne => "ne" | ``False => "false" | ``LE.le => "le" | ``LT.lt => "lt" | ``HEq => "eq" | ``Subtype => "exists"
      | _ => "other"
    | _ => "other"

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

def run (pfx : Name) (modPfx : Name := pfx) : CoreM Unit := do
  let env ← getEnv
  let mut thms : Array Name := #[]
  let mut defs : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if pfx.isPrefixOf n && !isAuxName n && modPfx.isPrefixOf (moduleOf env n) &&
        (Meta.Match.Extension.getMatcherInfo? env n).isNone && !n.isInternal then
      match ci with
      | .thmInfo _ => thms := thms.push n
      | .defnInfo _ => defs := defs.push n
      | _ => pure ()
  let mut stats : Std.HashMap Name Stats := {}
  for n in thms ++ defs do
    stats := stats.insert n (statsOf env pfx n)
  -- depth over theorems only, and over theorems + definitions (proof terms and definition bodies)
  let mut dThm : Std.HashMap Name Nat := {}
  let mut dAll : Std.HashMap Name Nat := {}
  let mut cThm : Std.HashMap Name NameSet := {}
  -- process in an order where dependencies come first: iterate until fixed point (DAG, small)
  let all := thms ++ defs
  let mut changed := true
  let mut rounds := 0
  while changed && rounds < 400 do
    changed := false
    rounds := rounds + 1
    for n in all do
      let s := stats.getD n {}
      let isThm := thms.contains n
      let mut mT := 0
      let mut mA := 0
      let mut clo : NameSet := {}
      for d in s.thmDeps.toList do
        if stats.contains d then
          mT := max mT (dThm.getD d 0)
          mA := max mA (dAll.getD d 0)
          clo := clo.insert d
          for x in (cThm.getD d {}).toList do clo := clo.insert x
      for d in s.defDeps.toList do
        if stats.contains d then
          mA := max mA (dAll.getD d 0)
          for x in (cThm.getD d {}).toList do clo := clo.insert x
      let newT := if isThm then mT + 1 else mT
      let newA := mA + 1
      if dThm.getD n 0 != newT || dAll.getD n 0 != newA || (cThm.getD n {}).size != clo.size then
        changed := true
        dThm := dThm.insert n newT
        dAll := dAll.insert n newA
        cThm := cThm.insert n clo
  let mut usedBy : Std.HashMap Name Nat := {}
  for n in thms do
    for d in (stats.getD n {}).thmDeps.toList do
      usedBy := usedBy.insert d (usedBy.getD d 0 + 1)
  IO.println "name,module,goal,size,thmDeps,defDeps,depthThm,depthAll,closureThm,witness,existsUse,cases,induct,contra,clash,classical,decide,rfl,usedBy,axioms"
  for n in thms do
    let s := stats.getD n {}
    let axs ← Lean.collectAxioms n
    let ax := String.intercalate "+" (axs.toList.map (fun a => match a with
      | ``propext => "P" | ``Classical.choice => "C" | ``Quot.sound => "Q" | _ => a.toString))
    let ax := if ax.isEmpty then "none" else ax
    IO.println s!"{n},{moduleOf env n},{goalHead ((env.find? n).map (·.type) |>.getD (.sort .zero))},{s.size},{s.thmDeps.size},{s.defDeps.size},{dThm.getD n 0},{dAll.getD n 0},{(cThm.getD n {}).size},{s.witness},{s.existsUse},{s.cases},{s.induct},{s.contra},{s.clash},{s.classical},{s.decide},{s.rfl},{usedBy.getD n 0},{ax}"
  IO.eprintln s!"rounds {rounds}, theorems {thms.size}, definitions {defs.size}"


partial def longest (env : Environment) (pfx : Name) (n : Name) : StateM (Std.HashMap Name (List Name)) (List Name) := do
  if let some c := (← get).get? n then return c
  let deps := (statsOf env pfx n).thmDeps.toList
  let mut best : List Name := []
  for d in deps do
    let c ← longest env pfx d
    if c.length > best.length then best := c
  let r := n :: best
  modify (·.insert n r)
  return r
def showChains (pfx : Name) (roots : List Name) : CoreM Unit := do
  let env ← getEnv
  for r in roots do
    let c := ((longest env pfx r).run {}).1
    IO.println s!"{r} ({c.length}): {c.map (fun n => (n.replacePrefix pfx .anonymous).toString)}"

end ProofMetrics
