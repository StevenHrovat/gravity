#!/usr/bin/env bash
# Generalisation phase 1b (ported inst files): build the ported layer in ~/formal-gen, recompile each new file to count warnings, print the
# axioms of every declaration (theorem, definition, instance) of the new modules, grep for sorry / admit / native_decide /
# axiom declarations.
#   wsl -d ym-replay -u ym -- bash -l <repository>/docs/mass-gap/weak-coupling/proof-phase/general/axioms-port.sh
# Needs ~/formal-gen with a Mathlib .lake (mkdir -p ~/formal-gen && cp -a ~/formal/.lake ~/formal-gen/); delete it afterwards.
set -uo pipefail
src="$(cd "$(dirname "$0")/../../../formal" && pwd)"
cd "$src"
FORMAL_DST=~/formal-gen bash sync-build.sh ProofPhase.General.TopPort 2>&1 | tail -1
cd ~/formal-gen
source ~/.elan/env
echo "--- warnings and errors per file (lake env lean):"
for m in Setting CondMass Fine Wilson Concrete Anchor Cube Gap Recursion PortSUN TopPort; do
  n=$(lake env lean ProofPhase/General/$m.lean 2>&1 | grep -cE "^ProofPhase/General.*: (warning|error)")
  echo "$m.lean: $n"
done
cat > /tmp/AxiomsPort.lean <<'LEAN'
import ProofPhase.General.TopPort
open Lean Elab Command

-- Every declaration (theorem, definition, instance) of the phase 1b modules, with its axioms.
#eval show CoreM Unit from do
  let env ← getEnv
  let mods : List Name := [`ProofPhase.General.Setting, `ProofPhase.General.CondMass, `ProofPhase.General.Fine,
    `ProofPhase.General.Wilson, `ProofPhase.General.Concrete, `ProofPhase.General.Anchor, `ProofPhase.General.Cube,
    `ProofPhase.General.Gap, `ProofPhase.General.Recursion, `ProofPhase.General.PortSUN]
  let mut names : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mods.contains mod do continue
    if n.isInternal || isAuxRecursor env n || isNoConfusion env n || Lean.Meta.isMatcherCore env n then continue
    match ci with
    | .thmInfo _ | .defnInfo _ => names := names.push n
    | _ => pure ()
  let sorted := names.qsort (fun a b => a.toString < b.toString)
  for n in sorted do
    let axs ← collectAxioms n
    IO.println s!"AX {n} : {axs.toList}"
  IO.println s!"COUNT {sorted.size}"
LEAN
lake env lean /tmp/AxiomsPort.lean > /tmp/axioms-port.out 2>&1
cat /tmp/axioms-port.out
grep -q "^COUNT " /tmp/axioms-port.out || { echo "AXIOM RUN FAILED"; exit 1; }
echo "--- declarations with an axiom other than propext / Classical.choice / Quot.sound:"
grep "^AX " /tmp/axioms-port.out | sed 's/.*: \[//; s/\]$//' | tr ',' '\n' | sed 's/^ *//' | sort -u | grep -vxE "propext|Classical.choice|Quot.sound|" || echo none
echo "--- sorry / admit / native_decide / axiom declarations in the new files:"
grep -nE "sorry|admit|native_decide|^axiom" $src/ProofPhase/General/{Setting,CondMass,Fine,Wilson,Concrete,Anchor,Cube,Gap,Recursion,PortSUN,TopPort}.lean || echo none
