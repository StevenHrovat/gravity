#!/usr/bin/env bash
# Generalisation phase 2 (SU(N)): build the SU(N) layer in ~/formal-gen, recompile each new file to count warnings, print the
# axioms of every declaration (theorem, definition, instance) of the new modules, grep for sorry / admit / native_decide /
# axiom declarations.
#   wsl -d ym-replay -u ym -- bash -l /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/general/axioms-sun.sh
# Needs ~/formal-gen with a Mathlib .lake (mkdir -p ~/formal-gen && cp -a ~/formal/.lake ~/formal-gen/); delete it afterwards.
set -uo pipefail
src=/mnt/c/claude/gravity-ym/docs/mass-gap/formal
cd "$src"
FORMAL_DST=~/formal-gen bash sync-build.sh ProofPhase.General.TopSUN 2>&1 | tail -1
cd ~/formal-gen
source ~/.elan/env
echo "--- warnings and errors per file (lake env lean):"
for m in SUN Centre Projection Meas SUNSubst TopSUN; do
  n=$(lake env lean ProofPhase/General/$m.lean 2>&1 | grep -cE "^ProofPhase/General.*: (warning|error)")
  echo "$m.lean: $n"
done
cat > /tmp/AxiomsSUN.lean <<'LEAN'
import ProofPhase.General.TopSUN
open Lean Elab Command

-- Every declaration (theorem, definition, instance) of the phase 2 modules, with its axioms.
#eval show CoreM Unit from do
  let env ← getEnv
  let mods : List Name := [`ProofPhase.General.SUN, `ProofPhase.General.Centre, `ProofPhase.General.Projection,
    `ProofPhase.General.Meas, `ProofPhase.General.SUNSubst]
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
lake env lean /tmp/AxiomsSUN.lean > /tmp/axioms-sun.out 2>&1
cat /tmp/axioms-sun.out
grep -q "^COUNT " /tmp/axioms-sun.out || { echo "AXIOM RUN FAILED"; exit 1; }
echo "--- declarations with an axiom other than propext / Classical.choice / Quot.sound:"
grep "^AX " /tmp/axioms-sun.out | sed 's/.*: \[//; s/\]$//' | tr ',' '\n' | sed 's/^ *//' | sort -u | grep -vxE "propext|Classical.choice|Quot.sound|" || echo none
echo "--- sorry / admit / native_decide / axiom declarations in the new files:"
grep -nE "sorry|admit|native_decide|^axiom" $src/ProofPhase/General/{SUN,Centre,Projection,Meas,SUNSubst,TopSUN}.lean || echo none
