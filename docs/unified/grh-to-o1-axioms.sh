#!/usr/bin/env bash
# GRH to O1: build ProofPhase.Unified.GRHToO1, list the axioms of EVERY declaration the module adds (read from the
# compiled environment, so nested names and structure fields are included), and grep the source for sorry / admit /
# native_decide / axiom. Run inside the WSL replay distro from the repository root as seen from WSL:
#   bash docs/unified/grh-to-o1-axioms.sh > docs/unified/grh-to-o1-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-o1; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-o1}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.Unified.GRHToO1"
bash sync-build.sh ProofPhase.Unified.GRHToO1 2>&1 | grep -E "ProofPhase/Unified/GRHToO1.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsGRHToO1.XXXXXX.lean)
cat > "$tmp" <<'EOF'
import ProofPhase.Unified.GRHToO1
open Lean Elab Command

/-- Print the axioms of every non-internal declaration that the module adds. -/
elab "#mod_axioms" : command => do
  let env ← getEnv
  let mods : List Name := [`ProofPhase.Unified.GRHToO1]
  let std : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if mods.contains env.header.moduleNames[idx.toNat]! && !n.isInternal then
        names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut bad : Nat := 0
  for n in names do
    let axs ← liftCoreM (collectAxioms n)
    let extra := axs.filter (fun a => !std.contains a)
    if !extra.isEmpty then bad := bad + 1
    logInfo m!"{n}: {axs.toList}"
  logInfo m!"declarations: {names.size}; with a non-standard axiom: {bad}"

#mod_axioms
EOF
echo "== axioms (every declaration of the module)"
lake env lean "$tmp" 2>&1 | sed -e 's/^[^ ]*: info: //'
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Unified/GRHToO1.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Unified/GRHToO1.lean"
