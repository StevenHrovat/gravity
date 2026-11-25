#!/usr/bin/env bash
# The PP-typed, Yang-Mills shaped interface (Draft 7, III.13): build ProofPhase.API.Perelman, list the axioms of EVERY
# declaration it adds (read from the compiled environment, so nested names and structure fields are included), and grep
# the source for sorry / admit / native_decide / axiom. Run inside the WSL replay distro from the repository root as seen
# from WSL:
#   bash docs/unified/perelman-axioms.sh > docs/unified/perelman-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
mods="API.Perelman"
for m in $mods; do
  echo "== build ProofPhase.$m"
  bash sync-build.sh ProofPhase.$m 2>&1 | grep -E "ProofPhase/API.*(warning|error)|^error|Build completed" || true
done
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsPerelman.XXXXXX.lean)
cat > "$tmp" <<'EOF'
import ProofPhase.API.Perelman
open Lean Elab Command

/-- Print the axioms of every non-internal declaration that the interface module adds. -/
elab "#perelman_axioms" : command => do
  let env ← getEnv
  let mods : List Name := [`ProofPhase.API.Perelman]
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

#perelman_axioms
EOF
echo "== axioms (every declaration of the module)"
lake env lean "$tmp" 2>&1 | sed -e 's/^[^ ]*: info: //'
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/API/Perelman.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/API/Perelman.lean"
