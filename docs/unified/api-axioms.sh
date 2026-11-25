#!/usr/bin/env bash
# The form-layer API: build ProofPhase.API and its five example modules, list the axioms of EVERY declaration those six
# modules add (read from the compiled environment, so nested names and structure fields are included), and grep the
# sources for sorry / admit / native_decide / axiom. Run inside the WSL replay distro from the repository root as seen
# from WSL:
#   bash docs/unified/api-axioms.sh > docs/unified/api-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-api; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-api}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
mods="API API.Template API.YangMills API.GRH API.NP API.Phase"
for m in $mods; do
  echo "== build ProofPhase.$m"
  bash sync-build.sh ProofPhase.$m 2>&1 | grep -E "ProofPhase/API.*(warning|error)|^error|Build completed" || true
done
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsAPI.XXXXXX.lean)
cat > "$tmp" <<'EOF'
import ProofPhase.API.Template
import ProofPhase.API.YangMills
import ProofPhase.API.GRH
import ProofPhase.API.NP
import ProofPhase.API.Phase
open Lean Elab Command

/-- Print the axioms of every non-internal declaration that the six API modules add. -/
elab "#api_axioms" : command => do
  let env ← getEnv
  let mods : List Name := [`ProofPhase.API, `ProofPhase.API.Template, `ProofPhase.API.YangMills,
    `ProofPhase.API.GRH, `ProofPhase.API.NP, `ProofPhase.API.Phase]
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

#api_axioms
EOF
echo "== axioms (every declaration of the six modules)"
lake env lean "$tmp" 2>&1 | sed -e 's/^[^ ]*: info: //'
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/API.lean ProofPhase/API/*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/API*"
