#!/usr/bin/env bash
# The closures round (2026-11-24, docs/paper/OPEN-CLAIMS-CLOSURES.md): build the five new modules under
# ProofPhase/Closures/, list the axioms of EVERY declaration they add (read from the compiled environment, so nested names and
# structure fields are included), and grep the sources for sorry / admit / native_decide / axiom. Run inside the WSL replay
# distro from the repository root as seen from WSL:
#   bash docs/unified/closures-axioms.sh > docs/unified/closures-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-close; seed it with ~/formal's .lake/packages and lake-manifest.json, and a copy of
# a built .lake/build to avoid rebuilding the project).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-close}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
mods="Closures.Anomaly Closures.OneBoxForm Closures.ChainJoint Closures.EulerCurve Closures.NonTrivialSplit"
for m in $mods; do
  echo "== build ProofPhase.$m"
  bash sync-build.sh ProofPhase.$m 2>&1 | grep -E "ProofPhase/Closures.*(warning|error)|^error|Build completed" || true
done
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsClosures.XXXXXX.lean)
cat > "$tmp" <<'EOF'
import ProofPhase.Closures.Anomaly
import ProofPhase.Closures.OneBoxForm
import ProofPhase.Closures.ChainJoint
import ProofPhase.Closures.EulerCurve
import ProofPhase.Closures.NonTrivialSplit
open Lean Elab Command

/-- Print the axioms of every non-internal declaration that the five closure modules add. -/
elab "#closures_axioms" : command => do
  let env ← getEnv
  let mods : List Name := [`ProofPhase.Closures.Anomaly, `ProofPhase.Closures.OneBoxForm,
    `ProofPhase.Closures.ChainJoint, `ProofPhase.Closures.EulerCurve, `ProofPhase.Closures.NonTrivialSplit]
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

#closures_axioms
EOF
echo "== axioms (every declaration of the five modules)"
lake env lean "$tmp" 2>&1 | sed -e 's/^[^ ]*: info: //'
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Closures/*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Closures"
