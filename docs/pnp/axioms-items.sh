#!/usr/bin/env bash
# P vs NP dictionary, "Unconditional for finite systems": build the two Lean modules Classical and FiniteSpectral of
# ProofPhase/Mixing, run #print axioms on every declaration of both, then grep the sources for sorry / admit /
# native_decide / axiom. Run inside the WSL replay distro (Lean 4.34.0, Mathlib v4.34.0), from the repository root as
# seen from WSL:
#   bash docs/pnp/axioms-items.sh > docs/pnp/axioms-items.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-mix; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-mix}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
for m in Classical FiniteSpectral; do
  echo "== build ProofPhase.Mixing.$m"
  bash sync-build.sh ProofPhase.Mixing.$m 2>&1 | grep -E "warning|error|Build completed" || true
done
# declarations that sit in the namespace ProofPhase.Mixing.SiteDynamics; everything else is in ProofPhase.Mixing
sd="isProbabilityMeasure_rsStep rsStep_real"
{
  echo "import ProofPhase.Mixing.Classical"
  echo "import ProofPhase.Mixing.FiniteSpectral"
  for f in Classical FiniteSpectral; do
    grep -hoE "^(theorem|def|abbrev) [A-Za-z0-9_.']+" "$src/ProofPhase/Mixing/$f.lean" | awk '{print $2}' | while read -r n; do
      case " $sd " in
        *" $n "*) echo "#print axioms ProofPhase.Mixing.SiteDynamics.$n" ;;
        *) echo "#print axioms ProofPhase.Mixing.$n" ;;
      esac
    done
  done
} > /tmp/AxiomsItems.lean
cd "$FORMAL_DST"
source ~/.elan/env
echo "== axioms"
lake env lean /tmp/AxiomsItems.lean
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Mixing/Classical.lean ProofPhase/Mixing/FiniteSpectral.lean || echo "no sorry / admit / native_decide / axiom in Classical.lean, FiniteSpectral.lean"
