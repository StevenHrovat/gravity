#!/usr/bin/env bash
# Dichotomy transfer: build ProofPhase/Proof/Crossing and Complete (and the Proof modules they import), run #print axioms
# on every declaration of Crossing.lean and Complete.lean, then grep the Proof sources for sorry / admit /
# native_decide / axiom. Run inside the WSL
# replay distro (Lean 4.34.0, Mathlib v4.34.0), from the repository root as seen from WSL:
#   bash docs/pnp/axioms-crossing.sh > docs/pnp/axioms-crossing.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-proof; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-proof}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
for m in Crossing Complete; do
  echo "== build ProofPhase.Proof.$m"
  bash sync-build.sh ProofPhase.Proof.$m 2>&1 | grep -E "warning|error|Build completed" || true
done
cd "$FORMAL_DST"
source ~/.elan/env
names="Tseitin.bd1 Tseitin.bd1_eq_boundary Tseitin.zmod2_natCast Tseitin.zmod2_small Tseitin.gauss Tseitin.odd_cast
  Tseitin.flux_fixed Tseitin.bd1_univ Tseitin.unsat_of_odd
  SD ImpliesL muL SD.impliesL_univ muL_le muL_spec muL_ax muL_inf exists_middleL sensitive_of_boundary cross_any_system
  Tseitin.cross_any_system Tseitin.summary
  nbr uniq unique_neighbors
  Sat lits_restrict' eq_or_eq_nl_of_fst_eq sat_of_restrict sub_insert_of' TL.lift complete_zero complete_aux complete
  refutable_iff"
tmp=$(mktemp --suffix=.lean)
{
  echo "import ProofPhase.Proof.Crossing"
  echo "import ProofPhase.Proof.Complete"
  for t in $names; do echo "#print axioms ProofPhase.Proof.$t"; done
} > "$tmp"
echo "== axioms ($(echo $names | wc -w) declarations)"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Proof/*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Proof"
