#!/usr/bin/env bash
# P vs NP, proof systems: build the four Lean modules of ProofPhase/Proof, run #print axioms on every declaration, then
# grep the sources for sorry / admit / native_decide / axiom. Run inside the WSL replay distro (Lean 4.34.0, Mathlib
# v4.34.0), from the repository root as seen from WSL:
#   bash docs/pnp/axioms-proof.sh > docs/pnp/axioms-proof.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-proof; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-proof}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
mods="Resolution SizeWidth Cut Tseitin"
for m in $mods; do
  echo "== build ProofPhase.Proof.$m"
  bash sync-build.sh ProofPhase.Proof.$m 2>&1 | grep -E "warning|error|Build completed" || true
done
cd "$FORMAL_DST"
source ~/.elan/env
names="nl nl_nl nl_ne ne_nl Clause CNF Falsifies falsifies_empty falsifies_res TL lits subset_lits TL.pos
  TL.subset_lits' TL.exists_falsified TL.unsat flux flux_empty flux_res TL.flux_le TL.card_le fullClause
  falsifies_fullClause fullCNF flux_fullClause fullCNF_leaves restrict mem_restrict lits_restrict card_restrict_le
  sub_erase_of TL.restrict
  WD WD.card_le WD.exists_falsified WD.mono WD.trans WD.sub_insert_of WD.lift WD.combine tl_width_aux tl_width
  tl_size_gt
  SatB Implies allAx mu flip implies_res WD.implies_univ mu_le mu_spec mu_ax mu_res mu_empty exists_middle
  mem_of_boundary width_ge tl_size_ge
  Tseitin.odd Tseitin.patClause Tseitin.block Tseitin.falsifies_patClause Tseitin.satB_block_iff Tseitin.toggle
  Tseitin.invisible Tseitin.boundary Tseitin.width_ge Tseitin.tl_size_ge"
tmp=$(mktemp --suffix=.lean)
{
  for m in $mods; do echo "import ProofPhase.Proof.$m"; done
  for t in $names; do echo "#print axioms ProofPhase.Proof.$t"; done
} > "$tmp"
echo "== axioms ($(echo $names | wc -w) declarations)"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/Proof/*.lean || echo "no sorry / admit / native_decide / axiom in ProofPhase/Proof"
