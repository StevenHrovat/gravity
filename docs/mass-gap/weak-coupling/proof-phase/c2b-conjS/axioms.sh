#!/usr/bin/env bash
# Build all ProofPhase.SectorS modules in ~/formal-c2b, grep for sorry/native_decide/axiom, print the axioms of the headline theorems.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2b-conjS/axioms.sh
set -euo pipefail
here=/mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c2b-conjS
for m in GeneratorRate Loops Mixture ConjS; do bash $here/build.sh ProofPhase.SectorS.$m | tail -1; done
cd ~/formal-c2b
echo "--- grep (sorry / native_decide / axiom declarations):"
grep -nE "\bsorry\b|native_decide|^axiom|^\s*axiom " ProofPhase/SectorS/*.lean || echo "none"
cat > /tmp/c2b_axioms.lean <<'LEAN'
import ProofPhase.SectorS.GeneratorRate
import ProofPhase.SectorS.Loops
import ProofPhase.SectorS.Mixture
import ProofPhase.SectorS.ConjS
open ProofPhase.SectorS
#print axioms le_of_doubling
#print axioms norm_pow_le_of_decay
#print axioms norm_pow_le_of_generators
#print axioms inner_pow_le_of_generators
#print axioms generators_of_uniform
#print axioms su2_mandelstam
#print axioms wilsonLoop_mul
#print axioms wilsonLoop_double
#print axioms wilsonLoop_lasso
#print axioms mul_mem_loopSpan
#print axioms loopAlgebra
#print axioms gauge_of_mem_loopAlgebra
#print axioms mem_loopSet_of_lasso
#print axioms abs_integral_mix_le
#print axioms integral_mix_nonneg
#print axioms cov_mix
#print axioms tendsto_cov_mix
#print axioms not_expDecay_mix
#print axioms abs_rectW_le
#print axioms areaLaw_iff_large
#print axioms conjectureS_of_slabDecay
#print axioms conjectureS_of_massGap
LEAN
source ~/.elan/env
lake env lean /tmp/c2b_axioms.lean
