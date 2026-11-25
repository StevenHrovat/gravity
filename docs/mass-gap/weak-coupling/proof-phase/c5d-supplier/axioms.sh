#!/usr/bin/env bash
# c5d-supplier: #print axioms on the headline theorems (run after build.sh ProofPhase.Defects.Annealed and
# build.sh ProofPhase.Defects.Supplier), then grep for sorry / native_decide / axiom in Defects.
#   wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/c5d-supplier/axioms.sh
cd ~/formal-c5d
source ~/.elan/env
{
  echo "import ProofPhase.Defects.Annealed"
  echo "import ProofPhase.Defects.Supplier"
  for t in effDist_le_add effWeight_le_mul walkCost_bypass_le expect_prod_le sum_card_walks_le expect_effWeight_le \
           expect_effWeight_le_geom quenched_defect_W annealed_of_quenched defect_decay_W mixture_cov_eq \
           mixture_counterexample exists_sep_subset measure_biInter_le_pow sum_badLaw_cyl cylinder_of_condBound \
           uvRepDefect_cylinder; do
    echo "#print axioms ProofPhase.Defects.$t"
  done
} > /tmp/AxiomsC5d.lean
lake env lean /tmp/AxiomsC5d.lean
grep -n "sorry\|native_decide\|^axiom" ProofPhase/Defects/*.lean || echo "no sorry / native_decide / axiom in ProofPhase/Defects"
