#!/usr/bin/env bash
# r4-layer: build all five modules in ~/formal-att-r4-2, print axioms of the headline theorems, scan for sorry/axiom/native_decide.
# Run: wsl -d ym-replay -u ym -- bash /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/attempts/r4-layer/axioms.sh
set -u
DST="$HOME/formal-att-r4-2"
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST="$DST" bash sync-build.sh Attempts.R4.LayerDecimation > "$DST/build_all.log" 2>&1 || true
# sync-build copies the sources and builds one target; build all five explicitly
cd "$DST" && source ~/.elan/env
lake build Attempts.R4.LayerSector Attempts.R4.LayerKernel Attempts.R4.LayerTransport Attempts.R4.LayerDecimation Attempts.R4.LayerTwisted 2>&1 | grep -E "error|warning: Attempts/R4/Layer|Build completed|failed"
cat > "$DST/r4l_axioms.lean" <<'EOL'
import Attempts.R4.LayerDecimation
import Attempts.R4.LayerTwisted
open Attempts.R4.Layer
#print axioms cs_int
#print axioms top_parity
#print axioms flux_bound_of_vacuum_bound
#print axioms lamFlux_le_lamVac
#print axioms fluxEnergy_nonneg
#print axioms lamFlux_eq
#print axioms sector_decay
#print axioms flux_correlator_decay
#print axioms twist_centre_transform
#print axioms Ztw_nonneg
#print axioms two_mul_Zper_sub_Ztw
#print axioms Zflux_nonneg
#print axioms Zflux_le_Zvac
#print axioms Zvac_nonneg
#print axioms freeFlux_nonneg
#print axioms freeFlux_eq_dual
#print axioms dual_selfDual
#print axioms pow_sigma
#print axioms wilsonKernel_symm
#print axioms wilsonKernel_le
#print axioms measurable_wilsonKernel
#print axioms plaquetteHolonomy_centreFlip
#print axioms wilsonKernel_centreFlip
#print axioms wilson_fluxEnergy_nonneg
#print axioms wilson_flux_correlator_decay
#print axioms su2_fluxEnergy_nonneg
#print axioms su2_flux_correlator_decay
#print axioms lift_charged
#print axioms map_centre_invariant
#print axioms correlator_conserved
#print axioms sector_partition_conserved
#print axioms act_conserved_per_layer
#print axioms lift_mem_sec
#print axioms blocked_flux_decay
#print axioms coarseForm_eq
#print axioms layer_rp
#print axioms straddle_fine_rp
#print axioms straddle_breaks_rp
#print axioms dbl_add
#print axioms decimate_gauge
#print axioms decimate_centreFlip
#print axioms decimate_thetaConn
#print axioms linkDep_decimate
#print axioms decimated_wilson_rp
#print axioms decimated_wilson_rp_SU2
#print axioms su2_decimated_flux_decay
#print axioms twKernel_centreFlip
#print axioms twisted_fluxEnergy_nonneg
#print axioms su2_twisted_fluxEnergy_nonneg
#print axioms su2_twisted_flux_correlator_decay
#print axioms un_fluxEnergy_nonneg
EOL
lake env lean "$DST/r4l_axioms.lean" 2>&1 | grep "depends on axioms" | sed "s/.*depends on axioms: //" | sort | uniq -c
lake env lean "$DST/r4l_axioms.lean" 2>&1 | grep -c "depends on axioms"
rm -f "$DST/r4l_axioms.lean"
grep -n "sorry\|native_decide\|^axiom" Attempts/R4/Layer*.lean || echo "no sorry/native_decide/axiom in Attempts/R4/Layer*.lean"
