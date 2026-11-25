#!/usr/bin/env bash
# os-windowed: build the three windowed OS modules in ~/formal-os, print the axioms of every declaration, grep for
# sorry / native_decide / axiom declarations.
#   wsl -d ym-replay -u ym -- bash -l /mnt/c/claude/gravity-ym/docs/mass-gap/weak-coupling/proof-phase/os-windowed/axioms.sh
# Needs ~/formal-os with a Mathlib .lake (mkdir -p ~/formal-os && cp -a ~/formal/.lake ~/formal-os/); delete it afterwards.
set -uo pipefail
cd /mnt/c/claude/gravity-ym/docs/mass-gap/formal
FORMAL_DST=~/formal-os bash sync-build.sh ProofPhase.OS.GapLoc 2>&1 | tail -1
cd ~/formal-os
source ~/.elan/env
{
  echo "import ProofPhase.OS.GapLoc"
  for t in WinRP.Adm.sub WinRP.Adm.mono WinRP.Adm.mem WinRP.cs WinRP.abs_le_sqrt WinRP.pow_symm WinRP.pow_add_apply \
           WinRP.hankel WinRP.H_two_mul WinRP.hankel_cs WinRP.H_zero WinRP.win_decay WinRP.win_contraction \
           WinRP.Q_approx_le WinRP.win_gap_approx \
           bObs mkObs integrable_obs_comp torusQ torusQ_apply shiftObs shiftObs_pow_coe posObs torusQ_symm \
           torusQ_τ_symm torusWin torusWin_Q torusWin_pow_coe admissible_of_slab abs_torusQ_le centred centred_coe H_centred \
           torus_gap_approx measurePreserving_thetaConn_gauge approx_le_of_UVTV \
           WinApprox timeSlab_mono level_gap WinBlockGap massGapLoc_of_winBlockGap UVTVApprox UVTVApprox.toWinApprox \
           UVTVBlockGap winBlockGap_of_UVTVBlockGap massGapLoc_of_UVTVBlockGap; do
    echo "#print axioms ProofPhase.OS.$t"
  done
} > ~/formal-os/AxiomsOS.lean
lake env lean ~/formal-os/AxiomsOS.lean
echo "--- grep (sorry / native_decide / axiom declarations):"
grep -nE "\bsorry\b|native_decide|^axiom|^\s*axiom " ProofPhase/OS/*.lean || echo "none"
