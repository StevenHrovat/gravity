#!/usr/bin/env bash
# GRH one-box certificate: build ProofPhase.GRH.OneBoxCert, run #print axioms on every theorem (names read from the
# source), and grep for sorry / admit / native_decide / axiom. Run inside the WSL replay distro from the repository
# root as seen from WSL:
#   bash docs/unified/grhonebox-axioms.sh > docs/unified/grhonebox-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.GRH.OneBoxCert"
bash sync-build.sh ProofPhase.GRH.OneBoxCert 2>&1 | grep -E "GRH/OneBoxCert.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsOneBox.XXXXXX.lean)
{
  echo "import ProofPhase.GRH.OneBoxCert"
  grep -oE "^(theorem|structure) [A-Za-z_][A-Za-z0-9_'.]*" ProofPhase/GRH/OneBoxCert.lean | awk '{print $2}' |
    while read -r n; do echo "#print axioms ProofPhase.GRH.$n"; done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/GRH/OneBoxCert.lean ||
  echo "no sorry / admit / native_decide / axiom in ProofPhase/GRH/OneBoxCert.lean"
