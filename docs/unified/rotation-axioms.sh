#!/usr/bin/env bash
# The rotation round: build ProofPhase.ETM.ETM (it imports Rotation and RotationInstances), run #print axioms on every
# declaration of ProofPhase/ETM/Rotation*.lean (names read from the sources, with the namespace prefixes tracked through
# `namespace` / `section` / `end`), and grep for sorry / admit / native_decide / axiom. Run inside the WSL replay distro
# from the repository root as seen from WSL:
#   bash docs/unified/rotation-axioms.sh > docs/unified/rotation-axioms.log 2>&1
# Build folder: $FORMAL_DST (default ~/formal-rot; seed it with a copy of a built .lake to avoid a Mathlib rebuild).
set -u
export FORMAL_DST=${FORMAL_DST:-~/formal-rot}
src="$(cd "$(dirname "$0")/../mass-gap/formal" && pwd)"
cd "$src"
echo "== build ProofPhase.ETM.ETM"
bash sync-build.sh ProofPhase.ETM.ETM 2>&1 | grep -E "ETM/Rotation.*(warning|error)|^error|Build completed" || true
cd "$FORMAL_DST"
source ~/.elan/env
tmp=$(mktemp /tmp/AxiomsRot.XXXXXX.lean)
{
  echo "import ProofPhase.ETM.ETM"
  for f in Rotation RotationInstances; do
    awk '
      /^namespace / { n++; kind[n] = "ns"; name[n] = $2; next }
      /^section/    { n++; kind[n] = "sec"; name[n] = ""; next }
      /^end( |$)/   { if (n > 0) n--; next }
      /^(noncomputable )?(theorem|def|structure|abbrev|instance|inductive) [A-Za-z_]/ {
        d = ($1 == "noncomputable") ? $3 : $2; sub(/[^A-Za-z0-9_.'"'"'].*$/, "", d)
        p = ""; for (i = 1; i <= n; i++) if (kind[i] == "ns") p = p name[i] "."
        print p d }' "ProofPhase/ETM/$f.lean" | while read -r d; do echo "#print axioms $d"; done
  done
} > "$tmp"
echo "== declarations: $(grep -c '#print' "$tmp")"
echo "== axioms"
lake env lean "$tmp"
rm -f "$tmp"
echo "== source grep"
grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" ProofPhase/ETM/Rotation*.lean ||
  echo "no sorry / admit / native_decide / axiom in ProofPhase/ETM/Rotation*.lean"
