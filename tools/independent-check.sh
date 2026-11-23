#!/usr/bin/env bash
# Independent re-check of every Lean proof in docs/mass-gap/formal (see docs/unified/INDEPENDENT-CHECK.md).
#
#   bash tools/independent-check.sh <stage>
#
# Two modes.
#   FULL (once per toolchain/Mathlib pin/checker version; hours; its result is the stamp docs/unified/independent-check.stamp):
#       setup, build, axioms, replay-all, export, nanoda, base-record
#   QUICK (every later run; minutes if little changed): the cached full result is the trusted base for Mathlib and Lean core.
#       quick   = build, axioms, replay-inc, export-project, nanoda-project
#                 (refuses to run until a matching full result is cached; `quick-force` ignores that)
#
# Stages, each logging to $LOGDIR:
#   setup           install the checkers (git, curl, a C compiler needed; installs rustup under ~ if cargo is missing)
#   build           copy the sources into $FC and build every module of every library
#   axioms          axiom audit with an own traversal of the environment + grep for sorry/admit/native_decide/axiom
#   replay          leanchecker per library (all modules of a library in parallel: needs ~16+ GB RAM for big ones)
#   replay-inc      incremental leanchecker: only modules whose source or project imports changed since the last pass,
#                   in small batches (RAM-friendly); the key is a hash of source + imports' keys + toolchain + Mathlib pin
#   replay-all      leanchecker --fresh over the whole environment (project + Mathlib + Lean core), one process
#   export          lean4export of the whole environment to $CHK/export/all.ndjson (about 6 GB)
#   nanoda          nanoda_lib (Rust kernel, independent code) over the full export
#   export-project  lean4export of only the declarations of changed (or all with ALL=1) project modules + what they use
#   nanoda-project  nanoda_lib over that export
#   perlib          nanoda over each library separately (declarations of that library + what they use), with counts and times
#   base-record     after a passing full run, write the stamp docs/unified/independent-check.stamp (Mathlib commit, toolchain, olean-set hash, checkers, result, date)
#   base-hash       print the olean-set hash of Mathlib + Lean core (what the stamp is matched against)
#   lean4lean       lean4lean (Lean kernel written in Lean) over the project libraries
#
# Run inside the Linux/WSL shell with elan installed. Long stages take minutes to hours: run them in the background and
# read the log, e.g.  nohup bash tools/independent-check.sh nanoda > ~/check-logs/nanoda.out 2>&1 &
# Run ONE heavy stage at a time (several leanchecker/nanoda runs at once get OOM-killed, exit 137).
# Work dir $FC is a *copy* of the build project, so other builds in ~/formal are not disturbed.
set -uo pipefail
REPO=${REPO:-/mnt/c/claude/gravity-ym}   # the repository checkout (the Windows path as seen from WSL)
SRC=$REPO/docs/mass-gap/formal
FC=${FORMAL_CHECK:-$HOME/formal-check}
CHK=${CHECKERS:-$HOME/checkers}
LOGDIR=${LOGDIR:-$HOME/check-logs}
LIBS="AreaLaw Influence Positivity OneScale Attempts ProofPhase"
L4LEAN_COMMIT=${L4LEAN_COMMIT:-0048ed7}   # lean4lean: "bump Lean toolchain to v4.34.0"
L4EXPORT_TAG=${L4EXPORT_TAG:-v4.34.0}     # lean4export tag matching the toolchain
mkdir -p "$LOGDIR" "$CHK"
[ -f ~/.elan/env ] && source ~/.elan/env
[ -f ~/.cargo/env ] && source ~/.cargo/env

CACHE=${CHECK_CACHE:-$HOME/check-cache}   # results that later runs may trust (see base-record, replay-inc)
BATCH=${BATCH:-1}                          # modules per leanchecker process in replay-inc. Every process loads the whole environment (~6 GB, 4-5 s) whatever the module, so 1 is the safe default
mkdir -p "$CACHE"

modules_of() { ( cd "$FC"; find $1 -name '*.lean' | sed 's/\.lean$//; s#/#.#g'; [ -f $1.lean ] && echo $1 ) | sort -u; }
modules() { for l in $LIBS; do modules_of $l; done; }
# modules to replay: the library root files (AreaLaw, Influence, Positivity, OneScale) hold only imports + a docstring, and the checkers
# treat a module name as a prefix (replaying ALL submodules at once, 20+ GB), so they are left out
check_modules() { modules | grep -vxE "AreaLaw|Influence|Positivity|OneScale"; }
is_proj() { case "$1" in AreaLaw*|Influence*|Positivity*|OneScale*|Attempts*|ProofPhase*) return 0;; esac; return 1; }
declare -A KEY
# Key of a module = hash of its source + the keys of the project modules it imports + toolchain + Mathlib pin.
# A module whose key was recorded as passed is not re-checked.
modkey() {
  local m=$1; [ -n "${KEY[$m]:-}" ] && return 0
  local f="$FC/$(echo "$m" | tr . /).lean" h i
  h=$( { sha256sum < "$f"; cat "$FC/lean-toolchain" "$FC/lake-manifest.json"; } | sha256sum | cut -c1-16)
  for i in $(grep -E '^(public )?import ' "$f" | sed -E 's/^(public )?import +//; s/[ \r].*//' | tr -d '\r'); do
    if is_proj "$i"; then modkey "$i"; h="$h${KEY[$i]}"; fi
  done
  KEY[$m]=$(echo "$h" | sha256sum | cut -c1-16)
}
timed() { local s=$(date +%s); "$@"; local rc=$?; echo "rc=$rc time=$(( $(date +%s)-s ))s"; return $rc; }

stage_setup() {
  cd "$CHK"
  command -v cargo >/dev/null || { curl -sSf https://sh.rustup.rs -o rustup-init.sh && sh rustup-init.sh -y --profile minimal; source ~/.cargo/env; }
  [ -d lean4export ] || git clone -q https://github.com/leanprover/lean4export.git
  [ -d nanoda_lib ]  || git clone -q https://github.com/ammkrn/nanoda_lib.git
  [ -d lean4lean ]   || git clone -q https://github.com/digama0/lean4lean.git
  (cd lean4export && git checkout -q $L4EXPORT_TAG && lake build 2>&1 | tail -1)
  (cd nanoda_lib && git log -1 --format='nanoda_lib %h %cd' && cargo build --release 2>&1 | tail -1)
  (cd lean4lean && git checkout -q $L4LEAN_COMMIT && lake build lean4lean 2>&1 | tail -1)
}

stage_build() {
  mkdir -p "$FC"; cd "$SRC"
  for f in lean-toolchain lakefile.toml $(ls *.lean) $(find $LIBS -name '*.lean'); do
    mkdir -p "$FC/$(dirname "$f")"; tr -d '\r' < "$f" > "$FC/$f"
  done
  cd "$FC"
  for f in $(find $LIBS -name '*.lean'); do [ -f "$SRC/$f" ] || { echo "stale: $f"; rm "$f"; }; done
  [ -d .lake/packages/mathlib ] || { lake update && lake exe cache get; }
  # Attempts and ProofPhase have no root module file, so every module is named explicitly.
  for l in $LIBS; do
    s=$(date +%s); lake build $(modules_of $l) > "$LOGDIR/build-$l.log" 2>&1; rc=$?
    echo "BUILD $l rc=$rc modules=$(modules_of $l | wc -l) time=$(( $(date +%s)-s ))s $(tail -1 "$LOGDIR/build-$l.log")"
  done
  # CheckAll imports every project module: one root for whole-environment checks (lives only in $FC, not in the repo)
  for l in $LIBS; do modules_of $l; done | sed 's/^/import /' > CheckAll.lean
  mkdir -p .lake/build/lib/lean
  lake env lean -o .lake/build/lib/lean/CheckAll.olean CheckAll.lean && echo "CheckAll: $(wc -l < CheckAll.lean) modules"
}

stage_axioms() {
  cd "$FC"
  cat > AxiomAudit.lean <<'LEAN'
import CheckAll
open Lean

/-! Independent axiom audit: an own traversal of the environment (it does not use the axiom cache that
    Lean stores in .olean files). Visits every constant reachable from any declaration of the project
    libraries, including Lean/Mathlib dependencies, and records every axiom met. -/

def libs : List String := ["AreaLaw", "Influence", "Positivity", "OneScale", "Attempts", "ProofPhase"]
def stdAx : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def deps (ci : ConstantInfo) : Array Name :=
  let t := ci.type.getUsedConstants
  match ci with
  | .defnInfo v   => t ++ v.value.getUsedConstants
  | .thmInfo v    => t ++ v.value.getUsedConstants
  | .opaqueInfo v => t ++ v.value.getUsedConstants
  | .inductInfo v => t ++ v.ctors.toArray
  | _ => t

partial def go (env : Environment) (todo : Array Name) (seen : NameSet) (axs : NameSet) (missing : Array Name) :
    NameSet × NameSet × Array Name :=
  match todo.back? with
  | none => (seen, axs, missing)
  | some n =>
    let todo := todo.pop
    if seen.contains n then go env todo seen axs missing
    else
      let seen := seen.insert n
      match env.find? n with
      | none => go env todo seen axs (missing.push n)
      | some ci =>
        let axs := match ci with | .axiomInfo _ => axs.insert n | _ => axs
        go env (todo ++ deps ci) seen axs missing

#eval show CoreM Unit from do
  let env ← getEnv
  -- optional: only the modules listed (one per line) in the file named by $CHECK_MODS (incremental runs)
  let only : Option (List Name) ← do
    match (← IO.getEnv "CHECK_MODS") with
    | some p => pure (some (((← IO.FS.readFile p).splitOn "\n").filter (· ≠ "") |>.map String.toName))
    | none => pure none
  let mut names : Array Name := #[]
  let mut thms : Nat := 0
  let mut counts : Array (String × Nat × Nat) := libs.toArray.map (·, 0, 0)
  for (nm, ci) in env.constants.map₁.toList do
    match env.getModuleIdxFor? nm with
    | some idx =>
      let root := (env.header.moduleNames[idx.toNat]!).getRoot.toString
      let modOk := only.isNone || (only.getD []).contains env.header.moduleNames[idx.toNat]!
      if libs.contains root && modOk then
        names := names.push nm
        let isT := ci.isTheorem
        if isT then thms := thms + 1
        counts := counts.map fun (l, a, b) => if l == root then (l, a + 1, if isT then b + 1 else b) else (l, a, b)
    | none => pure ()
  let (seen, axs, missing) := go env names {} {} #[]
  IO.println s!"DECLS {names.size} THEOREMS {thms}"
  for (l, a, b) in counts do IO.println s!"LIB {l} decls {a} theorems {b}"
  IO.println s!"REACHABLE_CONSTANTS {seen.size} (incl. Lean/Mathlib dependencies)"
  IO.println s!"MISSING {missing.size}"
  IO.println s!"AXIOMS_USED {axs.toList}"
  let bad := axs.toList.filter (fun a => !stdAx.contains a)
  IO.println s!"NONSTD_AXIOMS {bad}"
  if !bad.isEmpty then
    for nm in names do
      let (_, a, _) := go env #[nm] {} {} #[]
      if a.toList.any (fun x => !stdAx.contains x) then IO.println s!"NONSTD {nm} {a.toList}"
LEAN
  # incremental (quick): restrict to the changed modules via CHECK_MODS; a plain run audits everything
  timed lake env lean AxiomAudit.lean 2>&1 | tee "$LOGDIR/axioms.log"
  echo "--- forbidden tokens in the sources (comments excluded):"
  cd "$SRC"
  find $LIBS -name '*.lean' -print0 | xargs -0 grep -nE '\bsorry\b|\badmit\b|native_decide|^\s*axiom\b|\bunsafe\b|\bimplemented_by\b|\bextern\b' \
    | grep -vE '^[^:]*:[0-9]+:\s*(--|/-)' | tee "$LOGDIR/grep.log"
  echo "grep hits: $(wc -l < "$LOGDIR/grep.log")"
}

stage_replay() {   # leanchecker per library (module-name prefix): replays each module's own declarations
  cd "$FC"
  for l in $LIBS; do
    s=$(date +%s); lake env leanchecker $l > "$LOGDIR/replay-$l.log" 2>&1; rc=$?
    echo "REPLAY $l rc=$rc time=$(( $(date +%s)-s ))s :: $(tail -1 "$LOGDIR/replay-$l.log")" | tee -a "$LOGDIR/replay.log"
  done
}

stage_replay_all() {   # replays every declaration of the whole environment into a fresh one
  cd "$FC"
  s=$(date +%s); lake env leanchecker --fresh CheckAll > "$LOGDIR/replay-all.log" 2>&1; rc=$?
  echo "REPLAY-ALL rc=$rc time=$(( $(date +%s)-s ))s :: $(tail -1 "$LOGDIR/replay-all.log")" | tee -a "$LOGDIR/replay.log"
  [ $rc -eq 0 ] && stage_replay_seed
  return $rc
}
# A passing whole-environment replay covers every project module: record their keys as passed for replay-inc.
stage_replay_seed() {
  local m n=0; : > "$CACHE/replay-passed.txt"
  for m in $(check_modules); do modkey "$m"; echo "${KEY[$m]} $m" >> "$CACHE/replay-passed.txt"; n=$((n+1)); done
  echo "REPLAY-SEED recorded $n modules as passed" | tee -a "$LOGDIR/replay.log"
}

stage_export() {
  cd "$FC"; mkdir -p "$CHK/export"
  s=$(date +%s)
  lake env "$CHK/lean4export/.lake/build/bin/lean4export" CheckAll > "$CHK/export/all.ndjson" 2> "$LOGDIR/export.err"
  echo "EXPORT rc=$? time=$(( $(date +%s)-s ))s size=$(du -h "$CHK/export/all.ndjson" | cut -f1) lines=$(wc -l < "$CHK/export/all.ndjson")" | tee -a "$LOGDIR/nanoda.log"
}

# run nanoda_lib over one export file; $1 = export file, $2 = tag for log/config names
nanoda_run() {
  local exp=$1 tag=$2 s rc
  cat > "$CHK/nanoda-$tag.json" <<JSON
{
  "export_file_path": "$exp",
  "use_stdin": false,
  "num_threads": 8,
  "stack_size_bytes": 1073741824,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"],
  "unpermitted_axiom_hard_error": false,
  "nat_extension": true,
  "string_extension": true,
  "print_success_message": true
}
JSON
  # Axioms: only the three standard ones (plus Lean.trustCompiler, which Lean core's own reduceBool/reduceNat
  # declarations mention). Lean.ofReduceBool and any other axiom are skipped, so a declaration that used one fails.
  s=$(date +%s)
  /usr/bin/time -v "$CHK/nanoda_lib/target/release/nanoda_bin" "$CHK/nanoda-$tag.json" > "$LOGDIR/nanoda-$tag.log" 2> "$LOGDIR/nanoda-$tag.time"; rc=$?
  echo "NANODA-$tag rc=$rc time=$(( $(date +%s)-s ))s peakRSS=$(grep 'Maximum resident' "$LOGDIR/nanoda-$tag.time" | awk '{print int($6/1024)}')MB :: $(tail -2 "$LOGDIR/nanoda-$tag.log" | tr '\n' ' ')" | tee -a "$LOGDIR/nanoda.log"
  return $rc
}
stage_nanoda() { nanoda_run "$CHK/export/all.ndjson" all; }

# Declaration names of the project modules to export: all of them (ALL=1 or nothing cached) or only the changed ones.
stage_export_project() {
  cd "$FC"; mkdir -p "$CHK/export"
  if [ "${ALL:-0}" = 1 ] || [ ! -f "$CACHE/changed-modules.txt" ]; then modules > "$CACHE/changed-modules.txt"; fi
  if [ ! -s "$CACHE/changed-modules.txt" ]; then rm -f "$CHK/export/project.ndjson"; echo "EXPORT-PROJECT nothing changed: skipped" | tee -a "$LOGDIR/nanoda.log"; return 0; fi
  cat > NamesOf.lean <<'LEAN'
import CheckAll
open Lean
/-! Writes the names of all (non-internal) declarations of the modules listed in $CHECK_MODS to $CHECK_NAMES. -/
#eval show CoreM Unit from do
  let env ← getEnv
  let some mf ← IO.getEnv "CHECK_MODS" | throwError "CHECK_MODS not set"
  let some out ← IO.getEnv "CHECK_NAMES" | throwError "CHECK_NAMES not set"
  let mods := ((← IO.FS.readFile mf).splitOn "\n").filter (· ≠ "") |>.map String.toName
  let mut acc : Array String := #[]
  for (nm, _) in env.constants.map₁.toList do
    if nm.isInternal then continue
    if let some idx := env.getModuleIdxFor? nm then
      if mods.contains env.header.moduleNames[idx.toNat]! then acc := acc.push nm.toString
  IO.FS.writeFile out ("\n".intercalate acc.toList)
  IO.println s!"NAMES {acc.size} from {mods.length} modules"
LEAN
  CHECK_MODS="$CACHE/changed-modules.txt" CHECK_NAMES="$CACHE/names.txt" lake env lean NamesOf.lean || return 1
  s=$(date +%s)
  # shellcheck disable=SC2046
  lake env "$CHK/lean4export/.lake/build/bin/lean4export" CheckAll -- $(tr '\n' ' ' < "$CACHE/names.txt") > "$CHK/export/project.ndjson" 2> "$LOGDIR/export-project.err"
  echo "EXPORT-PROJECT rc=$? time=$(( $(date +%s)-s ))s size=$(du -h "$CHK/export/project.ndjson" | cut -f1) lines=$(wc -l < "$CHK/export/project.ndjson")" | tee -a "$LOGDIR/nanoda.log"
}
stage_nanoda_project() { [ -f "$CHK/export/project.ndjson" ] || { echo "NANODA-project nothing to check: skipped" | tee -a "$LOGDIR/nanoda.log"; return 0; }; nanoda_run "$CHK/export/project.ndjson" project; }

# Per-library independent check (nanoda over each library's declarations + everything they use): shows how cost follows size.
stage_perlib() {
  local l s
  for l in $LIBS; do
    modules_of $l > "$CACHE/changed-modules.txt"
    stage_export_project >/dev/null || return 1
    s=$(date +%s)
    nanoda_run "$CHK/export/project.ndjson" "lib-$l" > /dev/null
    echo "PERLIB $l modules=$(wc -l < "$CACHE/changed-modules.txt") names=$(wc -l < "$CACHE/names.txt") $(grep -E 'Checked [0-9]+ declarations' "$LOGDIR/nanoda-lib-$l.log" | sed 's/ with no.*//') nanoda_time=$(( $(date +%s)-s ))s" | tee -a "$LOGDIR/perlib.log"
  done
}

# ---- The trusted base: a stamp in the repo -------------------------------------------------------------------
# After ONE full independent check passes (replay-all + nanoda over the whole environment), `base-record` writes
# $STAMP: the Mathlib commit, the Lean toolchain, a hash of every non-project .olean in the import closure
# (Mathlib, Batteries, Lean core ...), the checkers' versions, result and date. Later runs recompute the hash; on a
# match Mathlib/Lean core are assumed correct and only the project's own declarations are checked. On any mismatch
# `quick` refuses and a new `full` run (and a new stamp) is needed.
STAMP=${STAMP:-$REPO/docs/unified/independent-check.stamp}
mathlib_rev() { grep -B8 '"name": "mathlib"' "$FC/lake-manifest.json" | grep '"rev"' | head -1 | sed 's/.*: *"\(.*\)".*/\1/'; }
# hash of the compiled non-project environment: sorted "module sha256(olean)" lines, hashed again
base_hash() {
  cd "$FC"
  cat > OleanList.lean <<'LEAN'
import CheckAll
open Lean
#eval show CoreM Unit from do
  let env ← getEnv
  let some out ← IO.getEnv "CHECK_OLEANS" | throwError "CHECK_OLEANS not set"
  let libs := ["AreaLaw", "Influence", "Positivity", "OneScale", "Attempts", "ProofPhase", "CheckAll"]
  let mut lines : Array String := #[]
  for m in env.header.moduleNames do
    if libs.contains m.getRoot.toString then continue
    lines := lines.push s!"{m} {← findOLean m}"
  IO.FS.writeFile out ("\n".intercalate lines.toList)
LEAN
  CHECK_OLEANS="$CACHE/oleans.txt" lake env lean OleanList.lean || return 1
  sort "$CACHE/oleans.txt" | while read -r m p; do echo "$m $(sha256sum < "$p" | cut -d' ' -f1)"; done > "$CACHE/olean-hashes.txt"
  echo "$(wc -l < "$CACHE/olean-hashes.txt") $(sha256sum < "$CACHE/olean-hashes.txt" | cut -d' ' -f1)"
}
stage_base_hash() { s=$(date +%s); echo "BASE-HASH modules_hash=$(base_hash) time=$(( $(date +%s)-s ))s" | tee -a "$LOGDIR/nanoda.log"; }
stage_base_record() {
  grep -q "^NANODA-all rc=0" "$LOGDIR/nanoda.log" || { echo "no passing full nanoda run in $LOGDIR/nanoda.log"; return 1; }
  grep -q "^REPLAY-ALL rc=0" "$LOGDIR/replay.log" || { echo "no passing replay-all in $LOGDIR/replay.log"; return 1; }
  local h; h=$(base_hash) || return 1
  {
    echo "# Trusted base for tools/independent-check.sh (see docs/unified/INDEPENDENT-CHECK.md). Written by 'base-record'."
    echo "result=PASS"
    echo "date=$(date -u +%F)"
    echo "lean_toolchain=$(cat "$FC/lean-toolchain")"
    echo "mathlib_rev=$(mathlib_rev)"
    echo "olean_modules=${h% *}"
    echo "olean_set_sha256=${h#* }"
    echo "export_sha256=$(sha256sum "$CHK/export/all.ndjson" | cut -d' ' -f1)   # lean4export of project + Mathlib closure at check time"
    echo "checker_leanchecker=Lean toolchain's own leanchecker ($(cat "$FC/lean-toolchain")), --fresh over the whole environment"
    echo "checker_nanoda_lib=$(git -C "$CHK/nanoda_lib" rev-parse --short=12 HEAD) ($(git -C "$CHK/nanoda_lib" log -1 --format=%cs))"
    echo "checker_lean4export=$(git -C "$CHK/lean4export" describe --tags --always)"
  } > "$STAMP"
  cat "$STAMP"
}
# does the stamp match what is on disk now?
base_ok() {
  [ -f "$STAMP" ] || { echo "no stamp $STAMP"; return 1; }
  grep -q '^result=PASS' "$STAMP" || return 1
  [ "$(grep '^lean_toolchain=' "$STAMP" | cut -d= -f2)" = "$(cat "$FC/lean-toolchain")" ] || { echo "stamp: toolchain differs"; return 1; }
  [ "$(grep '^mathlib_rev=' "$STAMP" | cut -d= -f2)" = "$(mathlib_rev)" ] || { echo "stamp: Mathlib commit differs"; return 1; }
  local h; h=$(base_hash) || return 1
  [ "$(grep '^olean_set_sha256=' "$STAMP" | cut -d= -f2)" = "${h#* }" ] || { echo "stamp: olean hash differs"; return 1; }
  echo "stamp matches (Mathlib $(mathlib_rev | cut -c1-12), ${h% *} non-project modules, hash ${h#* })"
}

# Incremental replay: re-check (with leanchecker, small batches) only modules whose key is not recorded as passed.
stage_replay_inc() {
  cd "$FC"; touch "$CACHE/replay-passed.txt"
  local todo=() total=0 m
  for m in $(check_modules); do
    modkey "$m"; total=$((total+1))
    grep -q "^${KEY[$m]} $m\$" "$CACHE/replay-passed.txt" || todo+=("$m")
  done
  : > "$CACHE/changed-modules.txt"
  [ ${#todo[@]} -gt 0 ] && printf '%s\n' "${todo[@]}" > "$CACHE/changed-modules.txt"
  echo "REPLAY-INC modules=$total changed=${#todo[@]}" | tee -a "$LOGDIR/replay.log"
  [ "${DRY:-0}" = 1 ] && return 0   # DRY=1: only report how many modules a change would re-check
  local i=0 s rc batch fail=0
  while [ $i -lt ${#todo[@]} ]; do
    batch=("${todo[@]:$i:$BATCH}"); i=$((i+BATCH)); s=$(date +%s)
    lake env leanchecker "${batch[@]}" > "$LOGDIR/replay-inc.last.log" 2>&1; rc=$?
    echo "REPLAY-INC batch rc=$rc n=${#batch[@]} time=$(( $(date +%s)-s ))s first=${batch[0]}" | tee -a "$LOGDIR/replay.log"
    if [ $rc -eq 0 ]; then for m in "${batch[@]}"; do echo "${KEY[$m]} $m" >> "$CACHE/replay-passed.txt"; done
    else
      for m in "${batch[@]}"; do   # find the failing module(s) one by one
        lake env leanchecker "$m" > "$LOGDIR/replay-inc.last.log" 2>&1 && echo "${KEY[$m]} $m" >> "$CACHE/replay-passed.txt" \
          || { echo "REPLAY-INC FAIL $m: $(tail -3 "$LOGDIR/replay-inc.last.log" | tr '\n' ' ')" | tee -a "$LOGDIR/replay.log"; fail=1; }
      done
    fi
  done
  echo "REPLAY-INC done fail=$fail" | tee -a "$LOGDIR/replay.log"
  return $fail
}

# lean4lean (kernel written in Lean) over every project module, ONE module per process, one process at a time
# (PAR=1 default). Do not pass a library's root name (AreaLaw, Influence, Positivity, OneScale): lean4lean and
# leanchecker treat a module name as a prefix and replay all its submodules at once, which needs 20+ GB. Those four
# root files hold only imports and a docstring (checked below), so there is nothing to replay in them.
stage_lean4lean() {
  cd "$FC"; mkdir -p "$LOGDIR/l4l"; export FC CHK LOGDIR
  local l s=$(date +%s)
  for l in AreaLaw Influence Positivity OneScale; do
    ! grep -qE '^\s*(theorem|lemma|def|instance|structure|class|inductive|abbrev|axiom|opaque|example|namespace)\b' "$FC/$l.lean" \
      || { echo "root module $l holds declarations: replay it with lean4lean --fresh $l"; return 1; }
  done
  check_modules | xargs -P "${PAR:-1}" -I{} bash -c \
    'cd "$FC"; source ~/.elan/env; /usr/bin/time -v lake env "$CHK/lean4lean/.lake/build/bin/lean4lean" {} > "$LOGDIR/l4l/{}.log" 2> "$LOGDIR/l4l/{}.time"; echo "{} $? $(grep "Maximum resident" "$LOGDIR/l4l/{}.time" | awk "{print int(\$6/1024)}")"' \
    > "$LOGDIR/l4l/results.txt"
  local fail n decls
  fail=$(awk '$2!=0' "$LOGDIR/l4l/results.txt"); n=$(wc -l < "$LOGDIR/l4l/results.txt")
  decls=$(cat "$LOGDIR"/l4l/*.log | awk '/^checked [0-9]+ declarations/ {s+=$2} END {print s}')
  echo "LEAN4LEAN modules=$n failed=$(echo -n "$fail" | grep -c .) declarations_checked_sum=$decls peakRSS_max=$(sort -k3 -n "$LOGDIR/l4l/results.txt" | tail -1 | awk '{print $1" "$3"MB"}') time=$(( $(date +%s)-s ))s" | tee -a "$LOGDIR/lean4lean.log"
  [ -z "$fail" ] || echo "$fail" | tee -a "$LOGDIR/lean4lean.log"
}

case "${1:-}" in
  setup) stage_setup;;
  build) stage_build;;
  axioms) stage_axioms;;
  replay) stage_replay;;
  replay-inc) stage_replay_inc;;
  replay-all) stage_replay_all;;
  replay-seed) stage_replay_seed;;
  export) stage_export;;
  nanoda) stage_nanoda;;
  export-project) stage_export_project;;
  nanoda-project) stage_nanoda_project;;
  perlib) stage_perlib;;
  base-record) stage_base_record;;
  base-hash) stage_base_hash;;
  lean4lean) stage_lean4lean;;
  full) stage_setup; stage_build; stage_axioms; stage_replay_all; stage_export; stage_nanoda; stage_base_record;;
  quick|quick-force)
    t0=$(date +%s); lap() { echo "QUICK step '$1' done at +$(( $(date +%s)-t0 ))s" | tee -a "$LOGDIR/nanoda.log"; }
    stage_build >/dev/null 2>&1; lap build
    if [ "$1" = quick ]; then
      out=$(base_ok); rc=$?; echo "$out" | tee -a "$LOGDIR/nanoda.log"; lap "stamp check"
      [ $rc -eq 0 ] || { echo "stamp missing or not matching: run the full check first (or quick-force)"; exit 3; }
    fi
    stage_replay_inc || exit 1; lap "replay of changed modules"
    if [ -s "$CACHE/changed-modules.txt" ]; then
      CHECK_MODS="$CACHE/changed-modules.txt" stage_axioms >/dev/null; lap "axiom audit of changed modules"
      stage_export_project && stage_nanoda_project; lap "independent kernel (nanoda) on changed modules"
    else echo "QUICK: nothing changed since the last passing run, nothing to re-check" | tee -a "$LOGDIR/nanoda.log"; fi;;
  *) sed -n 2,34p "$0"; exit 2;;
esac
