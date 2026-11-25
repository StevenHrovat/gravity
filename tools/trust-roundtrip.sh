#!/usr/bin/env bash
# tools/trust-roundtrip.sh - every hash this repository trusts is first proven by rotation, back and then forth, and each step
# must deliver the expected value (the first author's rule, 2026-11-25: "any sha that is trusted has to first be positively proven
# through rotation"). It runs before every commit and push (.githooks) and in CI (.github/workflows/trust-roundtrip.yml), so nothing
# is written that cannot be read back.
#
#   back   from the content to the hash: the hash is recomputed from what it names
#   forth  from the hash to the content: the content is fetched by its hash (git checks every object id on arrival) and must give
#          the same hash again
#
# First a canary: the full turn on vxunderground must return it, or the state is smelly and nothing is trusted.
# What it proves, found by itself so that a new pin is covered by construction:
#   vendor/*/PIN            the sha256 of the vendored copy (back), and the pinned commit rebuilt into the same copy, byte for byte
#                           (forth)
#   lakefile.toml requires  every commit id (fetched by its id, the id recomputed from its content); a tag must resolve to the hash
#                           recorded for it (Mathlib: mathlib_rev in docs/unified/independent-check.stamp), which is then proven
#   .github/workflows       every action pinned by a commit id (fetched, recomputed); an action trusted by a movable tag fails
# The hashes of build products (Mathlib's compiled files, the exported environment) are recomputed by the kernels stage of
# tools/reproduce.sh, not here. Fetched objects are cached in .reproduce/trust (TRUST_CACHE); without the cache and without network
# the check fails, so nothing is trusted unproven. Exit 0 only when every proof passes.
set -uo pipefail
# A git hook runs with GIT_DIR (and, for pre-commit, GIT_INDEX_FILE) set; clear git's environment so that every git command here acts
# on the repository or cache it names, and find the repository from this script's place (tools/ at its root).
unset GIT_DIR GIT_WORK_TREE GIT_INDEX_FILE GIT_PREFIX GIT_COMMON_DIR GIT_OBJECT_DIRECTORY GIT_ALTERNATE_OBJECT_DIRECTORIES
cd "$(cd "$(dirname "$0")/.." && pwd)"
export LC_ALL=C
CACHE=${TRUST_CACHE:-$PWD/.reproduce/trust}
mkdir -p "$CACHE"
fail=0; count=0
ok() { echo "ok   $*"; count=$((count + 1)); }
bad() { echo "FAIL $*"; fail=1; }
is_sha() { [[ "$1" =~ ^[0-9a-f]{40}$ ]]; }

# The folder hash of tools/check-pin.sh: every file but PIN, in ordinal path order, each as "<relative path>\n<bytes>".
hash_folder() {
  local folder="$1"
  { while IFS= read -r -d '' f; do printf '%s\n' "${f#"$folder"/}"; cat "$f"; done \
      < <(find "$folder" -type f ! -path "$folder/PIN" -print0 | sort -z); } | sha256sum | cut -d' ' -f1
}

# A bare cache repository per source, the source as its promisor remote (so a commit can be fetched without its files).
cache_for() {
  local url="$1" d
  d="$CACHE/$(printf '%s' "$url" | sha256sum | cut -c1-16)"
  if [ ! -d "$d" ]; then
    git init -q --bare "$d"
    git -C "$d" remote add origin "$url"
    git -C "$d" config remote.origin.promisor true
  fi
  printf '%s' "$d"
}

# forth: fetch the commit by its id (git recomputes each object id as it arrives); filter "tree:0" fetches the commit object only.
fetch_commit() {
  local d="$1" sha="$2" filter="$3"
  git -C "$d" cat-file -e "$sha^{commit}" 2>/dev/null && return 0
  if [ -n "$filter" ]; then git -C "$d" fetch -q --depth 1 --filter="$filter" origin "$sha" 2>/dev/null
  else git -C "$d" fetch -q --depth 1 origin "$sha" 2>/dev/null; fi
}

# back: recompute the commit id from the commit's own content.
commit_back() {
  local d="$1" sha="$2"
  [ "$(git -C "$d" cat-file commit "$sha" | git hash-object -t commit --stdin)" = "$sha" ]
}

# One commit id, forth (fetched by its id) and back (its id recomputed from its content).
roundtrip_commit() {
  local what="$1" url="$2" sha="$3" filter="$4" d
  d=$(cache_for "$url")
  if ! fetch_commit "$d" "$sha" "$filter"; then bad "$what: commit $sha could not be fetched from $url (no network and not cached)"; return; fi
  if ! commit_back "$d" "$sha"; then bad "$what: the content of commit $sha does not hash back to it"; return; fi
  ok "$what: commit ${sha:0:12} fetched by its id, its id recomputed from its content ($url)"
}

# 0. The canary: the full turn on vxunderground must return it (Appendix T.5 of Draft 5). A rotation by 13 gives ikhaqretebhaq and
#    a second one completes the turn; if the tools of this machine do not deliver that, the rotational symmetry is not positive, the
#    state is smelly, and nothing is trusted in it.
rot13() { tr 'abcdefghijklmnopqrstuvwxyz' 'nopqrstuvwxyzabcdefghijklm'; }
once=$(printf '%s' vxunderground | rot13); twice=$(printf '%s' "$once" | rot13)
if [ "$once" = ikhaqretebhaq ] && [ "$twice" = vxunderground ]; then
  ok "canary: the full turn on vxunderground returns it (ikhaqretebhaq, then vxunderground); the state is not smelly"
else
  echo "SMELLY: the full turn on vxunderground does not return it (got '$once', then '$twice'); nothing is trusted in this state"
  exit 1
fi

# 1. Vendored copies: the content's sha256 (back), then the pinned commit rebuilt into the same copy and sha256 (forth).
for folder in vendor/*/; do
  folder="${folder%/}"; pin="$folder/PIN"
  [ -f "$pin" ] || { bad "$folder has no PIN"; continue; }
  src=$(awk -F'\t' '$1=="source"{print $2}' "$pin"); commit=$(awk -F'\t' '$1=="commit"{print $2}' "$pin")
  want=$(awk -F'\t' '$1=="sha256"{print $2}' "$pin")
  have=$(hash_folder "$folder")
  if [ "$have" != "$want" ]; then bad "$folder back: the content hashes to $have, the PIN says $want"; continue; fi
  ok "$folder back: the content hashes to the PIN's sha256 ${want:0:12}"
  is_sha "$commit" || { bad "$folder: the PIN's commit '$commit' is not a commit id"; continue; }
  before=$fail
  roundtrip_commit "$folder PIN commit" "$src" "$commit" ""
  [ "$fail" = "$before" ] || continue
  d=$(cache_for "$src"); tmp=$(mktemp -d)
  # The commit's exact bytes: no line-ending conversion on any machine.
  if git -C "$d" -c core.autocrlf=false -c core.eol=lf archive "$commit" | tar -x -C "$tmp"; then
    rm -rf "$tmp/.github"
    rebuilt=$(hash_folder "$tmp")
    if [ "$rebuilt" != "$want" ]; then bad "$folder forth: the commit rebuilds to $rebuilt, the PIN says $want"
    elif ! diff -r --exclude=PIN "$tmp" "$folder" >/dev/null; then bad "$folder forth: the rebuilt copy differs from the vendored files"
    else ok "$folder forth: commit ${commit:0:12} rebuilds the vendored copy byte for byte, sha256 ${want:0:12}"; fi
  else bad "$folder forth: commit $commit could not be read back"; fi
  rm -rf "$tmp"
done

# 2. Lake requirements (the [[require]] blocks only): commit ids round trip; a tag must resolve to its recorded hash.
stamp=docs/unified/independent-check.stamp
while IFS= read -r lf; do
  while IFS=$'\t' read -r name url rev; do
    [ -n "$url" ] || continue
    if is_sha "$rev"; then roundtrip_commit "$lf $name" "$url" "$rev" "tree:0"; continue; fi
    recorded=""
    if [ "$name" = "mathlib" ] && [ -f "$stamp" ]; then recorded=$(sed -n 's/^mathlib_rev=\([0-9a-f]*\).*/\1/p' "$stamp"); fi
    if [ -z "$recorded" ]; then bad "$lf $name: trusted by the tag '$rev' with no recorded hash"; continue; fi
    resolved=$(git ls-remote "$url" "refs/tags/$rev^{}" 2>/dev/null | awk '{print $1}' | head -1)
    [ -n "$resolved" ] || resolved=$(git ls-remote "$url" "refs/tags/$rev" 2>/dev/null | awk '{print $1}' | head -1)
    if [ -z "$resolved" ]; then bad "$lf $name: the tag '$rev' could not be resolved at $url"; continue; fi
    if [ "$resolved" != "$recorded" ]; then bad "$lf $name: the tag '$rev' resolves to $resolved, the record says $recorded"; continue; fi
    ok "$lf $name: the tag '$rev' resolves to the recorded ${recorded:0:12}"
    roundtrip_commit "$lf $name" "$url" "$recorded" "tree:0"
  done < <(awk '
    /^\[\[/ { if (req && n != "") print n "\t" g "\t" r; req = ($0 ~ /^\[\[require\]\]/); n = ""; g = ""; r = ""; next }
    req && /^name = / { v = $0; sub(/^name = "/, "", v); sub(/".*/, "", v); n = v }
    req && /^git = /  { v = $0; sub(/^git = "/, "", v);  sub(/".*/, "", v); g = v }
    req && /^rev = /  { v = $0; sub(/^rev = "/, "", v);  sub(/".*/, "", v); r = v }
    END { if (req && n != "") print n "\t" g "\t" r }' "$lf")
done < <(git ls-files '*lakefile.toml')

# 3. CI actions: pinned by a commit id and proven, or refused.
while read -r ref; do
  action=${ref%@*}; at=${ref##*@}; repo=$(printf '%s' "$action" | cut -d/ -f1-2)
  if is_sha "$at"; then roundtrip_commit "action $action" "https://github.com/$repo" "$at" "tree:0"
  else bad "action $action: trusted by the movable tag '$at', not by a hash"; fi
done < <(grep -rhoE "uses: [^ ]+" .github/workflows/ 2>/dev/null | sed 's/^uses: //' | sort -u)

if [ "$fail" = 0 ]; then echo "trust-roundtrip: OK, $count proofs, every trusted hash proven back and forth"
else echo "trust-roundtrip: FAILED (see the lines above); nothing may be written until every trusted hash is proven"; fi
exit $fail
