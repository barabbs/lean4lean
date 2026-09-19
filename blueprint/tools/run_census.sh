#!/usr/bin/env bash
# Reproduce the ground-truth declaration census (understand/decls.tsv and
# understand/all-constants.tsv) that the blueprint's tools/ scripts and chapters
# are checked against.
#
# This does NOT build the project. It runs `lake env lean` against an
# already-built lean4lean checkout (a `lake build` must have succeeded already;
# see the top-level README). Each run below just re-elaborates a tiny generated
# file that imports part of the project and dumps its environment.
#
# Why one run per import set instead of one big import: several
# Lean4Lean/Experimental/*.lean modules open the same namespace and redeclare
# the same names (they are mutually exclusive drafts, not a library), so
# importing more than one of them at once fails with "environment already
# contains". Each set below is therefore compiled and evaluated in its own
# process, and the per-run outputs are merged afterwards.
#
# Usage:
#   ./run_census.sh
#   BLUEPRINT_WORK=/path/to/workdir ./run_census.sh
#
# Output: <workdir>/understand/decls.tsv and <workdir>/understand/all-constants.tsv
# (workdir defaults to <repo root>/.blueprint-work).

set -euo pipefail

TOOLS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$TOOLS_DIR/../.." && pwd)"
WORK="${BLUEPRINT_WORK:-$ROOT/.blueprint-work}"
OUT="$WORK/understand"
TEMPLATE="$TOOLS_DIR/Census2.lean"

if [ ! -f "$TEMPLATE" ]; then
  echo "missing $TEMPLATE" >&2
  exit 1
fi
if ! grep -q 'ALLC_PATH' "$TEMPLATE"; then
  echo "$TEMPLATE has no ALLC_PATH placeholder to substitute" >&2
  exit 1
fi

mkdir -p "$OUT"
RUNDIR="$(mktemp -d)"
trap 'rm -rf "$RUNDIR"' EXIT

# Each entry is "tag|import1,import2,...".
sets=()

sets+=("core|Lean4Lean,Lean4Lean.Theory,Lean4Lean.Verify,Lean4Lean.Tests")

for f in "$ROOT"/Lean4Lean/Experimental/*.lean; do
  name="$(basename "$f" .lean)"
  sets+=("$name|Lean4Lean.Experimental.$name")
done

for f in "$ROOT"/Lean4Lean/Tests/*.lean; do
  name="$(basename "$f" .lean)"
  sets+=("T_$name|Lean4Lean.Tests.$name")
done

sets+=("LevelSat|Lean4Lean.Theory.LevelSat")
sets+=("main|Main")

echo "running ${#sets[@]} census passes against $ROOT (workdir: $WORK)" >&2

cd "$ROOT"
for entry in "${sets[@]}"; do
  tag="${entry%%|*}"
  imports="${entry#*|}"
  allc_out="$RUNDIR/allc-$tag.tsv"
  runfile="$RUNDIR/Run_$tag.lean"
  {
    echo "import Lean"
    IFS=',' read -ra mods <<< "$imports"
    for m in "${mods[@]}"; do echo "import $m"; done
    sed "s#ALLC_PATH#$allc_out#" "$TEMPLATE"
  } > "$runfile"
  echo "  [$tag] $imports" >&2
  if ! lake env lean "$runfile" > "$RUNDIR/part-$tag.tsv" 2> "$RUNDIR/err-$tag.txt"; then
    echo "FAILED: $tag" >&2
    cat "$RUNDIR/err-$tag.txt" >&2
    exit 1
  fi
  if [ -s "$RUNDIR/err-$tag.txt" ]; then
    echo "  (stderr, non-fatal) $tag:" >&2
    cat "$RUNDIR/err-$tag.txt" >&2
  fi
done

sort -u "$RUNDIR"/part-*.tsv | awk -F'\t' 'NF>=7' > "$OUT/decls.tsv"
sort -u "$RUNDIR"/allc-*.tsv | awk -F'\t' 'NF==3' > "$OUT/all-constants.tsv"

echo "wrote $(wc -l < "$OUT/decls.tsv") lines to $OUT/decls.tsv" >&2
echo "wrote $(wc -l < "$OUT/all-constants.tsv") lines to $OUT/all-constants.tsv" >&2
