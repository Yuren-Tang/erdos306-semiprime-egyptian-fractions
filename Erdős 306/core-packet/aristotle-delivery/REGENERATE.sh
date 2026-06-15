#!/bin/sh
# Refresh this Aristotle delivery snapshot from the live core packet.
#
# Usage:
#   ./REGENERATE.sh
#   WARM_BUILD=/Users/david/erdos-lean-build ./REGENERATE.sh --with-oleans
#
# The default mode is source/notes only.  This is intentional: most prompt
# refreshes should not rewrite the prebuilt cache or trigger unnecessary build
# churn.  Use --with-oleans only after a green local build whose artifacts should
# be ferried to Aristotle.
set -e
here="$(cd "$(dirname "$0")" && pwd)"
core="$here/.."
src="$core/lean"

with_oleans=0
case "${1:-}" in
  --with-oleans) with_oleans=1 ;;
  "") ;;
  *)
    echo "Unknown option: $1" >&2
    echo "Usage: $0 [--with-oleans]" >&2
    exit 2
    ;;
esac

echo "Refreshing Lean sources from $src"
rm -rf "$here/RequestProject"
cp -R "$src/RequestProject" "$here/RequestProject"
cp "$src/lakefile.toml" "$src/lean-toolchain" "$here/"
[ -f "$src/lake-manifest.json" ] && cp "$src/lake-manifest.json" "$here/"

echo "Refreshing current R2 notes"
for note in \
  "00 README.md" \
  "35 Circle Method - Detailed Spec (Translation-Ready).md" \
  "50 R2 Construction Resolved - Gadget Cancellation and the b≥3 Reduction.md" \
  "51 R2 Mass Batch Completed.md" \
  "52 R2 Assembly Skeleton Next Task.md" \
  "53 R2 Assembly Skeleton Bookkeeping Completed.md" \
  "55 R2 Parallel Returns Integrated.md" \
  "56 R2 Endgame Map and Parallel Tasks.md" \
  "CODEX_TASK_r2_numeric_fields.md" \
  "CODEX_TASK_r2_minor_support_budget.md" \
  "CODEX_TASK_r2_pair_pool_full_lower.md" \
  "ARISTOTLE_TASK_r2_component_numeric.md" \
  "ARISTOTLE_TASK_r2_forbidden_pool_budget.md"
do
  [ -f "$core/$note" ] && cp "$core/$note" "$here/"
done

if [ "$with_oleans" -eq 1 ]; then
  warm="${WARM_BUILD:-$HOME/erdos-lean-build}"
  warm_lean="$warm/.lake/build/lib/lean/RequestProject"
  dest_lean="$here/.lake/build/lib/lean/RequestProject"
  if [ ! -d "$warm_lean" ]; then
    echo "Missing warm build artifacts: $warm_lean" >&2
    exit 1
  fi
  echo "Refreshing RequestProject oleans from $warm_lean"
  mkdir -p "$dest_lean"
  cp "$warm_lean"/* "$dest_lean/"
  tar -czf "$here/prebuilt-oleans.tar.gz" -C "$here" .lake/build/lib/lean/RequestProject
else
  echo "Skipping olean refresh.  Pass --with-oleans after a green build if needed."
fi

echo "Refreshed delivery snapshot."
echo "Upload the whole folder: $here"
