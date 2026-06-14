#!/bin/sh
# Refresh this Aristotle delivery snapshot from the live Lean package.
# Run from anywhere; paths are relative to this script's directory.
set -e
here="$(cd "$(dirname "$0")" && pwd)"
src="$here/../lean"
rm -rf "$here/RequestProject"
cp -R "$src/RequestProject" "$here/RequestProject"
cp "$src/lakefile.toml" "$src/lean-toolchain" "$here/"
[ -f "$src/lake-manifest.json" ] && cp "$src/lake-manifest.json" "$here/"
echo "Refreshed delivery snapshot from $src"
echo "Upload the whole folder: $here  (includes TASK.md)"
