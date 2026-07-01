#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if (( $# == 0 )); then
  mapfile -t files < <(find RequestProject -name '*.lean' -type f | sort)
else
  files=("$@")
fi

if (( ${#files[@]} == 0 )); then
  echo "No Lean source files to audit."
  exit 0
fi

status=0
for file in "${files[@]}"; do
  [[ -f "$file" ]] || continue
  module=${file%.lean}
  module=${module//\//.}
  echo "Building audit target: $module"
  lake build "$module"

  tmpdir=$(mktemp -d "${TMPDIR:-/tmp}/request-project-import-audit.XXXXXX")
  tmp="$tmpdir/Audit.lean"
  log="$tmpdir/Audit.log"
  trap 'rm -rf "$tmpdir"' EXIT

  cp "$file" "$tmp"
  printf '\n#redundant_imports\n' >> "$tmp"
  echo "Auditing imports: $file"
  if ! lake env lean "$tmp" >"$log" 2>&1; then
    cat "$log"
    status=1
  elif grep -Eiq 'Found the following transitively redundant imports|unneeded import|missing imports' "$log"; then
    cat "$log"
    status=1
  fi

  rm -rf "$tmpdir"
  trap - EXIT
done

exit "$status"
