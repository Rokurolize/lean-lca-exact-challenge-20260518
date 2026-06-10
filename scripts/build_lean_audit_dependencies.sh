#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -eq 0 ]; then
  audit_files=(
    audit/RequiredDeclarations.lean
    audit/ProductSuccessDeclarations.lean
    audit/OriginalFourTaskCompletionDeclarations.lean
  )
else
  audit_files=("$@")
fi

for audit_file in "${audit_files[@]}"; do
  if [ ! -f "$audit_file" ]; then
    echo "Missing Lean audit file: $audit_file" >&2
    exit 1
  fi
done

mapfile -t modules < <(
  awk '/^import LeanLCAExactChallenge(\.|$)/ { print $2 }' "${audit_files[@]}" | sort -u
)

if [ "${#modules[@]}" -eq 0 ]; then
  echo "No LeanLCAExactChallenge imports found in audit files." >&2
  exit 1
fi

lake build "${modules[@]}"
