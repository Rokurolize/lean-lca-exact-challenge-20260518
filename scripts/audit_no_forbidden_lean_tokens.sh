#!/usr/bin/env bash
set -euo pipefail

roots=("$@")
if (( ${#roots[@]} == 0 )); then
  roots=(".")
fi

if rg -n --glob '*.lean' '\b(sorry|admit|axiom|unsafe)\b|by\s+aesop\?' "${roots[@]}"; then
  echo "Forbidden Lean placeholder or trust-expanding token found." >&2
  exit 1
fi

echo "No forbidden Lean tokens found under: ${roots[*]}"
