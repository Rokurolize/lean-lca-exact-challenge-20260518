#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"

if rg -n --glob '*.lean' '\b(sorry|admit|axiom|unsafe)\b|by\s+aesop\?' "$root"; then
  echo "Forbidden Lean placeholder or trust-expanding token found." >&2
  exit 1
fi

echo "No forbidden Lean tokens found under $root."
