#!/usr/bin/env bash
set -euo pipefail

root="${1:-.}"

if [[ ! -e "$root/.git" ]]; then
  echo "audit_no_generated_files: $root is not a git worktree root" >&2
  exit 1
fi

offenders=()
while IFS= read -r -d '' path; do
  case "$path" in
    .lake/*|run/*|terminal_outcome/*|packets/*|__pycache__/*|manifest.json|*.pyc|*.log|*.exit|*.err|*.status|*.tsv|*.olean|*.ilean|*.c|*.o)
      offenders+=("$path")
      ;;
  esac
done < <(git -C "$root" ls-files -z)

if (( ${#offenders[@]} )); then
  printf 'Generated or transient artifacts are tracked:\n' >&2
  printf '  %s\n' "${offenders[@]}" >&2
  exit 1
fi

echo "No generated or transient artifacts are tracked."
