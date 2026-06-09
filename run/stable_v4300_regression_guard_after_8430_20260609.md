# Stable v4.30.0 Regression Guard After 8430

Generated UTC: 2026-06-09T12:39:36Z

## Commands

- `cat lean-toolchain`
- `rg -n 'mathlib|rev = ' lakefile.toml`
- `jq -r '.packages[] | select(.name=="mathlib" or .name=="aesop" or .name=="Qq" or .name=="batteries" or .name=="Cli") | [.name,.inputRev,.rev] | @tsv' lake-manifest.json`
- `git log --oneline -- lean-toolchain lakefile.toml lake-manifest.json`
- `rg -n 'v4\.30\.0-rc2' lean-toolchain lakefile.toml lake-manifest.json`
- `git diff --check -- lean-toolchain lakefile.toml lake-manifest.json`

## Results

- `lean-toolchain`: `leanprover/lean4:v4.30.0`.
- `lakefile.toml`: mathlib `rev = "v4.30.0"`.
- `lake-manifest.json` key revisions:
  - `mathlib`: input `v4.30.0`, rev `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
  - `aesop`: input `v4.30.0`, rev `558915ae105bfd8074e22d597613d1961822adc2`.
  - `Qq`: input `v4.30.0`, rev `a6e6c34c4ef182f83b219a3a5a385f51f44bdc4c`.
  - `batteries`: input `main`, rev `32dc18cde3684679f3c003de608743b57498c56f`.
  - `Cli`: input `v4.30.0`, rev `6b907cf12b2e445ccb7c24bc208ef04a1f39e84c`.
- Stable migration checkpoint visible: `b4cdb58d Migrate Lean toolchain to v4.30.0`.
- `v4.30.0-rc2`: no matches, absent as required.
- `git diff --check -- lean-toolchain lakefile.toml lake-manifest.json`: clean.

## Decision

The formal stable Lean/mathlib release gate remains satisfied. No dependency repair is needed before source proof work.
