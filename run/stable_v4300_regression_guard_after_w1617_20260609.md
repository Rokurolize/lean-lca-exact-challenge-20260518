# Stable v4.30.0 Regression Guard After W1617

Generated UTC: 2026-06-09T12:24:58Z

## Commands And Results

- `cat lean-toolchain`: `leanprover/lean4:v4.30.0`
- `rg -n 'mathlib|rev = ' lakefile.toml`:

```text
9:weak.linter.mathlibStandardSet = true
13:name = "mathlib"
15:rev = "v4.30.0"
```

- `jq -r '.packages[] | select(.name=="mathlib" or .name=="aesop" or .name=="Qq" or .name=="batteries" or .name=="Cli") | [.name,.inputRev,.rev] | @tsv' lake-manifest.json`:

```text
mathlib	v4.30.0	c5ea00351c28e24afc9f0f84379aa41082b1188f
aesop	v4.30.0	558915ae105bfd8074e22d597613d1961822adc2
Qq	v4.30.0	a6e6c34c4ef182f83b219a3a5a385f51f44bdc4c
batteries	main	32dc18cde3684679f3c003de608743b57498c56f
Cli	v4.30.0	6b907cf12b2e445ccb7c24bc208ef04a1f39e84c
```

- `git log --oneline -- lean-toolchain lakefile.toml lake-manifest.json`:

```text
b4cdb58d Migrate Lean toolchain to v4.30.0
0e0afaf8 Prepare Lean LCA exact challenge baseline
```

- `rg -n 'v4\.30\.0-rc2' lean-toolchain lakefile.toml lake-manifest.json`: no matches, exit code 1 as expected for an absent string.
- `git diff --check -- lean-toolchain lakefile.toml lake-manifest.json`: clean.

## Decision

The formal stable Lean/mathlib release gate passes as a regression guard. No dependency or source repair is needed before Tier A proof search.
