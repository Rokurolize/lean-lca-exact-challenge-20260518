# W1276 provider search ledger

Baseline: W1275 showed the checked W716/W717/W984/W950 atom routes are all larger than the W1270 one-input W987 surface.

Decision: W1276 records the direct field-split constructors. `boundaryDataOfFieldsW907` builds W716 from two raw boundary fields, and `relationDataOfFieldsW908` builds W717 from two raw relation fields. W984 and W950 are also two-field provider packages. Splitting all four atom candidates directly exposes eight raw/provider inputs. The current branch routes that perform the W716 and W717 field splits are W907 and W908, with 31 and 32 remaining inputs.

Checked Lean facts:

- `directAtomSplitInputNamesW1276_count`: the direct W716/W717/W984/W950 split has 8 inputs.
- `directAtomSplitDoesNotReduceW1276`: the direct split is larger than the W1270 one-input W987 surface.
- `currentBranchBoundaryFieldSplitInputNamesW1276_count`: W907 current branch has 31 inputs.
- `currentBranchRelationFieldSplitInputNamesW1276_count`: W908 current branch has 32 inputs.
- `currentBranchFieldSplitsDoNotReduceW1276`: both current branch field splits are larger than the W1270 one-input W987 surface.

Result: selected as a nonterminal provider-search guard. W1276 does not claim product success; the remaining W987 provider is still explicit.
