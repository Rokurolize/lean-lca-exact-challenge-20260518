# W927 Provider Search Ledger

W927 extends the W926 closed-map target-compact-cluster-primitive-field route by replacing the inner `Filter.NeBot (𝓝 x ⊓ f)` witness in the target-codomain compactness provider with the raw non-bottom inequality `(𝓝 x ⊓ f) ≠ ⊥`.

The route leaves the outer compactness filter assumption `[Filter.NeBot f]` unchanged and reconstructs the inner `Filter.NeBot` field by the class constructor from the non-bottom inequality.

This is still nonterminal for the original four-task contract: W927 preserves the stable W926 ExactAt route output, keeps `productSuccessClaimed = false`, and records 39 explicit input names with one input refined from neighborhood-filter meet nontriviality to the underlying non-bottom inequality.
