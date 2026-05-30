# W925 Provider Search Ledger

W925 extends the W924 closed-map target-compact-primitive-field route by replacing the target-codomain `IsCompact (Set.univ : Set (wppOpCodomainW441 Y))` provider with the filter-cluster quantifier from the mathlib definition of `IsCompact`.

The route uses explicit `Filter.NeBot` and `Filter.principal` names because the unqualified class name and principal-filter notation used in mathlib's definition are not in scope in this route module.

This is still nonterminal for the original four-task contract: W925 preserves the stable W924 ExactAt route output, keeps `productSuccessClaimed = false`, and records 39 explicit input names with one input refined from universe compactness to the target-codomain compactness filter-cluster condition.
