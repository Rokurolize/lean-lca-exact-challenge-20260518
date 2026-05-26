# W908 Provider Search Ledger

- Baseline: W907 keeps the endpoint-homology-free closed-map route nonterminal and exposes W716 as the two WPP boundary fields.
- Chosen refinement: open `ClosedNatTransOrdinaryRelationDataProviderW717` into its two constructor fields: `ClosedNatTransOrdinaryRelationPullbackProviderW712` and `ClosedNatTransOrdinaryTargetRelationLiftsProviderW712`.
- Reason: W717 is a plain two-field relation-data structure. Splitting it gives the next proof search the actual relation-pullback and target-relation-lift obligations while preserving the W899-W907 closed-map branch route.
- Existing precedent: W894 already uses this field split in a different route lane; W908 applies the same relation-data exposure to the current W907 branch.
- Result: W908 assembles W717 from the two relation fields, projects into W907, and inherits the W907 stable ExactAt route. It remains nonterminal under the immutable original four-task contract.
- Remaining explicit inputs after W908: 32. The count rises because one bundled W717 provider is replaced by two actual proof fields; this is a concreteness refinement, not a product-success claim.
- Deferred candidates: W715 target-surjective-compact fields, strict preimage object/map fields, fixed-target uniqueness, source-image normalization, branch selection/no-argument original-four-task witness, and the completion review packet.
