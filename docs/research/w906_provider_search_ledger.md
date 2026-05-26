# W906 Provider Search Ledger

- Baseline: W905 keeps the endpoint-homology-free closed-map route nonterminal and exposes W519's mapped-cokernel closed-map provider as the raw `IsClosedMap` field.
- Chosen refinement: open `SelectedDifferenceClosedMapDiagramComponentProviderW718` into the three W714 diagram-only component fields: `SelectedDifferenceClosedMapPi1DiagramFieldW714`, `SelectedDifferenceClosedMapPi2DiagramFieldW714`, and `SelectedDifferenceClosedMapPi3DiagramFieldW714`.
- Reason: W718 is a plain three-field structure for the selected π₁/π₂/π₃ closed-map diagram obligations. Splitting it gives the next proof search a concrete component surface without changing the W899-W905 closed-map branch semantics.
- Rejected alternative: route through W725 closedness data. That would again mix closed-map and closed-embedding branch data unless a larger branch-selection proof is built at the same time.
- Result: W906 assembles W718 from the three W714 fields, projects into W905, and inherits the W905 stable ExactAt route. It remains nonterminal under the immutable original four-task contract.
- Remaining explicit inputs after W906: 30. The count rises because one bundled W718 provider is replaced by three actual proof fields; this is a concreteness refinement, not a product-success claim.
- Deferred candidates: W716 boundary data fields, W717 relation data fields, strict preimage object/map fields, fixed-target uniqueness, source-image normalization, branch selection/no-argument original-four-task witness, and the completion review packet.
