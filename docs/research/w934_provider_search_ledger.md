# W934 Provider Search Ledger

W934 extends the W933 closed-map target-compact unit-iso-closure-witness route by exposing the witness object's exact-acyclic homotopy-object predicate as degreewise `QuillenExactCategory.Conflation` data.

The route uses the definitions `exactAcyclicHomotopyObject C K = exactAcyclic C K.as` and `exactAcyclic C K = ∀ i, QuillenExactCategory.Conflation (K.sc i)`. For each bounded complex object `X`, the new primitive asks for a homotopy-category object `K`, degreewise conflations on `K.as`, and an isomorphism from the homotopy-category image of the unit mapping cone to `K`. The adapter reconstructs W933's exact-acyclic homotopy-object witness by unfolding `exactAcyclicHomotopyObject` and `exactAcyclic`.

The target-compactness, strict-preimage, source-image, endpoint, and localized-right-adjoint existence inputs are not solved here. W934 only removes the exact-acyclic object packaging from the localized adjunction unit witness; the route still delegates through W933, W932, W931, and W930 and remains nonterminal for the original four-task contract.

This is still nonterminal for the original four-task contract: W934 preserves the stable W933/W932/W931/W930 ExactAt route output, keeps `productSuccessClaimed = false`, and records 39 explicit input names with the bounded-homotopy localized adjunction unit membership refined to degreewise Quillen conflations plus an isomorphism witness.
