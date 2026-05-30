# W933 Provider Search Ledger

W933 extends the W932 closed-map target-compact unit-cone-iso-closure route by exposing the unit mapping-cone exact-acyclic homotopy iso-closure predicate as the explicit witness hidden by mathlib's `ObjectProperty.isoClosure`.

The route uses the definition `ObjectProperty.isoClosure P X = ∃ Y, P Y ∧ Nonempty (X ≅ Y)`. For each bounded complex object `X`, the new primitive asks for a homotopy-category object `K`, a proof that `K` is an `exactAcyclicHomotopyObject MetrizableLCA`, and an isomorphism from the homotopy-category image of the unit mapping cone to `K`. The adapter reconstructs W932's `exactAcyclicHomotopyIsoClosure` field by unfolding `exactAcyclicHomotopyIsoClosure` and `ObjectProperty.isoClosure`.

The target-compactness, strict-preimage, source-image, endpoint, and localized-right-adjoint existence inputs are not solved here. W933 only removes the iso-closure packaging from the localized adjunction unit membership predicate; the route still delegates through W932, W931, and W930 and remains nonterminal for the original four-task contract.

This is still nonterminal for the original four-task contract: W933 preserves the stable W932/W931/W930 ExactAt route output, keeps `productSuccessClaimed = false`, and records 39 explicit input names with the bounded-homotopy localized adjunction unit membership refined to an explicit exact-acyclic homotopy object plus isomorphism witness.
