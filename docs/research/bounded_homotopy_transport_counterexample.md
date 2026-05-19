# Bounded homotopy transport counterexample probe

This note records the w76 boundedness-transport probe. The tested direct theorem is `boundedCochainComplex_transportOfHomotopyEquivUnsafe`: if `K` is a strictly bounded cochain complex and `K` is homotopy equivalent to `L`, then `L` is strictly bounded.

The direct theorem is not a safe assumption. A bounded complex can be homotopy equivalent to a selected representative that contains an added contractible tail with nonzero terms in arbitrarily high or low degrees. The tail is invisible in the homotopy category, but it is visible to `boundedCochainComplex`, whose definition is strict support between two integer bounds on the selected cochain complex.

The Lean audit `audit/blockers/bounded_homotopy_transport_counterexample.lean` isolates the exact formal failure mode. It defines `boundedHomotopyTransportCounterexample C` as a bounded `K`, an unbounded `L`, and nonempty `HomotopyEquiv K L` data, then proves this data refutes `boundedCochainComplex_transportOfHomotopyEquivUnsafe C`. It also records the contractible-tail sketch as `unboundedContractibleTailSketch C`, with a contractible tail and the same bounded/unbounded homotopy-equivalence refutation.

This outcome supports the w68/w72 selected-cochain-isomorphism strictification route. Existing local boundedness transport is through `ObjectProperty.prop_of_iso` and the `boundedCochainComplex_isClosedUnderIsomorphisms` instance, so the bounded route should require either cochain-level isomorphisms to selected representatives or a replacement theorem that controls the selected support directly. A bare homotopy-category isomorphism or `HomotopyEquiv` is too weak for strict boundedness.
