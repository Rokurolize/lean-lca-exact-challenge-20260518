# W975 provider search ledger

Baseline: W974 is the current clean endpoint kernel/cokernel-top data route. It verifies a nonterminal route with 13 explicit inputs, including separate bounded-homotopy localized right-adjoint and localized adjunction fields.

Decision: W975 adds `BoundedHomotopyLocalizedAdjunctionDataProviderW975` to package exactly those two localized-adjunction fields. The route projects W975 data back to W974, rebuilds W974 leaves, and delegates through the existing W974/W973/W972 stack.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| W721 localized-right-adjoint data | Bundle right adjoint, adjunction, and unit membership | W721 requires a unit membership field that W974 does not currently expose directly. |
| W945 localized-unit data | Bundle right adjoint, adjunction, and W939 component witness | W945 targets the older endpoint strict-exact plus W939 unit component witness surface, not W974's unit mapping-cone model/component/chosen-isomorphism fields. |
| Unit mapping-cone provider first | Bundle the remaining unit model/component/isomorphism fields | No existing provider matched the W974 chosen-model and chosen-isomorphism surface without adding extra assumptions, so W975 performs the exact two-field reduction first. |

Result: selected for W975. Explicit input names drop from 13 to 12. Product success remains false because the remaining W975 field surface still consists of explicit unit mapping-cone assumptions and does not construct the original four-task completion witness.
