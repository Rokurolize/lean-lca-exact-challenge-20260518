# W976 provider search ledger

Baseline: W975 is the current clean localized-adjunction data route. It verifies a nonterminal route with 12 explicit inputs, including six unit mapping-cone fields: chosen model, degreewise closed embedding, degreewise open map, degreewise cokernel-top, degreewise kernel equality, and chosen unit mapping-cone isomorphism.

Decision: W976 adds dependent `UnitMappingConeKernelCokernelTopIsoDataProviderW976`, parameterized by W975 localized-adjunction data, to package exactly those six unit mapping-cone fields. The route projects W976 data back to W975, rebuilds W975 leaves, and delegates through the existing W975/W974/W973/W972 stack.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| W967 unit kernel/cokernel component route | Reuse a prior unit component surface | W967 works inside an older raw component route and does not package the W975 localized-adjunction-dependent chosen model/isomorphism surface as one provider. |
| W968 chosen unit isomorphism route | Reuse the prior chosen-isomorphism route | W968 only handles the chosen-isomorphism wrapper and still leaves the model and degreewise component fields separate. |
| W945 localized-unit data | Collapse localized adjunction and unit witness together | W945 expects the W939 unit strict-exact component witness, not W975's lower chosen model/kernel/cokernel-top/isomorphism surface. |

Result: selected for W976. Explicit input names drop from 12 to 7. Product success remains false because the seven W976 provider inputs are still explicit assumptions and no original four-task completion witness exists.
