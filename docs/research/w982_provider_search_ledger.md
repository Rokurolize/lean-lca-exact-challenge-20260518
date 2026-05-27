# W982 provider search ledger

Baseline: W981 constructed the W976 unit mapping-cone kernel/cokernel-top provider from a unit mapping-cone model, a unit strict short-exact family, and a chosen mapping-cone isomorphism, then delegated through W980. Product success remained false because seven provider-level inputs were still explicit: boundary/relation data, target no-univ data, closed-embedding closedness data, endpoint strict exactness, W975 localized-adjunction data, W948 normalized-source-triangulation data, and W981 unit strict-exact/isomorphism data.

Decision: W982 targets the overlap between the W975 localized-adjunction input and the W981 unit strict-exact/isomorphism input. The existing W945 localized-unit provider already carries a localized right adjoint, its adjunction, and a W939 Prop-level unit mapping-cone component witness. W982 extracts the W975 localized-adjunction provider from W945 and uses `Classical.choose` on the W939 witness to choose the unit mapping-cone model, degreewise strict short exactness, and mapping-cone isomorphism required by W981.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| Construct localized adjunction outright | Remove the localized-unit/provider boundary | Still unsupported: no no-argument localized right adjoint or adjunction constructor was identified. |
| Keep W975 and W981 unit data separate | Avoid classical choice from W939 | This would leave W981's seven provider-level inputs unchanged and miss an already available local consolidation. |
| Replace target no-univ plus closed-embedding closedness with older W947 data | Potentially reduce two topological providers | The W947 closedness surface is not the same as the W973 closed-embedding branch consumed by the current W981/W980 route. |

Result: selected for W982. The route verifies that W945 localized-unit data can supply both W975 localized-adjunction data and W981 unit strict-exact/isomorphism data, reducing the current full-data surface from seven provider-level inputs to six. Product success remains false because W982 still assumes boundary/relation data, target no-univ data, closed-embedding closedness data, endpoint strict exactness, localized-unit data, and normalized-source-triangulation data, and no original four-task completion witness exists.
