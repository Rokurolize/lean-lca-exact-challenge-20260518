# W983 provider search ledger

Baseline: W982 supplied W981 localized-adjunction data and unit strict-exact/isomorphism data from W945 localized-unit data. Product success remained false because six provider-level inputs were still explicit: boundary/relation data, target no-univ data, closed-embedding closedness data, endpoint strict exactness, W945 localized-unit data, and normalized-source-triangulation data.

Decision: W983 targets the adjacent endpoint/localized-unit surface. The existing W949 `EndpointStrictExactLocalizedUnitDataProviderW949` packages exactly the endpoint strict short-exact family and the W945 localized-unit data provider. W983 uses only that W949 provider and its projection helpers, while keeping W982's current W944 target no-univ and W973 closed-embedding closedness surface unchanged.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| Reuse the full W949 route surface | Reduce to W949's older four-leaf route | Not type-aligned with the current W982 target/closedness surface: full W949 consumes W947 target-no-univ/closedness data, while W982 consumes W944 plus W973. |
| Construct endpoint strict exactness outright | Remove an endpoint assumption | Still unsupported: no no-argument endpoint strict short-exact family constructor was identified. |
| Bundle W944 target no-univ data with W973 closed-embedding closedness data | Reduce two non-endpoint providers | Plausible, but less local than the exact W949 endpoint/localized-unit fit and would be pure packaging unless a stronger constructor is found. |

Result: selected for W983. The route verifies that W949 endpoint-localized-unit data can supply W982's endpoint strict-exact and W945 localized-unit fields, reducing the current full-data surface from six provider-level inputs to five. Product success remains false because W983 still assumes boundary/relation data, target no-univ data, closed-embedding closedness data, endpoint-localized-unit data, and normalized-source-triangulation data, and no original four-task completion witness exists.
