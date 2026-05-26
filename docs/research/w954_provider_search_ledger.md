# W954 Provider Search Ledger

Generated: 2026-05-27 05:03 JST

Baseline: W953 commit `447ad30`, with product success still false and W945 primitive leaves feeding the W952 provider constructor.

| Candidate | Reduction | Fit | Decision |
| --- | --- | --- | --- |
| W944 unit-component leaves construct W953 | Replace W953's W945 localized-unit data provider field with W944's raw bounded-homotopy localized right adjoint, localized adjunction, and W939 unit strict-exact component witness | Exact fit: these are precisely the fields of `BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945`, so W954 can construct W945 data and then reuse W953 | Selected for W954. |
| Directly adapt W721 localized-right-adjoint data | Use older localized-right-adjoint data where W945 is required | Rejected: W721 has right adjoint, adjunction, and derived functor-category unit membership, but W945 requires the stronger W939 component-level unit witness that derives that membership. |
| Open W944 target no-univ data first | Split W944 into target-difference surjectivity and target no-univ compactness primitives | Also a valid future direction, but W954 targets the W945 localized-unit provider because it was the strongest opaque field exposed by W953. |

Selected W954 outcome: `ClosedMapBoundaryRelationTargetNoUnivClosednessNormalizedSourceEndpointLocalizedUnitDataFromUnitComponentsPrimitiveFieldsRoute.lean` constructs W945 localized-unit data from W944 raw unit-component fields and delegates through W953. Product success remains false because the resulting W944-style field surface is still explicit assumptions.
