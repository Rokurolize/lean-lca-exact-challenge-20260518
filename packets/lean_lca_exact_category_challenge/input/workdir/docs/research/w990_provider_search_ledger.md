# W990 Provider Search Ledger

Generated: 2026-05-27 13:07 JST

## Decision

W990 opens W989's W975 localized-adjunction data provider and W981 unit strict-exact/isomorphism provider into explicit localized adjunction fields plus the W939 unit mapping-cone component witness.

## Candidate Surfaces

- `BoundedHomotopyLocalizedAdjunctionDataProviderW975`: rejected as a terminal W990 input because W989 already consumed it opaquely.
- `UnitMappingConeStrictExactIsoDataProviderW981`: rejected as a terminal W990 input because W989 already consumed it opaquely.
- `BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945`: rejected because it repackages the same data into W988's older six-input surface and does not expose the W939 witness.
- W939 component witness plus localized right adjoint and adjunction: selected because it reconstructs both W975 and W981 while preserving the W973 closed-embedding branch.

## Result

`ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromPrimitiveUnitComponentsRoute.lean` constructs:

- `localizedAdjunctionDataOfPrimitiveUnitComponentsW990`
- `unitStrictExactIsoDataOfPrimitiveUnitComponentsW990`
- `unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990`
- delegates through W989/W988/W987 to the stable ExactAt route

Product success remains false. The remaining surface is eight explicit primitive-level fields.
