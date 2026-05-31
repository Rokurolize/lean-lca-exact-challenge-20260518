# LCA-SUP-004 API Scout Result

Status: rejected_candidate

Observed target HEAD: `1e1d98ffacb764c0efe204feaa23b04eed4d7037`

Base proof HEAD: `f08e8d914b47ade3e95745850251c82ef255796f`

## Finding

The relevant names are real, checked, and source-backed, but they do not replace the W987/W1007 provider surface with a positive construction. The W987 and W1007 declarations are provider structures, and the W1449 route exposes component fields, strict exactness, unit mapping-cone data, left calculus, and the bounded-derived infinity-category object only by delegating through a W1007 provider derived from the rewrapped W1447/W987 input.

This is not a product-success route. The strongest source evidence is `w1449W987RewrappedStableRouteInputCount`, which proves the W1449 stable route still has one W987-rewrapped input, together with the W1449 state theorem proving `productSuccessClaimed = false`.

## Source-Backed Declarations

- `LeanLCAExactChallenge.Dbounded.BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987`, structure, `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataRoute.lean:32`. This packages W730 boundary/relation data and W986 target/closedness/normalized-source/endpoint-localized data.
- `LeanLCAExactChallenge.Dbounded.BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007`, structure, `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataDirectRoute.lean:35`. This wraps W987 as the branch-full-data provider.
- `LeanLCAExactChallenge.Dbounded.componentFieldsOfBranchFullDataW1007`, `endpointStrictExactOfBranchFullDataW1007`, `unitMappingConeAlgebraicExactOfBranchFullDataW1007`, `unitMappingConeStrictExactOfBranchFullDataW1007`, `directBoundedLeftCalculusOfBranchFullDataW1007`, and `boundedDerivedInfinityCategoryOfBranchFullDataW1007`, in `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataDirectRoute.lean:206-276`. These are useful outputs, but each consumes a W1007 provider.
- `LeanLCAExactChallenge.Dbounded.w1007RewrappedBoundedDerivedInfinityCategoryW1449`, `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW987RewrappedStableRouteGuardW1449.lean:65`, exposes the stable object through the W1448/W1447 rewrapped provider.
- `LeanLCAExactChallenge.Dbounded.w1449W987RewrappedStableRouteInputCount`, `LeanLCAExactChallenge/Derived/ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW987RewrappedStableRouteGuardW1449.lean:130`, proves the remaining input count is one.
- `LeanLCAExactChallenge.YonedaExt`, `LeanLCAExactChallenge/Ext/Yoneda.lean:3283`, and the checked imported anchors `ShortComplex.Exact`, `DerivedCategory`, `HasDerivedCategory`, and `Abelian.Ext` in `LeanLCAExactChallenge/MathlibSurvey.lean:29-32` exist, but no inspected declaration bridges them to a W987/W1007 positive witness.

## Exact Gap

No inspected local or imported declaration constructs `BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987` or `BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007` from primitive mathlib exactness, Yoneda/Ext, or derived-category APIs without assuming provider data. Current W987/W988/W989/W1007 declarations are projections, packaging, or delegations.

## Rejected Routes

- W1445-W1447 provider packaging loop: `Issues/proof_search_cache.tsv` records this as `rejected_provider_packaging_nonterminal`.
- W1448 W987 rewrap cycle: recorded as `rejected_explicit_cycle`.
- W1449 W987 rewrapped stable route: exposes real exactness/stable outputs but remains one-input and has `productSuccessClaimed=false`.

## Minimal Rerun Snippet

```lean
import LeanLCAExactChallenge.MathlibSurvey
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW987RewrappedStableRouteGuardW1449

#check LeanLCAExactChallenge.Dbounded.BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987
#check LeanLCAExactChallenge.Dbounded.BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007
#check LeanLCAExactChallenge.Dbounded.w1007RewrappedBoundedDerivedInfinityCategoryW1449
#check LeanLCAExactChallenge.Dbounded.w1449W987RewrappedStableRouteInputCount
#check LeanLCAExactChallenge.YonedaExt
#check ShortComplex.Exact
#check DerivedCategory
#check Abelian.Ext
```

Suggested parent command, if a rerun is desired: `lake env lean audit/LCA_SUP_004_api_scout_check.lean`.

## Next Action

Reject another W987/W1007 provider-packaging implementation route. Continue only with a route that constructs W730 plus W986 from primitive positive data, or with an explicit positive `OriginalFourTaskProductSuccess` witness. Do not treat the W1449 stable outputs as product success.
