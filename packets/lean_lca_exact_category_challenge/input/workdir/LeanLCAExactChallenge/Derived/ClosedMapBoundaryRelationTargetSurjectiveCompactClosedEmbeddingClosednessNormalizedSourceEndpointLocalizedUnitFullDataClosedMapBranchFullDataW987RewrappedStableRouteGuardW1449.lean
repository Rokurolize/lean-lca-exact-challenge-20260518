import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW987RewrapCycleGuardW1448

/-!
W1449 records that the W1448 rewrapped W1007 provider carries the W1007 route
outputs used by the stable construction. The rewrapped provider exposes the
component-field data, endpoint exactness, unit exactness, left calculus, and
bounded-derived infinity-category object through the same W1007 route surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

/-- W1449 exposes W1007 component fields from the W1448 rewrapped provider. -/
noncomputable def w1007RewrappedComponentFieldsW1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :=
  componentFieldsOfBranchFullDataW1007
    (w1007BranchFullDataProviderOfW1447 branchFullData)

/-- W1449 exposes endpoint strict exactness from the W1448 rewrapped provider. -/
noncomputable def w1007RewrappedEndpointStrictExactW1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :=
  endpointStrictExactOfBranchFullDataW1007
    (w1007BranchFullDataProviderOfW1447 branchFullData)

/-- W1449 exposes unit mapping-cone algebraic exactness from the rewrapped provider. -/
noncomputable def w1007RewrappedUnitMappingConeAlgebraicExactW1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :=
  unitMappingConeAlgebraicExactOfBranchFullDataW1007
    (w1007BranchFullDataProviderOfW1447 branchFullData)

/-- W1449 exposes unit mapping-cone strict exactness from the rewrapped provider. -/
noncomputable def w1007RewrappedUnitMappingConeStrictExactW1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :=
  unitMappingConeStrictExactOfBranchFullDataW1007
    (w1007BranchFullDataProviderOfW1447 branchFullData)

/-- W1449 exposes unit mapping-cone isomorphism data from the rewrapped provider. -/
@[reducible]
noncomputable def w1007RewrappedUnitMappingConeIsoNonemptyW1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :=
  unitMappingConeIsoNonemptyOfBranchFullDataW1007
    (w1007BranchFullDataProviderOfW1447 branchFullData)

/-- W1449 exposes the direct bounded left-calculus proof from the rewrapped provider. -/
theorem w1007RewrappedDirectBoundedLeftCalculusW1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW1007
    (w1007BranchFullDataProviderOfW1447 branchFullData)

/-- W1449 exposes the bounded-derived infinity-category object from the rewrapped provider. -/
noncomputable def w1007RewrappedBoundedDerivedInfinityCategoryW1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW1007
    (w1007BranchFullDataProviderOfW1447 branchFullData)

/-- The W1449 component-field route is exactly the W1007 route on the rewrapped provider. -/
theorem w1007RewrappedComponentFieldsRunThroughW1007W1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    w1007RewrappedComponentFieldsW1449 branchFullData =
      componentFieldsOfBranchFullDataW1007
        (w1007BranchFullDataProviderOfW1447 branchFullData) :=
  rfl

/-- The W1449 endpoint strict-exact route is exactly the W1007 route on the rewrapped provider. -/
theorem w1007RewrappedEndpointStrictExactRunsThroughW1007W1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    w1007RewrappedEndpointStrictExactW1449 branchFullData =
      endpointStrictExactOfBranchFullDataW1007
        (w1007BranchFullDataProviderOfW1447 branchFullData) :=
  rfl

/-- The W1449 unit algebraic-exact route is exactly the W1007 route on the rewrapped provider. -/
theorem w1007RewrappedUnitAlgebraicExactRunsThroughW1007W1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    w1007RewrappedUnitMappingConeAlgebraicExactW1449 branchFullData =
      unitMappingConeAlgebraicExactOfBranchFullDataW1007
        (w1007BranchFullDataProviderOfW1447 branchFullData) :=
  rfl

/-- The W1449 unit strict-exact route is exactly the W1007 route on the rewrapped provider. -/
theorem w1007RewrappedUnitStrictExactRunsThroughW1007W1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    w1007RewrappedUnitMappingConeStrictExactW1449 branchFullData =
      unitMappingConeStrictExactOfBranchFullDataW1007
        (w1007BranchFullDataProviderOfW1447 branchFullData) :=
  rfl

/-- The W1449 unit isomorphism route is exactly the W1007 route on the rewrapped provider. -/
theorem w1007RewrappedUnitIsoRunsThroughW1007W1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    w1007RewrappedUnitMappingConeIsoNonemptyW1449 branchFullData =
      unitMappingConeIsoNonemptyOfBranchFullDataW1007
        (w1007BranchFullDataProviderOfW1447 branchFullData) :=
  rfl

/-- The W1449 stable object is exactly the W1007 construction on the rewrapped provider. -/
theorem w1007RewrappedBoundedDerivedInfinityCategoryRunsThroughW1007W1449
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    w1007RewrappedBoundedDerivedInfinityCategoryW1449 branchFullData =
      boundedDerivedInfinityCategoryOfBranchFullDataW1007
        (w1007BranchFullDataProviderOfW1447 branchFullData) :=
  rfl

/-- W1449 keeps W987's one-input stable-output surface visible after rewrapping. -/
theorem w1449W987RewrappedStableRouteInputCount :
    w1007W987RewrappedInputNamesW1448.length = 1 :=
  w1007W987RewrappedInputNamesW1448_count

/-- Current W1449 nonterminal W987-rewrapped stable-route state. -/
structure ClosedMapBranchFullDataW987RewrappedStableRouteStateW1449 : Type where
  seed : String
  declarations : List String
  exactnessResult : String
  stableRouteResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1449 records W1007 exactness and stable-route outputs for the W1448 wrapper. -/
def currentClosedMapBranchFullDataW987RewrappedStableRouteStateW1449 :
    ClosedMapBranchFullDataW987RewrappedStableRouteStateW1449 where
  seed := "w1449-closed-map-branch-full-data-w987-rewrapped-stable-route"
  declarations :=
    ["w1007RewrappedComponentFieldsW1449",
      "w1007RewrappedEndpointStrictExactW1449",
      "w1007RewrappedUnitMappingConeAlgebraicExactW1449",
      "w1007RewrappedUnitMappingConeStrictExactW1449",
      "w1007RewrappedUnitMappingConeIsoNonemptyW1449",
      "w1007RewrappedDirectBoundedLeftCalculusW1449",
      "w1007RewrappedBoundedDerivedInfinityCategoryW1449",
      "w1007RewrappedComponentFieldsRunThroughW1007W1449",
      "w1007RewrappedEndpointStrictExactRunsThroughW1007W1449",
      "w1007RewrappedUnitAlgebraicExactRunsThroughW1007W1449",
      "w1007RewrappedUnitStrictExactRunsThroughW1007W1449",
      "w1007RewrappedUnitIsoRunsThroughW1007W1449",
      "w1007RewrappedBoundedDerivedInfinityCategoryRunsThroughW1007W1449",
      "w1449W987RewrappedStableRouteInputCount"]
  exactnessResult :=
    "proved: the W1448 rewrapped W1007 provider carries component fields,\
      endpoint strict exactness, unit algebraic exactness, unit strict\
      exactness, and unit isomorphism data through the W1007 route"
  stableRouteResult :=
    "proved: the W1448 rewrapped W1007 provider supplies the direct bounded\
      left-calculus proof and bounded-derived infinity-category object through\
      the W1007 route; product success is still not claimed"
  remainingInputs := w1007W987RewrappedInputNamesW1448
  productSuccessClaimed := false

theorem currentW1449ClosedMapBranchFullDataW987RewrappedStableRoute_productSuccess :
    currentClosedMapBranchFullDataW987RewrappedStableRouteStateW1449.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
