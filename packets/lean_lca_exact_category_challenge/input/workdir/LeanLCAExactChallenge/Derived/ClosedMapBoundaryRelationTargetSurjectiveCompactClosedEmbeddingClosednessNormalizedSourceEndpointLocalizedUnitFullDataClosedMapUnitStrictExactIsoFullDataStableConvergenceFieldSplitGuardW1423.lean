import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapEndpointStrictExactFullDataStableConvergenceFieldSplitGuardW1422
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataRoute

/-!
W1423 records definitional convergence for the W981 endpoint/unit
strict-exact full-data route: W981 constructs the W976 unit provider from
strict exactness plus a chosen isomorphism, then delegates through W980.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W981 constructs W980 leaves after rebuilding unit kernel/cokernel-top iso data. -/
theorem w981W980LeavesRunThroughUnitStrictExactIsoW1423
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    w980LeavesOfUnitStrictExactIsoW981 fullData =
      w977LeavesOfEndpointStrictExactW980
        (fullDataOfUnitStrictExactIsoW981 fullData) :=
  rfl

/-- W981 exposes the W971 component split through W980. -/
theorem w981ComponentFieldsRunThroughW980W1423
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    componentFieldsOfUnitStrictExactIsoW981 fullData =
      componentFieldsOfEndpointStrictExactW980
        (fullDataOfUnitStrictExactIsoW981 fullData) :=
  rfl

/-- W981 endpoint strict exactness delegates through W980. -/
theorem w981EndpointStrictExactRunsThroughW980W1423
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    endpointStrictExactOfUnitStrictExactIsoW981 fullData =
      endpointStrictExactOfEndpointStrictExactW980
        (fullDataOfUnitStrictExactIsoW981 fullData) :=
  rfl

/-- W981 unit algebraic exactness delegates through W980. -/
theorem w981UnitAlgebraicExactRunsThroughW980W1423
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    unitMappingConeAlgebraicExactOfUnitStrictExactIsoW981 fullData =
      unitMappingConeAlgebraicExactOfEndpointStrictExactW980
        (fullDataOfUnitStrictExactIsoW981 fullData) :=
  rfl

/-- W981 direct calculus delegates to W980 after constructing unit data. -/
theorem w981DirectCalculusRunsThroughW980W1423
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    directBoundedLeftCalculusOfUnitStrictExactIsoW981 fullData =
      directBoundedLeftCalculusOfEndpointStrictExactW980
        (fullDataOfUnitStrictExactIsoW981 fullData) :=
  rfl

/-- W981 stable package delegates to W980 after constructing unit data. -/
theorem w981StablePackageRunsThroughW980W1423
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    boundedDerivedInfinityCategoryOfUnitStrictExactIsoW981 fullData =
      boundedDerivedInfinityCategoryOfEndpointStrictExactW980
        (fullDataOfUnitStrictExactIsoW981 fullData) :=
  rfl

/-- W1423 keeps the W981 unit strict-exact/isomorphism input count visible. -/
theorem w1423ClosedMapUnitStrictExactIsoDataInputCount :
    unitStrictExactIsoDataInputNamesW981.length =
      3 :=
  unitStrictExactIsoDataInputNamesW981_count

/-- W1423 keeps the W981 endpoint/unit full-data input count visible. -/
theorem w1423ClosedMapEndpointUnitStrictExactFullDataInputCount :
    endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981.length =
      7 :=
  endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981_count

/-- Current W1423 nonterminal state. -/
structure ClosedMapUnitStrictExactIsoFullDataStableConvergenceStateW1423 :
    Type where
  seed : String
  declarations : List String
  unitStrictExactIsoBridgeResult : String
  unitStrictExactIsoUnpackResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1423 records W981 convergence into the closed-map stable route. -/
def currentClosedMapUnitStrictExactIsoFullDataStableConvergenceStateW1423 :
    ClosedMapUnitStrictExactIsoFullDataStableConvergenceStateW1423 where
  seed := "w1423-closed-map-unit-strict-exact-iso-full-data-stable-convergence"
  declarations :=
    ["w981W980LeavesRunThroughUnitStrictExactIsoW1423",
      "w981ComponentFieldsRunThroughW980W1423",
      "w981EndpointStrictExactRunsThroughW980W1423",
      "w981UnitAlgebraicExactRunsThroughW980W1423",
      "w981DirectCalculusRunsThroughW980W1423",
      "w981StablePackageRunsThroughW980W1423",
      "w1423ClosedMapUnitStrictExactIsoDataInputCount",
      "w1423ClosedMapEndpointUnitStrictExactFullDataInputCount"]
  unitStrictExactIsoBridgeResult :=
    "proved: W981 endpoint/unit strict-exact full data delegates into W980"
  unitStrictExactIsoUnpackResult :=
    "proved: W981 replaces the W976 unit mapping-cone kernel/cokernel-top\
      provider by a model, strict short-exact family, and chosen isomorphism"
  remainingInputs :=
    endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981
  productSuccessClaimed := false

theorem currentW1423ClosedMapUnitStrictExactIsoFullDataStableConvergence_productSuccess :
    currentClosedMapUnitStrictExactIsoFullDataStableConvergenceStateW1423.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
