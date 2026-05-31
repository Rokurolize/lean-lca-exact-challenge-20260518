import LeanLCAExactChallenge.Derived.W987SourceHomologicalTriangulationDataConstructionGuardW1496
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataRoute

/-!
W1497 reconnects the W1496/W1495 74-field construction surface to the W987
stable ExactAt route outputs supplied by the existing full-data provider.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpSelectedW461TransportedPointIsoProviderV370SupportW506
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpClosedNatTransOrdinaryRelationFieldsV370SupportW512
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpClosedRangeOnlyComponentwiseProjectionV370SupportW484
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1497 keeps the W1496 74-field source-homological construction surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputW1497 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceHomologicalTriangulationDataConstructionInputW1496

/-- W1497 uses the W1495-constructed W987 full-data provider as its route input. -/
def fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputW1497) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceTriangulationFieldDataW1495
    input

/-- W1497's full-data provider is definitionally W1495's constructed full data. -/
theorem w1497FullDataKeepsW1495ConstructedFullData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputW1497) :
    fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
        input =
      fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceTriangulationFieldDataW1495
        input :=
  rfl

/-- W1497 preserves the boundary/relation projection of W1495's W987 full data. -/
theorem w1497FullDataKeepsBoundaryRelationData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputW1497) :
    boundaryRelationDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
          input) =
      boundaryRelationDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceTriangulationFieldDataW1495
        input :=
  rfl

/-- W1497 preserves the W986 target/closedness/normalized-source/endpoint projection. -/
theorem w1497FullDataKeepsTargetNormalizedEndpointData
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputW1497) :
    targetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataOfFullDataW987
        (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
          input) =
      targetNormalizedEndpointDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceTriangulationFieldDataW1495
        input :=
  rfl

/-- W1497 exposes endpoint strict exactness through W987 full data. -/
def endpointStrictExactOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputW1497) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfFullDataW987
    (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
      input)

/-- W1497 exposes unit mapping-cone strict exactness through W987 full data. -/
def unitMappingConeStrictExactOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputW1497) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfFullDataW987
              (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
                input)).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfFullDataW987
    (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
      input)

/-- W1497 exposes the W987 unit mapping-cone isomorphism nonemptiness. -/
@[reducible]
def unitMappingConeIsoNonemptyOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputW1497) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfFullDataW987
                    (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
                      input)).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfFullDataW987
            (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
              input)).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfFullDataW987
    (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
      input)

/-- W1497 feeds the W987 full-data provider to the direct bounded-left-calculus theorem. -/
theorem directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputW1497) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfFullDataW987
    (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
      input)

/-- W1497 exposes the bounded derived infinity category package through W987 full data. -/
def boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputW1497) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfFullDataW987
    (fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497
      input)

/-- W1497 keeps the W1496 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputNamesW1497 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceHomologicalTriangulationDataConstructionInputNamesW1496

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputNamesW1497_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputNamesW1497.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputNamesW1497]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceHomologicalTriangulationDataConstructionInputNamesW1496_count

/-- Current W1497 nonterminal stable ExactAt route-connection state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionStateW1497 :
    Type where
  seed : String
  declarations : List String
  fullDataResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1497 records the W987 route packages reached from the W1496/W1495 surface. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionStateW1497 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionStateW1497 where
  seed :=
    "w1497-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-stable-exact-at-route-connection"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputW1497",
      "fullDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497",
      "w1497FullDataKeepsW1495ConstructedFullData",
      "w1497FullDataKeepsBoundaryRelationData",
      "w1497FullDataKeepsTargetNormalizedEndpointData",
      "endpointStrictExactOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497",
      "unitMappingConeStrictExactOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497",
      "unitMappingConeIsoNonemptyOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497",
      "directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497",
      "boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionW1497",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputNamesW1497_count"]
  fullDataResult :=
    "proved: the W1496/W1495 construction surface supplies the same W987\
      full-data provider used by the existing W987 stable ExactAt route"
  exactAtResult :=
    "proved: the W1496/W1495 surface reaches endpoint strict exactness,\
      unit mapping-cone strict exactness, unit mapping-cone isomorphism\
      nonemptiness, direct bounded left calculus, and the bounded derived\
      infinity category through W987 full data"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionInputNamesW1497
  productSuccessClaimed := false

theorem currentW1497W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnection_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3StableExactAtRouteConnectionStateW1497.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
