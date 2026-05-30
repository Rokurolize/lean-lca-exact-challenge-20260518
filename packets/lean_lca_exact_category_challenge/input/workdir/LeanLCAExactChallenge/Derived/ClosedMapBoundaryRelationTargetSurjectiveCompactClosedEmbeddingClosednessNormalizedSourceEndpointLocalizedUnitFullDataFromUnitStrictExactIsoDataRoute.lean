import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromComponentFieldsRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataRoute

/-!
W1001 replaces W1000's W971 component-field surface by the existing W981
endpoint/unit-strict-exact provider surface. W981 already splits that provider
into W971 component fields, and W1001 feeds those fields into W1000.
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

/-- W1001 constructs the W971 component-field surface from W981 provider data. -/
def componentFieldsOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfUnitStrictExactIsoW981 fullData

/-- W1001 constructs W977 current full data from W981 provider data through W1000. -/
def currentFullDataOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  currentFullDataOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

/-- W1001 constructs W987 branch full data through W1000. -/
noncomputable def branchFullDataOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

/-- W1001 recovers W715 target surjective-compact data through W1000. -/
noncomputable def targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

/-- W1001 builds W997's branch-full-data surface from W981 provider data. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997
    where
  targetSurjectiveCompactData :=
    targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1001 fullData
  branchFullData := branchFullDataOfUnitStrictExactIsoDataW1001 fullData

/-- W1001 builds the W995 target-provider surface through W1000. -/
noncomputable def targetProviderDataOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

/-- W1001 builds the W994 normalized-source/endpoint route data through W1000. -/
noncomputable def normalizedSourceEndpointDataOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

/-- W1001 returns the constructed W987 branch full data through W1000. -/
noncomputable def fullDataOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

/- W1001 exposes W977 leaves through W1000. -/
noncomputable def w977LeavesOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

/-- W1001 reconstructs endpoint strict exactness through W1000. -/
noncomputable def endpointStrictExactOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

/-- W1001 derives unit mapping-cone algebraic exactness through W1000. -/
noncomputable def unitMappingConeAlgebraicExactOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfComponentFieldsW1000
            (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfComponentFieldsW1000
            (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfComponentFieldsW1000
                (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfComponentFieldsW1000
                (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

/-- W1001 reconstructs unit mapping-cone strict short exactness through W1000. -/
noncomputable def unitMappingConeStrictExactOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfComponentFieldsW1000
            (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

/-- W1001 wraps the unit mapping-cone isomorphism through W1000. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfComponentFieldsW1000
                    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfComponentFieldsW1000
            (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

theorem directBoundedLeftCalculusOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

noncomputable def boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1001
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitStrictExactIsoDataProviderW981) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfComponentFieldsW1000
    (componentFieldsOfUnitStrictExactIsoDataW1001 fullData)

def unitStrictExactIsoDataInputNamesW1001 : List String :=
  endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981

theorem unitStrictExactIsoDataInputNamesW1001_count :
    unitStrictExactIsoDataInputNamesW1001.length = 7 :=
  endpointUnitStrictExactLocalizedUnitFullDataInputNamesW981_count

structure MetrizableUnitStrictExactIsoDataRouteStateW1001 : Type where
  seed : String
  declarations : List String
  providerRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableUnitStrictExactIsoDataRouteStateW1001 :
    MetrizableUnitStrictExactIsoDataRouteStateW1001
    where
  seed := "w1001-unit-strict-exact-iso-data-to-component-fields-route"
  declarations :=
    ["componentFieldsOfUnitStrictExactIsoDataW1001",
      "currentFullDataOfUnitStrictExactIsoDataW1001",
      "branchFullDataOfUnitStrictExactIsoDataW1001",
      "targetSurjectiveCompactDataOfUnitStrictExactIsoDataW1001",
      "targetSurjectiveCompactBranchFullDataOfUnitStrictExactIsoDataW1001",
      "targetProviderDataOfUnitStrictExactIsoDataW1001",
      "normalizedSourceEndpointDataOfUnitStrictExactIsoDataW1001",
      "fullDataOfUnitStrictExactIsoDataW1001",
      "w977LeavesOfUnitStrictExactIsoDataW1001",
      "endpointStrictExactOfUnitStrictExactIsoDataW1001",
      "unitMappingConeAlgebraicExactOfUnitStrictExactIsoDataW1001",
      "unitMappingConeStrictExactOfUnitStrictExactIsoDataW1001",
      "unitMappingConeIsoNonemptyOfUnitStrictExactIsoDataW1001",
      "directBoundedLeftCalculusOfUnitStrictExactIsoDataW1001",
      "boundedDerivedInfinityCategoryOfUnitStrictExactIsoDataW1001",
      "unitStrictExactIsoDataInputNamesW1001_count"]
  providerRepackagingResult :=
    "proved: W1001 constructs the W971 component-field surface from W981\
      endpoint/unit-strict-exact provider data and feeds the W1000 route"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1001 inherits W1000/W999/W998 target surjective-compact\
      recovery after W981 constructs the W971 component-field surface"
  exactAtResult :=
    "proved: the W1001 W981 endpoint/unit-strict-exact provider surface feeds\
      the W1000/W999/W998/W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/\
      W983/W982/W981/W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/\
      W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/\
      W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := unitStrictExactIsoDataInputNamesW1001
  productSuccessClaimed := false

theorem currentW1001UnitStrictExactIsoDataRoute_productSuccess :
    (let state := currentMetrizableUnitStrictExactIsoDataRouteStateW1001;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
