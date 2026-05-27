import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromCurrentFullDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataNormalizedSourceTriangulationDataClosedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsRoute

/-!
W1000 replaces W999's remaining W977 current full-data provider by the W971
component-field surface. W978 already constructs W977 from W971 component
fields, and W1000 feeds that constructed current full data into W999.
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

/-- W1000 constructs W977 current full data from W971 component fields through W978. -/
def currentFullDataOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointLocalizedUnitDataProviderW977 :=
  fullDataOfComponentFieldsW978 leaves

/-- W1000 constructs W987 branch full data through W999 after W978 builds W977. -/
noncomputable def branchFullDataOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  branchFullDataOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

/-- W1000 recovers W715 target surjective-compact data from W971 component fields. -/
noncomputable def targetSurjectiveCompactDataOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

/-- W1000 builds W997's branch-full-data surface from W971 component fields. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997
    where
  targetSurjectiveCompactData :=
    targetSurjectiveCompactDataOfComponentFieldsW1000 leaves
  branchFullData := branchFullDataOfComponentFieldsW1000 leaves

/-- W1000 builds the W995 target-provider surface through W999. -/
noncomputable def targetProviderDataOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

/-- W1000 builds the W994 normalized-source/endpoint route data through W999. -/
noncomputable def normalizedSourceEndpointDataOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

/-- W1000 returns the constructed W987 branch full data through W999. -/
noncomputable def fullDataOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

/- W1000 exposes W981 leaves through W999. -/
noncomputable def w981LeavesOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

/- W1000 exposes W971 component fields through W999. -/
noncomputable def componentFieldsOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

/-- W1000 reconstructs endpoint strict exactness through W999. -/
noncomputable def endpointStrictExactOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

/-- W1000 derives unit mapping-cone algebraic exactness through W999. -/
noncomputable def unitMappingConeAlgebraicExactOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfComponentFieldsW1000 leaves).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfComponentFieldsW1000 leaves).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfComponentFieldsW1000 leaves).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfComponentFieldsW1000 leaves).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

/-- W1000 reconstructs unit mapping-cone strict short exactness through W999. -/
noncomputable def unitMappingConeStrictExactOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfComponentFieldsW1000 leaves).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

/-- W1000 wraps the unit mapping-cone isomorphism through W999. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfComponentFieldsW1000 leaves).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfComponentFieldsW1000 leaves).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

theorem directBoundedLeftCalculusOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

noncomputable def boundedDerivedInfinityCategoryOfComponentFieldsW1000
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfCurrentFullDataW999
    (currentFullDataOfComponentFieldsW1000 leaves)

def componentFieldsInputNamesW1000 : List String :=
  closedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsInputNamesW978

theorem componentFieldsInputNamesW1000_count :
    componentFieldsInputNamesW1000.length = 18 :=
  closedEmbeddingEndpointLocalizedUnitFullDataFromComponentFieldsInputNamesW978_count

structure MetrizableComponentFieldsRouteStateW1000 : Type where
  seed : String
  declarations : List String
  componentFieldRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComponentFieldsRouteStateW1000 :
    MetrizableComponentFieldsRouteStateW1000
    where
  seed := "w1000-component-fields-to-current-full-data-target-compact-route"
  declarations :=
    ["currentFullDataOfComponentFieldsW1000",
      "branchFullDataOfComponentFieldsW1000",
      "targetSurjectiveCompactDataOfComponentFieldsW1000",
      "targetSurjectiveCompactBranchFullDataOfComponentFieldsW1000",
      "targetProviderDataOfComponentFieldsW1000",
      "normalizedSourceEndpointDataOfComponentFieldsW1000",
      "fullDataOfComponentFieldsW1000",
      "w981LeavesOfComponentFieldsW1000",
      "componentFieldsOfComponentFieldsW1000",
      "endpointStrictExactOfComponentFieldsW1000",
      "unitMappingConeAlgebraicExactOfComponentFieldsW1000",
      "unitMappingConeStrictExactOfComponentFieldsW1000",
      "unitMappingConeIsoNonemptyOfComponentFieldsW1000",
      "directBoundedLeftCalculusOfComponentFieldsW1000",
      "boundedDerivedInfinityCategoryOfComponentFieldsW1000",
      "componentFieldsInputNamesW1000_count"]
  componentFieldRepackagingResult :=
    "proved: W1000 constructs W977 current full data from W971 component\
      fields through W978 and feeds the W999 current-full-data route"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1000 inherits W998's W715 recovery from W944 target no-univ\
      data after W978/W999 construct W977 and W987 from W971 component fields"
  exactAtResult :=
    "proved: the W1000 W971 component-field surface feeds the W999/W998/\
      W997/W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/\
      W980/W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/\
      W967/W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/\
      W953/W952 stable ExactAt route"
  remainingInputs := componentFieldsInputNamesW1000
  productSuccessClaimed := false

theorem currentW1000ComponentFieldsRoute_productSuccess :
    (let state := currentMetrizableComponentFieldsRouteStateW1000;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
