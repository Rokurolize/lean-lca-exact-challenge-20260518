import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromBranchFullDataRoute
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromLocalizedUnitChoiceRoute

/-!
W1002 replaces W1001's W981 endpoint/unit-strict-exact provider surface by the
W982 localized-unit-choice surface. W988 constructs W987 branch full data from
W982, and W1002 feeds that full data into W998.
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

/-- W1002 constructs W987 branch full data from W982 localized-unit-choice data. -/
noncomputable def branchFullDataOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfLocalizedUnitChoiceW988 localizedUnitChoiceData

/-- W1002 recovers W715 target surjective-compact data through W998. -/
noncomputable def targetSurjectiveCompactDataOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  targetSurjectiveCompactDataOfBranchFullDataW998
    (branchFullDataOfLocalizedUnitChoiceW1002 localizedUnitChoiceData)

/-- W1002 builds W997's branch-full-data surface from W982 data. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997
    where
  targetSurjectiveCompactData :=
    targetSurjectiveCompactDataOfLocalizedUnitChoiceW1002
      localizedUnitChoiceData
  branchFullData := branchFullDataOfLocalizedUnitChoiceW1002
    localizedUnitChoiceData

/-- W1002 builds the W995 target-provider surface through W998. -/
noncomputable def targetProviderDataOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfBranchFullDataW998
    (branchFullDataOfLocalizedUnitChoiceW1002 localizedUnitChoiceData)

/-- W1002 builds the W994 normalized-source/endpoint route data through W998. -/
noncomputable def normalizedSourceEndpointDataOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfBranchFullDataW998
    (branchFullDataOfLocalizedUnitChoiceW1002 localizedUnitChoiceData)

/-- W1002 returns the constructed W987 branch full data through W998. -/
noncomputable def fullDataOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfBranchFullDataW998
    (branchFullDataOfLocalizedUnitChoiceW1002 localizedUnitChoiceData)

/- W1002 exposes W977 leaves through W998. -/
noncomputable def w977LeavesOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfBranchFullDataW998
    (branchFullDataOfLocalizedUnitChoiceW1002 localizedUnitChoiceData)

/- W1002 exposes W971 component fields through W998. -/
noncomputable def componentFieldsOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfBranchFullDataW998
    (branchFullDataOfLocalizedUnitChoiceW1002 localizedUnitChoiceData)

/-- W1002 reconstructs endpoint strict exactness through W998. -/
noncomputable def endpointStrictExactOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfBranchFullDataW998
    (branchFullDataOfLocalizedUnitChoiceW1002 localizedUnitChoiceData)

/-- W1002 derives unit mapping-cone algebraic exactness through W998. -/
noncomputable def unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfLocalizedUnitChoiceW1002 localizedUnitChoiceData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfLocalizedUnitChoiceW1002 localizedUnitChoiceData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfLocalizedUnitChoiceW1002 localizedUnitChoiceData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfLocalizedUnitChoiceW1002 localizedUnitChoiceData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfBranchFullDataW998
    (branchFullDataOfLocalizedUnitChoiceW1002 localizedUnitChoiceData)

/-- W1002 reconstructs unit mapping-cone strict short exactness through W998. -/
noncomputable def unitMappingConeStrictExactOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfLocalizedUnitChoiceW1002 localizedUnitChoiceData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfBranchFullDataW998
    (branchFullDataOfLocalizedUnitChoiceW1002 localizedUnitChoiceData)

/-- W1002 wraps the unit mapping-cone isomorphism through W998. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfLocalizedUnitChoiceW1002 localizedUnitChoiceData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfLocalizedUnitChoiceW1002 localizedUnitChoiceData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfBranchFullDataW998
    (branchFullDataOfLocalizedUnitChoiceW1002 localizedUnitChoiceData)

theorem directBoundedLeftCalculusOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfBranchFullDataW998
    (branchFullDataOfLocalizedUnitChoiceW1002 localizedUnitChoiceData)

noncomputable def boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1002
    (localizedUnitChoiceData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfBranchFullDataW998
    (branchFullDataOfLocalizedUnitChoiceW1002 localizedUnitChoiceData)

def localizedUnitChoiceInputNamesW1002 : List String :=
  endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982

theorem localizedUnitChoiceInputNamesW1002_count :
    localizedUnitChoiceInputNamesW1002.length = 6 :=
  endpointStrictExactLocalizedUnitChoiceFullDataInputNamesW982_count

structure MetrizableLocalizedUnitChoiceTargetSurjectiveCompactRouteStateW1002 :
    Type where
  seed : String
  declarations : List String
  localizedUnitChoiceRepackagingResult : String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableLocalizedUnitChoiceTargetSurjectiveCompactRouteStateW1002 :
    MetrizableLocalizedUnitChoiceTargetSurjectiveCompactRouteStateW1002
    where
  seed := "w1002-localized-unit-choice-to-target-surjective-compact-route"
  declarations :=
    ["branchFullDataOfLocalizedUnitChoiceW1002",
      "targetSurjectiveCompactDataOfLocalizedUnitChoiceW1002",
      "targetSurjectiveCompactBranchFullDataOfLocalizedUnitChoiceW1002",
      "targetProviderDataOfLocalizedUnitChoiceW1002",
      "normalizedSourceEndpointDataOfLocalizedUnitChoiceW1002",
      "fullDataOfLocalizedUnitChoiceW1002",
      "w977LeavesOfLocalizedUnitChoiceW1002",
      "componentFieldsOfLocalizedUnitChoiceW1002",
      "endpointStrictExactOfLocalizedUnitChoiceW1002",
      "unitMappingConeAlgebraicExactOfLocalizedUnitChoiceW1002",
      "unitMappingConeStrictExactOfLocalizedUnitChoiceW1002",
      "unitMappingConeIsoNonemptyOfLocalizedUnitChoiceW1002",
      "directBoundedLeftCalculusOfLocalizedUnitChoiceW1002",
      "boundedDerivedInfinityCategoryOfLocalizedUnitChoiceW1002",
      "localizedUnitChoiceInputNamesW1002_count"]
  localizedUnitChoiceRepackagingResult :=
    "proved: W1002 constructs W987 branch full data from W982 localized-unit\
      choice data through W988 and feeds W998"
  targetSurjectiveCompactRecoveryResult :=
    "proved: W1002 inherits W998 target surjective-compact recovery from the\
      W987 branch full data constructed by W988"
  exactAtResult :=
    "proved: the W1002 W982 localized-unit-choice surface feeds W998/W997/\
      W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/\
      W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/\
      W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := localizedUnitChoiceInputNamesW1002
  productSuccessClaimed := false

theorem currentW1002LocalizedUnitChoiceRoute_productSuccess :
    (let state :=
        currentMetrizableLocalizedUnitChoiceTargetSurjectiveCompactRouteStateW1002;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
