import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsRoute

/-!
W976 feeds the W975 localized-adjunction route while replacing the unit
mapping-cone model, component, and chosen-isomorphism fields by one dependent
unit mapping-cone data provider.
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

/--
W976 unit mapping-cone data provider: package the chosen model, four
degreewise strictness/kernal-cokernel fields, and the chosen mapping-cone
isomorphism relative to W975 localized-adjunction data.
-/
structure UnitMappingConeKernelCokernelTopIsoDataProviderW976
    (localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975) :
    Type 2 where
  unitMappingConeModel :
    UnitMappingConeModelW962
  unitMappingConeClosedEmbedding :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsClosedEmbedding (((unitMappingConeModel X).as.sc i).f :
        ((unitMappingConeModel X).as.sc i).X₁ →
          ((unitMappingConeModel X).as.sc i).X₂)
  unitMappingConeOpenMap :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsOpenMap (((unitMappingConeModel X).as.sc i).g :
        ((unitMappingConeModel X).as.sc i).X₂ →
          ((unitMappingConeModel X).as.sc i).X₃)
  unitMappingConeCokernelTop :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.cokernelSubgroup (((unitMappingConeModel X).as.sc i).g) =
        ⊤
  unitMappingConeKernelEquality :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((unitMappingConeModel X).as.sc i).X₂),
        ((unitMappingConeModel X).as.sc i).g x₂ = 0 ↔
          ∃ x₁ : ((unitMappingConeModel X).as.sc i).X₁,
            ((unitMappingConeModel X).as.sc i).f x₁ = x₂
  unitMappingConeIso :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
              ((boundedHomotopyLocalizedAdjunctionOfLocalizedAdjunctionDataW975
                localizedAdjunctionData).unit.app X)))) ≅
        unitMappingConeModel X)

/-- W976 projects the chosen unit mapping-cone model. -/
def unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeKernelCokernelTopIsoDataProviderW976
        localizedAdjunctionData) :
    UnitMappingConeModelW962 :=
  unitData.unitMappingConeModel

/-- W976 projects unit mapping-cone closed-embedding components. -/
def unitMappingConeClosedEmbeddingOfUnitKernelCokernelTopIsoDataW976
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeKernelCokernelTopIsoDataProviderW976
        localizedAdjunctionData) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsClosedEmbedding (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData X).as.sc i).f :
        ((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData X).as.sc i).X₁ →
          ((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData X).as.sc i).X₂) :=
  unitData.unitMappingConeClosedEmbedding

/-- W976 projects unit mapping-cone open-map components. -/
def unitMappingConeOpenMapOfUnitKernelCokernelTopIsoDataW976
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeKernelCokernelTopIsoDataProviderW976
        localizedAdjunctionData) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      IsOpenMap (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData X).as.sc i).g :
        ((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData X).as.sc i).X₂ →
          ((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData X).as.sc i).X₃) :=
  unitData.unitMappingConeOpenMap

/-- W976 projects unit mapping-cone cokernel-top components. -/
def unitMappingConeCokernelTopOfUnitKernelCokernelTopIsoDataW976
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeKernelCokernelTopIsoDataProviderW976
        localizedAdjunctionData) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.cokernelSubgroup
          (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData X).as.sc i).g) =
        ⊤ :=
  unitData.unitMappingConeCokernelTop

/-- W976 projects unit mapping-cone kernel-equality components. -/
def unitMappingConeKernelEqualityOfUnitKernelCokernelTopIsoDataW976
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeKernelCokernelTopIsoDataProviderW976
        localizedAdjunctionData) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData X).as.sc i).X₂),
        ((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData X).as.sc i).g x₂ = 0 ↔
          ∃ x₁ : ((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData X).as.sc i).X₁,
            ((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData X).as.sc i).f x₁ = x₂ :=
  unitData.unitMappingConeKernelEquality

/-- W976 projects the chosen unit mapping-cone isomorphism. -/
def unitMappingConeIsoOfUnitKernelCokernelTopIsoDataW976
    {localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975}
    (unitData :
      UnitMappingConeKernelCokernelTopIsoDataProviderW976
        localizedAdjunctionData) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
              ((boundedHomotopyLocalizedAdjunctionOfLocalizedAdjunctionDataW975
                localizedAdjunctionData).unit.app X)))) ≅
        unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976 unitData X) :=
  unitData.unitMappingConeIso

/--
W976 preserves the W975 field surface while replacing unit mapping-cone fields
by one dependent unit mapping-cone data provider.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataLeavesW976 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973
  endpointKernelCokernelTopData :
    EndpointKernelCokernelTopDataProviderW974
  localizedAdjunctionData :
    BoundedHomotopyLocalizedAdjunctionDataProviderW975
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948
  unitKernelCokernelTopIsoData :
    UnitMappingConeKernelCokernelTopIsoDataProviderW976
      localizedAdjunctionData

/- W976 builds the W975 leaves consumed by the localized-adjunction route. -/
def w975LeavesOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataLeavesW976) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetNoUnivData := leaves.targetNoUnivData
  closedEmbeddingClosednessData := leaves.closedEmbeddingClosednessData
  endpointKernelCokernelTopData := leaves.endpointKernelCokernelTopData
  localizedAdjunctionData := leaves.localizedAdjunctionData
  normalizedSourceTriangulationData :=
    leaves.normalizedSourceTriangulationData
  unitMappingConeModel :=
    unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
      leaves.unitKernelCokernelTopIsoData
  unitMappingConeClosedEmbedding :=
    unitMappingConeClosedEmbeddingOfUnitKernelCokernelTopIsoDataW976
      leaves.unitKernelCokernelTopIsoData
  unitMappingConeOpenMap :=
    unitMappingConeOpenMapOfUnitKernelCokernelTopIsoDataW976
      leaves.unitKernelCokernelTopIsoData
  unitMappingConeCokernelTop :=
    unitMappingConeCokernelTopOfUnitKernelCokernelTopIsoDataW976
      leaves.unitKernelCokernelTopIsoData
  unitMappingConeKernelEquality :=
    unitMappingConeKernelEqualityOfUnitKernelCokernelTopIsoDataW976
      leaves.unitKernelCokernelTopIsoData
  unitMappingConeIso :=
    unitMappingConeIsoOfUnitKernelCokernelTopIsoDataW976
      leaves.unitKernelCokernelTopIsoData

/-- W976 reconstructs endpoint strict short exactness through W975. -/
def endpointStrictExactOfUnitKernelCokernelTopIsoDataW976
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataLeavesW976) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfLocalizedAdjunctionDataW975
    (w975LeavesOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976
      leaves)

/-- W976 derives unit mapping-cone algebraic exactness through W975. -/
def unitMappingConeAlgebraicExactOfUnitKernelCokernelTopIsoDataW976
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataLeavesW976) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
        leaves.unitKernelCokernelTopIsoData) X).as.sc i).X₂),
        (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
          leaves.unitKernelCokernelTopIsoData) X).as.sc i).g x₂ = 0 →
          ∃ x₁ : (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
            leaves.unitKernelCokernelTopIsoData) X).as.sc i).X₁,
            (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
              leaves.unitKernelCokernelTopIsoData) X).as.sc i).f x₁ = x₂ :=
  unitMappingConeAlgebraicExactOfLocalizedAdjunctionDataW975
    (w975LeavesOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976
      leaves)

/-- W976 reconstructs unit mapping-cone strict short exactness through W975. -/
def unitMappingConeStrictExactOfUnitKernelCokernelTopIsoDataW976
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataLeavesW976) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
          leaves.unitKernelCokernelTopIsoData) X).as.sc i) :=
  unitMappingConeStrictExactOfLocalizedAdjunctionDataW975
    (w975LeavesOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976
      leaves)

/-- W976 wraps the chosen unit mapping-cone isomorphism through W975. -/
@[reducible]
def unitMappingConeIsoNonemptyOfUnitKernelCokernelTopIsoDataW976
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataLeavesW976) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((boundedHomotopyLocalizedAdjunctionOfLocalizedAdjunctionDataW975
                  leaves.localizedAdjunctionData).unit.app X)))) ≅
          unitMappingConeModelOfUnitKernelCokernelTopIsoDataW976
            leaves.unitKernelCokernelTopIsoData X) :=
  unitMappingConeIsoNonemptyOfLocalizedAdjunctionDataW975
    (w975LeavesOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976
      leaves)

theorem directBoundedLeftCalculusOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataLeavesW976) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
    (w975LeavesOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976 leaves)

noncomputable def boundedDerivedInfinityCategoryOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataLeavesW976) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
    (w975LeavesOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976 leaves)

/--
W976 records the W975 surface with the unit mapping-cone model/component and
chosen isomorphism fields consolidated into one dependent provider.
-/
def closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataInputNamesW976 :
    List String :=
  ["W730 boundary/relation data provider: W716 WPP-limit boundary data and\
      W717 closed-natural-transformation relation data",
    "W944 target no-univ data provider: target-difference preimage surjectivity\
      and target-codomain compact no-univ membership data for every target\
      diagram",
    "W973 closed-embedding closedness data provider: W718 selected-difference\
      closed-embedding components and W519 mapped explicit cokernel\
      closed-embedding provider",
    "W974 endpoint kernel/cokernel-top data provider: endpoint closed\
      embeddings, open maps, cokernel-top witnesses, and kernel equalities",
    "W975 localized-adjunction data provider: localized right adjoint and\
      adjunction for the bounded homotopy localized Verdier functor",
    "W948 normalized-source-triangulation data provider: W719 normalized\
      fixed-target data and W722 source-side triangulation data",
    "W976 unit mapping-cone kernel/cokernel-top iso data provider: chosen model,\
      degreewise closed/open/kernel/cokernel fields, and chosen isomorphism"]

theorem closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataInputNamesW976_count :
    closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataInputNamesW976.length =
      7 :=
  rfl

/-- Current checked W976 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataRouteStateW976 :
    Type where
  seed : String
  declarations : List String
  unitDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataRouteStateW976 :
    MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataRouteStateW976
    where
  seed :=
    "w976-unit-kernel-cokernel-top-iso-data-boundary-relation-target-no-univ-\
      closed-embedding-closedness-data-endpoint-kernel-cokernel-top-data-\
      localized-adjunction-data-normalized-source-triangulation-data"
  declarations :=
    ["UnitMappingConeKernelCokernelTopIsoDataProviderW976",
      "w975LeavesOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976",
      "endpointStrictExactOfUnitKernelCokernelTopIsoDataW976",
      "unitMappingConeAlgebraicExactOfUnitKernelCokernelTopIsoDataW976",
      "unitMappingConeStrictExactOfUnitKernelCokernelTopIsoDataW976",
      "unitMappingConeIsoNonemptyOfUnitKernelCokernelTopIsoDataW976",
      "directBoundedLeftCalculusOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976",
      "boundedDerivedInfinityCategoryOfUnitKernelCokernelTopIsoDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataW976",
      "closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataInputNamesW976",
      "closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataInputNamesW976_count"]
  unitDataResult :=
    "proved: W976 projects dependent unit mapping-cone kernel/cokernel-top iso\
      data into the six unit mapping-cone fields consumed by W975"
  exactAtResult :=
    "proved: the W976 unit mapping-cone data localized-adjunction endpoint-\
      kernel/cokernel-top closed-embedding-closedness-data target-no-univ\
      boundary-relation normalized-source field surface feeds the W975/W974/\
      W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/W962/W961/W959/\
      W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  refinedInputs :=
    ["unit mapping-cone model, degreewise closed/open/kernel/cokernel fields,\
      and chosen isomorphism replaced by W976 unit mapping-cone data",
      "boundary/relation, target no-univ, closed-embedding closedness, endpoint,\
      localized-adjunction, and normalized-source data remain explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataInputNamesW976
  productSuccessClaimed := false

theorem currentW976ClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopIsoBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoDataRouteStateW976;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
