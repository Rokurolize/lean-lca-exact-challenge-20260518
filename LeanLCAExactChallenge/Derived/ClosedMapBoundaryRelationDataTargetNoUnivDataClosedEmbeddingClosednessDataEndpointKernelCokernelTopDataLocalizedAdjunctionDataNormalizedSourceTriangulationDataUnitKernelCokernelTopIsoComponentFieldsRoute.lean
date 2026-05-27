import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsRoute

/-!
W975 feeds the W974 endpoint-kernel/cokernel-top-data route while replacing the
localized right adjoint and its adjunction by one localized-adjunction provider.
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
W975 localized-adjunction provider: package the localized right adjoint and
the adjunction consumed separately by W974.
-/
structure BoundedHomotopyLocalizedAdjunctionDataProviderW975 : Type 2 where
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint

/-- W975 projects the localized right adjoint. -/
def boundedHomotopyLocalizedRightAdjointOfLocalizedAdjunctionDataW975
    (localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975) :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedAdjunctionData.boundedHomotopyLocalizedRightAdjoint

/-- W975 projects the localized adjunction. -/
def boundedHomotopyLocalizedAdjunctionOfLocalizedAdjunctionDataW975
    (localizedAdjunctionData :
      BoundedHomotopyLocalizedAdjunctionDataProviderW975) :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjointOfLocalizedAdjunctionDataW975
        localizedAdjunctionData :=
  localizedAdjunctionData.boundedHomotopyLocalizedAdjunction

/--
W975 preserves the W974 field surface while replacing the localized adjoint and
adjunction fields by one localized-adjunction data provider.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975 :
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

/- W975 builds the W974 leaves consumed by the endpoint-data route. -/
def w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetNoUnivData := leaves.targetNoUnivData
  closedEmbeddingClosednessData := leaves.closedEmbeddingClosednessData
  endpointKernelCokernelTopData := leaves.endpointKernelCokernelTopData
  normalizedSourceTriangulationData :=
    leaves.normalizedSourceTriangulationData
  boundedHomotopyLocalizedRightAdjoint :=
    boundedHomotopyLocalizedRightAdjointOfLocalizedAdjunctionDataW975
      leaves.localizedAdjunctionData
  boundedHomotopyLocalizedAdjunction :=
    boundedHomotopyLocalizedAdjunctionOfLocalizedAdjunctionDataW975
      leaves.localizedAdjunctionData
  unitMappingConeModel := leaves.unitMappingConeModel
  unitMappingConeClosedEmbedding := leaves.unitMappingConeClosedEmbedding
  unitMappingConeOpenMap := leaves.unitMappingConeOpenMap
  unitMappingConeCokernelTop := leaves.unitMappingConeCokernelTop
  unitMappingConeKernelEquality := leaves.unitMappingConeKernelEquality
  unitMappingConeIso := leaves.unitMappingConeIso

/-- W975 reconstructs endpoint strict short exactness through W974. -/
def endpointStrictExactOfLocalizedAdjunctionDataW975
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfEndpointKernelCokernelTopDataW974
    (w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
      leaves)

/-- W975 derives unit mapping-cone algebraic exactness through W974. -/
def unitMappingConeAlgebraicExactOfLocalizedAdjunctionDataW975
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((leaves.unitMappingConeModel X).as.sc i).X₂),
        ((leaves.unitMappingConeModel X).as.sc i).g x₂ = 0 →
          ∃ x₁ : ((leaves.unitMappingConeModel X).as.sc i).X₁,
            ((leaves.unitMappingConeModel X).as.sc i).f x₁ = x₂ :=
  unitMappingConeAlgebraicExactOfUnitKernelEqualityW974
    (w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
      leaves)

/-- W975 reconstructs unit mapping-cone strict short exactness through W974. -/
def unitMappingConeStrictExactOfLocalizedAdjunctionDataW975
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact ((leaves.unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfUnitKernelCokernelTopW974
    (w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
      leaves)

/-- W975 wraps the chosen unit mapping-cone isomorphism through W974. -/
@[reducible]
def unitMappingConeIsoNonemptyOfLocalizedAdjunctionDataW975
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((boundedHomotopyLocalizedAdjunctionOfLocalizedAdjunctionDataW975
                  leaves.localizedAdjunctionData).unit.app X)))) ≅
          leaves.unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfUnitIsoChoiceW974
    (w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
      leaves)

theorem directBoundedLeftCalculusOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
    (w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975 leaves)

noncomputable def boundedDerivedInfinityCategoryOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW975) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
    (w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975 leaves)

/--
W975 records the W974 surface with localized right-adjoint/adjunction fields
consolidated into one localized-adjunction data provider.
-/
def closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW975 :
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
    "unit mapping-cone model in the homotopy category for every bounded complex",
    "unit mapping-cone degreewise closed-embedding components",
    "unit mapping-cone degreewise open-map components",
    "unit mapping-cone degreewise cokernel-subgroup-top components",
    "unit mapping-cone degreewise kernel-equality components",
    "chosen unit mapping-cone isomorphism from the adjunction-unit mapping cone\
      to the chosen model"]

theorem closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW975_count :
    closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW975.length =
      12 :=
  rfl

/-- Current checked W975 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW975 :
    Type where
  seed : String
  declarations : List String
  localizedAdjunctionDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW975 :
    MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW975
    where
  seed :=
    "w975-localized-adjunction-data-boundary-relation-target-no-univ-closed-\
      embedding-closedness-data-endpoint-kernel-cokernel-top-data-normalized-\
      source-triangulation-data-unit-kernel-cokernel-top-iso-component-fields"
  declarations :=
    ["BoundedHomotopyLocalizedAdjunctionDataProviderW975",
      "boundedHomotopyLocalizedRightAdjointOfLocalizedAdjunctionDataW975",
      "boundedHomotopyLocalizedAdjunctionOfLocalizedAdjunctionDataW975",
      "w974LeavesOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975",
      "endpointStrictExactOfLocalizedAdjunctionDataW975",
      "unitMappingConeAlgebraicExactOfLocalizedAdjunctionDataW975",
      "unitMappingConeStrictExactOfLocalizedAdjunctionDataW975",
      "unitMappingConeIsoNonemptyOfLocalizedAdjunctionDataW975",
      "directBoundedLeftCalculusOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975",
      "boundedDerivedInfinityCategoryOfLocalizedAdjunctionDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW975",
      "closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW975",
      "closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW975_count"]
  localizedAdjunctionDataResult :=
    "proved: W975 projects localized-adjunction data into the localized right\
      adjoint and adjunction consumed by W974"
  exactAtResult :=
    "proved: the W975 localized-adjunction-data endpoint-kernel/cokernel-top\
      closed-embedding-closedness-data target-no-univ boundary-relation\
      normalized-source unit-kernel/cokernel-top iso component field surface\
      feeds the W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/\
      W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  refinedInputs :=
    ["localized right adjoint and localized adjunction fields replaced by W975\
      localized-adjunction data",
      "unit mapping-cone model/component/isomorphism fields remain explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW975
  productSuccessClaimed := false

theorem currentW975ClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopLocalizedAdjunctionUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataLocalizedAdjunctionDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW975;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
