import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationDataTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopAndUnitKernelCokernelTopIsoComponentFieldsRoute

/-!
W974 feeds the W973 closed-embedding-closedness-data route while replacing the
four endpoint kernel/cokernel-top fields by one endpoint data provider.
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
W974 endpoint kernel/cokernel-top provider: package the endpoint closed
embedding, open map, cokernel-top, and kernel-equality fields consumed by W973.
-/
structure EndpointKernelCokernelTopDataProviderW974 : Type 2 where
  endpointClosedEmbedding :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)
  endpointOpenMap :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃)
  endpointCokernelTop :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.cokernelSubgroup (K.sc i).g = ⊤
  endpointKernelEquality :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
      (x₂ : (K.sc i).X₂),
        (K.sc i).g x₂ = 0 ↔
          ∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂

/-- W974 projects endpoint closed-embedding witnesses. -/
def endpointClosedEmbeddingOfEndpointKernelCokernelTopDataW974
    (endpointData : EndpointKernelCokernelTopDataProviderW974) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂) :=
  endpointData.endpointClosedEmbedding

/-- W974 projects endpoint open-map witnesses. -/
def endpointOpenMapOfEndpointKernelCokernelTopDataW974
    (endpointData : EndpointKernelCokernelTopDataProviderW974) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃) :=
  endpointData.endpointOpenMap

/-- W974 projects endpoint cokernel-top witnesses. -/
def endpointCokernelTopOfEndpointKernelCokernelTopDataW974
    (endpointData : EndpointKernelCokernelTopDataProviderW974) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.cokernelSubgroup (K.sc i).g = ⊤ :=
  endpointData.endpointCokernelTop

/-- W974 projects endpoint kernel-equality witnesses. -/
def endpointKernelEqualityOfEndpointKernelCokernelTopDataW974
    (endpointData : EndpointKernelCokernelTopDataProviderW974) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ)
      (x₂ : (K.sc i).X₂),
        (K.sc i).g x₂ = 0 ↔
          ∃ x₁ : (K.sc i).X₁, (K.sc i).f x₁ = x₂ :=
  endpointData.endpointKernelEquality

/--
W974 preserves the W973 field surface while replacing endpoint kernel/cokernel
topology fields by one endpoint data provider.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
  closedEmbeddingClosednessData :
    ClosedEmbeddingClosednessDataProviderW973
  endpointKernelCokernelTopData :
    EndpointKernelCokernelTopDataProviderW974
  normalizedSourceTriangulationData :
    NormalizedFixedTargetSourceTriangulationDataProviderW948
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
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
              (boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
        unitMappingConeModel X)

/- W974 builds the W973 leaves consumed by the closed-embedding data route. -/
def w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW973
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetNoUnivData := leaves.targetNoUnivData
  closedEmbeddingClosednessData := leaves.closedEmbeddingClosednessData
  normalizedSourceTriangulationData :=
    leaves.normalizedSourceTriangulationData
  endpointClosedEmbedding :=
    endpointClosedEmbeddingOfEndpointKernelCokernelTopDataW974
      leaves.endpointKernelCokernelTopData
  endpointOpenMap :=
    endpointOpenMapOfEndpointKernelCokernelTopDataW974
      leaves.endpointKernelCokernelTopData
  endpointCokernelTop :=
    endpointCokernelTopOfEndpointKernelCokernelTopDataW974
      leaves.endpointKernelCokernelTopData
  endpointKernelEquality :=
    endpointKernelEqualityOfEndpointKernelCokernelTopDataW974
      leaves.endpointKernelCokernelTopData
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  unitMappingConeModel := leaves.unitMappingConeModel
  unitMappingConeClosedEmbedding := leaves.unitMappingConeClosedEmbedding
  unitMappingConeOpenMap := leaves.unitMappingConeOpenMap
  unitMappingConeCokernelTop := leaves.unitMappingConeCokernelTop
  unitMappingConeKernelEquality := leaves.unitMappingConeKernelEquality
  unitMappingConeIso := leaves.unitMappingConeIso

/-- W974 reconstructs endpoint strict short exactness from endpoint data. -/
def endpointStrictExactOfEndpointKernelCokernelTopDataW974
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) := by
  intro K i
  exact
    MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
      (endpointKernelEqualityOfEndpointKernelCokernelTopDataW974
        leaves.endpointKernelCokernelTopData K i)
      (endpointClosedEmbeddingOfEndpointKernelCokernelTopDataW974
        leaves.endpointKernelCokernelTopData K i)
      (endpointOpenMapOfEndpointKernelCokernelTopDataW974
        leaves.endpointKernelCokernelTopData K i)
      (endpointCokernelTopOfEndpointKernelCokernelTopDataW974
        leaves.endpointKernelCokernelTopData K i)

/-- W974 derives unit mapping-cone algebraic exactness through W973. -/
def unitMappingConeAlgebraicExactOfUnitKernelEqualityW974
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ : ((leaves.unitMappingConeModel X).as.sc i).X₂),
        ((leaves.unitMappingConeModel X).as.sc i).g x₂ = 0 →
          ∃ x₁ : ((leaves.unitMappingConeModel X).as.sc i).X₁,
            ((leaves.unitMappingConeModel X).as.sc i).f x₁ = x₂ :=
  unitMappingConeAlgebraicExactOfUnitKernelEqualityW973
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
      leaves)

/-- W974 reconstructs unit mapping-cone strict short exactness through W973. -/
def unitMappingConeStrictExactOfUnitKernelCokernelTopW974
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact ((leaves.unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfUnitKernelCokernelTopW973
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
      leaves)

/-- W974 wraps a chosen unit mapping-cone isomorphism through W973. -/
@[reducible]
def unitMappingConeIsoNonemptyOfUnitIsoChoiceW974
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                (leaves.boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          leaves.unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfUnitIsoChoiceW973
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
      leaves)

/-- W974 builds the W972 leaves through W973. -/
def w972LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW972 :=
  w972LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974 leaves)

/-- W974 builds the W971 leaves through W973. -/
def w971LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  w971LeavesOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974 leaves)

theorem directBoundedLeftCalculusOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974 leaves)

noncomputable def boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingClosednessDataBoundaryRelationTargetNoUnivDataNormalizedSourceTriangulationDataEndpointKernelCokernelTopUnitKernelCokernelTopIsoComponentFieldsW973
    (w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974 leaves)

/--
W974 records the W973 surface with endpoint kernel/cokernel-top fields
consolidated into one endpoint data provider.
-/
def closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW974 :
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
    "W948 normalized-source-triangulation data provider: W719 normalized\
      fixed-target data and W722 source-side triangulation data",
    "right adjoint to the bounded homotopy localized Verdier functor",
    "adjunction for the bounded homotopy localized Verdier functor",
    "unit mapping-cone model in the homotopy category for every bounded complex",
    "unit mapping-cone degreewise closed-embedding components",
    "unit mapping-cone degreewise open-map components",
    "unit mapping-cone degreewise cokernel-subgroup-top components",
    "unit mapping-cone degreewise kernel-equality components",
    "chosen unit mapping-cone isomorphism from the adjunction-unit mapping cone\
      to the chosen model"]

theorem closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW974_count :
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW974.length =
      13 :=
  rfl

/-- Current checked W974 state. -/
structure MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW974 :
    Type where
  seed : String
  declarations : List String
  endpointDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW974 :
    MetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW974
    where
  seed :=
    "w974-endpoint-kernel-cokernel-top-data-boundary-relation-target-no-univ-\
      closed-embedding-closedness-data-normalized-source-triangulation-data-\
      unit-kernel-cokernel-top-iso-component-fields"
  declarations :=
    ["EndpointKernelCokernelTopDataProviderW974",
      "endpointClosedEmbeddingOfEndpointKernelCokernelTopDataW974",
      "endpointOpenMapOfEndpointKernelCokernelTopDataW974",
      "endpointCokernelTopOfEndpointKernelCokernelTopDataW974",
      "endpointKernelEqualityOfEndpointKernelCokernelTopDataW974",
      "w973LeavesOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974",
      "endpointStrictExactOfEndpointKernelCokernelTopDataW974",
      "unitMappingConeAlgebraicExactOfUnitKernelEqualityW974",
      "unitMappingConeStrictExactOfUnitKernelCokernelTopW974",
      "unitMappingConeIsoNonemptyOfUnitIsoChoiceW974",
      "directBoundedLeftCalculusOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974",
      "boundedDerivedInfinityCategoryOfEndpointKernelCokernelTopDataBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataNormalizedSourceTriangulationDataUnitKernelCokernelTopIsoComponentFieldsW974",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW974",
      "closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW974_count"]
  endpointDataResult :=
    "proved: W974 projects endpoint kernel/cokernel-top data into endpoint\
      closed embedding, open map, cokernel-top, and kernel-equality fields\
      consumed by the W973 route"
  exactAtResult :=
    "proved: the W974 endpoint-data closed-embedding-closedness-data target-\
      no-univ boundary-relation normalized-source unit-kernel/cokernel-top iso\
      component field surface feeds the W973/W972/W971/W970/W969/W968/W967/\
      W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952\
      stable ExactAt route"
  refinedInputs :=
    ["endpoint closed-embedding/open-map/cokernel-top/kernel-equality fields\
      replaced by W974 endpoint kernel/cokernel-top data",
      "bounded-homotopy localized right-adjoint/adjunction fields and the\
      remaining unit mapping-cone model/component/isomorphism fields remain\
      explicit"]
  remainingInputs :=
    closedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsInputNamesW974
  productSuccessClaimed := false

theorem currentW974ClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldsRouteStateW974;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
