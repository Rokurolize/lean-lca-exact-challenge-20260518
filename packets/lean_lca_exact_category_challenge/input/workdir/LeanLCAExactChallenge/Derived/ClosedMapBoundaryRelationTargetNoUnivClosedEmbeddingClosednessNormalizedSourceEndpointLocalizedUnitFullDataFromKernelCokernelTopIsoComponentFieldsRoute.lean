import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromPrimitiveUnitComponentsRoute

/-!
W991 opens W990's endpoint strict-exact family and W939 unit-component witness
into endpoint kernel/cokernel-top data plus unit kernel/cokernel-top/isomorphism
component fields.
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
W991 constructs the W939 unit-component witness from the W974-style unit
mapping-cone component fields.
-/
def unitComponentsOfKernelCokernelTopIsoComponentFieldsW991
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      leaves.boundedHomotopyLocalizedRightAdjoint
      leaves.boundedHomotopyLocalizedAdjunction := by
  intro X
  exact
    ⟨leaves.unitMappingConeModel X,
      leaves.unitMappingConeClosedEmbedding X,
      leaves.unitMappingConeOpenMap X,
      fun i =>
        MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap
          (((leaves.unitMappingConeModel X).as.sc i).g)
          (leaves.unitMappingConeCokernelTop X i)
          (leaves.unitMappingConeOpenMap X i),
      fun i x₂ hx₂ => (leaves.unitMappingConeKernelEquality X i x₂).mp hx₂,
      ⟨leaves.unitMappingConeIso X⟩⟩

/-- W991 constructs the W990 primitive-unit-component provider from W974 data. -/
def primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetNoUnivData := leaves.targetNoUnivData
  closedEmbeddingClosednessData := leaves.closedEmbeddingClosednessData
  endpointStrictExact :=
    endpointStrictExactOfEndpointKernelCokernelTopDataW974 leaves
  boundedHomotopyLocalizedRightAdjoint :=
    leaves.boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedAdjunction :=
    leaves.boundedHomotopyLocalizedAdjunction
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    unitComponentsOfKernelCokernelTopIsoComponentFieldsW991 leaves
  normalizedSourceTriangulationData :=
    leaves.normalizedSourceTriangulationData

/-- W991 constructs W987 full data through the W990 route. -/
noncomputable def fullDataOfKernelCokernelTopIsoComponentFieldsW991
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfPrimitiveUnitComponentsW990
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
      leaves)

/- W991 feeds W990 after reconstructing endpoint strictness and unit components. -/
noncomputable def w981LeavesOfKernelCokernelTopIsoComponentFieldsW991
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfPrimitiveUnitComponentsW990
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
      leaves)

/- W991 exposes the W971 component-field split obtained through W990. -/
noncomputable def componentFieldsOfKernelCokernelTopIsoComponentFieldsW991
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfPrimitiveUnitComponentsW990
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
      leaves)

/-- W991 reconstructs endpoint strict short exactness through W990. -/
noncomputable def endpointStrictExactOfKernelCokernelTopIsoComponentFieldsW991
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfPrimitiveUnitComponentsW990
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
      leaves)

/-- W991 derives unit mapping-cone algebraic exactness through W990. -/
noncomputable def unitMappingConeAlgebraicExactOfKernelCokernelTopIsoComponentFieldsW991
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfKernelCokernelTopIsoComponentFieldsW991 leaves).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfKernelCokernelTopIsoComponentFieldsW991 leaves).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfKernelCokernelTopIsoComponentFieldsW991 leaves).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfKernelCokernelTopIsoComponentFieldsW991 leaves).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfPrimitiveUnitComponentsW990
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
      leaves)

/-- W991 reconstructs unit mapping-cone strict short exactness through W990. -/
noncomputable def unitMappingConeStrictExactOfKernelCokernelTopIsoComponentFieldsW991
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfKernelCokernelTopIsoComponentFieldsW991 leaves).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfPrimitiveUnitComponentsW990
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
      leaves)

/-- W991 wraps the unit mapping-cone isomorphism through W990. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfKernelCokernelTopIsoComponentFieldsW991
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfKernelCokernelTopIsoComponentFieldsW991 leaves).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfKernelCokernelTopIsoComponentFieldsW991 leaves).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfPrimitiveUnitComponentsW990
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
      leaves)

theorem directBoundedLeftCalculusOfKernelCokernelTopIsoComponentFieldsW991
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfPrimitiveUnitComponentsW990
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
      leaves)

noncomputable def boundedDerivedInfinityCategoryOfKernelCokernelTopIsoComponentFieldsW991
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfPrimitiveUnitComponentsW990
    (primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991
      leaves)

def kernelCokernelTopIsoComponentFieldsInputNamesW991 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "W974 endpoint kernel/cokernel-top data provider",
    "W948 normalized-source-triangulation data provider",
    "bounded homotopy localized right adjoint",
    "bounded homotopy localized adjunction",
    "unit mapping-cone model",
    "unit mapping-cone closed-embedding components",
    "unit mapping-cone open-map components",
    "unit mapping-cone cokernel-subgroup-top components",
    "unit mapping-cone kernel-equality components",
    "chosen unit mapping-cone isomorphism"]

theorem kernelCokernelTopIsoComponentFieldsInputNamesW991_count :
    kernelCokernelTopIsoComponentFieldsInputNamesW991.length = 13 :=
  rfl

structure MetrizableKernelCokernelTopIsoComponentFieldsRouteStateW991 :
    Type where
  seed : String
  declarations : List String
  kernelCokernelConstructionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableKernelCokernelTopIsoComponentFieldsRouteStateW991 :
    MetrizableKernelCokernelTopIsoComponentFieldsRouteStateW991
    where
  seed := "w991-kernel-cokernel-top-iso-component-fields-to-w990-route"
  declarations :=
    ["unitComponentsOfKernelCokernelTopIsoComponentFieldsW991",
      "primitiveUnitComponentsDataOfKernelCokernelTopIsoComponentFieldsW991",
      "fullDataOfKernelCokernelTopIsoComponentFieldsW991",
      "w981LeavesOfKernelCokernelTopIsoComponentFieldsW991",
      "componentFieldsOfKernelCokernelTopIsoComponentFieldsW991",
      "endpointStrictExactOfKernelCokernelTopIsoComponentFieldsW991",
      "unitMappingConeAlgebraicExactOfKernelCokernelTopIsoComponentFieldsW991",
      "unitMappingConeStrictExactOfKernelCokernelTopIsoComponentFieldsW991",
      "unitMappingConeIsoNonemptyOfKernelCokernelTopIsoComponentFieldsW991",
      "directBoundedLeftCalculusOfKernelCokernelTopIsoComponentFieldsW991",
      "boundedDerivedInfinityCategoryOfKernelCokernelTopIsoComponentFieldsW991",
      "kernelCokernelTopIsoComponentFieldsInputNamesW991_count"]
  kernelCokernelConstructionResult :=
    "proved: W991 constructs W990 endpoint strict-exact data from W974\
      endpoint kernel/cokernel-top data and constructs the W939 unit-component\
      witness from unit kernel/cokernel-top/isomorphism component fields"
  exactAtResult :=
    "proved: the W991 kernel/cokernel-top component-field surface feeds the\
      W990/W989/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/\
      W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/\
      W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable\
      ExactAt route"
  remainingInputs := kernelCokernelTopIsoComponentFieldsInputNamesW991
  productSuccessClaimed := false

theorem currentW991KernelCokernelTopIsoComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableKernelCokernelTopIsoComponentFieldsRouteStateW991;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
