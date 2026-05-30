import LeanLCAExactChallenge.Derived.ClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute

/-!
W945 feeds the W944 closed-map target-no-univ route while replacing the
bounded-homotopy localized right adjoint, its adjunction, and the stronger
unit mapping-cone strict-component witness by one localized-unit data provider.
-/

set_option autoImplicit false

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

namespace Dbounded

/--
W945 localized-unit provider: package the localized right adjoint, the
localized adjunction, and the W939 component-level unit mapping-cone witness.
-/
structure
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945 :
    Type 2 where
  boundedHomotopyLocalizedRightAdjoint :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0}
  boundedHomotopyLocalizedAdjunction :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjoint
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      boundedHomotopyLocalizedRightAdjoint
      boundedHomotopyLocalizedAdjunction

/-- W945 projects the localized right adjoint. -/
def boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
    (localizedUnitData :
      BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945) :
    MorphismProperty.Localization
        ((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW) ⥤
      BoundedComplexCategory MetrizableLCA.{0} :=
  localizedUnitData.boundedHomotopyLocalizedRightAdjoint

/-- W945 projects the localized adjunction. -/
def boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
    (localizedUnitData :
      BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945) :
    boundedHomotopyLocalizedVerdierFunctor MetrizableLCA.{0} ⊣
      boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        localizedUnitData :=
  localizedUnitData.boundedHomotopyLocalizedAdjunction

/-- W945 projects the stronger W939 component-level unit witness. -/
def boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
    (localizedUnitData :
      BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945) :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsPrimitiveW939
      (boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        localizedUnitData)
      (boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
        localizedUnitData) :=
  localizedUnitData.boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents

/--
W945 derives W721's functor-category unit membership from the stronger W939
component-level unit witness by reusing the existing W936/W935/W933/W932/W931
projection chain.
-/
def boundedHomotopyLocalizedUnitMemOfLocalizedUnitDataW945
    (localizedUnitData :
      BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945) :
    (boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).functorCategory
      (BoundedComplexCategory MetrizableLCA.{0})
      (boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
        localizedUnitData).unit :=
  boundedHomotopyLocalizedUnitMemOfObjectwisePrimitiveW931
    (boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
      localizedUnitData)
    (boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
      localizedUnitData)
    (boundedHomotopyLocalizedUnitObjectwiseOfConeIsoClosurePrimitiveW932
      (boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        localizedUnitData)
      (boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
        localizedUnitData)
      (boundedHomotopyLocalizedUnitConeIsoClosureOfWitnessPrimitiveW933
        (boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
          localizedUnitData)
        (boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
          localizedUnitData)
        (boundedHomotopyLocalizedUnitIsoClosureWitnessOfConflationPrimitiveW935
          (boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
            localizedUnitData)
          (boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
            localizedUnitData)
          (boundedHomotopyLocalizedEndpointShortExactUnitConflationWitnessOfStrictExactPrimitiveW936
            (boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
              localizedUnitData)
            (boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
              localizedUnitData)
            (boundedHomotopyLocalizedEndpointShortExactUnitStrictExactWitnessOfComponentsPrimitiveW939
              (boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
                localizedUnitData)
              (boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
                localizedUnitData)
              (boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
                localizedUnitData))))))

/--
W945 gives a W721 localized-right-adjoint data provider without adding W721's
unit membership as a fresh assumption.
-/
def localizedRightAdjointDataOfLocalizedUnitDataW945
    (localizedUnitData :
      BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945) :
    MetrizableWppLocalizedRightAdjointDataProviderW721
    where
  boundedHomotopyLocalizedRightAdjoint :=
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
      localizedUnitData
  boundedHomotopyLocalizedAdjunction :=
    boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
      localizedUnitData
  boundedHomotopyLocalizedUnitMem :=
    boundedHomotopyLocalizedUnitMemOfLocalizedUnitDataW945
      localizedUnitData

/--
W945 preserves W944's boundary, relation, target, closedness, normalized
fixed-target, source-triangulation, and endpoint strict-exact fields, while
bundling the localized adjoint and unit-component witness fields.
-/
structure MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945 :
    Type 2 where
  boundaryData :
    MetrizableWppLimitBoundaryDataW716
  relationData :
    ClosedNatTransOrdinaryRelationDataProviderW717
  targetNoUnivData :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944
  diagramAndMappedCokernelClosednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  normalizedFixedTargetData :
    MetrizableWppNormalizedFixedTargetDataProviderW719
  sourceTriangulationData :
    MetrizableWppSourceTriangulationDataProviderW722
  endpointStrictExact :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i)
  localizedUnitData :
    BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945

/--
W945 projects W944 leaves by unpacking the localized-unit provider.
-/
def w944LeavesOfLocalizedUnitDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactFieldsW945
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldLeavesW944
    where
  boundaryData := leaves.boundaryData
  relationData := leaves.relationData
  targetNoUnivData := leaves.targetNoUnivData
  diagramAndMappedCokernelClosednessData :=
    leaves.diagramAndMappedCokernelClosednessData
  normalizedFixedTargetData := leaves.normalizedFixedTargetData
  sourceTriangulationData := leaves.sourceTriangulationData
  endpointStrictExact := leaves.endpointStrictExact
  boundedHomotopyLocalizedRightAdjoint :=
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
      leaves.localizedUnitData
  boundedHomotopyLocalizedAdjunction :=
    boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
      leaves.localizedUnitData
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
      leaves.localizedUnitData

/-- W945 W733 concrete leaves after projecting W944 leaves. -/
def concreteLeavesOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW945
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
    (w944LeavesOfLocalizedUnitDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactFieldsW945
      leaves)

/-- W945 W732 route data after projecting W944 leaves. -/
def routeDataProviderOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW945
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
    (w944LeavesOfLocalizedUnitDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactFieldsW945
      leaves)

theorem
    directBoundedLeftCalculusOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW945
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
    (w944LeavesOfLocalizedUnitDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactFieldsW945
      leaves)

noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW945
    (leaves :
      MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsFieldsW944
    (w944LeavesOfLocalizedUnitDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactFieldsW945
      leaves)

/--
W945 exposes W944's route with localized adjoint data and the strong
unit-component witness consolidated into one provider.
-/
def closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW945 :
    List String :=
  ["bundled W716 WPP-limit boundary data provider: right-open closed-quotient-cover\
      boundary and source-difference cokernel-pi-zero boundary",
    "bundled W717 closed-natural-transformation relation data provider: relation\
      pullback and target-relation lifting",
    "W944 target no-univ data provider: target-difference preimage surjectivity\
      and target-codomain compactness filter nonbottom data",
    "W725 selected-difference and mapped-cokernel closedness branch: closed map\
      or closed embedding data",
    "W719 normalized fixed-target data provider: normalized strict-representative\
      lift blueprint, target fixed-target uniqueness, and localization-model\
      fixed-target uniqueness",
    "bundled W722 source-triangulation data provider: pretriangulated,\
      triangulated, and source-side triangle-completion data",
    "endpoint strict short-exact witnesses for closed embeddings, open maps,\
      and outgoing epi data",
    "W945 localized-unit data provider: right adjoint, adjunction, and unit\
      mapping-cone strict-exact component witness"]

theorem closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW945_count :
    closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW945.length =
      8 :=
  rfl

/-- Current checked W945 state. -/
structure MetrizableClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsRouteStateW945 :
    Type where
  seed : String
  declarations : List String
  localizedUnitDataResult : String
  exactAtResult : String
  refinedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsRouteStateW945 :
    MetrizableClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsRouteStateW945
    where
  seed :=
    "w945-closed-map-target-no-univ-membership-data-closedness-data-boundary-\
      relation-data-normalized-fixed-target-data-source-triangulation-endpoint-\
      strict-exact-localized-unit-data-primitive-field-route"
  declarations :=
    ["BoundedHomotopyLocalizedEndpointStrictExactUnitComponentsProviderW945",
      "boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945",
      "boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945",
      "boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945",
      "boundedHomotopyLocalizedUnitMemOfLocalizedUnitDataW945",
      "localizedRightAdjointDataOfLocalizedUnitDataW945",
      "MetrizableWppClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldLeavesW945",
      "w944LeavesOfLocalizedUnitDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactFieldsW945",
      "concreteLeavesOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW945",
      "routeDataProviderOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW945",
      "directBoundedLeftCalculusOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW945",
      "boundedDerivedInfinityCategoryOfClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsW945",
      "closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW945",
      "closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW945_count"]
  localizedUnitDataResult :=
    "proved: W945 localized-unit data projects the right adjoint, adjunction,\
      strong W939 unit component witness, and derived W721 unit membership\
      without adding the weaker W721 unit field as a separate assumption"
  exactAtResult :=
    "proved: closed-map target-no-univ-membership-data-closedness-data-\
      boundary-relation-data-normalized-fixed-target-data-source-triangulation-\
      endpoint-strict-exact-localized-unit-data route feeds the W944/W943/W942/\
      W941/W940/W937/W936/W935/W934/W933/W932/W931/W930 stable ExactAt route"
  refinedInputs :=
    ["bounded-homotopy localized right adjoint, localized adjunction, and unit\
      mapping-cone strict-exact component witness replaced by W945 localized-unit data",
      "W945 derives W721 functor-category unit membership from the stronger\
      W939 component witness through the existing W936/W935/W933/W932/W931 chain",
      "target-difference surjectivity and target-codomain no-univ compactness\
      remain consolidated into W944 target no-univ data",
      "boundary, relation, closedness, normalized fixed-target, and source\
      triangulation providers remain W716/W717/W725/W719/W722"]
  remainingInputs :=
    closedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsInputNamesW945
  productSuccessClaimed := false

theorem currentW945ClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactLocalizedUnitDataFieldsRouteStateW945;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
