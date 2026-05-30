import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataFromKernelCokernelTopIsoComponentFieldsRoute

/-!
W992 replaces W991's W944 target no-univ provider by the older W715
target-surjective-compact provider, deriving the W930 no-univ compactness
primitive from `CompactSpace` using compact cluster points.
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
W992 derives W944 target no-univ data from W715 target surjectivity plus
compactness. The compactness branch uses `isCompact_univ.exists_clusterPt` to
turn a nonbottom filter into a cluster point, then extracts the nonbottom
neighborhood/filter intersection required by W930.
-/
def targetNoUnivDataOfTargetSurjectiveCompactW992
    (targetData : TargetSurjectiveCompactForTargetProviderW715) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 := by
  intro Y
  constructor
  · intro y
    exact (targetData Y).1 y
  · intro f hfne
    letI : CompactSpace (wppOpCodomainW441 Y) := (targetData Y).2
    haveI : Filter.NeBot f := Filter.neBot_iff.mpr hfne
    obtain ⟨x, _hx, hxcluster⟩ :=
      (isCompact_univ :
        IsCompact (Set.univ : Set (wppOpCodomainW441 Y))).exists_clusterPt
        (f := f)
        (by
          simpa using
            (le_top : f ≤ (⊤ : Filter (wppOpCodomainW441 Y))))
    exact ⟨x, Filter.neBot_iff.mp hxcluster.neBot⟩

/--
W992 preserves W991's component-field surface while replacing the W944 target
no-univ data input by W715 target surjective compact data.
-/
structure MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW992 :
    Type 2 where
  boundaryRelationData :
    MetrizableWppBoundaryRelationDataProviderW730
  targetSurjectiveCompactData :
    TargetSurjectiveCompactForTargetProviderW715
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

/-- W992 builds the W991 leaves by deriving W944 target no-univ data from W715. -/
def w991LeavesOfTargetSurjectiveCompactW992
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW992) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetNoUnivDataClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW974
    where
  boundaryRelationData := leaves.boundaryRelationData
  targetNoUnivData :=
    targetNoUnivDataOfTargetSurjectiveCompactW992
      leaves.targetSurjectiveCompactData
  closedEmbeddingClosednessData := leaves.closedEmbeddingClosednessData
  endpointKernelCokernelTopData := leaves.endpointKernelCokernelTopData
  normalizedSourceTriangulationData :=
    leaves.normalizedSourceTriangulationData
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

/-- W992 constructs W987 full data through W991 after deriving W944 from W715. -/
noncomputable def fullDataOfTargetSurjectiveCompactW992
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW992) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfKernelCokernelTopIsoComponentFieldsW991
    (w991LeavesOfTargetSurjectiveCompactW992 leaves)

/-- W992 exposes W981 leaves through the W991 route. -/
noncomputable def w981LeavesOfTargetSurjectiveCompactW992
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW992) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfKernelCokernelTopIsoComponentFieldsW991
    (w991LeavesOfTargetSurjectiveCompactW992 leaves)

/-- W992 exposes W971 component fields through the W991 route. -/
noncomputable def componentFieldsOfTargetSurjectiveCompactW992
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW992) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfKernelCokernelTopIsoComponentFieldsW991
    (w991LeavesOfTargetSurjectiveCompactW992 leaves)

/-- W992 reconstructs endpoint strict exactness through W991. -/
noncomputable def endpointStrictExactOfTargetSurjectiveCompactW992
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW992) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfKernelCokernelTopIsoComponentFieldsW991
    (w991LeavesOfTargetSurjectiveCompactW992 leaves)

theorem directBoundedLeftCalculusOfTargetSurjectiveCompactW992
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW992) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfKernelCokernelTopIsoComponentFieldsW991
    (w991LeavesOfTargetSurjectiveCompactW992 leaves)

noncomputable def boundedDerivedInfinityCategoryOfTargetSurjectiveCompactW992
    (leaves :
      MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessDataEndpointKernelCokernelTopDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW992) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfKernelCokernelTopIsoComponentFieldsW991
    (w991LeavesOfTargetSurjectiveCompactW992 leaves)

def targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW992 :
    List String :=
  ["W730 boundary/relation data provider",
    "W715 target surjective-compact data provider",
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

theorem targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW992_count :
    targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW992.length = 13 :=
  rfl

structure MetrizableTargetSurjectiveCompactKernelCokernelTopIsoComponentFieldsRouteStateW992 :
    Type where
  seed : String
  declarations : List String
  targetCompactnessResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetSurjectiveCompactKernelCokernelTopIsoComponentFieldsRouteStateW992 :
    MetrizableTargetSurjectiveCompactKernelCokernelTopIsoComponentFieldsRouteStateW992
    where
  seed := "w992-target-surjective-compact-to-w991-route"
  declarations :=
    ["targetNoUnivDataOfTargetSurjectiveCompactW992",
      "w991LeavesOfTargetSurjectiveCompactW992",
      "fullDataOfTargetSurjectiveCompactW992",
      "w981LeavesOfTargetSurjectiveCompactW992",
      "componentFieldsOfTargetSurjectiveCompactW992",
      "endpointStrictExactOfTargetSurjectiveCompactW992",
      "directBoundedLeftCalculusOfTargetSurjectiveCompactW992",
      "boundedDerivedInfinityCategoryOfTargetSurjectiveCompactW992",
      "targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW992_count"]
  targetCompactnessResult :=
    "proved: W992 derives W944 target no-univ compactness from W715\
      CompactSpace data using compact cluster points, while projecting target\
      difference surjectivity from W715"
  exactAtResult :=
    "proved: the W992 target-surjective-compact component-field surface feeds\
      the W991/W990/W989/W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/\
      W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/\
      W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable\
      ExactAt route"
  remainingInputs := targetSurjectiveCompactKernelCokernelTopIsoComponentFieldsInputNamesW992
  productSuccessClaimed := false

theorem currentW992TargetSurjectiveCompactKernelCokernelTopIsoComponentFieldsRoute_productSuccess :
    (let state :=
        currentMetrizableTargetSurjectiveCompactKernelCokernelTopIsoComponentFieldsRouteStateW992;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
