import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataRoute

/-!
W998 removes W997's extra W715 target surjective-compact sub-assumption.
The W987 branch full-data provider already feeds W977, hence exposes W944
target no-univ data. W998 converts that no-univ compactness primitive back into
`CompactSpace` and feeds the W997 route from W987 alone.
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

/-- W998 recovers W944 target no-univ data from W987 through W987's W977 leaves. -/
noncomputable def targetNoUnivDataOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfFullDataW977 (w981LeavesOfFullDataW987 fullData).fullData

/--
W998 turns W930's no-univ compactness primitive into the `CompactSpace` field
used by W715, by rebuilding `IsCompact Set.univ` through cluster points.
-/
@[reducible]
def targetCodomainCompactSpaceOfNoUnivMembershipW998
    (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
    (hcompact : targetCodomainCompactNoUnivMembershipPrimitiveW930 Y) :
    CompactSpace (wppOpCodomainW441 Y) := by
  refine isCompact_univ_iff.mp ?_
  intro f hfne _hle
  obtain ⟨x, hx⟩ :=
    hcompact (f := f) (Filter.neBot_iff.mp hfne)
  exact ⟨x, Set.mem_univ x, by
    simpa [ClusterPt] using (Filter.neBot_iff.mpr hx)⟩

/-- W998 derives the W715 target surjective-compact provider from W987 alone. -/
noncomputable def targetSurjectiveCompactDataOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    TargetSurjectiveCompactForTargetProviderW715 := by
  intro Y
  let targetData := targetNoUnivDataOfBranchFullDataW998 fullData
  constructor
  · exact
      targetDifferenceSurjectiveOfPrimitiveW923
        (targetDifferenceSurjectivePrimitiveOfTargetNoUnivDataW944
          targetData) Y
  · exact
      targetCodomainCompactSpaceOfNoUnivMembershipW998 Y
        ((targetData Y).2)

/-- W998 builds W996's two-field surface from W987 alone. -/
noncomputable def targetSurjectiveCompactFullDataOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    BoundaryRelationTargetSurjectiveCompactFullDataProviderW996
    where
  targetSurjectiveCompactData :=
    targetSurjectiveCompactDataOfBranchFullDataW998 fullData
  fullData := fullData

/-- W998 builds W997's one-provider surface from W987 alone. -/
noncomputable def targetSurjectiveCompactBranchFullDataOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997
    where
  targetSurjectiveCompactData :=
    targetSurjectiveCompactDataOfBranchFullDataW998 fullData
  branchFullData := fullData

/-- W998 builds the W995 data surface through W997 after deriving W715 from W987. -/
noncomputable def targetProviderDataOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfTargetSurjectiveCompactBranchFullDataW997
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998 fullData)

/-- W998 constructs the W994 normalized-source/endpoint data through W997. -/
noncomputable def normalizedSourceEndpointDataOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfTargetSurjectiveCompactBranchFullDataW997
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998 fullData)

/-- W998 returns the underlying W987 full data through the W997 route. -/
noncomputable def fullDataOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfTargetSurjectiveCompactBranchFullDataW997
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998 fullData)

/- W998 exposes W981 leaves through W997. -/
noncomputable def w981LeavesOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfTargetSurjectiveCompactBranchFullDataW997
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998 fullData)

/- W998 exposes W971 component fields through W997. -/
noncomputable def componentFieldsOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetSurjectiveCompactBranchFullDataW997
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998 fullData)

/-- W998 reconstructs endpoint strict exactness through W997. -/
noncomputable def endpointStrictExactOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfTargetSurjectiveCompactBranchFullDataW997
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998 fullData)

/-- W998 derives unit mapping-cone algebraic exactness through W997. -/
noncomputable def unitMappingConeAlgebraicExactOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfBranchFullDataW998 fullData).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfBranchFullDataW998 fullData).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfBranchFullDataW998 fullData).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfBranchFullDataW998 fullData).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfTargetSurjectiveCompactBranchFullDataW997
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998 fullData)

/-- W998 reconstructs unit mapping-cone strict short exactness through W997. -/
noncomputable def unitMappingConeStrictExactOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfBranchFullDataW998 fullData).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfTargetSurjectiveCompactBranchFullDataW997
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998 fullData)

/-- W998 wraps the unit mapping-cone isomorphism through W997. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfBranchFullDataW998 fullData).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfBranchFullDataW998 fullData).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfTargetSurjectiveCompactBranchFullDataW997
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998 fullData)

theorem directBoundedLeftCalculusOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetSurjectiveCompactBranchFullDataW997
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998 fullData)

noncomputable def boundedDerivedInfinityCategoryOfBranchFullDataW998
    (fullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetSurjectiveCompactBranchFullDataW997
    (targetSurjectiveCompactBranchFullDataOfBranchFullDataW998 fullData)

def branchFullDataInputNamesW998 : List String :=
  ["W987 boundary-relation/target-closed-embedding-closedness/normalized-source/endpoint-localized full-data provider"]

theorem branchFullDataInputNamesW998_count :
    branchFullDataInputNamesW998.length = 1 :=
  rfl

structure MetrizableBranchFullDataRouteStateW998 : Type where
  seed : String
  declarations : List String
  targetSurjectiveCompactRecoveryResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableBranchFullDataRouteStateW998 :
    MetrizableBranchFullDataRouteStateW998
    where
  seed := "w998-branch-full-data-to-target-surjective-compact-route"
  declarations :=
    ["targetNoUnivDataOfBranchFullDataW998",
      "targetCodomainCompactSpaceOfNoUnivMembershipW998",
      "targetSurjectiveCompactDataOfBranchFullDataW998",
      "targetSurjectiveCompactFullDataOfBranchFullDataW998",
      "targetSurjectiveCompactBranchFullDataOfBranchFullDataW998",
      "targetProviderDataOfBranchFullDataW998",
      "normalizedSourceEndpointDataOfBranchFullDataW998",
      "fullDataOfBranchFullDataW998",
      "w981LeavesOfBranchFullDataW998",
      "componentFieldsOfBranchFullDataW998",
      "endpointStrictExactOfBranchFullDataW998",
      "unitMappingConeAlgebraicExactOfBranchFullDataW998",
      "unitMappingConeStrictExactOfBranchFullDataW998",
      "unitMappingConeIsoNonemptyOfBranchFullDataW998",
      "directBoundedLeftCalculusOfBranchFullDataW998",
      "boundedDerivedInfinityCategoryOfBranchFullDataW998",
      "branchFullDataInputNamesW998_count"]
  targetSurjectiveCompactRecoveryResult :=
    "proved: W998 derives W715 target surjective-compact data from W987 via\
      W977/W944 target no-univ data and compact cluster-point reconstruction"
  exactAtResult :=
    "proved: the W998 W987-only surface feeds the W997/W996/W995/W994/W993/\
      W988/W987/W986/W985/W984/W983/W982/W981/W980/W979/W978/W977/W976/\
      W975/W974/W973/W972/W971/W970/W969/W968/W967/W966/W965/W964/W963/\
      W962/W961/W959/W958/W957/W956/W955/W954/W953/W952 stable ExactAt route"
  remainingInputs := branchFullDataInputNamesW998
  productSuccessClaimed := false

theorem currentW998BranchFullDataRoute_productSuccess :
    (let state := currentMetrizableBranchFullDataRouteStateW998;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
