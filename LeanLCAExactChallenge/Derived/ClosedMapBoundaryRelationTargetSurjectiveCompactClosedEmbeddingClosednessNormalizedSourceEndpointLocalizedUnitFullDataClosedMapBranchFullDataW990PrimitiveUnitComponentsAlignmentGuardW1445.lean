import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW945LocalizedUnitUnpackBoundaryGuardW1444
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataPrimitiveUnitComponentsGuardW1321

/-!
W1445 aligns the W1444 unpacked branch-full-data surface with the W990
primitive unit-components route. The W1444 surface exposes W719 and W722
separately, while W990 consumes their W948 repack together with W730, W944,
W973, endpoint strict exactness, the localized right adjoint, localized
adjunction, and the W939 unit-component witness.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def w1007W990PrimitiveUnitComponentsAlignedInputNamesW1445 : List String :=
  primitiveUnitComponentsInputNamesW990

theorem w1007W990PrimitiveUnitComponentsAlignedInputNamesW1445_count :
    w1007W990PrimitiveUnitComponentsAlignedInputNamesW1445.length = 8 :=
  primitiveUnitComponentsInputNamesW990_count

/-- W1007's W1444 data repacks to the W990 primitive unit-components surface. -/
noncomputable def w1007PrimitiveUnitComponentsDataW1445
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactPrimitiveUnitComponentsDataProviderW990
    where
  boundaryRelationData :=
    boundaryRelationDataOfBranchFullDataW1007 branchFullData
  targetNoUnivData :=
    targetNoUnivDataOfBranchFullDataW1007 branchFullData
  closedEmbeddingClosednessData :=
    closedEmbeddingClosednessDataOfBranchFullDataW1007 branchFullData
  endpointStrictExact :=
    endpointStrictExactOfEndpointLocalizedUnitDataW949
      (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
          branchFullData))
  boundedHomotopyLocalizedRightAdjoint :=
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
      (localizedUnitDataOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
          (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
            branchFullData)))
  boundedHomotopyLocalizedAdjunction :=
    boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
      (localizedUnitDataOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
          (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
            branchFullData)))
  boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponents :=
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
      (localizedUnitDataOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
          (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
            branchFullData)))
  normalizedSourceTriangulationData :=
    repackNormalizedSourceTriangulationDataW1303
      (normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
          branchFullData))

/-- The W1445 W990 provider keeps W1007's boundary/relation data. -/
theorem w1007W990PrimitiveUnitComponentsKeepsBoundaryRelationW1445
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007PrimitiveUnitComponentsDataW1445
        branchFullData).boundaryRelationData =
      boundaryRelationDataOfBranchFullDataW1007 branchFullData :=
  rfl

/-- The W1445 W990 provider keeps W1007's target no-univ data. -/
theorem w1007W990PrimitiveUnitComponentsKeepsTargetNoUnivW1445
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007PrimitiveUnitComponentsDataW1445
        branchFullData).targetNoUnivData =
      targetNoUnivDataOfBranchFullDataW1007 branchFullData :=
  rfl

/-- The W1445 W990 provider keeps W1007's closed-embedding closedness data. -/
theorem w1007W990PrimitiveUnitComponentsKeepsClosedEmbeddingClosednessW1445
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007PrimitiveUnitComponentsDataW1445
        branchFullData).closedEmbeddingClosednessData =
      closedEmbeddingClosednessDataOfBranchFullDataW1007 branchFullData :=
  rfl

/-- W1445's W948 repack is judgmentally the W1007 W948 component exposed by W1442. -/
theorem w1007W990PrimitiveUnitComponentsRepackedW948IsW948W1445
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (w1007PrimitiveUnitComponentsDataW1445
        branchFullData).normalizedSourceTriangulationData =
      normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
          branchFullData) :=
  repackNormalizedSourceTriangulationDataW1303_eq
    (normalizedSourceTriangulationDataOfNormalizedSourceEndpointLocalizedUnitDataW950
      (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007
        branchFullData))

/-- The W990 localized-adjunction provider keeps W1445's localized right adjoint. -/
theorem w1007W990LocalizedAdjunctionKeepsRightAdjointW1445
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (localizedAdjunctionDataOfPrimitiveUnitComponentsW990
        (w1007PrimitiveUnitComponentsDataW1445
          branchFullData)).boundedHomotopyLocalizedRightAdjoint =
      (w1007PrimitiveUnitComponentsDataW1445
        branchFullData).boundedHomotopyLocalizedRightAdjoint :=
  w990LocalizedAdjunctionKeepsRightAdjointW1321
    (w1007PrimitiveUnitComponentsDataW1445 branchFullData)

/-- The W990 localized-adjunction provider keeps W1445's localized adjunction. -/
theorem w1007W990LocalizedAdjunctionKeepsAdjunctionW1445
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (localizedAdjunctionDataOfPrimitiveUnitComponentsW990
        (w1007PrimitiveUnitComponentsDataW1445
          branchFullData)).boundedHomotopyLocalizedAdjunction =
      (w1007PrimitiveUnitComponentsDataW1445
        branchFullData).boundedHomotopyLocalizedAdjunction :=
  w990LocalizedAdjunctionKeepsAdjunctionW1321
    (w1007PrimitiveUnitComponentsDataW1445 branchFullData)

/-- The W1445 W990 route feeds the W989 full-data construction. -/
theorem w1007W990FullDataRunsThroughW989W1445
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    fullDataOfPrimitiveUnitComponentsW990
        (w1007PrimitiveUnitComponentsDataW1445 branchFullData) =
      fullDataOfUnitStrictExactIsoW989
        (unitStrictExactIsoFullDataOfPrimitiveUnitComponentsW990
          (w1007PrimitiveUnitComponentsDataW1445 branchFullData)) :=
  w990FullDataRunsThroughW989W1321
    (w1007PrimitiveUnitComponentsDataW1445 branchFullData)

/-- W1445 exposes the eight inputs consumed by W990 after W948 repacking. -/
theorem w1445BranchFullDataW990PrimitiveUnitComponentsInputCount :
    w1007W990PrimitiveUnitComponentsAlignedInputNamesW1445.length = 8 :=
  w1007W990PrimitiveUnitComponentsAlignedInputNamesW1445_count

/-- W1445 uses the canonical W990 primitive unit-components input count. -/
theorem w1445CanonicalW990PrimitiveUnitComponentsRouteInputCount :
    canonicalW990PrimitiveUnitComponentsInputNamesW1321.length = 8 :=
  canonicalW990PrimitiveUnitComponentsInputNamesW1321_count

/-- W1444's nine-field unpack aligns with W990's eight-field W948-repacked route. -/
theorem w1445W1444SurfaceAlignsWithW990PrimitiveUnitComponents :
    w1007W990PrimitiveUnitComponentsAlignedInputNamesW1445.length <
      w1007W945LocalizedUnitUnpackedInputNamesW1444.length := by
  rw [w1007W990PrimitiveUnitComponentsAlignedInputNamesW1445_count,
    w1007W945LocalizedUnitUnpackedInputNamesW1444_count]
  norm_num

/-- Current W1445 nonterminal W990 primitive-unit route-alignment state. -/
structure ClosedMapBranchFullDataW990PrimitiveUnitComponentsAlignmentStateW1445 :
    Type where
  seed : String
  declarations : List String
  alignmentResult : String
  routeResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1445 records W1007's W1444 surface as a W990 primitive unit-components provider. -/
def currentClosedMapBranchFullDataW990PrimitiveUnitComponentsAlignmentStateW1445 :
    ClosedMapBranchFullDataW990PrimitiveUnitComponentsAlignmentStateW1445 where
  seed := "w1445-closed-map-branch-full-data-w990-primitive-unit-components-alignment"
  declarations :=
    ["w1007PrimitiveUnitComponentsDataW1445",
      "w1007W990PrimitiveUnitComponentsKeepsBoundaryRelationW1445",
      "w1007W990PrimitiveUnitComponentsKeepsTargetNoUnivW1445",
      "w1007W990PrimitiveUnitComponentsKeepsClosedEmbeddingClosednessW1445",
      "w1007W990PrimitiveUnitComponentsRepackedW948IsW948W1445",
      "w1007W990LocalizedAdjunctionKeepsRightAdjointW1445",
      "w1007W990LocalizedAdjunctionKeepsAdjunctionW1445",
      "w1007W990FullDataRunsThroughW989W1445",
      "w1445BranchFullDataW990PrimitiveUnitComponentsInputCount",
      "w1445CanonicalW990PrimitiveUnitComponentsRouteInputCount",
      "w1445W1444SurfaceAlignsWithW990PrimitiveUnitComponents"]
  alignmentResult :=
    "proved: W1007's W1444 surface forms the W990 primitive unit-components\
      provider after W948 repacking, preserving W730, W944, W973, the W948\
      component, localized right adjoint, and localized adjunction"
  routeResult :=
    "proved: the W1445 provider enters W990's W975/W981 construction and then\
      delegates through W989, but this is route alignment rather than a\
      positive OriginalFourTaskProductSuccess witness"
  remainingInputs := w1007W990PrimitiveUnitComponentsAlignedInputNamesW1445
  productSuccessClaimed := false

theorem currentW1445ClosedMapBranchFullDataW990PrimitiveUnitComponentsAlignment_productSuccess :
    currentClosedMapBranchFullDataW990PrimitiveUnitComponentsAlignmentStateW1445.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
