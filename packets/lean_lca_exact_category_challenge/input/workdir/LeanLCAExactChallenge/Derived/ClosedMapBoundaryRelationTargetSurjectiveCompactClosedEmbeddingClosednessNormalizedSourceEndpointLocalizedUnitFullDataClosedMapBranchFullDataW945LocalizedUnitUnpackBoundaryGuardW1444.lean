import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW949EndpointLocalizedUnitUnpackBoundaryGuardW1443
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataLocalizedUnitBoundaryUnpackGuardW1306

/-!
W1444 connects the W945 localized-unit component exposed by W1443 to the W1306
repack. The W1007 branch-full-data route therefore exposes the W730
boundary/relation provider, W944 target no-univ data, W973 closed-embedding
closedness data, W719 normalized fixed-target data, W722 source-triangulation
data, endpoint strict-exact witnesses, the localized right adjoint, localized
adjunction, and W939 unit-component witness.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def w1007W945LocalizedUnitUnpackedInputNamesW1444 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "W719 normalized fixed-target data provider",
    "W722 source-triangulation data provider",
    "endpoint strict-exact witnesses",
    "bounded homotopy localized right adjoint",
    "bounded homotopy localized adjunction",
    "W939 unit mapping-cone strict-exact component witness"]

theorem w1007W945LocalizedUnitUnpackedInputNamesW1444_count :
    w1007W945LocalizedUnitUnpackedInputNamesW1444.length = 9 :=
  rfl

/-- Repacking W1007's W945 component through W1306 returns the same W945 component. -/
theorem w1007RepackedW945ComponentIsW945W1444
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    repackLocalizedUnitDataW1306
        (localizedUnitDataOfEndpointLocalizedUnitDataW949
          (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
            (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData))) =
      localizedUnitDataOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
          (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData)) :=
  repackLocalizedUnitDataW1306_eq
    (localizedUnitDataOfEndpointLocalizedUnitDataW949
      (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData)))

/-- W1007's W985 surface feeds W984 with the W945 localized-unit component. -/
theorem w1007W985LocalizedUnitComponentRunsThroughW945W1444
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    localizedUnitDataOfEndpointLocalizedUnitDataW949
        ((fullDataOfNormalizedSourceEndpointLocalizedUnitW985
          (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
            (w986FullDataOfFullDataW987
              (branchFullDataInputOfBranchFullDataW1007
                branchFullData)))).endpointLocalizedUnitData) =
      localizedUnitDataOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
          (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData)) :=
  rfl

/-- The W945 component over W1007's W950 data keeps the localized right adjoint. -/
theorem w1007W945LocalizedRightAdjointRunsThroughW1444
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfEndpointLocalizedUnitDataW949
          ((fullDataOfNormalizedSourceEndpointLocalizedUnitW985
            (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
              (w986FullDataOfFullDataW987
                (branchFullDataInputOfBranchFullDataW1007
                  branchFullData)))).endpointLocalizedUnitData)) =
      boundedHomotopyLocalizedRightAdjointOfLocalizedUnitDataW945
        (localizedUnitDataOfEndpointLocalizedUnitDataW949
          (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
            (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData))) :=
  rfl

/-- The W945 component over W1007's W950 data keeps the localized adjunction. -/
theorem w1007W945LocalizedAdjunctionRunsThroughW1444
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
        (localizedUnitDataOfEndpointLocalizedUnitDataW949
          ((fullDataOfNormalizedSourceEndpointLocalizedUnitW985
            (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
              (w986FullDataOfFullDataW987
                (branchFullDataInputOfBranchFullDataW1007
                  branchFullData)))).endpointLocalizedUnitData)) =
      boundedHomotopyLocalizedAdjunctionOfLocalizedUnitDataW945
        (localizedUnitDataOfEndpointLocalizedUnitDataW949
          (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
            (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData))) :=
  rfl

/-- The W945 component over W1007's W950 data keeps the W939 unit-component witness. -/
theorem w1007W945UnitComponentsRunsThroughW1444
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
        (localizedUnitDataOfEndpointLocalizedUnitDataW949
          ((fullDataOfNormalizedSourceEndpointLocalizedUnitW985
            (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
              (w986FullDataOfFullDataW987
                (branchFullDataInputOfBranchFullDataW1007
                  branchFullData)))).endpointLocalizedUnitData)) =
      boundedHomotopyLocalizedEndpointStrictExactUnitStrictExactComponentsOfLocalizedUnitDataW945
        (localizedUnitDataOfEndpointLocalizedUnitDataW949
          (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
            (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData))) :=
  rfl

/-- W1444 exposes the nine inputs obtained by unpacking W1443's W945 component. -/
theorem w1444BranchFullDataUnpackedW730W944W973W719W722EndpointRightAdjointAdjunctionW939InputCount :
    w1007W945LocalizedUnitUnpackedInputNamesW1444.length = 9 :=
  w1007W945LocalizedUnitUnpackedInputNamesW1444_count

/-- W1306 records the three internal W945 localized-unit inputs. -/
theorem w1444W945LocalizedUnitInnerInputCount :
    canonicalW945LocalizedUnitInnerInputNamesW1306.length = 3 :=
  canonicalW945LocalizedUnitInnerInputNamesW1306_count

/-- W1443's seven-input surface opens to W1444's nine-input surface. -/
theorem w1444W1443UnpackExpandsToW945LocalizedUnit :
    w1007W949EndpointLocalizedUnitUnpackedInputNamesW1443.length <
      w1007W945LocalizedUnitUnpackedInputNamesW1444.length := by
  rw [w1007W949EndpointLocalizedUnitUnpackedInputNamesW1443_count,
    w1007W945LocalizedUnitUnpackedInputNamesW1444_count]
  norm_num

/-- W1169's one-input branch-full-data surface opens to W1444's nine-input surface. -/
theorem w1444W1169UnpackExpandsToW945LocalizedUnit :
    branchFullDataInputNamesW1169.length <
      w1007W945LocalizedUnitUnpackedInputNamesW1444.length := by
  rw [branchFullDataInputNamesW1169_count,
    w1007W945LocalizedUnitUnpackedInputNamesW1444_count]
  norm_num

/-- Current W1444 nonterminal W945 localized-unit unpack state. -/
structure ClosedMapBranchFullDataW945LocalizedUnitUnpackBoundaryStateW1444 :
    Type where
  seed : String
  declarations : List String
  projectionResult : String
  unpackResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1444 records W1007's concrete W945 localized-unit unpack after W1443. -/
def currentClosedMapBranchFullDataW945LocalizedUnitUnpackBoundaryStateW1444 :
    ClosedMapBranchFullDataW945LocalizedUnitUnpackBoundaryStateW1444 where
  seed := "w1444-closed-map-branch-full-data-w945-localized-unit-unpack-boundary"
  declarations :=
    ["w1007RepackedW945ComponentIsW945W1444",
      "w1007W985LocalizedUnitComponentRunsThroughW945W1444",
      "w1007W945LocalizedRightAdjointRunsThroughW1444",
      "w1007W945LocalizedAdjunctionRunsThroughW1444",
      "w1007W945UnitComponentsRunsThroughW1444",
      "w1444BranchFullDataUnpackedW730W944W973W719W722EndpointRightAdjointAdjunctionW939InputCount",
      "w1444W945LocalizedUnitInnerInputCount",
      "w1444W1443UnpackExpandsToW945LocalizedUnit",
      "w1444W1169UnpackExpandsToW945LocalizedUnit"]
  projectionResult :=
    "proved: W1007's W945 component projects to the localized right adjoint,\
      localized adjunction, and W939 unit-component witness, and W985 receives\
      those fields"
  unpackResult :=
    "proved: unpacking the W1443 W730/W944/W973/W719/W722/endpoint/W945\
      surface exposes the W1444 nine-input W730/W944/W973/W719/W722/endpoint/\
      right-adjoint/adjunction/W939 surface, so this remains nonterminal"
  remainingInputs := w1007W945LocalizedUnitUnpackedInputNamesW1444
  productSuccessClaimed := false

theorem currentW1444ClosedMapBranchFullDataW945LocalizedUnitUnpackBoundary_productSuccess :
    currentClosedMapBranchFullDataW945LocalizedUnitUnpackBoundaryStateW1444.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
