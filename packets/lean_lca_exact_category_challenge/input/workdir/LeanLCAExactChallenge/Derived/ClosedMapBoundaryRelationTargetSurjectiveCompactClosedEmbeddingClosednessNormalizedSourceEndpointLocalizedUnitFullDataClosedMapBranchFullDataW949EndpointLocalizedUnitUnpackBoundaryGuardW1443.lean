import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapBranchFullDataW948NormalizedSourceUnpackBoundaryGuardW1442
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataEndpointLocalizedUnitBoundaryUnpackGuardW1301

/-!
W1443 connects the W949 endpoint-localized-unit component exposed by W1442 to
the W1301 repack. The W1007 branch-full-data route therefore exposes the W730
boundary/relation provider, W944 target no-univ data, W973 closed-embedding
closedness data, W719 normalized fixed-target data, W722 source-triangulation
data, endpoint strict-exact witnesses, and W945 localized-unit data.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def w1007W949EndpointLocalizedUnitUnpackedInputNamesW1443 : List String :=
  ["W730 boundary/relation data provider",
    "W944 target no-univ data provider",
    "W973 closed-embedding closedness data provider",
    "W719 normalized fixed-target data provider",
    "W722 source-triangulation data provider",
    "endpoint strict-exact witnesses",
    "W945 localized-unit data provider"]

theorem w1007W949EndpointLocalizedUnitUnpackedInputNamesW1443_count :
    w1007W949EndpointLocalizedUnitUnpackedInputNamesW1443.length = 7 :=
  rfl

def w1007W949EndpointLocalizedUnitInnerInputNamesW1443 : List String :=
  ["endpoint strict-exact witnesses", "W945 localized-unit data provider"]

theorem w1007W949EndpointLocalizedUnitInnerInputNamesW1443_count :
    w1007W949EndpointLocalizedUnitInnerInputNamesW1443.length = 2 :=
  rfl

/-- Repacking W1007's W949 component through W1301 returns the same W949 component. -/
theorem w1007RepackedW949ComponentIsW949W1443
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    repackEndpointLocalizedUnitDataW1301
        (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
          (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData)) =
      endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData) :=
  repackEndpointLocalizedUnitDataW1301_eq
    (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
      (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData))

/-- W1007's W985 surface feeds W984 with the W949 endpoint-localized component. -/
theorem w1007W985EndpointLocalizedComponentRunsThroughW949W1443
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    (fullDataOfNormalizedSourceEndpointLocalizedUnitW985
        (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
          (w986FullDataOfFullDataW987
            (branchFullDataInputOfBranchFullDataW1007
              branchFullData)))).endpointLocalizedUnitData =
      endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
        (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData) :=
  rfl

/-- The W949 component over W1007's W950 data keeps the endpoint strict-exact witnesses. -/
theorem w1007W949EndpointStrictExactRunsThroughW1443
    (branchFullData :
      BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitBranchFullDataProviderW1007) :
    endpointStrictExactOfEndpointLocalizedUnitDataW949
        ((fullDataOfNormalizedSourceEndpointLocalizedUnitW985
          (fullDataOfTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitW986
            (w986FullDataOfFullDataW987
              (branchFullDataInputOfBranchFullDataW1007
                branchFullData)))).endpointLocalizedUnitData) =
      endpointStrictExactOfEndpointLocalizedUnitDataW949
        (endpointLocalizedUnitDataOfNormalizedSourceEndpointLocalizedUnitDataW950
          (normalizedSourceEndpointLocalizedUnitDataOfBranchFullDataW1007 branchFullData)) :=
  rfl

/-- The W949 component over W1007's W950 data keeps the W945 localized-unit provider. -/
theorem w1007W949LocalizedUnitDataRunsThroughW1443
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

/-- W1443 exposes the seven inputs obtained by unpacking W1442's W949 component. -/
theorem w1443BranchFullDataUnpackedW730W944W973W719W722EndpointW945InputCount :
    w1007W949EndpointLocalizedUnitUnpackedInputNamesW1443.length = 7 :=
  w1007W949EndpointLocalizedUnitUnpackedInputNamesW1443_count

/-- W1443 records the two internal W949 endpoint-localized-unit inputs. -/
theorem w1443W949EndpointLocalizedUnitInnerInputCount :
    w1007W949EndpointLocalizedUnitInnerInputNamesW1443.length = 2 :=
  w1007W949EndpointLocalizedUnitInnerInputNamesW1443_count

/-- W1442's six-input W730/W944/W973/W719/W722/W949 surface opens to W1443's seven-input surface. -/
theorem w1443W1442UnpackExpandsToW949EndpointLocalizedUnit :
    w1007W948NormalizedSourceUnpackedInputNamesW1442.length <
      w1007W949EndpointLocalizedUnitUnpackedInputNamesW1443.length := by
  rw [w1007W948NormalizedSourceUnpackedInputNamesW1442_count,
    w1007W949EndpointLocalizedUnitUnpackedInputNamesW1443_count]
  norm_num

/-- W1169's one-input branch-full-data surface opens to W1443's seven-input surface. -/
theorem w1443W1169UnpackExpandsToW949EndpointLocalizedUnit :
    branchFullDataInputNamesW1169.length <
      w1007W949EndpointLocalizedUnitUnpackedInputNamesW1443.length := by
  rw [branchFullDataInputNamesW1169_count,
    w1007W949EndpointLocalizedUnitUnpackedInputNamesW1443_count]
  norm_num

/-- Current W1443 nonterminal W949 endpoint-localized-unit unpack state. -/
structure ClosedMapBranchFullDataW949EndpointLocalizedUnitUnpackBoundaryStateW1443 :
    Type where
  seed : String
  declarations : List String
  projectionResult : String
  unpackResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1443 records W1007's concrete W949 endpoint-localized-unit unpack after W1442. -/
def currentClosedMapBranchFullDataW949EndpointLocalizedUnitUnpackBoundaryStateW1443 :
    ClosedMapBranchFullDataW949EndpointLocalizedUnitUnpackBoundaryStateW1443 where
  seed := "w1443-closed-map-branch-full-data-w949-endpoint-localized-unit-unpack-boundary"
  declarations :=
    ["w1007RepackedW949ComponentIsW949W1443",
      "w1007W985EndpointLocalizedComponentRunsThroughW949W1443",
      "w1007W949EndpointStrictExactRunsThroughW1443",
      "w1007W949LocalizedUnitDataRunsThroughW1443",
      "w1443BranchFullDataUnpackedW730W944W973W719W722EndpointW945InputCount",
      "w1443W949EndpointLocalizedUnitInnerInputCount",
      "w1443W1442UnpackExpandsToW949EndpointLocalizedUnit",
      "w1443W1169UnpackExpandsToW949EndpointLocalizedUnit"]
  projectionResult :=
    "proved: W1007's W949 component projects to endpoint strict-exact witnesses\
      and W945 localized-unit data, and W985 receives those fields"
  unpackResult :=
    "proved: unpacking the W1442 W730/W944/W973/W719/W722/W949 surface exposes\
      the W1443 seven-input W730/W944/W973/W719/W722/endpoint/W945 surface, so\
      this remains nonterminal"
  remainingInputs := w1007W949EndpointLocalizedUnitUnpackedInputNamesW1443
  productSuccessClaimed := false

theorem currentW1443ClosedMapBranchFullDataW949EndpointLocalizedUnitUnpackBoundary_productSuccess :
    currentClosedMapBranchFullDataW949EndpointLocalizedUnitUnpackBoundaryStateW1443.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
