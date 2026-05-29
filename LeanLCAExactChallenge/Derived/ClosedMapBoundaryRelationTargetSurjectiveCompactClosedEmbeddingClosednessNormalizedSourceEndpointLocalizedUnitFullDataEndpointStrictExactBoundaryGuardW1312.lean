import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataUnitStrictExactIsoBoundaryGuardW1311
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataRoute

/-!
W1312 records the W980 endpoint strict-exact boundary. W980 replaces the W974
endpoint kernel/cokernel-top data provider by one endpoint strict short-exact
family, but the full-data route remains a seven-input surface.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

namespace Dbounded

def canonicalW980EndpointStrictExactInnerInputNamesW1312 :
    List String :=
  ["endpoint strict short-exact family"]

theorem canonicalW980EndpointStrictExactInnerInputNamesW1312_count :
    canonicalW980EndpointStrictExactInnerInputNamesW1312.length = 1 :=
  rfl

def canonicalW980EndpointStrictExactRouteInputNamesW1312 :
    List String :=
  endpointStrictExactLocalizedUnitFullDataInputNamesW980

theorem canonicalW980EndpointStrictExactRouteInputNamesW1312_count :
    canonicalW980EndpointStrictExactRouteInputNamesW1312.length = 7 :=
  endpointStrictExactLocalizedUnitFullDataInputNamesW980_count

theorem canonicalW980EndpointStrictExactInnerKeepsCurrentSurfaceW1312 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length =
      canonicalW980EndpointStrictExactInnerInputNamesW1312.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW980EndpointStrictExactInnerInputNamesW1312_count]

theorem canonicalW980EndpointStrictExactRouteExpandsCurrentSurfaceW1312 :
    currentFullDataPayloadFromBranchFullDataInputNamesW1270.length <
      canonicalW980EndpointStrictExactRouteInputNamesW1312.length := by
  rw [currentFullDataPayloadFromBranchFullDataInputNamesW1270_count,
    canonicalW980EndpointStrictExactRouteInputNamesW1312_count]
  norm_num

def endpointKernelCokernelTopDataFromEndpointStrictExactW1312
    (endpointStrictExact :
      ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
        MetrizableLCA.strictShortExact (K.sc i)) :
    EndpointKernelCokernelTopDataProviderW974
    where
  endpointClosedEmbedding := fun K i =>
    (endpointStrictExact K i).closed_inclusion
  endpointOpenMap := fun K i =>
    (endpointStrictExact K i).open_map
  endpointCokernelTop := fun K i =>
    MetrizableLCA.cokernelSubgroup_eq_top_of_surjective
      (K.sc i).g (endpointStrictExact K i).surjective
  endpointKernelEquality := fun K i =>
    (MetrizableLCA.algebraic_kernel_of_strict
      (endpointStrictExact K i)).2

theorem endpointKernelCokernelTopDataOfEndpointStrictExactW980_eq_W1312
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980) :
    endpointKernelCokernelTopDataOfEndpointStrictExactW980 fullData =
      endpointKernelCokernelTopDataFromEndpointStrictExactW1312
        fullData.endpointStrictExact :=
  rfl

theorem w977FullDataEndpointDataOfW980FullDataW1312
    (fullData :
      BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitDataProviderW980) :
    (fullDataOfEndpointStrictExactW980 fullData).endpointKernelCokernelTopData =
      endpointKernelCokernelTopDataOfEndpointStrictExactW980 fullData :=
  rfl

structure MetrizableEndpointStrictExactBoundaryGuardStateW1312 :
    Type where
  seed : String
  inspectedBoundary : String
  innerSurfaceCount : Nat
  routeSurfaceCount : Nat
  providerSearchResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableEndpointStrictExactBoundaryGuardStateW1312 :
    MetrizableEndpointStrictExactBoundaryGuardStateW1312 where
  seed := "w1312-endpoint-strict-exact-boundary-guard"
  inspectedBoundary :=
    "W980 endpoint strict short-exact family constructing the W974 endpoint\
      kernel/cokernel-top provider"
  innerSurfaceCount :=
    canonicalW980EndpointStrictExactInnerInputNamesW1312.length
  routeSurfaceCount :=
    canonicalW980EndpointStrictExactRouteInputNamesW1312.length
  providerSearchResult :=
    "proved: W980 replaces the W974 endpoint kernel/cokernel-top provider with\
      one endpoint strict short-exact family, but this only keeps the current\
      one-input size at the endpoint sub-boundary and expands to a seven-input\
      full-data route; it does not close the remaining W987 obligation"
  remainingInputs := currentFullDataPayloadFromBranchFullDataInputNamesW1270
  productSuccessClaimed := false

theorem currentW1312EndpointStrictExactBoundaryGuard_productSuccess :
    (let state :=
        currentMetrizableEndpointStrictExactBoundaryGuardStateW1312;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
