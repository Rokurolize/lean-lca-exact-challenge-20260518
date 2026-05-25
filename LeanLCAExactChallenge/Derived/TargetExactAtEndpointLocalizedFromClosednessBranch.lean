import LeanLCAExactChallenge.Derived.TargetExactAtFromClosednessBranch

/-!
W860 feeds the W859 target-ExactAt-from-closedness route from W726 endpoint
strict-topology plus localized-right-adjoint data.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/--
W860 derives W859's endpoint ExactAt topology facts from the W720 endpoint
strict-topology component bundled in W726 endpoint/localized data.
-/
def endpointExactAtTopologyFactsOfEndpointLocalizedRightAdjointW860
    (endpointLocalizedData :
      MetrizableWppEndpointLocalizedRightAdjointDataProviderW726) :
    MetrizableWppEndpointExactAtTopologyFactsProviderW859
    where
  closedEmbedding_of_exactAt := by
    intro K i _hExact
    exact
      endpointClosedEmbedding_of_endpointStrictTopologyDataW720
        (endpointStrictTopologyData_of_endpointLocalizedRightAdjointDataW726
          endpointLocalizedData) K i
  openMap_of_exactAt := by
    intro K i _hExact
    exact
      endpointOpenMap_of_endpointStrictTopologyDataW720
        (endpointStrictTopologyData_of_endpointLocalizedRightAdjointDataW726
          endpointLocalizedData) K i
  epi_of_exactAt := by
    intro K i hExact
    exact
      endpointEpiOfExactAt_of_endpointStrictTopologyDataW720
        (endpointStrictTopologyData_of_endpointLocalizedRightAdjointDataW726
          endpointLocalizedData) K i hExact

/- W860 data for W859 after W726 bundles endpoint facts and localized data. -/
structure MetrizableEndpointLocalizedTargetExactAtClosednessBranchDataW860 :
    Type 2 where
  closednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  endpointLocalizedRightAdjointData :
    MetrizableWppEndpointLocalizedRightAdjointDataProviderW726
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785

/-- W860 supplies W859 data from W725 closedness plus W726 endpoint/localized data. -/
noncomputable def closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
    (data : MetrizableEndpointLocalizedTargetExactAtClosednessBranchDataW860) :
    MetrizableClosednessBranchTargetExactAtLeftCalculusDataW859
    where
  closednessData := data.closednessData
  endpointExactAtTopologyFacts :=
    endpointExactAtTopologyFactsOfEndpointLocalizedRightAdjointW860
      data.endpointLocalizedRightAdjointData
  targetExactAtPayload := data.targetExactAtPayload
  localizedRightAdjointData :=
    localizedRightAdjointData_of_endpointLocalizedRightAdjointDataW726
      data.endpointLocalizedRightAdjointData

/--
W860 direct bounded left calculus from W725 closedness, W726 endpoint/localized
data, and W785 target ExactAt payload.
-/
theorem directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860
    (data : MetrizableEndpointLocalizedTargetExactAtClosednessBranchDataW860) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  Dbounded.directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859
    (Dbounded.closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
      data)

/- W860 stable route through W859 after W726 supplies endpoint/localized data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfEndpointLocalizedClosednessBranchTargetExactAtW860
    (data : MetrizableEndpointLocalizedTargetExactAtClosednessBranchDataW860)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        Dbounded.directBoundedLeftCalculusOfTargetExactAtW832
          (Dbounded.targetExactAtLeftCalculusDataOfClosednessBranchW859
            (Dbounded.closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
              data))
      letI : Preadditive (Dbounded MetrizableLCA.{0}) :=
        Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : HasZeroObject (Dbounded MetrizableLCA.{0}) :=
        Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive := by
        intro n
        exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
          MetrizableLCA.{0} n
      Pretriangulated (Dbounded MetrizableLCA.{0}))
    (triangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        Dbounded.directBoundedLeftCalculusOfTargetExactAtW832
          (Dbounded.targetExactAtLeftCalculusDataOfClosednessBranchW859
            (Dbounded.closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
              data))
      letI : Preadditive (Dbounded MetrizableLCA.{0}) :=
        Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : HasZeroObject (Dbounded MetrizableLCA.{0}) :=
        Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive := by
        intro n
        exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
          MetrizableLCA.{0} n
      letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := pretriangulated
      IsTriangulated (Dbounded MetrizableLCA.{0})) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfClosednessBranchTargetExactAtW859
    (Dbounded.closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
      data)
    finiteLimits finiteColimits pretriangulated triangulated

/-- W860 direct-left-calculus inputs after W726 bundles endpoint and localized data. -/
def endpointLocalizedClosednessBranchTargetExactAtLeftCalculusInputNamesW860 :
    List String :=
  ["matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "W726 endpoint/localized-right-adjoint data provider",
    "W785 target ExactAt payload for exact-acyclic homotopy objects"]

theorem
    endpointLocalizedClosednessBranchTargetExactAtLeftCalculusInputNamesW860_count :
    endpointLocalizedClosednessBranchTargetExactAtLeftCalculusInputNamesW860.length =
      3 :=
  rfl

/-- W860 expanded stable-route requirements. -/
def endpointLocalizedClosednessBranchTargetExactAtStableRouteExpandedInputNamesW860 :
    List String :=
  endpointLocalizedClosednessBranchTargetExactAtLeftCalculusInputNamesW860 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

theorem
    endpointLocalizedClosednessBranchTargetExactAtStableRouteExpandedInputNamesW860_count :
    endpointLocalizedClosednessBranchTargetExactAtStableRouteExpandedInputNamesW860.length =
      7 :=
  rfl

/- Current checked W860 state for the W726-to-W859 route. -/
structure MetrizableEndpointLocalizedClosednessBranchTargetExactAtRouteStateW860 :
    Type where
  seed : String
  declarations : List String
  endpointFactsResult : String
  localizedRightAdjointResult : String
  leftCalculusResult : String
  stablePackageResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/- Current W860 nonterminal state. -/
def currentMetrizableEndpointLocalizedClosednessBranchTargetExactAtRouteStateW860 :
    MetrizableEndpointLocalizedClosednessBranchTargetExactAtRouteStateW860
    where
  seed := "w860-target-exact-at-endpoint-localized-from-closedness-branch"
  declarations :=
    ["endpointExactAtTopologyFactsOfEndpointLocalizedRightAdjointW860",
      "MetrizableEndpointLocalizedTargetExactAtClosednessBranchDataW860",
      "closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860",
      "directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860",
      "boundedDerivedInfinityCategoryOfEndpointLocalizedClosednessBranchTargetExactAtW860",
      "endpointLocalizedClosednessBranchTargetExactAtLeftCalculusInputNamesW860",
      "endpointLocalizedClosednessBranchTargetExactAtLeftCalculusInputNamesW860_count",
      "endpointLocalizedClosednessBranchTargetExactAtStableRouteExpandedInputNamesW860",
      "endpointLocalizedClosednessBranchTargetExactAtStableRouteExpandedInputNamesW860_count"]
  endpointFactsResult :=
    "proved: W726's W720 endpoint strict-topology data supplies W859's \
      endpoint ExactAt closed-embedding, open-map, and epi facts"
  localizedRightAdjointResult :=
    "proved: W726 projects to the W721 localized-right-adjoint data consumed by W859"
  leftCalculusResult :=
    "proved: W859 consumes the W860 endpoint/localized data surface to produce \
      direct bounded left calculus"
  stablePackageResult :=
    "proved: the W859 stable package can be invoked through the W860 data surface"
  replacedInputs :=
    ["separate W859 endpoint ExactAt topology-facts provider",
      "separate W721 bounded homotopy localized-right-adjoint data provider"]
  remainingInputs :=
    endpointLocalizedClosednessBranchTargetExactAtStableRouteExpandedInputNamesW860
  productSuccessClaimed := false

theorem currentW860EndpointLocalizedClosednessBranchTargetExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableEndpointLocalizedClosednessBranchTargetExactAtRouteStateW860;
      state.productSuccessClaimed) =
        false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
