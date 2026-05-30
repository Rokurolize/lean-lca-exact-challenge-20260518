import LeanLCAExactChallenge.Derived.EndpointTopologyFromClosednessBranch
import LeanLCAExactChallenge.Derived.TargetExactAtLeftCalculusRoute

/-!
W859 feeds the W832 target-ExactAt left-calculus route from the same W725/W519
closedness branch used by the W856 endpoint route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519
open scoped ZeroObject

namespace Dbounded

/-- W859 extracts W696's closed-range provider from the matched W725 closedness branch. -/
@[reducible]
def closedRangeProviderOfClosednessBranchW859
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725) :
    MappedExplicitCokernelClosedRangeProviderW519 :=
  match closednessData with
  | .closedMap _ mappedCokernelClosedMapProvider =>
      closedRangeProvider_of_closedMapProvider_w519
        mappedCokernelClosedMapProvider
  | .closedEmbedding _ mappedCokernelClosedEmbeddingProvider =>
      closedRangeProvider_of_closedEmbeddingProvider_w519
        mappedCokernelClosedEmbeddingProvider

/--
W859 endpoint ExactAt facts after removing W696's closed-range-provider field:
the W725/W519 closedness branch supplies that field.
-/
structure MetrizableWppEndpointExactAtTopologyFactsProviderW859 :
    Type 2 where
  closedEmbedding_of_exactAt :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      K.ExactAt i →
        Topology.IsClosedEmbedding ((K.sc i).f : (K.sc i).X₁ → (K.sc i).X₂)
  openMap_of_exactAt :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      K.ExactAt i → IsOpenMap ((K.sc i).g : (K.sc i).X₂ → (K.sc i).X₃)
  epi_of_exactAt :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      K.ExactAt i → Epi ((K.sc i).g)

/--
W859 reconstructs W696 closed-range endpoint topology from W725 closedness plus
ExactAt facts.
-/
def closedRangeEndpointTopologyOfClosednessBranchW859
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725)
    (endpointFacts : MetrizableWppEndpointExactAtTopologyFactsProviderW859) :
    MetrizableExactAtClosedRangeEndpointTopologyInputsW696 where
  closedRangeProvider :=
    closedRangeProviderOfClosednessBranchW859 closednessData
  closedEmbedding_of_exactAt := endpointFacts.closedEmbedding_of_exactAt
  openMap_of_exactAt := endpointFacts.openMap_of_exactAt
  epi_of_exactAt := endpointFacts.epi_of_exactAt

/- W859 data for the target-ExactAt route after deriving W696's closedness field. -/
structure MetrizableClosednessBranchTargetExactAtLeftCalculusDataW859 :
    Type 2 where
  closednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  endpointExactAtTopologyFacts :
    MetrizableWppEndpointExactAtTopologyFactsProviderW859
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W859 supplies W832's data package from W725 closedness plus endpoint ExactAt facts. -/
noncomputable def targetExactAtLeftCalculusDataOfClosednessBranchW859
    (data : MetrizableClosednessBranchTargetExactAtLeftCalculusDataW859) :
    MetrizableTargetExactAtLeftCalculusDataW832 where
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosednessBranchW859
      data.closednessData data.endpointExactAtTopologyFacts
  targetExactAtPayload := data.targetExactAtPayload
  localizedRightAdjointData := data.localizedRightAdjointData

/--
W859 direct bounded left calculus through W832 from W725 closedness and
endpoint ExactAt facts.
-/
theorem directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859
    (data : MetrizableClosednessBranchTargetExactAtLeftCalculusDataW859) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  Dbounded.directBoundedLeftCalculusOfTargetExactAtW832
    (Dbounded.targetExactAtLeftCalculusDataOfClosednessBranchW859 data)

/-- W859 stable route through W832 from W725 closedness and endpoint ExactAt facts. -/
noncomputable def boundedDerivedInfinityCategoryOfClosednessBranchTargetExactAtW859
    (data : MetrizableClosednessBranchTargetExactAtLeftCalculusDataW859)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        Dbounded.directBoundedLeftCalculusOfTargetExactAtW832
          (Dbounded.targetExactAtLeftCalculusDataOfClosednessBranchW859 data)
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
          (Dbounded.targetExactAtLeftCalculusDataOfClosednessBranchW859 data)
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
  Dbounded.boundedDerivedInfinityCategoryOfTargetExactAtLeftCalculusW832
    (Dbounded.targetExactAtLeftCalculusDataOfClosednessBranchW859 data)
    finiteLimits finiteColimits pretriangulated triangulated

/-- W859 endpoint ExactAt facts still required after W725 supplies closed-range data. -/
def endpointExactAtTopologyFactInputNamesW859 : List String :=
  ["ExactAt supplies endpoint closed-embedding facts",
    "ExactAt supplies endpoint open-map facts",
    "ExactAt supplies endpoint epi facts"]

theorem endpointExactAtTopologyFactInputNamesW859_count :
    endpointExactAtTopologyFactInputNamesW859.length = 3 :=
  rfl

/-- W859 direct-left-calculus inputs after deriving W696's closedness field from W725. -/
def closednessBranchTargetExactAtLeftCalculusInputNamesW859 :
    List String :=
  ["matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "endpoint ExactAt topology facts excluding the W519 closed-range provider",
    "W785 target ExactAt payload for exact-acyclic homotopy objects",
    "W721 bounded homotopy localized-right-adjoint data provider"]

theorem closednessBranchTargetExactAtLeftCalculusInputNamesW859_count :
    closednessBranchTargetExactAtLeftCalculusInputNamesW859.length = 4 :=
  rfl

/-- W859 expanded stable-route requirements. -/
def closednessBranchTargetExactAtStableRouteExpandedInputNamesW859 :
    List String :=
  closednessBranchTargetExactAtLeftCalculusInputNamesW859 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

theorem closednessBranchTargetExactAtStableRouteExpandedInputNamesW859_count :
    closednessBranchTargetExactAtStableRouteExpandedInputNamesW859.length = 8 :=
  rfl

/-- Current checked W859 state for the W725-to-W832 target-ExactAt route. -/
structure MetrizableClosednessBranchTargetExactAtRouteStateW859 :
    Type where
  seed : String
  declarations : List String
  closedRangeProviderResult : String
  routeDataResult : String
  leftCalculusResult : String
  stablePackageResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current W859 nonterminal state. -/
def currentMetrizableClosednessBranchTargetExactAtRouteStateW859 :
    MetrizableClosednessBranchTargetExactAtRouteStateW859
    where
  seed := "w859-target-exact-at-from-w519-closedness-branch"
  declarations :=
    ["closedRangeProviderOfClosednessBranchW859",
      "MetrizableWppEndpointExactAtTopologyFactsProviderW859",
      "closedRangeEndpointTopologyOfClosednessBranchW859",
      "MetrizableClosednessBranchTargetExactAtLeftCalculusDataW859",
      "targetExactAtLeftCalculusDataOfClosednessBranchW859",
      "directBoundedLeftCalculusOfClosednessBranchTargetExactAtW859",
      "boundedDerivedInfinityCategoryOfClosednessBranchTargetExactAtW859",
      "endpointExactAtTopologyFactInputNamesW859",
      "endpointExactAtTopologyFactInputNamesW859_count",
      "closednessBranchTargetExactAtLeftCalculusInputNamesW859",
      "closednessBranchTargetExactAtLeftCalculusInputNamesW859_count",
      "closednessBranchTargetExactAtStableRouteExpandedInputNamesW859",
      "closednessBranchTargetExactAtStableRouteExpandedInputNamesW859_count"]
  closedRangeProviderResult :=
    "proved: the W725 closed-map or closed-embedding branch supplies W696's \
      W519 closed-range provider field"
  routeDataResult :=
    "proved: W725 closedness plus endpoint ExactAt facts reconstruct W696 \
      closed-range endpoint topology and feed W832"
  leftCalculusResult :=
    "proved: W832 consumes the W859 data surface to produce direct bounded \
      left calculus"
  stablePackageResult :=
    "proved: the W832 stable package can be invoked through the W859 data surface"
  replacedInputs :=
    ["separate W696 closed-range-provider field",
      "raw exactClosed2 input from the W858 route surface",
      "raw endpoint kernel/cokernel fact provider from the W858 route surface"]
  remainingInputs :=
    closednessBranchTargetExactAtStableRouteExpandedInputNamesW859
  productSuccessClaimed := false

theorem currentW859ClosednessBranchTargetExactAtRoute_productSuccess :
    currentMetrizableClosednessBranchTargetExactAtRouteStateW859.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
