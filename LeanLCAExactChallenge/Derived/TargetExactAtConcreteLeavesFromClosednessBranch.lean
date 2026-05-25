import LeanLCAExactChallenge.Derived.TargetExactAtEndpointLocalizedFromClosednessBranch

/-!
W861 feeds the W860 endpoint/localized target-ExactAt route from W733 concrete
leaves plus W785 target ExactAt payload data.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/- W861 data for W860 after W733 supplies W725 closedness and W726 data. -/
structure MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861 :
    Type 2 where
  concreteLeaves :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785

/--
W861 supplies W860 data from W733 concrete leaves by projecting the W725
closedness branch and assembling W726 endpoint/localized data.
-/
noncomputable def endpointLocalizedTargetExactAtDataOfConcreteLeavesW861
    (data : MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861) :
    MetrizableEndpointLocalizedTargetExactAtClosednessBranchDataW860
    where
  closednessData := data.concreteLeaves.diagramAndMappedCokernelClosednessData
  endpointLocalizedRightAdjointData :=
    endpointLocalizedRightAdjointData_of_concreteLeavesW733
      data.concreteLeaves
  targetExactAtPayload := data.targetExactAtPayload

/-- W861 direct bounded left calculus from W733 concrete leaves and W785 payload. -/
theorem directBoundedLeftCalculusOfConcreteLeavesTargetExactAtW861
    (data : MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  Dbounded.directBoundedLeftCalculusOfEndpointLocalizedClosednessBranchTargetExactAtW860
    (Dbounded.endpointLocalizedTargetExactAtDataOfConcreteLeavesW861 data)

/- W861 stable route through W860 after W733 supplies W725 and W726. -/
noncomputable def boundedDerivedInfinityCategoryOfConcreteLeavesTargetExactAtW861
    (data : MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        Dbounded.directBoundedLeftCalculusOfTargetExactAtW832
          (Dbounded.targetExactAtLeftCalculusDataOfClosednessBranchW859
            (Dbounded.closednessBranchTargetExactAtLeftCalculusDataOfEndpointLocalizedW860
              (Dbounded.endpointLocalizedTargetExactAtDataOfConcreteLeavesW861
                data)))
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
              (Dbounded.endpointLocalizedTargetExactAtDataOfConcreteLeavesW861
                data)))
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
  Dbounded.boundedDerivedInfinityCategoryOfEndpointLocalizedClosednessBranchTargetExactAtW860
    (Dbounded.endpointLocalizedTargetExactAtDataOfConcreteLeavesW861 data)
    finiteLimits finiteColimits pretriangulated triangulated

/-- W861 direct-left-calculus inputs after W733 supplies W725 and W726. -/
def concreteLeavesTargetExactAtLeftCalculusInputNamesW861 : List String :=
  ["W733 concrete leaves for W725 closedness and W726 endpoint/localized data",
    "W785 target ExactAt payload for exact-acyclic homotopy objects"]

theorem concreteLeavesTargetExactAtLeftCalculusInputNamesW861_count :
    concreteLeavesTargetExactAtLeftCalculusInputNamesW861.length = 2 :=
  rfl

/-- W861 expanded stable-route requirements. -/
def concreteLeavesTargetExactAtStableRouteExpandedInputNamesW861 :
    List String :=
  concreteLeavesTargetExactAtLeftCalculusInputNamesW861 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

theorem concreteLeavesTargetExactAtStableRouteExpandedInputNamesW861_count :
    concreteLeavesTargetExactAtStableRouteExpandedInputNamesW861.length = 6 :=
  rfl

/- Current checked W861 state for the W733-to-W860 route. -/
structure MetrizableConcreteLeavesTargetExactAtRouteStateW861 :
    Type where
  seed : String
  declarations : List String
  concreteLeavesProjectionResult : String
  leftCalculusResult : String
  stablePackageResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/- Current W861 nonterminal state. -/
def currentMetrizableConcreteLeavesTargetExactAtRouteStateW861 :
    MetrizableConcreteLeavesTargetExactAtRouteStateW861
    where
  seed := "w861-target-exact-at-concrete-leaves-from-closedness-branch"
  declarations :=
    ["MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861",
      "endpointLocalizedTargetExactAtDataOfConcreteLeavesW861",
      "directBoundedLeftCalculusOfConcreteLeavesTargetExactAtW861",
      "boundedDerivedInfinityCategoryOfConcreteLeavesTargetExactAtW861",
      "concreteLeavesTargetExactAtLeftCalculusInputNamesW861",
      "concreteLeavesTargetExactAtLeftCalculusInputNamesW861_count",
      "concreteLeavesTargetExactAtStableRouteExpandedInputNamesW861",
      "concreteLeavesTargetExactAtStableRouteExpandedInputNamesW861_count"]
  concreteLeavesProjectionResult :=
    "proved: W733 concrete leaves project to W725 closedness and assemble W726 \
      endpoint/localized data"
  leftCalculusResult :=
    "proved: W860 consumes the W861 concrete-leaves data surface to produce \
      direct bounded left calculus"
  stablePackageResult :=
    "proved: the W860 stable package can be invoked through the W861 data surface"
  replacedInputs :=
    ["separate W725 matched closedness branch provider",
      "separate W726 endpoint/localized-right-adjoint data provider"]
  remainingInputs :=
    concreteLeavesTargetExactAtStableRouteExpandedInputNamesW861
  productSuccessClaimed := false

theorem currentW861ConcreteLeavesTargetExactAtRoute_productSuccess :
    currentMetrizableConcreteLeavesTargetExactAtRouteStateW861.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
