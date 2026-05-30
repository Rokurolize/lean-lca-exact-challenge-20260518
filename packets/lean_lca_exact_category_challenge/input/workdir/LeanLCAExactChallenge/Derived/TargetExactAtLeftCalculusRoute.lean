import LeanLCAExactChallenge.Derived.ComparisonBijectivityLeftCalculusRoute
import LeanLCAExactChallenge.Derived.TargetExactAtClosedRangeProductRoute
import LeanLCAExactChallenge.Derived.KernelCokernelProductRoute

/-!
W832 target-ExactAt route into direct bounded left calculus.

This module replaces W831's three direct-left-calculus fields with the more
concrete W696 closed-range endpoint topology, W785 target ExactAt payload, and
W721 localized-right-adjoint provider.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/-- W832 concrete inputs for the W831 direct-left-calculus data package. -/
structure MetrizableTargetExactAtLeftCalculusDataW832 : Type 2 where
  closedRangeEndpointTopology : MetrizableExactAtClosedRangeEndpointTopologyInputsW696
  targetExactAtPayload : MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785
  localizedRightAdjointData : MetrizableWppLocalizedRightAdjointDataProviderW721

/--
W832 supplies W831's direct-left-calculus data from W696/W785/W721 route inputs.
-/
noncomputable def targetExactAtLeftCalculusDataW832
    (data : MetrizableTargetExactAtLeftCalculusDataW832) :
    MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831 where
  exactClosed2 :=
    exactClosed2OfTargetExactAtClosedRangeW796
      data.closedRangeEndpointTopology data.targetExactAtPayload
  kernelCokernelTopologyData :=
    metrizableExactAtKernelCokernelConditionedTopologyInputs_of_closedRangeEndpointTopologyW696
      data.closedRangeEndpointTopology
  localizedRightAdjoint :=
    boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
      data.localizedRightAdjointData

/--
W832 proves direct bounded left calculus from comparison bijectivity plus the
W696/W785/W721 input surface.
-/
theorem directBoundedLeftCalculusOfTargetExactAtW832
    (data : MetrizableTargetExactAtLeftCalculusDataW832) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  Dbounded.directBoundedLeftCalculusOfComparisonBijectivityW831
    (Dbounded.targetExactAtLeftCalculusDataW832 data)

/-- W832 stable route using the target-ExactAt direct-left-calculus data. -/
noncomputable def boundedDerivedInfinityCategoryOfTargetExactAtLeftCalculusW832
    (data : MetrizableTargetExactAtLeftCalculusDataW832)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfTargetExactAtW832 data
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
        directBoundedLeftCalculusOfTargetExactAtW832 data
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
      (Dbounded.infinityCategory MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfTargetExactAtW832 data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/-- W832 direct-left-calculus inputs after expanding W831 fields through W696/W785/W721. -/
def targetExactAtLeftCalculusInputNamesW832 : List String :=
  ["W696 closed-range endpoint topology",
    "W785 target ExactAt payload for exact-acyclic homotopy objects",
    "W721 bounded homotopy localized right adjoint data"]

/-- W832 uses three concrete inputs for direct left calculus. -/
theorem targetExactAtLeftCalculusInputNamesW832_count :
    Dbounded.targetExactAtLeftCalculusInputNamesW832.length = 3 :=
  rfl

/-- W832 stable route requirements when the target-ExactAt data are bundled. -/
def targetExactAtLeftCalculusStableRouteRequiredFieldNamesW832 : List String :=
  ["MetrizableTargetExactAtLeftCalculusDataW832",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)"]

/-- W832 keeps the stable route to five bundled requirements. -/
theorem targetExactAtLeftCalculusStableRouteRequiredFieldNamesW832_count :
    Dbounded.targetExactAtLeftCalculusStableRouteRequiredFieldNamesW832.length =
      5 :=
  rfl

/-- Expanded W832 requirements, showing the current concrete route obligations. -/
def targetExactAtLeftCalculusExpandedRequiredFieldNamesW832 : List String :=
  Dbounded.targetExactAtLeftCalculusInputNamesW832 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

/-- The W832 expanded stable route has seven concrete requirements. -/
theorem targetExactAtLeftCalculusExpandedRequiredFieldNamesW832_count :
    Dbounded.targetExactAtLeftCalculusExpandedRequiredFieldNamesW832.length = 7 :=
  rfl

/-- Current checked W832 state for the target-ExactAt left-calculus route. -/
structure MetrizableTargetExactAtLeftCalculusRouteStateW832 : Type where
  seed : String
  declarations : List String
  leftCalculusResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W832 state. -/
def currentMetrizableTargetExactAtLeftCalculusRouteStateW832 :
    Dbounded.MetrizableTargetExactAtLeftCalculusRouteStateW832 where
  seed := "w832-target-exact-at-left-calculus-route"
  declarations :=
    ["MetrizableTargetExactAtLeftCalculusDataW832",
      "targetExactAtLeftCalculusDataW832",
      "directBoundedLeftCalculusOfTargetExactAtW832",
      "boundedDerivedInfinityCategoryOfTargetExactAtLeftCalculusW832",
      "targetExactAtLeftCalculusInputNamesW832",
      "targetExactAtLeftCalculusInputNamesW832_count",
      "targetExactAtLeftCalculusStableRouteRequiredFieldNamesW832",
      "targetExactAtLeftCalculusStableRouteRequiredFieldNamesW832_count",
      "targetExactAtLeftCalculusExpandedRequiredFieldNamesW832",
      "targetExactAtLeftCalculusExpandedRequiredFieldNamesW832_count"]
  leftCalculusResult :=
    "proved: W696/W785/W721 data supply W831 direct-left-calculus data"
  replacedInputs :=
    ["exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "MetrizableExactAtKernelCokernelConditionedTopologyInputs",
      "BoundedHomotopyLocalizedRightAdjointInput MetrizableLCA"]
  remainingInputs :=
    Dbounded.targetExactAtLeftCalculusExpandedRequiredFieldNamesW832
  productSuccessClaimed := false

theorem currentMetrizableTargetExactAtLeftCalculusRouteStateW832_productSuccess :
    Dbounded.currentMetrizableTargetExactAtLeftCalculusRouteStateW832.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
