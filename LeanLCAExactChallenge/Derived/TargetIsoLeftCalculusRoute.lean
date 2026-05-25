import LeanLCAExactChallenge.Derived.TargetExactAtLeftCalculusRoute
import LeanLCAExactChallenge.Derived.TargetIsoToTargetExactAtTerminalProductRoute

/-!
W833 routes target-isomorphism realization data into the W832 target-ExactAt
left-calculus route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/-- W833 inputs for deriving W832 data through W808 target-isomorphism conversion. -/
structure MetrizableTargetIsoLeftCalculusDataW833 : Type 2 where
  closedRangeEndpointTopology : MetrizableExactAtClosedRangeEndpointTopologyInputsW696
  targetIsoRealization : MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784
  localizedRightAdjointData : MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W833 derives the W785 target ExactAt payload from W784 and W696 data. -/
noncomputable def targetExactAtPayloadOfTargetIsoLeftCalculusW833
    (data : MetrizableTargetIsoLeftCalculusDataW833) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  targetExactAtPayloadOfTargetIsoRealizationW808
    (cochainHasHomology_of_leftRightComparisonIsoW768
      universalLeftRightComparisonIso_of_comparisonBijectivityW831)
    ((metrizableExactAtKernelCokernelConditionedTopologyInputs_of_closedRangeEndpointTopologyW696
      data.closedRangeEndpointTopology).forgetPreservesHomology)
    data.targetIsoRealization

/-- W833 supplies W832 target-ExactAt left-calculus data from W784/W696/W721. -/
noncomputable def targetExactAtLeftCalculusDataOfTargetIsoW833
    (data : MetrizableTargetIsoLeftCalculusDataW833) :
    MetrizableTargetExactAtLeftCalculusDataW832 where
  closedRangeEndpointTopology := data.closedRangeEndpointTopology
  targetExactAtPayload := targetExactAtPayloadOfTargetIsoLeftCalculusW833 data
  localizedRightAdjointData := data.localizedRightAdjointData

/-- W833 proves direct bounded left calculus from target-isomorphism route data. -/
theorem directBoundedLeftCalculusOfTargetIsoW833
    (data : MetrizableTargetIsoLeftCalculusDataW833) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetExactAtW832
    (targetExactAtLeftCalculusDataOfTargetIsoW833 data)

/-- W833 stable route using target-isomorphism-derived target-ExactAt data. -/
noncomputable def boundedDerivedInfinityCategoryOfTargetIsoLeftCalculusW833
    (data : MetrizableTargetIsoLeftCalculusDataW833)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfTargetIsoW833 data
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
        directBoundedLeftCalculusOfTargetIsoW833 data
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
    directBoundedLeftCalculusOfTargetIsoW833 data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/-- W833 direct-left-calculus inputs after deriving W832's W785 payload through W808. -/
def targetIsoLeftCalculusInputNamesW833 : List String :=
  ["W696 closed-range endpoint topology",
    "W784 exact-acyclic homotopy-object target-isomorphism realization",
    "W721 bounded homotopy localized right adjoint data"]

/-- W833 uses three concrete inputs for direct left calculus. -/
theorem targetIsoLeftCalculusInputNamesW833_count :
    Dbounded.targetIsoLeftCalculusInputNamesW833.length = 3 :=
  rfl

/-- W833 stable route requirements when target-isomorphism data are bundled. -/
def targetIsoLeftCalculusStableRouteRequiredFieldNamesW833 : List String :=
  ["MetrizableTargetIsoLeftCalculusDataW833",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)"]

/-- W833 keeps the stable route to five bundled requirements. -/
theorem targetIsoLeftCalculusStableRouteRequiredFieldNamesW833_count :
    Dbounded.targetIsoLeftCalculusStableRouteRequiredFieldNamesW833.length = 5 :=
  rfl

/-- Expanded W833 requirements, showing the current concrete route obligations. -/
def targetIsoLeftCalculusExpandedRequiredFieldNamesW833 : List String :=
  Dbounded.targetIsoLeftCalculusInputNamesW833 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

/-- The W833 expanded stable route has seven concrete requirements. -/
theorem targetIsoLeftCalculusExpandedRequiredFieldNamesW833_count :
    Dbounded.targetIsoLeftCalculusExpandedRequiredFieldNamesW833.length = 7 :=
  rfl

/-- Current checked W833 state for the target-isomorphism left-calculus route. -/
structure MetrizableTargetIsoLeftCalculusRouteStateW833 : Type where
  seed : String
  declarations : List String
  leftCalculusResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W833 state. -/
def currentMetrizableTargetIsoLeftCalculusRouteStateW833 :
    Dbounded.MetrizableTargetIsoLeftCalculusRouteStateW833 where
  seed := "w833-target-iso-left-calculus-route"
  declarations :=
    ["MetrizableTargetIsoLeftCalculusDataW833",
      "targetExactAtPayloadOfTargetIsoLeftCalculusW833",
      "targetExactAtLeftCalculusDataOfTargetIsoW833",
      "directBoundedLeftCalculusOfTargetIsoW833",
      "boundedDerivedInfinityCategoryOfTargetIsoLeftCalculusW833",
      "targetIsoLeftCalculusInputNamesW833",
      "targetIsoLeftCalculusInputNamesW833_count",
      "targetIsoLeftCalculusStableRouteRequiredFieldNamesW833",
      "targetIsoLeftCalculusStableRouteRequiredFieldNamesW833_count",
      "targetIsoLeftCalculusExpandedRequiredFieldNamesW833",
      "targetIsoLeftCalculusExpandedRequiredFieldNamesW833_count"]
  leftCalculusResult :=
    "proved: W696/W784/W721 data supply W832 target-ExactAt left-calculus data"
  replacedInputs :=
    ["W785 target ExactAt payload for exact-acyclic homotopy objects"]
  remainingInputs :=
    Dbounded.targetIsoLeftCalculusExpandedRequiredFieldNamesW833
  productSuccessClaimed := false

theorem currentMetrizableTargetIsoLeftCalculusRouteStateW833_productSuccess :
    Dbounded.currentMetrizableTargetIsoLeftCalculusRouteStateW833.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
