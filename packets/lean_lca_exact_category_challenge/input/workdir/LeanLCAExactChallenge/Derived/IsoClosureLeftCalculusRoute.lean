import LeanLCAExactChallenge.Derived.TargetIsoLeftCalculusRoute
import LeanLCAExactChallenge.Derived.IsoClosureStrictRealizationTerminalProductRoute

/-!
W834 routes W651 iso-closure realization data into the W833 target-isomorphism
left-calculus route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/-- W834 inputs for deriving W833 data through W810 and W809. -/
structure MetrizableIsoClosureRealizationLeftCalculusDataW834 : Type 2 where
  closedRangeEndpointTopology : MetrizableExactAtClosedRangeEndpointTopologyInputsW696
  isoClosureRealization : MetrizableExactAcyclicIsoClosureTrianglehIso13RealizationInputW651
  localizedRightAdjointData : MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W834 derives the W784 target-isomorphism realization from W651 data. -/
noncomputable def targetIsoRealizationOfIsoClosureLeftCalculusW834
    (data : MetrizableIsoClosureRealizationLeftCalculusDataW834) :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784 :=
  targetIsoRealizationOfTrianglehRealizationW809
    (strictRealizationOfIsoClosureRealizationW810 data.isoClosureRealization)

/-- W834 supplies W833 target-isomorphism left-calculus data from W651/W696/W721. -/
noncomputable def targetIsoLeftCalculusDataOfIsoClosureRealizationW834
    (data : MetrizableIsoClosureRealizationLeftCalculusDataW834) :
    MetrizableTargetIsoLeftCalculusDataW833 where
  closedRangeEndpointTopology := data.closedRangeEndpointTopology
  targetIsoRealization := targetIsoRealizationOfIsoClosureLeftCalculusW834 data
  localizedRightAdjointData := data.localizedRightAdjointData

/-- W834 derives the W785 target ExactAt payload through the W833 route. -/
noncomputable def targetExactAtPayloadOfIsoClosureLeftCalculusW834
    (data : MetrizableIsoClosureRealizationLeftCalculusDataW834) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  targetExactAtPayloadOfTargetIsoLeftCalculusW833
    (targetIsoLeftCalculusDataOfIsoClosureRealizationW834 data)

/-- W834 proves direct bounded left calculus from W651 iso-closure route data. -/
theorem directBoundedLeftCalculusOfIsoClosureRealizationW834
    (data : MetrizableIsoClosureRealizationLeftCalculusDataW834) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetIsoW833
    (targetIsoLeftCalculusDataOfIsoClosureRealizationW834 data)

/-- W834 stable route using W651-derived target-isomorphism data. -/
noncomputable def boundedDerivedInfinityCategoryOfIsoClosureLeftCalculusW834
    (data : MetrizableIsoClosureRealizationLeftCalculusDataW834)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfIsoClosureRealizationW834 data
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
        directBoundedLeftCalculusOfIsoClosureRealizationW834 data
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
    directBoundedLeftCalculusOfIsoClosureRealizationW834 data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/-- W834 direct-left-calculus inputs after deriving W833's W784 input through W810/W809. -/
def isoClosureLeftCalculusInputNamesW834 : List String :=
  ["W696 closed-range endpoint topology",
    "W651 exact-acyclic iso-closure strict realization data",
    "W721 bounded homotopy localized right adjoint data"]

/-- W834 uses three concrete inputs for direct left calculus. -/
theorem isoClosureLeftCalculusInputNamesW834_count :
    Dbounded.isoClosureLeftCalculusInputNamesW834.length = 3 :=
  rfl

/-- W834 stable route requirements when iso-closure data are bundled. -/
def isoClosureLeftCalculusStableRouteRequiredFieldNamesW834 : List String :=
  ["MetrizableIsoClosureRealizationLeftCalculusDataW834",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)"]

/-- W834 keeps the stable route to five bundled requirements. -/
theorem isoClosureLeftCalculusStableRouteRequiredFieldNamesW834_count :
    Dbounded.isoClosureLeftCalculusStableRouteRequiredFieldNamesW834.length = 5 :=
  rfl

/-- Expanded W834 requirements, showing the current concrete route obligations. -/
def isoClosureLeftCalculusExpandedRequiredFieldNamesW834 : List String :=
  Dbounded.isoClosureLeftCalculusInputNamesW834 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

/-- The W834 expanded stable route has seven concrete requirements. -/
theorem isoClosureLeftCalculusExpandedRequiredFieldNamesW834_count :
    Dbounded.isoClosureLeftCalculusExpandedRequiredFieldNamesW834.length = 7 :=
  rfl

/-- Current checked W834 state for the iso-closure left-calculus route. -/
structure MetrizableIsoClosureLeftCalculusRouteStateW834 : Type where
  seed : String
  declarations : List String
  leftCalculusResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W834 state. -/
def currentMetrizableIsoClosureLeftCalculusRouteStateW834 :
    Dbounded.MetrizableIsoClosureLeftCalculusRouteStateW834 where
  seed := "w834-iso-closure-left-calculus-route"
  declarations :=
    ["MetrizableIsoClosureRealizationLeftCalculusDataW834",
      "targetIsoRealizationOfIsoClosureLeftCalculusW834",
      "targetIsoLeftCalculusDataOfIsoClosureRealizationW834",
      "targetExactAtPayloadOfIsoClosureLeftCalculusW834",
      "directBoundedLeftCalculusOfIsoClosureRealizationW834",
      "boundedDerivedInfinityCategoryOfIsoClosureLeftCalculusW834",
      "isoClosureLeftCalculusInputNamesW834",
      "isoClosureLeftCalculusInputNamesW834_count",
      "isoClosureLeftCalculusStableRouteRequiredFieldNamesW834",
      "isoClosureLeftCalculusStableRouteRequiredFieldNamesW834_count",
      "isoClosureLeftCalculusExpandedRequiredFieldNamesW834",
      "isoClosureLeftCalculusExpandedRequiredFieldNamesW834_count"]
  leftCalculusResult :=
    "proved: W696/W651/W721 data supply W833 target-isomorphism left-calculus data"
  replacedInputs :=
    ["W784 exact-acyclic homotopy-object target-isomorphism realization"]
  remainingInputs :=
    Dbounded.isoClosureLeftCalculusExpandedRequiredFieldNamesW834
  productSuccessClaimed := false

theorem currentMetrizableIsoClosureLeftCalculusRouteStateW834_productSuccess :
    Dbounded.currentMetrizableIsoClosureLeftCalculusRouteStateW834.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
