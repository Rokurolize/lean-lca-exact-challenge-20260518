import LeanLCAExactChallenge.Derived.IsoClosureLeftCalculusRoute
import LeanLCAExactChallenge.Derived.TargetHomologyZeroExactInputsClosedRangeProductRoute

/-!
W835 routes W735 exact-input branch data into the W834 iso-closure
left-calculus route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/-- W835 closed-map inputs deriving W834 data through W790. -/
structure MetrizableClosedMapExactInputsIsoClosureLeftCalculusDataW835 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  isoClosureRealization :
    MetrizableExactAcyclicIsoClosureTrianglehIso13RealizationInputW651
  localizedRightAdjointData : MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W835 closed-embedding inputs deriving W834 data through W790. -/
structure MetrizableClosedEmbeddingExactInputsIsoClosureLeftCalculusDataW835 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  isoClosureRealization :
    MetrizableExactAcyclicIsoClosureTrianglehIso13RealizationInputW651
  localizedRightAdjointData : MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W835 closed-map data converted to W834 data. -/
noncomputable def isoClosureLeftCalculusDataOfClosedMapExactInputsW835
    (data : MetrizableClosedMapExactInputsIsoClosureLeftCalculusDataW835) :
    MetrizableIsoClosureRealizationLeftCalculusDataW834 where
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs
  isoClosureRealization := data.isoClosureRealization
  localizedRightAdjointData := data.localizedRightAdjointData

/-- W835 closed-embedding data converted to W834 data. -/
noncomputable def isoClosureLeftCalculusDataOfClosedEmbeddingExactInputsW835
    (data :
      MetrizableClosedEmbeddingExactInputsIsoClosureLeftCalculusDataW835) :
    MetrizableIsoClosureRealizationLeftCalculusDataW834 where
  closedRangeEndpointTopology :=
    closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790
      data.exactInputs
  isoClosureRealization := data.isoClosureRealization
  localizedRightAdjointData := data.localizedRightAdjointData

/-- W835 derives the W785 target ExactAt payload from closed-map exact inputs. -/
noncomputable def targetExactAtPayloadOfClosedMapExactInputsIsoClosureW835
    (data : MetrizableClosedMapExactInputsIsoClosureLeftCalculusDataW835) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  targetExactAtPayloadOfIsoClosureLeftCalculusW834
    (isoClosureLeftCalculusDataOfClosedMapExactInputsW835 data)

/--
W835 derives the W785 target ExactAt payload from closed-embedding exact
inputs.
-/
noncomputable def targetExactAtPayloadOfClosedEmbeddingExactInputsIsoClosureW835
    (data :
      MetrizableClosedEmbeddingExactInputsIsoClosureLeftCalculusDataW835) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  targetExactAtPayloadOfIsoClosureLeftCalculusW834
    (isoClosureLeftCalculusDataOfClosedEmbeddingExactInputsW835 data)

/-- W835 proves direct bounded left calculus from closed-map exact inputs. -/
theorem directBoundedLeftCalculusOfClosedMapExactInputsIsoClosureW835
    (data : MetrizableClosedMapExactInputsIsoClosureLeftCalculusDataW835) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfIsoClosureRealizationW834
    (isoClosureLeftCalculusDataOfClosedMapExactInputsW835 data)

/-- W835 proves direct bounded left calculus from closed-embedding exact inputs. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingExactInputsIsoClosureW835
    (data :
      MetrizableClosedEmbeddingExactInputsIsoClosureLeftCalculusDataW835) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfIsoClosureRealizationW834
    (isoClosureLeftCalculusDataOfClosedEmbeddingExactInputsW835 data)

/-- W835 stable route using closed-map exact-input data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapExactInputsIsoClosureW835
    (data : MetrizableClosedMapExactInputsIsoClosureLeftCalculusDataW835)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedMapExactInputsIsoClosureW835 data
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
        directBoundedLeftCalculusOfClosedMapExactInputsIsoClosureW835 data
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
    directBoundedLeftCalculusOfClosedMapExactInputsIsoClosureW835 data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/-- W835 stable route using closed-embedding exact-input data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsIsoClosureW835
    (data :
      MetrizableClosedEmbeddingExactInputsIsoClosureLeftCalculusDataW835)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedEmbeddingExactInputsIsoClosureW835
          data
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
        directBoundedLeftCalculusOfClosedEmbeddingExactInputsIsoClosureW835
          data
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
    directBoundedLeftCalculusOfClosedEmbeddingExactInputsIsoClosureW835 data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/-- W835 direct-left-calculus inputs after deriving W834's W696 field through W790. -/
def exactInputsIsoClosureLeftCalculusInputNamesW835 : List String :=
  ["W735 closed-map or closed-embedding exact inputs",
    "W651 exact-acyclic iso-closure strict realization data",
    "W721 bounded homotopy localized right adjoint data"]

/-- W835 uses three concrete inputs for direct left calculus. -/
theorem exactInputsIsoClosureLeftCalculusInputNamesW835_count :
    Dbounded.exactInputsIsoClosureLeftCalculusInputNamesW835.length = 3 :=
  rfl

/-- W835 stable route requirements when exact-input branch data are bundled. -/
def exactInputsIsoClosureLeftCalculusStableRouteRequiredFieldNamesW835 :
    List String :=
  ["closed-map or closed-embedding W835 exact-input data",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)"]

/-- W835 keeps the stable route to five bundled requirements. -/
theorem exactInputsIsoClosureLeftCalculusStableRouteRequiredFieldNamesW835_count :
    Dbounded.exactInputsIsoClosureLeftCalculusStableRouteRequiredFieldNamesW835.length =
      5 :=
  rfl

/-- Expanded W835 requirements, showing the current concrete route obligations. -/
def exactInputsIsoClosureLeftCalculusExpandedRequiredFieldNamesW835 :
    List String :=
  Dbounded.exactInputsIsoClosureLeftCalculusInputNamesW835 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

/-- The W835 expanded stable route has seven concrete requirements. -/
theorem exactInputsIsoClosureLeftCalculusExpandedRequiredFieldNamesW835_count :
    Dbounded.exactInputsIsoClosureLeftCalculusExpandedRequiredFieldNamesW835.length =
      7 :=
  rfl

/-- Current checked W835 state for the exact-input left-calculus route. -/
structure MetrizableExactInputsIsoClosureLeftCalculusRouteStateW835 :
    Type where
  seed : String
  declarations : List String
  leftCalculusResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W835 state. -/
def currentMetrizableExactInputsIsoClosureLeftCalculusRouteStateW835 :
    Dbounded.MetrizableExactInputsIsoClosureLeftCalculusRouteStateW835 where
  seed := "w835-exact-inputs-iso-closure-left-calculus-route"
  declarations :=
    ["MetrizableClosedMapExactInputsIsoClosureLeftCalculusDataW835",
      "MetrizableClosedEmbeddingExactInputsIsoClosureLeftCalculusDataW835",
      "isoClosureLeftCalculusDataOfClosedMapExactInputsW835",
      "isoClosureLeftCalculusDataOfClosedEmbeddingExactInputsW835",
      "targetExactAtPayloadOfClosedMapExactInputsIsoClosureW835",
      "targetExactAtPayloadOfClosedEmbeddingExactInputsIsoClosureW835",
      "directBoundedLeftCalculusOfClosedMapExactInputsIsoClosureW835",
      "directBoundedLeftCalculusOfClosedEmbeddingExactInputsIsoClosureW835",
      "boundedDerivedInfinityCategoryOfClosedMapExactInputsIsoClosureW835",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsIsoClosureW835",
      "exactInputsIsoClosureLeftCalculusInputNamesW835",
      "exactInputsIsoClosureLeftCalculusInputNamesW835_count",
      "exactInputsIsoClosureLeftCalculusStableRouteRequiredFieldNamesW835",
      "exactInputsIsoClosureLeftCalculusStableRouteRequiredFieldNamesW835_count",
      "exactInputsIsoClosureLeftCalculusExpandedRequiredFieldNamesW835",
      "exactInputsIsoClosureLeftCalculusExpandedRequiredFieldNamesW835_count"]
  leftCalculusResult :=
    "proved: W735/W651/W721 data supply W834 iso-closure left-calculus data"
  replacedInputs :=
    ["W696 closed-range endpoint topology"]
  remainingInputs :=
    Dbounded.exactInputsIsoClosureLeftCalculusExpandedRequiredFieldNamesW835
  productSuccessClaimed := false

theorem currentMetrizableExactInputsIsoClosureLeftCalculusRouteStateW835_productSuccess :
    (let state :=
        Dbounded.currentMetrizableExactInputsIsoClosureLeftCalculusRouteStateW835;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
