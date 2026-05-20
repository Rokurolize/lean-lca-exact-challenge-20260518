import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import LeanLCAExactChallenge.Derived.BoundedFiniteProducts

/-!
W258: isolate the opposite finite-product stability bridge.

`Localization.hasFiniteProducts` consumes finite-product stability of the morphism property on
the source category.  For the opposite bounded-complex localization this is the missing input
`((boundedExactWeakEquivalence MetrizableLCA).op).IsStableUnderFiniteProducts`.

The direct product-side theorem in `BoundedFiniteProducts` does not provide this automatically:
products in the opposite category correspond to coproducts in the original category.  This file
records the exact finite-coproduct route that would close the opposite finite-product input.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OppositeFiniteProductStabilityInputW258

abbrev metrizableLCAWeakEquivalence : MorphismProperty (BoundedComplexCategory MetrizableLCA.{u}) :=
  boundedExactWeakEquivalence MetrizableLCA.{u}

abbrev metrizableLCAOppositeWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
  (metrizableLCAWeakEquivalence.{u}).op

/--
The non-opposite finite-product theorem already available in the project.

This is intentionally recorded next to the opposite input because it is not enough by itself:
it proves stability for products in the original bounded-complex category, while the localization
consumer for the opposite category needs products in the opposite category.
-/
theorem directFiniteProductStability_available :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteProducts :=
  BoundedFiniteProducts.isStableUnderFiniteProducts_metrizableLCA

/--
Input package for closing finite-product stability on the opposite weak equivalences.

The intended mathematical route is:

* prove finite-coproduct stability of bounded exact weak equivalences in the original category;
* transport those finite coproducts across `Cᵒᵖ` as finite products;
* identify the resulting product map with the opposite of the coproduct map.

The third bullet is the formal bridge not currently provided by mathlib in this repository.
-/
structure OppositeFiniteProductStabilityBridgeInput : Prop where
  finiteCoproductStability :
    (metrizableLCAWeakEquivalence.{u}).IsStableUnderFiniteCoproducts
  oppositeFiniteProductStability :
    (metrizableLCAOppositeWeakEquivalence.{u}).IsStableUnderFiniteProducts

theorem oppositeFiniteProductStability_of_bridgeInput
    (h : OppositeFiniteProductStabilityBridgeInput.{u}) :
    (metrizableLCAOppositeWeakEquivalence.{u}).IsStableUnderFiniteProducts :=
  h.oppositeFiniteProductStability

/--
Finite products in the opposite localization once the bridge input and the existing localization
calculus hypotheses are supplied.
-/
noncomputable abbrev oppositeLocalizationHasFiniteProducts_of_bridgeInput
    [(metrizableLCAOppositeWeakEquivalence.{u}).HasLeftCalculusOfFractions]
    (h : OppositeFiniteProductStabilityBridgeInput.{u}) :
    HasFiniteProducts ((metrizableLCAOppositeWeakEquivalence.{u}).Localization) := by
  haveI : (metrizableLCAOppositeWeakEquivalence.{u}).IsStableUnderFiniteProducts :=
    oppositeFiniteProductStability_of_bridgeInput h
  infer_instance

def remainingOppositeFiniteProductBridgeInputs : List String :=
  [ "(boundedExactWeakEquivalence MetrizableLCA).IsStableUnderFiniteCoproducts",
    "formal transport: finite coproduct stability of W implies finite product stability of W.op" ]

structure OppositeFiniteProductBridgeState where
  directProductStabilityAvailable : Bool
  finiteCoproductStabilityConstructor : Option String
  opTransportConstructor : Option String
  localizationConsumer : String

def currentBridgeState : OppositeFiniteProductBridgeState where
  directProductStabilityAvailable := true
  finiteCoproductStabilityConstructor := none
  opTransportConstructor := none
  localizationConsumer := "CategoryTheory.Localization.hasFiniteProducts"

theorem currentBridgeState_directProductStabilityAvailable :
    currentBridgeState.directProductStabilityAvailable = true := rfl

theorem currentBridgeState_finiteCoproductStability_missing :
    currentBridgeState.finiteCoproductStabilityConstructor = none := rfl

theorem currentBridgeState_opTransport_missing :
    currentBridgeState.opTransportConstructor = none := rfl

section Checks

#check directFiniteProductStability_available
#check OppositeFiniteProductStabilityBridgeInput
#check oppositeFiniteProductStability_of_bridgeInput
#check oppositeLocalizationHasFiniteProducts_of_bridgeInput
#check remainingOppositeFiniteProductBridgeInputs
#check currentBridgeState
#check currentBridgeState_directProductStabilityAvailable
#check currentBridgeState_finiteCoproductStability_missing
#check currentBridgeState_opTransport_missing
#check CategoryTheory.Localization.hasFiniteProducts
#check CategoryTheory.Limits.opCoproductIsoProduct

end Checks

end OppositeFiniteProductStabilityInputW258

end LeanLCAExactChallenge
