import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import LeanLCAExactChallenge.Derived.Bounded

/-!
Worker W230: opposite left-calculus transfer.

Mathlib's calculus-of-fractions API swaps handedness under `MorphismProperty.op`:
left calculus on `W` produces right calculus on `W.op`, and right calculus on `W`
produces left calculus on `W.op`. Thus the opposite finite-limit route needs a
right-calculus input for `boundedExactWeakEquivalence C`, not merely the existing
left-calculus input.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OppositeLeftCalculusTransferW230

variable {C : Type u} [Category.{v} C]

/-- Local name for the opposite bounded exact weak-equivalence property. -/
abbrev oppositeWeakEquivalence
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    MorphismProperty (BoundedComplexCategory C)ᵒᵖ :=
  (boundedExactWeakEquivalence C).op

/--
The generic handedness swap used by mathlib: left calculus on `W` becomes right
calculus on `W.op`.
-/
theorem op_hasRightCalculusOfFractions_of_hasLeft
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] :
    W.op.HasRightCalculusOfFractions := by
  infer_instance

/--
The transfer needed by the opposite localization finite-limit route: left calculus on
`W.op` is supplied by right calculus on `W`.
-/
theorem op_hasLeftCalculusOfFractions_of_hasRight
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] :
    W.op.HasLeftCalculusOfFractions := by
  infer_instance

/-- Specialization of the right-to-left opposite transfer to bounded exact weak equivalences. -/
theorem oppositeWeakEquivalence_hasLeftCalculusOfFractions_of_hasRight
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasRightCalculusOfFractions] :
    (oppositeWeakEquivalence C).HasLeftCalculusOfFractions := by
  infer_instance

/--
The exact pullback-transfer field that would provide the right calculus on bounded
homotopy/Verdier weak equivalences.
-/
structure PullbackRightCalculusTransfer
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop where
  transfer :
    (exactAcyclicHomotopyIsoClosure C).trW.HasRightCalculusOfFractions →
      (((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
        (BoundedComplexCategory.homotopyQuotient C)).HasRightCalculusOfFractions

/-- Existing Verdier/TRW input: triangulating the isomorphism closure gives right calculus. -/
theorem ambientVerdierRightCalculus_of_isoClosureClosed2
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.HasRightCalculusOfFractions :=
  exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2 C

/-- Right-calculus analogue of W217's bounded homotopy pullback-transfer package. -/
theorem boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_closed2_and_transfer
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂]
    (T : PullbackRightCalculusTransfer C) :
    (boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions :=
  T.transfer (ambientVerdierRightCalculus_of_isoClosureClosed2 C)

/--
Conditional opposite left calculus for the bounded exact localizer. The non-opposite field
needed upstream is right calculus for `boundedHomotopyExactWeakEquivalence C`.
-/
theorem boundedExactWeakEquivalence_op_hasLeftCalculusOfFractions_of_isoClosed
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions] :
    ((boundedExactWeakEquivalence C).op).HasLeftCalculusOfFractions := by
  haveI : (boundedExactWeakEquivalence C).HasRightCalculusOfFractions :=
    boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_isoClosed C
  infer_instance

/--
End-to-end conditional package for the finite-limit side: isomorphism invariance plus
right pullback transfer supply left calculus for the opposite bounded exact weak-equivalence
localizer.
-/
theorem oppositeWeakEquivalence_hasLeftCalculusOfFractions_of_closed2_and_rightTransfer
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂]
    (T : PullbackRightCalculusTransfer C) :
    (oppositeWeakEquivalence C).HasLeftCalculusOfFractions := by
  haveI : (boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions :=
    boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_closed2_and_transfer C T
  exact boundedExactWeakEquivalence_op_hasLeftCalculusOfFractions_of_isoClosed C

/-- Search result: the opposite route consumes right calculus on the original localizer. -/
def oppositeLeftCalculusFindings : List String :=
  ["mathlib instance: W.HasRightCalculusOfFractions -> W.op.HasLeftCalculusOfFractions",
    "mathlib instance: W.HasLeftCalculusOfFractions -> W.op.HasRightCalculusOfFractions",
    "for (boundedExactWeakEquivalence C).op left calculus, the missing non-opposite input is right calculus on boundedExactWeakEquivalence C",
    "a PullbackRightCalculusTransfer C, parallel to W217's left-transfer field, is sufficient after iso-closure triangulation"]

theorem oppositeLeftCalculusFindings_count :
    oppositeLeftCalculusFindings.length = 4 := rfl

/-- Reproducible audit state for this worker. -/
structure OppositeLeftCalculusTransferState : Type where
  selectedRoute : Nat
  seedHash : String
  mathlibSwap : String
  specializedLocalizer : String
  requiredNonOppositeInput : String
  productSuccessClaimed : Bool

/-- Current state encoded as Lean data. -/
def currentOppositeLeftCalculusTransferState : OppositeLeftCalculusTransferState where
  selectedRoute := 1
  seedHash := "2e671ca7d3b511b56a5fee140d0e00f210bfe166e7a0090fbf9b4b76b2a1a953"
  mathlibSwap := "HasRightCalculusOfFractions W gives HasLeftCalculusOfFractions W.op"
  specializedLocalizer := "(boundedExactWeakEquivalence C).op"
  requiredNonOppositeInput := "(boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions, or PullbackRightCalculusTransfer C"
  productSuccessClaimed := false

theorem currentOppositeLeftCalculusTransferState_route :
    currentOppositeLeftCalculusTransferState.selectedRoute = 1 := rfl

theorem currentOppositeLeftCalculusTransferState_productSuccess :
    currentOppositeLeftCalculusTransferState.productSuccessClaimed = false := rfl

section Checks

#check op_hasRightCalculusOfFractions_of_hasLeft
#check op_hasLeftCalculusOfFractions_of_hasRight
#check oppositeWeakEquivalence
#check oppositeWeakEquivalence_hasLeftCalculusOfFractions_of_hasRight
#check PullbackRightCalculusTransfer
#check ambientVerdierRightCalculus_of_isoClosureClosed2
#check boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_closed2_and_transfer
#check boundedExactWeakEquivalence_op_hasLeftCalculusOfFractions_of_isoClosed
#check oppositeWeakEquivalence_hasLeftCalculusOfFractions_of_closed2_and_rightTransfer
#check oppositeLeftCalculusFindings
#check currentOppositeLeftCalculusTransferState

end Checks

end OppositeLeftCalculusTransferW230

end LeanLCAExactChallenge
