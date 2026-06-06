import LeanLCAExactChallenge.Derived.MetrizableStableInstanceBoundary
import LeanLCAExactChallenge.Derived.TargetHomologyZeroDirectLocalizationStableRoute

/-!
Direct-localization refinement of the `Dbounded MetrizableLCA` stable-instance boundary.

This module reduces the boundary's explicit triangulated fields to the existing W657
source-side direct-localization core, together with direct bounded left calculus and WPP
finite-shape transfer. It does not supply an inhabitant of those inputs and does not claim
product success.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- Direct-localization inputs for the canonical stable-instance boundary. -/
structure MetrizableStableInstanceBoundaryDirectLocalizationInputs : Type 1 where
  transferInputs :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs
  directLeftCalculus :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/-- W657 direct-localization source data derives the localized pretriangulated field. -/
@[reducible] noncomputable def
    pretriangulatedOfMetrizableStableInstanceBoundaryDirectLocalization
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
      Dbounded.metrizableLeftCalculusSemanticFields
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      available.shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    inputs.directLeftCalculus
  letI : HasShift (Dbounded MetrizableLCA.{0}) ℤ :=
    HasShift.localization (boundedExactWeakEquivalence MetrizableLCA.{0}) ℤ
  let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
    Dbounded.metrizableLeftCalculusSemanticFields
  letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
  letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
  letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
    available.shiftAdditiveAll
  letI : (Dbounded.localization MetrizableLCA.{0}).Additive :=
    Dbounded.localization_additiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsCompatibleWithShift ℤ :=
    boundedExactWeakEquivalence_isCompatibleWithShift MetrizableLCA.{0}
  letI : (Dbounded.localization MetrizableLCA.{0}).CommShift ℤ := inferInstance
  letI : ∀ n : ℤ,
      (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
    inferInstance
  letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
    inputs.directLocalization.sourcePretriangulated
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsCompatibleWithTriangulation :=
    metrizableBoundedExactWeakEquivalence_isCompatibleWithTriangulation_of_triangleCompletionW654
      inputs.directLocalization.triangleCompletion
  exact metrizablePretriangulatedOfDirectLocalizationCompatibilityW654

/-- W657 direct-localization source data derives the localized triangulated field. -/
@[reducible] noncomputable def
    triangulatedOfMetrizableStableInstanceBoundaryDirectLocalization
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
      Dbounded.metrizableLeftCalculusSemanticFields
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      available.shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) :=
      pretriangulatedOfMetrizableStableInstanceBoundaryDirectLocalization inputs
    IsTriangulated (Dbounded MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    inputs.directLeftCalculus
  letI : HasShift (Dbounded MetrizableLCA.{0}) ℤ :=
    HasShift.localization (boundedExactWeakEquivalence MetrizableLCA.{0}) ℤ
  let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
    Dbounded.metrizableLeftCalculusSemanticFields
  letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
  letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
  letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
    available.shiftAdditiveAll
  letI : (Dbounded.localization MetrizableLCA.{0}).Additive :=
    Dbounded.localization_additiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsCompatibleWithShift ℤ :=
    boundedExactWeakEquivalence_isCompatibleWithShift MetrizableLCA.{0}
  letI : (Dbounded.localization MetrizableLCA.{0}).CommShift ℤ := inferInstance
  letI : ∀ n : ℤ,
      (shiftFunctor (BoundedComplexCategory MetrizableLCA.{0}) n).Additive :=
    inferInstance
  letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
    inputs.directLocalization.sourcePretriangulated
  letI : IsTriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
    inputs.directLocalization.sourceTriangulated
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsCompatibleWithTriangulation :=
    metrizableBoundedExactWeakEquivalence_isCompatibleWithTriangulation_of_triangleCompletionW654
      inputs.directLocalization.triangleCompletion
  letI : Pretriangulated (Dbounded MetrizableLCA.{0}) :=
    pretriangulatedOfMetrizableStableInstanceBoundaryDirectLocalization inputs
  exact metrizableIsTriangulatedOfDirectLocalizationCompatibilityW654

/--
Direct-localization source data supplies the WPP transfer-stable semantic input expected by the
canonical stable-instance boundary.
-/
noncomputable def
    metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    Dbounded.MetrizableWalkingParallelPairTransferStableSemanticInputs
      Dbounded.metrizableLeftCalculusSemanticFields := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    inputs.directLeftCalculus
  exact
    { transferInputs := inputs.transferInputs
      pretriangulated :=
        Dbounded.pretriangulatedOfMetrizableStableInstanceBoundaryDirectLocalization
          inputs
      triangulated :=
        Dbounded.triangulatedOfMetrizableStableInstanceBoundaryDirectLocalization
          inputs }

/--
Bounded-derived infinity-category package from the direct-localization refinement of the
stable-instance boundary.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    inputs.directLeftCalculus
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundary
    (Dbounded.metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
      inputs)

/-- The direct-localization boundary produces the ready four-projection stable certificate. -/
theorem stableCertificateOfMetrizableStableInstanceBoundaryDirectLocalization_ready
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (Dbounded.metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (Dbounded.metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          inputs))).ready := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    inputs.directLeftCalculus
  exact Dbounded.stableCertificateOfMetrizableWalkingParallelPairTransfer_ready _

/-- Remaining source-facing inputs for the direct-localization stable-instance boundary. -/
def metrizableStableInstanceBoundaryDirectLocalizationInputNames : List String :=
  ["direct bounded left calculus of fractions",
    "MetrizableWalkingParallelPairFiniteShapeTransferInputs",
    "MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657"]

/-- The direct-localization boundary has three remaining input families. -/
theorem metrizableStableInstanceBoundaryDirectLocalizationInputNames_count :
    Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputNames.length = 3 :=
  rfl

/-- Fields or packages derived from the direct-localization boundary inputs. -/
def metrizableStableInstanceBoundaryDirectLocalizationDerivedFieldNames : List String :=
  ["Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)",
    "MetrizableWalkingParallelPairTransferStableSemanticInputs",
    "BoundedDerivedInfinityCategory MetrizableLCA"]

/-- The direct-localization boundary exposes four derived fields or packages. -/
theorem metrizableStableInstanceBoundaryDirectLocalizationDerivedFieldNames_count :
    Dbounded.metrizableStableInstanceBoundaryDirectLocalizationDerivedFieldNames.length =
      4 :=
  rfl

/-- Current checked direct-localization boundary state. -/
structure MetrizableStableInstanceBoundaryDirectLocalizationRouteState : Type where
  seed : String
  declarations : List String
  boundaryResult : String
  derivedFields : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked direct-localization boundary state. -/
def currentMetrizableStableInstanceBoundaryDirectLocalizationRouteState :
    Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationRouteState where
  seed := "metrizable-stable-instance-boundary-direct-localization"
  declarations :=
    ["MetrizableStableInstanceBoundaryDirectLocalizationInputs",
      "pretriangulatedOfMetrizableStableInstanceBoundaryDirectLocalization",
      "triangulatedOfMetrizableStableInstanceBoundaryDirectLocalization",
      "metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization",
      "boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization",
      "stableCertificateOfMetrizableStableInstanceBoundaryDirectLocalization_ready",
      "metrizableStableInstanceBoundaryDirectLocalizationInputNames",
      "metrizableStableInstanceBoundaryDirectLocalizationInputNames_count",
      "metrizableStableInstanceBoundaryDirectLocalizationDerivedFieldNames",
      "metrizableStableInstanceBoundaryDirectLocalizationDerivedFieldNames_count"]
  boundaryResult :=
    "proved: direct bounded left calculus plus WPP finite-shape transfer and W657 " ++
      "direct-localization source data assemble the canonical stable-instance boundary"
  derivedFields :=
    Dbounded.metrizableStableInstanceBoundaryDirectLocalizationDerivedFieldNames
  remainingInputs :=
    Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputNames
  productSuccessClaimed := false

theorem currentMetrizableStableInstanceBoundaryDirectLocalizationRouteState_productSuccess :
    (let state :=
        Dbounded.currentMetrizableStableInstanceBoundaryDirectLocalizationRouteState;
      state.productSuccessClaimed) =
      false :=
  rfl

section Checks

#check Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs
#check Dbounded.pretriangulatedOfMetrizableStableInstanceBoundaryDirectLocalization
#check Dbounded.triangulatedOfMetrizableStableInstanceBoundaryDirectLocalization
#check Dbounded.metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
#check Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
#check Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryDirectLocalization_ready
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputNames
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputNames_count
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationDerivedFieldNames
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationDerivedFieldNames_count
#check Dbounded.currentMetrizableStableInstanceBoundaryDirectLocalizationRouteState_productSuccess

end Checks

end Dbounded

end LeanLCAExactChallenge
