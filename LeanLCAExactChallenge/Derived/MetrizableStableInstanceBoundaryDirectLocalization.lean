import LeanLCAExactChallenge.Derived.MetrizableStableInstanceBoundary
import LeanLCAExactChallenge.Derived.DirectWppLimitFiniteShapeTransfer
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

/-- Direct-localization inputs as the explicit canonical stable-instance boundary inputs. -/
noncomputable def metrizableStableInstanceBoundaryInputs_of_directLocalization
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    Dbounded.MetrizableStableInstanceBoundaryInputs where
  directLeftCalculus := inputs.directLeftCalculus
  transferStableInputs := by
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      inputs.directLeftCalculus
    exact Dbounded.metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
      inputs

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

/--
Accepted stable `Dbounded` package from the direct-localization refinement of the canonical
stable-instance boundary.
-/
noncomputable def
    acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  Dbounded.MetrizableStableInstanceBoundaryInputs.acceptedStable
    (Dbounded.metrizableStableInstanceBoundaryInputs_of_directLocalization inputs)

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

/--
Direct WPP limit and WPP-op colimit closure data refine the finite-shape transfer input in the
direct-localization stable-instance boundary.
-/
structure MetrizableStableInstanceBoundaryDirectLimitOpClosureInputs : Type 1 where
  transferInputs :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitAndOpClosure
  directLeftCalculus :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/-- Build the direct-localization boundary inputs from direct WPP limit/op-closure data. -/
noncomputable def
    metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directLimitOpClosure
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLimitOpClosureInputs) :
    Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs where
  transferInputs :=
    Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_limitAndOpClosure
      inputs.transferInputs
  directLeftCalculus := inputs.directLeftCalculus
  directLocalization := inputs.directLocalization

/--
Bounded-derived infinity-category package from the direct limit/op-closure refinement of the
stable-instance boundary.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLimitOpClosure
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLimitOpClosureInputs) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directLimitOpClosure
      inputs)

/-- The direct limit/op-closure refinement produces the ready four-projection stable certificate. -/
theorem stableCertificateOfMetrizableStableInstanceBoundaryDirectLimitOpClosure_ready
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLimitOpClosureInputs) :
    let localizedInputs :=
      Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directLimitOpClosure
        inputs
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      localizedInputs.directLeftCalculus
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (Dbounded.metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (Dbounded.metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          localizedInputs))).ready := by
  exact
    Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryDirectLocalization_ready
      (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directLimitOpClosure
        inputs)

/-- Source-facing input names for the direct limit/op-closure stable-instance boundary. -/
def metrizableStableInstanceBoundaryDirectLimitOpClosureInputNames : List String :=
  ["direct bounded left calculus of fractions",
    "direct WPP limit comparison",
    "direct WPP exact-acyclic limit closure",
    "WPP-op exact-acyclic colimit closure",
    "WalkingParallelPair functor-category localization",
    "direct-localization triangulated source core"]

/-- The direct limit/op-closure stable-instance boundary has six source-facing input families. -/
theorem metrizableStableInstanceBoundaryDirectLimitOpClosureInputNames_count :
    Dbounded.metrizableStableInstanceBoundaryDirectLimitOpClosureInputNames.length = 6 :=
  rfl

/--
Direct WPP limit field data and WPP-op colimit closure data refine the finite-shape transfer
input in the direct-localization stable-instance boundary.
-/
structure MetrizableStableInstanceBoundaryDirectLimitFieldsOpClosureInputs : Type 1 where
  transferInputs :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromLimitFieldsAndOpClosure
  directLeftCalculus :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/--
Build the direct-localization boundary inputs from direct WPP limit field/op-closure data.
-/
noncomputable def
    metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directLimitFieldsOpClosure
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLimitFieldsOpClosureInputs) :
    Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs where
  transferInputs :=
    Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_limitFieldsAndOpClosure
      inputs.transferInputs
  directLeftCalculus := inputs.directLeftCalculus
  directLocalization := inputs.directLocalization

/--
Bounded-derived infinity-category package from the direct limit-field/op-closure refinement of the
stable-instance boundary.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLimitFieldsOpClosure
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLimitFieldsOpClosureInputs) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directLimitFieldsOpClosure
      inputs)

/--
The direct limit-field/op-closure refinement produces the ready four-projection stable certificate.
-/
theorem stableCertificateOfMetrizableStableInstanceBoundaryDirectLimitFieldsOpClosure_ready
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLimitFieldsOpClosureInputs) :
    let localizedInputs :=
      Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directLimitFieldsOpClosure
        inputs
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      localizedInputs.directLeftCalculus
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (Dbounded.metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (Dbounded.metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          localizedInputs))).ready := by
  exact
    Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryDirectLocalization_ready
      (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directLimitFieldsOpClosure
        inputs)

/-- Source-facing input names for the direct limit-field/op-closure stable-instance boundary. -/
def metrizableStableInstanceBoundaryDirectLimitFieldsOpClosureInputNames : List String :=
  ["direct bounded left calculus of fractions",
    "mapping-cone WPP limit comparison",
    "WPP limit left closed-embedding field",
    "WPP limit right open-map field",
    "WPP limit right-surjectivity field",
    "WPP limit algebraic exactness field",
    "WPP-op exact-acyclic colimit closure",
    "WalkingParallelPair functor-category localization",
    "direct-localization triangulated source core"]

/--
The direct limit-field/op-closure stable-instance boundary has nine source-facing input families.
-/
theorem metrizableStableInstanceBoundaryDirectLimitFieldsOpClosureInputNames_count :
    Dbounded.metrizableStableInstanceBoundaryDirectLimitFieldsOpClosureInputNames.length = 9 :=
  rfl

/--
Direct right-LCA WPP limit data and WPP-op colimit closure data refine the finite-shape
transfer input in the direct-localization stable-instance boundary. The W551 comparison
and W555 left/algebraic fields are supplied by the direct route.
-/
structure MetrizableStableInstanceBoundaryDirectRightLcaOpClosureInputs : Type 1 where
  transferInputs :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromDirectRightLcaOpClosure
  directLeftCalculus :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/--
Build the direct-localization boundary inputs from direct right-LCA WPP limit/op-closure data.
-/
noncomputable def
    metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directRightLcaOpClosure
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectRightLcaOpClosureInputs) :
    Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs where
  transferInputs :=
    Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_directRightLcaOpClosure
      inputs.transferInputs
  directLeftCalculus := inputs.directLeftCalculus
  directLocalization := inputs.directLocalization

/--
Bounded-derived infinity-category package from the direct right-LCA/op-closure refinement of
the stable-instance boundary.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectRightLcaOpClosure
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectRightLcaOpClosureInputs) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directRightLcaOpClosure
      inputs)

/--
The direct right-LCA/op-closure refinement produces the ready four-projection stable certificate.
-/
theorem stableCertificateOfMetrizableStableInstanceBoundaryDirectRightLcaOpClosure_ready
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectRightLcaOpClosureInputs) :
    let localizedInputs :=
      Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directRightLcaOpClosure
        inputs
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      localizedInputs.directLeftCalculus
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (Dbounded.metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (Dbounded.metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          localizedInputs))).ready := by
  exact
    Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryDirectLocalization_ready
      (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directRightLcaOpClosure
        inputs)

/-- Source-facing input names for the direct right-LCA/op-closure stable-instance boundary. -/
def metrizableStableInstanceBoundaryDirectRightLcaOpClosureInputNames : List String :=
  ["direct bounded left calculus of fractions",
    "WPP limit right open-map pure LCA certificate",
    "WPP limit right-surjectivity pure LCA certificate",
    "WPP-op exact-acyclic colimit closure",
    "WalkingParallelPair functor-category localization",
    "direct-localization triangulated source core"]

/--
The direct right-LCA/op-closure stable-instance boundary has six source-facing input families.
-/
theorem metrizableStableInstanceBoundaryDirectRightLcaOpClosureInputNames_count :
    Dbounded.metrizableStableInstanceBoundaryDirectRightLcaOpClosureInputNames.length = 6 :=
  rfl

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
      "metrizableStableInstanceBoundaryInputs_of_directLocalization",
      "boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization",
      "acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization",
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
#check Dbounded.metrizableStableInstanceBoundaryInputs_of_directLocalization
#check Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
#check
  Dbounded.acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
#check Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryDirectLocalization_ready
#check Dbounded.MetrizableStableInstanceBoundaryDirectLimitOpClosureInputs
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directLimitOpClosure
#check Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLimitOpClosure
#check Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryDirectLimitOpClosure_ready
#check Dbounded.metrizableStableInstanceBoundaryDirectLimitOpClosureInputNames
#check Dbounded.metrizableStableInstanceBoundaryDirectLimitOpClosureInputNames_count
#check Dbounded.MetrizableStableInstanceBoundaryDirectLimitFieldsOpClosureInputs
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directLimitFieldsOpClosure
#check
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLimitFieldsOpClosure
#check Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryDirectLimitFieldsOpClosure_ready
#check Dbounded.metrizableStableInstanceBoundaryDirectLimitFieldsOpClosureInputNames
#check Dbounded.metrizableStableInstanceBoundaryDirectLimitFieldsOpClosureInputNames_count
#check Dbounded.MetrizableStableInstanceBoundaryDirectRightLcaOpClosureInputs
#check
  Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_directRightLcaOpClosure
#check
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectRightLcaOpClosure
#check Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryDirectRightLcaOpClosure_ready
#check Dbounded.metrizableStableInstanceBoundaryDirectRightLcaOpClosureInputNames
#check Dbounded.metrizableStableInstanceBoundaryDirectRightLcaOpClosureInputNames_count
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputNames
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputNames_count
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationDerivedFieldNames
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationDerivedFieldNames_count
#check Dbounded.currentMetrizableStableInstanceBoundaryDirectLocalizationRouteState_productSuccess

end Checks

end Dbounded

end LeanLCAExactChallenge
