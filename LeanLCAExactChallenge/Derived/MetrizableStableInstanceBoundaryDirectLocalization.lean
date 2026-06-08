import LeanLCAExactChallenge.Derived.MetrizableStableInstanceBoundary
import LeanLCAExactChallenge.Derived.DirectWppLimitFiniteShapeTransfer
import LeanLCAExactChallenge.Derived.TargetHomologyZeroDirectLocalizationStableRoute
import LeanLCAExactChallenge.Derived.TargetExactAtLeftCalculusRoute
import LeanLCAExactChallenge.Derived.TargetIsoLeftCalculusRoute
import LeanLCAExactChallenge.Derived.IsoClosureLeftCalculusRoute

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
Target-ExactAt direct-localization inputs for the canonical stable-instance boundary.
W832 supplies direct bounded left calculus from W696/W785/W721, leaving WPP transfer
and the W657 direct-localization triangulated source core as the other boundary inputs.
-/
structure MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputs : Type 2 where
  targetExactAtLeftCalculusData :
    Dbounded.MetrizableTargetExactAtLeftCalculusDataW832
  transferInputs :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/--
Build the direct-localization boundary inputs by deriving direct left calculus from the
W832 target-ExactAt route.
-/
noncomputable def
    metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetExactAt
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputs) :
    Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs where
  transferInputs := inputs.transferInputs
  directLeftCalculus :=
    Dbounded.directBoundedLeftCalculusOfTargetExactAtW832
      inputs.targetExactAtLeftCalculusData
  directLocalization := inputs.directLocalization

/--
Bounded-derived infinity-category package from the target-ExactAt direct-localization
refinement of the stable-instance boundary.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetExactAtDirectLocalization
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputs) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetExactAt
      inputs)

/--
Accepted stable `Dbounded` package from the target-ExactAt direct-localization refinement of the
canonical stable-instance boundary.
-/
noncomputable def
    acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetExactAtDirectLocalization
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputs) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  Dbounded.acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetExactAt
      inputs)

/--
The target-ExactAt direct-localization refinement produces the ready four-projection stable
certificate.
-/
theorem
    stableCertificateOfMetrizableStableInstanceBoundaryTargetExactAtDirectLocalization_ready
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputs) :
    let localizedInputs :=
      Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetExactAt
        inputs
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      localizedInputs.directLeftCalculus
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (Dbounded.metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (Dbounded.metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          localizedInputs))).ready := by
  exact
    Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryDirectLocalization_ready
      (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetExactAt
        inputs)

/--
Source-facing input names for the target-ExactAt direct-localization stable-instance boundary.
-/
def metrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputNames :
    List String :=
  Dbounded.targetExactAtLeftCalculusInputNamesW832 ++
    ["MetrizableWalkingParallelPairFiniteShapeTransferInputs",
      "MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657"]

/--
The target-ExactAt direct-localization boundary has five source-facing input families.
-/
theorem metrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputNames_count :
    Dbounded.metrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputNames.length =
      5 :=
  rfl

/-- Current checked target-ExactAt direct-localization boundary state. -/
structure MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationRouteState :
    Type where
  seed : String
  declarations : List String
  boundaryResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked target-ExactAt direct-localization boundary state. -/
def currentMetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationRouteState :
    Dbounded.MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationRouteState where
  seed := "metrizable-stable-instance-boundary-target-exact-at-direct-localization"
  declarations :=
    ["MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputs",
      "metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetExactAt",
      "boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetExactAtDirectLocalization",
      "acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetExactAtDirectLocalization",
      "stableCertificateOfMetrizableStableInstanceBoundaryTargetExactAtDirectLocalization_ready",
      "metrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputNames",
      "metrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputNames_count"]
  boundaryResult :=
    "proved: W832 target-ExactAt data derive direct bounded left calculus for the " ++
      "direct-localization stable-instance boundary"
  replacedInputs := ["direct bounded left calculus of fractions"]
  remainingInputs :=
    Dbounded.metrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputNames
  productSuccessClaimed := false

theorem
    currentMetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationRouteState_productSuccess :
    (let state :=
        Dbounded.currentMetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationRouteState;
      state.productSuccessClaimed) =
      false :=
  rfl

/--
Target-isomorphism direct-localization inputs for the canonical stable-instance boundary.
W833 replaces W832's W785 target ExactAt payload with a W784 target-isomorphism realization.
-/
structure MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs : Type 2 where
  targetIsoLeftCalculusData :
    Dbounded.MetrizableTargetIsoLeftCalculusDataW833
  transferInputs :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/--
Build the target-ExactAt direct-localization inputs by deriving W832 data from W833 target-iso
data.
-/
noncomputable def
    metrizableStableInstanceBoundaryTargetExactAtInputs_of_targetIso
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs) :
    Dbounded.MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputs where
  targetExactAtLeftCalculusData :=
    Dbounded.targetExactAtLeftCalculusDataOfTargetIsoW833
      inputs.targetIsoLeftCalculusData
  transferInputs := inputs.transferInputs
  directLocalization := inputs.directLocalization

/--
Build the direct-localization boundary inputs by deriving direct left calculus from the W833
target-isomorphism route.
-/
noncomputable def
    metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetIso
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs) :
    Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetExactAt
    (Dbounded.metrizableStableInstanceBoundaryTargetExactAtInputs_of_targetIso
      inputs)

/--
Bounded-derived infinity-category package from the target-isomorphism direct-localization
refinement of the stable-instance boundary.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetIsoDirectLocalization
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetIso
      inputs)

/--
Accepted stable `Dbounded` package from the target-isomorphism direct-localization refinement of
the canonical stable-instance boundary.
-/
noncomputable def
    acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetIsoDirectLocalization
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  Dbounded.acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetIso
      inputs)

/--
The target-isomorphism direct-localization refinement produces the ready four-projection stable
certificate.
-/
theorem
    stableCertificateOfMetrizableStableInstanceBoundaryTargetIsoDirectLocalization_ready
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs) :
    let localizedInputs :=
      Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetIso
        inputs
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      localizedInputs.directLeftCalculus
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (Dbounded.metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (Dbounded.metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          localizedInputs))).ready := by
  exact
    Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryDirectLocalization_ready
      (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetIso
        inputs)

/--
Source-facing input names for the target-isomorphism direct-localization stable-instance boundary.
-/
def metrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputNames :
    List String :=
  Dbounded.targetIsoLeftCalculusInputNamesW833 ++
    ["MetrizableWalkingParallelPairFiniteShapeTransferInputs",
      "MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657"]

/--
The target-isomorphism direct-localization boundary has five source-facing input families.
-/
theorem metrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputNames_count :
    Dbounded.metrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputNames.length =
      5 :=
  rfl

/-- Current checked target-isomorphism direct-localization boundary state. -/
structure MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationRouteState :
    Type where
  seed : String
  declarations : List String
  boundaryResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked target-isomorphism direct-localization boundary state. -/
def currentMetrizableStableInstanceBoundaryTargetIsoDirectLocalizationRouteState :
    Dbounded.MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationRouteState where
  seed := "metrizable-stable-instance-boundary-target-iso-direct-localization"
  declarations :=
    ["MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs",
      "metrizableStableInstanceBoundaryTargetExactAtInputs_of_targetIso",
      "metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetIso",
      "boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetIsoDirectLocalization",
      "acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetIsoDirectLocalization",
      "stableCertificateOfMetrizableStableInstanceBoundaryTargetIsoDirectLocalization_ready",
      "metrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputNames",
      "metrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputNames_count"]
  boundaryResult :=
    "proved: W833 target-isomorphism data derive the W832 target-ExactAt direct-" ++
      "localization boundary"
  replacedInputs := ["W785 target ExactAt payload for exact-acyclic homotopy objects"]
  remainingInputs :=
    Dbounded.metrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputNames
  productSuccessClaimed := false

theorem
    currentMetrizableStableInstanceBoundaryTargetIsoDirectLocalizationRouteState_productSuccess :
    (let state :=
        Dbounded.currentMetrizableStableInstanceBoundaryTargetIsoDirectLocalizationRouteState;
      state.productSuccessClaimed) =
      false :=
  rfl

/--
Iso-closure direct-localization inputs for the canonical stable-instance boundary.
W834 replaces W833's W784 target-isomorphism realization with W651 iso-closure realization.
-/
structure MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputs : Type 2 where
  isoClosureLeftCalculusData :
    Dbounded.MetrizableIsoClosureRealizationLeftCalculusDataW834
  transferInputs :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/--
Build the target-isomorphism direct-localization inputs by deriving W833 data from W834
iso-closure data.
-/
noncomputable def
    metrizableStableInstanceBoundaryTargetIsoInputs_of_isoClosure
    (inputs : Dbounded.MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputs) :
    Dbounded.MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs where
  targetIsoLeftCalculusData :=
    Dbounded.targetIsoLeftCalculusDataOfIsoClosureRealizationW834
      inputs.isoClosureLeftCalculusData
  transferInputs := inputs.transferInputs
  directLocalization := inputs.directLocalization

/--
Build the direct-localization boundary inputs by deriving direct left calculus from the W834
iso-closure route.
-/
noncomputable def
    metrizableStableInstanceBoundaryDirectLocalizationInputs_of_isoClosure
    (inputs : Dbounded.MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputs) :
    Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetIso
    (Dbounded.metrizableStableInstanceBoundaryTargetIsoInputs_of_isoClosure
      inputs)

/--
Bounded-derived infinity-category package from the iso-closure direct-localization refinement of
the stable-instance boundary.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryIsoClosureDirectLocalization
    (inputs : Dbounded.MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputs) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_isoClosure
      inputs)

/--
Accepted stable `Dbounded` package from the iso-closure direct-localization refinement of the
canonical stable-instance boundary.
-/
noncomputable def
    acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryIsoClosureDirectLocalization
    (inputs : Dbounded.MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputs) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  Dbounded.acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_isoClosure
      inputs)

/--
The iso-closure direct-localization refinement produces the ready four-projection stable
certificate.
-/
theorem
    stableCertificateOfMetrizableStableInstanceBoundaryIsoClosureDirectLocalization_ready
    (inputs : Dbounded.MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputs) :
    let localizedInputs :=
      Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_isoClosure
        inputs
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      localizedInputs.directLeftCalculus
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (Dbounded.metrizableOrdinaryStableSemanticInputOfWalkingParallelPairTransfer
        (Dbounded.metrizableWalkingParallelPairTransferStableSemanticInputsOfDirectLocalization
          localizedInputs))).ready := by
  exact
    Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryDirectLocalization_ready
      (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_isoClosure
        inputs)

/-- Source-facing input names for the iso-closure direct-localization stable-instance boundary. -/
def metrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputNames :
    List String :=
  Dbounded.isoClosureLeftCalculusInputNamesW834 ++
    ["MetrizableWalkingParallelPairFiniteShapeTransferInputs",
      "MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657"]

/-- The iso-closure direct-localization boundary has five source-facing input families. -/
theorem metrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputNames_count :
    Dbounded.metrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputNames.length =
      5 :=
  rfl

/-- Current checked iso-closure direct-localization boundary state. -/
structure MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationRouteState :
    Type where
  seed : String
  declarations : List String
  boundaryResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked iso-closure direct-localization boundary state. -/
def currentMetrizableStableInstanceBoundaryIsoClosureDirectLocalizationRouteState :
    Dbounded.MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationRouteState where
  seed := "metrizable-stable-instance-boundary-iso-closure-direct-localization"
  declarations :=
    ["MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputs",
      "metrizableStableInstanceBoundaryTargetIsoInputs_of_isoClosure",
      "metrizableStableInstanceBoundaryDirectLocalizationInputs_of_isoClosure",
      "boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryIsoClosureDirectLocalization",
      "acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryIsoClosureDirectLocalization",
      "stableCertificateOfMetrizableStableInstanceBoundaryIsoClosureDirectLocalization_ready",
      "metrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputNames",
      "metrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputNames_count"]
  boundaryResult :=
    "proved: W834 iso-closure data derive the W833 target-isomorphism direct-" ++
      "localization boundary"
  replacedInputs := ["W784 exact-acyclic homotopy-object target-isomorphism realization"]
  remainingInputs :=
    Dbounded.metrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputNames
  productSuccessClaimed := false

theorem
    currentMetrizableStableInstanceBoundaryIsoClosureDirectLocalizationRouteState_productSuccess :
    (let state :=
        Dbounded.currentMetrizableStableInstanceBoundaryIsoClosureDirectLocalizationRouteState;
      state.productSuccessClaimed) =
      false :=
  rfl

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
#check Dbounded.MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputs
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetExactAt
#check
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetExactAtDirectLocalization
#check
  Dbounded.acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetExactAtDirectLocalization
#check
  Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryTargetExactAtDirectLocalization_ready
#check Dbounded.metrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputNames
#check Dbounded.metrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputNames_count
#check
  Dbounded.currentMetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationRouteState_productSuccess
#check Dbounded.MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs
#check Dbounded.metrizableStableInstanceBoundaryTargetExactAtInputs_of_targetIso
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetIso
#check
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetIsoDirectLocalization
#check
  Dbounded.acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetIsoDirectLocalization
#check
  Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryTargetIsoDirectLocalization_ready
#check Dbounded.metrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputNames
#check Dbounded.metrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputNames_count
#check
  Dbounded.currentMetrizableStableInstanceBoundaryTargetIsoDirectLocalizationRouteState_productSuccess
#check Dbounded.MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputs
#check Dbounded.metrizableStableInstanceBoundaryTargetIsoInputs_of_isoClosure
#check Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_isoClosure
#check
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryIsoClosureDirectLocalization
#check
  Dbounded.acceptedStableBoundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryIsoClosureDirectLocalization
#check
  Dbounded.stableCertificateOfMetrizableStableInstanceBoundaryIsoClosureDirectLocalization_ready
#check Dbounded.metrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputNames
#check Dbounded.metrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputNames_count
#check
  Dbounded.currentMetrizableStableInstanceBoundaryIsoClosureDirectLocalizationRouteState_productSuccess
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
