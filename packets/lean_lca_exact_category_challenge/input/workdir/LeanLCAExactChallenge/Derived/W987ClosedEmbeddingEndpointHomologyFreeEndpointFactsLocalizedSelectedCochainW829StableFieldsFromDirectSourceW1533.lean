import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW829LeftCalculusStableRouteConvergenceGuardW1532

/-!
W1533 discharges the four W829 stable-route fields for the W1532 W987
surface. W1532 supplied the W829 left-calculus premise from W830 data but left
finite limits, finite colimits, pretriangulated structure, and triangulated
structure as explicit parameters. The same W987 input already reaches W843
through W1526; W843/W842 derive W653 finite-shape transfer data and W657
direct-localization triangulated source data. W1533 feeds those source-side
data into the W1532 W829 semantic record.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519
open scoped ZeroObject

namespace Dbounded

noncomputable section

/-- W1533 reuses the W1532 W829 left-calculus stable-route surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputW1532

/-- W1533 closed-map W653 direct finite-shape source data from the W1526 W843 branch. -/
noncomputable def closedMapDirectSourceW829OfW843ConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableWppDirectFiniteShapeTrianglehPayloadSourceW653 :=
  closedMapDirectSourceOfTargetHomologyZeroW842
    (closedMapTargetHomologyZeroDataOfTargetExactAtW843
      (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
        input globalClosedMapComponents mappedCokernelClosedMapProvider))

/-- W1533 closed-embedding W653 direct finite-shape source data from the W1526 W843 branch. -/
noncomputable def closedEmbeddingDirectSourceW829OfW843ConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableWppDirectFiniteShapeTrianglehPayloadSourceW653 :=
  closedEmbeddingDirectSourceOfTargetHomologyZeroW842
    (closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843
      (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider))

/-- W1533 closed-map W657 direct-localization source data from the W1526 W843 branch. -/
noncomputable def closedMapDirectLocalizationW829OfW843ConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657 :=
  closedMapDirectLocalizationOfTargetHomologyZeroW842
    (closedMapTargetHomologyZeroDataOfTargetExactAtW843
      (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
        input globalClosedMapComponents mappedCokernelClosedMapProvider))

/-- W1533 closed-embedding W657 direct-localization source data from the W1526 W843 branch. -/
noncomputable def closedEmbeddingDirectLocalizationW829OfW843ConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657 :=
  closedEmbeddingDirectLocalizationOfTargetHomologyZeroW842
    (closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843
      (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider))

/-- W1533 closed-map W829 pretriangulated structure from W657 source data. -/
@[reducible] noncomputable def closedMapPretriangulatedW829OfW843ConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
      closedMapLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
        input globalClosedMapComponents mappedCokernelClosedMapProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      available.shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    closedMapLeftCalculusPremiseW829OfW830ConvergenceW1532
      input globalClosedMapComponents mappedCokernelClosedMapProvider
  letI : HasShift (Dbounded MetrizableLCA.{0}) ℤ :=
    HasShift.localization (boundedExactWeakEquivalence MetrizableLCA.{0}) ℤ
  let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
    closedMapLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
      input globalClosedMapComponents mappedCokernelClosedMapProvider
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
  let directLocalization :=
    closedMapDirectLocalizationW829OfW843ConvergenceW1533
      input globalClosedMapComponents mappedCokernelClosedMapProvider
  letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
    directLocalization.sourcePretriangulated
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsCompatibleWithTriangulation :=
    metrizableBoundedExactWeakEquivalence_isCompatibleWithTriangulation_of_triangleCompletionW654
      directLocalization.triangleCompletion
  exact metrizablePretriangulatedOfDirectLocalizationCompatibilityW654

/-- W1533 closed-embedding W829 pretriangulated structure from W657 source data. -/
@[reducible] noncomputable def
    closedEmbeddingPretriangulatedW829OfW843ConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
      closedEmbeddingLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      available.shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    closedEmbeddingLeftCalculusPremiseW829OfW830ConvergenceW1532
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider
  letI : HasShift (Dbounded MetrizableLCA.{0}) ℤ :=
    HasShift.localization (boundedExactWeakEquivalence MetrizableLCA.{0}) ℤ
  let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
    closedEmbeddingLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider
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
  let directLocalization :=
    closedEmbeddingDirectLocalizationW829OfW843ConvergenceW1533
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider
  letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
    directLocalization.sourcePretriangulated
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsCompatibleWithTriangulation :=
    metrizableBoundedExactWeakEquivalence_isCompatibleWithTriangulation_of_triangleCompletionW654
      directLocalization.triangleCompletion
  exact metrizablePretriangulatedOfDirectLocalizationCompatibilityW654

/-- W1533 closed-map W829 triangulated structure from W657 source data. -/
@[reducible] noncomputable def closedMapTriangulatedW829OfW843ConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
      closedMapLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
        input globalClosedMapComponents mappedCokernelClosedMapProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      available.shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) :=
      closedMapPretriangulatedW829OfW843ConvergenceW1533
        input globalClosedMapComponents mappedCokernelClosedMapProvider
    IsTriangulated (Dbounded MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    closedMapLeftCalculusPremiseW829OfW830ConvergenceW1532
      input globalClosedMapComponents mappedCokernelClosedMapProvider
  letI : HasShift (Dbounded MetrizableLCA.{0}) ℤ :=
    HasShift.localization (boundedExactWeakEquivalence MetrizableLCA.{0}) ℤ
  let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
    closedMapLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
      input globalClosedMapComponents mappedCokernelClosedMapProvider
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
  let directLocalization :=
    closedMapDirectLocalizationW829OfW843ConvergenceW1533
      input globalClosedMapComponents mappedCokernelClosedMapProvider
  letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
    directLocalization.sourcePretriangulated
  letI : IsTriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
    directLocalization.sourceTriangulated
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsCompatibleWithTriangulation :=
    metrizableBoundedExactWeakEquivalence_isCompatibleWithTriangulation_of_triangleCompletionW654
      directLocalization.triangleCompletion
  letI : Pretriangulated (Dbounded MetrizableLCA.{0}) :=
    closedMapPretriangulatedW829OfW843ConvergenceW1533
      input globalClosedMapComponents mappedCokernelClosedMapProvider
  exact metrizableIsTriangulatedOfDirectLocalizationCompatibilityW654

/-- W1533 closed-embedding W829 triangulated structure from W657 source data. -/
@[reducible] noncomputable def
    closedEmbeddingTriangulatedW829OfW843ConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
      closedEmbeddingLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      available.shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) :=
      closedEmbeddingPretriangulatedW829OfW843ConvergenceW1533
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider
    IsTriangulated (Dbounded MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    closedEmbeddingLeftCalculusPremiseW829OfW830ConvergenceW1532
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider
  letI : HasShift (Dbounded MetrizableLCA.{0}) ℤ :=
    HasShift.localization (boundedExactWeakEquivalence MetrizableLCA.{0}) ℤ
  let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
    closedEmbeddingLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider
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
  let directLocalization :=
    closedEmbeddingDirectLocalizationW829OfW843ConvergenceW1533
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider
  letI : Pretriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
    directLocalization.sourcePretriangulated
  letI : IsTriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
    directLocalization.sourceTriangulated
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsCompatibleWithTriangulation :=
    metrizableBoundedExactWeakEquivalence_isCompatibleWithTriangulation_of_triangleCompletionW654
      directLocalization.triangleCompletion
  letI : Pretriangulated (Dbounded MetrizableLCA.{0}) :=
    closedEmbeddingPretriangulatedW829OfW843ConvergenceW1533
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider
  exact metrizableIsTriangulatedOfDirectLocalizationCompatibilityW654

/-- W1533 closed-map WPP transfer plus W657 triangulated fields for the W829 record. -/
noncomputable def closedMapTransferStableInputsW829OfW843ConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Dbounded.MetrizableWalkingParallelPairTransferStableSemanticInputs
      (closedMapLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
        input globalClosedMapComponents mappedCokernelClosedMapProvider)
    where
  transferInputs :=
    (closedMapDirectSourceW829OfW843ConvergenceW1533
      input globalClosedMapComponents mappedCokernelClosedMapProvider).finiteShapeInputs
  pretriangulated :=
    closedMapPretriangulatedW829OfW843ConvergenceW1533
      input globalClosedMapComponents mappedCokernelClosedMapProvider
  triangulated :=
    closedMapTriangulatedW829OfW843ConvergenceW1533
      input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1533 closed-embedding WPP transfer plus W657 triangulated fields for the W829 record. -/
noncomputable def closedEmbeddingTransferStableInputsW829OfW843ConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Dbounded.MetrizableWalkingParallelPairTransferStableSemanticInputs
      (closedEmbeddingLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider)
    where
  transferInputs :=
    (closedEmbeddingDirectSourceW829OfW843ConvergenceW1533
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider).finiteShapeInputs
  pretriangulated :=
    closedEmbeddingPretriangulatedW829OfW843ConvergenceW1533
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider
  triangulated :=
    closedEmbeddingTriangulatedW829OfW843ConvergenceW1533
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider

/-- W1533 closed-map remaining W829 stable fields from W843/W842 source data. -/
noncomputable def closedMapRemainingStableFieldsW829OfW843ConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (closedMapLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
        input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    closedMapLeftCalculusPremiseW829OfW830ConvergenceW1532
      input globalClosedMapComponents mappedCokernelClosedMapProvider
  exact Dbounded.metrizableRemainingStableSemanticFieldsOfWalkingParallelPairTransferForAvailable
    (closedMapTransferStableInputsW829OfW843ConvergenceW1533
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1533 closed-embedding remaining W829 stable fields from W843/W842 source data. -/
noncomputable def closedEmbeddingRemainingStableFieldsW829OfW843ConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (closedEmbeddingLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    closedEmbeddingLeftCalculusPremiseW829OfW830ConvergenceW1532
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider
  exact Dbounded.metrizableRemainingStableSemanticFieldsOfWalkingParallelPairTransferForAvailable
    (closedEmbeddingTransferStableInputsW829OfW843ConvergenceW1533
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider)

/-- W1533 closed-map W829 stable package with all four W829 fields supplied. -/
noncomputable def closedMapBoundedDerivedInfinityCategoryOfW829DirectSourceConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  closedMapBoundedDerivedInfinityCategoryOfW829ConvergenceW1532
    input globalClosedMapComponents mappedCokernelClosedMapProvider
    (closedMapRemainingStableFieldsW829OfW843ConvergenceW1533
      input globalClosedMapComponents mappedCokernelClosedMapProvider).finiteLimits
    (closedMapRemainingStableFieldsW829OfW843ConvergenceW1533
      input globalClosedMapComponents mappedCokernelClosedMapProvider).finiteColimits
    (closedMapRemainingStableFieldsW829OfW843ConvergenceW1533
      input globalClosedMapComponents mappedCokernelClosedMapProvider).pretriangulated
    (closedMapRemainingStableFieldsW829OfW843ConvergenceW1533
      input globalClosedMapComponents mappedCokernelClosedMapProvider).triangulated

/-- W1533 closed-embedding W829 stable package with all four W829 fields supplied. -/
noncomputable def
    closedEmbeddingBoundedDerivedInfinityCategoryOfW829DirectSourceConvergenceW1533
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  closedEmbeddingBoundedDerivedInfinityCategoryOfW829ConvergenceW1532
    input globalClosedEmbeddingComponents
    mappedCokernelClosedEmbeddingProvider
    (closedEmbeddingRemainingStableFieldsW829OfW843ConvergenceW1533
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider).finiteLimits
    (closedEmbeddingRemainingStableFieldsW829OfW843ConvergenceW1533
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider).finiteColimits
    (closedEmbeddingRemainingStableFieldsW829OfW843ConvergenceW1533
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider).pretriangulated
    (closedEmbeddingRemainingStableFieldsW829OfW843ConvergenceW1533
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider).triangulated

/-- W1533 closed-map direct calculus agrees with the earlier W843 route. -/
theorem w1533ClosedMapDirectCalculusRunsThroughW843W829
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapLeftCalculusPremiseW829OfW830ConvergenceW1532
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    closedMapLeftCalculusPremiseW829OfW830ConvergenceW1532
        input globalClosedMapComponents mappedCokernelClosedMapProvider =
      directBoundedLeftCalculusOfKernelCokernelComparisonW830
        (closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := rfl
    _ =
      directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        (w1531ClosedMapDirectCalculusRunsThroughW830W1519W1530
          input globalClosedMapComponents mappedCokernelClosedMapProvider).symm
    _ =
      directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1526ClosedMapDirectCalculusRunsThroughW864W1519W1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1533 closed-embedding direct calculus agrees with the earlier W843 route. -/
theorem w1533ClosedEmbeddingDirectCalculusRunsThroughW843W829
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputW1533)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingLeftCalculusPremiseW829OfW830ConvergenceW1532
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider =
      directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    closedEmbeddingLeftCalculusPremiseW829OfW830ConvergenceW1532
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider =
      directBoundedLeftCalculusOfKernelCokernelComparisonW830
        (closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := rfl
    _ =
      directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        (w1531ClosedEmbeddingDirectCalculusRunsThroughW830W1519W1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider).symm
    _ =
      directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1526ClosedEmbeddingDirectCalculusRunsThroughW864W1519W1525
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider

/-- W1533 names the W829 stable fields now supplied by W843/W842 direct-source data. -/
def w829StableFieldsSuppliedFromDirectSourceNamesW1533 : List String :=
  ["HasFiniteLimits (Dbounded MetrizableLCA) from W653 finite-shape transfer",
    "HasFiniteColimits (Dbounded MetrizableLCA) from W653 finite-shape transfer",
    "Pretriangulated (Dbounded MetrizableLCA) from W657 direct localization",
    "IsTriangulated (Dbounded MetrizableLCA) from W657 direct localization"]

theorem w829StableFieldsSuppliedFromDirectSourceNamesW1533_count :
    w829StableFieldsSuppliedFromDirectSourceNamesW1533.length = 4 :=
  rfl

/-- W1533 keeps the W1532 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputNamesW1533 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputNamesW1532

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputNamesW1533_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputNamesW1533.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputNamesW1533]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputNamesW1532_count

/-- Current W1533 nonterminal state after discharging W829 stable-route fields. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceStateW1533 :
    Type where
  seed : String
  declarations : List String
  finiteShapeResult : String
  triangulatedSourceResult : String
  remainingStableFieldsResult : String
  stablePackageResult : String
  remainingInputs : List String
  w829SuppliedStableFields : List String
  productSuccessClaimed : Bool

/-- W1533 records that W843/W842 supply the four W829 stable fields. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceStateW1533 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceStateW1533
    where
  seed :=
    "w1533-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w829-stable-fields-from-direct-source"
  declarations :=
    ["closedMapDirectSourceW829OfW843ConvergenceW1533",
      "closedEmbeddingDirectSourceW829OfW843ConvergenceW1533",
      "closedMapDirectLocalizationW829OfW843ConvergenceW1533",
      "closedEmbeddingDirectLocalizationW829OfW843ConvergenceW1533",
      "closedMapPretriangulatedW829OfW843ConvergenceW1533",
      "closedEmbeddingPretriangulatedW829OfW843ConvergenceW1533",
      "closedMapTriangulatedW829OfW843ConvergenceW1533",
      "closedEmbeddingTriangulatedW829OfW843ConvergenceW1533",
      "closedMapTransferStableInputsW829OfW843ConvergenceW1533",
      "closedEmbeddingTransferStableInputsW829OfW843ConvergenceW1533",
      "closedMapRemainingStableFieldsW829OfW843ConvergenceW1533",
      "closedEmbeddingRemainingStableFieldsW829OfW843ConvergenceW1533",
      "closedMapBoundedDerivedInfinityCategoryOfW829DirectSourceConvergenceW1533",
      "closedEmbeddingBoundedDerivedInfinityCategoryOfW829DirectSourceConvergenceW1533",
      "w1533ClosedMapDirectCalculusRunsThroughW843W829",
      "w1533ClosedEmbeddingDirectCalculusRunsThroughW843W829",
      "w829StableFieldsSuppliedFromDirectSourceNamesW1533_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputNamesW1533_count"]
  finiteShapeResult :=
    "proved: W1526/W843/W842 provide W653 finite-shape transfer data for the \
      W1532 W829 semantic record"
  triangulatedSourceResult :=
    "proved: W1526/W843/W842 provide W657 direct-localization \
      pretriangulated and triangulated source data for the W1532 W829 \
      semantic record"
  remainingStableFieldsResult :=
    "proved: finite limits, finite colimits, pretriangulated structure, and \
      triangulated structure are assembled for both W829 branches"
  stablePackageResult :=
    "proved: the W1532 W829 stable package can now be built without separate \
      W829 stable-field parameters on both branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceInputNamesW1533
  w829SuppliedStableFields :=
    w829StableFieldsSuppliedFromDirectSourceNamesW1533
  productSuccessClaimed := false

theorem currentW1533W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSource_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829StableFieldsFromDirectSourceStateW1533.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
