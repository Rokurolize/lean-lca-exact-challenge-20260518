import LeanLCAExactChallenge.Derived.TargetHomologyZeroFiniteShapeStableRoute

/-!
W841 routes the W839 target-homology-zero left-calculus data through the
direct finite-shape source and direct-localization triangulated source core.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W841 closed-map data replacing W840 transfer-stable fields by source data. -/
structure MetrizableClosedMapTargetHomologyZeroDirectLocalizationStableRouteDataW841 :
    Type 2 where
  routeData :
    MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839
  directSource :
    MetrizableWppDirectFiniteShapeTrianglehPayloadSourceW653
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/-- W841 closed-embedding data replacing W840 transfer-stable fields by source data. -/
structure
    MetrizableClosedEmbeddingTargetHomologyZeroDirectLocalizationStableRouteDataW841 :
    Type 2 where
  routeData :
    MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839
  directSource :
    MetrizableWppDirectFiniteShapeTrianglehPayloadSourceW653
  directLocalization :
    MetrizableDirectLocalizationTriangulatedSourceNoCommShiftCoreW657

/-- W841 closed-map route preserves the W839 direct-left-calculus theorem. -/
theorem directBoundedLeftCalculusOfClosedMapTargetHomologyZeroDirectLocalizationW841
    (data :
      MetrizableClosedMapTargetHomologyZeroDirectLocalizationStableRouteDataW841) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839 data.routeData

/-- W841 closed-embedding route preserves the W839 direct-left-calculus theorem. -/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroDirectLocalizationStableRouteDataW841) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839 data.routeData

/-- W841 closed-map route derives finite-limit/finite-colimit remainder from W653. -/
noncomputable def
    finiteLimitColimitRemainderOfClosedMapTargetHomologyZeroDirectLocalizationW841
    (data :
      MetrizableClosedMapTargetHomologyZeroDirectLocalizationStableRouteDataW841) :
    Dbounded.MetrizableFiniteLimitColimitRemainderAfterLeftCalculus :=
  Dbounded.metrizableFiniteLimitColimitRemainderOfWalkingParallelPairTransfer
    data.directSource.finiteShapeInputs

/-- W841 closed-embedding route derives finite-limit/finite-colimit remainder from W653. -/
noncomputable def
    finiteLimitColimitRemainderOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroDirectLocalizationStableRouteDataW841) :
    Dbounded.MetrizableFiniteLimitColimitRemainderAfterLeftCalculus :=
  Dbounded.metrizableFiniteLimitColimitRemainderOfWalkingParallelPairTransfer
    data.directSource.finiteShapeInputs

/-- W841 closed-map route derives pretriangulated structure from W657. -/
@[reducible] noncomputable def
    pretriangulatedOfClosedMapTargetHomologyZeroDirectLocalizationW841
    (data :
      MetrizableClosedMapTargetHomologyZeroDirectLocalizationStableRouteDataW841) :
    let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
      targetHomologyZeroLeftCalculusFieldsOfClosedMapW840 data.routeData
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      available.shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839 data.routeData
  letI : HasShift (Dbounded MetrizableLCA.{0}) ℤ :=
    HasShift.localization (boundedExactWeakEquivalence MetrizableLCA.{0}) ℤ
  let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
    targetHomologyZeroLeftCalculusFieldsOfClosedMapW840 data.routeData
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
    data.directLocalization.sourcePretriangulated
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsCompatibleWithTriangulation :=
    metrizableBoundedExactWeakEquivalence_isCompatibleWithTriangulation_of_triangleCompletionW654
      data.directLocalization.triangleCompletion
  exact metrizablePretriangulatedOfDirectLocalizationCompatibilityW654

/-- W841 closed-embedding route derives pretriangulated structure from W657. -/
@[reducible] noncomputable def
    pretriangulatedOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroDirectLocalizationStableRouteDataW841) :
    let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
      targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840 data.routeData
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      available.shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839 data.routeData
  letI : HasShift (Dbounded MetrizableLCA.{0}) ℤ :=
    HasShift.localization (boundedExactWeakEquivalence MetrizableLCA.{0}) ℤ
  let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
    targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840 data.routeData
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
    data.directLocalization.sourcePretriangulated
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsCompatibleWithTriangulation :=
    metrizableBoundedExactWeakEquivalence_isCompatibleWithTriangulation_of_triangleCompletionW654
      data.directLocalization.triangleCompletion
  exact metrizablePretriangulatedOfDirectLocalizationCompatibilityW654

/-- W841 closed-map route derives triangulated structure from W657. -/
@[reducible] noncomputable def
    triangulatedOfClosedMapTargetHomologyZeroDirectLocalizationW841
    (data :
      MetrizableClosedMapTargetHomologyZeroDirectLocalizationStableRouteDataW841) :
    let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
      targetHomologyZeroLeftCalculusFieldsOfClosedMapW840 data.routeData
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      available.shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) :=
      pretriangulatedOfClosedMapTargetHomologyZeroDirectLocalizationW841 data
    IsTriangulated (Dbounded MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839 data.routeData
  letI : HasShift (Dbounded MetrizableLCA.{0}) ℤ :=
    HasShift.localization (boundedExactWeakEquivalence MetrizableLCA.{0}) ℤ
  let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
    targetHomologyZeroLeftCalculusFieldsOfClosedMapW840 data.routeData
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
    data.directLocalization.sourcePretriangulated
  letI : IsTriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
    data.directLocalization.sourceTriangulated
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsCompatibleWithTriangulation :=
    metrizableBoundedExactWeakEquivalence_isCompatibleWithTriangulation_of_triangleCompletionW654
      data.directLocalization.triangleCompletion
  letI : Pretriangulated (Dbounded MetrizableLCA.{0}) :=
    pretriangulatedOfClosedMapTargetHomologyZeroDirectLocalizationW841 data
  exact metrizableIsTriangulatedOfDirectLocalizationCompatibilityW654

/-- W841 closed-embedding route derives triangulated structure from W657. -/
@[reducible] noncomputable def
    triangulatedOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroDirectLocalizationStableRouteDataW841) :
    let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
      targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840 data.routeData
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      available.shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) :=
      pretriangulatedOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841 data
    IsTriangulated (Dbounded MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839 data.routeData
  letI : HasShift (Dbounded MetrizableLCA.{0}) ℤ :=
    HasShift.localization (boundedExactWeakEquivalence MetrizableLCA.{0}) ℤ
  let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
    targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840 data.routeData
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
    data.directLocalization.sourcePretriangulated
  letI : IsTriangulated (BoundedComplexCategory MetrizableLCA.{0}) :=
    data.directLocalization.sourceTriangulated
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsCompatibleWithTriangulation :=
    metrizableBoundedExactWeakEquivalence_isCompatibleWithTriangulation_of_triangleCompletionW654
      data.directLocalization.triangleCompletion
  letI : Pretriangulated (Dbounded MetrizableLCA.{0}) :=
    pretriangulatedOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841 data
  exact metrizableIsTriangulatedOfDirectLocalizationCompatibilityW654

/-- W841 closed-map route derives all remaining stable fields from source data. -/
noncomputable def remainingStableFieldsOfClosedMapTargetHomologyZeroDirectLocalizationW841
    (data :
      MetrizableClosedMapTargetHomologyZeroDirectLocalizationStableRouteDataW841) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedMapW840 data.routeData) where
  finiteLimits := by
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839 data.routeData
    exact Dbounded.metrizableFiniteLimitsOfLeftCalculusProductsForAvailable
      (targetHomologyZeroLeftCalculusFieldsOfClosedMapW840 data.routeData)
      (finiteLimitColimitRemainderOfClosedMapTargetHomologyZeroDirectLocalizationW841 data)
  finiteColimits := by
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839 data.routeData
    exact Dbounded.metrizableFiniteColimitsOfLeftCalculusProductsForAvailable
      (targetHomologyZeroLeftCalculusFieldsOfClosedMapW840 data.routeData)
      (finiteLimitColimitRemainderOfClosedMapTargetHomologyZeroDirectLocalizationW841 data)
  pretriangulated :=
    pretriangulatedOfClosedMapTargetHomologyZeroDirectLocalizationW841 data
  triangulated :=
    triangulatedOfClosedMapTargetHomologyZeroDirectLocalizationW841 data

/-- W841 closed-embedding route derives all remaining stable fields from source data. -/
noncomputable def
    remainingStableFieldsOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroDirectLocalizationStableRouteDataW841) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840 data.routeData) where
  finiteLimits := by
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839 data.routeData
    exact Dbounded.metrizableFiniteLimitsOfLeftCalculusProductsForAvailable
      (targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840 data.routeData)
      (finiteLimitColimitRemainderOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841
        data)
  finiteColimits := by
    letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
      directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839 data.routeData
    exact Dbounded.metrizableFiniteColimitsOfLeftCalculusProductsForAvailable
      (targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840 data.routeData)
      (finiteLimitColimitRemainderOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841
        data)
  pretriangulated :=
    pretriangulatedOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841 data
  triangulated :=
    triangulatedOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841 data

/-- W841 closed-map stable package from W839 plus direct source data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroDirectLocalizationW841
    (data :
      MetrizableClosedMapTargetHomologyZeroDirectLocalizationStableRouteDataW841) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableOrdinaryInput
    (Dbounded.metrizableOrdinaryStableSemanticInputOfLeftCalculusFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedMapW840 data.routeData)
      (remainingStableFieldsOfClosedMapTargetHomologyZeroDirectLocalizationW841 data))

/-- W841 closed-embedding stable package from W839 plus direct source data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroDirectLocalizationStableRouteDataW841) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableOrdinaryInput
    (Dbounded.metrizableOrdinaryStableSemanticInputOfLeftCalculusFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840 data.routeData)
      (remainingStableFieldsOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841
        data))

/-- W841 bundled input names. -/
def targetHomologyZeroDirectLocalizationStableRouteInputNamesW841 : List String :=
  ["W839 target homology-zero strict-realization left-calculus route data",
    "W653 direct finite-shape WPP source data",
    "W657 direct-localization triangulated source data"]

/-- W841 keeps the route to three bundled source-side inputs. -/
theorem targetHomologyZeroDirectLocalizationStableRouteInputNamesW841_count :
    Dbounded.targetHomologyZeroDirectLocalizationStableRouteInputNamesW841.length =
      3 :=
  rfl

/-- Expanded W841 requirements after direct source data supply all stable fields. -/
def targetHomologyZeroDirectLocalizationStableRouteExpandedRequiredFieldNamesW841 :
    List String :=
  Dbounded.targetHomologyZeroStrictRealizationLeftCalculusInputNamesW839 ++
    ["W653 direct finite-shape WPP source data",
      "W657 direct-localization triangulated source data"]

/-- The W841 expanded stable route has four concrete requirements. -/
theorem
    targetHomologyZeroDirectLocalizationStableRouteExpandedRequiredFieldNamesW841_count :
    (let names :=
      targetHomologyZeroDirectLocalizationStableRouteExpandedRequiredFieldNamesW841;
      names.length) =
        4 :=
  rfl

/-- Current checked W841 state for direct-localization stable fields. -/
structure MetrizableTargetHomologyZeroDirectLocalizationStableRouteStateW841 :
    Type where
  seed : String
  declarations : List String
  leftCalculusResult : String
  stableFieldResult : String
  stablePackageResult : String
  derivedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W841 state. -/
def currentMetrizableTargetHomologyZeroDirectLocalizationStableRouteStateW841 :
    Dbounded.MetrizableTargetHomologyZeroDirectLocalizationStableRouteStateW841
    where
  seed := "w841-target-homology-zero-direct-localization-stable-route"
  declarations :=
    ["MetrizableClosedMapTargetHomologyZeroDirectLocalizationStableRouteDataW841",
      "MetrizableClosedEmbeddingTargetHomologyZeroDirectLocalizationStableRouteDataW841",
      "directBoundedLeftCalculusOfClosedMapTargetHomologyZeroDirectLocalizationW841",
      "directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841",
      "finiteLimitColimitRemainderOfClosedMapTargetHomologyZeroDirectLocalizationW841",
      "finiteLimitColimitRemainderOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841",
      "pretriangulatedOfClosedMapTargetHomologyZeroDirectLocalizationW841",
      "pretriangulatedOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841",
      "triangulatedOfClosedMapTargetHomologyZeroDirectLocalizationW841",
      "triangulatedOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841",
      "remainingStableFieldsOfClosedMapTargetHomologyZeroDirectLocalizationW841",
      "remainingStableFieldsOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841",
      "boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroDirectLocalizationW841",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroDirectLocalizationW841",
      "targetHomologyZeroDirectLocalizationStableRouteInputNamesW841",
      "targetHomologyZeroDirectLocalizationStableRouteInputNamesW841_count",
      "targetHomologyZeroDirectLocalizationStableRouteExpandedRequiredFieldNamesW841",
      "targetHomologyZeroDirectLocalizationStableRouteExpandedRequiredFieldNamesW841_count"]
  leftCalculusResult :=
    "proved: W839 target homology-zero data still supply direct bounded left calculus"
  stableFieldResult :=
    "proved: W653 and W657 source data derive finite limits, finite colimits, " ++
      "pretriangulated structure, and triangulated structure for the W839 route"
  stablePackageResult :=
    "proved: W841 assembles the bounded-derived infinity-category package from " ++
      "W839 data plus direct source-side stable data"
  derivedInputs :=
    ["MetrizableWalkingParallelPairFiniteShapeTransferInputs from W653 source data",
      "Pretriangulated (Dbounded MetrizableLCA) from W657 source data",
      "IsTriangulated (Dbounded MetrizableLCA) from W657 source data"]
  remainingInputs :=
    Dbounded.targetHomologyZeroDirectLocalizationStableRouteExpandedRequiredFieldNamesW841
  productSuccessClaimed := false

theorem currentW841TargetHomologyZeroDirectLocalizationStableRoute_productSuccess :
    (let state :=
        currentMetrizableTargetHomologyZeroDirectLocalizationStableRouteStateW841;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
