import LeanLCAExactChallenge.Derived.W987TargetSurjectiveCompactFieldsComparisonGuardW1509
import LeanLCAExactChallenge.Derived.ClosedEmbeddingClosednessFieldsComparisonStableExactAtRoute

/-!
W1510 feeds the W1509/W1498 surface through the W897 explicit
closed-embedding closedness-fields comparison route. W1498 presents the W987
closedness branch as W725's closed-embedding constructor from W973; W1510
splits that branch into the selected-difference closed-embedding components
and mapped-cokernel closed-embedding provider consumed by W897.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1510 reuses the W1509 74-field target-surjective-compact comparison surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509

/-- W1510 names the W1509 W895 target-surjective-compact leaves used by W897. -/
def targetSurjectiveCompactFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510) :
    MetrizableWppTargetSurjectiveCompactFieldLeavesW895 :=
  targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1509
    input

/-- W1510 names the W1498 W973 closed-embedding closedness data behind W1509's W725 branch. -/
def closedEmbeddingClosednessDataForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510) :
    ClosedEmbeddingClosednessDataProviderW973 :=
  closedEmbeddingClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceTriangulationComparisonLeavesW1498
    input

/-- W1510 assembles W897 leaves by splitting W1498's W973 closed-embedding data. -/
def closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1510
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510) :
    MetrizableWppClosedEmbeddingClosednessFieldLeavesW897 :=
  let targetLeaves :=
    targetSurjectiveCompactFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
      input
  let closednessData :=
    closedEmbeddingClosednessDataForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
      input
  { rightOpenBoundary := targetLeaves.rightOpenBoundary
    sourcePiZeroBoundary := targetLeaves.sourcePiZeroBoundary
    relationPullbackProvider := targetLeaves.relationPullbackProvider
    targetRelationLiftsProvider := targetLeaves.targetRelationLiftsProvider
    targetDifferenceSurjectiveForTargetProvider :=
      targetLeaves.targetDifferenceSurjectiveForTargetProvider
    targetCodomainCompactSpaceProvider :=
      targetLeaves.targetCodomainCompactSpaceProvider
    globalClosedEmbeddingComponents :=
      globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
        closednessData
    mappedCokernelClosedEmbeddingProvider :=
      mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
        closednessData
    strictPreimageZeroSrc := targetLeaves.strictPreimageZeroSrc
    strictPreimageOneSrc := targetLeaves.strictPreimageOneSrc
    strictPreimageZeroIso := targetLeaves.strictPreimageZeroIso
    strictPreimageOneIso := targetLeaves.strictPreimageOneIso
    strictPreimageLeftSrc := targetLeaves.strictPreimageLeftSrc
    strictPreimageRightSrc := targetLeaves.strictPreimageRightSrc
    strictPreimageLeftFac := targetLeaves.strictPreimageLeftFac
    strictPreimageRightFac := targetLeaves.strictPreimageRightFac
    strictPreimageZeroMap := targetLeaves.strictPreimageZeroMap
    strictPreimageOneMap := targetLeaves.strictPreimageOneMap
    strictPreimageZeroMapFac := targetLeaves.strictPreimageZeroMapFac
    strictPreimageOneMapFac := targetLeaves.strictPreimageOneMapFac
    strictPreimageLeftNaturality := targetLeaves.strictPreimageLeftNaturality
    strictPreimageRightNaturality := targetLeaves.strictPreimageRightNaturality
    strictRepresentativeMapId := targetLeaves.strictRepresentativeMapId
    strictRepresentativeMapComp := targetLeaves.strictRepresentativeMapComp
    sourceImageObjectNormalization :=
      targetLeaves.sourceImageObjectNormalization
    sourceImageMapNormalization := targetLeaves.sourceImageMapNormalization
    targetFixedTargetUniq := targetLeaves.targetFixedTargetUniq
    localizationModelFixedTargetUniq :=
      targetLeaves.localizationModelFixedTargetUniq
    sourcePretriangulated := targetLeaves.sourcePretriangulated
    sourceTriangulated := targetLeaves.sourceTriangulated
    triangleCompletion := targetLeaves.triangleCompletion
    endpointForgetPreservesHomology :=
      targetLeaves.endpointForgetPreservesHomology
    endpointClosedEmbedding := targetLeaves.endpointClosedEmbedding
    endpointOpenMap := targetLeaves.endpointOpenMap
    endpointEpiOfExactAt := targetLeaves.endpointEpiOfExactAt
    boundedHomotopyLocalizedRightAdjoint :=
      targetLeaves.boundedHomotopyLocalizedRightAdjoint
    boundedHomotopyLocalizedAdjunction :=
      targetLeaves.boundedHomotopyLocalizedAdjunction
    boundedHomotopyLocalizedUnitMem :=
      targetLeaves.boundedHomotopyLocalizedUnitMem }

/-- W1510 projects W897 back to the W895 leaves consumed by W1509. -/
def targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510) :
    MetrizableWppTargetSurjectiveCompactFieldLeavesW895 :=
  targetSurjectiveCompactFieldLeavesOfClosedEmbeddingClosednessFieldsW897
    (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1510
      input)

/-- W1510 exposes W897's W733 concrete leaves. -/
def concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfClosedEmbeddingClosednessFieldsComparisonW897
    (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1510
      input)

/-- W1510 exposes W897's W732 route data. -/
def routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfClosedEmbeddingClosednessFieldsComparisonW897
    (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1510
      input)

/-- W1510 feeds W897 explicit closed-embedding closedness fields to direct bounded left calculus. -/
theorem directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingClosednessFieldsComparisonStableExactAtW897
    (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1510
      input)

/-- W1510 exposes W897's bounded derived infinity-category package. -/
def boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingClosednessFieldsComparisonStableExactAtW897
    (closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1510
      input)

/-- W1510's split W897 closed-embedding fields rebuild W1498's W725 branch. -/
theorem w1510ClosedEmbeddingClosednessDataMatchesW1498
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510) :
    diagramAndMappedCokernelClosednessDataOfClosedEmbeddingFieldsW897
        (globalClosedEmbeddingComponentsOfClosedEmbeddingClosednessDataW973
          (closedEmbeddingClosednessDataForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
            input))
        (mappedCokernelClosedEmbeddingProviderOfClosedEmbeddingClosednessDataW973
          (closedEmbeddingClosednessDataForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
            input)) =
      diagramAndMappedCokernelClosednessDataOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3SourceTriangulationComparisonLeavesW1498
        input :=
  rfl

/-- W1510's W897-to-W895 projection carries W1509's closed-embedding W725 branch. -/
theorem w1510TargetSurjectiveCompactFieldLeavesClosednessDataMatchesW1509
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510) :
    (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
        input).diagramAndMappedCokernelClosednessData =
      (targetSurjectiveCompactFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
        input).diagramAndMappedCokernelClosednessData := by
  exact w1510ClosedEmbeddingClosednessDataMatchesW1498 input

/-- W1510's W897 concrete leaves delegate to W895 after closed-embedding branch assembly. -/
theorem w1510ConcreteLeavesRunThroughW895
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
        input =
      concreteLeavesOfTargetSurjectiveCompactFieldsComparisonW895
        (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510
          input) :=
  rfl

/-- W1510 keeps the W1509 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputNamesW1510 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputNamesW1509

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputNamesW1510_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputNamesW1510.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputNamesW1510]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputNamesW1509_count

/-- Current W1510 nonterminal explicit closed-embedding closedness fields route state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonStateW1510 :
    Type where
  seed : String
  declarations : List String
  closedEmbeddingFieldAssemblyResult : String
  comparisonResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1510 records the W897 explicit closed-embedding closedness-fields route reached from W1509. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonStateW1510 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonStateW1510 where
  seed :=
    "w1510-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-closed-embedding-closedness-fields-comparison"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputW1510",
      "targetSurjectiveCompactFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510",
      "closedEmbeddingClosednessDataForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510",
      "closedEmbeddingClosednessFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1510",
      "targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510",
      "concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510",
      "routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510",
      "directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510",
      "boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonW1510",
      "w1510ClosedEmbeddingClosednessDataMatchesW1498",
      "w1510TargetSurjectiveCompactFieldLeavesClosednessDataMatchesW1509",
      "w1510ConcreteLeavesRunThroughW895",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputNamesW1510_count"]
  closedEmbeddingFieldAssemblyResult :=
    "proved: W1498's W973 closed-embedding closedness data supplies the W897\
      selected-difference closed-embedding components and mapped-cokernel\
      closed-embedding provider"
  comparisonResult :=
    "proved: W1510's W897 closed-embedding closedness-fields route delegates\
      to W895 while its rebuilt W725 closedness branch matches W1498/W1509"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonInputNamesW1510
  productSuccessClaimed := false

theorem currentW1510W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparison_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3ClosedEmbeddingClosednessFieldsComparisonStateW1510.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
