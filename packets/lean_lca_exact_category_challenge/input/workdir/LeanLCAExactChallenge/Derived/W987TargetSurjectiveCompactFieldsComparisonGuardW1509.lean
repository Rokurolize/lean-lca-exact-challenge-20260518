import LeanLCAExactChallenge.Derived.W987RelationFieldsComparisonGuardW1508
import LeanLCAExactChallenge.Derived.TargetSurjectiveCompactFieldsComparisonStableExactAtRoute

/-!
W1509 feeds the W1508/W1498 surface through the W895 explicit
target-surjective-compact fields comparison route. W1508 reaches W894
relation-field leaves; W1509 splits their W715 target data into the W713
target-difference-surjectivity and W601 target-codomain-compactness fields
consumed by W895.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

noncomputable section

/-- W1509 reuses the W1508 74-field relation comparison surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3RelationFieldsComparisonInputW1508

/-- W1509 names the W1508 W894 relation-field leaves used by the projections. -/
def relationFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509) :
    MetrizableWppRelationFieldLeavesW894 :=
  relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1508
    input

/-- W1509 assembles W895 leaves by splitting W1508's W715 target data. -/
def targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1509
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509) :
    MetrizableWppTargetSurjectiveCompactFieldLeavesW895 :=
  let relationLeaves :=
    relationFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
      input
  { rightOpenBoundary := relationLeaves.rightOpenBoundary
    sourcePiZeroBoundary := relationLeaves.sourcePiZeroBoundary
    relationPullbackProvider := relationLeaves.relationPullbackProvider
    targetRelationLiftsProvider := relationLeaves.targetRelationLiftsProvider
    targetDifferenceSurjectiveForTargetProvider :=
      targetDifferenceSurjectiveForTargetProvider_of_surjectiveCompactW715
        relationLeaves.targetSurjectiveCompactForTargetProvider
    targetCodomainCompactSpaceProvider :=
      targetCodomainCompactSpaceProvider_of_surjectiveCompactW715
        relationLeaves.targetSurjectiveCompactForTargetProvider
    diagramAndMappedCokernelClosednessData :=
      relationLeaves.diagramAndMappedCokernelClosednessData
    strictPreimageZeroSrc := relationLeaves.strictPreimageZeroSrc
    strictPreimageOneSrc := relationLeaves.strictPreimageOneSrc
    strictPreimageZeroIso := relationLeaves.strictPreimageZeroIso
    strictPreimageOneIso := relationLeaves.strictPreimageOneIso
    strictPreimageLeftSrc := relationLeaves.strictPreimageLeftSrc
    strictPreimageRightSrc := relationLeaves.strictPreimageRightSrc
    strictPreimageLeftFac := relationLeaves.strictPreimageLeftFac
    strictPreimageRightFac := relationLeaves.strictPreimageRightFac
    strictPreimageZeroMap := relationLeaves.strictPreimageZeroMap
    strictPreimageOneMap := relationLeaves.strictPreimageOneMap
    strictPreimageZeroMapFac := relationLeaves.strictPreimageZeroMapFac
    strictPreimageOneMapFac := relationLeaves.strictPreimageOneMapFac
    strictPreimageLeftNaturality := relationLeaves.strictPreimageLeftNaturality
    strictPreimageRightNaturality := relationLeaves.strictPreimageRightNaturality
    strictRepresentativeMapId := relationLeaves.strictRepresentativeMapId
    strictRepresentativeMapComp := relationLeaves.strictRepresentativeMapComp
    sourceImageObjectNormalization :=
      relationLeaves.sourceImageObjectNormalization
    sourceImageMapNormalization := relationLeaves.sourceImageMapNormalization
    targetFixedTargetUniq := relationLeaves.targetFixedTargetUniq
    localizationModelFixedTargetUniq :=
      relationLeaves.localizationModelFixedTargetUniq
    sourcePretriangulated := relationLeaves.sourcePretriangulated
    sourceTriangulated := relationLeaves.sourceTriangulated
    triangleCompletion := relationLeaves.triangleCompletion
    endpointForgetPreservesHomology :=
      relationLeaves.endpointForgetPreservesHomology
    endpointClosedEmbedding := relationLeaves.endpointClosedEmbedding
    endpointOpenMap := relationLeaves.endpointOpenMap
    endpointEpiOfExactAt := relationLeaves.endpointEpiOfExactAt
    boundedHomotopyLocalizedRightAdjoint :=
      relationLeaves.boundedHomotopyLocalizedRightAdjoint
    boundedHomotopyLocalizedAdjunction :=
      relationLeaves.boundedHomotopyLocalizedAdjunction
    boundedHomotopyLocalizedUnitMem :=
      relationLeaves.boundedHomotopyLocalizedUnitMem }

/-- W1509 projects W895 back to the W894 leaves consumed by W1508. -/
def relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509) :
    MetrizableWppRelationFieldLeavesW894 :=
  relationFieldLeavesOfTargetSurjectiveCompactFieldsW895
    (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1509
      input)

/-- W1509 exposes W895's W733 concrete leaves. -/
def concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedConcreteLeavesW733 :=
  concreteLeavesOfTargetSurjectiveCompactFieldsComparisonW895
    (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1509
      input)

/-- W1509 exposes W895's W732 route data. -/
def routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  routeDataProviderOfTargetSurjectiveCompactFieldsComparisonW895
    (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1509
      input)

/-- W1509 feeds W895 explicit target fields to direct bounded left calculus. -/
theorem directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
    (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1509
      input)

/-- W1509 exposes W895's bounded derived infinity-category package. -/
def boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetSurjectiveCompactFieldsComparisonStableExactAtW895
    (targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1509
      input)

/-- W1509's split W895 target fields rebuild W1508's bundled W715 target data. -/
theorem w1509TargetSurjectiveCompactDataMatchesW1508
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509) :
    targetSurjectiveCompactForTargetOfFieldsW895
        (targetDifferenceSurjectiveForTargetProvider_of_surjectiveCompactW715
          (relationFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
            input).targetSurjectiveCompactForTargetProvider)
        (targetCodomainCompactSpaceProvider_of_surjectiveCompactW715
          (relationFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
            input).targetSurjectiveCompactForTargetProvider) =
      (relationFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
        input).targetSurjectiveCompactForTargetProvider := by
  funext Y
  cases
    (relationFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
      input).targetSurjectiveCompactForTargetProvider Y
  rfl

/-- W1509's W895-to-W894 projection carries W1508's bundled W715 target data. -/
theorem w1509RelationFieldLeavesTargetDataMatchesW1508
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509) :
    (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
        input).targetSurjectiveCompactForTargetProvider =
      (relationFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
        input).targetSurjectiveCompactForTargetProvider := by
  exact w1509TargetSurjectiveCompactDataMatchesW1508 input

/-- W1509's W895 concrete leaves delegate to W894 after target-field assembly. -/
theorem w1509ConcreteLeavesRunThroughW894
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509) :
    concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
        input =
      concreteLeavesOfRelationFieldsComparisonW894
        (relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509
          input) :=
  rfl

/-- W1509 keeps the W1508 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputNamesW1509 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3RelationFieldsComparisonInputNamesW1508

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputNamesW1509_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputNamesW1509.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputNamesW1509]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3RelationFieldsComparisonInputNamesW1508_count

/-- Current W1509 nonterminal explicit target-surjective-compact fields route state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonStateW1509 :
    Type where
  seed : String
  declarations : List String
  targetFieldAssemblyResult : String
  comparisonResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1509 records the W895 explicit target-surjective-compact fields route reached from W1508. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonStateW1509 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonStateW1509 where
  seed :=
    "w1509-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-target-surjective-compact-fields-comparison"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputW1509",
      "relationFieldLeavesForW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509",
      "targetSurjectiveCompactFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W1509",
      "relationFieldLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509",
      "concreteLeavesOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509",
      "routeDataProviderOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509",
      "directBoundedLeftCalculusOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509",
      "boundedDerivedInfinityCategoryOfW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonW1509",
      "w1509TargetSurjectiveCompactDataMatchesW1508",
      "w1509RelationFieldLeavesTargetDataMatchesW1508",
      "w1509ConcreteLeavesRunThroughW894",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputNamesW1509_count"]
  targetFieldAssemblyResult :=
    "proved: W1508's bundled W715 target data supplies the W895\
      target-difference-surjectivity and target-codomain-compactness fields"
  comparisonResult :=
    "proved: W1509's W895 target-surjective-compact fields route delegates to\
      W894 while its rebuilt target data matches W1508's bundled W715 target data"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonInputNamesW1509
  productSuccessClaimed := false

theorem currentW1509W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparison_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3TargetSurjectiveCompactFieldsComparisonStateW1509.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
