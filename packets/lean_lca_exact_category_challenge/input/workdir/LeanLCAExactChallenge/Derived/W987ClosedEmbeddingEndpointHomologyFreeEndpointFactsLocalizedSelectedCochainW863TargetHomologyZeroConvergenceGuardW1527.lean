import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW864TargetExactAtConvergenceGuardW1526

/-!
W1527 specializes the W1526 W864 target-ExactAt surface to the W863
target-homology-zero stable-ExactAt route. W1526 reaches W843 target-ExactAt
direct-source data; W1527 names the induced W839 target-homology-zero data and
records that the W1519/W1525/W1526 direct-calculus and stable-package paths run
through W863 on both branches.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1527 reuses the W1526 W864 target-ExactAt convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526

/-- W1527 closed-map W839 target-homology-zero data from the W1526 W843 branch. -/
def closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839 :=
  closedMapTargetHomologyZeroDataOfTargetExactAtW843
    (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1527 closed-embedding W839 target-homology-zero data from the W1526 W843 branch. -/
def closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839 :=
  closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843
    (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1527 closed-map W839 data preserves the W1521 W870 exact-input branch. -/
theorem w1527ClosedMapTargetHomologyZeroDataExactInputsFieldW839
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
        input globalClosedMapComponents mappedCokernelClosedMapProvider).exactInputs =
      closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- W1527 closed-embedding W839 data preserves the W1521 W870 exact-input branch. -/
theorem w1527ClosedEmbeddingTargetHomologyZeroDataExactInputsFieldW839
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).exactInputs =
      closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1527 closed-map W839 target-homology-zero payload is the W843/W803 payload. -/
theorem w1527ClosedMapTargetHomologyZeroDataPayloadFieldW843W803
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).targetHomologyZeroPayload
        (T := T) hT h₁ h₃ =
      (targetHomologyZeroPayloadOfTargetExactAtW803
        cochainHasHomology_of_comparisonBijectivityW839
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider).targetExactAtPayload)
        hT h₁ h₃ :=
  rfl

/-- W1527 closed-embedding W839 target-homology-zero payload is the W843/W803 payload. -/
theorem w1527ClosedEmbeddingTargetHomologyZeroDataPayloadFieldW843W803
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).targetHomologyZeroPayload
        (T := T) hT h₁ h₃ =
      (targetHomologyZeroPayloadOfTargetExactAtW803
        cochainHasHomology_of_comparisonBijectivityW839
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider).targetExactAtPayload)
        hT h₁ h₃ :=
  rfl

/-- W1527 closed-map W864 direct calculus delegates to W863. -/
theorem w1527ClosedMapDirectCalculusRunsThroughW863W864
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapTargetHomologyZeroStableExactAtW863
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1527 closed-embedding W864 direct calculus delegates to W863. -/
theorem w1527ClosedEmbeddingDirectCalculusRunsThroughW863W864
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1527 closed-map W864 stable package delegates to W863. -/
theorem w1527ClosedMapStablePackageRunsThroughW863W864
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroStableExactAtW863
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1527 closed-embedding W864 stable package delegates to W863. -/
theorem w1527ClosedEmbeddingStablePackageRunsThroughW863W864
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1527 composes the closed-map W1519/W1526 direct path through W863. -/
theorem w1527ClosedMapDirectCalculusRunsThroughW863W1519W1526
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapTargetHomologyZeroStableExactAtW863
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1526ClosedMapDirectCalculusRunsThroughW864W1519W1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfClosedMapTargetHomologyZeroStableExactAtW863
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1527ClosedMapDirectCalculusRunsThroughW863W864
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1527 composes the closed-embedding W1519/W1526 direct path through W863. -/
theorem w1527ClosedEmbeddingDirectCalculusRunsThroughW863W1519W1526
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1526ClosedEmbeddingDirectCalculusRunsThroughW864W1519W1525
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1527ClosedEmbeddingDirectCalculusRunsThroughW863W864
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1527 composes the closed-map W1519/W1526 stable path through W863. -/
theorem w1527ClosedMapStablePackageRunsThroughW863W1519W1526
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroStableExactAtW863
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1526ClosedMapStablePackageRunsThroughW864W1519W1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroStableExactAtW863
        (closedMapTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1527ClosedMapStablePackageRunsThroughW863W864
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1527 composes the closed-embedding W1519/W1526 stable path through W863. -/
theorem w1527ClosedEmbeddingStablePackageRunsThroughW863W1519W1526
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1526ClosedEmbeddingStablePackageRunsThroughW864W1519W1525
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
        (closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1527ClosedEmbeddingStablePackageRunsThroughW863W864
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1527 keeps the W1526 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputNamesW1527 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputNamesW1526

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputNamesW1527_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputNamesW1527.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputNamesW1527]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputNamesW1526_count

/-- Current W1527 nonterminal W863 target-homology-zero convergence state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceStateW1527 :
    Type where
  seed : String
  declarations : List String
  targetHomologyZeroDataResult : String
  w863Result : String
  remainingInputs : List String
  w863RemainingInputs : List String
  w839RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1527 records the W1526-to-W863 target-homology-zero convergence bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceStateW1527 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceStateW1527 where
  seed :=
    "w1527-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w863-target-homology-zero-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputW1527",
      "closedMapTargetHomologyZeroDataOfW863ConvergenceW1527",
      "closedEmbeddingTargetHomologyZeroDataOfW863ConvergenceW1527",
      "w1527ClosedMapTargetHomologyZeroDataExactInputsFieldW839",
      "w1527ClosedEmbeddingTargetHomologyZeroDataExactInputsFieldW839",
      "w1527ClosedMapTargetHomologyZeroDataPayloadFieldW843W803",
      "w1527ClosedEmbeddingTargetHomologyZeroDataPayloadFieldW843W803",
      "w1527ClosedMapDirectCalculusRunsThroughW863W864",
      "w1527ClosedEmbeddingDirectCalculusRunsThroughW863W864",
      "w1527ClosedMapStablePackageRunsThroughW863W864",
      "w1527ClosedEmbeddingStablePackageRunsThroughW863W864",
      "w1527ClosedMapDirectCalculusRunsThroughW863W1519W1526",
      "w1527ClosedEmbeddingDirectCalculusRunsThroughW863W1519W1526",
      "w1527ClosedMapStablePackageRunsThroughW863W1519W1526",
      "w1527ClosedEmbeddingStablePackageRunsThroughW863W1519W1526",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputNamesW1527_count"]
  targetHomologyZeroDataResult :=
    "proved: W1526 closed-map and closed-embedding W843 target-ExactAt data \
      assemble W839 target-homology-zero data through W803"
  w863Result :=
    "proved: W1519/W1525/W1526 direct-calculus and stable-package paths \
      compose through W864 to W863 on both closed-map and closed-embedding branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceInputNamesW1527
  w863RemainingInputs :=
    targetHomologyZeroStableExactAtExpandedInputNamesW863
  w839RemainingInputs :=
    targetHomologyZeroStrictRealizationLeftCalculusInputNamesW839
  productSuccessClaimed := false

theorem currentW1527W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W863TargetHomologyZeroConvergenceStateW1527.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
