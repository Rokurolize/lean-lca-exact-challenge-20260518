import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW867StrictRealizationConvergenceGuardW1523

/-!
W1524 specializes the W1523 W867 strict-realization surface to the W866
iso-closure stable-ExactAt route. W1523 reaches W846 strict-realization data;
W1524 names the induced W845 iso-closure data and records that the W1519/W1522
direct-calculus and stable-package paths run through W866 on both branches.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1524 reuses the W1523 W867 strict-realization convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523

/-- W1524 closed-map W845 iso-closure data from the W1523 W846 branch. -/
def closedMapIsoClosureDataOfW866ConvergenceW1524
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845 :=
  closedMapIsoClosureDataOfStrictDirectSourceW846
    (closedMapStrictRealizationDataOfW867ConvergenceW1523
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1524 closed-embedding W845 iso-closure data from the W1523 W846 branch. -/
def closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845 :=
  closedEmbeddingIsoClosureDataOfStrictDirectSourceW846
    (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1524 closed-map W845 data preserves the W1521 W870 exact-input branch. -/
theorem w1524ClosedMapIsoClosureDataExactInputsFieldW845
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapIsoClosureDataOfW866ConvergenceW1524
        input globalClosedMapComponents mappedCokernelClosedMapProvider).exactInputs =
      closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- W1524 closed-embedding W845 data preserves the W1521 W870 exact-input branch. -/
theorem w1524ClosedEmbeddingIsoClosureDataExactInputsFieldW845
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).exactInputs =
      closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1524 closed-map W845 iso-closure realization is the W812/W847 realization. -/
theorem w1524ClosedMapIsoClosureDataIsoClosureFieldW812W847
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyIsoClosure MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyIsoClosure MetrizableLCA.{0} T.obj₃) :
    (closedMapIsoClosureDataOfW866ConvergenceW1524
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).isoClosureRealization
        (T := T) hT h₁ h₃ =
      isoClosureRealizationOfStrictRealizationHomologyDetectionW812
        (homologyDetectionOfClosedMapExactInputsW812
          universalLeftRightComparisonIso_of_comparisonBijectivityW831
          (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
            input globalClosedMapComponents mappedCokernelClosedMapProvider))
        (trianglehRealizationOfSelectedCochainStrictificationW847
          (selectedCochainStrictificationOfClosedMapExactInputsW849
            universalLeftRightComparisonIso_of_comparisonBijectivityW831
            (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
              input globalClosedMapComponents mappedCokernelClosedMapProvider)))
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1524 closed-embedding W845 iso-closure realization is the W812/W847 realization. -/
theorem w1524ClosedEmbeddingIsoClosureDataIsoClosureFieldW812W847
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyIsoClosure MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyIsoClosure MetrizableLCA.{0} T.obj₃) :
    (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).isoClosureRealization
        (T := T) hT h₁ h₃ =
      isoClosureRealizationOfStrictRealizationHomologyDetectionW812
        (homologyDetectionOfClosedEmbeddingExactInputsW812
          universalLeftRightComparisonIso_of_comparisonBijectivityW831
          (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
            input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider))
        (trianglehRealizationOfSelectedCochainStrictificationW847
          (selectedCochainStrictificationOfClosedEmbeddingExactInputsW849
            universalLeftRightComparisonIso_of_comparisonBijectivityW831
            (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
              input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)))
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1524 closed-map W867 direct calculus delegates to W866. -/
theorem w1524ClosedMapDirectCalculusRunsThroughW866W867
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfClosedMapStrictRealizationDirectSourceStableExactAtW867
        (closedMapStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapIsoClosureDirectSourceStableExactAtW866
        (closedMapIsoClosureDataOfW866ConvergenceW1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1524 closed-embedding W867 direct calculus delegates to W866. -/
theorem w1524ClosedEmbeddingDirectCalculusRunsThroughW866W867
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
        (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
        (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1524 closed-map W867 stable package delegates to W866. -/
theorem w1524ClosedMapStablePackageRunsThroughW866W867
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfClosedMapStrictRealizationDirectSourceStableExactAtW867
        (closedMapStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapIsoClosureDirectSourceStableExactAtW866
        (closedMapIsoClosureDataOfW866ConvergenceW1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1524 closed-embedding W867 stable package delegates to W866. -/
theorem w1524ClosedEmbeddingStablePackageRunsThroughW866W867
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
        (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
        (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1524 composes the closed-map W1519/W1522 direct path through W866. -/
theorem w1524ClosedMapDirectCalculusRunsThroughW866W1519W1522W1523
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapIsoClosureDirectSourceStableExactAtW866
        (closedMapIsoClosureDataOfW866ConvergenceW1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapStrictRealizationDirectSourceStableExactAtW867
        (closedMapStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1523ClosedMapDirectCalculusRunsThroughW867W1519W1522W1371
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfClosedMapIsoClosureDirectSourceStableExactAtW866
        (closedMapIsoClosureDataOfW866ConvergenceW1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1524ClosedMapDirectCalculusRunsThroughW866W867
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1524 composes the closed-embedding W1519/W1522 direct path through W866. -/
theorem w1524ClosedEmbeddingDirectCalculusRunsThroughW866W1519W1522W1523
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
        (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
        (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1523ClosedEmbeddingDirectCalculusRunsThroughW867W1519W1522W1371
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
        (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1524ClosedEmbeddingDirectCalculusRunsThroughW866W867
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1524 composes the closed-map W1519/W1522 stable path through W866. -/
theorem w1524ClosedMapStablePackageRunsThroughW866W1519W1522W1523
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapIsoClosureDirectSourceStableExactAtW866
        (closedMapIsoClosureDataOfW866ConvergenceW1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapStrictRealizationDirectSourceStableExactAtW867
        (closedMapStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1523ClosedMapStablePackageRunsThroughW867W1519W1522W1371
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedMapIsoClosureDirectSourceStableExactAtW866
        (closedMapIsoClosureDataOfW866ConvergenceW1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1524ClosedMapStablePackageRunsThroughW866W867
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1524 composes the closed-embedding W1519/W1522 stable path through W866. -/
theorem w1524ClosedEmbeddingStablePackageRunsThroughW866W1519W1522W1523
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
        (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
        (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1523ClosedEmbeddingStablePackageRunsThroughW867W1519W1522W1371
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
        (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1524ClosedEmbeddingStablePackageRunsThroughW866W867
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1524 keeps the W1523 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputNamesW1524 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputNamesW1523

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputNamesW1524_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputNamesW1524.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputNamesW1524]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputNamesW1523_count

/-- Current W1524 nonterminal W866 iso-closure convergence state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceStateW1524 :
    Type where
  seed : String
  declarations : List String
  isoClosureDataResult : String
  w866Result : String
  remainingInputs : List String
  w866RemainingInputs : List String
  w845RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1524 records the W1523-to-W866 iso-closure convergence bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceStateW1524 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceStateW1524 where
  seed :=
    "w1524-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w866-iso-closure-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524",
      "closedMapIsoClosureDataOfW866ConvergenceW1524",
      "closedEmbeddingIsoClosureDataOfW866ConvergenceW1524",
      "w1524ClosedMapIsoClosureDataExactInputsFieldW845",
      "w1524ClosedEmbeddingIsoClosureDataExactInputsFieldW845",
      "w1524ClosedMapIsoClosureDataIsoClosureFieldW812W847",
      "w1524ClosedEmbeddingIsoClosureDataIsoClosureFieldW812W847",
      "w1524ClosedMapDirectCalculusRunsThroughW866W867",
      "w1524ClosedEmbeddingDirectCalculusRunsThroughW866W867",
      "w1524ClosedMapStablePackageRunsThroughW866W867",
      "w1524ClosedEmbeddingStablePackageRunsThroughW866W867",
      "w1524ClosedMapDirectCalculusRunsThroughW866W1519W1522W1523",
      "w1524ClosedEmbeddingDirectCalculusRunsThroughW866W1519W1522W1523",
      "w1524ClosedMapStablePackageRunsThroughW866W1519W1522W1523",
      "w1524ClosedEmbeddingStablePackageRunsThroughW866W1519W1522W1523",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputNamesW1524_count"]
  isoClosureDataResult :=
    "proved: W1523 closed-map and closed-embedding W846 strict-realization data \
      assemble W845 iso-closure direct-source data through W812/W847"
  w866Result :=
    "proved: W1519/W1522/W1523 direct-calculus and stable-package paths compose \
      through W867 to W866 on both closed-map and closed-embedding branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputNamesW1524
  w866RemainingInputs :=
    isoClosureDirectSourceStableExactAtExpandedInputNamesW866
  w845RemainingInputs :=
    isoClosureDirectSourceStableRouteExpandedRequiredFieldNamesW845
  productSuccessClaimed := false

theorem currentW1524W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceStateW1524.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
