import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW869W868ConvergenceGuardW1522
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataSelectedCochainStrictificationStableConvergenceFieldSplitGuardW1371

/-!
W1523 specializes the W1522 W868 selected-cochain direct-source surface to the
existing W1371 W847-to-W846 and W868-to-W867 convergence guard. W1522 reaches
W868 on both closed-map and closed-embedding branches; W1523 names the induced
W846 strict-realization data and composes the route through W867.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1523 reuses the W1522 W869/W868 convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522

/-- W1523 closed-map W846 strict-realization data from the W1522 W847 branch. -/
def closedMapStrictRealizationDataOfW867ConvergenceW1523
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846 :=
  closedMapStrictRealizationDataOfSelectedCochainW847
    (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1523 closed-embedding W846 strict-realization data from the W1522 W847 branch. -/
def closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846 :=
  closedEmbeddingStrictRealizationDataOfSelectedCochainW847
    (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1523 closed-map W846 data preserves the W1521 W870 exact-input branch. -/
theorem w1523ClosedMapStrictRealizationDataExactInputsFieldW1371
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapStrictRealizationDataOfW867ConvergenceW1523
        input globalClosedMapComponents mappedCokernelClosedMapProvider).exactInputs =
      closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- W1523 closed-embedding W846 data preserves the W1521 W870 exact-input branch. -/
theorem w1523ClosedEmbeddingStrictRealizationDataExactInputsFieldW1371
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).exactInputs =
      closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1523 closed-map W846 realization is the W847 selected-cochain realization. -/
theorem w1523ClosedMapStrictRealizationDataTrianglehFieldW847
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedMapStrictRealizationDataOfW867ConvergenceW1523
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).trianglehRealization
        (T := T) hT h₁ h₃ =
      trianglehRealizationOfSelectedCochainStrictificationW847
        (selectedCochainStrictificationOfClosedMapExactInputsW849
          universalLeftRightComparisonIso_of_comparisonBijectivityW831
          (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
            input globalClosedMapComponents mappedCokernelClosedMapProvider))
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1523 closed-embedding W846 realization is the W847 selected-cochain realization. -/
theorem w1523ClosedEmbeddingStrictRealizationDataTrianglehFieldW847
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).trianglehRealization
        (T := T) hT h₁ h₃ =
      trianglehRealizationOfSelectedCochainStrictificationW847
        (selectedCochainStrictificationOfClosedEmbeddingExactInputsW849
          universalLeftRightComparisonIso_of_comparisonBijectivityW831
          (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
            input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider))
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1523 closed-map W868 direct calculus delegates to W867. -/
theorem w1523ClosedMapDirectCalculusRunsThroughW867W1371
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapStrictRealizationDirectSourceStableExactAtW867
        (closedMapStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w868ClosedMapDirectCalculusRunsThroughW847W846W867W1371
    (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1523 closed-embedding W868 direct calculus delegates to W867. -/
theorem w1523ClosedEmbeddingDirectCalculusRunsThroughW867W1371
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
        (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  w868ClosedEmbeddingDirectCalculusRunsThroughW847W846W867W1371
    (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1523 closed-map W868 stable package delegates to W867. -/
theorem w1523ClosedMapStablePackageRunsThroughW867W1371
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapStrictRealizationDirectSourceStableExactAtW867
        (closedMapStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w868ClosedMapStablePackageRunsThroughW847W846W867W1371
    (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1523 closed-embedding W868 stable package delegates to W867. -/
theorem w1523ClosedEmbeddingStablePackageRunsThroughW867W1371
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
        (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  w868ClosedEmbeddingStablePackageRunsThroughW847W846W867W1371
    (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1523 composes the closed-map W1519/W1522 direct path through W867. -/
theorem w1523ClosedMapDirectCalculusRunsThroughW867W1519W1522W1371
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapStrictRealizationDirectSourceStableExactAtW867
        (closedMapStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1522ClosedMapDirectCalculusRunsThroughW868W1519W1521W1372
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfClosedMapStrictRealizationDirectSourceStableExactAtW867
        (closedMapStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1523ClosedMapDirectCalculusRunsThroughW867W1371
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1523 composes the closed-embedding W1519/W1522 direct path through W867. -/
theorem w1523ClosedEmbeddingDirectCalculusRunsThroughW867W1519W1522W1371
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
        (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1522ClosedEmbeddingDirectCalculusRunsThroughW868W1519W1521W1372
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
        (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1523ClosedEmbeddingDirectCalculusRunsThroughW867W1371
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1523 composes the closed-map W1519/W1522 stable path through W867. -/
theorem w1523ClosedMapStablePackageRunsThroughW867W1519W1522W1371
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapStrictRealizationDirectSourceStableExactAtW867
        (closedMapStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1522ClosedMapStablePackageRunsThroughW868W1519W1521W1372
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedMapStrictRealizationDirectSourceStableExactAtW867
        (closedMapStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1523ClosedMapStablePackageRunsThroughW867W1371
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1523 composes the closed-embedding W1519/W1522 stable path through W867. -/
theorem w1523ClosedEmbeddingStablePackageRunsThroughW867W1519W1522W1371
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
        (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1522ClosedEmbeddingStablePackageRunsThroughW868W1519W1521W1372
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
        (closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1523ClosedEmbeddingStablePackageRunsThroughW867W1371
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1523 keeps the W1522 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputNamesW1523 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputNamesW1522

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputNamesW1523_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputNamesW1523.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputNamesW1523]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputNamesW1522_count

/-- Current W1523 nonterminal W867 strict-realization convergence state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceStateW1523 :
    Type where
  seed : String
  declarations : List String
  strictRealizationDataResult : String
  w867Result : String
  remainingInputs : List String
  w868RemainingInputs : List String
  w867RemainingInputs : List String
  w846RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1523 records the W1522-to-W1371 W867 convergence bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceStateW1523 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceStateW1523 where
  seed :=
    "w1523-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w867-strict-realization-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputW1523",
      "closedMapStrictRealizationDataOfW867ConvergenceW1523",
      "closedEmbeddingStrictRealizationDataOfW867ConvergenceW1523",
      "w1523ClosedMapStrictRealizationDataExactInputsFieldW1371",
      "w1523ClosedEmbeddingStrictRealizationDataExactInputsFieldW1371",
      "w1523ClosedMapStrictRealizationDataTrianglehFieldW847",
      "w1523ClosedEmbeddingStrictRealizationDataTrianglehFieldW847",
      "w1523ClosedMapDirectCalculusRunsThroughW867W1371",
      "w1523ClosedEmbeddingDirectCalculusRunsThroughW867W1371",
      "w1523ClosedMapStablePackageRunsThroughW867W1371",
      "w1523ClosedEmbeddingStablePackageRunsThroughW867W1371",
      "w1523ClosedMapDirectCalculusRunsThroughW867W1519W1522W1371",
      "w1523ClosedEmbeddingDirectCalculusRunsThroughW867W1519W1522W1371",
      "w1523ClosedMapStablePackageRunsThroughW867W1519W1522W1371",
      "w1523ClosedEmbeddingStablePackageRunsThroughW867W1519W1522W1371",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputNamesW1523_count"]
  strictRealizationDataResult :=
    "proved: W1522 closed-map and closed-embedding W847 selected-cochain data \
      assemble W846 strict-realization direct-source data through W1371"
  w867Result :=
    "proved: W1519/W1522 direct-calculus and stable-package paths compose \
      through W868 to W867 on both closed-map and closed-embedding branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceInputNamesW1523
  w868RemainingInputs :=
    selectedCochainDirectSourceStableExactAtExpandedInputNamesW868
  w867RemainingInputs :=
    strictRealizationDirectSourceStableExactAtExpandedInputNamesW867
  w846RemainingInputs :=
    strictRealizationDirectSourceStableRouteExpandedRequiredFieldNamesW846
  productSuccessClaimed := false

theorem currentW1523W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W867StrictRealizationConvergenceStateW1523.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
