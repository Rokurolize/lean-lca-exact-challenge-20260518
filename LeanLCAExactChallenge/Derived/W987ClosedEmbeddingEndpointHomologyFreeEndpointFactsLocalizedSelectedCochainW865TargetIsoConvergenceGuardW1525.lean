import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW866IsoClosureConvergenceGuardW1524

/-!
W1525 specializes the W1524 W866 iso-closure surface to the W865
target-isomorphism stable-ExactAt route. W1524 reaches W845 iso-closure data;
W1525 names the induced W844 target-isomorphism data and records that the
W1519/W1522/W1523/W1524 direct-calculus and stable-package paths run through
W865 on both branches.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1525 reuses the W1524 W866 iso-closure convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputW1524

/-- W1525 closed-map W844 target-isomorphism data from the W1524 W845 branch. -/
def closedMapTargetIsoDataOfW865ConvergenceW1525
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844 :=
  closedMapTargetIsoDataOfIsoClosureW845
    (closedMapIsoClosureDataOfW866ConvergenceW1524
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1525 closed-embedding W844 target-isomorphism data from the W1524 W845 branch. -/
def closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844 :=
  closedEmbeddingTargetIsoDataOfIsoClosureW845
    (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1525 closed-map W844 data preserves the W1521 W870 exact-input branch. -/
theorem w1525ClosedMapTargetIsoDataExactInputsFieldW844
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapTargetIsoDataOfW865ConvergenceW1525
        input globalClosedMapComponents mappedCokernelClosedMapProvider).exactInputs =
      closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- W1525 closed-embedding W844 data preserves the W1521 W870 exact-input branch. -/
theorem w1525ClosedEmbeddingTargetIsoDataExactInputsFieldW844
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).exactInputs =
      closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1525 closed-map W844 target-isomorphism realization is the W845/W810/W809 realization. -/
theorem w1525ClosedMapTargetIsoDataTargetIsoFieldW845W810W809
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedMapTargetIsoDataOfW865ConvergenceW1525
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).targetIsoRealization
        (T := T) hT h₁ h₃ =
      targetIsoRealizationOfIsoClosureDirectSourceW845
        (closedMapIsoClosureDataOfW866ConvergenceW1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider).isoClosureRealization
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1525 closed-embedding W844 target-isomorphism realization is the W845/W810/W809 realization. -/
theorem w1525ClosedEmbeddingTargetIsoDataTargetIsoFieldW845W810W809
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).targetIsoRealization
        (T := T) hT h₁ h₃ =
      targetIsoRealizationOfIsoClosureDirectSourceW845
        (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider).isoClosureRealization
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1525 closed-map W866 direct calculus delegates to W865. -/
theorem w1525ClosedMapDirectCalculusRunsThroughW865W866
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfClosedMapIsoClosureDirectSourceStableExactAtW866
        (closedMapIsoClosureDataOfW866ConvergenceW1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapTargetIsoDirectSourceStableExactAtW865
        (closedMapTargetIsoDataOfW865ConvergenceW1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1525 closed-embedding W866 direct calculus delegates to W865. -/
theorem w1525ClosedEmbeddingDirectCalculusRunsThroughW865W866
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
        (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
        (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1525 closed-map W866 stable package delegates to W865. -/
theorem w1525ClosedMapStablePackageRunsThroughW865W866
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfClosedMapIsoClosureDirectSourceStableExactAtW866
        (closedMapIsoClosureDataOfW866ConvergenceW1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapTargetIsoDirectSourceStableExactAtW865
        (closedMapTargetIsoDataOfW865ConvergenceW1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1525 closed-embedding W866 stable package delegates to W865. -/
theorem w1525ClosedEmbeddingStablePackageRunsThroughW865W866
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
        (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
        (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1525 composes the closed-map W1519/W1524 direct path through W865. -/
theorem w1525ClosedMapDirectCalculusRunsThroughW865W1519W1524
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapTargetIsoDirectSourceStableExactAtW865
        (closedMapTargetIsoDataOfW865ConvergenceW1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapIsoClosureDirectSourceStableExactAtW866
        (closedMapIsoClosureDataOfW866ConvergenceW1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1524ClosedMapDirectCalculusRunsThroughW866W1519W1522W1523
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfClosedMapTargetIsoDirectSourceStableExactAtW865
        (closedMapTargetIsoDataOfW865ConvergenceW1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1525ClosedMapDirectCalculusRunsThroughW865W866
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1525 composes the closed-embedding W1519/W1524 direct path through W865. -/
theorem w1525ClosedEmbeddingDirectCalculusRunsThroughW865W1519W1524
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
        (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
        (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1524ClosedEmbeddingDirectCalculusRunsThroughW866W1519W1522W1523
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
        (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1525ClosedEmbeddingDirectCalculusRunsThroughW865W866
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1525 composes the closed-map W1519/W1524 stable path through W865. -/
theorem w1525ClosedMapStablePackageRunsThroughW865W1519W1524
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapTargetIsoDirectSourceStableExactAtW865
        (closedMapTargetIsoDataOfW865ConvergenceW1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapIsoClosureDirectSourceStableExactAtW866
        (closedMapIsoClosureDataOfW866ConvergenceW1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1524ClosedMapStablePackageRunsThroughW866W1519W1522W1523
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedMapTargetIsoDirectSourceStableExactAtW865
        (closedMapTargetIsoDataOfW865ConvergenceW1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1525ClosedMapStablePackageRunsThroughW865W866
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1525 composes the closed-embedding W1519/W1524 stable path through W865. -/
theorem w1525ClosedEmbeddingStablePackageRunsThroughW865W1519W1524
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
        (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
        (closedEmbeddingIsoClosureDataOfW866ConvergenceW1524
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1524ClosedEmbeddingStablePackageRunsThroughW866W1519W1522W1523
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
        (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1525ClosedEmbeddingStablePackageRunsThroughW865W866
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1525 keeps the W1524 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputNamesW1525 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputNamesW1524

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputNamesW1525_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputNamesW1525.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputNamesW1525]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W866IsoClosureConvergenceInputNamesW1524_count

/-- Current W1525 nonterminal W865 target-isomorphism convergence state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceStateW1525 :
    Type where
  seed : String
  declarations : List String
  targetIsoDataResult : String
  w865Result : String
  remainingInputs : List String
  w865RemainingInputs : List String
  w844RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1525 records the W1524-to-W865 target-isomorphism convergence bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceStateW1525 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceStateW1525 where
  seed :=
    "w1525-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w865-target-iso-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525",
      "closedMapTargetIsoDataOfW865ConvergenceW1525",
      "closedEmbeddingTargetIsoDataOfW865ConvergenceW1525",
      "w1525ClosedMapTargetIsoDataExactInputsFieldW844",
      "w1525ClosedEmbeddingTargetIsoDataExactInputsFieldW844",
      "w1525ClosedMapTargetIsoDataTargetIsoFieldW845W810W809",
      "w1525ClosedEmbeddingTargetIsoDataTargetIsoFieldW845W810W809",
      "w1525ClosedMapDirectCalculusRunsThroughW865W866",
      "w1525ClosedEmbeddingDirectCalculusRunsThroughW865W866",
      "w1525ClosedMapStablePackageRunsThroughW865W866",
      "w1525ClosedEmbeddingStablePackageRunsThroughW865W866",
      "w1525ClosedMapDirectCalculusRunsThroughW865W1519W1524",
      "w1525ClosedEmbeddingDirectCalculusRunsThroughW865W1519W1524",
      "w1525ClosedMapStablePackageRunsThroughW865W1519W1524",
      "w1525ClosedEmbeddingStablePackageRunsThroughW865W1519W1524",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputNamesW1525_count"]
  targetIsoDataResult :=
    "proved: W1524 closed-map and closed-embedding W845 iso-closure data \
      assemble W844 target-isomorphism direct-source data through W810/W809"
  w865Result :=
    "proved: W1519/W1522/W1523/W1524 direct-calculus and stable-package paths \
      compose through W866 to W865 on both closed-map and closed-embedding branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputNamesW1525
  w865RemainingInputs :=
    targetIsoDirectSourceStableExactAtExpandedInputNamesW865
  w844RemainingInputs :=
    targetIsoDirectSourceStableRouteExpandedRequiredFieldNamesW844
  productSuccessClaimed := false

theorem currentW1525W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceStateW1525.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
